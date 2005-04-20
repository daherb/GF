----------------------------------------------------------------------
-- |
-- Maintainer  : PL
-- Stability   : (stable)
-- Portability : (portable)
--
-- > CVS $Date: 2005/04/20 12:49:44 $ 
-- > CVS $Author: peb $
-- > CVS $Revision: 1.5 $
--
-- The main parsing module, parsing GFC grammars
-- by translating to simpler formats, such as PMCFG and CFG
----------------------------------------------------------------------

module GF.NewParsing.GFC
    (parse, PInfo(..), buildPInfo) where

import GF.System.Tracing 
import GF.Infra.Print
import qualified PrGrammar

import Operations (Err(..))

import qualified Grammar 
import qualified Macros 
import qualified AbsGFC
import qualified Ident
import CFIdent (CFCat, cfCat2Ident, CFTok, wordsCFTok)

import GF.Data.SortedList 
import GF.Data.Assoc
import GF.Formalism.Utilities
import GF.Conversion.Types

import qualified GF.Formalism.GCFG as G
import qualified GF.Formalism.SimpleGFC as S
import qualified GF.Formalism.MCFG as M
import qualified GF.Formalism.CFG as C
import qualified GF.NewParsing.MCFG as PM
import qualified GF.NewParsing.CFG as PC

----------------------------------------------------------------------
-- parsing information

data PInfo = PInfo { mcfPInfo :: MCFPInfo,
		     cfPInfo  :: CFPInfo }

type MCFPInfo = MGrammar
type CFPInfo  = PC.CFPInfo CCat Name Token

buildPInfo :: MGrammar -> CGrammar -> PInfo
buildPInfo mcfg cfg = PInfo { mcfPInfo = mcfg,
			      cfPInfo  = PC.buildCFPInfo cfg }


----------------------------------------------------------------------
-- main parsing function

parse :: String         -- ^ parsing strategy
      -> PInfo          -- ^ compiled grammars (mcfg and cfg) 
      -> Ident.Ident    -- ^ abstract module name
      -> CFCat          -- ^ starting category
      -> [CFTok]        -- ^ input tokens
      -> Err [Grammar.Term] -- ^ resulting GF terms

parse (prs:strategy) pinfo abs startCat inString = 
    do let inTokens = tracePrt "Parsing.GFC - input tokens" prt $
		      inputMany (map wordsCFTok inString)
       forests <- selectParser prs strategy pinfo startCat inTokens
       traceM "Parsing.GFC - nr. forests" (prt (length forests))
       let filteredForests = tracePrt "Parsing.GFC - nr. filtered forests" (prt . length) $
			     forests >>= applyProfileToForest
	   -- compactFs = tracePrt "#compactForests" (prt . length) $
	   -- 	          tracePrt "compactForests" (prtBefore "\n") $
	   -- 	          compactForests forests
	   trees = tracePrt "Parsing.GFC - nr. trees" (prt . length) $
		   nubsort $ filteredForests >>= forest2trees
		   -- compactFs >>= forest2trees
       return $ map (tree2term abs) trees

-- default parser = CFG (for now)
parse "" pinfo abs startCat inString = parse "c" pinfo abs startCat inString


-- parsing via CFG
selectParser prs strategy pinfo startCat inTokens | prs=='c' 
    = do let startCats = tracePrt "Parsing.GFC - starting CF categories" prt $
			 filter isStart $ map fst $ aAssocs $ PC.topdownRules cfpi
	     isStart cat = ccat2scat cat == cfCat2Ident startCat
	     cfpi = cfPInfo pinfo
	 cfParser <- PC.parseCF strategy
	 let cfChart = tracePrt "Parsing.GFC - sz. CF chart" (prt . length) $
		       cfParser cfpi startCats inTokens
	     chart = tracePrt "Parsing.GFC - sz. chart" (prt . map (length.snd) . aAssocs) $
		     C.grammar2chart cfChart
	     finalEdges = tracePrt "Parsing.GFC - final chart edges" prt $
			  map (uncurry Edge (inputBounds inTokens)) startCats
	 return $ chart2forests chart (const False) finalEdges

-- parsing via MCFG
selectParser prs strategy pinfo startCat inTokens | prs=='m' 
    = do let startCats = tracePrt "Parsing.GFC - starting MCF categories" prt $
			 filter isStart $ nubsort [ c | G.Rule (G.Abs c _ _) _ <- mcfpi ]
	     isStart cat = mcat2scat cat == cfCat2Ident startCat
	     mcfpi = mcfPInfo pinfo
	 mcfParser <- PM.parseMCF strategy
	 let mcfChart = tracePrt "Parsing.GFC - sz. MCF chart" (prt . length) $
			mcfParser mcfpi startCats inTokens
	     chart = tracePrt "Parsing.GFC - sz. chart" (prt . map (length.snd) . aAssocs) $
		     G.abstract2chart mcfChart
	     finalEdges = tracePrt "Parsing.GFC - final chart edges" prt $
			  [ PM.makeFinalEdge cat lbl (inputBounds inTokens) | 
			    cat@(MCat _ [lbl]) <- startCats ]
	 return $ chart2forests chart (const False) finalEdges

-- error parser: 
selectParser prs strategy _ _ _ = Bad $ "Parser not defined: " ++ (prs:strategy)


----------------------------------------------------------------------
-- parse trees to GF terms

tree2term :: Ident.Ident -> SyntaxTree Fun -> Grammar.Term
tree2term abs (TNode f ts) = Macros.mkApp (Macros.qq (abs,f)) (map (tree2term abs) ts)
tree2term abs (TMeta)      = Macros.mkMeta 0


----------------------------------------------------------------------
-- conversion and unification of forests

-- simplest implementation
applyProfileToForest :: SyntaxForest Name -> [SyntaxForest Fun]
applyProfileToForest (FNode name@(Name fun profile) children) 
    | isCoercion name = concat chForests
    | otherwise       = [ FNode fun chForests | not (null chForests) ]
    where chForests   = concat [ applyProfileM unifyManyForests profile forests |
				 forests0 <- children,
				 forests <- mapM applyProfileToForest forests0 ]

{-
-- more intelligent(?) implementation
applyProfileToForest (FNode (Name name profile) children) 
    | isCoercion name = concat chForests
    | otherwise       = [ FNode name chForests | not (null chForests) ]
    where chForests   = concat [ mapM (checkProfile forests) profile |
				 forests0 <- children,
				 forests <- mapM applyProfileToForest forests0 ]
-}


