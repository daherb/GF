----------------------------------------------------------------------
-- |
-- Maintainer  : PL
-- Stability   : (stable)
-- Portability : (portable)
--
-- > CVS $Date: 2005/04/18 14:55:33 $ 
-- > CVS $Author: peb $
-- > CVS $Revision: 1.2 $
--
-- Chart parsing of grammars in CF format
-----------------------------------------------------------------------------

module GF.NewParsing.CF (parse) where

import GF.System.Tracing
import GF.Infra.Print

import GF.Data.SortedList (nubsort)
import GF.Data.Assoc
import qualified CF
import qualified CFIdent as CFI
import GF.Formalism.Utilities
import GF.Formalism.CFG
import qualified GF.NewParsing.CFG as P

type Token    = CFI.CFTok
type Name     = CFI.CFFun
type Category = CFI.CFCat

parse :: String -> CF.CF -> Category -> CF.CFParser
parse = buildParser . P.parseCF 

buildParser :: P.CFParser Category Name Token -> CF.CF -> Category -> CF.CFParser
buildParser parser cf start tokens = (parseResults, parseInformation)
    where parseInformation = prtSep "\n" trees
	  parseResults     = [ (tree2cfTree t, []) | t <- trees ]
	  theInput = input tokens
	  edges    = tracePrt "Parsing.CF - nr. edges" (prt.length) $
		     parser pInf [start] theInput
	  chart    = tracePrt "Parsing.CF - size of chart" (prt . map (length.snd) . aAssocs) $
		     grammar2chart $ map addCategory edges
	  forests  = tracePrt "Parsing.CF - nr. forests" (prt.length) $
		     chart2forests chart (const False) 
		     [ uncurry Edge (inputBounds theInput) start ]
	  trees    = tracePrt "Parsing.CF - nr. trees" (prt.length) $
		     concatMap forest2trees forests
	  pInf     = P.buildCFPInfo $ cf2grammar cf (nubsort tokens)
	  

addCategory (CFRule cat rhs name) = CFRule cat rhs (name, cat)

tree2cfTree (TNode (name, Edge _ _ cat) trees) = CF.CFTree (name, (cat, map tree2cfTree trees))

cf2grammar :: CF.CF -> [Token] -> CFGrammar Category Name Token
cf2grammar cf tokens = [ CFRule cat rhs name |
			 (name, (cat, rhs0)) <- cfRules, 
			 rhs <- mapM item2symbol rhs0 ] 
    where cfRules = concatMap (CF.predefRules (CF.predefOfCF cf)) tokens ++ 
		    CF.rulesOfCF cf 
	  item2symbol (CF.CFNonterm cat) = [Cat cat]
	  item2symbol item = map Tok $ filter (CF.matchCFTerm item) tokens


