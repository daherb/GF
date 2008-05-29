----------------------------------------------------------------------
-- |
-- Maintainer  : Krasimir Angelov
-- Stability   : (stable)
-- Portability : (portable)
--
-- FCFG parsing
-----------------------------------------------------------------------------

module PGF.Parsing.FCFG
    (parseFCF,buildParserInfo,ParserInfo(..),makeFinalEdge) where

import GF.Data.ErrM
import GF.Data.Assoc
import GF.Data.SortedList 

import PGF.CId
import PGF.Data
import PGF.Macros
import PGF.BuildParser
import PGF.Parsing.FCFG.Utilities
import PGF.Parsing.FCFG.Active

import qualified Data.Map as Map

----------------------------------------------------------------------
-- parsing

-- main parsing function

parseFCF :: 
      String ->         -- ^ parsing strategy
      ParserInfo ->     -- ^ compiled grammar (fcfg) 
      CId ->            -- ^ starting category
      [String] ->       -- ^ input tokens
      Err [Exp]         -- ^ resulting GF terms
parseFCF strategy pinfo startCat inString =
    do let inTokens = input inString
       startCats <- Map.lookup startCat (startupCats pinfo)
       fcfParser <- {- trace lctree $ -} parseFCF strategy
       let chart = fcfParser pinfo startCats inTokens
	   (i,j) = inputBounds inTokens
	   finalEdges = [makeFinalEdge cat i j | cat <- startCats]
	   forests = chart2forests chart (const False) finalEdges
           filteredForests = forests >>= applyProfileToForest
	   trees = nubsort $ filteredForests >>= forest2trees
       return $ map tree2term trees
    where
      parseFCF :: String -> Err (FCFParser)
      parseFCF "bottomup" = Ok  $ parse "b"
      parseFCF "topdown"  = Ok  $ parse "t"
      parseFCF strat      = Bad $ "FCFG parsing strategy not defined: " ++ strat

----------------------------------------------------------------------
-- parse trees to GFCC terms

tree2term :: SyntaxTree CId -> Exp
tree2term (TNode f ts) = tree (AC f) (map tree2term ts)
tree2term (TString  s) = tree (AS s) []
tree2term (TInt     n) = tree (AI n) []
tree2term (TFloat   f) = tree (AF f) []
tree2term (TMeta)      = exp0

----------------------------------------------------------------------
-- conversion and unification of forests

-- simplest implementation
applyProfileToForest :: SyntaxForest (CId,[Profile]) -> [SyntaxForest CId]
applyProfileToForest (FNode (fun,profiles) children) 
    | fun == wildCId = concat chForests
    | otherwise      = [ FNode fun chForests | not (null chForests) ]
    where chForests  = concat [ mapM (unifyManyForests . map (forests !!)) profiles |
			        forests0 <- children,
			        forests <- mapM applyProfileToForest forests0 ]
applyProfileToForest (FString s) = [FString s]
applyProfileToForest (FInt    n) = [FInt    n]
applyProfileToForest (FFloat  f) = [FFloat  f]
applyProfileToForest (FMeta)     = [FMeta]
