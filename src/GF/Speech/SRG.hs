----------------------------------------------------------------------
-- |
-- Module      : SRG
-- Maintainer  : BB
-- Stability   : (stable)
-- Portability : (portable)
--
-- > CVS $Date: 2005/11/01 20:09:04 $ 
-- > CVS $Author: bringert $
-- > CVS $Revision: 1.20 $
--
-- Representation of, conversion to, and utilities for 
-- printing of a general Speech Recognition Grammar. 
--
-- FIXME: remove \/ warn \/ fail if there are int \/ string literal
-- categories in the grammar
-----------------------------------------------------------------------------

module GF.Speech.SRG (SRG(..), SRGRule(..), SRGAlt(..),
                      SRGCat, SRGNT, CFTerm,
                       makeSimpleSRG
                     , lookupFM_, prtS
                     , cfgCatToGFCat, srgTopCats
                     , EBnfSRGAlt(..), EBnfSRGItem
                     , ebnfSRGAlts
                     ) where

import GF.Data.Operations
import GF.Data.Utilities
import GF.Infra.Ident
import GF.Formalism.CFG
import GF.Formalism.Utilities (Symbol(..), NameProfile(..)
                              , Profile(..), SyntaxForest
                              , filterCats, mapSymbol, symbol)
import GF.Conversion.Types
import GF.Infra.Print
import GF.Speech.TransformCFG
import GF.Speech.Relation
import GF.Speech.FiniteState
import GF.Speech.RegExp
import GF.Infra.Option
import GF.Probabilistic.Probabilistic (Probs)
import GF.Compile.ShellState (StateGrammar, stateProbs, stateOptions, cncId)

import Data.List
import Data.Maybe (fromMaybe, maybeToList)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

data SRG = SRG { grammarName :: String    -- ^ grammar name
		 , startCat :: String     -- ^ start category name
		 , origStartCat :: String -- ^ original start category name
                 , grammarLanguage :: Maybe String -- ^ The language for which the grammar 
                                                   --   is intended, e.g. en-UK
	         , rules :: [SRGRule] 
	       }
	 deriving (Eq,Show)

data SRGRule = SRGRule SRGCat String [SRGAlt] -- ^ SRG category name, original category name
	                                      --   and productions
	     deriving (Eq,Show)

-- | maybe a probability, a rule name and a list of symbols
data SRGAlt = SRGAlt (Maybe Double) CFTerm [Symbol SRGNT Token]
	      deriving (Eq,Show)

type SRGCat = String

-- | An SRG non-terminal. Category name and its number in the profile.
type SRGNT = (SRGCat, Int)

-- | SRG category name and original name
type CatName = (SRGCat,String) 

type CatNames = Map String String

-- | Create a non-left-recursive SRG. 
--   FIXME: the probabilities in the returned 
--   grammar may be meaningless.
makeSimpleSRG :: Options   -- ^ Grammar options
	      -> StateGrammar
	      -> SRG
makeSimpleSRG opt s =
      SRG { grammarName = name,
	    startCat = lookupFM_ names origStart,
	    origStartCat = origStart,
            grammarLanguage = l,
	    rules = rs }
    where 
    opts = addOptions opt (stateOptions s)
    name = prIdent (cncId s)
    origStart = getStartCatCF opts s
    probs = stateProbs s
    l = fmap (replace '_' '-') $ getOptVal opts speechLanguage
    (cats,cfgRules) = unzip $ preprocess $ cfgToCFRules s
    preprocess = removeLeftRecursion origStart 
                 . removeEmptyCats 
                 . topDownFilter origStart
                 . removeIdenticalRules 
                 . removeCycles
    names = mkCatNames name cats
    rs = map (cfgRulesToSRGRule names probs) cfgRules

-- FIXME: merge alternatives with same rhs and profile but different probabilities
cfgRulesToSRGRule :: Map String String -> Probs -> [CFRule_] -> SRGRule
cfgRulesToSRGRule names probs rs@(r:_) = SRGRule cat origCat rhs
    where 
      origCat = lhsCat r
      cat = lookupFM_ names origCat
      rhs = nub $ map ruleToAlt rs
      ruleToAlt r@(CFRule c ss n) 
          = SRGAlt (ruleProb probs r) n (mkSRGSymbols 0 ss)
            where
              mkSRGSymbols _ [] = []
              mkSRGSymbols i (Cat c:ss) = Cat (renameCat c,i) : mkSRGSymbols (i+1) ss
              mkSRGSymbols i (Tok t:ss) = Tok t : mkSRGSymbols i ss
      renameCat = lookupFM_ names

ruleProb :: Probs -> CFRule_ -> Maybe Double
ruleProb probs r = lookupProb probs (ruleFun r)

-- FIXME: move to GF.Probabilistic.Probabilistic?
lookupProb :: Probs -> Ident -> Maybe Double
lookupProb probs i = lookupTree prIdent i probs

mkCatNames :: String   -- ^ Category name prefix
	   -> [String] -- ^ Original category names
	   -> Map String String -- ^ Maps original names to SRG names
mkCatNames prefix origNames = Map.fromList (zip origNames names)
    where names = [prefix ++ "_" ++ show x | x <- [0..]]


allSRGCats :: SRG -> [String]
allSRGCats SRG { rules = rs } = [c | SRGRule c _ _ <- rs]

cfgCatToGFCat :: SRGCat -> Maybe String
cfgCatToGFCat c 
    -- categories introduced by removeLeftRecursion contain dashes
    | '-' `elem` c = Nothing 
    -- some categories introduced by -conversion=finite have the form
    -- "{fun:cat}..."
    | "{" `isPrefixOf` c = case dropWhile (/=':') $ takeWhile (/='}') $ tail c of
                             ':':c' -> Just c'
                             _ -> error $ "cfgCatToGFCat: Strange category " ++ show c
    | otherwise = Just $ takeWhile (/='{') c

srgTopCats :: SRG -> [(String,[SRGCat])]
srgTopCats srg = buildMultiMap [(oc, cat) | SRGRule cat origCat _ <- rules srg, 
                                            oc <- maybeToList $ cfgCatToGFCat origCat]

--
-- * Size-optimized EBNF SRGs
--

data EBnfSRGAlt = EBnfSRGAlt (Maybe Double) CFTerm EBnfSRGItem
	     deriving (Eq,Show)

type EBnfSRGItem = RE (Symbol SRGNT Token)


ebnfSRGAlts :: [SRGAlt] -> [EBnfSRGAlt]
ebnfSRGAlts alts = [EBnfSRGAlt p n (ebnfSRGItem sss) 
                    | ((n,p),sss) <- buildMultiMap [((n,p),ss) | SRGAlt p n ss <- alts]]

ebnfSRGItem :: [[Symbol SRGNT Token]] -> EBnfSRGItem
ebnfSRGItem = unionRE . map mergeItems . sortGroupBy (compareBy filterCats)

-- | Merges a list of right-hand sides which all have the same 
-- sequence of non-terminals.
mergeItems :: [[Symbol SRGNT Token]] -> EBnfSRGItem
mergeItems = minimizeRE . ungroupTokens . minimizeRE . unionRE . map seqRE . map groupTokens

groupTokens :: [Symbol SRGNT Token] -> [Symbol SRGNT [Token]]
groupTokens [] = []
groupTokens (Tok t:ss) = case groupTokens ss of
                           Tok ts:ss' -> Tok (t:ts):ss'
                           ss'        -> Tok [t]:ss'
groupTokens (Cat c:ss) = Cat c : groupTokens ss

ungroupTokens :: RE (Symbol SRGNT [Token]) -> RE (Symbol SRGNT Token)
ungroupTokens = joinRE . mapRE (symbol (RESymbol . Cat) (REConcat . map (RESymbol . Tok)))

--
-- * Utilities for building and printing SRGs
--

lookupFM_ :: (Ord key, Show key) => Map key elt -> key -> elt
lookupFM_ fm k = Map.findWithDefault (error $ "Key not found: " ++ show k) k fm

prtS :: Print a => a -> ShowS
prtS = showString . prt