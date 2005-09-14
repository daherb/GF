----------------------------------------------------------------------
-- |
-- Module      : SRG
-- Maintainer  : BB
-- Stability   : (stable)
-- Portability : (portable)
--
-- > CVS $Date: 2005/09/14 15:17:30 $ 
-- > CVS $Author: bringert $
-- > CVS $Revision: 1.17 $
--
-- Representation of, conversion to, and utilities for 
-- printing of a general Speech Recognition Grammar. 
--
-- FIXME: remove \/ warn \/ fail if there are int \/ string literal
-- categories in the grammar
--
-- FIXME: figure out name prefix from grammar name
-----------------------------------------------------------------------------

module GF.Speech.SRG where

import GF.Data.Utilities
import GF.Infra.Ident
import GF.Formalism.CFG
import GF.Formalism.Utilities (Symbol(..))
import GF.Conversion.Types
import GF.Infra.Print
import GF.Speech.TransformCFG
import GF.Infra.Option

import Data.List
import Data.Maybe (fromMaybe)
import Data.FiniteMap


data SRG = SRG { grammarName :: String    -- ^ grammar name
		 , startCat :: String     -- ^ start category name
		 , origStartCat :: String -- ^ original start category name
	         , rules :: [SRGRule] 
	       }
data SRGRule = SRGRule String String [SRGAlt] -- ^ SRG category name, original category name
	                                      --   and productions
type SRGAlt = [Symbol String Token]

-- | SRG category name and original name
type CatName = (String,String) 

type CatNames = FiniteMap String String

makeSRG :: Ident     -- ^ Grammar name
	-> Options   -- ^ Grammar options
	-> CGrammar -- ^ A context-free grammar
	-> SRG
makeSRG i opts gr = SRG { grammarName = name,
			  startCat = lookupFM_ names origStart,
			  origStartCat = origStart,
			  rules = map (cfgRulesToSRGRule names) cfgRules }
    where 
    name = prIdent i
    origStart = getStartCat opts
    gr' = removeLeftRecursion $ removeIdenticalRules $ removeEmptyCats $ cfgToCFRules gr
    (cats,cfgRules) = unzip gr'
    names = mkCatNames name cats

cfgRulesToSRGRule :: FiniteMap String String -> [CFRule_] -> SRGRule
cfgRulesToSRGRule names rs@(r:_) = SRGRule cat origCat rhs
    where origCat = lhsCat r
	  cat = lookupFM_ names origCat
	  rhs = nub $ map (map renameCat . ruleRhs) rs
	  renameCat (Cat c) = Cat (lookupFM_ names c)
	  renameCat t = t

mkCatNames :: String   -- ^ Category name prefix
	   -> [String] -- ^ Original category names
	   -> FiniteMap String String -- ^ Maps original names to SRG names
mkCatNames prefix origNames = listToFM (zip origNames names)
    where names = [prefix ++ "_" ++ show x | x <- [0..]]

--
-- * Utilities for building and printing SRGs
--

lookupFM_ :: (Ord key, Show key) => FiniteMap key elt -> key -> elt
lookupFM_ fm k = lookupWithDefaultFM fm (error $ "Key not found: " ++ show k) k

prtS :: Print a => a -> ShowS
prtS = showString . prt