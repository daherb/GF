----------------------------------------------------------------------
-- |
-- Maintainer  : Krasimir Angelov
-- Stability   : (stable)
-- Portability : (portable)
--
-- FCFG parsing
-----------------------------------------------------------------------------

module GF.Parsing.FCFG
    (parseFCF, module GF.Parsing.FCFG.PInfo) where

import GF.Data.Operations (Err(..))

import GF.Formalism.Utilities
import GF.Formalism.GCFG
import GF.Formalism.MCFG
import GF.Parsing.FCFG.PInfo

import qualified GF.Parsing.FCFG.Active as Active
import GF.Infra.Print

----------------------------------------------------------------------
-- parsing

parseFCF :: (Print c, Ord c, Ord n, Print t, Ord t) => String -> Err (FCFParser c n t)
parseFCF prs | prs `elem` strategies = Ok $ parseFCF' prs
	     | otherwise = Bad $ "FCFG parsing strategy not defined: " ++ prs 

strategies = words "bottomup topdown"

parseFCF' :: (Print c, Ord c, Ord n, Print t, Ord t) => String -> FCFParser c n t
parseFCF' "bottomup" pinfo starts toks = Active.parse "b" pinfo starts toks 
parseFCF' "topdown"  pinfo starts toks = Active.parse "t" pinfo starts toks 
