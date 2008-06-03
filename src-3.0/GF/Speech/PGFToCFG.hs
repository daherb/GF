----------------------------------------------------------------------
-- |
-- Module      : GF.Speech.PGFToCFG
--
-- Approximates PGF grammars with context-free grammars.
----------------------------------------------------------------------
module GF.Speech.PGFToCFG (pgfToCFG) where

import PGF.CId
import PGF.Data as PGF
import PGF.Macros
import GF.Infra.Ident
import GF.Speech.CFG

import Data.Array as Array
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set


pgfToCFG :: PGF 
          -> CId   -- ^ Concrete syntax name
          -> CFG
pgfToCFG pgf lang = mkCFG (lookStartCat pgf) extCats (startRules ++ concatMap fruleToCFRule rules)
  where
    pinfo = fromMaybe (error "pgfToCFG: No parser.") (lookParser pgf lang)

    rules :: [FRule]
    rules = Array.elems (PGF.allRules pinfo)

    fcatGFCats :: Map FCat CId
    fcatGFCats = Map.fromList [(fc,c) | (c,fcs) <- Map.toList (startupCats pinfo), fc <- fcs]
    
    fcatGFCat :: FCat -> CId
    fcatGFCat c = fromMaybe (mkCId "Unknown") (Map.lookup c fcatGFCats)

    fcatToCat :: FCat -> FIndex -> Cat
    fcatToCat c l = prCId (fcatGFCat c) ++ "_" ++ show c ++ "_" ++ show l

    extCats :: Set Cat
    extCats = Set.fromList $ map lhsCat startRules

    -- NOTE: this is only correct for cats that have a lincat with exactly one row.
    startRules :: [CFRule]
    startRules = [CFRule (prCId c) [NonTerminal (fcatToCat fc 0)] (CFRes 0) 
                      | (c,fcs) <- Map.toList (startupCats pinfo), fc <- fcs]

    fruleToCFRule :: FRule -> [CFRule]
    fruleToCFRule (FRule f ps args c rhs) = 
        [CFRule (fcatToCat c l) (mkRhs row) (profilesToTerm (map (fixProfile row) ps))
         | (l,row) <- Array.assocs rhs]
      where
        mkRhs :: Array FPointPos FSymbol -> [CFSymbol]
        mkRhs = map fsymbolToSymbol . Array.elems

        fsymbolToSymbol :: FSymbol -> CFSymbol
        fsymbolToSymbol (FSymCat l n) = NonTerminal (fcatToCat (args!!n) l)
        fsymbolToSymbol (FSymTok t) = Terminal t

        fixProfile :: Array FPointPos FSymbol -> Profile -> Profile
        fixProfile row = concatMap positions
            where
              nts = zip [0..] [nt | nt@(FSymCat _ _) <- Array.elems row ]
              positions i = [k | (k,FSymCat _ j) <- nts, j == i]

        profilesToTerm :: [Profile] -> CFTerm
        profilesToTerm [[n]] | f == wildCId = CFRes n
        profilesToTerm ps = CFObj f (zipWith profileToTerm argTypes ps)
            where (argTypes,_) = catSkeleton $ lookType pgf f

        profileToTerm :: CId -> Profile -> CFTerm
        profileToTerm t [] = CFMeta t
        profileToTerm _ xs = CFRes (last xs) -- FIXME: unify
