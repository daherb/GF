----------------------------------------------------------------------
-- |
-- Module      : Paraphrase
-- Maintainer  : AR
-- Stability   : (stable)
-- Portability : (portable)
--
-- Generate parapharases with def definitions.
-----------------------------------------------------------------------------

module PGF.Paraphrase (
  paraphrase,
  paraphraseN
  ) where

import PGF.Data
import PGF.Macros (lookDef,isData)
import PGF.Expr
import PGF.CId

import Data.List (nub,sort,group)
import qualified Data.Map as Map

import Debug.Trace ----

paraphrase :: PGF -> Tree -> [Tree]
paraphrase pgf = nub . paraphraseN 2 pgf

paraphraseN :: Int -> PGF -> Tree -> [Tree]
paraphraseN 0 _ t = [t]
paraphraseN i pgf t = 
  step i t ++ [Fun g ts' | Fun g ts <- step (i-1) t, ts' <- sequence (map par ts)]
 where
  par = paraphraseN (i-1) pgf 
  step 0 t = [t]
  step i t = let stept = step (i-1) t in stept ++ concat [def u | u <- stept]
  def = fromDef pgf

fromDef :: PGF -> Tree -> [Tree]
fromDef pgf t@(Fun f ts) = defDown t ++ defUp t where
  defDown t = [subst g u | let equ = equsFrom f, (u,g) <- match equ ts, trequ "U" f equ]
  defUp   t = [subst g u | equ <- equsTo   f, (u,g) <- match [equ] ts, trequ "D" f equ]

  equsFrom f = [(ps,d) | Just equs <- [lookup f equss], (Fun _ ps,d) <- equs]

  equsTo f  = [c | (_,equs) <- equss, c <- casesTo f equs]

  casesTo f equs = 
    [(ps,p) | (p,d@(Fun g ps)) <- equs, g==f, 
              isClosed d || (length equs == 1 && isLinear d)]

  equss = [(f,[(Fun f (map expr2tree ps), expr2tree d) | (Equ ps d) <- eqs]) | 
                       (f,(_,d)) <- Map.assocs (funs (abstract pgf)), eqs <- defs d]

  defs d = case d of
    EEq eqs -> [eqs]
    EMeta _ -> []
    _      -> [[Equ [] d]]

  trequ s f e = True ----trace (s ++ ": " ++ show f ++ "  " ++ show e) True

subst :: Subst -> Tree -> Tree
subst g e = case e of
  Fun f ts -> Fun f (map substg ts)
  Var x -> maybe e id $ lookup x g
  _ -> e
 where
  substg = subst g

type Subst = [(CId,Tree)]

-- this applies to pattern, hence don't need to consider abstractions
isClosed :: Tree -> Bool
isClosed t = case t of
  Fun _ ts -> all isClosed ts
  Var _ -> False
  _ -> True

-- this applies to pattern, hence don't need to consider abstractions
isLinear :: Tree -> Bool
isLinear = nodup . vars where
  vars t = case t of
    Fun _ ts -> concatMap vars ts
    Var x -> [x]
    _ -> []
  nodup = all ((<2) . length) . group . sort


-- special version of AbsCompute.findMatch, working on Tree

match :: [([Tree],Tree)] -> [Tree] -> [(Tree, Subst)]
match cases terms = case cases of
  [] -> []
  (patts,_):_ | length patts /= length terms -> []
  (patts,val):cc -> case mapM tryMatch (zip patts terms) of
     Just substs -> return (val, concat substs)
     _           -> match cc terms
 where  
  tryMatch (p,t) = case (p, t) of
    (Var x,     _) | notMeta t  -> return [(x,t)]
    (Fun p pp, Fun f tt) | p == f && length pp == length tt -> do
         matches <- mapM tryMatch (zip pp tt)
         return (concat matches)
    _ -> if p==t then return [] else Nothing

  notMeta e = case e of
    Meta _   -> False
    Fun f ts -> all notMeta ts  
    _ -> True

