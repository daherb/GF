----------------------------------------------------------------------
-- |
-- Module      : (Module)
-- Maintainer  : Aarne Ranta
-- Stability   : (stable)
-- Portability : (portable)
--
-- > CVS $Date $ 
-- > CVS $Author $
-- > CVS $Revision $
--
-- Optimizations on GF source code: sharing, parametrization, value sets.
-----------------------------------------------------------------------------

module BackOpt (shareModule, OptSpec, shareOpt, paramOpt, valOpt, allOpt) where

import Grammar
import Ident
import qualified Macros as C
import Operations
import List
import qualified Modules as M

-- optimization: sharing branches in tables. AR 25/4/2003
-- following advice of Josef Svenningsson

type OptSpec = [Integer] ---
doOptFactor opt = elem 2 opt
doOptValues opt = elem 3 opt
shareOpt = []
paramOpt = [2]
valOpt = [3]
allOpt = [2,3]

shareModule :: OptSpec -> (Ident, SourceModInfo) -> (Ident, SourceModInfo)
shareModule opt (i,m) = case m of
  M.ModMod (M.Module mt st fs me ops js) -> 
    (i,M.ModMod (M.Module mt st fs me ops (mapTree (shareInfo opt) js)))
  _ -> (i,m)

shareInfo opt (c, CncCat ty (Yes t) m) = (c, CncCat ty (Yes (shareOptim opt t)) m)
shareInfo opt (c, CncFun kxs (Yes t) m) = (c, CncFun kxs (Yes (shareOptim opt t)) m)
shareInfo opt (c, ResOper ty (Yes t)) = (c, ResOper ty (Yes (shareOptim opt t)))
shareInfo _ i = i

-- the function putting together optimizations
shareOptim :: OptSpec -> Term -> Term
shareOptim opt 
  | doOptFactor opt && doOptValues opt = values . factor 0
  | doOptFactor opt = share . factor 0
  | doOptValues opt = values    
  | otherwise = share

-- we need no counter to create new variable names, since variables are 
-- local to tables (only true in GFC) ---

share :: Term -> Term
share t = case t of
  T ty@(TComp _) cs -> shareT ty [(p, share v) | (p, v) <- cs]
  _ -> C.composSafeOp share t

 where
   shareT ty = finalize ty . groupC . sortC
 
   sortC :: [(Patt,Term)] -> [(Patt,Term)]
   sortC = sortBy $ \a b -> compare (snd a) (snd b)

   groupC :: [(Patt,Term)] -> [[(Patt,Term)]]
   groupC = groupBy $ \a b -> snd a == snd b

   finalize :: TInfo -> [[(Patt,Term)]] -> Term
   finalize ty css = TSh ty [(map fst ps, t) | ps@((_,t):_) <- css]

-- do even more: factor parametric branches

factor :: Int -> Term -> Term
factor i t = case t of
  T _ [_] -> t
  T _ []  -> t
  T (TComp ty) cs -> 
    T (TTyped ty) $ factors i [(p, factor (i+1) v) | (p, v) <- cs]
  _ -> C.composSafeOp (factor i) t
 where

   factors i psvs =   -- we know psvs has at least 2 elements
     let p   = qqIdent i
         vs' = map (mkFun p) psvs
     in if   allEqs vs'
        then mkCase p vs' 
        else psvs

   mkFun p (patt, val) = replace (C.patt2term patt) (Vr p) val

   allEqs (v:vs) = all (==v) vs

   mkCase p (v:_) = [(PV p, v)]

--- we hope this will be fresh and don't check... in GFC would be safe

qqIdent i = identC ("q4q__" ++ show i)


--  we need to replace subterms

replace :: Term -> Term -> Term -> Term
replace old new trm = case trm of
  
  -- these are the important cases, since they can correspond to patterns  
  QC _ _   | trm == old -> new
  App t ts | trm == old -> new
  App t ts              -> App (repl t) (repl ts)
  R _ | isRec && trm == old -> new
  _ -> C.composSafeOp repl trm
 where
   repl = replace old new
   isRec = case trm of
     R _ -> True
     _ -> False

-- It is very important that this is performed only after case
-- expansion since otherwise the order and number of values can
-- be incorrect. Guaranteed by the TComp flag.

values :: Term -> Term
values t = case t of
  T ty [(ps,t)]   -> T ty [(ps,values t)] -- don't destroy parametrization
  T (TComp ty) cs -> V ty [values t | (_, t) <- cs]
  _ -> C.composSafeOp values t
