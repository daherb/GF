----------------------------------------------------------------------
-- |
-- Module      : Compute
-- Maintainer  : AR
-- Stability   : (stable)
-- Portability : (portable)
--
-- > CVS $Date: 2005/11/01 15:39:12 $ 
-- > CVS $Author: aarne $
-- > CVS $Revision: 1.19 $
--
-- Computation of source terms. Used in compilation and in @cc@ command.
-----------------------------------------------------------------------------

module GF.Grammar.Compute (computeConcrete, computeTerm,computeConcreteRec) where

import GF.Data.Operations
import GF.Grammar.Grammar
import GF.Infra.Ident
import GF.Infra.Option
import GF.Data.Str
import GF.Grammar.PrGrammar
import GF.Infra.Modules
import GF.Grammar.Macros
import GF.Grammar.Lookup
import GF.Grammar.Refresh
import GF.Grammar.PatternMatch
import GF.Grammar.Lockfield (isLockLabel) ----

import GF.Grammar.AppPredefined

import Data.List (nub,intersperse)
import Control.Monad (liftM2, liftM)

-- | computation of concrete syntax terms into normal form
-- used mainly for partial evaluation
computeConcrete :: SourceGrammar -> Term -> Err Term
computeConcrete    g t = {- refreshTerm t >>= -} computeTerm g [] t
computeConcreteRec g t = {- refreshTerm t >>= -} computeTermOpt True g [] t

computeTerm :: SourceGrammar -> Substitution -> Term -> Err Term
computeTerm = computeTermOpt False

-- rec=True is used if it cannot be assumed that looked-up constants
-- have already been computed (mainly with -optimize=noexpand in .gfr)

computeTermOpt :: Bool -> SourceGrammar -> Substitution -> Term -> Err Term
computeTermOpt rec gr = comp where

   comp g t = ---- errIn ("subterm" +++ prt t) $ --- for debugging 
              case t of

     Q (IC "Predef") _ -> return t
     Q p c -> look p c 

     -- if computed do nothing
     Computed t' -> return $ unComputed t'

     Vr x -> do
       t' <- maybe (prtBad ("no value given to variable") x) return $ lookup x g
       case t' of 
         _ | t == t' -> return t
         _ -> comp g t'

     Abs x b -> do 
       b' <- comp (ext x (Vr x) g) b
       return $ Abs x b'

     Let (x,(_,a)) b -> do
       a' <- comp g a
       comp (ext x a' g) b

     Prod x a b -> do
       a' <- comp g a
       b' <- comp (ext x (Vr x) g) b
       return $ Prod x a' b'

     -- beta-convert
     App f a -> do
       f' <- comp g f
       a' <- comp g a
       case (f',a') of
         (Abs x b, FV as) -> 
           mapM (\c -> comp (ext x c g) b) as >>= return . variants
         (_, FV as)  -> mapM (\c -> comp g (App f' c)) as >>= return . variants
         (FV fs, _)  -> mapM (\c -> comp g (App c a')) fs >>= return . variants
         (Abs x b,_) -> comp (ext x a' g) b
         (QC _ _,_)  -> returnC $ App f' a'

         (Alias _ _ d, _) -> comp g (App d a')

         (S (T i cs) e,_) -> prawitz g i (flip App a') cs e
         (S (V i cs) e,_) -> prawitzV g i (flip App a') cs e

	 _ -> do
           (t',b) <- appPredefined (App f' a')
           if b then return t' else comp g t'

     P t l | isLockLabel l -> return $ R [] 
     ---- a workaround 18/2/2005: take this away and find the reason
     ---- why earlier compilation destroys the lock field


     P t l  -> do
       t' <- comp g t
       case t' of
         FV rs -> mapM (\c -> comp g (P c l)) rs >>= returnC . variants
         R r   -> maybe (prtBad "no value for label" l) (comp g . snd) $ 
                    lookup l $ reverse r 

         ExtR a (R b) ->                 
           case comp g (P (R b) l) of
             Ok v -> return v
             _ -> comp g (P a l)

--- { - --- this is incorrect, since b can contain the proper value
         ExtR (R a) b ->                 -- NOT POSSIBLE both a and b records!
           case comp g (P (R a) l) of
             Ok v -> return v
             _ -> comp g (P b l)
--- - } ---

         Alias _ _ r -> comp g (P r l)

         S (T i cs) e -> prawitz g i (flip P l) cs e
         S (V i cs) e -> prawitzV g i (flip P l) cs e

         _   -> returnC $ P t' l

     PI t l i -> comp g $ P t l -----

     S t@(T ti cc) v -> do
       v'     <- comp g v
       case v' of
         FV vs -> do
           ts' <- mapM (comp g . S t) vs
           return $ variants ts' 
         _ -> case ti of
{-
           TComp _  -> do
             case term2patt v' of
               Ok p' -> case lookup p' cc of
                 Just u -> comp g u
                 _ -> do
                   t' <- comp g t
                   return $ S t' v' -- if v' is not canonical
               _ -> do
                  t' <- comp g t
                  return $ S t' v'
-}
           _ -> case matchPattern cc v' of
             Ok (c,g') -> comp (g' ++ g) c
             _ | isCan v' -> prtBad ("missing case" +++ prt v' +++ "in") t 
             _ -> do
               t' <- comp g t
               return $ S t' v' -- if v' is not canonical


     S t v -> do

      t'     <- case t of
--        T _ _ -> return t
--        V _ _ -> return t
        _ -> comp g t

      v'     <- comp g v

      case v' of
       FV vs -> mapM (\c -> comp g (S t' c)) vs >>= returnC . variants        
       _ -> case t' of
         FV ccs -> mapM (\c -> comp g (S c v')) ccs >>= returnC . variants

         T _ [(PV IW,c)] -> comp g c           --- an optimization
         T _ [(PT _ (PV IW),c)] -> comp g c

         T _ [(PV z,c)] -> comp (ext z v' g) c --- another optimization
         T _ [(PT _ (PV z),c)] -> comp (ext z v' g) c

         -- course-of-values table: look up by index, no pattern matching needed
         V ptyp ts -> do
           vs <- allParamValues gr ptyp
           case lookup v' (zip vs [0 .. length vs - 1]) of
             Just i -> comp g $ ts !! i
-----             _ -> prtBad "selection" $ S t' v' -- debug
             _ -> return $ S t' v' -- if v' is not canonical

         T (TComp _) cs -> do
           case term2patt v' of
             Ok p' -> case lookup p' cs of
               Just u -> comp g u
               _ -> return $ S t' v' -- if v' is not canonical
             _ -> return $ S t' v'

         T _ cc -> case matchPattern cc v' of
             Ok (c,g') -> comp (g' ++ g) c
             _ | isCan v' -> prtBad ("missing case" +++ prt v' +++ "in") t 
             _ -> return $ S t' v' -- if v' is not canonical

         Alias _ _ d -> comp g (S d v')

         S (T i cs) e -> prawitz g i (flip S v') cs e
         S (V i cs) e -> prawitzV g i (flip S v') cs e
         _    -> returnC $ S t' v'

     -- normalize away empty tokens
     K "" -> return Empty

     -- glue if you can
     Glue x0 y0 -> do
       x <- comp g x0
       y <- comp g y0
       case (x,y) of
         (FV ks,_)         -> do
           kys <- mapM (comp g . flip Glue y) ks
           return $ variants kys
         (_,FV ks)         -> do
           xks <- mapM (comp g . Glue x) ks
           return $ variants xks

         (Alias _ _ d, y)  -> comp g $ Glue d y
         (x, Alias _ _ d)  -> comp g $ Glue x d

         (S (T i cs) e, s) -> prawitz g i (flip Glue s) cs e
         (s, S (T i cs) e) -> prawitz g i (Glue s) cs e
         (S (V i cs) e, s) -> prawitzV g i (flip Glue s) cs e
         (s, S (V i cs) e) -> prawitzV g i (Glue s) cs e
         (_,Empty)         -> return x
         (Empty,_)         -> return y
         (K a, K b)        -> return $ K (a ++ b)
         (_, Alts (d,vs)) -> do
----         (K a, Alts (d,vs)) -> do
            let glx = Glue x
            comp g $ Alts (glx d, [(glx v,c) | (v,c) <- vs])
         (Alts _, ka) -> checks [do
            y' <- strsFromTerm ka
----         (Alts _, K a) -> checks [do
            x' <- strsFromTerm x -- this may fail when compiling opers
            return $ variants [
              foldr1 C (map K (str2strings (glueStr v u))) | v <- x', u <- y']
----              foldr1 C (map K (str2strings (glueStr v (str a)))) | v <- x']
           ,return $ Glue x y
           ]
         (C u v,_) -> comp g $ C u (Glue v y)

         _ -> do
           mapM_ checkNoArgVars [x,y]
           r <- composOp (comp g) t
           returnC r

     Alts _ -> do
       r <- composOp (comp g) t
       returnC r

     -- remove empty
     C a b    -> do
       a' <- comp g a
       b' <- comp g b
       case (a',b') of
         (Alts _, K a) -> checks [do
            as <- strsFromTerm a' -- this may fail when compiling opers
            return $ variants [
              foldr1 C (map K (str2strings (plusStr v (str a)))) | v <- as]
            ,
            return $ C a' b'
           ]
         (Empty,_) -> returnC b'
         (_,Empty) -> returnC a'
         _     -> returnC $ C a' b'

     -- reduce free variation as much as you can
     FV ts -> mapM (comp g) ts >>= returnC . variants

     -- merge record extensions if you can
     ExtR r s -> do
       r' <- comp g r
       s' <- comp g s
       case (r',s') of
         (Alias _ _ d, _)  -> comp g $ ExtR d s'
         (_, Alias _ _ d)  -> comp g $ Glue r' d

         (R rs, R ss) -> plusRecord r' s'
         (RecType rs, RecType ss) -> plusRecType r' s'
         _ -> return $ ExtR r' s'

     -- case-expand tables
     -- if already expanded, don't expand again
     T i@(TComp ty) cs -> do
       -- if there are no variables, don't even go inside
       cs' <- if (null g) then return cs else mapPairsM (comp g) cs
----       return $ V ty (map snd cs')
       return $ T i cs'
     --- this means some extra work; should implement TSh directly
     TSh i cs -> comp g $ T i [(p,v) | (ps,v) <- cs, p <- ps]

     T i cs -> do
       pty0 <- getTableType i
       ptyp <- comp g pty0
       case allParamValues gr ptyp of
         Ok vs -> do

           cs'  <- mapM (compBranchOpt g) cs
           sts  <- mapM (matchPattern cs') vs 
           ts   <- mapM (\ (c,g') -> comp (g' ++ g) c) sts
           ps   <- mapM term2patt vs
           let ps' = ps --- PT ptyp (head ps) : tail ps
----           return $ V ptyp ts -- to save space, just course of values
           return $ T (TComp ptyp) (zip ps' ts)
         _ -> do
           cs' <- mapM (compBranch g) cs
           return $ T i cs'  -- happens with variable types

     Alias c a d -> do
       d' <- comp g d
       return $ Alias c a d'  -- alias only disappears in certain redexes

     -- otherwise go ahead
     _ -> composOp (comp g) t >>= returnC

    where

     look p c
       | rec       = lookupResDef gr p c >>= comp []
       | otherwise = lookupResDef gr p c

{-
     look p c = case lookupResDefKind gr p c of
       Ok (t,_) | noExpand p || rec -> comp [] t
       Ok (t,_) -> return t
       Bad s -> raise s

     noExpand p = errVal False $ do
       mo <- lookupModMod gr p
       return $ case getOptVal (iOpts (flags mo)) useOptimizer of
         Just "noexpand" -> True
         _ -> False
-}

     ext x a g = (x,a):g

     returnC = return --- . computed

     variants ts = case nub ts of
       [t] -> t
       ts  -> FV ts

     isCan v = case v of
       Con _    -> True
       QC _ _   -> True
       App f a  -> isCan f && isCan a
       R rs     -> all (isCan . snd . snd) rs
       _        -> False

     compBranch g (p,v) = do
       let g' = contP p ++ g
       v' <- comp g' v
       return (p,v')

     compBranchOpt g c@(p,v) = case contP p of
       [] -> return c
       _ -> err (const (return c)) return $ compBranch g c

     contP p = case p of
       PV x -> [(x,Vr x)]
       PC _ ps -> concatMap contP ps
       PP _ _ ps -> concatMap contP ps
       PT _ p -> contP p
       PR rs -> concatMap (contP . snd) rs

       PAs x p -> (x,Vr x) : contP p

       PSeq p q -> concatMap contP [p,q]
       PAlt p q -> concatMap contP [p,q]
       PRep p   -> contP p
       PNeg p   -> contP p

       _ -> []

     prawitz g i f cs e = do
       cs' <- mapM (compBranch g) [(p, f v) | (p,v) <- cs]
       return $ S (T i cs') e
     prawitzV g i f cs e = do
       cs' <- mapM (comp g) [(f v) | v <- cs]
       return $ S (V i cs') e

-- | argument variables cannot be glued
checkNoArgVars :: Term -> Err Term
checkNoArgVars t = case t of
  Vr (IA _)  -> Bad $ glueErrorMsg $ prt t 
  Vr (IAV _) -> Bad $ glueErrorMsg $ prt t 
  _ -> composOp checkNoArgVars t

glueErrorMsg s = 
  "Cannot glue (+) term with run-time variable" +++ s ++ "." ++++
  "Use Prelude.bind instead."
