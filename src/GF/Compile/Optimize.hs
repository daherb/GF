{-# LANGUAGE PatternGuards #-}
----------------------------------------------------------------------
-- |
-- Module      : Optimize
-- Maintainer  : AR
-- Stability   : (stable)
-- Portability : (portable)
--
-- > CVS $Date: 2005/09/16 13:56:13 $ 
-- > CVS $Author: aarne $
-- > CVS $Revision: 1.18 $
--
-- Top-level partial evaluation for GF source modules.
-----------------------------------------------------------------------------

module GF.Compile.Optimize (optimizeModule) where

import GF.Grammar.Grammar
import GF.Infra.Ident
import GF.Infra.Modules
import GF.Grammar.Printer
import GF.Grammar.Macros
import GF.Grammar.Lookup
import GF.Grammar.Predef
import GF.Compile.Refresh
import GF.Compile.Concrete.Compute
import GF.Compile.BackOpt
import GF.Compile.CheckGrammar
import GF.Compile.Update

import GF.Data.Operations
import GF.Infra.CheckM
import GF.Infra.Option

import Control.Monad
import Data.List
import qualified Data.Set as Set
import Text.PrettyPrint
import Debug.Trace


-- | partial evaluation of concrete syntax. AR 6\/2001 -- 16\/5\/2003 -- 5\/2\/2005.

optimizeModule :: Options -> [SourceModule] -> SourceModule -> Err SourceModule
optimizeModule opts ms m@(name,mi)
  | mstatus mi == MSComplete = do
      ids <- topoSortJments m
      mi <- foldM updateEvalInfo mi ids
      return (shareModule oopts (name,mi))
  | otherwise = return m
 where
   oopts = opts `addOptions` flagsModule m

   updateEvalInfo mi (i,info) = do
     info' <- evalInfo oopts ms (name,mi) i info
     return (updateModule mi i info')

evalInfo :: Options -> [SourceModule] -> SourceModule -> Ident -> Info -> Err Info
evalInfo opts ms m c info = do

 (if verbAtLeast opts Verbose then trace (" " ++ showIdent c) else id) return ()

 errIn ("optimizing " ++ showIdent c) $ case info of

  CncCat ptyp pde ppr -> do
    pde' <- case (ptyp,pde) of
      (Just typ, Just de) -> 
        liftM Just $ partEval opts gr ([(Explicit, varStr, typeStr)], typ) de
      (Just typ, Nothing) -> 
        liftM Just $ mkLinDefault gr typ >>= partEval noOptions gr ([(Explicit, varStr, typeStr)],typ)
      _ -> return pde   -- indirection

    ppr' <- liftM Just $ evalPrintname gr c ppr (Just $ K $ showIdent c)

    return (CncCat ptyp pde' ppr')

  CncFun (mt@(Just (_,cont,val))) pde ppr -> --trace (prt c) $
       eIn (text "linearization in type" <+> ppTerm Unqualified 0 (mkProd cont val []) $$ text "of function") $ do
    pde' <- case pde of
      Just de -> liftM Just $ partEval opts gr (cont,val) de
      Nothing -> return pde
    ppr' <-  liftM Just $ evalPrintname gr c ppr pde'
    return $ CncFun mt pde' ppr' -- only cat in type actually needed

  ResOper pty pde 
    | OptExpand `Set.member` optim -> do
         pde' <- case pde of
                   Just de -> liftM Just $ computeConcrete gr de 
                   Nothing -> return Nothing
         return $ ResOper pty pde'

  _ ->  return info
 where
   gr = MGrammar (m : ms)
   optim = flag optOptimizations opts
   eIn cat = errIn (render (text "Error optimizing" <+> cat <+> ppIdent c <+> colon))

-- | the main function for compiling linearizations
partEval :: Options -> SourceGrammar -> (Context,Type) -> Term -> Err Term
partEval opts gr (context, val) trm = errIn (render (text "partial evaluation" <+> ppTerm Qualified 0 trm)) $ do
  let vars  = map (\(bt,x,t) -> x) context
      args  = map Vr vars
      subst = [(v, Vr v) | v <- vars]
      trm1 = mkApp trm args
  trm2 <- computeTerm gr subst trm1
  trm3 <- if rightType trm2
            then computeTerm gr subst trm2
            else recordExpand val trm2 >>= computeTerm gr subst
  return $ mkAbs [(Explicit,v) | v <- vars] trm3
  where
    -- don't eta expand records of right length (correct by type checking)
    rightType (R rs) = case val of
                         RecType ts -> length rs == length ts
                         _          -> False
    rightType _      = False




-- here we must be careful not to reduce
--   variants {{s = "Auto" ; g = N} ; {s = "Wagen" ; g = M}}
--   {s  = variants {"Auto" ; "Wagen"} ; g  = variants {N ; M}} ;

recordExpand :: Type -> Term -> Err Term
recordExpand typ trm = case typ of
  RecType tys -> case trm of
    FV rs -> return $ FV [R [assign lab (P r lab) | (lab,_) <- tys] | r <- rs]
    _ -> return $ R [assign lab (P trm lab) | (lab,_) <- tys]
  _ -> return trm


-- | auxiliaries for compiling the resource

mkLinDefault :: SourceGrammar -> Type -> Err Term
mkLinDefault gr typ = do
  case typ of
    RecType lts -> mapPairsM mkDefField lts >>= (return . Abs Explicit varStr . R . mkAssign)
    _ -> liftM (Abs Explicit varStr) $ mkDefField typ
----    _ -> prtBad "linearization type must be a record type, not" typ
 where
   mkDefField typ = case typ of
     Table p t  -> do
       t' <- mkDefField t
       let T _ cs = mkWildCases t'
       return $ T (TWild p) cs 
     Sort s | s == cStr -> return $ Vr varStr
     QC q p             -> do vs <- lookupParamValues gr q p
                              case vs of
                                v:_ -> return v
                                _   -> Bad (render (text "no parameter values given to type" <+> ppIdent p))
     RecType r  -> do
       let (ls,ts) = unzip r
       ts' <- mapM mkDefField ts
       return $ R $ [assign l t | (l,t) <- zip ls ts']
     _ | Just _ <- isTypeInts typ -> return $ EInt 0 -- exists in all as first val
     _ -> Bad (render (text "linearization type field cannot be" <+> ppTerm Unqualified 0 typ))

-- | Form the printname: if given, compute. If not, use the computed
-- lin for functions, cat name for cats (dispatch made in evalCncDef above).
--- We cannot use linearization at this stage, since we do not know the
--- defaults we would need for question marks - and we're not yet in canon.
evalPrintname :: SourceGrammar -> Ident -> Maybe Term -> Maybe Term -> Err Term
evalPrintname gr c ppr lin =
  case ppr of
    Just pr -> comp pr
    Nothing -> case lin of
                 Just t  -> return $ K $ clean $ render (ppTerm Unqualified 0 (oneBranch t))
                 Nothing -> return $ K $ showIdent c ----
 where
   comp = computeConcrete gr

   oneBranch t = case t of
     Abs _ _ b -> oneBranch b
     R   (r:_) -> oneBranch $ snd $ snd r
     T _ (c:_) -> oneBranch $ snd c
     V _ (c:_) -> oneBranch c
     FV  (t:_) -> oneBranch t
     C x y     -> C (oneBranch x) (oneBranch y)
     S x _     -> oneBranch x
     P x _     -> oneBranch x
     Alts (d,_) -> oneBranch d
     _ -> t

  --- very unclean cleaner
   clean s = case s of
     '+':'+':' ':cs -> clean cs
     '"':cs -> clean cs
     c:cs -> c: clean cs
     _ -> s

