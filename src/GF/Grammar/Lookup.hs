----------------------------------------------------------------------
-- |
-- Module      : Lookup
-- Maintainer  : AR
-- Stability   : (stable)
-- Portability : (portable)
--
-- > CVS $Date: 2005/10/27 13:21:53 $ 
-- > CVS $Author: aarne $
-- > CVS $Revision: 1.15 $
--
-- Lookup in source (concrete and resource) when compiling.
--
-- lookup in resource and concrete in compiling; for abstract, use 'Look'
-----------------------------------------------------------------------------

module GF.Grammar.Lookup (lookupResDef,
	       lookupResType, 
	       lookupParams, 
	       lookupParamValues, 
	       lookupFirstTag, 
	       allParamValues, 
	       lookupAbsDef, 
	       lookupLincat, 
	       opersForType
	      ) where

import GF.Data.Operations
import GF.Grammar.Abstract
import GF.Infra.Modules
import GF.Grammar.Lockfield

import Data.List (nub)
import Control.Monad

lookupResDef :: SourceGrammar -> Ident -> Ident -> Err Term
lookupResDef gr m c = look True m c where 
  look isTop m c = do
    mi   <- lookupModule gr m
    case mi of
      ModMod mo -> do
        info <- lookupIdentInfo mo c
        case info of
          ResOper _ (Yes t) -> return $ qualifAnnot m t 
          ResOper _ Nope    -> return (Q m c) ---- if isTop then lookExt m c 
                                 ---- else prtBad "cannot find in exts" c 

          CncCat (Yes ty) _ _ -> return ty ---- lockRecType c $ ty
          CncCat _ _ _        -> return defLinType ---- lockRecType c $ defLinType
          CncFun _ (Yes tr) _ -> return tr ---- unlockRecord c tr

          AnyInd _ n        -> look False n c
          ResParam _        -> return $ QC m c
          ResValue _        -> return $ QC m c
          _   -> Bad $ prt c +++ "is not defined in resource" +++ prt m
      _ -> Bad $ prt m +++ "is not a resource"
  lookExt m c =
    checks ([look False n c | n <- allExtensions gr m] ++ [return (Q m c)])

lookupResType :: SourceGrammar -> Ident -> Ident -> Err Type
lookupResType gr m c = do
  mi   <- lookupModule gr m
  case mi of
    ModMod mo -> do
      info <- lookupIdentInfo mo c
      case info of
        ResOper (Yes t) _ -> return $ qualifAnnot m t
        ResOper (May n) _ -> lookupResType gr n c

        -- used in reused concrete
        CncCat _ _ _ -> return typeType
        CncFun (Just (cat,(cont,val))) _ _ -> do
          val' <- return val ---- lockRecType cat val 
          return $ mkProd (cont, val', [])
        CncFun _ _ _ -> do
          a  <- abstractOfConcrete gr m
          mu <- lookupModMod gr a
          info <- lookupIdentInfo mu c
          case info of
            AbsFun (Yes ty) _ -> return $ redirectTerm m ty 
            AbsCat _ _ -> return typeType
            _ -> prtBad "cannot find type of reused function" c
        AnyInd _ n        -> lookupResType gr n c
        ResParam _        -> return $ typePType
        ResValue (Yes t)  -> return $ qualifAnnotPar m t
        _   -> Bad $ prt c +++ "has no type defined in resource" +++ prt m
    _ -> Bad $ prt m +++ "is not a resource"

lookupParams :: SourceGrammar -> Ident -> Ident -> Err [Param]
lookupParams gr = look True where 
  look isTop m c = do
    mi   <- lookupModule gr m
    case mi of
      ModMod mo -> do
        info <- lookupIdentInfo mo c
        case info of
          ResParam (Yes ps) -> return ps
          ---- ResParam   Nope   -> if isTop then lookExt m c 
          ----                       else prtBad "cannot find params in exts" c 
          AnyInd _ n        -> look False n c
          _   -> Bad $ prt c +++ "has no parameters defined in resource" +++ prt m
      _ -> Bad $ prt m +++ "is not a resource"
  lookExt m c =
    checks [look False n c | n <- allExtensions gr m]

lookupParamValues :: SourceGrammar -> Ident -> Ident -> Err [Term]
lookupParamValues gr m c = do
  ps <- lookupParams gr m c
  liftM concat $ mapM mkPar ps
 where
   mkPar (f,co) = do
     vs <- liftM combinations $ mapM (\ (_,ty) -> allParamValues gr ty) co
     return $ map (mkApp (QC m f)) vs

lookupFirstTag :: SourceGrammar -> Ident -> Ident -> Err Term
lookupFirstTag gr m c = do
  vs <- lookupParamValues gr m c
  case vs of
    v:_ -> return v
    _ -> prtBad "no parameter values given to type" c

allParamValues :: SourceGrammar -> Type -> Err [Term]
allParamValues cnc ptyp = case ptyp of
     App (Q (IC "Predef") (IC "Ints")) (EInt n) -> 
       return [EInt i | i <- [0..n]]
     QC p c -> lookupParamValues cnc p c
     RecType r -> do
       let (ls,tys) = unzip r
       tss <- mapM allPV tys
       return [R (zipAssign ls ts) | ts <- combinations tss]
     _ -> prtBad "cannot find parameter values for" ptyp
  where
    allPV = allParamValues cnc

qualifAnnot :: Ident -> Term -> Term
qualifAnnot _ = id
-- Using this we wouldn't have to annotate constants defined in a module itself.
-- But things are simpler if we do (cf. Zinc).
-- Change Rename.self2status to change this behaviour.

-- we need this for lookup in ResVal
qualifAnnotPar m t = case t of
  Cn c  -> Q m c
  Con c -> QC m c
  _ -> composSafeOp (qualifAnnotPar m) t

lookupAbsDef :: SourceGrammar -> Ident -> Ident -> Err (Maybe Term)
lookupAbsDef gr m c = errIn ("looking up absdef of" +++ prt c) $ do
  mi   <- lookupModule gr m
  case mi of
    ModMod mo -> do
      info <- lookupIdentInfo mo c
      case info of
        AbsFun _ (Yes t)  -> return $ return t
        AnyInd _ n  -> lookupAbsDef gr n c
        _ -> return Nothing
    _ -> Bad $ prt m +++ "is not an abstract module"


lookupLincat :: SourceGrammar -> Ident -> Ident -> Err Type
lookupLincat gr m c | elem c [zIdent "Int"] =
      let ints k = App (Q (IC "Predef") (IC "Ints")) (EInt k) in
      return $
      RecType [
        (LIdent "s", typeStr), (LIdent "last",ints 9),(LIdent "size",ints 1)]
lookupLincat gr m c | elem c [zIdent "String", zIdent "Float"] = 
  return defLinType --- ad hoc; not needed?

lookupLincat gr m c = do
  mi <- lookupModule gr m
  case mi of
    ModMod mo -> do
      info <- lookupIdentInfo mo c
      case info of
        CncCat (Yes t) _ _ -> return t
        AnyInd _ n         -> lookupLincat gr n c
        _   -> Bad $ prt c +++ "has no linearization type in" +++ prt m
    _ -> Bad $ prt m +++ "is not concrete"


-- The first type argument is uncomputed, usually a category symbol.
-- This is a hack to find implicit (= reused) opers.

opersForType :: SourceGrammar -> Type -> Type -> [(QIdent,Term)]
opersForType gr orig val = 
  [((i,f),ty) | (i,m) <- allModMod gr, (f,ty) <- opers i m val] where
    opers i m val = 
      [(f,ty) |
        (f,ResOper (Yes ty) _) <- tree2list $ jments m,
        Ok valt <- [valTypeCnc ty],
        elem valt [val,orig]
        ] ++
      let cat = err zIdent snd (valCat orig) in --- ignore module
      [(f,ty) |
        Ok a <- [abstractOfConcrete gr i >>= lookupModMod gr],
        (f, AbsFun (Yes ty0) _) <- tree2list $ jments a,
        let ty = redirectTerm i ty0,
        Ok valt  <- [valCat ty],
        cat == snd valt ---
        ]
