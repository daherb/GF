module MkResource where

import Grammar
import Ident
import Modules
import Macros
import PrGrammar

import Operations

import Monad

-- extracting resource r from abstract + concrete syntax
-- AR 21/8/2002 -- 22/6/2003 for GF with modules

makeReuse :: SourceGrammar -> Ident -> Maybe Ident -> Ident -> Err SourceRes
makeReuse gr r me c = do
  mc <- lookupModule gr c

  flags <- return [] --- no flags are passed: they would not make sense

  (ops,jms) <- case mc of 
    ModMod m -> case mtype m of
      MTConcrete a -> do
        ma <- lookupModule gr a
        jmsA <- case ma of 
           ModMod m' -> return $ jments m'
           _ -> prtBad "expected abstract to be the type of" a
        liftM ((,) (opens m)) $ mkResDefs gr r a me (extends m) jmsA (jments m)
      _ -> prtBad "expected concrete to be the type of" c
    _ -> prtBad "expected concrete to be the type of" c

  return $ Module MTResource MSComplete flags me ops jms

mkResDefs :: SourceGrammar -> Ident -> Ident -> Maybe Ident -> Maybe Ident -> 
             BinTree (Ident,Info) -> BinTree (Ident,Info) -> 
             Err (BinTree (Ident,Info))
mkResDefs gr r a mext maext abs cnc = mapMTree (mkOne a maext) abs where

  mkOne a mae (f,info) = case info of
      AbsCat _ _ -> do
        typ  <- err (const (return defLinType)) return $ look cnc f
        typ' <- lockRecType f typ 
        return (f, ResOper (Yes typeType) (Yes typ'))
      AbsFun (Yes typ0) _ -> do
        trm <- look cnc f
        testErr (not (isHardType typ0)) 
                ("cannot build reuse for function" +++ prt f +++ ":" +++ prt typ0)
        typ <- redirTyp True a mae typ0
        cat <- valCat typ
        trm' <- unlockRecord (snd cat) trm 
        return (f, ResOper (Yes typ) (Yes trm'))
      AnyInd b n -> do
        mo    <- lookupModMod gr n
        info' <- lookupInfo mo f
        mkOne n (extends mo) (f,info')

  look cnc f = do
     info <- lookupTree prt f cnc
     case info of
       CncCat (Yes ty) _ _ -> return ty
       CncCat _ _ _        -> return defLinType
       CncFun _ (Yes tr) _ -> return tr
       AnyInd _ n -> do 
         mo    <- lookupModMod gr n
         t <- look (jments mo) f
         redirTyp False n (extends mo) t
       _ -> prtBad "not enough information to reuse" f

  -- type constant qualifications changed from abstract to resource
  redirTyp always a mae ty = case ty of
    Q _ c | always -> return $ Q r c
    Q n c | n == a || Just n == mae -> return $ Q r c
    _ -> composOp (redirTyp always a mae) ty

lockRecType :: Ident -> Type -> Err Type
lockRecType c t = plusRecType t $ RecType [(lockLabel c,  RecType [])]

unlockRecord :: Ident -> Term -> Err Term
unlockRecord c ft = do
  let (xs,t) = termFormCnc ft
  t' <- plusRecord t $ R [(lockLabel c,  (Just (RecType []),R []))]
  return $ mkAbs xs t'

lockLabel :: Ident -> Label
lockLabel c = LIdent $ "lock_" ++ prt c ----


-- no reuse for functions of HO/dep types

isHardType t = case t of
  Prod x a b -> not (isWild x) || isHardType a || isHardType b
  App _ _    -> True
  _          -> False  
 where 
   isWild x = isWildIdent x || prt x == "h_" --- produced by transl from canon
