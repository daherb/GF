{-# LANGUAGE PatternGuards #-}
----------------------------------------------------------------------
-- |
-- Module      : CheckGrammar
-- Maintainer  : AR
-- Stability   : (stable)
-- Portability : (portable)
--
-- > CVS $Date: 2005/11/11 23:24:33 $ 
-- > CVS $Author: aarne $
-- > CVS $Revision: 1.31 $
--
-- AR 4\/12\/1999 -- 1\/4\/2000 -- 8\/9\/2001 -- 15\/5\/2002 -- 27\/11\/2002 -- 18\/6\/2003
--
-- type checking also does the following modifications:
--
--  - types of operations and local constants are inferred and put in place
--
--  - both these types and linearization types are computed
--
--  - tables are type-annotated
-----------------------------------------------------------------------------

module GF.Compile.CheckGrammar (
  showCheckModule, justCheckLTerm, allOperDependencies, topoSortOpers) where

import GF.Infra.Ident
import GF.Infra.Modules

import GF.Compile.TypeCheck

import GF.Compile.Refresh
import GF.Grammar.Lexer
import GF.Grammar.Grammar
import GF.Grammar.PrGrammar
import GF.Grammar.Lookup
import GF.Grammar.Predef
import GF.Grammar.Macros
import GF.Grammar.PatternMatch
import GF.Grammar.AppPredefined
import GF.Grammar.Lockfield (isLockLabel, lockRecType, unlockRecord)

import GF.Data.Operations
import GF.Infra.CheckM

import Data.List
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Monad
import Debug.Trace ---


showCheckModule :: [SourceModule] -> SourceModule -> Err ([SourceModule],String)
showCheckModule mos m = do
  (st,(_,msg)) <- checkStart $ checkModule mos m
  return (st, unlines $ reverse msg)

mapsCheckTree :: 
  (Ord a) => ((a,b) -> Check (a,c)) -> BinTree a b -> Check (BinTree a c)
mapsCheckTree f = checkErr . mapsErrTree (\t -> checkStart (f t) >>= return . fst)


-- | checking is performed in the dependency order of modules
checkModule :: [SourceModule] -> SourceModule -> Check [SourceModule]
checkModule ms (name,mo) = checkIn ("checking module" +++ prt name) $ do
    let js = jments mo
    checkRestrictedInheritance ms (name, mo)
    js' <- case mtype mo of
      MTAbstract -> mapsCheckTree (checkAbsInfo gr name mo) js

      MTTransfer a b -> mapsCheckTree (checkAbsInfo gr name mo) js

      MTResource -> mapsCheckTree (checkResInfo gr name mo) js

      MTConcrete a -> do
        checkErr $ topoSortOpers $ allOperDependencies name js
        abs <- checkErr $ lookupModule gr a
        js1 <- checkCompleteGrammar gr abs mo
        mapsCheckTree (checkCncInfo gr name mo (a,abs)) js1

      MTInterface -> mapsCheckTree (checkResInfo gr name mo) js

      MTInstance a -> do
        mapsCheckTree (checkResInfo gr name mo) js

    return $ (name, replaceJudgements mo js') : ms
 where
   gr  = MGrammar $ (name,mo):ms

-- check if restricted inheritance modules are still coherent
-- i.e. that the defs of remaining names don't depend on omitted names
checkRestrictedInheritance :: [SourceModule] -> SourceModule -> Check ()
checkRestrictedInheritance mos (name,mo) = do
  let irs = [ii | ii@(_,mi) <- extend mo, mi /= MIAll]  -- names with restr. inh.
  let mrs = [((i,m),mi) | (i,m) <- mos, Just mi <- [lookup i irs]] 
                             -- the restr. modules themself, with restr. infos
  mapM_ checkRem mrs
 where
   checkRem ((i,m),mi) = do
     let (incl,excl) = partition (isInherited mi) (map fst (tree2list (jments m)))
     let incld c   = Set.member c (Set.fromList incl)
     let illegal c = Set.member c (Set.fromList excl)
     let illegals = [(f,is) | 
           (f,cs) <- allDeps, incld f, let is = filter illegal cs, not (null is)]
     case illegals of 
       [] -> return ()
       cs -> fail $ "In inherited module" +++ prt i ++
               ", dependence of excluded constants:" ++++
               unlines ["  " ++ prt f +++ "on" +++ unwords (map prt is) | 
                              (f,is) <- cs]
   allDeps = concatMap (allDependencies (const True) . jments . snd) mos

-- | check if a term is typable
justCheckLTerm :: SourceGrammar -> Term -> Err Term
justCheckLTerm src t = do
  ((t',_),_) <- checkStart (inferLType src t)
  return t'

checkAbsInfo :: 
  SourceGrammar -> Ident -> SourceModInfo -> (Ident,Info) -> Check (Ident,Info)
checkAbsInfo st m mo (c,info) = do
---- checkReservedId c
 case info of
   AbsCat (Just cont) _ -> mkCheck "category" $ 
     checkContext st cont ---- also cstrs
   AbsFun (Just typ0) ma md -> do
     typ <- compAbsTyp [] typ0   -- to calculate let definitions
     mkCheck "type of function" $
       checkTyp st typ
     case md of
       Just eqs -> mkCheck "definition of function" $
	             checkDef st (m,c) typ eqs
       Nothing  -> return (c,info)
     return $ (c,AbsFun (Just typ) ma md)
   _ -> return (c,info)
 where
   mkCheck cat ss = case ss of
     [] -> return (c,info)
     _  -> checkErr $ Bad (unlines ss ++++ "in" +++ cat +++ prt c +++ pos c)
   ---- temporary solution when tc of defs is incomplete
   mkCheckWarn cat ss = case ss of
     [] -> return (c,info)
     ["[]"] -> return (c,info) ----
     _  -> do
       checkWarn (unlines ss ++++ "in" +++ cat +++ prt c +++ pos c)
       return (c,info)

   pos c = showPosition mo c

   compAbsTyp g t = case t of
     Vr x -> maybe (fail ("no value given to variable" +++ prt x)) return $ lookup x g
     Let (x,(_,a)) b -> do
       a' <- compAbsTyp g a
       compAbsTyp ((x, a'):g) b
     Prod x a b -> do
       a' <- compAbsTyp g a
       b' <- compAbsTyp ((x,Vr x):g) b
       return $ Prod x a' b'
     Abs _ _ -> return t
     _ -> composOp (compAbsTyp g) t

checkCompleteGrammar :: SourceGrammar -> SourceModInfo -> SourceModInfo -> Check (BinTree Ident Info)
checkCompleteGrammar gr abs cnc = do
  let jsa = jments abs
  let fsa = tree2list jsa
  let jsc = jments cnc
  let fsc = map fst $ filter (isCnc . snd) $ tree2list jsc

  -- remove those lincat and lin in concrete that are not in abstract
  let unkn = filter (not . flip isInBinTree jsa) fsc
  jsc1 <- if (null unkn) then return jsc else do
    checkWarn $ "ignoring constants not in abstract:" +++ 
                unwords (map prt unkn)
    return $ filterBinTree (\f _ -> notElem f unkn) jsc 

  -- check that all abstract constants are in concrete; build default lincats
  foldM checkOne jsc1 fsa
 where
   isCnc j = case j of
     CncFun _ _ _ -> True
     CncCat _ _ _ -> True
     _ -> False
   checkOne js i@(c,info) = case info of
     AbsFun (Just ty) _ _ -> do let mb_def = do
                                      (cxt,(_,i),_) <- typeForm ty
                                      info <- lookupIdent i js
                                      info <- case info of
                                                (AnyInd _ m) -> do (m,info) <- lookupOrigInfo gr m i
                                                                   return info
                                                _            -> return info
                                      case info of
                                        CncCat (Just (RecType [])) _ _ -> return (foldr (\_ -> Abs identW) (R []) cxt)
                                        _                              -> Bad "no def lin"
                                case lookupIdent c js of
                                  Ok (CncFun _   (Just _) _ ) -> return js
                                  Ok (CncFun cty Nothing  pn) ->
                                    case mb_def of
                                      Ok def -> return $ updateTree (c,CncFun cty (Just def) pn) js
                                      Bad _  -> do checkWarn $ "no linearization of" +++ prt c
                                                   return js
                                  _ -> do
                                    case mb_def of
                                      Ok def -> return $ updateTree (c,CncFun Nothing (Just def) Nothing) js
                                      Bad _  -> do checkWarn $ "no linearization of" +++ prt c
                                                   return js
     AbsCat (Just _) _ -> case lookupIdent c js of
       Ok (AnyInd _ _) -> return js
       Ok (CncCat (Just _) _ _) -> return js
       Ok (CncCat _ mt mp) -> do
         checkWarn $ 
           "no linearization type for" +++ prt c ++ 
           ", inserting default {s : Str}" 
         return $ updateTree (c,CncCat (Just defLinType) mt mp) js
       _ -> do
         checkWarn $ 
           "no linearization type for" +++ prt c ++ 
           ", inserting default {s : Str}" 
         return $ updateTree (c,CncCat (Just defLinType) Nothing Nothing) js
     _ -> return js

-- | General Principle: only Just-values are checked. 
-- A May-value has always been checked in its origin module.
checkResInfo :: SourceGrammar -> Ident -> SourceModInfo -> (Ident,Info) -> Check (Ident,Info)
checkResInfo gr mo mm (c,info) = do
  checkReservedId c
  case info of
    ResOper pty pde -> chIn "operation" $ do
      (pty', pde') <- case (pty,pde) of
         (Just ty, Just de) -> do
           ty'     <- check ty typeType >>= comp . fst
           (de',_) <- check de ty'
           return (Just ty', Just de')
         (_      , Just de) -> do
           (de',ty') <- infer de
           return (Just ty', Just de')
         (_      , Nothing) -> do
           raise "No definition given to oper"
      return (c, ResOper pty' pde')

    ResOverload os tysts -> chIn "overloading" $ do
      tysts' <- mapM (uncurry $ flip check) tysts  -- return explicit ones
      tysts0 <- checkErr $ lookupOverload gr mo c  -- check against inherited ones too
      tysts1 <- mapM (uncurry $ flip check) 
                  [(mkFunType args val,tr) | (args,(val,tr)) <- tysts0]
      let tysts2 = [(y,x) | (x,y) <- tysts1]
      --- this can only be a partial guarantee, since matching
      --- with value type is only possible if expected type is given
      checkUniq $ 
        sort [t : map snd xs | (x,_) <- tysts2, Ok (xs,t) <- [typeFormCnc x]]
      return (c,ResOverload os [(y,x) | (x,y) <- tysts'])

    ResParam (Just (pcs,_)) -> chIn "parameter type" $ do
----      mapM ((mapM (computeLType gr . snd)) . snd) pcs
      mapM_ ((mapM_ (checkIfParType gr . snd)) . snd) pcs
      ts <- checkErr $ lookupParamValues gr mo c
      return (c,ResParam (Just (pcs, Just ts)))

    _ ->  return (c,info)
 where
   infer = inferLType gr
   check = checkLType gr
   chIn cat = checkIn ("Happened in" +++ cat +++ prt c +++ pos c +++ ":")
   comp = computeLType gr
   pos c = showPosition mm c

   checkUniq xss = case xss of
     x:y:xs 
      | x == y -> raise $ "ambiguous for type" +++ 
                           prtType gr (mkFunType (tail x) (head x))  
      | otherwise -> checkUniq $ y:xs
     _ -> return ()


checkCncInfo :: SourceGrammar -> Ident -> SourceModInfo -> 
                (Ident,SourceModInfo) -> 
                (Ident,Info) -> Check (Ident,Info)
checkCncInfo gr m mo (a,abs) (c,info) = do
  checkReservedId c
  case info of

    CncFun _ (Just trm) mpr -> chIn "linearization of" $ do
      typ        <- checkErr $ lookupFunType gr a c
      cat0       <- checkErr $ valCat typ
      (cont,val) <- linTypeOfType gr m typ         -- creates arg vars
      (trm',_)   <- check trm (mkFunType (map snd cont) val)  -- erases arg vars
      checkPrintname gr mpr
      cat        <- return $ snd cat0
      return (c, CncFun (Just (cat,(cont,val))) (Just trm') mpr)
                                                   -- cat for cf, typ for pe

    CncCat (Just typ) mdef mpr -> chIn "linearization type of" $ do
      checkErr $ lookupCatContext gr a c
      typ'  <- checkIfLinType gr typ
      mdef' <- case mdef of
        Just def -> do
          (def',_) <- checkLType gr def (mkFunType [typeStr] typ)
          return $ Just def'
        _ -> return mdef
      checkPrintname gr mpr
      return (c,CncCat (Just typ') mdef' mpr)

    _ -> checkResInfo gr m mo (c,info)

 where
   env = gr
   infer = inferLType gr
   comp = computeLType gr 
   check = checkLType gr
   chIn cat = checkIn ("Happened in" +++ cat +++ prt c +++ pos c +++ ":")
   pos c = showPosition mo c

checkIfParType :: SourceGrammar -> Type -> Check ()
checkIfParType st typ = checkCond ("Not parameter type" +++ prt typ) (isParType typ)
  where
   isParType ty = True ----
{- case ty of
     Cn typ -> case lookupConcrete st typ of
       Ok (CncParType _ _ _) -> True
       Ok (CncOper _ ty' _) -> isParType ty'
       _ -> False
     Q p t -> case lookupInPackage st (p,t) of
       Ok (CncParType _ _ _) -> True
       _ -> False
     RecType r -> all (isParType . snd) r
     _ -> False
-}

checkIfStrType :: SourceGrammar -> Type -> Check ()
checkIfStrType st typ = case typ of
  Table arg val -> do
    checkIfParType st arg 
    checkIfStrType st val
  _ | typ == typeStr -> return ()
  _ -> prtFail "not a string type" typ


checkIfLinType :: SourceGrammar -> Type -> Check Type
checkIfLinType st typ0 = do
  typ <- computeLType st typ0
{- ---- should check that not fun type
  case typ of
    RecType r -> do
      let (lins,ihs) = partition (isLinLabel .fst) r
      --- checkErr $ checkUnique $ map fst r
      mapM_ checkInh ihs
      mapM_ checkLin lins
    _ -> prtFail "a linearization type cannot be" typ
-}
  return typ

 where
   checkInh (label,typ) = checkIfParType st typ
   checkLin (label,typ) = return () ---- checkIfStrType st typ


computeLType :: SourceGrammar -> Type -> Check Type
computeLType gr t = do
  g0 <- checkGetContext
  let g = [(x, Vr x) | (x,_) <- g0]
  checkInContext g $ comp t
 where
  comp ty = case ty of
    _ | Just _ <- isTypeInts ty -> return ty ---- shouldn't be needed
      | isPredefConstant ty     -> return ty ---- shouldn't be needed

    Q m ident -> checkIn ("module" +++ prt m) $ do
      ty' <- checkErr (lookupResDef gr m ident) 
      if ty' == ty then return ty else comp ty' --- is this necessary to test?

    Vr ident  -> checkLookup ident -- never needed to compute!

    App f a -> do
      f' <- comp f
      a' <- comp a
      case f' of
        Abs x b -> checkInContext [(x,a')] $ comp b
        _ -> return $ App f' a'

    Prod x a b -> do
      a' <- comp a
      b' <- checkInContext [(x,Vr x)] $ comp b
      return $ Prod x a' b'

    Abs x b -> do
      b' <- checkInContext [(x,Vr x)] $ comp b
      return $ Abs x b'

    ExtR r s -> do
      r' <- comp r
      s' <- comp s
      case (r',s') of
        (RecType rs, RecType ss) -> checkErr (plusRecType r' s') >>= comp
        _ -> return $ ExtR r' s'

    RecType fs -> do
      let fs' = sortRec fs
      liftM RecType $ mapPairsM comp fs'

    ELincat c t -> do
      t' <- comp t
      checkErr $ lockRecType c t' ---- locking to be removed AR 20/6/2009

    _ | ty == typeTok -> return typeStr
    _ | isPredefConstant ty -> return ty

    _ -> composOp comp ty

checkPrintname :: SourceGrammar -> Maybe Term -> Check ()
checkPrintname st (Just t) = checkLType st t typeStr >> return ()
checkPrintname _  _        = return ()

-- | for grammars obtained otherwise than by parsing ---- update!!
checkReservedId :: Ident -> Check ()
checkReservedId x
  | isReservedWord (ident2bs x) = checkWarn ("reserved word used as identifier:" +++ prt x)
  | otherwise                   = return ()

-- to normalize records and record types
labelIndex :: Type -> Label -> Int
labelIndex ty lab = case ty of
  RecType ts -> maybe (error ("label index" +++ prt lab)) id $ lookup lab $ labs ts
  _ -> error $ "label index" +++ prt ty
 where 
  labs ts = zip (map fst (sortRec ts)) [0..]

-- the underlying algorithms

inferLType :: SourceGrammar -> Term -> Check (Term, Type)
inferLType gr trm = case trm of

   Q m ident | isPredef m -> termWith trm $ checkErr (typPredefined ident)

   Q m ident -> checks [
     termWith trm $ checkErr (lookupResType gr m ident) >>= comp
     ,
     checkErr (lookupResDef gr m ident) >>= infer
     ,
     prtFail "cannot infer type of constant" trm
     ]

   QC m ident | isPredef m -> termWith trm $ checkErr (typPredefined ident)

   QC m ident -> checks [
       termWith trm $ checkErr (lookupResType gr m ident) >>= comp
       ,
       checkErr (lookupResDef gr m ident) >>= infer
       ,
       prtFail "cannot infer type of canonical constant" trm
       ]

   Val _ ty i -> termWith trm $ return ty

   Vr ident -> termWith trm $ checkLookup ident

   Typed e t -> do
     t' <- comp t
     check e t'
     return (e,t')

   App f a -> do
     over <- getOverload gr Nothing trm
     case over of
       Just trty -> return trty
       _ -> do
         (f',fty) <- infer f
         fty' <- comp fty
         case fty' of
           Prod z arg val -> do 
             a' <- justCheck a arg
             ty <- if isWildIdent z 
                      then return val
                      else substituteLType [(z,a')] val
             return (App f' a',ty) 
           _ -> raise ("function type expected for"+++ 
                      prt f +++"instead of" +++ prtType env fty)

   S f x -> do
     (f', fty) <- infer f
     case fty of
       Table arg val -> do
         x'<- justCheck x arg
         return (S f' x', val)
       _ -> prtFail "table lintype expected for the table in" trm

   P t i -> do
     (t',ty) <- infer t   --- ??
     ty' <- comp ty
-----     let tr2 = PI t' i (labelIndex ty' i)
     let tr2 = P t' i
     termWith tr2 $ checkErr $ case ty' of
       RecType ts -> maybeErr ("unknown label" +++ prt i +++ "in" +++ prt ty') $ 
                     lookup i ts
       _ -> prtBad ("record type expected for" +++ prt t +++ "instead of") ty'
   PI t i _ -> infer $ P t i

   R r -> do
     let (ls,fs) = unzip r
     fsts <- mapM inferM fs
     let ts = [ty | (Just ty,_) <- fsts]
     checkCond ("cannot infer type of record"+++ prt trm) (length ts == length fsts)
     return $ (R (zip ls fsts), RecType (zip ls ts))

   T (TTyped arg) pts -> do
     (_,val) <- checks $ map (inferCase (Just arg)) pts
     check trm (Table arg val)
   T (TComp arg) pts -> do
     (_,val) <- checks $ map (inferCase (Just arg)) pts
     check trm (Table arg val)
   T ti pts -> do  -- tries to guess: good in oper type inference
     let pts' = [pt | pt@(p,_) <- pts, isConstPatt p]
     case pts' of 
       [] -> prtFail "cannot infer table type of" trm
----       PInt k : _ -> return $ Ints $ max [i | PInt i <- pts'] 
       _  -> do 
         (arg,val) <- checks $ map (inferCase Nothing) pts'
         check trm (Table arg val)
   V arg pts -> do
     (_,val) <- checks $ map infer pts
     return (trm, Table arg val)

   K s  -> do
     if elem ' ' s
        then do
          let ss = foldr C Empty (map K (words s))  
          ----- removed irritating warning AR 24/5/2008
          ----- checkWarn ("token \"" ++ s ++ 
          -----              "\" converted to token list" ++ prt ss)
          return (ss, typeStr)
        else return (trm, typeStr)

   EInt i -> return (trm, typeInt)

   EFloat i -> return (trm, typeFloat)

   Empty -> return (trm, typeStr)

   C s1 s2 -> 
     check2 (flip justCheck typeStr) C s1 s2 typeStr

   Glue s1 s2 -> 
     check2 (flip justCheck typeStr) Glue s1 s2 typeStr ---- typeTok

---- hack from Rename.identRenameTerm, to live with files with naming conflicts 18/6/2007
   Strs (Cn c : ts) | c == cConflict -> do
     trace ("WARNING: unresolved constant, could be any of" +++ unwords (map prt ts)) (infer $ head ts)
--     checkWarn ("unresolved constant, could be any of" +++ unwords (map prt ts))
--     infer $ head ts

   Strs ts -> do
     ts' <- mapM (\t -> justCheck t typeStr) ts 
     return (Strs ts', typeStrs)

   Alts (t,aa) -> do
     t'  <- justCheck t typeStr
     aa' <- flip mapM aa (\ (c,v) -> do
        c' <- justCheck c typeStr 
        v' <- checks $ map (justCheck v) [typeStrs, EPattType typeStr]
        return (c',v'))
     return (Alts (t',aa'), typeStr)

   RecType r -> do
     let (ls,ts) = unzip r
     ts' <- mapM (flip justCheck typeType) ts 
     return (RecType (zip ls ts'), typeType)

   ExtR r s -> do
     (r',rT) <- infer r 
     rT'     <- comp rT
     (s',sT) <- infer s
     sT'     <- comp sT

     let trm' = ExtR r' s'
     ---- trm'    <- checkErr $ plusRecord r' s'
     case (rT', sT') of
       (RecType rs, RecType ss) -> do
         rt <- checkErr $ plusRecType rT' sT'
         check trm' rt ---- return (trm', rt)
       _ | rT' == typeType && sT' == typeType -> return (trm', typeType)
       _ -> prtFail "records or record types expected in" trm

   Sort _     -> 
     termWith trm $ return typeType

   Prod x a b -> do
     a' <- justCheck a typeType
     b' <- checkInContext [(x,a')] $ justCheck b typeType
     return (Prod x a' b', typeType)

   Table p t  -> do
     p' <- justCheck p typeType --- check p partype! 
     t' <- justCheck t typeType
     return $ (Table p' t', typeType)

   FV vs -> do
     (_,ty) <- checks $ map infer vs
---     checkIfComplexVariantType trm ty
     check trm ty

   EPattType ty -> do
     ty' <- justCheck ty typeType
     return (EPattType ty',typeType)
   EPatt p -> do
     ty <- inferPatt p
     return (trm, EPattType ty)

   ELin c trm -> do
     (trm',ty) <- infer trm
     ty' <- checkErr $ lockRecType c ty ---- lookup c; remove lock AR 20/6/2009
     return $ (ELin c trm', ty') 

   _ -> prtFail "cannot infer lintype of" trm

 where
   env = gr
   infer = inferLType env
   comp = computeLType env 

   check = checkLType env
   
   isPredef m = elem m [cPredef,cPredefAbs]

   justCheck ty te = check ty te >>= return . fst

   -- for record fields, which may be typed
   inferM (mty, t) = do
     (t', ty') <- case mty of
       Just ty -> check ty t
       _ -> infer t
     return (Just ty',t')

   inferCase mty (patt,term) = do
     arg  <- maybe (inferPatt patt) return mty
     cont <- pattContext env arg patt
     i    <- checkUpdates cont
     (_,val) <- infer term
     checkResets i
     return (arg,val)
   isConstPatt p = case p of
     PC _ ps -> True --- all isConstPatt ps
     PP _ _ ps -> True --- all isConstPatt ps
     PR ps -> all (isConstPatt . snd) ps
     PT _ p -> isConstPatt p
     PString _ -> True
     PInt _ -> True
     PFloat _ -> True
     PChar -> True
     PChars _ -> True
     PSeq p q -> isConstPatt p && isConstPatt q
     PAlt p q -> isConstPatt p && isConstPatt q
     PRep p -> isConstPatt p
     PNeg p -> isConstPatt p
     PAs _ p -> isConstPatt p
     _ -> False

   inferPatt p = case p of
     PP q c ps | q /= cPredef -> checkErr $ lookupResType gr q c >>= valTypeCnc
     PAs _ p  -> inferPatt p
     PNeg p   -> inferPatt p
     PAlt p q -> checks [inferPatt p, inferPatt q]
     PSeq _ _ -> return $ typeStr
     PRep _   -> return $ typeStr
     PChar    -> return $ typeStr
     PChars _ -> return $ typeStr
     _ -> infer (patt2term p) >>= return . snd


-- type inference: Nothing, type checking: Just t
-- the latter permits matching with value type
getOverload :: SourceGrammar -> Maybe Type -> Term -> Check (Maybe (Term,Type))
getOverload env@gr mt ot = case appForm ot of
     (f@(Q m c), ts) -> case lookupOverload gr m c of
       Ok typs -> do
         ttys <- mapM infer ts
         v <- matchOverload f typs ttys
         return $ Just v
       _ -> return Nothing
     _ -> return Nothing
 where
   infer = inferLType env
   matchOverload f typs ttys = do
     let (tts,tys) = unzip ttys
     let vfs = lookupOverloadInstance tys typs
     let matches = [vf | vf@((v,_),_) <- vfs, matchVal mt v]

     case ([vf | (vf,True) <- matches],[vf | (vf,False) <- matches]) of
       ([(val,fun)],_) -> return (mkApp fun tts, val)
       ([],[(val,fun)]) -> do
         checkWarn ("ignoring lock fields in resolving" +++ prt ot) 
         return (mkApp fun tts, val)
       ([],[]) -> do
         ---- let prtType _ = prt  -- to debug grammars
         let sought = unwords (map (prtType env) tys)
         let showTypes ty = case unwords (map (prtType env) ty) of
               s | s == sought -> 
                 s +++ "  -- i.e." +++ unwords (map prt ty) ++++
                 "     where we sought" +++ unwords (map prt tys)
               s -> s
         raise $ "no overload instance of" +++ prt f +++ 
           "for" +++ 
           sought +++
           "among" ++++ 
           unlines ["  " ++ showTypes ty | (ty,_) <- typs] ++
           maybe [] (("with value type" +++) . prtType env) mt

       (vfs1,vfs2) -> case (noProds vfs1,noProds vfs2) of
         ([(val,fun)],_) -> do
           return (mkApp fun tts, val)
         ([],[(val,fun)]) -> do
           checkWarn ("ignoring lock fields in resolving" +++ prt ot) 
           return (mkApp fun tts, val)

----- unsafely exclude irritating warning AR 24/5/2008
-----           checkWarn $ "overloading of" +++ prt f +++ 
-----             "resolved by excluding partial applications:" ++++
-----             unlines [prtType env ty | (ty,_) <- vfs', not (noProd ty)]


         _ -> raise $ "ambiguous overloading of" +++ prt f +++
             "for" +++ unwords (map (prtType env) tys) ++++ "with alternatives" ++++ 
             unlines [prtType env ty | (ty,_) <- if (null vfs1) then vfs2 else vfs2]

   matchVal mt v = elem mt [Nothing,Just v,Just (unlocked v)]

   unlocked v = case v of
     RecType fs -> RecType $ filter (not . isLockLabel . fst) fs
     _ -> v
   ---- TODO: accept subtypes
   ---- TODO: use a trie
   lookupOverloadInstance tys typs = 
     [((mkFunType rest val, t),isExact) | 
       let lt = length tys,
       (ty,(val,t)) <- typs, length ty >= lt,
       let (pre,rest) = splitAt lt ty, 
       let isExact = pre == tys,
       isExact || map unlocked pre == map unlocked tys
     ]

   noProds vfs = [(v,f) | (v,f) <- vfs, noProd v]

   noProd ty = case ty of
     Prod _ _ _ -> False
     _ -> True

checkLType :: SourceGrammar -> Term -> Type -> Check (Term, Type)
checkLType env trm typ0 = do

  typ <- comp typ0

  case trm of

    Abs x c -> do
      case typ of
        Prod z a b -> do 
          checkUpdate (x,a)
          (c',b') <- if isWildIdent z
                        then check c b
                        else do
                          b' <- checkIn "abs" $ substituteLType [(z,Vr x)] b
                          check c b'
          checkReset
          return $ (Abs x c', Prod x a b')
        _ -> raise $ "function type expected instead of" +++ prtType env typ

    App f a -> do
       over <- getOverload env (Just typ) trm
       case over of
         Just trty -> return trty
         _ -> do
          (trm',ty') <- infer trm
          termWith trm' $ checkEq typ ty' trm'

    Q _ _ -> do
       over <- getOverload env (Just typ) trm
       case over of
         Just trty -> return trty
         _ -> do
          (trm',ty') <- infer trm
          termWith trm' $ checkEq typ ty' trm'

    T _ [] ->
      prtFail "found empty table in type" typ
    T _ cs -> case typ of 
      Table arg val -> do 
        case allParamValues env arg of
          Ok vs -> do
            let ps0 = map fst cs
            ps <- checkErr $ testOvershadow ps0 vs
            if null ps 
              then return () 
---- use this if you want to see where the error is
--              else raise $ "patterns never reached:" +++ 
--                               concat (intersperse ", " (map prt ps))
---- else use this
              else trace ("WARNING: patterns never reached:" +++ 
                               concat (intersperse ", " (map prt ps))) (return ())
---- AR 6/4/2009: this would be the best but checkWarn doesn't show because of laziness (?)
----              else checkWarn $ "patterns never reached:" +++ 
----                               concat (intersperse ", " (map prt ps))

          _ -> return () -- happens with variable types
        cs' <- mapM (checkCase arg val) cs
        return (T (TTyped arg) cs', typ)
      _ -> raise $ "table type expected for table instead of" +++ prtType env typ

    R r -> case typ of --- why needed? because inference may be too difficult
       RecType rr -> do
         let (ls,_) = unzip rr        -- labels of expected type
         fsts <- mapM (checkM r) rr   -- check that they are found in the record
         return $ (R fsts, typ)       -- normalize record

       _ -> prtFail "record type expected in type checking instead of" typ

    ExtR r s -> case typ of
       _ | typ == typeType -> do
         trm' <- comp trm
         case trm' of
           RecType _ -> termWith trm $ return typeType
           ExtR (Vr _) (RecType _) -> termWith trm $ return typeType 
                                      -- ext t = t ** ...
           _ -> prtFail "invalid record type extension" trm
       RecType rr -> do
         (r',ty,s') <- checks [
            do (r',ty) <- infer r
               return (r',ty,s)
           ,
            do (s',ty) <- infer s
               return (s',ty,r)
            ]
         case ty of
           RecType rr1 -> do
                let (rr0,rr2) = recParts rr rr1
                r2 <- justCheck r' rr0
                s2 <- justCheck s' rr2
                return $ (ExtR r2 s2, typ) 
           _ -> raise ("record type expected in extension of" +++ prt r +++ 
                       "but found" +++ prt ty)

       ExtR ty ex -> do
         r' <- justCheck r ty
         s' <- justCheck s ex
         return $ (ExtR r' s', typ) --- is this all?

       _ -> prtFail "record extension not meaningful for" typ

    FV vs -> do
      ttys <- mapM (flip check typ) vs
---      checkIfComplexVariantType trm typ
      return (FV (map fst ttys), typ) --- typ' ?

    S tab arg -> checks [ do
      (tab',ty) <- infer tab
      ty'       <- comp ty
      case ty' of
        Table p t -> do
          (arg',val) <- check arg p
          checkEq typ t trm
          return (S tab' arg', t)
        _ -> raise $ "table type expected for applied table instead of" +++ 
                   prtType env ty'
     , do
      (arg',ty) <- infer arg
      ty'       <- comp ty
      (tab',_)  <- check tab (Table ty' typ)
      return (S tab' arg', typ)
      ]
    Let (x,(mty,def)) body -> case mty of
      Just ty -> do
        (def',ty') <- check def ty
        checkUpdate (x,ty')
        body' <- justCheck body typ
        checkReset
        return (Let (x,(Just ty',def')) body', typ)
      _ -> do
        (def',ty) <- infer def  -- tries to infer type of local constant
        check (Let (x,(Just ty,def')) body) typ

    ELin c tr -> do
      tr1 <- checkErr $ unlockRecord c tr
      check tr1 typ

    _ -> do
      (trm',ty') <- infer trm
      termWith trm' $ checkEq typ ty' trm'
 where
   cnc = env
   infer = inferLType env
   comp = computeLType env 

   check = checkLType env
   
   justCheck ty te = check ty te >>= return . fst

   checkEq = checkEqLType env

   recParts rr t = (RecType rr1,RecType rr2) where 
     (rr1,rr2) = partition (flip elem (map fst t) . fst) rr 

   checkM rms (l,ty) = case lookup l rms of
     Just (Just ty0,t) -> do
       checkEq ty ty0 t
       (t',ty') <- check t ty
       return (l,(Just ty',t'))
     Just (_,t) -> do
       (t',ty') <- check t ty
       return (l,(Just ty',t'))
     _ -> raise $ 
       if isLockLabel l 
       then
         let cat = drop 5 (prt l) in
         prt_ (R rms) +++ "is not in the lincat of" +++ cat ++ 
         "; try wrapping it with lin " ++ cat
       else
         "cannot find value for label" +++ prt l +++ "in" +++ prt_ (R rms)

   checkCase arg val (p,t) = do
     cont <- pattContext env arg p
     i    <- checkUpdates cont
     t'   <- justCheck t val
     checkResets i
     return (p,t')

pattContext :: LTEnv -> Type -> Patt -> Check Context
pattContext env typ p = case p of
  PV x -> return [(x,typ)]
  PP q c ps | q /= cPredef -> do ---- why this /=? AR 6/1/2006
    t <- checkErr $ lookupResType cnc q c
    (cont,v) <- checkErr $ typeFormCnc t
    checkCond ("wrong number of arguments for constructor in" +++ prt p) 
              (length cont == length ps)
    checkEqLType env typ v (patt2term p)
    mapM (uncurry (pattContext env)) (zip (map snd cont) ps) >>= return . concat
  PR r -> do
    typ' <- computeLType env typ
    case typ' of
      RecType t -> do
        let pts = [(ty,tr) | (l,tr) <- r, Just ty <- [lookup l t]]
        ----- checkWarn $ prt p ++++ show pts ----- debug
        mapM (uncurry (pattContext env)) pts >>= return . concat
      _ -> prtFail "record type expected for pattern instead of" typ'
  PT t p' -> do
    checkEqLType env typ t (patt2term p')
    pattContext env typ p'

  PAs x p -> do
    g <- pattContext env typ p
    return $ (x,typ):g

  PAlt p' q -> do
    g1 <- pattContext env typ p'
    g2 <- pattContext env typ q
    let pts = [pt | pt <- g1, notElem pt g2] ++ [pt | pt <- g2, notElem pt g1]
    checkCond 
      ("incompatible bindings of" +++ 
       unwords (nub (map (prt . fst) pts))+++ 
       "in pattern alterantives" +++ prt p) (null pts) 
    return g1 -- must be g1 == g2
  PSeq p q -> do
    g1 <- pattContext env typ p
    g2 <- pattContext env typ q
    return $ g1 ++ g2
  PRep p' -> noBind typeStr p'
  PNeg p' -> noBind typ p'

  _ -> return [] ---- check types!
 where 
   cnc = env
   noBind typ p' = do
    co <- pattContext env typ p'
    if not (null co)
      then checkWarn ("no variable bound inside pattern" +++ prt p) 
           >> return []
      else return []

-- auxiliaries

type LTEnv = SourceGrammar

termWith :: Term -> Check Type -> Check (Term, Type)
termWith t ct = do
  ty <- ct
  return (t,ty)

-- | light-weight substitution for dep. types
substituteLType :: Context -> Type -> Check Type
substituteLType g t = case t of
  Vr x -> return $ maybe t id $ lookup x g
  _ -> composOp (substituteLType g) t

-- | compositional check\/infer of binary operations
check2 :: (Term -> Check Term) -> (Term -> Term -> Term) -> 
          Term -> Term -> Type -> Check (Term,Type)
check2 chk con a b t = do
  a' <- chk a
  b' <- chk b
  return (con a' b', t)

checkEqLType :: LTEnv -> Type -> Type -> Term -> Check Type
checkEqLType env t u trm = do
  (b,t',u',s) <- checkIfEqLType env t u trm
  case b of
    True  -> return t'
    False -> raise $ s +++ "type of" +++ prt trm +++ 
                        ": expected:" +++ prtType env t ++++ 
                        "inferred:" +++ prtType env u

checkIfEqLType :: LTEnv -> Type -> Type -> Term -> Check (Bool,Type,Type,String)
checkIfEqLType env t u trm = do
  t' <- comp t 
  u' <- comp u
  case t' == u' || alpha [] t' u' of
    True -> return (True,t',u',[])
    -- forgive missing lock fields by only generating a warning.
    --- better: use a flag to forgive? (AR 31/1/2006)
    _ -> case missingLock [] t' u' of
      Ok lo -> do
        checkWarn $ "missing lock field" +++ unwords (map prt lo)
        return (True,t',u',[])
      Bad s -> return (False,t',u',s)

  where

   -- t is a subtype of u 
   --- quick hack version of TC.eqVal
   alpha g t u = case (t,u) of  

     -- error (the empty type!) is subtype of any other type
     (_,u) | u == typeError -> True

     -- contravariance
     (Prod x a b, Prod y c d) -> alpha g c a && alpha ((x,y):g) b d 
                              
     -- record subtyping
     (RecType rs, RecType ts) -> all (\ (l,a) -> 
                                   any (\ (k,b) -> alpha g a b && l == k) ts) rs
     (ExtR r s, ExtR r' s') -> alpha g r r' && alpha g s s'
     (ExtR r s, t) -> alpha g r t || alpha g s t

     -- the following say that Ints n is a subset of Int and of Ints m >= n
     (t,u) | Just m <- isTypeInts t, Just n <- isTypeInts t -> m >= n
           | Just _ <- isTypeInts t, u == typeInt           -> True ---- check size!
           | t == typeInt,           Just _ <- isTypeInts u -> True ---- why this ???? AR 11/12/2005

     ---- this should be made in Rename
     (Q  m a, Q  n b) | a == b -> elem m (allExtendsPlus env n) 
                               || elem n (allExtendsPlus env m)
                               || m == n --- for Predef
     (QC m a, QC n b) | a == b -> elem m (allExtendsPlus env n) 
                               || elem n (allExtendsPlus env m)
     (QC m a, Q  n b) | a == b -> elem m (allExtendsPlus env n) 
                               || elem n (allExtendsPlus env m)
     (Q  m a, QC n b) | a == b -> elem m (allExtendsPlus env n) 
                               || elem n (allExtendsPlus env m)

     (Table a b,  Table c d)  -> alpha g a c && alpha g b d
     (Vr x,       Vr y)       -> x == y || elem (x,y) g || elem (y,x) g
     _                        -> t == u 
     --- the following should be one-way coercions only. AR 4/1/2001
                                  || elem t sTypes && elem u sTypes
                                  || (t == typeType && u == typePType) 
                                  || (u == typeType && t == typePType) 

   missingLock g t u = case (t,u) of  
     (RecType rs, RecType ts) -> 
       let 
         ls = [l | (l,a) <- rs, 
                   not (any (\ (k,b) -> alpha g a b && l == k) ts)]
         (locks,others) = partition isLockLabel ls
       in case others of
         _:_ -> Bad $ "missing record fields" +++ unwords (map prt others)
         _ -> return locks
     -- contravariance
     (Prod x a b, Prod y c d) -> do
        ls1 <- missingLock g c a
        ls2 <- missingLock g b d
        return $ ls1 ++ ls2

     _ -> Bad ""

   sTypes = [typeStr, typeTok, typeString]
   comp = computeLType env

-- if prtType is misleading, print the full type
prtTypeF :: LTEnv -> Type -> Type -> String
prtTypeF env exp ty = 
 let pty = prtType env ty 
 in if pty == prtType env exp then prt ty else pty

-- printing a type with a lock field lock_C as C
prtType :: LTEnv -> Type -> String
prtType env ty = case ty of
  RecType fs -> case filter isLockLabel $ map fst fs of
    [lock] -> (drop 5 $ prt lock) --- ++++ "Full form" +++ prt ty
    _ -> prtt ty
  Prod x a b -> prtType env a +++ "->" +++ prtType env b
  _ -> prtt ty
 where
   prtt t = prt t
   ---- use computeLType gr to check if really equal to the cat with lock


-- | linearization types and defaults
linTypeOfType :: SourceGrammar -> Ident -> Type -> Check (Context,Type)
linTypeOfType cnc m typ = do
  (cont,cat) <- checkErr $ typeSkeleton typ
  val  <- lookLin cat
  args <- mapM mkLinArg (zip [0..] cont)
  return (args, val)
 where
   mkLinArg (i,(n,mc@(m,cat))) = do
     val  <- lookLin mc
     let vars = mkRecType varLabel $ replicate n typeStr
	 symb = argIdent n cat i
     rec <- if n==0 then return val else
            checkErr $ errIn ("extending" +++ prt vars +++ "with" +++ prt val) $
            plusRecType vars val
     return (symb,rec)
   lookLin (_,c) = checks [ --- rather: update with defLinType ?
      checkErr (lookupLincat cnc m c) >>= computeLType cnc
     ,return defLinType
     ]

-- | dependency check, detecting circularities and returning topo-sorted list

allOperDependencies :: Ident -> BinTree Ident Info -> [(Ident,[Ident])]
allOperDependencies m = allDependencies (==m)

allDependencies :: (Ident -> Bool) -> BinTree Ident Info -> [(Ident,[Ident])]
allDependencies ism b = 
  [(f, nub (concatMap opty (pts i))) | (f,i) <- tree2list b]
  where
    opersIn t = case t of
      Q n c | ism n -> [c]
      QC n c | ism n -> [c]
      _ -> collectOp opersIn t
    opty (Just ty) = opersIn ty
    opty _ = []
    pts i = case i of
      ResOper pty pt -> [pty,pt]
      ResParam (Just (ps,_)) -> [Just t | (_,cont) <- ps, (_,t) <- cont]
      CncCat pty _ _ -> [pty]
      CncFun _   pt _ -> [pt]  ---- (Maybe (Ident,(Context,Type))
      AbsFun pty _ ptr -> [pty] --- ptr is def, which can be mutual
      AbsCat (Just co) _ -> [Just ty | (_,ty) <- co]
      _              -> []

topoSortOpers :: [(Ident,[Ident])] -> Err [Ident]
topoSortOpers st = do
  let eops = topoTest st
  either 
    return 
    (\ops -> Bad ("circular definitions:" +++ unwords (map prt (head ops))))
    eops
