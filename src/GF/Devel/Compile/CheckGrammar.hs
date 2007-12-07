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
-- AR 4\/12\/1999 -- 1\/4\/2000 -- 8\/9\/2001 -- 15\/5\/2002 -- 27\/11\/2002 -- 18\/6\/2003 -- 6/12/2007
--
-- type checking also does the following modifications:
--
--  - types of operations and local constants are inferred and put in place
--
--  - both these types and linearization types are computed
--
--  - tables are type-annotated
--
--  - overloading is resolved
-----------------------------------------------------------------------------

module GF.Devel.Compile.CheckGrammar (
  showCheckModule, 
  justCheckLTerm, 
  allOperDependencies, 
  topoSortOpers
  ) where

import GF.Devel.Grammar.Modules
import GF.Devel.Grammar.Judgements
import GF.Devel.Grammar.Terms
import GF.Devel.Grammar.MkJudgements
import GF.Devel.Grammar.Macros
import GF.Devel.Grammar.PrGF
import GF.Devel.Grammar.Lookup

import GF.Infra.Ident

--import GF.Grammar.Refresh ----

--import GF.Grammar.TypeCheck
--import GF.Grammar.Values (cPredefAbs) ---


--import GF.Grammar.LookAbs
--import GF.Grammar.ReservedWords ----
import GF.Devel.Grammar.PatternMatch (testOvershadow)
import GF.Devel.Grammar.AppPredefined
--import GF.Grammar.Lockfield (isLockLabel)

import GF.Devel.CheckM

import GF.Data.Operations

import Data.List
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Monad
import Debug.Trace ---


showCheckModule :: GF -> SourceModule -> Err (SourceModule,String)
showCheckModule mos m = do
  (st,(_,msg)) <- checkStart $ checkModule mos m
  return (st, unlines $ reverse msg)

checkModule :: GF -> SourceModule -> Check SourceModule
checkModule gf0 (name,mo) = checkIn ("checking module" +++ prt name) $ do
  let gr = gf0 {gfmodules = Map.insert name mo (gfmodules gf0)}
----  checkRestrictedInheritance gr (name, mo)
  mo1 <- case mtype mo of
    MTAbstract -> judgementOpModule (checkAbsInfo gr name) mo
    MTGrammar -> entryOpModule (checkResInfo gr name) mo

    MTConcrete aname -> do
      checkErr $ topoSortOpers $ allOperDependencies name $ mjments mo
      abs <- checkErr $ lookupModule gr aname
      mo1 <- checkCompleteGrammar abs mo
      entryOpModule (checkCncInfo gr name (aname,abs)) mo1

    MTInterface -> entryOpModule (checkResInfo gr name) mo

    MTInstance iname -> do
      intf <- checkErr $ lookupModule gr iname
      -- checkCompleteInstance abs mo -- this is done in Rebuild
      entryOpModule  (checkResInfo gr name) mo

  return $ (name, mo1)

{- ----
-- check if restricted inheritance modules are still coherent
-- i.e. that the defs of remaining names don't depend on omitted names
---checkRestrictedInheritance :: [SourceModule] -> SourceModule -> Check ()
checkRestrictedInheritance mos (name,mo) = do
  let irs = [ii | ii@(_,mi) <- extend mo, mi /= MIAll]  -- names with restr. inh.
  let mrs = [((i,m),mi) | (i,ModMod m) <- mos, Just mi <- [lookup i irs]] 
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
   allDeps = ---- transClosure $ Map.fromList $ 
             concatMap (allDependencies (const True)) 
                              [jments m | (_,ModMod m) <- mos]
   transClosure ds = ds ---- TODO: check in deeper modules
-}


-- | check if a term is typable
justCheckLTerm :: GF -> Term -> Err Term
justCheckLTerm src t = do
  ((t',_),_) <- checkStart (inferLType src t)
  return t'

checkAbsInfo :: GF -> Ident -> Judgement -> Check Judgement
checkAbsInfo st m info = return info ----

{-
checkAbsInfo st m (c,info) = do
---- checkReservedId c
 case info of
   AbsCat (Yes cont) _ -> mkCheck "category" $ 
     checkContext st cont ---- also cstrs
   AbsFun (Yes typ0) md -> do
    typ <- compAbsTyp [] typ0   -- to calculate let definitions
    mkCheck "type of function" $ checkTyp st typ 
    md' <- case md of
       Yes d -> do
         let d' = elimTables d
         mkCheckWarn "definition of function" $ checkEquation st (m,c) d'
         return $ Yes d'
       _ -> return md
    return $ (c,AbsFun (Yes typ) md')
   _ -> return (c,info)
 where
   mkCheck cat ss = case ss of
     [] -> return (c,info)
     ["[]"] -> return (c,info) ----
     _  -> checkErr $ prtBad (unlines ss ++++ "in" +++ cat) c
   ---- temporary solution when tc of defs is incomplete
   mkCheckWarn cat ss = case ss of
     [] -> return (c,info)
     ["[]"] -> return (c,info) ----
     _  -> checkWarn (unlines ss ++++ "in" +++ cat +++ prt c) >> return (c,info)
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

   elimTables e = case e of
     S t a  -> elimSel (elimTables t) (elimTables a)
     T _ cs -> Eqs [(elimPatt p, elimTables t) | (p,t) <- cs]
     _ -> composSafeOp elimTables e
   elimPatt p = case p of
     PR lps -> map snd lps
     _ -> [p]
   elimSel t a = case a of
     R fs -> mkApp t (map (snd . snd) fs)
     _ -> mkApp t [a]
-}


checkCompleteGrammar :: Module -> Module -> Check Module
checkCompleteGrammar abs cnc = do
  let js = mjments cnc
  let fs = Map.assocs $ mjments abs
  js' <- foldM checkOne js fs
  return $ cnc {mjments = js'}
 where
   checkOne js i@(c, Left ju) = case jform ju of
     JFun -> case Map.lookup c js of
       Just (Left j) | jform j == JLin -> return js
       _ -> do
         checkWarn $ "WARNING: no linearization of" +++ prt c
         return js
     JCat -> case Map.lookup c js of
       Just (Left j) | jform ju == JLincat -> return js  
       _ -> do        ---- TODO: other things to check here
         checkWarn $ 
           "Warning: no linearization type for" +++ prt c ++ 
           ", inserting default {s : Str}" 
         return $ Map.insert c (Left (cncCat defLinType)) js
     _ -> return js

checkResInfo :: GF -> Ident -> Ident -> Judgement -> Check Judgement
checkResInfo gr mo c info = do
  ----  checkReservedId c
  case jform info of
    JOper -> chIn "operation" $ case (jtype info, jdef info) of
      (_,Meta _) -> do
        checkWarn "No definition given to oper"
        return info
      (Meta _,de) -> do
        (de',ty') <- infer de
        ---- trace ("inferred" +++ prt de' +++ ":" +++ prt ty') $ 
        return (resOper ty' de')
      (ty, de) -> do
        ty'     <- check ty typeType >>= comp . fst
        (de',_) <- check de ty'
        return (resOper ty' de')
{- ----
    ResOverload tysts -> chIn "overloading" $ do
      tysts' <- mapM (uncurry $ flip check) tysts
      let tysts2 = [(y,x) | (x,y) <- tysts']
      --- this can only be a partial guarantee, since matching
      --- with value type is only possible if expected type is given
      checkUniq $ 
        sort [t : map snd xs | (x,_) <- tysts2, let (xs,t) = prodForm x]
      return (c,ResOverload tysts2)
-}
{- ----
    ResParam (Yes (pcs,_)) -> chIn "parameter type" $ do
----      mapM ((mapM (computeLType gr . snd)) . snd) pcs
      mapM_ ((mapM_ (checkIfParType gr . snd)) . snd) pcs
      ts <- checkErr $ lookupParamValues gr mo c
      return (c,ResParam (Yes (pcs, Just ts)))
-}
    _ ->  return info
 where
   infer = inferLType gr
   check = checkLType gr
   chIn cat = checkIn ("Happened in" +++ cat +++ prt c +++ ":")
   comp = computeLType gr

   checkUniq xss = case xss of
     x:y:xs 
      | x == y -> raise $ "ambiguous for argument list" +++ 
                         unwords (map (prtType gr) x)  
      | otherwise -> checkUniq $ y:xs
     _ -> return ()


checkCncInfo :: GF -> Ident -> SourceModule -> 
                Ident -> Judgement -> Check Judgement
checkCncInfo gr cnc (a,abs) c info = do
  ----  checkReservedId c
  case jform info of
    JFun -> chIn "linearization of" $ do
      typ        <- checkErr $ lookupFunType gr a c
      cat0       <- checkErr $ valCat typ
      (cont,val) <- linTypeOfType gr cnc typ     -- creates arg vars
      let lintyp = mkFunType (map snd cont) val
      (trm',_)   <- check (jdef info) lintyp     -- erases arg vars
      checkPrintname gr (jprintname info)
      cat        <- return $ snd cat0
      return (info {jdef = trm'})
      ---- return (c, CncFun (Just (cat,(cont,val))) (Yes trm') mpr)
                                                   -- cat for cf, typ for pe

    JCat -> chIn "linearization type of" $ do
      checkErr $ lookupCatContext gr a c
      typ'  <- checkIfLinType gr (jtype info)
    {- ----
      mdef' <- case mdef of
        Yes def -> do
          (def',_) <- checkLType gr def (mkFunType [typeStr] typ)
          return $ Yes def'
        _ -> return mdef
    -}
      checkPrintname gr (jprintname info)
      return (info {jtype = typ'})

    _ -> checkResInfo gr cnc c info

 where
   env = gr
   infer = inferLType gr
   comp = computeLType gr 
   check = checkLType gr
   chIn cat = checkIn ("Happened in" +++ cat +++ prt c +++ ":")


checkIfParType :: GF -> Type -> Check ()
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

{- ----
checkIfStrType :: SourceGrammar -> Type -> Check ()
checkIfStrType st typ = case typ of
  Table arg val -> do
    checkIfParType st arg 
    checkIfStrType st val
  _ | typ == typeStr -> return ()
  _ -> prtFail "not a string type" typ
-}

checkIfLinType :: GF -> Type -> Check Type
checkIfLinType st typ0 = do
  typ <- computeLType st typ0
  case typ of
    RecType r -> return ()
    _ -> prtFail "a linearization type must be a record type instead of" typ
  return typ

computeLType :: GF -> Type -> Check Type
computeLType gr t = do
  g0 <- checkGetContext
  let g = [(x, Vr x) | (x,_) <- g0]
  checkInContext g $ comp t
 where
  comp ty = case ty of

    App (Q (IC "Predef") (IC "Ints")) _ -> return ty ---- shouldn't be needed
    Q (IC "Predef") (IC "Int")          -> return ty ---- shouldn't be needed
    Q (IC "Predef") (IC "Float")        -> return ty ---- shouldn't be needed
    Q (IC "Predef") (IC "Error")        -> return ty ---- shouldn't be needed

    Q m c | elem c [cPredef,cPredefAbs] -> return ty
    Q m c | elem c [identC "Int"] -> 
      return $ defLinType
----      let ints k = App (Q (IC "Predef") (IC "Ints")) (EInt k) in
----      RecType [
----        (LIdent "last",ints 9),(LIdent "s", typeStr), (LIdent "size",ints 1)]
    Q m c | elem c [identC "Float",identC "String"] -> return defLinType ----

    Q m ident -> checkIn ("module" +++ prt m) $ do
      ty' <- checkErr (lookupOperDef gr m ident) 
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
      let fs' = sortBy (\x y -> compare (fst x) (fst y)) fs
      liftM RecType $ mapPairsM comp fs'

    _ | ty == typeTok -> return typeStr  ---- deprecated
    _ | isPredefConstant ty -> return ty

    _ -> composOp comp ty

checkPrintname :: GF -> Term -> Check ()
---- checkPrintname st (Yes t) = checkLType st t typeStr >> return ()
checkPrintname _ _ = return ()

{- ----
-- | for grammars obtained otherwise than by parsing ---- update!!
checkReservedId :: Ident -> Check ()
checkReservedId x = let c = prt x in
         if isResWord c 
            then checkWarn ("Warning: reserved word used as identifier:" +++ c)
            else return ()
-}

-- to normalize records and record types
labelIndex :: Type -> Label -> Int
labelIndex ty lab = case ty of
  RecType ts -> maybe (error ("label index"+++ prt lab)) id $ lookup lab $ labs ts
  _ -> error $ "label index" +++ prt ty
 where 
  labs ts = zip (map fst (sortBy (\ x y -> compare (fst x) (fst y)) ts)) [0..]

-- the underlying algorithms

inferLType :: GF -> Term -> Check (Term, Type)
inferLType gr trm = case trm of

   Q m ident | isPredef m -> termWith trm $ checkErr (typPredefined ident)

   Q m ident -> checks [
     termWith trm $ checkErr (lookupOperType gr m ident) >>= comp
     ,
     checkErr (lookupOperDef gr m ident) >>= infer
     ,
{-
     do
       over <- getOverload gr Nothing trm
       case over of
         Just trty -> return trty
         _ -> prtFail "not overloaded" trm
     ,
-}
     prtFail "cannot infer type of constant" trm
     ]

   QC m ident | isPredef m -> termWith trm $ checkErr (typPredefined ident)

   QC m ident -> checks [
       termWith trm $ checkErr (lookupOperType gr m ident) >>= comp
       ,
       checkErr (lookupOperDef gr m ident) >>= infer
       ,
       prtFail "cannot infer type of canonical constant" trm
       ]

   Val ty i -> termWith trm $ return ty

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
        then checkWarn ("WARNING: space in token \"" ++ s ++ 
                        "\". Lexical analysis may fail.")
        else return ()
     return (trm, typeStr)

   EInt i -> return (trm, typeInt)

   EFloat i -> return (trm, typeFloat)

   Empty -> return (trm, typeStr)

   C s1 s2 -> 
     check2 (flip justCheck typeStr) C s1 s2 typeStr

   Glue s1 s2 -> 
     check2 (flip justCheck typeStr) Glue s1 s2 typeStr

---- hack from Rename.identRenameTerm, to live with files with naming conflicts 18/6/2007
----   Strs (Cn (IC "#conflict") : ts) -> do
----     trace ("WARNING: unresolved constant, could be any of" +++ unwords (map prt ts)) (infer $ head ts)
--     checkWarn ("WARNING: unresolved constant, could be any of" +++ unwords (map prt ts))
--     infer $ head ts


   Alts (t,aa) -> do
     t'  <- justCheck t typeStr
     aa' <- flip mapM aa (\ (c,v) -> do
        c' <- justCheck c typeStr 
        v' <- justCheck v typeStr
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
     PSeq p q -> isConstPatt p && isConstPatt q
     PAlt p q -> isConstPatt p && isConstPatt q
     PRep p -> isConstPatt p
     PNeg p -> isConstPatt p
     PAs _ p -> isConstPatt p
     _ -> False

   inferPatt p = case p of
     PP q c ps | q /= cPredef -> checkErr $ lookupOperType gr q c >>= return . snd . prodForm
     PAs _ p  -> inferPatt p
     PNeg p   -> inferPatt p
     PAlt p q -> checks [inferPatt p, inferPatt q]
     PSeq _ _ -> return $ typeStr
     PRep _   -> return $ typeStr
     _ -> infer (patt2term p) >>= return . snd


-- type inference: Nothing, type checking: Just t
-- the latter permits matching with value type
getOverload :: GF -> Maybe Type -> Term -> Check (Maybe (Term,Type))
getOverload env@gr mt t = case appForm t of
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

     case [vf | vf@(v,f) <- vfs, matchVal mt v] of
       [(val,fun)] -> return (mkApp fun tts, val)
       [] -> raise $ "no overload instance of" +++ prt f +++ 
         "for" +++ unwords (map (prtType env) tys) +++ "among" ++++ 
         unlines ["  " ++ unwords (map (prtType env) ty) | (ty,_) <- typs] ++
         maybe [] (("with value type" +++) . prtType env) mt

      ----  ++++ "DEBUG" +++ unwords (map show tys) +++ ";" 
      ----  ++++ unlines (map (show . fst) typs) ----

       vfs' -> case [(v,f) | (v,f) <- vfs', noProd v] of
         [(val,fun)] -> do
           checkWarn $ "WARNING: overloading of" +++ prt f +++ 
             "resolved by excluding partial applications:" ++++
             unlines [prtType env ty | (ty,_) <- vfs', not (noProd ty)]
           return (mkApp fun tts, val)

         _ -> raise $ "ambiguous overloading of" +++ prt f +++
           "for" +++ unwords (map (prtType env) tys) ++++ "with alternatives" ++++ 
           unlines [prtType env ty | (ty,_) <- vfs']

   matchVal mt v = elem mt ([Nothing,Just v] ++ unlocked) where
     unlocked = case v of
       RecType fs -> [Just $ RecType $ fs] ---- filter (not . isLockLabel . fst) fs]
       _ -> []
   ---- TODO: accept subtypes
   ---- TODO: use a trie
   lookupOverloadInstance tys typs = 
     [(mkFunType rest val, t) | 
       let lt = length tys,
       (ty,(val,t)) <- typs, length ty >= lt,
       let (pre,rest) = splitAt lt ty, 
       pre == tys
     ]

   noProd ty = case ty of
     Prod _ _ _ -> False
     _ -> True

checkLType :: GF -> Term -> Type -> Check (Term, Type)
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
        _ -> raise $ "product expected instead of" +++ prtType env typ

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

    EData -> return (trm,typ)

    T _ [] ->
      prtFail "found empty table in type" typ
    T _ cs -> case typ of 
      Table arg val -> do 
        case allParamValues env arg of
          Ok vs -> do
            let ps0 = map fst cs
            ps <- return [] ---- checkErr $ testOvershadow ps0 vs
            if null ps 
              then return () 
              else checkWarn $ "WARNING: patterns never reached:"
                               ---- +++ concat (intersperse ", " (map prt ps))

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
     _ -> prtFail "cannot find value for label" l

   checkCase arg val (p,t) = do
     cont <- pattContext env arg p
     i    <- checkUpdates cont
     t'   <- justCheck t val
     checkResets i
     return (p,t')

pattContext :: LTEnv -> Type -> Patt -> Check Context
pattContext env typ p = case p of
  PV x | not (isWildIdent x) -> return [(x,typ)]
  PP q c ps | q /= cPredef -> do ---- why this /=? AR 6/1/2006
    t <- checkErr $ lookupOperType cnc q c
    let (cont,v) = prodForm t
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

type LTEnv = GF

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
        checkWarn $ "WARNING: missing lock field" +++ unwords (map prt lo)
        return (True,t',u',[])
      Bad s -> return (False,t',u',s)

  where

   -- t is a subtype of u 
   --- quick hack version of TC.eqVal
   alpha g t u = case (t,u) of  

     -- error (the empty type!) is subtype of any other type
     (_,Q (IC "Predef") (IC "Error")) -> True

     -- unknown type unifies with any type ----
     (_,Meta _) -> True

     -- contravariance
     (Prod x a b, Prod y c d) -> alpha g c a && alpha ((x,y):g) b d 
                              
     -- record subtyping
     (RecType rs, RecType ts) -> all (\ (l,a) -> 
                                   any (\ (k,b) -> alpha g a b && l == k) ts) rs
     (ExtR r s, ExtR r' s') -> alpha g r r' && alpha g s s'
     (ExtR r s, t) -> alpha g r t || alpha g s t

     -- the following say that Ints n is a subset of Int and of Ints m >= n
     (App (Q (IC "Predef") (IC "Ints")) (EInt n), 
        App (Q (IC "Predef") (IC "Ints")) (EInt m)) -> m >= n
     (App (Q (IC "Predef") (IC "Ints")) (EInt n), 
        Q (IC "Predef") (IC "Int"))                 -> True ---- check size!
     
     (Q (IC "Predef") (IC "Int"),  ---- why this ???? AR 11/12/2005
        App (Q (IC "Predef") (IC "Ints")) (EInt n)) -> True

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
         (locks,others) = partition (const False) ls ---- isLockLabel ls
       in case others of
         _:_ -> Bad $ "missing record fields" +++ unwords (map prt others)
         _ -> return locks
     -- contravariance
     (Prod x a b, Prod y c d) -> do
        ls1 <- missingLock g c a
        ls2 <- missingLock g b d
        return $ ls1 ++ ls2

     _ -> Bad ""

   ---- to revise
   allExtendsPlus _ n = [n]

   sTypes = [typeStr, typeString, typeTok] ---- Tok deprecated
   comp = computeLType env

-- printing a type with a lock field lock_C as C
prtType :: LTEnv -> Type -> String
prtType env ty = case ty of
  RecType fs -> ---- case filter isLockLabel $ map fst fs of
   ---- [lock] -> (drop 5 $ prt lock) --- ++++ "Full form" +++ prt ty
   ---- _ -> 
   prtt ty
  Prod x a b -> prtType env a +++ "->" +++ prtType env b
  _ -> prtt ty
 where
   prtt t = prt t
   ---- use computeLType gr to check if really equal to the cat with lock


-- | linearization types and defaults
linTypeOfType :: GF -> Ident -> Type -> Check (Context,Type)
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
     rec <- checkErr $ errIn ("extending" +++ prt vars +++ "with" +++ prt val) $
            plusRecType vars val
     return (symb,rec)
   lookLin (_,c) = checks [ --- rather: update with defLinType ?
      checkErr (lookupLincat cnc m c) >>= computeLType cnc
     ,return defLinType
     ]

-- | dependency check, detecting circularities and returning topo-sorted list

allOperDependencies :: Ident -> Map.Map Ident JEntry -> [(Ident,[Ident])]
allOperDependencies m = allDependencies (==m)

allDependencies :: (Ident -> Bool) -> Map.Map Ident JEntry -> [(Ident,[Ident])]
allDependencies ism b = 
  [(f, nub (concatMap opersIn (pts i))) | (f,Left i) <- Map.assocs b]
  where
    opersIn t = case t of
      Q n c | ism n -> [c]
      QC n c | ism n -> [c]
      _ -> collectOp opersIn t
    pts i = [jtype i, jdef i]
    ----  AbsFun pty ptr -> [pty] --- ptr is def, which can be mutual
 
topoSortOpers :: [(Ident,[Ident])] -> Err [Ident]
topoSortOpers st = do
  let eops = topoTest st
  either 
    return 
    (\ops -> Bad ("circular definitions:" +++ unwords (map prt (head ops))))
    eops
