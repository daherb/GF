----------------------------------------------------------------------
-- |
-- Module      : (Module)
-- Maintainer  : (Maintainer)
-- Stability   : (stable)
-- Portability : (portable)
--
-- > CVS $Date: 2005/02/18 19:21:22 $ 
-- > CVS $Author: peb $
-- > CVS $Revision: 1.3 $
--
-- (Description of the module)
-----------------------------------------------------------------------------

module Information where

import Grammar
import Ident
import Modules
import Option
import CF
import PPrCF
import ShellState
import PrGrammar
import Lookup
import qualified GFC
import qualified AbsGFC

import Operations
import UseIO

-- information on module, category, function, operation, parameter,... AR 16/9/2003
-- uses source grammar

-- the top level function

showInformation :: Options -> ShellState -> Ident -> IOE ()
showInformation opts st c = do
  is <- ioeErr $ getInformation opts st c
  mapM_ (putStrLnE . prInformation opts c) is

-- the data type of different kinds of information

data Information = 
   IModAbs  SourceAbs
 | IModRes  SourceRes
 | IModCnc  SourceCnc
 | IModule  SourceAbs ---- to be deprecated
 | ICatAbs  Ident Context [Ident]
 | ICatCnc  Ident Type    [CFRule] Term
 | IFunAbs  Ident Type    (Maybe Term)
 | IFunCnc  Ident Type    [CFRule] Term
 | IOper    Ident Type    Term
 | IParam   Ident         [Param] [Term]
 | IValue   Ident Type

type CatId = AbsGFC.CIdent
type FunId = AbsGFC.CIdent

prInformation :: Options -> Ident -> Information -> String
prInformation opts c i = unlines $ prt c : case i of
  IModule m -> [
    "module of type" +++ show (mtype m),
    "extends" +++ show (extends m),
    "opens" +++ show (opens m),
    "defines" +++ unwords (map prt (ownConstants (jments m)))
    ]
  ICatAbs m co _ -> [
    "category in abstract module" +++ prt m,
    "context" +++ prContext co
    ]
  ICatCnc m ty cfs tr -> [
    "category in concrete module" +++ prt m,
    "linearization type" +++ prt ty
    ]
  IFunAbs m ty _ -> [
    "function in abstract module" +++ prt m,
    "type" +++ prt ty
    ]
  IFunCnc m ty cfs tr -> [
    "function in concrete module" +++ prt m,
    "linearization" +++ prt tr
   ---    "linearization type" +++ prt ty
    ]
  IOper m ty tr -> [
    "operation in resource module" +++ prt m,
    "type" +++ prt ty,
    "definition" +++ prt tr 
    ]
  IParam m ty ts -> [
    "parameter type in resource module" +++ prt m,
    "constructors" +++ unwords (map prParam ty),
    "values" +++ unwords (map prt ts)
    ]
  IValue m ty -> [
    "parameter constructor in resource module" +++ prt m,
    "type" +++ show ty
    ]

-- also finds out if an identifier is defined in many places

getInformation :: Options -> ShellState -> Ident -> Err [Information]
getInformation opts st c = allChecks $ [
  do
    m <- lookupModule src c 
    case m of
      ModMod mo -> return $ IModule mo
      _ -> prtBad "not a source module" c
  ] ++ map lookInSrc ss ++ map lookInCan cs
 where
   lookInSrc (i,m) = do
     j <- lookupInfo m c 
     case j of
       AbsCat (Yes co) _ -> return $ ICatAbs i co [] ---
       AbsFun (Yes ty) _ -> return $ IFunAbs i ty Nothing ---
       CncCat (Yes ty) _ _ -> do
         ---- let cat = ident2CFCat i c
         ---- rs <- concat [rs | (c,rs) <- cf, ]
         return $ ICatCnc i ty [] ty ---       
       CncFun _ (Yes tr) _ -> do
         rs <- return []
         return $ IFunCnc i tr rs tr ---       
       ResOper (Yes ty) (Yes tr) -> return $ IOper i ty tr
       ResParam (Yes ps) -> do
         ts <- allParamValues src (QC i c)
         return $ IParam i ps ts
       ResValue (Yes ty) -> return $ IValue i ty ---
       
       _ -> prtBad "nothing available for" i
   lookInCan (i,m) = do
     Bad "nothing available yet in canonical"

   src = srcModules st
   can = canModules st
   ss  = [(i,m) | (i,ModMod m) <- modules src]
   cs  = [(i,m) | (i,ModMod m) <- modules can]
   cf  = concatMap ruleGroupsOfCF $ map snd $ cfs st

ownConstants :: BinTree (Ident, Info) -> [Ident]
ownConstants = map fst . filter isOwn . tree2list where
  isOwn (c,i) = case i of
    AnyInd _ _ -> False
    _ -> True

