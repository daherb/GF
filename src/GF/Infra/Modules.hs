----------------------------------------------------------------------
-- |
-- Module      : Modules
-- Maintainer  : AR
-- Stability   : (stable)
-- Portability : (portable)
--
-- > CVS $Date: 2005/11/09 15:14:30 $ 
-- > CVS $Author: aarne $
-- > CVS $Revision: 1.26 $
--
-- Datastructures and functions for modules, common to GF and GFC.
--
-- AR 29\/4\/2003
--
-- The same structure will be used in both source code and canonical.
-- The parameters tell what kind of data is involved.
-- Invariant: modules are stored in dependency order
-----------------------------------------------------------------------------

module GF.Infra.Modules (
		MGrammar(..), ModInfo(..), Module(..), ModuleType(..),
		MReuseType(..), MInclude (..),
		extends, isInherited,inheritAll, 
                updateMGrammar, updateModule, replaceJudgements, addFlag,
		addOpenQualif, flagsModule, allFlags, mapModules, mapModules',
		MainGrammar(..), MainConcreteSpec(..), OpenSpec(..), OpenQualif(..),
		oSimple, oQualif,
		ModuleStatus(..),
		openedModule, allOpens, depPathModule, allDepsModule, partOfGrammar,
		allExtends, allExtendSpecs, allExtendsPlus, allExtensions, 
                searchPathModule, addModule,
		emptyMGrammar, emptyModInfo, emptyModule,
		IdentM(..),
		typeOfModule, abstractOfConcrete, abstractModOfConcrete,
		lookupModule, lookupModuleType, lookupModMod, lookupInfo,
                lookupPosition, showPosition,
		allModMod, isModAbs, isModRes, isModCnc, isModTrans,
		sameMType, isCompilableModule, isCompleteModule,
		allAbstracts, greatestAbstract, allResources,
		greatestResource, allConcretes, allConcreteModules
	       ) where

import GF.Infra.Ident
import GF.Infra.Option
import GF.Data.Operations

import Data.List


-- AR 29/4/2003

-- The same structure will be used in both source code and canonical.
-- The parameters tell what kind of data is involved.
-- Invariant: modules are stored in dependency order

data MGrammar i a = MGrammar {modules :: [(i,ModInfo i a)]}
  deriving Show

data ModInfo i a =
    ModMainGrammar (MainGrammar i)
  | ModMod  (Module i a)
  | ModWith (Module i a) (i,MInclude i) [OpenSpec i]
  deriving Show

data Module i a = Module {
    mtype   :: ModuleType i ,
    mstatus :: ModuleStatus ,
    flags   :: Options,
    extend  :: [(i,MInclude i)],
    opens   :: [OpenSpec i] ,
    jments  :: BinTree i a ,
    positions :: BinTree i (String,(Int,Int)) -- file, first line, last line
  }
---  deriving Show
instance Show (Module i a) where
  show _ = "cannot show Module with FiniteMap"

-- | encoding the type of the module
data ModuleType i = 
    MTAbstract 
  | MTTransfer (OpenSpec i) (OpenSpec i) 
  | MTResource
  | MTConcrete i
    -- ^ up to this, also used in GFC. Below, source only.
  | MTInterface
  | MTInstance i 
  | MTReuse (MReuseType i)
  | MTUnion (ModuleType i) [(i,[i])] -- ^ not meant to be recursive
  deriving (Eq,Show)

data MReuseType i = MRInterface i | MRInstance i i | MRResource i
  deriving (Show,Eq)

data MInclude i = MIAll | MIOnly [i] | MIExcept [i]
  deriving (Show,Eq)

extends :: Module i a -> [i]
extends = map fst . extend

isInherited :: Eq i => MInclude i -> i -> Bool
isInherited c i = case c of
  MIAll -> True
  MIOnly is -> elem i is
  MIExcept is -> notElem i is

inheritAll :: i -> (i,MInclude i)
inheritAll i = (i,MIAll)

-- destructive update

-- | dep order preserved since old cannot depend on new
updateMGrammar :: Ord i => MGrammar i a -> MGrammar i a -> MGrammar i a
updateMGrammar old new = MGrammar $ 
  [(i,m) | (i,m) <- os, notElem i (map fst ns)] ++ ns
 where
   os = modules old
   ns = modules new

updateModule :: Ord i => Module i t -> i -> t -> Module i t
updateModule (Module  mt ms fs me ops js ps) i t = 
  Module mt ms fs me ops (updateTree (i,t) js) ps

replaceJudgements :: Module i t -> BinTree i t -> Module i t
replaceJudgements (Module mt ms fs me ops _ ps) js = Module mt ms fs me ops js ps

addOpenQualif :: i -> i -> Module i t -> Module i t
addOpenQualif i j (Module mt ms fs me ops js ps) = 
  Module mt ms fs me (oQualif i j : ops) js ps

addFlag :: Options -> Module i t -> Module i t
addFlag f mo = mo {flags = flags mo `addOptions` f} 

flagsModule :: (i,ModInfo i a) -> Options
flagsModule (_,mi) = case mi of
  ModMod m -> flags m
  _ -> noOptions

allFlags :: MGrammar i a -> Options
allFlags gr = concatOptions $ map flags $ [m | (_, ModMod m) <- modules gr]

mapModules :: (Module i a -> Module i a) 
	   -> MGrammar i a -> MGrammar i a 
mapModules f = MGrammar . map (onSnd (mapModules' f)) . modules

mapModules' :: (Module i a -> Module i a) 
	   -> ModInfo i a -> ModInfo i a 
mapModules' f (ModMod m) = ModMod (f m)
mapModules' _ m = m

data MainGrammar i = MainGrammar {
    mainAbstract  :: i ,
    mainConcretes :: [MainConcreteSpec i]
  }
  deriving Show

data MainConcreteSpec i = MainConcreteSpec {
    concretePrintname :: i ,
    concreteName :: i ,
    transferIn   :: Maybe (OpenSpec i) ,  -- ^ if there is an in-transfer
    transferOut  :: Maybe (OpenSpec i)    -- ^ if there is an out-transfer
  }
  deriving Show

data OpenSpec i = 
   OSimple OpenQualif i 
 | OQualif OpenQualif i i
  deriving (Eq,Show)

data OpenQualif =
   OQNormal
 | OQInterface
 | OQIncomplete
  deriving (Eq,Show)

oSimple :: i -> OpenSpec i
oSimple = OSimple OQNormal

oQualif :: i -> i -> OpenSpec i
oQualif = OQualif OQNormal

data ModuleStatus = 
   MSComplete 
 | MSIncomplete 
  deriving (Eq,Show)

openedModule :: OpenSpec i -> i
openedModule o = case o of
  OSimple _ m -> m
  OQualif _ _ m -> m

allOpens :: Module i a -> [OpenSpec i]
allOpens m = case mtype m of
  MTTransfer a b -> a : b : opens m
  _ -> opens m

-- | initial dependency list
depPathModule :: Ord i => Module i a -> [OpenSpec i]
depPathModule m = fors m ++ exts m ++ opens m where
  fors m = case mtype m of
    MTTransfer i j -> [i,j]
    MTConcrete i   -> [oSimple i]
    MTInstance i   -> [oSimple i]
    _              -> []
  exts m = map oSimple $ extends m

-- | all dependencies
allDepsModule :: Ord i => MGrammar i a -> Module i a -> [OpenSpec i]
allDepsModule gr m = iterFix add os0 where
  os0 = depPathModule m
  add os = [m | o <- os, Just (ModMod n) <- [lookup (openedModule o) mods], 
                m <- depPathModule n]
  mods = modules gr

-- | select just those modules that a given one depends on, including itself
partOfGrammar :: Ord i => MGrammar i a -> (i,ModInfo i a) -> MGrammar i a
partOfGrammar gr (i,m) = MGrammar [mo | mo@(j,_) <- mods, elem j modsFor] 
  where
    mods = modules gr
    modsFor = case m of
      ModMod n -> (i:) $ map openedModule $ allDepsModule gr n
      ---- ModWith n i os -> i : map openedModule os ++ partOfGrammar (ModMod n) ----
      _ -> [i]

-- | all modules that a module extends, directly or indirectly, without restricts
allExtends :: (Show i,Ord i) => MGrammar i a -> i -> [i]
allExtends gr i = case lookupModule gr i of
  Ok (ModMod m) -> case extends m of 
    [] -> [i]
    is -> i : concatMap (allExtends gr) is
  _ -> []

-- | all modules that a module extends, directly or indirectly, with restricts
allExtendSpecs :: (Show i,Ord i) => MGrammar i a -> i -> [(i,MInclude i)]
allExtendSpecs gr i = case lookupModule gr i of
  Ok (ModMod m) -> case extend m of 
    [] -> [(i,MIAll)]
    is -> (i,MIAll) : concatMap (allExtendSpecs gr . fst) is
  _ -> []

-- | this plus that an instance extends its interface
allExtendsPlus :: (Show i,Ord i) => MGrammar i a -> i -> [i]
allExtendsPlus gr i = case lookupModule gr i of
  Ok (ModMod m) -> i : concatMap (allExtendsPlus gr) (exts m)
  _ -> []
 where
   exts m = extends m ++ [j | MTInstance j <- [mtype m]]

-- | conversely: all modules that extend a given module, incl. instances of interface
allExtensions :: (Show i,Ord i) => MGrammar i a -> i -> [i]
allExtensions gr i = case lookupModule gr i of
  Ok (ModMod m) -> let es = exts i in es ++ concatMap (allExtensions gr) es
  _ -> []
 where
   exts i = [j | (j,m) <- mods, elem i (extends m) 
                             || elem (MTInstance i) [mtype m]]
   mods = [(j,m) | (j,ModMod m) <- modules gr]

-- | initial search path: the nonqualified dependencies
searchPathModule :: Ord i => Module i a -> [i]
searchPathModule m = [i | OSimple _ i <- depPathModule m]

-- | a new module can safely be added to the end, since nothing old can depend on it
addModule :: Ord i => 
             MGrammar i a -> i -> ModInfo i a -> MGrammar i a
addModule gr name mi = MGrammar $ (modules gr ++ [(name,mi)])

emptyMGrammar :: MGrammar i a
emptyMGrammar = MGrammar []

emptyModInfo :: ModInfo i a
emptyModInfo = ModMod emptyModule

emptyModule :: Module i a
emptyModule = Module 
  MTResource MSComplete noOptions [] [] emptyBinTree emptyBinTree

-- | we store the module type with the identifier
data IdentM i = IdentM {
  identM :: i ,
  typeM  :: ModuleType i
  }
  deriving (Eq,Show)

typeOfModule :: ModInfo i a -> ModuleType i
typeOfModule mi = case mi of
  ModMod m -> mtype m

abstractOfConcrete :: (Show i, Eq i) => MGrammar i a -> i -> Err i
abstractOfConcrete gr c = do
  m <- lookupModule gr c
  case m of
    ModMod n -> case mtype n of
      MTConcrete a -> return a
      _ -> Bad $ "expected concrete" +++ show c
    _ -> Bad $ "expected concrete" +++ show c

abstractModOfConcrete :: (Show i, Eq i) => 
                         MGrammar i a -> i -> Err (Module i a)
abstractModOfConcrete gr c = do
  a <- abstractOfConcrete gr c
  m <- lookupModule gr a
  case m of
    ModMod n -> return n
    _ -> Bad $ "expected abstract" +++ show c


-- the canonical file name

--- canonFileName s = prt s ++ ".gfc"

lookupModule :: (Show i,Eq i) => MGrammar i a -> i -> Err (ModInfo i a)
lookupModule gr m = case lookup m (modules gr) of
  Just i -> return i
  _ -> Bad $ "unknown module" +++ show m 
             +++ "among" +++ unwords (map (show . fst) (modules gr)) ---- debug

lookupModuleType :: (Show i,Eq i) => MGrammar i a -> i -> Err (ModuleType i)
lookupModuleType gr m = do
  mi <- lookupModule gr m
  return $ typeOfModule mi

lookupModMod :: (Show i,Eq i) => MGrammar i a -> i -> Err (Module i a)
lookupModMod gr i = do
  mo <- lookupModule gr i
  case mo of 
    ModMod m -> return m
    _ -> Bad $ "expected proper module, not" +++ show i

lookupInfo :: (Show i, Ord i) => Module i a -> i -> Err a
lookupInfo mo i = lookupTree show i (jments mo)

lookupPosition :: (Show i, Ord i) => Module i a -> i -> Err (String,(Int,Int))
lookupPosition mo i = lookupTree show i (positions mo)

showPosition :: (Show i, Ord i) => Module i a -> i -> String
showPosition mo i = case lookupPosition mo i of
  Ok (f,(b,e)) | b == e -> "in" +++ f ++ ", line" +++ show b
  Ok (f,(b,e)) -> "in" +++ f ++ ", lines" +++ show b ++ "-" ++ show e
  _ -> ""


allModMod :: (Show i,Eq i) => MGrammar i a -> [(i,Module i a)]
allModMod gr = [(i,m) | (i, ModMod m) <- modules gr]

isModAbs :: Module i a -> Bool
isModAbs m = case mtype m of
  MTAbstract -> True
----  MTUnion t -> isModAbs t
  _ -> False

isModRes :: Module i a -> Bool
isModRes m = case mtype m of
  MTResource -> True
  MTReuse _ -> True
----  MTUnion t -> isModRes t --- maybe not needed, since eliminated early
  MTInterface -> True ---
  MTInstance _ -> True
  _ -> False

isModCnc :: Module i a -> Bool
isModCnc m = case mtype m of
  MTConcrete _ -> True
----  MTUnion t -> isModCnc t
  _ -> False

isModTrans :: Module i a -> Bool
isModTrans m = case mtype m of
  MTTransfer _ _ -> True
----  MTUnion t -> isModTrans t
  _ -> False

sameMType :: Eq i => ModuleType i -> ModuleType i -> Bool
sameMType m n = case (n,m) of
  (MTConcrete _, MTConcrete _) -> True

  (MTInstance _, MTInstance _) -> True
  (MTInstance _, MTResource)   -> True
  (MTInstance _, MTConcrete _) -> True

  (MTInterface,  MTInstance _) -> True
  (MTInterface,  MTResource)   -> True    -- for reuse
  (MTInterface,  MTAbstract)   -> True    -- for reuse
  (MTInterface,  MTConcrete _) -> True    -- for reuse

  (MTResource,   MTInstance _) -> True
  (MTResource,   MTConcrete _) -> True    -- for reuse

  _ -> m == n

-- | don't generate code for interfaces and for incomplete modules
isCompilableModule :: ModInfo i a -> Bool
isCompilableModule m = case m of
  ModMod m -> case mtype m of
    MTInterface -> False
    _ -> mstatus m == MSComplete
  _ -> False ---

-- | interface and "incomplete M" are not complete
isCompleteModule :: (Eq i) =>  Module i a -> Bool
isCompleteModule m = mstatus m == MSComplete && mtype m /= MTInterface


-- | all abstract modules sorted from least to most dependent
allAbstracts :: Eq i => MGrammar i a -> [i]
allAbstracts gr = topoSort 
  [(i,extends m) | (i,ModMod m) <- modules gr, mtype m == MTAbstract]

-- | the last abstract in dependency order (head of list)
greatestAbstract :: Eq i => MGrammar i a -> Maybe i
greatestAbstract gr = case allAbstracts gr of
  [] -> Nothing
  as -> return $ last as

-- | all resource modules
allResources :: MGrammar i a -> [i]
allResources gr = [i | (i,ModMod m) <- modules gr, isModRes m || isModCnc m]

-- | the greatest resource in dependency order
greatestResource :: MGrammar i a -> Maybe i
greatestResource gr = case allResources gr of
  [] -> Nothing
  a -> return $ head a ---- why not last as in Abstract? works though AR 24/5/2008

-- | all concretes for a given abstract
allConcretes :: Eq i => MGrammar i a -> i -> [i]
allConcretes gr a = 
  [i | (i, ModMod m) <- modules gr, mtype m == MTConcrete a, isCompleteModule m]

-- | all concrete modules for any abstract
allConcreteModules :: Eq i => MGrammar i a -> [i]
allConcreteModules gr = 
  [i | (i, ModMod m) <- modules gr, MTConcrete _ <- [mtype m], isCompleteModule m]
