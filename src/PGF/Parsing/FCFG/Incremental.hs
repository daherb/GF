{-# LANGUAGE BangPatterns #-}
module PGF.Parsing.FCFG.Incremental
          ( ParseState
          , initState
          , nextState
          , getCompletions
          , extractExps
          , parse
          ) where

import Data.Array.IArray
import Data.Array.Base (unsafeAt)
import Data.List (isPrefixOf, foldl')
import Data.Maybe (fromMaybe, maybe)
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import Control.Monad

import GF.Data.SortedList
import PGF.CId
import PGF.Data
import Debug.Trace

parse :: ParserInfo -> Type -> [String] -> [Tree]
parse pinfo typ toks = maybe [] (\ps -> extractExps ps typ) (foldM nextState (initState pinfo typ) toks)

initState :: ParserInfo -> Type -> ParseState
initState pinfo (DTyp _ start _) = 
  let items = do
        cat <- fromMaybe [] (Map.lookup start (startCats pinfo))
        (funid,args) <- foldForest (\funid args -> (:) (funid,args)) (\_ _ args -> args)
                                   [] cat (productions pinfo)
        let FFun fn _ lins = functions pinfo ! funid
        (lbl,seqid) <- assocs lins
        return (Active 0 0 funid seqid args (AK cat lbl))
        
  in State pinfo
           (Chart emptyAC [] emptyPC (productions pinfo) (totalCats pinfo) 0)
           (Set.fromList items)

-- | From the current state and the next token
-- 'nextState' computes a new state where the token
-- is consumed and the current position shifted by one.
nextState :: ParseState -> String -> Maybe ParseState
nextState (State pinfo chart items) t =
  let (items1,chart1) = process (Just t) add (sequences pinfo) (functions pinfo) (Set.toList items) Set.empty chart
      chart2 = chart1{ active =emptyAC
                     , actives=active chart1 : actives chart1
                     , passive=emptyPC
                     , offset =offset chart1+1
                     }
  in if Set.null items1
       then Nothing
       else Just (State pinfo chart2 items1)
  where
    add (KS tok) item set
      | tok == t  = Set.insert item set
      | otherwise = set

-- | If the next token is not known but only its prefix (possible empty prefix)
-- then the 'getCompletions' function can be used to calculate the possible
-- next words and the consequent states. This is used for word completions in
-- the GF interpreter.
getCompletions :: ParseState -> String -> Map.Map String ParseState
getCompletions (State pinfo chart items) w =
  let (map',chart1) = process Nothing add (sequences pinfo) (functions pinfo) (Set.toList items) Map.empty chart
      chart2 = chart1{ active =emptyAC
                     , actives=active chart1 : actives chart1
                     , passive=emptyPC
                     , offset =offset chart1+1
                     }
  in fmap (State pinfo chart2) map'
  where
    add (KS tok) item map
      | isPrefixOf w tok = Map.insertWith Set.union tok (Set.singleton item) map
      | otherwise        = map

extractExps :: ParseState -> Type -> [Tree]
extractExps (State pinfo chart items) (DTyp _ start _) = exps
  where
    (_,st) = process Nothing (\_ _ -> id) (sequences pinfo) (functions pinfo) (Set.toList items) () chart

    exps = nubsort $ do
      cat <- fromMaybe [] (Map.lookup start (startCats pinfo))
      (funid,args) <- foldForest (\funid args -> (:) (funid,args)) (\_ _ args -> args)
                                 [] cat (productions pinfo)
      let FFun fn _ lins = functions pinfo ! funid
      lbl <- indices lins
      Just fid <- [lookupPC (PK cat lbl 0) (passive st)]
      (fvs,tree) <- go Set.empty 0 (0,fid)
      guard (Set.null fvs)
      return tree

    go rec fcat' (d,fcat)
      | fcat < totalCats pinfo = return (Set.empty,Meta (fcat'*10+d))   -- FIXME: here we assume that every rule has at most 10 arguments
      | Set.member fcat rec    = mzero
      | otherwise              = foldForest (\funid args trees -> 
                                                  do let FFun fn _ lins = functions pinfo ! funid
                                                     args <- mapM (go (Set.insert fcat rec) fcat) (zip [0..] args)
                                                     check_ho_fun fn args
                                                  `mplus`
                                                  trees)
                                            (\const _ trees ->
                                                  return (freeVar const,const)
                                                  `mplus`
                                                  trees)
                                            [] fcat (forest st)

    check_ho_fun fun args
      | fun == _V = return (head args)
      | fun == _B = return (foldl1 Set.difference (map fst args),Abs [mkVar (snd e) | e <- tail args] (snd (head args)))
      | otherwise = return (Set.unions (map fst args),Fun fun (map snd args))
    
    mkVar (Var  v) = v
    mkVar (Meta _) = wildCId
    
    freeVar (Var v) = Set.singleton v
    freeVar _       = Set.empty

_B = mkCId "_B"
_V = mkCId "_V"

process mbt fn !seqs !funs []                                                 acc chart = (acc,chart)
process mbt fn !seqs !funs (item@(Active j ppos funid seqid args key0):items) acc chart
  | inRange (bounds lin) ppos =
      case unsafeAt lin ppos of
        FSymCat d r -> let !fid = args !! d
                           key  = AK fid r
                                
                           items2 = case lookupPC (mkPK key k) (passive chart) of
                                      Nothing -> items
                                      Just id -> (Active j (ppos+1) funid seqid (updateAt d id args) key0) : items
                           items3 = foldForest (\funid args items -> Active k 0 funid (rhs funid r) args key : items)
                                               (\_ _ items -> items)
                                               items2 fid (forest chart)
                       in case lookupAC key (active chart) of
                            Nothing                        -> process mbt fn seqs funs items3 acc chart{active=insertAC key (Set.singleton item) (active chart)}
                            Just set | Set.member item set -> process mbt fn seqs funs items  acc chart
                                     | otherwise           -> process mbt fn seqs funs items2 acc chart{active=insertAC key (Set.insert item set) (active chart)}
      	FSymTok tok -> let !acc' = fn tok (Active j (ppos+1) funid seqid args key0) acc
                       in process mbt fn seqs funs items acc' chart
        FSymLit d r -> let !fid = args !! d
                       in case [t | set <- IntMap.lookup fid (forest chart), FConst _ t <- Set.toList set] of
                            (tok:_) -> let !acc' = fn (KS tok) (Active j (ppos+1) funid seqid args key0) acc
                                       in process mbt fn seqs funs items acc' chart
                            []      -> case litCatMatch fid mbt of
                                         Just (t,lit) -> let fid'  = nextId chart
                                                             !acc' = fn (KS t) (Active j (ppos+1) funid seqid (updateAt d fid' args) key0) acc
                                                         in process mbt fn seqs funs items acc' chart{forest=IntMap.insert fid' (Set.singleton (FConst lit t)) (forest chart)
                                                                                                     ,nextId=nextId chart+1
                                                                                                     }
                                         Nothing      -> process mbt fn seqs funs items acc chart
  | otherwise =
      case lookupPC (mkPK key0 j) (passive chart) of
        Nothing -> let fid = nextId chart
                       
                       items2 = case lookupAC key0 ((active chart:actives chart) !! (k-j)) of
                                  Nothing  -> items
                                  Just set -> Set.fold (\(Active j' ppos funid seqid args keyc) -> 
                                                            let FSymCat d _ = unsafeAt (unsafeAt seqs seqid) ppos
                                                            in (:) (Active j' (ppos+1) funid seqid (updateAt d fid args) keyc)) items set
	           in process mbt fn seqs funs items2 acc chart{passive=insertPC (mkPK key0 j) fid (passive chart)
                                                               ,forest =IntMap.insert fid (Set.singleton (FApply funid args)) (forest chart)
                                                               ,nextId =nextId chart+1
                                                               }
        Just id -> let items2 = [Active k 0 funid (rhs funid r) args (AK id r) | r <- labelsAC id (active chart)] ++ items
                   in process mbt fn seqs funs items2 acc chart{forest = IntMap.insertWith Set.union id (Set.singleton (FApply funid args)) (forest chart)}
  where
    !lin = unsafeAt seqs seqid
    !k   = offset chart

    mkPK (AK fid lbl) j = PK fid lbl j
    
    rhs funid lbl = unsafeAt lins lbl
      where
        FFun _ _ lins = unsafeAt funs funid


updateAt :: Int -> a -> [a] -> [a]
updateAt nr x xs = [if i == nr then x else y | (i,y) <- zip [0..] xs]

litCatMatch fcat (Just t)
  | fcat == fcatString = Just (t,Lit (LStr t))
  | fcat == fcatInt    = case reads t of {[(n,"")] -> Just (t,Lit (LInt n));
                                         _         -> Nothing }
  | fcat == fcatFloat  = case reads t of {[(d,"")] -> Just (t,Lit (LFlt d));
                                         _         -> Nothing }
  | fcat == fcatVar    = Just (t,Var (mkCId t))
litCatMatch _    _     = Nothing


----------------------------------------------------------------
-- Active Chart
----------------------------------------------------------------

data Active
  = Active {-# UNPACK #-} !Int
           {-# UNPACK #-} !FPointPos
           {-# UNPACK #-} !FunId
           {-# UNPACK #-} !SeqId
                           [FCat]
           {-# UNPACK #-} !ActiveKey
  deriving (Eq,Show,Ord)
data ActiveKey
  = AK {-# UNPACK #-} !FCat
       {-# UNPACK #-} !FIndex
  deriving (Eq,Ord,Show)
type ActiveChart  = IntMap.IntMap (IntMap.IntMap (Set.Set Active))

emptyAC :: ActiveChart
emptyAC = IntMap.empty

lookupAC :: ActiveKey -> ActiveChart -> Maybe (Set.Set Active)
lookupAC (AK fcat l) chart = IntMap.lookup fcat chart >>= IntMap.lookup l

labelsAC :: FCat -> ActiveChart -> [FIndex]
labelsAC fcat chart = 
  case IntMap.lookup fcat chart of
    Nothing  -> []
    Just map -> IntMap.keys map

insertAC :: ActiveKey -> Set.Set Active -> ActiveChart -> ActiveChart
insertAC (AK fcat l) set chart = IntMap.insertWith IntMap.union fcat (IntMap.singleton l set) chart


----------------------------------------------------------------
-- Passive Chart
----------------------------------------------------------------

data PassiveKey
  = PK {-# UNPACK #-} !FCat
       {-# UNPACK #-} !FIndex
       {-# UNPACK #-} !Int
  deriving (Eq,Ord,Show)

type PassiveChart = Map.Map PassiveKey FCat 

emptyPC :: PassiveChart
emptyPC = Map.empty

lookupPC :: PassiveKey -> PassiveChart -> Maybe FCat
lookupPC key chart = Map.lookup key chart

insertPC :: PassiveKey -> FCat -> PassiveChart -> PassiveChart
insertPC key fcat chart = Map.insert key fcat chart


----------------------------------------------------------------
-- Forest
----------------------------------------------------------------

foldForest :: (FunId -> [FCat] -> b -> b) -> (Tree -> String -> b -> b) -> b -> FCat -> IntMap.IntMap (Set.Set Production) -> b
foldForest f g b fcat forest =
  case IntMap.lookup fcat forest of
    Nothing  -> b
    Just set -> Set.fold foldProd b set
  where
    foldProd (FCoerce fcat)      b = foldForest f g b fcat forest
    foldProd (FApply funid args) b = f funid args b
    foldProd (FConst const s)    b = g const s b


----------------------------------------------------------------
-- Parse State
----------------------------------------------------------------

-- | An abstract data type whose values represent
-- the current state in an incremental parser.
data ParseState = State ParserInfo Chart (Set.Set Active)

data Chart
  = Chart
      { active  :: ActiveChart
      , actives :: [ActiveChart]
      , passive :: PassiveChart
      , forest  :: IntMap.IntMap (Set.Set Production)
      , nextId  :: {-# UNPACK #-} !FCat
      , offset  :: {-# UNPACK #-} !Int
      }
      deriving Show
