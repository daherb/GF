module PGF.Linearize where

import PGF.CId
import PGF.Data
import PGF.Macros
import qualified Data.Map as Map
import Data.List

import Debug.Trace

-- linearization and computation of concrete PGF Terms

linearize :: PGF -> CId -> Tree -> String
linearize pgf lang = realize . linTree pgf lang

realize :: Term -> String
realize trm = case trm of
  R ts     -> realize (ts !! 0)
  S ss     -> unwords $ map realize ss
  K t -> case t of
    KS s -> s
    KP s _ -> unwords s ---- prefix choice TODO
  W s t    -> s ++ realize t
  FV ts    -> realize (ts !! 0)  ---- other variants TODO
  TM s     -> s
  _ -> "ERROR " ++ show trm ---- debug

linTree :: PGF -> CId -> Tree -> Term
linTree pgf lang = lin
  where
    lin (Abs xs  e )   = case lin e of
                             R ts -> R $ ts     ++ (Data.List.map (kks . prCId) xs)
                             TM s -> R $ (TM s)  : (Data.List.map (kks . prCId) xs)
    lin (Fun fun es)   = comp (map lin es) $ look fun
    lin (Lit (LStr s)) = R [kks (show s)] -- quoted
    lin (Lit (LInt i)) = R [kks (show i)] 
    lin (Lit (LFlt d)) = R [kks (show d)]
    lin (Var x)        = TM (prCId x)
    lin (Meta i)       = TM (show i)
 
    comp = compute pgf lang
    look = lookLin pgf lang


compute :: PGF -> CId -> [Term] -> Term -> Term
compute pgf lang args = comp where
  comp trm = case trm of
    P r p  -> proj (comp r) (comp p) 
    W s t  -> W s (comp t)
    R ts   -> R $ map comp ts
    V i    -> idx args i          -- already computed
    F c    -> comp $ look c       -- not computed (if contains argvar)
    FV ts  -> FV $ map comp ts
    S ts   -> S $ filter (/= S []) $ map comp ts
    _ -> trm

  look = lookOper pgf lang

  idx xs i = if i > length xs - 1 
    then trace 
         ("too large " ++ show i ++ " for\n" ++ unlines (map show xs) ++ "\n") tm0 
    else xs !! i 

  proj r p = case (r,p) of
    (_,     FV ts) -> FV $ map (proj r) ts
    (FV ts, _    ) -> FV $ map (\t -> proj t p) ts
    (W s t, _)     -> kks (s ++ getString (proj t p))
    _              -> comp $ getField r (getIndex p)

  getString t = case t of
    K (KS s) -> s
    _ -> error ("ERROR in grammar compiler: string from "++ show t) "ERR"

  getIndex t =  case t of
    C i    -> i
    TM _   -> 0  -- default value for parameter
    _ -> trace ("ERROR in grammar compiler: index from " ++ show t) 666

  getField t i = case t of
    R rs   -> idx rs i
    TM s   -> TM s
    _ -> error ("ERROR in grammar compiler: field from " ++ show t) t

