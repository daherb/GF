module AnswerBase where

import GSyntax

-- interpretation of Base

type Prop = Bool
type Exp = Int
domain = [0 .. 100]

iS :: GS -> Prop
iS s = case s of
  GPredAP np ap -> iNP np (iAP ap)
  GConjS c s t  -> iConj c (iS s) (iS t)

iNP :: GNP -> (Exp -> Prop) -> Prop
iNP np p = case np of
  GEvery cn -> all (\x -> not (iCN cn x) || p x) domain
  GSome  cn -> any (\x ->      iCN cn x  && p x) domain
  GConjNP c np1 np2 -> iConj c (iNP np1 p) (iNP np2 p)
  GUseInt (GInt i) -> p (fromInteger i)

iAP :: GAP -> Exp -> Prop
iAP ap e = case ap of
  GComplA2 a2 np    -> iNP np (iA2 a2 e)
  GConjAP c ap1 ap2 -> iConj c (iAP ap1 e) (iAP ap2 e)
  GEven -> even e
  GOdd -> not (even e)

iCN :: GCN -> Exp -> Prop
iCN cn e = case cn of
  GModCN ap cn0 -> (iCN cn0 e) && (iAP ap e)
  GNumber -> True

iConj :: GConj -> Prop -> Prop -> Prop
iConj c = case c of
  GAnd -> (&&)
  GOr  -> (||)

iA2 :: GA2 -> Exp -> Exp -> Prop
iA2 a2 e1 e2 = case a2 of
  GGreater -> e1 > e1
  GSmaller -> e1 < e2 
  GEqual   -> e1 == e2
