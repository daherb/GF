incomplete concrete BaseI of Base = 
  open Syntax, (G = Grammar), Symbolic, LexBase in {

flags lexer=literals ; unlexer=text ;

lincat
  Question = G.Phr ;
  Answer = G.Phr ;
  S  = Cl ;
  NP = G.NP ;
  PN = G.NP ;
  CN = G.CN ;
  AP = G.AP ;
  A2 = G.A2 ;
  Conj = G.Conj ;
  ListPN = G.ListNP ;

lin 
  PredAP  = mkCl ;

  ComplA2 = mkAP ;

  ModCN   = mkCN ;

---  ConjS  = mkS ;
  ConjAP = mkAP ;
  ConjNP = mkNP ;

  UsePN p = p ;
  Every = mkNP every_Det ;
  Some  = mkNP someSg_Det ;
---  None  = mkNP noSg_Det ; ---

  And = and_Conj ;
  Or  = or_Conj ;

  UseInt i = symb i ;

  Number = mkCN number_N ;

  Even = mkAP even_A ;
  Odd  = mkAP odd_A ;
  Prime = mkAP prime_A ;
  Equal = equal_A2 ;
  Greater = greater_A2 ;
  Smaller = smaller_A2 ;
  Divisible = divisible_A2 ;
 
  Sum     = prefix sum_N2 ;
  Product = prefix product_N2 ;
---  GCD     = prefixSS ["the greatest common divisor of"] ;

  WhatIs np = mkPhr (mkQS (mkQCl whatSg_IP (mkVP np))) ;
  WhichAre cn ap = mkPhr (mkQS (mkQCl (mkIP whichPl_IDet cn) (mkVP ap))) ;
  QuestS s = mkPhr (mkQS (mkQCl s)) ;

  Yes = yes_Phr ;
  No = no_Phr ;

  Value np = mkPhr (mkUtt np) ;
  Many list = mkNP and_Conj list ;

  BasePN = G.BaseNP ;
  ConsPN = G.ConsNP ;

oper
  prefix : G.N2 -> G.ListNP -> G.NP = \n2,nps -> 
    mkNP defSgDet (mkCN n2 (mkNP and_Conj nps)) ;
  
}
