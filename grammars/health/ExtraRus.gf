-- use this path to read the grammar from the same directory
--# -path=.:../abstract:../../prelude:../russian

--1 Functions that are not in the API, but common in Russian 
--
-- Aarne Ranta, Janna Khegai 2003
resource ExtraRus = open ResourceRus, Prelude, SyntaxRus in {

flags  coding=utf8 ;

oper
  predNeedShortAdjective: Bool -> NP -> CN -> S = \b, Jag, Dig -> { s =
    let {
      mne  = Jag.s ! (mkPronForm Dat No NonPoss) ; 
      nuzhen  = need.s ! AF Nom Inanimate (gNum Dig.g Sg)  ;
      doctor = Dig.s ! Sg ! Nom ;
      ne = negation b
    } in
       mne ++ ne ++ nuzhen ++ doctor ;
      lock_S = <>
    } ;

  U_predTransVerb : Bool -> TV -> NP -> NP -> S = 
    \b,Ser,Jag,Dig -> { s =
    let {
      menya  =  Jag.s ! (mkPronForm Gen Yes NonPoss) ; 
      bolit  = Ser.s ! VFin (gNum (pgen2gen Dig.g) Dig.n) Dig.p ;
      golova = Dig.s ! (mkPronForm Nom No NonPoss) ;
      ne = negation b
    } in
       "у" ++ menya ++ ne ++ bolit  ++ golova  ;
      lock_S = <>
    } ;

  tvHave : TV = mkDirectVerb (extVerb have Act Present) ** { lock_TV = <>};    
};
