--# -path=.:../scandinavian:../abstract:../../prelude

--1 The Top-Level Swedish Resource Grammar: Structural Words
--
-- Aarne Ranta 2002 -- 2004
--
concrete StructuralDan of Structural = 
  CategoriesDan, NumeralsDan ** open Prelude, MorphoDan, SyntaxDan in {
 lin

  INP    = pronNounPhrase jag_32 ;
  ThouNP = pronNounPhrase du_33 ;
  HeNP   = pronNounPhrase han_34 ;
  SheNP  = pronNounPhrase hon_35 ;
  WeNumNP n = pronNounPhrase (pronWithNum vi_36 n) ;
  YeNumNP n = pronNounPhrase (pronWithNum ni_37 n) ;
  TheyNP = pronNounPhrase de_38 ;
  TheyFemNP = pronNounPhrase de_38 ;

  YouNP  = pronNounPhrase De_38 ;

  ItNP   = pronNounPhrase det_40 ; ----
  ThisNP = regNameNounPhrase ["det her"] NNeutr ; 
  ThatNP = regNameNounPhrase ["det der"] NNeutr ; 
  TheseNumNP n = 
    {s = \\c => ["de her"] ++ n.s ! npCase c ; g = Neutr ; n = Pl ; p
  = P3} ;
  ThoseNumNP n = 
    {s = \\c => ["de der"] ++ n.s ! npCase c ; g = Neutr ; n = Pl ; p
  = P3} ;

  EveryDet = varjeDet ; 
  AllMassDet   = mkDeterminerSgGender2 "all" "alt" IndefP ; 
  AllNumDet  = mkDeterminerPlNum "alle" IndefP ; 
  AnyDet   = mkDeterminerSgGender2 "nogen" "noget" IndefP ; 
  AnyNumDet  = mkDeterminerPlNum "nogle" IndefP ; 
  SomeDet  = mkDeterminerSgGender2 "nogen" "noget" IndefP ; 
  SomeNumDet = mkDeterminerPlNum "nogle" IndefP ; 
  ManyDet  = mkDeterminerPl "mange" IndefP ; 
  HowManyDet  = mkDeterminerPl ["hvor mange"] IndefP ; 
  NoDet    = mkDeterminerSgGender2 "ingen" "ingen" IndefP ; 
  NoNumDet   = mkDeterminerPlNum "ingen" IndefP ; 
  WhichNumDet = mkDeterminerPlNum "hvilke" IndefP ; 

  UseNumeral i = {s = table {Nom => i.s ; Gen => i.s ++ "s"}} ; ---

  WhichDet = vilkenDet ;
  MostDet  = mkDeterminerSgGender2 ["den meste"] ["det meste"] (DefP Def) ;
  MostsDet = flestaDet ;
  MuchDet  = mkDeterminerSg (detSgInvar "meget") IndefP ;

  ThisDet  = mkDeterminerSgGender2 ["den her"] ["det her"] (DefP Indef) ;
  ThatDet  = mkDeterminerSgGender2 ["den der"] ["det der"] (DefP Indef) ;
  TheseNumDet = mkDeterminerPlNum ["de her"] (DefP Indef) ; 
  ThoseNumDet = mkDeterminerPlNum ["de der"] (DefP Indef) ; 

  HowIAdv = ss "hvor" ;
  WhenIAdv = ss "hvorn�r" ;
  WhereIAdv = ss "hver" ;
  WhyIAdv = ss "hvorfor" ;

  AndConj  = ss "og" ** {n = Pl}  ;
  OrConj   = ss "eller" ** {n = Sg} ;
  BothAnd  = sd2 "b�de" "og" ** {n = Pl}  ;
  EitherOr = sd2 "enten" "eller" ** {n = Sg} ;
  NeitherNor = sd2 "hverken" "eller" ** {n = Sg} ;
  IfSubj   = ss "hvis" ;
  WhenSubj = ss "n�r" ;

  PhrYes = ss ["Ja ."] ;
  PhrNo = ss ["Nej ."] ;

  VeryAdv = ss "meget" ;
  TooAdv = ss "for" ; ---- ?
  OtherwiseAdv = ss "anderledes" ; ---- ?
  ThereforeAdv = ss "derfor" ;

  EverybodyNP  = let alla = table {Nom => "alle" ; Gen => "alles"} in
                 {s = \\c => alla ! npCase c ; g = Utr ; n = Pl ; p = P3} ;
  SomebodyNP   = nameNounPhrase (mkProperName "nogen" NUtr) ;
  NobodyNP     = nameNounPhrase (mkProperName "ingen" NUtr) ;
  EverythingNP = nameNounPhrase (mkProperName "alt"   NNeutr) ; 
  SomethingNP  = nameNounPhrase (mkProperName "noget" NNeutr) ; 
  NothingNP    = nameNounPhrase (mkProperName "intet" NNeutr) ; 

  CanVV     = mkVerb "kunne" "kan" nonExist  "kunne" "kunnet" nonExist ** {s1 = [] ; s3 = []} ;
  CanKnowVV = mkVerb "kunne" "kan" nonExist  "kunne" "kunnet" nonExist ** {s1 = [] ; s3 = []} ;
  MustVV    = mkVerb "m�tte" "m�" "m�s"  "m�tte"  "m�ttet" "m�" ** {s1 = [] ; s3 = []} ; ---- ?
  WantVV    = mkVerb "ville" "vil" nonExist "ville" "villet" nonExist ** {s1 = [] ; s3 = []} ; ---

  EverywhereNP = advPost "overalt" ;
  SomewhereNP = advPost ["et eller andet sted"] ; ---- ?
  NowhereNP = advPost "intetsteds" ;

  AlthoughSubj = ss ["selv om"] ;

  AlmostAdv = ss "n�sten" ;
  QuiteAdv = ss "temmelig" ;

  InPrep = ss "i" ;
  OnPrep = ss "p�" ;
  ToPrep = ss "til" ;
  ThroughPrep = ss "igennem" ;
  AbovePrep = ss "ovenfor" ;
  UnderPrep = ss "under" ;
  InFrontPrep = ss "fremfor" ; ---- ?
  BehindPrep = ss "bag" ;
  BetweenPrep = ss "mellem" ;
  FromPrep = ss "fra" ;
  BeforePrep = ss "f�r" ;
  DuringPrep = ss "under" ;
  AfterPrep = ss "efter" ;
  WithPrep = ss "med" ;
  WithoutPrep = ss "uden" ;
  ByMeansPrep = ss "med" ;
  PossessPrep = ss "af" ;
  PartPrep = ss "af" ;
  AgentPrep = ss "af" ;

}
