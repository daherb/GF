--# -path=.:../abstract:../scandinavian:../../prelude

--1 The Top-Level Swedish Resource Grammar: Structural Words
--
-- Aarne Ranta 2002 -- 2004
--
concrete StructuralSwe of Structural = 
  CategoriesSwe, NumeralsSwe ** 
    open Prelude, MorphoSwe, SyntaxSwe in {

  flags optimize=values ;

 lin

  UseNumeral i = {s = table {Nom => i.s ; Gen => i.s ++ "s"}} ; ---

  above_Prep = ss "ovanf�r" ;
  after_Prep = ss "efter" ;
  by8agent_Prep = ss "av" ;
  all8mass_Det = mkDeterminerSgGender2 "all" "allt" IndefP ;
  all_NDet = mkDeterminerPlNum "alla" IndefP ;
  almost_Adv = ss "n�stan" ;
  although_Subj = ss "fast" ;
  and_Conj = ss "och" ** {n = Pl} ;
  because_Subj = ss "eftersom" ;
  before_Prep = ss "f�re" ;
  behind_Prep = ss "bakom" ;
  between_Prep = ss "mellan" ;
  both_AndConjD = sd2 "b�de" "och" ** {n = Pl} ;
  by8means_Prep = ss "med" ;
  can8know_VV = mkVerb "kunna" "kan" "kunn" "kunde" "kunnat" "kunnen"
  ** {isAux = True} ;
  can_VV = mkVerb "kunna" "kan" "kunn" "kunde" "kunnat" "kunnen"
  ** {isAux = True} ;
  during_Prep = ss "under" ;
  either8or_ConjD = sd2 "antingen" "eller" ** {n = Sg} ;
  everybody_NP = let alla = table {Nom => "alla" ; Gen => "allas"} in 
    {s = \\c => alla ! npCase c ; g = Utr ; n = Pl ; p = P3} ;
  every_Det = varjeDet ;
  everything_NP = nameNounPhrase (mkProperName "allting" NNeutr) ;
  everywhere_Adv = advPost "varstans" ;
  from_Prep = ss "fr�n" ;
  he_NP = pronNounPhrase han_34 ;
  how_IAdv = ss "hur" ;
  how8many_IDet = mkDeterminerPl ["hur m�nga"] IndefP ;
  if_Subj = ss "om" ;
  in8front_Prep = ss "framf�r" ;
  i_NP = pronNounPhrase jag_32 ;
  in_Prep = ss "i" ;
  it_NP = pronNounPhrase det_40 ; ----

  many_Det = mkDeterminerPl "m�nga" IndefP ;
  most_Det = mkDeterminerSgGender2 ["den mesta"] ["det mesta"] (DefP Def) ;
  most8many_Det = flestaDet ;
  much_Det = mkDeterminerSg (detSgInvar "mycket") IndefP ;
  must_VV = mkVerb "f�" "m�ste" "f�" "fick" "m�st" "m�st"   ** {isAux = True} ;
  no_Phr = ss ["Nej ."] ;
  on_Prep = ss "p�" ;
  or_Conj = ss "eller" ** {n = Sg} ;
  otherwise_Adv = ss "annars" ;
  part_Prep = ss "av" ;
  possess_Prep = ss "av" ;
  quite_Adv = ss "ganska" ;
  she_NP = pronNounPhrase hon_35 ;
  so_Adv = ss "s�" ;
  somebody_NP = nameNounPhrase (mkProperName "n�gon" (NUtr Masc)) ;
  some_Det = mkDeterminerSgGender2 "n�gon" "n�got" IndefP ;
  some_NDet = mkDeterminerPlNum "n�gra" IndefP ;
  something_NP = nameNounPhrase (mkProperName "n�gonting" NNeutr) ;
  somewhere_Adv = advPost "n�gonstans" ;
  that_Det = mkDeterminerSgGender2 ["den d�r"] ["det d�r"] (DefP Def) ;
  that_NP = regNameNounPhrase ["det d�r"] NNeutr ;
  therefore_Adv = ss "d�rf�r" ;
  these_NDet = mkDeterminerPlNum ["de h�r"] (DefP Def) ;
  they8fem_NP = pronNounPhrase de_38 ;
  they_NP = pronNounPhrase de_38 ;
  this_Det = mkDeterminerSgGender2 ["den h�r"] ["det h�r"] (DefP Def) ;
  this_NP = regNameNounPhrase ["det h�r"] NNeutr ;
  those_NDet = mkDeterminerPlNum ["de d�r"] (DefP Def) ;
  thou_NP = pronNounPhrase du_33 ;
  through_Prep = ss "genom" ;
  too_Adv = ss "f�r" ;
  to_Prep = ss "till" ;
  under_Prep = ss "under" ;
  very_Adv = ss "mycket" ;
  want_VV = mkVerb "vilja" "vill" "vilj" "ville" "velat" "velad"   ** {isAux = True} ;
  we_NP = pronNounPhrase (vi_36) ;
  what8many_IP = intPronWhat plural ;
  what8one_IP = intPronWhat singular ;
  when_IAdv = ss "n�r" ;
  when_Subj = ss "n�r" ;
  where_IAdv = ss "var" ;
  which8one_IDet = vilkenDet ;
  which8many_IDet = mkDeterminerPl "vilka" IndefP ;
  who8many_IP = intPronWho plural ;
  who8one_IP = intPronWho singular ;
  why_IAdv = ss "varf�r" ;
  without_Prep = ss "utan" ;
  with_Prep = ss "med" ;
  ye_NP = pronNounPhrase (ni_37) ;
  yes_Phr = ss ["Ja ."] ;
  you_NP = let {ni = pronNounPhrase ni_37 } in {
             s = ni.s ; g = ni.g ; n = Sg ; p = P2} ; ---- gives wrong refl



{-
  INP    = pronNounPhrase jag_32 ;
  ThouNP = pronNounPhrase du_33 ;
  HeNP   = pronNounPhrase han_34 ;
  SheNP  = pronNounPhrase hon_35 ;
  WeNP n = pronNounPhrase (vi_36 n) ;
  YeNP n = pronNounPhrase (ni_37 n) ;
  TheyNP = pronNounPhrase de_38 ;
  TheyFemNP = pronNounPhrase de_38 ;

  YouNP  = let {ni = pronNounPhrase ni_37 } in {
             s = ni.s ; g = ni.g ; n = Sg ; p = P2} ; ---- gives wrong refl

  ItNP   = pronNounPhrase det_40 ; ----
  ThisNP = regNameNounPhrase ["det h�r"] NNeutr ; 
  ThatNP = regNameNounPhrase ["det d�r"] NNeutr ; 

  EveryDet = varjeDet ; 
  AllMassDet   = mkDeterminerSgGender2 "all" "allt" IndefP ; 
  AllNumDet  = mkDeterminerPlNum "alla" IndefP ; 
  AnyDet   = mkDeterminerSgGender2 "n�gon" "n�got" IndefP ; 
  AnyNumDet  = mkDeterminerPlNum "n�gra" IndefP ; 
  SomeDet  = mkDeterminerSgGender2 "n�gon" "n�got" IndefP ; 
  SomeNumDet = mkDeterminerPlNum "n�gra" IndefP ; 
  ManyDet  = mkDeterminerPl "m�nga" IndefP ; 
  HowManyDet  = mkDeterminerPl ["hur m�nga"] IndefP ; 
  NoDet    = mkDeterminerSgGender2 "ingen" "inget" IndefP ; 
  NoNumDet   = mkDeterminerPlNum "inga" IndefP ; 
  WhichNumDet = mkDeterminerPlNum "vilka" IndefP ; 

  UseNumeral i = {s = table {Nom => i.s ; Gen => i.s ++ "s"}} ; ---

  WhichDet = vilkenDet ;
  MostDet  = mkDeterminerSgGender2 ["den mesta"] ["det mesta"] (DefP Def) ;
  MostsDet = flestaDet ;
  MuchDet  = mkDeterminerSg (detSgInvar "mycket") IndefP ;

  ThisDet  = mkDeterminerSgGender2 ["den h�r"] ["det h�r"] (DefP Def) ;
  ThatDet  = mkDeterminerSgGender2 ["den d�r"] ["det d�r"] (DefP Def) ;
  TheseNumDet = mkDeterminerPlNum ["de h�r"] (DefP Def) ; 
  ThoseNumDet = mkDeterminerPlNum ["de d�r"] (DefP Def) ; 

  HowIAdv = ss "hur" ;
  WhenIAdv = ss "n�r" ;
  WhereIAdv = ss "var" ;
  WhyIAdv = ss "varf�r" ;

  AndConj  = ss "och" ** {n = Pl}  ;
  OrConj   = ss "eller" ** {n = Sg} ;
  BothAnd  = sd2 "b�de" "och" ** {n = Pl}  ;
  EitherOr = sd2 "antingen" "eller" ** {n = Sg} ;
  NeitherNor = sd2 "varken" "eller" ** {n = Sg} ;
  IfSubj   = ss "om" ;
  WhenSubj = ss "n�r" ;

  YesPhr = ss ["Ja ."] ;
  NoPhr = ss ["Nej ."] ;

  VeryAdv = ss "mycket" ;
  TooAdv = ss "f�r" ;
  SoAdv = ss "s�" ;
  OtherwiseAdv = ss "annars" ;
  ThereforeAdv = ss "d�rf�r" ;

  EverybodyNP  = let alla = table {Nom => "alla" ; Gen => "allas"} in {s = \\c => alla ! npCase c ; g = Utr ; n = Pl ; p = P3} ;
  SomebodyNP   = nameNounPhrase (mkProperName "n�gon" (NUtr Masc)) ;
  NobodyNP     = nameNounPhrase (mkProperName "ingen" (NUtr Masc)) ;
  EverythingNP = nameNounPhrase (mkProperName "allting" NNeutr) ; 
  SomethingNP  = nameNounPhrase (mkProperName "n�gonting" NNeutr) ; 
  NothingNP    = nameNounPhrase (mkProperName "ingenting" NNeutr) ; 

  CanVV     = mkVerb "kunna" "kan" "kunn"  "kunde" "kunnat" "kunnen" ** {s3 = []} ;
  CanKnowVV = mkVerb "kunna" "kan" "kunn"  "kunde" "kunnat" "kunnen" ** {s3 = []} ;
  MustVV    = mkVerb "f�"    "m�ste" "f�"  "fick"  "m�st"   "m�st" ** {s3 = []} ;
  WantVV    = mkVerb "vilja" "vill" "vilj" "ville" "velat" "velad" ** {s3 = []} ;

  EverywhereNP = advPost "varstans" ;
  SomewhereNP = advPost "n�gonstans" ;
  NowhereNP = advPost "ingenstans" ;

  AlthoughSubj = ss "fast" ;

  AlmostAdv = ss "n�stan" ;
  QuiteAdv = ss "ganska" ;

  InPrep = ss "i" ;
  OnPrep = ss "p�" ;
  ToPrep = ss "till" ;
  ThroughPrep = ss "genom" ;
  AbovePrep = ss "ovanf�r" ;
  UnderPrep = ss "under" ;
  InFrontPrep = ss "framf�r" ;
  BehindPrep = ss "bakom" ;
  BetweenPrep = ss "mellan" ;
  FromPrep = ss "fr�n" ;
  BeforePrep = ss "f�re" ;
  DuringPrep = ss "under" ;
  AfterPrep = ss "efter" ;
  WithPrep = ss "med" ;
  WithoutPrep = ss "utan" ;
  ByMeansPrep = ss "med" ;
  PossessPrep = ss "av" ;
  PartPrep = ss "av" ;
  AgentPrep = ss "av" ;
-}


}
