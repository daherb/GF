--# -path=.:../nabstract:../../prelude

--1 The Top-Level English Resource Grammar: Structural Words
--
-- Aarne Ranta 2002 -- 2003
--
concrete StructuralSwe of Structural = 
                      CombinationsSwe ** open Prelude, SyntaxSwe in {
 lin

  INP    = pronNounPhrase jag_32 ;
  ThouNP = pronNounPhrase du_33 ;
  HeNP   = pronNounPhrase han_34 ;
  SheNP  = pronNounPhrase hon_35 ;
  ItNP   = pronNounPhrase det_40 ; ----
  WeNP n = pronNounPhrase (pronWithNum vi_36 n) ;
  YeNP n = pronNounPhrase (pronWithNum ni_37 n) ;
  TheyNP = pronNounPhrase de_38 ;

  YouNP  = let {ni = pronNounPhrase ni_37 } in {s = ni.s ; g = ni.g ; n = Sg} ;

  EveryDet = varjeDet ; 
  AllsDet  = mkDeterminerPlNum "alla" IndefP ; 
  WhichDet = vilkenDet ;
  MostDet  = flestaDet ;

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

  PhrYes = ss ["Ja ."] ;
  PhrNo = ss ["Nej ."] ;

  VeryAdv = ss "mycket" ;
  TooAdv = ss "f�r" ;
  OtherwiseAdv = ss "annars" ;
  ThereforeAdv = ss "d�rf�r" ;

{-
  EveryDet = everyDet ; 
  AllDet   = mkDeterminer Sg "all" ; --- all the missing
  AllsDet  = mkDeterminerNum Pl "all" ;
  WhichDet = whichDet ;
  WhichsDet = mkDeterminerNum Pl "which" ;
  MostsDet = mostDet ;
  MostDet  = mkDeterminer Sg "most" ;
  SomeDet  = mkDeterminer Sg "some" ;
  SomesDet = mkDeterminerNum Pl "some" ;
  AnyDet   = mkDeterminer Sg "any" ;
  AnysDet  = mkDeterminerNum Pl "any" ;
  NoDet    = mkDeterminer Sg "no" ;
  NosDet   = mkDeterminerNum Pl "no" ;
  ManyDet  = mkDeterminer Sg "many" ;
  MuchDet  = mkDeterminer Sg ["a lot of"] ; ---
  ThisDet  = mkDeterminer Sg "this" ;
  TheseDet = mkDeterminerNum Pl "these" ;
  ThatDet  = mkDeterminer Sg "that" ;
  ThoseDet = mkDeterminerNum Pl "those" ;

  ThisNP = nameNounPhrase (nameReg "this") ;
  ThatNP = nameNounPhrase (nameReg "that") ;
  TheseNP n = nameNounPhrase {s = \\c => "these" ++ n.s ! c} ;
  ThoseNP n = nameNounPhrase {s = \\c => "those" ++ n.s ! c} ;
-}

  EverybodyNP  = nameNounPhrase (mkProperName "alleman" Utr Masc) ;
  SomebodyNP   = nameNounPhrase (mkProperName "n�gon" Utr Masc) ;
  NobodyNP     = nameNounPhrase (mkProperName "ingen" Utr Masc) ;
  EverythingNP = nameNounPhrase (mkProperName "allting" Neutr NoMasc) ; 
  SomethingNP  = nameNounPhrase (mkProperName "n�gonting" Neutr NoMasc) ; 
  NothingNP    = nameNounPhrase (mkProperName "ingenting" Neutr NoMasc) ; 

  CanVV     = mkVerb "kunna" "kan" "kunn"  ** {isAux = True} ; ---
  CanKnowVV = mkVerb "kunna" "kan" "kunn"  ** {isAux = True} ; ---
  MustVV    = mkVerb "f�"    "m�ste" "f�"  ** {isAux = True} ; ---
  WantVV    = mkVerb "vilja" "vill" "vilj" ** {isAux = True} ; ---

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
  PartPrep = ss "av" ;
  AgentPrep = ss "av" ;

}
