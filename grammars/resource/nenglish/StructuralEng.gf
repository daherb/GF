--# -path=.:../nabstract:../../prelude

--1 The Top-Level English Resource Grammar: Structural Words
--
-- Aarne Ranta 2002 -- 2003
--
concrete StructuralEng of Structural = 
                      CombinationsEng ** open Prelude, SyntaxEng in {
 lin
  INP    = pronI ;
  ThouNP = pronYouSg ;
  HeNP   = pronHe ;
  SheNP  = pronShe ;
  ItNP   = pronIt ;
  WeNP   = pronWithNum pronWe ;
  YeNP   = pronWithNum pronYouPl ;
  YouNP  = pronYouSg ;
  TheyNP = pronThey ;

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

  EverybodyNP = nameNounPhrase (nameReg "everybody") ;
  SomebodyNP = nameNounPhrase (nameReg "somebody") ;
  NobodyNP = nameNounPhrase (nameReg "nobody") ;
  EverythingNP = nameNounPhrase (nameReg "everything") ;
  SomethingNP = nameNounPhrase (nameReg "something") ;
  NothingNP = nameNounPhrase (nameReg "nothing") ;

  CanVV = vvCan ;
  CanKnowVV = vvCan ;
  MustVV = vvMust ;
  WantVV = verbNoPart (regVerbP3 "want") ** {isAux = False} ;

  HowIAdv = ss "how" ;
  WhenIAdv = ss "when" ;
  WhereIAdv = ss "where" ;
  WhyIAdv = ss "why" ;
  EverywhereNP = advPost "everywhere" ;
  SomewhereNP = advPost "somewhere" ;
  NowhereNP = advPost "nowhere" ;

  AndConj = ss "and" ** {n = Pl} ;
  OrConj = ss "or" ** {n = Sg} ;
  BothAnd = sd2 "both" "and" ** {n = Pl} ;
  EitherOr = sd2 "either" "or" ** {n = Sg} ;
  NeitherNor = sd2 "neither" "nor" ** {n = Sg} ;
  IfSubj = ss "if" ;
  WhenSubj = ss "when" ;
  AlthoughSubj = ss "although" ;

  PhrYes = ss "Yes." ;
  PhrNo = ss "No." ;

  VeryAdv = ss "very" ;
  TooAdv = ss "too" ;
  AlmostAdv = ss "almost" ;
  QuiteAdv = ss "quite" ;
  OtherwiseAdv = ss "otherwise" ;
  ThereforeAdv = ss "therefore" ;

  InPrep = ss "in" ;
  OnPrep = ss "on" ;
  ToPrep = ss "to" ;
  ThroughPrep = ss "through" ;
  AbovePrep = ss "above" ;
  UnderPrep = ss "under" ;
  InFrontPrep = ss ["in front of"] ;
  BehindPrep = ss "behind" ;
  BetweenPrep = ss "between" ;
  FromPrep = ss "from" ;
  BeforePrep = ss "before" ;
  DuringPrep = ss "during" ;
  AfterPrep = ss "after" ;
  WithPrep = ss "with" ;
  WithoutPrep = ss "without" ;
  ByMeansPrep = ss "by" ;
  PartPrep = ss "of" ;
  AgentPrep = ss "by" ;

}
