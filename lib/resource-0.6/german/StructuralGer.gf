--1 The Top-Level German Resource Grammar
--
-- Aarne Ranta 2002 -- 2003
--
-- This is the German concrete syntax of the multilingual resource
-- grammar. Most of the work is done in the file $syntax.Deu.gf$.
-- However, for the purpose of documentation, we make here explicit the
-- linearization types of each category, so that their structures and
-- dependencies can be seen.
-- Another substantial part are the linearization rules of some
-- structural words.
--
-- The users of the resource grammar should not look at this file for the
-- linearization rules, which are in fact hidden in the document version.
-- They should use $resource.Abs.gf$ to access the syntactic rules.
-- This file can be consulted in those, hopefully rare, occasions in which
-- one has to know how the syntactic categories are
-- implemented. The parameter types are defined in $Types.gf$.

concrete StructuralGer of Structural = CombinationsGer ** open Prelude, SyntaxGer in {

lin
  INP    = pronNounPhrase pronIch ;
  ThouNP = pronNounPhrase pronDu ;
  HeNP   = pronNounPhrase pronEr ;
  SheNP  = pronNounPhrase pronSie ; 
  WeNP n = pronNounPhrase (pronWithNum pronWir n) ;
  YeNP n = pronNounPhrase (pronWithNum pronIhr n) ;
  TheyNP = pronNounPhrase pronSiePl ;

  YouNP  = pronNounPhrase pronSSie ;

  ItNP   = pronNounPhrase pronEs ; 
  ThisNP = nameNounPhrase {s = dieserDet.s ! Neut} ; ---
  ThatNP = nameNounPhrase {s = jenerDet.s ! Neut} ; ---

  EveryDet = jederDet ; 
  AllDet   = allesDet ; 
  AllsDet  = alleDet ; 
  WhichDet = welcherDet ;
  WhichsDet = welcheDet ;
  MostDet  = meistDet ;

  HowIAdv   = ss "wie" ;
  WhenIAdv  = ss "wann" ;
  WhereIAdv = ss "war" ;
  WhyIAdv   = ss "warum" ;

  AndConj  = ss "und" ** {n = Pl} ;
  OrConj   = ss "oder" ** {n = Sg} ;
  BothAnd  = sd2 "sowohl" ["als auch"] ** {n = Pl} ;
  EitherOr = sd2 "entweder" "oder" ** {n = Sg} ;
  NeitherNor = sd2 "weder" "noch" ** {n = Sg} ;
  IfSubj   = ss "wenn" ;
  WhenSubj = ss "wenn" ;

  PhrYes = ss ["Ja ."] ;
  PhrNo = ss ["Nein ."] ;

  VeryAdv = ss "sehr" ;
  TooAdv = ss "zu" ;
  OtherwiseAdv = ss "sonst" ;
  ThereforeAdv = ss "deshalb" ;



  CanVV     = 
    mkVerbSimple (verbSehen "k�nnen" "kann" "gekonnt")  ** {isAux = True} ; ---
  CanKnowVV = 
    mkVerbSimple (verbSehen "k�nnen" "kann" "gekonnt")  ** {isAux = True} ; ---
  MustVV    = 
    mkVerbSimple (verbSehen "m�ssen" "muss" "gemusst")  ** {isAux = True} ; ---
  WantVV    = 
    mkVerbSimple (verbSehen "wollen" "will" "gewollt")  ** {isAux = True} ; ---


  EverywhereNP = ss "�berall" ;
  SomewhereNP = ss "irgendwo" ;
  NowhereNP = ss "nirgends" ;

  AlthoughSubj = ss "obwohl" ;

  AlmostAdv = ss "fast" ;
  QuiteAdv = ss "ziemlich" ;

  InPrep = mkPrep "in" Dat ;
  OnPrep = mkPrep "auf" Dat ;
  ToPrep = mkPrep "nach" Dat ;
  ThroughPrep = mkPrep "durch" Acc ;
  AbovePrep = mkPrep "�ber" Dat ;
  UnderPrep = mkPrep "unter" Dat ;
  InFrontPrep = mkPrep "vor" Dat ;
  BehindPrep = mkPrep "hinter" Dat ;
  BetweenPrep = mkPrep "zwischen" Dat ;
  FromPrep = mkPrep "aus" Dat ;
  BeforePrep = mkPrep "vor" Dat ;
  DuringPrep = mkPrep "w�hrend" Gen ;
  AfterPrep = mkPrep "nach" Dat ;
  WithPrep = mkPrep "mit" Dat ;
  WithoutPrep = mkPrep "ohne" Acc ;
  ByMeansPrep = mkPrep "mit" Dat ;
  PartPrep = mkPrep "von" Dat ;
  AgentPrep = mkPrep "durch" Acc ;

} ;
