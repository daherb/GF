--1 The Top-Level English Resource Grammar
--
-- Aarne Ranta 2002 -- 2003
--
-- This is the English concrete syntax of the multilingual resource
-- grammar. Most of the work is done in the file $syntax.Eng.gf$.
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
-- implemented. The parameter types are defined in $types.Eng.gf$.

concrete ResEng of ResAbs = open Prelude, Syntax in {

flags 
  startcat=Phr ; 
  parser=chart ;

lincat 
  N      = CommNoun ;         
      -- = {s : Number => Case => Str}
  CN     = CommNounPhrase ;   
      -- = CommNoun ** {g : Gender}
  NP     = {s : NPForm => Str ; n : Number ; p : Person} ;
  PN     = {s : Case => Str} ;
  Det    = {s : Str ; n : Number} ;
  Fun    = CommNounPhrase ** {s2 : Preposition} ;

  Adj1   = Adjective ; 
      -- = {s : Str}
  Adj2   = Adjective ** {s2 : Preposition} ;
  AdjDeg = {s : Degree => Str} ;
  AP     = Adjective ** {p : Bool} ;

  V      = Verb ; 
      -- = {s : VForm => Str ; s1 : Particle}
  VP     = {s : VForm => Str ; s2 : Number => Str ; isAux : Bool} ;
  TV     = Verb ** {s3 : Preposition} ;
  VS     = Verb ;

  AdV    = {s : Str ; isPost : Bool} ;

  S      = {s : Str} ; 
  Slash  = {s : Bool => Str ; s2 : Preposition} ;
  RP     = {s : Gender => Number => NPForm => Str} ;
  RC     = {s : Gender => Number => Str} ;

  IP     = {s : NPForm => Str ; n : Number} ;
  Qu     = {s : QuestForm => Str} ;
  Imp    = {s : Number => Str} ;
  Phr    = {s : Str} ;

  Conj   = {s : Str ; n : Number} ;
  ConjD  = {s1 : Str ; s2 : Str ; n : Number} ;

  ListS  = {s1 : Str ; s2 : Str} ;
  ListAP = {s1 : Str ; s2 : Str ; p : Bool} ;
  ListNP = {s1,s2 : NPForm => Str ; n : Number ; p : Person} ;

--.

lin 
  UseN = noun2CommNounPhrase ;
  ModAdj = modCommNounPhrase ;
  ModGenOne = npGenDet singular ;
  ModGenMany = npGenDet plural ;
  UsePN = nameNounPhrase ;
  UseFun = funAsCommNounPhrase ;
  AppFun = appFunComm ;
  AdjP1 = adj2adjPhrase ;
  ComplAdj = complAdj ;
  PositAdjP = positAdjPhrase ;
  ComparAdjP = comparAdjPhrase ;
  SuperlNP = superlNounPhrase ;

  DetNP = detNounPhrase ;
  IndefOneNP = indefNounPhrase singular ;
  IndefManyNP = indefNounPhrase plural ;
  DefOneNP = defNounPhrase singular ;
  DefManyNP = defNounPhrase plural ;

  PredVP = predVerbPhrase ;
  PosV = predVerb True ;
  NegV = predVerb False ;
  PosA = predAdjective True ;
  NegA = predAdjective False ;
  PosCN = predCommNoun True ;
  NegCN = predCommNoun False ;
  PosTV = complTransVerb True ;
  NegTV = complTransVerb False ;
  PosNP = predNounPhrase True ;
  NegNP = predNounPhrase False ;
  PosVS = complSentVerb True ;
  NegVS = complSentVerb False ;


  AdvVP = adVerbPhrase ;
  LocNP = locativeNounPhrase ;
  AdvCN = advCommNounPhrase ;

  PosSlashTV = slashTransVerb True ;
  NegSlashTV = slashTransVerb False ;

  IdRP = identRelPron ;
  FunRP = funRelPron ;
  RelVP = relVerbPhrase ;
  RelSlash = relSlash ;
  ModRC = modRelClause ;
  RelSuch = relSuch ;

  WhoOne = intPronWho singular ;
  WhoMany = intPronWho plural ;
  WhatOne = intPronWhat singular ;
  WhatMany = intPronWhat plural ;
  FunIP = funIntPron ;
  NounIPOne = nounIntPron singular ;
  NounIPMany = nounIntPron plural ;

  QuestVP = questVerbPhrase ;
  IntVP = intVerbPhrase ;
  IntSlash = intSlash ;
  QuestAdv = questAdverbial ;

  ImperVP = imperVerbPhrase ;

  IndicPhrase = indicUtt ;
  QuestPhrase = interrogUtt ;
  ImperOne = imperUtterance singular ;
  ImperMany = imperUtterance plural ;

lin
  TwoS = twoSentence ;
  ConsS = consSentence ;
  ConjS = conjunctSentence ;
  ConjDS = conjunctDistrSentence ;

  TwoAP = twoAdjPhrase ;
  ConsAP = consAdjPhrase ;
  ConjAP = conjunctAdjPhrase ;
  ConjDAP = conjunctDistrAdjPhrase ;

  TwoNP = twoNounPhrase ;
  ConsNP = consNounPhrase ;
  ConjNP = conjunctNounPhrase ;
  ConjDNP = conjunctDistrNounPhrase ;

  SubjS = subjunctSentence ;
  SubjImper = subjunctImperative ;
  SubjQu = subjunctQuestion ;

  PhrNP = useNounPhrase ;
  PhrOneCN = useCommonNounPhrase singular ;
  PhrManyCN = useCommonNounPhrase plural ;
  PhrIP ip = ip ;
  PhrIAdv ia = ia ;


lin
  INP    = pronI ;
  ThouNP = pronYouSg ;
  HeNP   = pronHe ;
  SheNP  = pronShe ;
  WeNP   = pronWe ;
  YeNP   = pronYouPl ;
  YouNP  = pronYouSg ;
  TheyNP = pronThey ;

  EveryDet = everyDet ; 
  AllDet   = allDet ; 
  WhichDet = whichDet ;
  MostDet  = mostDet ;

  HowIAdv = ss "how" ;
  WhenIAdv = ss "when" ;
  WhereIAdv = ss "where" ;
  WhyIAdv = ss "why" ;

  AndConj = ss "and" ** {n = Pl} ;
  OrConj = ss "or" ** {n = Sg} ;
  BothAnd = sd2 "both" "and" ** {n = Pl} ;
  EitherOr = sd2 "either" "or" ** {n = Sg} ;
  NeitherNor = sd2 "neither" "nor" ** {n = Sg} ;
  IfSubj = ss "if" ;
  WhenSubj = ss "when" ;

  PhrYes = ss "Yes." ;
  PhrNo = ss "No." ;
} ;
