--# -path=.:../abstract:../../prelude

--1 The Top-Level English Resource Grammar: Combination Rules
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
-- implemented. The parameter types are defined in $TypesEng.gf$.

concrete RulesEng of Rules = CategoriesEng ** open Prelude, SyntaxEng in {

flags 
  startcat=Phr ; 
  lexer=text ;
  unlexer=text ;

lin 
  UseN = noun2CommNounPhrase ;
  UsePN = nameNounPhrase ;

  SymbPN i = {s = table {Nom => i.s ; Gen => i.s ++ "'s"} ; g = Neutr} ; ---
  SymbCN cn s =
    {s = \\n,c => cn.s ! n ! c ++ s.s ; 
     g = cn.g} ;
  IntCN cn s =
    {s = \\n,c => cn.s ! n ! c ++ s.s ; 
     g = cn.g} ;

  IndefOneNP = indefNounPhrase singular ;
  IndefNumNP = indefNounPhraseNum plural ;
  DefOneNP = defNounPhrase singular ;
  DefNumNP = defNounPhraseNum plural ;

  DetNP = detNounPhrase ;
  MassNP = detNounPhrase (mkDeterminer Sg []) ;

  AppN2 = appFunComm ;
  AppN3 = appFun2 ;
  UseN2 = funAsCommNounPhrase ;

  ModAP = modCommNounPhrase ;
  CNthatS = nounThatSentence ;

  ModGenOne = npGenDet singular noNum ;
  ModGenNum = npGenDet plural ;

  UseInt i = {s = table {Nom => i.s ; Gen => i.s ++ "s"}} ; ---
  NoNum = noNum ;

  UseA = adj2adjPhrase ;
  ComplA2 = complAdj ;

  PositADeg = positAdjPhrase ;
  ComparADeg = comparAdjPhrase ;
  SuperlNP = superlNounPhrase ;

-- verbs and verb prases

  UseV  = predVerb ;
  UsePassV = passVerb ;
  ComplV2 = complTransVerb ;
  ComplReflV2 = reflTransVerb ;
  ComplVS = complSentVerb ;
  ComplVV = complVerbVerb ;
  ComplVQ = complQuestVerb ;
  ComplVA = complAdjVerb ;
  ComplV2A = complDitransAdjVerb ;
  ComplSubjV2V = complDitransVerbVerb False ;
  ComplObjV2V = complDitransVerbVerb True ;
  ComplV2S = complDitransSentVerb ;
  ComplV2Q = complDitransQuestVerb ;

  PredAP = predAdjective ;
  PredSuperl a = predAdjective (superlAdjPhrase a) ;
  PredCN = predCommNoun ;
  PredNP = predNounPhrase ;
  PredPP = predAdverb ;
  PredAV = complVerbAdj ;
  PredObjA2V = complVerbAdj2 True ;

  PredAS = predAdjSent ;
  PredV0 rain = predVerbGroupClause (pronNounPhrase pronIt) (predVerb rain) ;

-- Partial saturation.

  UseV2 = transAsVerb ;
  ComplV3 = complDitransVerb ;

  ComplA2S = predAdjSent2 ;

  TransVV2 = transVerbVerb ;
  AdjPart = adjPastPart ;

  UseV2V x = x ** {isAux = False} ;
  UseV2S x = x ;
  UseV2Q x = x ;
  UseA2S x = x ;
  UseA2V x = x ;

-- Formation of infinitival phrases.

  PosVP tp = predVerbGroup True tp.a ;
  NegVP tp = predVerbGroup False tp.a ;

  ProgVG = progressiveVerbPhrase ;

  UseCl  tp cl = {s = tp.s ++ cl.s ! tp.b ! VFinite tp.t tp.a} ;
  UseQCl tp cl = {s = \\q => tp.s ++ cl.s ! tp.b ! VFinite tp.t tp.a ! q} ;
  UseRCl tp cl = {s = \\a => tp.s ++ cl.s ! tp.b ! VFinite tp.t tp.a ! a} ;

  PosTP t a = {s = t.s ++ a.s ; b = True  ; t = t.t ; a = a.a} ;
  NegTP t a = {s = t.s ++ a.s ; b = False ; t = t.t ; a = a.a} ;

  TPresent     = {s = [] ; t = Present} ;
  TPast        = {s = [] ; t = Past} ;
  TFuture      = {s = [] ; t = Future} ;
  TConditional = {s = [] ; t = Conditional} ;

  ASimul = {s = [] ; a = Simul} ;
  AAnter = {s = [] ; a = Anter} ;

-- Adverbs.

  AdjAdv a = advPost (a.s ! AAdv) ;
  AdvPP p = advPost p.s ;
  PrepNP p = prepPhrase p.s ; ---

  AdvVP = adVerbPhrase ;
  AdvCN = advCommNounPhrase ;
  AdvAP = advAdjPhrase ;

--3 Sentences and relative clauses
--

  PredVP = predVerbGroupClause ;

  SlashV2 = slashTransVerbCl ;

  IdRP = identRelPron ;
  FunRP = funRelPron ;
  RelVP = relVerbPhrase ;
  RelSlash = relSlash ;
  ModRS = modRelClause ;
  RelCl = relSuch ;


--!
--3 Questions and imperatives
--

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

  PosImperVP = imperVerbPhrase True ;
  NegImperVP = imperVerbPhrase False ;

  IndicPhrase = indicUtt ;
  QuestPhrase = interrogUtt ;
  ImperOne  = imperUtterance singular ;
  ImperMany = imperUtterance plural ;

  PrepS p = ss (p.s ++ ",") ;
  AdvS = advSentence ;


--!
--3 Coordination
--

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
  SubjQS = subjunctQuestion ;
  SubjVP = subjunctVerbPhrase ;

  PhrNP = useNounPhrase ;
  PhrOneCN = useCommonNounPhrase singular ;
  PhrManyCN = useCommonNounPhrase plural ;
  PhrIP ip = ip ;
  PhrIAdv ia = ia ;

  OnePhr p = p ;
  ConsPhr = cc2 ;

-----------------------
-- special constructions

  OneVP = predVerbGroupClause (nameNounPhrase (nameReg "one" human)) ;
----  ThereNP = thereIs ;

  ExistCN A = predVerbGroupClause 
                (nameNounPhrase (nameReg "there" Neutr))
                (complTransVerb (mkTransVerbDir verbBe) 
                   (indefNounPhrase singular A)) ;
  ExistNumCN nu A = 
              predVerbGroupClause 
                (nameNounPhrasePl (nameReg "there" Neutr))
                (complTransVerb (mkTransVerbDir verbBe) 
                   (indefNounPhraseNum plural nu A)) ;

  ExistQCl A = questVerbPhrase
                (nameNounPhrase (nameReg "there" Neutr))
                (complTransVerb (mkTransVerbDir verbBe) 
                   (indefNounPhrase singular A)) ;
  ExistNumQCl nu A = 
              questVerbPhrase
                (nameNounPhrasePl (nameReg "there" Neutr))
                (complTransVerb (mkTransVerbDir verbBe) 
                   (indefNounPhraseNum plural nu A)) ;

} ;

