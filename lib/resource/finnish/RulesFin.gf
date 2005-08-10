--# -path=.:../abstract:../../prelude

--1 The Top-Level Finnish Resource Grammar: Combination Rules
--
-- Aarne Ranta 2002 -- 2003
--
-- This is the Finnish concrete syntax of the multilingual resource
-- grammar. Most of the work is done in the file $SyntaxFin.gf$.
--
-- The users of the resource grammar should not look at this file for the
-- linearization rules, which are in fact hidden in the document version.
-- They should use $Rules.gf$ to access the syntactic rules.
-- This file can be consulted in those, hopefully rare, occasions in which
-- one has to know how the rules are
-- implemented. The parameter types are defined in $TypesFin.gf$. For
-- parameter values, access through $ParadigmFin$ is recommended.

concrete RulesFin of Rules = CategoriesFin ** open Prelude, SyntaxFin in {

flags 
  optimize=all ;

lin 
  UseN  = noun2CommNounPhrase ;
  UsePN = nameNounPhrase ;

  SymbPN i = {s = \\_ => i.s} ;  --- case endings often needed
  SymbCN cn s =
    {s = \\f,n,c => cn.s ! f ! n ! c ++ s.s ; 
     g = cn.g} ;
  IntCN cn s =
    {s = \\f,n,c => cn.s ! f ! n ! c ++ s.s ; 
     g = cn.g} ;

  IndefOneNP = indefNounPhrase singular ;
  IndefNumNP = nounPhraseNum False ;
  DefOneNP = defNounPhrase singular ;
  DefNumNP = nounPhraseNum True ;

  DetNP = detNounPhrase ;
  NDetNP = numDetNounPhrase ;
----  NDetNum = justNumDetNounPhrase ; 
  MassNP = partNounPhrase singular ;

  AppN2 = appFunComm ;
  AppN3 = appFun2 ;
  UseN2 = funAsCommNounPhrase ;

  ModAP = modCommNounPhrase ;
  CNthatS = nounThatSentence ;

  ModGenOne = npGenDet singular ;
  ModGenNum = npGenDetNum ;

  UseInt i = {s = \\_ => i.s ; isNum = True ; n = Pl} ; --- case endings; Sg for 1
  NoNum = noNum ;

  UseA = adj2adjPhrase ;
-----  ComplA2 = complAdj ;

----  ComplAV av vpi = {s = \\_,a => av.s ! a ++ vpi.s ! VIInfinit} ;
----  ComplObjA2V av obj vpi = {s = \\_,a => av.s ! a ++ obj.s ! complCase
----    True av.c (SVI VIInf3Iness) ++ vpi.s ! VIInfinit} ;

  PositADeg  = positAdjPhrase ;
  ComparADeg = comparAdjPhrase ;
  SuperlADeg = superlAdjPhrase ;

-- verbs and verb prases

  PredAS adj sent = sats2clause (
    insertComplement 
      (mkSats impersNounPhrase (vNom verbOlla))
      (complAdjPhrase Sg (adj2adjPhrase adj) ++ sent.s)
      ) ; 
  PredV0 rain = sats2clause (mkSats impersNounPhrase (vNom rain)) ;

-- Partial saturation.

  UseV2 v = v ;

----  ComplA2S = predAdjSent2 ;

----  AdjPart = adjPastPart ;

----  UseV2V x = verb2aux x ** {isAux = False} ;

  UseV2S x = x ;
  UseV2Q x = x ;
  UseA2S x = x ;
  UseA2V x = x ;

  UseCl  tp cl = {s = tp.s ++ cl.s ! tp.b ! VFinite SDecl  tp.t tp.a} ;
  UseQCl tp cl = {s = tp.s ++ cl.s ! tp.b ! VFinite SQuest tp.t tp.a} ;
----  UseRCl tp cl = {s = \\a => tp.s ++ cl.s ! tp.b ! VFinite tp.t tp.a ! a} ;

  PosTP t a = {s = t.s ++ a.s ; b = True  ; t = t.t ; a = a.a} ;
  NegTP t a = {s = t.s ++ a.s ; b = False ; t = t.t ; a = a.a} ;

  TPresent     = {s = [] ; t = Present} ;
  TPast        = {s = [] ; t = Past} ;
  TFuture      = {s = [] ; t = Future} ;
  TConditional = {s = [] ; t = Conditional} ;

  ASimul = {s = [] ; a = Simul} ;
  AAnter = {s = [] ; a = Anter} ;

-- Adverbs.

  AdjAdv a = ss (a.s ! AAdv) ; --- also APred?
  AdvPP p = p ;
  PrepNP = prepPhrase ;
  AdvCN = advCommNounPhrase ;
  AdvAP = advAdjPhrase ;
  AdvAdv = cc2 ;
  AdvNP pn pp = {s = \\c => pn.s ! c ++ pp.s ; n = pn.n ; p = pn.p} ;

--3 Sentences and relative clauses
--

----  SlashV2 = slashTransVerbCl ;
----  SlashVV2 = slashVerbVerb ;
----  SlashAdv cl p = slashAdverb cl p.s ;

  IdRP = identRelPron ;
  FunRP = funRelPron ;
----  RelSlash = relSlash ;
----  ModRS = modRelClause ;
----  RelCl = relSuch ;


--!
--3 Questions and imperatives
--

----  IDetCN d n = nounPhraseInt (detNounPhrase d n) ;
  FunIP = funIntPron ;

  QuestCl cl = cl ;
----  IntSlash = intSlash ;
  QuestAdv = questAdverbial ;

  PosImpVP = imperVerbPhrase True ;
  NegImpVP = imperVerbPhrase False ;

  IndicPhrase = indicUtt ;
  QuestPhrase = interrogUtt ;
  ImperOne  = imperUtterance singular ;
  ImperMany = imperUtterance plural ;

----  AdvCl  = advClause ;
----  AdvVPI = advVerbPhrase ;

  AdCPhr = advSentence ;
  AdvPhr = advSentence ;


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

  TwoAdv = twoSentence ;
  ConsAdv = consSentence ;
  ConjAdv = conjunctSentence ;
  ConjDAdv = conjunctDistrSentence ;

  SubjS = subjunctSentence ;
  SubjImper = subjunctImperative ;
  SubjQS = subjunctQuestion ;
  AdvSubj if A = ss (if.s ++ A.s) ;

  PhrNP = useNounPhrase ;
  PhrOneCN = useCommonNounPhrase singular ;
  PhrManyCN = useCommonNounPhrase plural ;
  PhrIP ip = ip ;
  PhrIAdv ia = ia ;
----  PhrVPI = verbUtterance ;

  OnePhr p = p ;
  ConsPhr = cc2 ;

-----------------------
-- special constructions

----  OneNP = nameNounPhrase (nameReg "one" human) ;

  ExistCN cn = 
    sats2clause (
      mkSatsCopula impersNounPhrase ("olemassa" ++ (singularNounPhrase cn).s ! NPCase Nom)
      ) ;

  ExistNumCN nu cn = 
    sats2clause (
      mkSatsCopula impersNounPhrase (
        "olemassa" ++ (nounPhraseNum False nu cn).s ! NPCase Nom)
      ) ;

} ;
