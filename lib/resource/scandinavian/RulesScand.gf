--# -path=.:../abstract:../../prelude

incomplete concrete RulesScand of Rules = CategoriesScand ** 
  open Prelude, SyntaxScand in {

lin 
  UseN = noun2CommNounPhrase ;
  ModAP = modCommNounPhrase ;
  ModGenOne = npGenDet singular noNum ;
  ModGenNum = npGenDet plural ;
  UsePN = nameNounPhrase ;
  UseN2 = funAsCommNounPhrase ;
  AppN2 = appFunComm ;
  AppN3 = appFun2 ;
  UseA = adj2adjPhrase ;
  ComplA2 = complAdj ;
  PositADeg = positAdjPhrase ;
  ComparADeg = comparAdjPhrase ;
  SuperlNP = superlNounPhrase ;

  DetNP = detNounPhrase ;
  IndefOneNP = indefNounPhrase singular ;
  IndefNumNP = indefNounPhraseNum plural ;
  DefOneNP = defNounPhrase singular ;
  DefNumNP = defNounPhraseNum plural ;
  MassNP = detNounPhrase (mkDeterminerSg (detSgInvar []) IndefP) ;
  UseInt i = {s = table {Nom => i.s ; Gen => i.s ++ "s"}} ; ---
  NoNum = noNum ;

  SymbPN i = {s = \\_ => i.s ; g = NNeutr} ;
  SymbCN cn s =
    {s = \\a,n,c => cn.s ! a ! n ! c ++ s.s ; 
     g = cn.g ;
     p = cn.p
     } ;
  IntCN cn s =
    {s = \\a,n,c => cn.s ! a ! n ! c ++ s.s ; 
     g = cn.g ;
     p = cn.p
     } ;

  CNthatS = nounThatSentence ;

  PredVV2 = transVerbVerb ;
  AdjPart = adjPastPart ;

  PredV2A = complDitransAdjVerb ;
  PredSubjV2V = complDitransVerbVerb False ;
  PredObjV2V = complDitransVerbVerb True ;
  PredV2S = complDitransSentVerb ;
  PredV2Q = complDitransQuestVerb ;
  PredVA = complAdjVerb ;

  UseV2V x = x ;
  UseV2S x = x ;
  UseV2Q x = x ;
  UseA2S x = x ;
  UseA2V x = x ;

   UseCl tp cl = {s = \\o => tp.s ++ cl.s ! tp.b ! ClFinite tp.t tp.a o} ;
 
  PosVP tp = predVerbGroup True tp.a ;
  NegVP tp = predVerbGroup False tp.a ;

  ProgVP = progressiveVerbPhrase ;

  PosTP t a = {s = t.s ++ a.s ; b = True  ; t = t.t ; a = a.a} ;
  NegTP t a = {s = t.s ++ a.s ; b = False ; t = t.t ; a = a.a} ;
  TPresent     = {s = [] ; t = Present} ;
  TPast        = {s = [] ; t = Past} ;
  TFuture      = {s = [] ; t = Future} ;
  TConditional = {s = [] ; t = Condit} ;
  ASimul = {s = [] ; a = Simul} ;
  AAnter = {s = [] ; a = Anter} ;

  PredVP = predVerbGroupClause ;

  PredV  = predVerb ;
  PredAP = predAdjective ;
  PredSuperl a = predAdjective (superlAdjPhrase a) ;
  PredCN = predCommNoun ;
  PredV2 = complTransVerb ;
  PredV3 = complDitransVerb ;
  PredPassV = passVerb ;
  ReflV2 = reflTransVerb ;

  PredNP = predNounPhrase ;
  PredPP = predAdverb ;
  PredVS = complSentVerb ;
  PredVQ = complQuestVerb ;
  PredVV = complVerbVerb ;
  VTrans = transAsVerb ;
  PredV0 = predVerb0 ;

  PredAS  = predAdjSent ;
  PredA2S = predAdjSent2 ;
  PredAV  = complVerbAdj ;
  PredSubjA2V = complVerbAdj2 False ;
  PredObjA2V = complVerbAdj2 True ;

  AdjAdv a = advPost (a.s ! adverbForm ! Nom) ;
  AdvPP p = p ;
  PrepNP p = prepPhrase p.s ; ---
  AdvVP = adVerbPhrase ;
  AdvCN = advCommNounPhrase ;
  AdvAP = advAdjPhrase ;

  ExistCN A = predVerbGroupClause npDet 
                (complTransVerb (mkDirectVerb (deponentVerb verbFinnas)) 
                   (indefNounPhrase singular A)) ;
  ExistNumCN nu A = predVerbGroupClause npDet 
                (complTransVerb (mkDirectVerb (deponentVerb verbFinnas)) 
                   (indefNounPhraseNum plural nu A)) ;

  SlashV2 = slashTransVerb ;
  OneVP = predVerbGroupClause npMan ;

  IdRP = identRelPron ;
  FunRP = funRelPron ;
  RelVP = relVerbGroup ;
  RelSlash = relSlash ;
  ModRS = modRelClause ;
  RelCl = relSuch ;

  UseRCl tp cl = 
    {s = \\gn,p => tp.s ++ cl.s ! tp.b ! VFinite tp.t tp.a ! gn ! p} ;

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

  ExistQCl A = questVerbPhrase npDet 
                (complTransVerb (mkDirectVerb (deponentVerb verbFinnas)) 
                   (indefNounPhrase singular A)) ;
  ExistNumQCl nu A = questVerbPhrase npDet 
                (complTransVerb (mkDirectVerb (deponentVerb verbFinnas)) 
                   (indefNounPhraseNum plural nu A)) ;


  UseQCl tp cl = {s = \\q => tp.s ++ cl.s ! tp.b ! VFinite tp.t tp.a ! q} ;


  PosImperVP = imperVerbPhrase True ;
  NegImperVP = imperVerbPhrase False ;

  IndicPhrase = indicUtt ;
  QuestPhrase = interrogUtt ;
  ImperOne  = imperUtterance singular ;
  ImperMany = imperUtterance plural ;

  PrepS p = ss (p.s ++ ",") ;
  AdvS = advSentence ;

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

} ;
