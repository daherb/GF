--# -path=.:../abstract:../../prelude

--1 The Top-Level Russian Resource Grammar
--
-- Janna Khegai 2003
-- on the basis of code for other languages by Aarne Ranta
--
-- This is the Russian concrete syntax of the multilingual resource
-- grammar. Most of the work is done in the file $syntax.RusU.gf$.
-- However, for the purpose of documentation, we make here explicit the
-- linearization types of each category, so that their structures and
-- dependencies can be seen.
-- Another substantial part is the linearization rules of some
-- structural words.
--
-- The users of the resource grammar should not look at this file for the
-- linearization rules, which are in fact hidden in the document version.
-- They should use $resource.Abs.gf$ to access the syntactic rules.
-- This file can be consulted in those, hopefully rare, occasions in which
-- one has to know how the syntactic categories are
-- implemented. The parameter types are defined in $types.RusU.gf$.

concrete StructuralRus of Structural = CombinationsRus ** open Prelude, SyntaxRus in {
flags 
 coding=utf8 ;

lin
  INP    = pron2NounPhrase pronYa Animate;
  ThouNP = pron2NounPhrase pronTu Animate;
  HeNP   = pron2NounPhrase pronOn Animate;
  SheNP  = pron2NounPhrase pronOna Animate;
  ItNP   = pron2NounPhrase pronOno Inanimate;
  WeNumNP = pronWithNum (pron2NounPhrase pronMu Animate);
  YeNumNP = pronWithNum (pron2NounPhrase pronVu Animate);
  YouNP  = pron2NounPhrase pronVu Animate;
  TheyNP = pron2NounPhrase pronOni Animate;

  EveryDet = kazhdujDet ** {n = Sg ; g = PNoGen; c= Nom} ; 
  AllMassDet   = vesDet ** {n = Sg; g = PNoGen;  c = Nom} ; 
  AllNumDet  = mkDeterminerNum (vseDetPl ** {n = Pl; g = PNoGen; c = Nom} ); 
  WhichDet = kotorujDet ** {n = Sg; g = PNoGen; c= Nom} ;
  WhichNumDet = mkDeterminerNum (kotorujDet ** {n = Pl; g = PNoGen; c= Nom} );  
  MostDet  = bolshinstvoSgDet ** {n = Sg; g = (PGen Neut); c= Gen} ; 
  -- inanimate, Sg: "большинство телефонов безмолству-ет" 
  MostsDet = bolshinstvoPlDet ** {n = Pl; g = (PGen Neut); c= Gen} ;  
  -- animate, Pl: "большинство учащихся хорошо подготовлен-ы"
  ManyDet  = mnogoSgDet ** {n = Sg; g = (PGen Neut); c= Gen} ; 
  MuchDet  = mnogoSgDet ** {n = Sg; g = (PGen Neut); c= Gen} ; -- same as previous
  SomeDet  = nekotorujDet ** {n = Sg; g = PNoGen; c= Nom} ;
  SomeNumDet = mkDeterminerNum (nekotorujDet ** {n = Pl; g = PNoGen; c= Nom} );  
  AnyDet   = lubojDet ** {n = Sg; g = PNoGen; c= Nom} ;
  AnyNumDet  = mkDeterminerNum (lubojDet ** {n = Pl; g = PNoGen; c= Nom} );  
  NoDet    = nikakojDet ** {n = Sg; g = PNoGen; c= Nom} ;
  NoNumDet   = mkDeterminerNum (nikakojDet ** {n = Pl; g = PNoGen; c= Nom} );  
  ThisDet  = etotDet ** {n = Sg; g = PNoGen; c= Nom} ;
  TheseNumDet = mkDeterminerNum (etotDet ** {n = Pl; g = PNoGen; c= Nom} );  
  ThatDet  = totDet ** {n = Sg; g = PNoGen; c= Nom} ;
  ThoseNumDet = mkDeterminerNum (totDet ** {n = Pl; g = PNoGen; c= Nom} );  
  
  ThisNP = det2NounPhrase etotDet ; -- inanimate form only
  ThatNP = det2NounPhrase totDet ; -- inanimate form only
  TheseNumNP n =  { s =\\_ => [] ; n = Pl; p = P3; g= PGen Fem ; anim = Animate ;  pron = True} ; 
   -- missing in Russian
  ThoseNumNP n =  { s =\\_ => [] ; n = Pl; p = P3; g=PGen Fem ; anim = Animate ;  pron = True} ; 
   -- missing in Russian

EverybodyNP = mkNounPhrase Pl (noun2CommNounPhrase (eEnd_Decl "вс")) ;
SomebodyNP = pron2NounPhrase pronKtoTo Animate;
NobodyNP = pron2NounPhrase pronNikto Animate;
EverythingNP = pron2NounPhrase pronVseInanimate Inanimate;
SomethingNP = pron2NounPhrase pronChtoTo Inanimate ;
NothingNP = pron2NounPhrase pronNichto Inanimate;

CanVV =  extVerb verbMoch Act Present  ;
CanKnowVV = extVerb verbMoch Act Present  ;
MustVV = extVerb verbDolzhen Act Present  ;
WantVV = extVerb verbKhotet Act Present  ;

  HowIAdv = ss "как" ;
  WhenIAdv = ss "когда" ;
  WhereIAdv = ss "где" ;
  WhyIAdv = ss "почему" ;

  AndConj  = ss "и"  ** {n = Pl} ;
  OrConj   = ss "или"  ** {n = Sg} ;
  BothAnd  = sd2 "как" [", так и"]  ** {n = Pl} ;
  EitherOr = sd2 "либо" [", либо"]  ** {n = Sg} ;
-- comma is not visible in GUI!

-- In case of "neither..  no" expression double negation is not 
-- only possible, but also required in Russian.
-- There is no means of control for this however in the resource grammar.

  NeitherNor = sd2 "ни" [", ни"]  ** {n = Sg} ;

  IfSubj   = ss "если" ;
  WhenSubj = ss "когда" ;
  AlthoughSubj = ss "хотя" ;

  PhrYes = ss ["Да ."] ;
  PhrNo = ss ["Нет ."] ;

  EverywhereNP = ss "везде" ;
  SomewhereNP = ss "где-нибудь" ;
  NowhereNP = ss "нигде" ;
  VeryAdv = ss "очень" ;
  TooAdv = ss "слишком" ;
  OtherwiseAdv = ss "иначе" ;
   AlmostAdv = ss "почти" ;
  QuiteAdv = ss "довольно" ;
  ThereforeAdv = ss "следовательно" ;

  InPrep = { s2 = "в" ; c = Prepos };
  OnPrep = { s2 = "на" ; c = Prepos };
  ToPrep = { s2 = "к" ; c = Dat };
  ThroughPrep = { s2 = "через" ; c = Acc };
  AbovePrep =  { s2 = "над" ; c = Inst};
  UnderPrep = { s2 = "под"  ; c = Inst };
  InFrontPrep = { s2 = "перед" ; c = Inst};
  BehindPrep = { s2 = "за" ; c = Inst };
  BetweenPrep = { s2 = "между" ; c = Inst};
  FromPrep = { s2 = "от" ; c = Gen };
  BeforePrep = { s2 = "перед" ; c = Inst};
  DuringPrep = { s2 = ["в течение"] ; c = Gen};
  AfterPrep = { s2 = "после" ; c = Gen };
  WithPrep = { s2 = "с" ; c = Inst};
  WithoutPrep = { s2 = "без" ; c = Gen};
  ByMeansPrep = { s2 = ["с помощью"] ; c = Gen};
  PossessPrep = { s2 = "" ; c = Gen}; --- ?? AR 19/2/2004
  PartPrep = { s2 = "" ; c = Nom}; -- missing in Russian
  AgentPrep = { s2 = "" ; c = Nom}; -- missing in Russian
} ;
