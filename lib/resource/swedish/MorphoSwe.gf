--1 A Simple Swedish Resource Morphology
--
-- Aarne Ranta 2002
--
-- This resource morphology contains definitions needed in the resource
-- syntax. It moreover contains copies of the most usual inflectional patterns
-- as defined in functional morphology (in the Haskell file $RulesSw.hs$).
--
-- We use the parameter types and word classes defined for morphology.

resource MorphoSwe = TypesSwe ** open Prelude in {

oper
  mkVerbPart : (supa,super,sup,s�p,supit,supen,upp : Str) -> Verb = 
   \finna,finner,finn,fann,funnit,funnen,upp ->
    let funn = ptPretForms funnen in
    {s = table {
    VF (Pres Ind Act) => finner ;
    VF (Pres Ind Pass) => finn + "s" ;
    VF (Pres Cnj Act) => finn + "e" ;
    VF (Pres Cnj Pass) => finn + "es" ;
    VF (Pret Ind Act) => fann ;
    VF (Pret Ind Pass) => fann + "s" ;
    VF (Pret Cnj Act) => fann ;        --- = ind
    VF (Pret Cnj Pass) => fann + "s" ; --- 
    VF Imper => finn ;
    VI (Inf Act) => finna ;
    VI (Inf Pass) => finna + "s" ;
    VI (Supin Act) => funnit ;
    VI (Supin Pass) => funnit + "s" ;
    VI (PtPres Nom) => finn + "ande" ;
    VI (PtPres Gen) => finn + "andes" ;
    VI (PtPret a c) => funn ! a ! c
    } ;
     s1 = upp
    } ;

ptPretForms : Str -> AdjFormPos => Case => Str = \funnen -> \\a,c =>  
  mkCase c (
 {- ----
    case Predef.dp 2 funnen of {
   "en" => let funn : Str = Predef.tk 2 funnen in 
     case a of {
      (Strong (ASg Utr)) => funn + "en" ;
      (Strong (ASg Neutr)) => funn + "et" ;
      (Strong APl) => funn + "a" ;
      (Weak (AxSg NoMasc)) => funn + "a" ;
      (Weak (AxSg Masc)) => funn + "e" ;
      (Weak AxPl) => funn + "a" 
    } ;
  "ad" => let funn : Str = Predef.tk 2 funnen in 
     case a of {
      (Strong (ASg Utr)) => funn + "ad" ;
      (Strong (ASg Neutr)) => funn + "at" ;
      (Strong APl) => funn + "ade" ;
      (Weak _) => funn + "ade"
    } ;

  _ => 
-}
  funnen ---- to be completed
 ---- }
 ) ;

mkCase : Case -> Str -> Str = \c,f -> case c of {
      Nom => f ;
      Gen => f + "s"
      } ;


-- The most common is a verb without a particle.

  mkVerb : (_,_,_,_,_,_ : Str) -> Verb = \supa,super,sup,s�p,supit,supen ->
    mkVerbPart supa super sup s�p supit supen [] ; 


-- Prepositions are just strings.
  Preposition = Str ;

-- Relative pronouns have a special case system. $RPrep$ is the form used
-- after a preposition (e.g. "det hus i vilket jag bor").
param
  RelCase = RNom | RAcc | RGen | RPrep ;

oper
  relPronForms : RelCase => GenNum => Str = table {
    RNom  => \\_ => "som" ;
    RAcc  => \\_ => variants {"som" ; []} ;
    RGen  => \\_ => "vars" ;
    RPrep => pronVilken
    } ;
  
  pronVilken = table {
      ASg Utr   => "vilken" ; 
      ASg Neutr => "vilket" ; 
      APl       => "vilka"
      } ;

  pronS�dan = table {
      ASg Utr   => "s�dan" ; 
      ASg Neutr => "s�dant" ; 
      APl       => "s�dana"
      } ;

-- What follows are machine-generated inflection paradigms from functional 
-- morphology. Hence they are low-level paradigms, without any 
-- abstractions or generalizations: the Haskell code is better in these respects.
-- 
-- The variable names are selected in such a way that the paradigms can be read
-- as inflection tables of certain words.

oper sApa : Str -> Subst = \ap -> 
 {s = table {
    SF Sg Indef Nom => ap + "a" ;
    SF Sg Indef Gen => ap + "as" ;
    SF Sg Def Nom => ap + "an" ;
    SF Sg Def Gen => ap + "ans" ;
    SF Pl Indef Nom => ap + "or" ;
    SF Pl Indef Gen => ap + "ors" ;
    SF Pl Def Nom => ap + "orna" ;
    SF Pl Def Gen => ap + "ornas"
    } ;
  h1 = Utr
  } ;

oper sBil : Str -> Subst = \bil -> 
 {s = table {
    SF Sg Indef Nom => bil ;
    SF Sg Indef Gen => bil + "s" ;
    SF Sg Def Nom => bil + "en" ;
    SF Sg Def Gen => bil + "ens" ;
    SF Pl Indef Nom => bil + "ar" ;
    SF Pl Indef Gen => bil + "ars" ;
    SF Pl Def Nom => bil + "arna" ;
    SF Pl Def Gen => bil + "arnas"
    } ;
  h1 = Utr
  } ;

oper sPojke : Str -> Subst = \pojk -> 
 {s = table {
    SF Sg Indef Nom => pojk + "e" ;
    SF Sg Indef Gen => pojk + "es" ;
    SF Sg Def Nom => pojk + "en" ;
    SF Sg Def Gen => pojk + "ens" ;
    SF Pl Indef Nom => pojk + "ar" ;
    SF Pl Indef Gen => pojk + "ars" ;
    SF Pl Def Nom => pojk + "arna" ;
    SF Pl Def Gen => pojk + "arnas"
    } ;
  h1 = Utr
  } ;

oper sNyckel : Str -> Subst = \nyck -> 
 {s = table {
    SF Sg Indef Nom => nyck + "el" ;
    SF Sg Indef Gen => nyck + "els" ;
    SF Sg Def Nom => nyck + "eln" ;
    SF Sg Def Gen => nyck + "elns" ;
    SF Pl Indef Nom => nyck + "lar" ;
    SF Pl Indef Gen => nyck + "lars" ;
    SF Pl Def Nom => nyck + "larna" ;
    SF Pl Def Gen => nyck + "larnas"
    } ;
  h1 = Utr
  } ;

oper sKam : Str -> Subst = \kam -> 
 {s = table {
    SF Sg Indef Nom => kam ;
    SF Sg Indef Gen => kam + "s" ;
    SF Sg Def Nom => kam + "men" ;
    SF Sg Def Gen => kam + "mens" ;
    SF Pl Indef Nom => kam + "mar" ;
    SF Pl Indef Gen => kam + "mars" ;
    SF Pl Def Nom => kam + "marna" ;
    SF Pl Def Gen => kam + "marnas"
    } ;
  h1 = Utr
  } ;

oper sSak : Str -> Subst = \sak -> 
 {s = table {
    SF Sg Indef Nom => sak ;
    SF Sg Indef Gen => sak + "s" ;
    SF Sg Def Nom => sak + "en" ;
    SF Sg Def Gen => sak + "ens" ;
    SF Pl Indef Nom => sak + "er" ;
    SF Pl Indef Gen => sak + "ers" ;
    SF Pl Def Nom => sak + "erna" ;
    SF Pl Def Gen => sak + "ernas"
    } ;
  h1 = Utr
  } ;

oper sVarelse : Str -> Subst = \varelse -> 
 {s = table {
    SF Sg Indef Nom => varelse ;
    SF Sg Indef Gen => varelse + "s" ;
    SF Sg Def Nom => varelse + "n" ;
    SF Sg Def Gen => varelse + "ns" ;
    SF Pl Indef Nom => varelse + "r" ;
    SF Pl Indef Gen => varelse + "rs" ;
    SF Pl Def Nom => varelse + "rna" ;
    SF Pl Def Gen => varelse + "rnas"
    } ;
  h1 = Utr
  } ;

oper sNiv� : Str -> Subst = \niv� -> 
 {s = table {
    SF Sg Indef Nom => niv� ;
    SF Sg Indef Gen => niv� + "s" ;
    SF Sg Def Nom => niv� + "n" ;
    SF Sg Def Gen => niv� + "ns" ;
    SF Pl Indef Nom => niv� + "er" ;
    SF Pl Indef Gen => niv� + "ers" ;
    SF Pl Def Nom => niv� + "erna" ;
    SF Pl Def Gen => niv� + "ernas"
    } ;
  h1 = Utr
  } ;

oper sParti : Str -> Subst = \parti -> 
 {s = table {
    SF Sg Indef Nom => parti ;
    SF Sg Indef Gen => parti + "s" ;
    SF Sg Def Nom => parti + "et" ;
    SF Sg Def Gen => parti + "ets" ;
    SF Pl Indef Nom => parti + "er" ;
    SF Pl Indef Gen => parti + "ers" ;
    SF Pl Def Nom => parti + "erna" ;
    SF Pl Def Gen => parti + "ernas"
    } ;
  h1 = Neutr
  } ;

oper sMuseum : Str -> Subst = \muse -> 
 {s = table {
    SF Sg Indef Nom => muse + "um" ;
    SF Sg Indef Gen => muse + "ums" ;
    SF Sg Def Nom => muse + "et" ;
    SF Sg Def Gen => muse + "ets" ;
    SF Pl Indef Nom => muse + "er" ;
    SF Pl Indef Gen => muse + "ers" ;
    SF Pl Def Nom => muse + "erna" ;
    SF Pl Def Gen => muse + "ernas"
    } ;
  h1 = Neutr
  } ;

oper sRike : Str -> Subst = \rike -> 
 {s = table {
    SF Sg Indef Nom => rike ;
    SF Sg Indef Gen => rike + "s" ;
    SF Sg Def Nom => rike + "t" ;
    SF Sg Def Gen => rike + "ts" ;
    SF Pl Indef Nom => rike + "n" ;
    SF Pl Indef Gen => rike + "ns" ;
    SF Pl Def Nom => rike + "na" ;
    SF Pl Def Gen => rike + "nas"
    } ;
  h1 = Neutr
  } ;

oper sLik : Str -> Subst = \lik -> 
 {s = table {
    SF Sg Indef Nom => lik ;
    SF Sg Indef Gen => lik + "s" ;
    SF Sg Def Nom => lik + "et" ;
    SF Sg Def Gen => lik + "ets" ;
    SF Pl Indef Nom => lik ;
    SF Pl Indef Gen => lik + "s" ;
    SF Pl Def Nom => lik + "en" ;
    SF Pl Def Gen => lik + "ens"
    } ;
  h1 = Neutr
  } ;

oper sRum : Str -> Subst = \rum -> 
 {s = table {
    SF Sg Indef Nom => rum ;
    SF Sg Indef Gen => rum + "s" ;
    SF Sg Def Nom => rum + "met" ;
    SF Sg Def Gen => rum + "mets" ;
    SF Pl Indef Nom => rum ;
    SF Pl Indef Gen => rum + "s" ;
    SF Pl Def Nom => rum + "men" ;
    SF Pl Def Gen => rum + "mens"
    } ;
  h1 = Neutr
  } ;

oper sHus : Str -> Subst = \hus -> 
 {s = table {
    SF Sg Indef Nom => hus ;
    SF Sg Indef Gen => hus ;
    SF Sg Def Nom => hus + "et" ;
    SF Sg Def Gen => hus + "ets" ;
    SF Pl Indef Nom => hus ;
    SF Pl Indef Gen => hus ;
    SF Pl Def Nom => hus + "en" ;
    SF Pl Def Gen => hus + "ens"
    } ;
  h1 = Neutr
  } ;

oper sPapper : Str -> Subst = \papp -> 
 {s = table {
    SF Sg Indef Nom => papp + "er" ;
    SF Sg Indef Gen => papp + "ers" ;
    SF Sg Def Nom => papp + "ret" ;
    SF Sg Def Gen => papp + "rets" ;
    SF Pl Indef Nom => papp + "er" ;
    SF Pl Indef Gen => papp + "ers" ;
    SF Pl Def Nom => papp + "ren" ;
    SF Pl Def Gen => papp + "rens"
    } ;
  h1 = Neutr
  } ;

oper sNummer : Str -> Subst = \num -> 
 {s = table {
    SF Sg Indef Nom => num + "mer" ;
    SF Sg Indef Gen => num + "mers" ;
    SF Sg Def Nom => num + "ret" ;
    SF Sg Def Gen => num + "rets" ;
    SF Pl Indef Nom => num + "mer" ;
    SF Pl Indef Gen => num + "mers" ;
    SF Pl Def Nom => num + "ren" ;
    SF Pl Def Gen => num + "rens"
    } ;
  h1 = Neutr
  } ;

oper sKikare : Str -> Subst = \kikar -> 
 {s = table {
    SF Sg Indef Nom => kikar + "e" ;
    SF Sg Indef Gen => kikar + "es" ;
    SF Sg Def Nom => kikar + "en" ;
    SF Sg Def Gen => kikar + "ens" ;
    SF Pl Indef Nom => kikar + "e" ;
    SF Pl Indef Gen => kikar + "es" ;
    SF Pl Def Nom => kikar + "na" ;
    SF Pl Def Gen => kikar + "nas"
    } ;
  h1 = Utr
  } ;

oper sProgram : Str -> Subst = \program -> 
 {s = table {
    SF Sg Indef Nom => program ;
    SF Sg Indef Gen => program + "s" ;
    SF Sg Def Nom => program + "met" ;
    SF Sg Def Gen => program + "mets" ;
    SF Pl Indef Nom => program ;
    SF Pl Indef Gen => program + "s" ;
    SF Pl Def Nom => program + "men" ;
    SF Pl Def Gen => program + "mens"
    } ;
  h1 = Neutr
  } ;

oper aFin : Str -> Adj = \fin -> 
 {s = table {
    AF (Posit (Strong (ASg Utr))) Nom => fin ;
    AF (Posit (Strong (ASg Utr))) Gen => fin + "s" ;
    AF (Posit (Strong (ASg Neutr))) Nom => fin + "t" ;
    AF (Posit (Strong (ASg Neutr))) Gen => fin + "ts" ;
    AF (Posit (Strong APl)) Nom => fin + "a" ;
    AF (Posit (Strong APl)) Gen => fin + "as" ;
    AF (Posit (Weak (AxSg NoMasc))) Nom => fin + "a" ;
    AF (Posit (Weak (AxSg NoMasc))) Gen => fin + "as" ;
    AF (Posit (Weak (AxSg Masc))) Nom => fin + "e" ;
    AF (Posit (Weak (AxSg Masc))) Gen => fin + "es" ;
    AF (Posit (Weak AxPl)) Nom => fin + "a" ;
    AF (Posit (Weak AxPl)) Gen => fin + "as" ;
    AF Compar Nom => fin + "are" ;
    AF Compar Gen => fin + "ares" ;
    AF (Super SupStrong) Nom => fin + "ast" ;
    AF (Super SupStrong) Gen => fin + "asts" ;
    AF (Super SupWeak) Nom => fin + "aste" ;
    AF (Super SupWeak) Gen => fin + "astes"
    }
  } ;

oper aFager : Str -> Adj = \fag -> 
 {s = table {
    AF (Posit (Strong (ASg Utr))) Nom => fag + "er" ;
    AF (Posit (Strong (ASg Utr))) Gen => fag + "ers" ;
    AF (Posit (Strong (ASg Neutr))) Nom => fag + "ert" ;
    AF (Posit (Strong (ASg Neutr))) Gen => fag + "erts" ;
    AF (Posit (Strong APl)) Nom => fag + "era" ;
    AF (Posit (Strong APl)) Gen => fag + "eras" ;
    AF (Posit (Weak (AxSg NoMasc))) Nom => fag + "era" ;
    AF (Posit (Weak (AxSg NoMasc))) Gen => fag + "eras" ;
    AF (Posit (Weak (AxSg Masc))) Nom => fag + "ere" ;
    AF (Posit (Weak (AxSg Masc))) Gen => fag + "eres" ;
    AF (Posit (Weak AxPl)) Nom => fag + "era" ;
    AF (Posit (Weak AxPl)) Gen => fag + "eras" ;
    AF Compar Nom => fag + "erare" ;
    AF Compar Gen => fag + "erares" ;
    AF (Super SupStrong) Nom => fag + "erast" ;
    AF (Super SupStrong) Gen => fag + "erasts" ;
    AF (Super SupWeak) Nom => fag + "eraste" ;
    AF (Super SupWeak) Gen => fag + "erastes"
    }
  } ;

oper aGrund : Str -> Adj = \grun -> 
 {s = table {
    AF (Posit (Strong (ASg Utr))) Nom => grun + "d" ;
    AF (Posit (Strong (ASg Utr))) Gen => grun + "ds" ;
    AF (Posit (Strong (ASg Neutr))) Nom => grun + "t" ;
    AF (Posit (Strong (ASg Neutr))) Gen => grun + "ts" ;
    AF (Posit (Strong APl)) Nom => grun + "da" ;
    AF (Posit (Strong APl)) Gen => grun + "das" ;
    AF (Posit (Weak (AxSg NoMasc))) Nom => grun + "da" ;
    AF (Posit (Weak (AxSg NoMasc))) Gen => grun + "das" ;
    AF (Posit (Weak (AxSg Masc))) Nom => grun + "de" ;
    AF (Posit (Weak (AxSg Masc))) Gen => grun + "des" ;
    AF (Posit (Weak AxPl)) Nom => grun + "da" ;
    AF (Posit (Weak AxPl)) Gen => grun + "das" ;
    AF Compar Nom => grun + "dare" ;
    AF Compar Gen => grun + "dares" ;
    AF (Super SupStrong) Nom => grun + "dast" ;
    AF (Super SupStrong) Gen => grun + "dasts" ;
    AF (Super SupWeak) Nom => grun + "daste" ;
    AF (Super SupWeak) Gen => grun + "dastes"
    }
  } ;

oper aVid : Str -> Adj = \vi -> 
 {s = table {
    AF (Posit (Strong (ASg Utr))) Nom => vi + "d" ;
    AF (Posit (Strong (ASg Utr))) Gen => vi + "ds" ;
    AF (Posit (Strong (ASg Neutr))) Nom => vi + "tt" ;
    AF (Posit (Strong (ASg Neutr))) Gen => vi + "tts" ;
    AF (Posit (Strong APl)) Nom => vi + "da" ;
    AF (Posit (Strong APl)) Gen => vi + "das" ;
    AF (Posit (Weak (AxSg NoMasc))) Nom => vi + "da" ;
    AF (Posit (Weak (AxSg NoMasc))) Gen => vi + "das" ;
    AF (Posit (Weak (AxSg Masc))) Nom => vi + "de" ;
    AF (Posit (Weak (AxSg Masc))) Gen => vi + "des" ;
    AF (Posit (Weak AxPl)) Nom => vi + "da" ;
    AF (Posit (Weak AxPl)) Gen => vi + "das" ;
    AF Compar Nom => vi + "dare" ;
    AF Compar Gen => vi + "dares" ;
    AF (Super SupStrong) Nom => vi + "dast" ;
    AF (Super SupStrong) Gen => vi + "dasts" ;
    AF (Super SupWeak) Nom => vi + "daste" ;
    AF (Super SupWeak) Gen => vi + "dastes"
    }
  } ;

oper aVaken : Str -> Adj = \vak -> 
 {s = table {
    AF (Posit (Strong (ASg Utr))) Nom => vak + "en" ;
    AF (Posit (Strong (ASg Utr))) Gen => vak + "ens" ;
    AF (Posit (Strong (ASg Neutr))) Nom => vak + "et" ;
    AF (Posit (Strong (ASg Neutr))) Gen => vak + "ets" ;
    AF (Posit (Strong APl)) Nom => vak + "na" ;
    AF (Posit (Strong APl)) Gen => vak + "nas" ;
    AF (Posit (Weak (AxSg NoMasc))) Nom => vak + "na" ;
    AF (Posit (Weak (AxSg NoMasc))) Gen => vak + "nas" ;
    AF (Posit (Weak (AxSg Masc))) Nom => vak + "ne" ;
    AF (Posit (Weak (AxSg Masc))) Gen => vak + "nes" ;
    AF (Posit (Weak AxPl)) Nom => vak + "na" ;
    AF (Posit (Weak AxPl)) Gen => vak + "nas" ;
    AF Compar Nom => vak + "nare" ;
    AF Compar Gen => vak + "nares" ;
    AF (Super SupStrong) Nom => vak + "nast" ;
    AF (Super SupStrong) Gen => vak + "nasts" ;
    AF (Super SupWeak) Nom => vak + "naste" ;
    AF (Super SupWeak) Gen => vak + "nastes"
    }
  } ;

oper aKorkad : Str -> Adj = \korka -> 
 {s = table {
    AF (Posit (Strong (ASg Utr))) Nom => korka + "d" ;
    AF (Posit (Strong (ASg Utr))) Gen => korka + "ds" ;
    AF (Posit (Strong (ASg Neutr))) Nom => korka + "t" ;
    AF (Posit (Strong (ASg Neutr))) Gen => korka + "ts" ;
    AF (Posit (Strong APl)) Nom => korka + "de" ;
    AF (Posit (Strong APl)) Gen => korka + "des" ;
    AF (Posit (Weak (AxSg NoMasc))) Nom => korka + "de" ;
    AF (Posit (Weak (AxSg NoMasc))) Gen => korka + "des" ;
    AF (Posit (Weak (AxSg Masc))) Nom => korka + "de" ;
    AF (Posit (Weak (AxSg Masc))) Gen => korka + "des" ;
    AF (Posit (Weak AxPl)) Nom => korka + "de" ;
    AF (Posit (Weak AxPl)) Gen => korka + "des" ;
    AF Compar Nom => variants {} ;
    AF Compar Gen => variants {} ;
    AF (Super SupStrong) Nom => variants {} ;
    AF (Super SupStrong) Gen => variants {} ;
    AF (Super SupWeak) Nom => variants {} ;
    AF (Super SupWeak) Gen => variants {}
    }
  } ;

oper aAbstrakt : Str -> Adj = \abstrakt -> 
 {s = table {
    AF (Posit (Strong (ASg Utr))) Nom => abstrakt ;
    AF (Posit (Strong (ASg Utr))) Gen => abstrakt + "s" ;
    AF (Posit (Strong (ASg Neutr))) Nom => abstrakt ;
    AF (Posit (Strong (ASg Neutr))) Gen => abstrakt + "s" ;
    AF (Posit (Strong APl)) Nom => abstrakt + "a" ;
    AF (Posit (Strong APl)) Gen => abstrakt + "as" ;
    AF (Posit (Weak (AxSg NoMasc))) Nom => abstrakt + "a" ;
    AF (Posit (Weak (AxSg NoMasc))) Gen => abstrakt + "as" ;
    AF (Posit (Weak (AxSg Masc))) Nom => abstrakt + "e" ;
    AF (Posit (Weak (AxSg Masc))) Gen => abstrakt + "es" ;
    AF (Posit (Weak AxPl)) Nom => abstrakt + "a" ;
    AF (Posit (Weak AxPl)) Gen => abstrakt + "as" ;
    AF Compar Nom => abstrakt + "are" ;
    AF Compar Gen => abstrakt + "ares" ;
    AF (Super SupStrong) Nom => abstrakt + "ast" ;
    AF (Super SupStrong) Gen => abstrakt + "asts" ;
    AF (Super SupWeak) Nom => abstrakt + "aste" ;
    AF (Super SupWeak) Gen => abstrakt + "astes"
    }
  } ;

oper vTala : Str -> Verbum = \tal -> 
 {s = table {
    VF (Pres Ind Act) => tal + "ar" ;
    VF (Pres Ind Pass) => tal + "as" ;
    VF (Pres Cnj Act) => tal + "e" ;
    VF (Pres Cnj Pass) => tal + "es" ;
    VF (Pret Ind Act) => tal + "ade" ;
    VF (Pret Ind Pass) => tal + "ades" ;
    VF (Pret Cnj Act) => tal + "ade" ;
    VF (Pret Cnj Pass) => tal + "ades" ;
    VF Imper => tal + "a" ;
    VI (Inf Act) => tal + "a" ;
    VI (Inf Pass) => tal + "as" ;
    VI (Supin Act) => tal + "at" ;
    VI (Supin Pass) => tal + "ats" ;
    VI (PtPres Nom) => tal + "ande" ;
    VI (PtPres Gen) => tal + "andes" ;
    VI (PtPret (Strong (ASg Utr)) Nom) => tal + "ad" ;
    VI (PtPret (Strong (ASg Utr)) Gen) => tal + "ads" ;
    VI (PtPret (Strong (ASg Neutr)) Nom) => tal + "at" ;
    VI (PtPret (Strong (ASg Neutr)) Gen) => tal + "ats" ;
    VI (PtPret (Strong APl) Nom) => tal + "ade" ;
    VI (PtPret (Strong APl) Gen) => tal + "ades" ;
    VI (PtPret (Weak (AxSg NoMasc)) Nom) => tal + "ade" ;
    VI (PtPret (Weak (AxSg NoMasc)) Gen) => tal + "ades" ;
    VI (PtPret (Weak (AxSg Masc)) Nom) => tal + "ade" ;
    VI (PtPret (Weak (AxSg Masc)) Gen) => tal + "ades" ;
    VI (PtPret (Weak AxPl) Nom) => tal + "ade" ;
    VI (PtPret (Weak AxPl) Gen) => tal + "ades"
    }
  } ;

oper vLeka : Str -> Verbum = \lek -> 
 {s = table {
    VF (Pres Ind Act) => lek + "er" ;
    VF (Pres Ind Pass) => variants {lek + "s" ; lek + "es"} ;
    VF (Pres Cnj Act) => lek + "e" ;
    VF (Pres Cnj Pass) => lek + "es" ;
    VF (Pret Ind Act) => lek + "te" ;
    VF (Pret Ind Pass) => lek + "tes" ;
    VF (Pret Cnj Act) => lek + "te" ;
    VF (Pret Cnj Pass) => lek + "tes" ;
    VF Imper => lek ;
    VI (Inf Act) => lek + "a" ;
    VI (Inf Pass) => lek + "as" ;
    VI (Supin Act) => lek + "t" ;
    VI (Supin Pass) => lek + "ts" ;
    VI (PtPres Nom) => lek + "ande" ;
    VI (PtPres Gen) => lek + "andes" ;
    VI (PtPret (Strong (ASg Utr)) Nom) => lek + "t" ;
    VI (PtPret (Strong (ASg Utr)) Gen) => lek + "ts" ;
    VI (PtPret (Strong (ASg Neutr)) Nom) => lek + "t" ;
    VI (PtPret (Strong (ASg Neutr)) Gen) => lek + "ts" ;
    VI (PtPret (Strong APl) Nom) => lek + "ta" ;
    VI (PtPret (Strong APl) Gen) => lek + "tas" ;
    VI (PtPret (Weak (AxSg NoMasc)) Nom) => lek + "ta" ;
    VI (PtPret (Weak (AxSg NoMasc)) Gen) => lek + "tas" ;
    VI (PtPret (Weak (AxSg Masc)) Nom) => lek + "te" ;
    VI (PtPret (Weak (AxSg Masc)) Gen) => lek + "tes" ;
    VI (PtPret (Weak AxPl) Nom) => lek + "ta" ;
    VI (PtPret (Weak AxPl) Gen) => lek + "tas"
    }
  } ;

oper vTyda : Str -> Verbum = \ty -> 
 {s = table {
    VF (Pres Ind Act) => ty + "der" ;
    VF (Pres Ind Pass) => variants {ty + "ds" ; ty + "des"} ;
    VF (Pres Cnj Act) => ty + "de" ;
    VF (Pres Cnj Pass) => ty + "des" ;
    VF (Pret Ind Act) => ty + "dde" ;
    VF (Pret Ind Pass) => ty + "ddes" ;
    VF (Pret Cnj Act) => ty + "dde" ;
    VF (Pret Cnj Pass) => ty + "ddes" ;
    VF Imper => ty + "d" ;
    VI (Inf Act) => ty + "da" ;
    VI (Inf Pass) => ty + "das" ;
    VI (Supin Act) => ty + "tt" ;
    VI (Supin Pass) => ty + "tts" ;
    VI (PtPres Nom) => ty + "dande" ;
    VI (PtPres Gen) => ty + "dandes" ;
    VI (PtPret (Strong (ASg Utr)) Nom) => ty + "dd" ;
    VI (PtPret (Strong (ASg Utr)) Gen) => ty + "dds" ;
    VI (PtPret (Strong (ASg Neutr)) Nom) => ty + "tt" ;
    VI (PtPret (Strong (ASg Neutr)) Gen) => ty + "tts" ;
    VI (PtPret (Strong APl) Nom) => ty + "dda" ;
    VI (PtPret (Strong APl) Gen) => ty + "ddas" ;
    VI (PtPret (Weak (AxSg NoMasc)) Nom) => ty + "dda" ;
    VI (PtPret (Weak (AxSg NoMasc)) Gen) => ty + "ddas" ;
    VI (PtPret (Weak (AxSg Masc)) Nom) => ty + "dde" ;
    VI (PtPret (Weak (AxSg Masc)) Gen) => ty + "ddes" ;
    VI (PtPret (Weak AxPl) Nom) => ty + "dda" ;
    VI (PtPret (Weak AxPl) Gen) => ty + "ddas"
    }
  } ;

oper vV�nda : Str -> Verbum = \v�n -> 
 {s = table {
    VF (Pres Ind Act) => v�n + "der" ;
    VF (Pres Ind Pass) => variants {v�n + "ds" ; v�n + "des"} ;
    VF (Pres Cnj Act) => v�n + "de" ;
    VF (Pres Cnj Pass) => v�n + "des" ;
    VF (Pret Ind Act) => v�n + "de" ;
    VF (Pret Ind Pass) => v�n + "des" ;
    VF (Pret Cnj Act) => v�n + "de" ;
    VF (Pret Cnj Pass) => v�n + "des" ;
    VF Imper => v�n + "d" ;
    VI (Inf Act) => v�n + "da" ;
    VI (Inf Pass) => v�n + "das" ;
    VI (Supin Act) => v�n + "t" ;
    VI (Supin Pass) => v�n + "ts" ;
    VI (PtPres Nom) => v�n + "dande" ;
    VI (PtPres Gen) => v�n + "dandes" ;
    VI (PtPret (Strong (ASg Utr)) Nom) => v�n + "d" ;
    VI (PtPret (Strong (ASg Utr)) Gen) => v�n + "ds" ;
    VI (PtPret (Strong (ASg Neutr)) Nom) => v�n + "t" ;
    VI (PtPret (Strong (ASg Neutr)) Gen) => v�n + "ts" ;
    VI (PtPret (Strong APl) Nom) => v�n + "da" ;
    VI (PtPret (Strong APl) Gen) => v�n + "das" ;
    VI (PtPret (Weak (AxSg NoMasc)) Nom) => v�n + "da" ;
    VI (PtPret (Weak (AxSg NoMasc)) Gen) => v�n + "das" ;
    VI (PtPret (Weak (AxSg Masc)) Nom) => v�n + "de" ;
    VI (PtPret (Weak (AxSg Masc)) Gen) => v�n + "des" ;
    VI (PtPret (Weak AxPl) Nom) => v�n + "da" ;
    VI (PtPret (Weak AxPl) Gen) => v�n + "das"
    }
  } ;

oper vByta : Str -> Verbum = \by -> 
 {s = table {
    VF (Pres Ind Act) => by + "ter" ;
    VF (Pres Ind Pass) => variants {by + "ts" ; by + "tes"} ;
    VF (Pres Cnj Act) => by + "te" ;
    VF (Pres Cnj Pass) => by + "tes" ;
    VF (Pret Ind Act) => by + "tte" ;
    VF (Pret Ind Pass) => by + "ttes" ;
    VF (Pret Cnj Act) => by + "tte" ;
    VF (Pret Cnj Pass) => by + "ttes" ;
    VF Imper => by + "t" ;
    VI (Inf Act) => by + "ta" ;
    VI (Inf Pass) => by + "tas" ;
    VI (Supin Act) => by + "tt" ;
    VI (Supin Pass) => by + "tts" ;
    VI (PtPres Nom) => by + "tande" ;
    VI (PtPres Gen) => by + "tandes" ;
    VI (PtPret (Strong (ASg Utr)) Nom) => by + "tt" ;
    VI (PtPret (Strong (ASg Utr)) Gen) => by + "tts" ;
    VI (PtPret (Strong (ASg Neutr)) Nom) => by + "tt" ;
    VI (PtPret (Strong (ASg Neutr)) Gen) => by + "tts" ;
    VI (PtPret (Strong APl) Nom) => by + "tta" ;
    VI (PtPret (Strong APl) Gen) => by + "ttas" ;
    VI (PtPret (Weak (AxSg NoMasc)) Nom) => by + "tta" ;
    VI (PtPret (Weak (AxSg NoMasc)) Gen) => by + "ttas" ;
    VI (PtPret (Weak (AxSg Masc)) Nom) => by + "tte" ;
    VI (PtPret (Weak (AxSg Masc)) Gen) => by + "ttes" ;
    VI (PtPret (Weak AxPl) Nom) => by + "tta" ;
    VI (PtPret (Weak AxPl) Gen) => by + "ttas"
    }
  } ;

oper vG�mma : Str -> Verbum = \g�m -> 
 {s = table {
    VF (Pres Ind Act) => g�m + "mer" ;
    VF (Pres Ind Pass) => variants {g�m + "s" ; g�m + "mes"} ;
    VF (Pres Cnj Act) => g�m + "me" ;
    VF (Pres Cnj Pass) => g�m + "mes" ;
    VF (Pret Ind Act) => g�m + "de" ;
    VF (Pret Ind Pass) => g�m + "des" ;
    VF (Pret Cnj Act) => g�m + "de" ;
    VF (Pret Cnj Pass) => g�m + "des" ;
    VF Imper => g�m ;
    VI (Inf Act) => g�m + "ma" ;
    VI (Inf Pass) => g�m + "mas" ;
    VI (Supin Act) => g�m + "t" ;
    VI (Supin Pass) => g�m + "ts" ;
    VI (PtPres Nom) => g�m + "mande" ;
    VI (PtPres Gen) => g�m + "mandes" ;
    VI (PtPret (Strong (ASg Utr)) Nom) => g�m + "d" ;
    VI (PtPret (Strong (ASg Utr)) Gen) => g�m + "ds" ;
    VI (PtPret (Strong (ASg Neutr)) Nom) => g�m + "t" ;
    VI (PtPret (Strong (ASg Neutr)) Gen) => g�m + "ts" ;
    VI (PtPret (Strong APl) Nom) => g�m + "da" ;
    VI (PtPret (Strong APl) Gen) => g�m + "das" ;
    VI (PtPret (Weak (AxSg NoMasc)) Nom) => g�m + "da" ;
    VI (PtPret (Weak (AxSg NoMasc)) Gen) => g�m + "das" ;
    VI (PtPret (Weak (AxSg Masc)) Nom) => g�m + "de" ;
    VI (PtPret (Weak (AxSg Masc)) Gen) => g�m + "des" ;
    VI (PtPret (Weak AxPl) Nom) => g�m + "da" ;
    VI (PtPret (Weak AxPl) Gen) => g�m + "das"
    }
  } ;

oper vHyra : Str -> Verbum = \hyr -> 
 {s = table {
    VF (Pres Ind Act) => hyr ;
    VF (Pres Ind Pass) => variants {hyr + "s" ; hyr + "es"} ;
    VF (Pres Cnj Act) => hyr + "e" ;
    VF (Pres Cnj Pass) => hyr + "es" ;
    VF (Pret Ind Act) => hyr + "de" ;
    VF (Pret Ind Pass) => hyr + "des" ;
    VF (Pret Cnj Act) => hyr + "de" ;
    VF (Pret Cnj Pass) => hyr + "des" ;
    VF Imper => hyr ;
    VI (Inf Act) => hyr + "a" ;
    VI (Inf Pass) => hyr + "as" ;
    VI (Supin Act) => hyr + "t" ;
    VI (Supin Pass) => hyr + "ts" ;
    VI (PtPres Nom) => hyr + "ande" ;
    VI (PtPres Gen) => hyr + "andes" ;
    VI (PtPret (Strong (ASg Utr)) Nom) => hyr + "d" ;
    VI (PtPret (Strong (ASg Utr)) Gen) => hyr + "ds" ;
    VI (PtPret (Strong (ASg Neutr)) Nom) => hyr + "t" ;
    VI (PtPret (Strong (ASg Neutr)) Gen) => hyr + "ts" ;
    VI (PtPret (Strong APl) Nom) => hyr + "da" ;
    VI (PtPret (Strong APl) Gen) => hyr + "das" ;
    VI (PtPret (Weak (AxSg NoMasc)) Nom) => hyr + "da" ;
    VI (PtPret (Weak (AxSg NoMasc)) Gen) => hyr + "das" ;
    VI (PtPret (Weak (AxSg Masc)) Nom) => hyr + "de" ;
    VI (PtPret (Weak (AxSg Masc)) Gen) => hyr + "des" ;
    VI (PtPret (Weak AxPl) Nom) => hyr + "da" ;
    VI (PtPret (Weak AxPl) Gen) => hyr + "das"
    }
  } ;

oper vT�la : Str -> Verbum = \t�l -> 
 {s = table {
    VF (Pres Ind Act) => t�l ;
    VF (Pres Ind Pass) => variants {t�l + "s" ; t�l + "es"} ;
    VF (Pres Cnj Act) => t�l + "e" ;
    VF (Pres Cnj Pass) => t�l + "es" ;
    VF (Pret Ind Act) => t�l + "de" ;
    VF (Pret Ind Pass) => t�l + "des" ;
    VF (Pret Cnj Act) => t�l + "de" ;
    VF (Pret Cnj Pass) => t�l + "des" ;
    VF Imper => t�l ;
    VI (Inf Act) => t�l + "a" ;
    VI (Inf Pass) => t�l + "as" ;
    VI (Supin Act) => t�l + "t" ;
    VI (Supin Pass) => t�l + "ts" ;
    VI (PtPres Nom) => t�l + "ande" ;
    VI (PtPres Gen) => t�l + "andes" ;
    VI (PtPret (Strong (ASg Utr)) Nom) => t�l + "d" ;
    VI (PtPret (Strong (ASg Utr)) Gen) => t�l + "ds" ;
    VI (PtPret (Strong (ASg Neutr)) Nom) => t�l + "t" ;
    VI (PtPret (Strong (ASg Neutr)) Gen) => t�l + "ts" ;
    VI (PtPret (Strong APl) Nom) => t�l + "da" ;
    VI (PtPret (Strong APl) Gen) => t�l + "das" ;
    VI (PtPret (Weak (AxSg NoMasc)) Nom) => t�l + "da" ;
    VI (PtPret (Weak (AxSg NoMasc)) Gen) => t�l + "das" ;
    VI (PtPret (Weak (AxSg Masc)) Nom) => t�l + "de" ;
    VI (PtPret (Weak (AxSg Masc)) Gen) => t�l + "des" ;
    VI (PtPret (Weak AxPl) Nom) => t�l + "da" ;
    VI (PtPret (Weak AxPl) Gen) => t�l + "das"
    }
  } ;

oper vFinna : (_,_,_ : Str) -> Verbum = \finn, fann, funn -> 
 {s = table {
    VF (Pres Ind Act) => finn + "er" ;
    VF (Pres Ind Pass) => variants {finn + "s" ; finn + "es"} ;
    VF (Pres Cnj Act) => finn + "e" ;
    VF (Pres Cnj Pass) => finn + "es" ;
    VF (Pret Ind Act) => fann ;
    VF (Pret Ind Pass) => fann + "s" ;
    VF (Pret Cnj Act) => funn + "e" ;
    VF (Pret Cnj Pass) => funn + "es" ;
    VF Imper => finn ;
    VI (Inf Act) => finn + "a" ;
    VI (Inf Pass) => finn + "as" ;
    VI (Supin Act) => funn + "it" ;
    VI (Supin Pass) => funn + "its" ;
    VI (PtPres Nom) => finn + "ande" ;
    VI (PtPres Gen) => finn + "andes" ;
    VI (PtPret (Strong (ASg Utr)) Nom) => funn + "en" ;
    VI (PtPret (Strong (ASg Utr)) Gen) => funn + "ens" ;
    VI (PtPret (Strong (ASg Neutr)) Nom) => funn + "et" ;
    VI (PtPret (Strong (ASg Neutr)) Gen) => funn + "ets" ;
    VI (PtPret (Strong APl) Nom) => funn + "a" ;
    VI (PtPret (Strong APl) Gen) => funn + "as" ;
    VI (PtPret (Weak (AxSg NoMasc)) Nom) => funn + "a" ;
    VI (PtPret (Weak (AxSg NoMasc)) Gen) => funn + "as" ;
    VI (PtPret (Weak (AxSg Masc)) Nom) => funn + "e" ;
    VI (PtPret (Weak (AxSg Masc)) Gen) => funn + "es" ;
    VI (PtPret (Weak AxPl) Nom) => funn + "a" ;
    VI (PtPret (Weak AxPl) Gen) => funn + "as"
    }
  } ;

-- machine-generated exceptional inflection tables from rules.Swe.gf

oper mor_1 : Subst = 
 {s = table {
    SF Sg Indef Nom => variants {"mor" ; "moder"} ;
    SF Sg Indef Gen => variants {"mors" ; "moders"} ;
    SF Sg Def Nom => "modern" ;
    SF Sg Def Gen => "moderns" ;
    SF Pl Indef Nom => "m�drar" ;
    SF Pl Indef Gen => "m�drars" ;
    SF Pl Def Nom => "m�drarna" ;
    SF Pl Def Gen => "m�drarnas"
    } ;
  h1 = Utr
  } ;

oper farbror_8 : Subst = 
 {s = table {
    SF Sg Indef Nom => variants {"farbror" ; "farbroder"} ;
    SF Sg Indef Gen => variants {"farbrors" ; "farbroders"} ;
    SF Sg Def Nom => "farbrodern" ;
    SF Sg Def Gen => "farbroderns" ;
    SF Pl Indef Nom => "farbr�der" ;
    SF Pl Indef Gen => "farbr�ders" ;
    SF Pl Def Nom => "farbr�derna" ;
    SF Pl Def Gen => "farbr�dernas"
    } ;
  h1 = Utr
  } ;

oper gammal_16 : Adj = 
 {s = table {
    AF (Posit (Strong (ASg Utr))) Nom => "gammal" ;
    AF (Posit (Strong (ASg Utr))) Gen => "gammals" ;
    AF (Posit (Strong (ASg Neutr))) Nom => "gammalt" ;
    AF (Posit (Strong (ASg Neutr))) Gen => "gammalts" ;
    AF (Posit (Strong APl)) Nom => "gamla" ;
    AF (Posit (Strong APl)) Gen => "gamlas" ;
    AF (Posit (Weak (AxSg NoMasc))) Nom => "gamla" ;
    AF (Posit (Weak (AxSg NoMasc))) Gen => "gamlas" ;
    AF (Posit (Weak (AxSg Masc))) Nom => "gamle" ;
    AF (Posit (Weak (AxSg Masc))) Gen => "gamles" ;
    AF (Posit (Weak AxPl)) Nom => "gamla" ;
    AF (Posit (Weak AxPl)) Gen => "gamlas" ;
    AF Compar Nom => "�ldre" ;
    AF Compar Gen => "�ldres" ;
    AF (Super SupStrong) Nom => "�ldst" ;
    AF (Super SupStrong) Gen => "�ldsts" ;
    AF (Super SupWeak) Nom => "�ldsta" ;
    AF (Super SupWeak) Gen => "�ldstas"
    }
  } ;


oper stor_25 : Adj = 
 {s = table {
    AF (Posit (Strong (ASg Utr))) Nom => "stor" ;
    AF (Posit (Strong (ASg Utr))) Gen => "stors" ;
    AF (Posit (Strong (ASg Neutr))) Nom => "stort" ;
    AF (Posit (Strong (ASg Neutr))) Gen => "storts" ;
    AF (Posit (Strong APl)) Nom => "stora" ;
    AF (Posit (Strong APl)) Gen => "storas" ;
    AF (Posit (Weak (AxSg NoMasc))) Nom => "stora" ;
    AF (Posit (Weak (AxSg NoMasc))) Gen => "storas" ;
    AF (Posit (Weak (AxSg Masc))) Nom => "store" ;
    AF (Posit (Weak (AxSg Masc))) Gen => "stores" ;
    AF (Posit (Weak AxPl)) Nom => "stora" ;
    AF (Posit (Weak AxPl)) Gen => "storas" ;
    AF Compar Nom => "st�rre" ;
    AF Compar Gen => "st�rres" ;
    AF (Super SupStrong) Nom => "st�rst" ;
    AF (Super SupStrong) Gen => "st�rsts" ;
    AF (Super SupWeak) Nom => "st�rsta" ;
    AF (Super SupWeak) Gen => "st�rstas"
    }
  } ;

oper ung_29 : Adj = 
 {s = table {
    AF (Posit (Strong (ASg Utr))) Nom => "ung" ;
    AF (Posit (Strong (ASg Utr))) Gen => "ungs" ;
    AF (Posit (Strong (ASg Neutr))) Nom => "ungt" ;
    AF (Posit (Strong (ASg Neutr))) Gen => "ungts" ;
    AF (Posit (Strong APl)) Nom => "unga" ;
    AF (Posit (Strong APl)) Gen => "ungas" ;
    AF (Posit (Weak (AxSg NoMasc))) Nom => "unga" ;
    AF (Posit (Weak (AxSg NoMasc))) Gen => "ungas" ;
    AF (Posit (Weak (AxSg Masc))) Nom => "unge" ;
    AF (Posit (Weak (AxSg Masc))) Gen => "unges" ;
    AF (Posit (Weak AxPl)) Nom => "unga" ;
    AF (Posit (Weak AxPl)) Gen => "ungas" ;
    AF Compar Nom => "yngre" ;
    AF Compar Gen => "yngres" ;
    AF (Super SupStrong) Nom => "yngst" ;
    AF (Super SupStrong) Gen => "yngsts" ;
    AF (Super SupWeak) Nom => "yngsta" ;
    AF (Super SupWeak) Gen => "yngstas"
    }
  } ;


oper jag_32 : ProPN = 
 {s = table {
    PNom => "jag" ;
    PAcc => "mig" ;
    PGen (ASg Utr) => "min" ;
    PGen (ASg Neutr) => "mitt" ;
    PGen APl => "mina"
    } ;
  h1 = Utr ;
  h2 = Sg ;
  h3 = P1
  } ;

oper du_33 : ProPN = 
 {s = table {
    PNom => "du" ;
    PAcc => "dig" ;
    PGen (ASg Utr) => "din" ;
    PGen (ASg Neutr) => "ditt" ;
    PGen APl => "dina"
    } ;
  h1 = Utr ;
  h2 = Sg ;
  h3 = P2
  } ;

oper han_34 : ProPN = 
 {s = table {
    PNom => "han" ;
    PAcc => "honom" ;
    PGen (ASg Utr) => "hans" ;
    PGen (ASg Neutr) => "hans" ;
    PGen APl => "hans"
    } ;
  h1 = Utr ;
  h2 = Sg ;
  h3 = P3
  } ;

oper hon_35 : ProPN = 
 {s = table {
    PNom => "hon" ;
    PAcc => "henne" ;
    PGen (ASg Utr) => "hennes" ;
    PGen (ASg Neutr) => "hennes" ;
    PGen APl => "hennes"
    } ;
  h1 = Utr ;
  h2 = Sg ;
  h3 = P3
  } ;

oper vi_36 : ProPN = 
 {s = table {
    PNom => "vi" ;
    PAcc => "oss" ;
    PGen (ASg Utr) => "v�r" ;
    PGen (ASg Neutr) => "v�rt" ;
    PGen APl => "v�ra"
    } ;
  h1 = Utr ;
  h2 = Pl ;
  h3 = P1
  } ;

oper ni_37 : ProPN = 
 {s = table {
    PNom => "ni" ;
    PAcc => "er" ;
    PGen (ASg Utr) => "er" ;
    PGen (ASg Neutr) => "ert" ;
    PGen APl => "era"
    } ;
  h1 = Utr ;
  h2 = Pl ;
  h3 = P2
  } ;

oper de_38 : ProPN = 
 {s = table {
    PNom => "de" ;
    PAcc => "dem" ;
    PGen (ASg Utr) => "deras" ;
    PGen (ASg Neutr) => "deras" ;
    PGen APl => "deras"
    } ;
  h1 = Utr ;
  h2 = Pl ;
  h3 = P3
  } ;

oper den_39 : ProPN = 
 {s = table {
    PNom => "den" ;
    PAcc => "den" ;
    PGen (ASg Utr) => "dess" ;
    PGen (ASg Neutr) => "dess" ;
    PGen APl => "dess"
    } ;
  h1 = Utr ;
  h2 = Sg ;
  h3 = P3
  } ;

oper det_40 : ProPN = 
 {s = table {
    PNom => "det" ;
    PAcc => "det" ;
    PGen (ASg Utr) => "dess" ;
    PGen (ASg Neutr) => "dess" ;
    PGen APl => "dess"
    } ;
  h1 = Neutr ;
  h2 = Sg ;
  h3 = P3
  } ;

oper man_1144 : Subst = 
 {s = table {
    SF Sg Indef Nom => "man" ;
    SF Sg Indef Gen => "mans" ;
    SF Sg Def Nom => "mannen" ;
    SF Sg Def Gen => "mannens" ;
    SF Pl Indef Nom => "m�n" ;
    SF Pl Indef Gen => "m�ns" ;
    SF Pl Def Nom => "m�nnen" ;
    SF Pl Def Gen => "m�nnens" 
    } ;
  h1 = Utr
  } ;

oper liten_1146 : Adj = 
 {s = table {
    AF (Posit (Strong (ASg Utr))) Nom => "liten" ;
    AF (Posit (Strong (ASg Utr))) Gen => "litens" ;
    AF (Posit (Strong (ASg Neutr))) Nom => "litet" ;
    AF (Posit (Strong (ASg Neutr))) Gen => "litets" ;
    AF (Posit (Strong APl)) Nom => "sm�" ;
    AF (Posit (Strong APl)) Gen => "sm�s" ;
    AF (Posit (Weak (AxSg NoMasc))) Nom => "lilla" ;
    AF (Posit (Weak (AxSg NoMasc))) Gen => "lillas" ;
    AF (Posit (Weak (AxSg Masc))) Nom => "lille" ;
    AF (Posit (Weak (AxSg Masc))) Gen => "lilles" ;
    AF (Posit (Weak AxPl)) Nom => "sm�" ;
    AF (Posit (Weak AxPl)) Gen => "sm�s" ;
    AF Compar Nom => "mindre" ;
    AF Compar Gen => "mindres" ;
    AF (Super SupStrong) Nom => "minst" ;
    AF (Super SupStrong) Gen => "minsts" ;
    AF (Super SupWeak) Nom => "minsta" ;
    AF (Super SupWeak) Gen => "minstas"
    }
  } ;

oper giva_1147 : Verbum = 
 {s = table {
    VF (Pres Ind Act) => variants {"giver" ; "ger"} ;
    VF (Pres Ind Pass) => variants {"gives" ; "givs" ; "ges"} ;
    VF (Pres Conj Act) => "give" ;
    VF (Pres Conj Pass) => "gives" ;
    VF (Pret Ind Act) => "gav" ;
    VF (Pret Ind Pass) => "gavs" ;
    VF (Pret Conj Act) => "give" ;
    VF (Pret Conj Pass) => "gives" ;
    VF Imper => variants {"giv" ; "ge"} ;
    VI (Inf Act) => variants {"giva" ; "ge"} ;
    VI (Inf Pass) => variants {"givas" ; "ges"} ;
    VI (Supin Act) => "givit" ;
    VI (Supin Pass) => "givits" ;
    VI (PtPres Nom) => "givande" ;
    VI (PtPres Gen) => "givandes" ;
    VI (PtPret (Strong (ASg Utr)) Nom) => "given" ;
    VI (PtPret (Strong (ASg Utr)) Gen) => "givens" ;
    VI (PtPret (Strong (ASg Neutr)) Nom) => "givet" ;
    VI (PtPret (Strong (ASg Neutr)) Gen) => "givets" ;
    VI (PtPret (Strong APl) Nom) => "givna" ;
    VI (PtPret (Strong APl) Gen) => "givnas" ;
    VI (PtPret (Weak (AxSg NoMasc)) Nom) => "givna" ;
    VI (PtPret (Weak (AxSg NoMasc)) Gen) => "givnas" ;
    VI (PtPret (Weak (AxSg Masc)) Nom) => "givne" ;
    VI (PtPret (Weak (AxSg Masc)) Gen) => "givnes" ;
    VI (PtPret (Weak AxPl) Nom) => "givna" ;
    VI (PtPret (Weak AxPl) Gen) => "givnas"
    }
  } ;

oper g�_1174 : Verbum = 
 {s = table {
    VF (Pres Ind Act) => "g�r" ;
    VF (Pres Ind Pass) => "g�s" ;
    VF (Pres Cnj Act) => "g�" ;
    VF (Pres Cnj Pass) => "g�s" ;
    VF (Pret Ind Act) => "gick" ;
    VF (Pret Ind Pass) => "gicks" ;
    VF (Pret Cnj Act) => "ginge" ;
    VF (Pret Cnj Pass) => "ginges" ;
    VF Imper => "g�" ;
    VI (Inf Act) => "g�" ;
    VI (Inf Pass) => "g�s" ;
    VI (Supin Act) => "g�tt" ;
    VI (Supin Pass) => "g�tts" ;
    VI (PtPres Nom) => "g�ende" ;
    VI (PtPres Gen) => "g�endes" ;
    VI (PtPret (Strong (ASg Utr)) Nom) => "g�ngen" ;
    VI (PtPret (Strong (ASg Utr)) Gen) => "g�ngens" ;
    VI (PtPret (Strong (ASg Neutr)) Nom) => "g�nget" ;
    VI (PtPret (Strong (ASg Neutr)) Gen) => "g�ngets" ;
    VI (PtPret (Strong APl) Nom) => "g�ngna" ;
    VI (PtPret (Strong APl) Gen) => "g�ngnas" ;
    VI (PtPret (Weak (AxSg NoMasc)) Nom) => "g�ngna" ;
    VI (PtPret (Weak (AxSg NoMasc)) Gen) => "g�ngnas" ;
    VI (PtPret (Weak (AxSg Masc)) Nom) => "g�ngne" ;
    VI (PtPret (Weak (AxSg Masc)) Gen) => "g�ngnes" ;
    VI (PtPret (Weak AxPl) Nom) => "g�ngna" ;
    VI (PtPret (Weak AxPl) Gen) => "g�ngnas"
    }
  } ;
oper hava_1198 : Verbum = 
 {s = table {
    VF (Pres Ind Act) => variants {"haver" ; "har"} ;
    VF (Pres Ind Pass) => variants {"havs" ; "has"} ;
    VF (Pres Conj Act) => "have" ;
    VF (Pres Conj Pass) => "haves" ;
    VF (Pret Ind Act) => "hade" ;
    VF (Pret Ind Pass) => "hades" ;
    VF (Pret Conj Act) => "hade" ;
    VF (Pret Conj Pass) => "hades" ;
    VF Imper => variants {"hav" ; "ha"} ;
    VI (Inf Act) => variants {"hava" ; "ha"} ;
    VI (Inf Pass) => variants {"havas" ; "has"} ;
    VI (Supin Act) => "haft" ;
    VI (Supin Pass) => "hafts" ;
    VI (PtPres Nom) => "havande" ;
    VI (PtPres Gen) => "havandes" ;
    VI (PtPret (Strong (ASg Utr)) Nom) => variants {} ;
    VI (PtPret (Strong (ASg Utr)) Gen) => variants {} ;
    VI (PtPret (Strong (ASg Neutr)) Nom) => variants {} ;
    VI (PtPret (Strong (ASg Neutr)) Gen) => variants {} ;
    VI (PtPret (Strong APl) Nom) => variants {} ;
    VI (PtPret (Strong APl) Gen) => variants {} ;
    VI (PtPret (Weak (AxSg NoMasc)) Nom) => variants {} ;
    VI (PtPret (Weak (AxSg NoMasc)) Gen) => variants {} ;
    VI (PtPret (Weak (AxSg Masc)) Nom) => variants {} ;
    VI (PtPret (Weak (AxSg Masc)) Gen) => variants {} ;
    VI (PtPret (Weak AxPl) Nom) => variants {} ;
    VI (PtPret (Weak AxPl) Gen) => variants {}
    }
  } ;

oper vara_1200 : Verbum = 
 {s = table {
    VF (Pres Ind Act) => "�r" ;
    VF (Pres Ind Pass) => variants {} ;
    VF (Pres Conj Act) => "vare" ;
    VF (Pres Conj Pass) => variants {} ;
    VF (Pret Ind Act) => "var" ;
    VF (Pret Ind Pass) => variants {} ;
    VF (Pret Conj Act) => "vore" ;
    VF (Pret Conj Pass) => variants {} ;
    VF Imper => "var" ;
    VI (Inf Act) => "vara" ;
    VI (Inf Pass) => variants {} ;
    VI (Supin Act) => "varit" ;
    VI (Supin Pass) => variants {} ;
    VI (PtPres Nom) => "varande" ;
    VI (PtPres Gen) => "varandes" ;
    VI (PtPret (Strong (ASg Utr)) Nom) => variants {} ;
    VI (PtPret (Strong (ASg Utr)) Gen) => variants {} ;
    VI (PtPret (Strong (ASg Neutr)) Nom) => variants {} ;
    VI (PtPret (Strong (ASg Neutr)) Gen) => variants {} ;
    VI (PtPret (Strong APl) Nom) => variants {} ;
    VI (PtPret (Strong APl) Gen) => variants {} ;
    VI (PtPret (Weak (AxSg NoMasc)) Nom) => variants {} ;
    VI (PtPret (Weak (AxSg NoMasc)) Gen) => variants {} ;
    VI (PtPret (Weak (AxSg Masc)) Nom) => variants {} ;
    VI (PtPret (Weak (AxSg Masc)) Gen) => variants {} ;
    VI (PtPret (Weak AxPl) Nom) => variants {} ;
    VI (PtPret (Weak AxPl) Gen) => variants {}
    }
  } ;

-- for Numerals

param DForm = ental  | ton  | tiotal  ;

oper 
  LinDigit = {s : DForm => Str} ;

  mkTal : Str -> Str -> Str -> LinDigit = \tv�, tolv, tjugo -> 
    {s = table {ental => tv� ; ton => tolv ; tiotal => tjugo}} ;

  regTal : Str -> LinDigit = \fem -> 
    mkTal fem (fem + "ton") (fem + "tio") ;



}
