--# -path=.:../romance:../../prelude

--1 A Simple Spanish Resource Morphology
--
-- Aarne Ranta 2002--2003
--
-- This resource morphology contains definitions needed in the resource
-- syntax. It moreover contains the most usual inflectional patterns.
-- The patterns for verbs contain the complete "Bescherelle" conjugation
-- tables.
--
-- We use the parameter types and word classes defined in $TypesSpa.gf$.

resource MorphoSpa = open (Predef=Predef), Prelude, TypesSpa in {

--2 Some phonology
--
--3 Elision
--
-- The phonological rule of *elision* can be defined as follows in GF.
-- In Italian it includes both vowels and the *impure 's'*.

oper 
  vocale : Strs = strs {
    "a" ; "e" ; "h" ; "i" ; "o" ; "u"
    } ;

  elisQue = "que" ; --- no elision in Italian
  elisDe = "de" ;

--2 Nouns
--
-- The following macro is useful for creating the forms of number-dependent
-- tables, such as common nouns.

  numForms : (_,_ : Str) -> Number => Str = \vino, vini ->
    table {Sg => vino ; Pl => vini} ; 

-- For example:

  nomVino : Str -> Number => Str = \vino -> 
    numForms vino (vino + "s") ;

  nomPilar : Str -> Number => Str = \pilar -> 
    numForms pilar (pilar + "es") ;

  nomTram : Str -> Number => Str = \tram ->
    numForms tram tram ;

-- Common nouns are inflected in number and have an inherent gender.

  mkCNom : (Number => Str) -> Gender -> CNom = \mecmecs,gen -> 
    {s = mecmecs ; g = gen} ;

  mkCNomIrreg : Str -> Str -> Gender -> CNom = \mec,mecs -> 
    mkCNom (numForms mec mecs) ;



--2 Adjectives
--
-- Adjectives are conveniently seen as gender-dependent nouns.
-- Here are some patterns. First one that describes the worst case.

  mkAdj : (_,_,_,_,_ : Str) -> Adj = \solo,sola,soli,sole,solamente ->
    {s = table {
       AF Masc n => numForms solo soli ! n ;
       AF Fem  n => numForms sola sole ! n ;
       AA        => solamente
       }
    } ;

-- Then the regular and invariant patterns.

  adjSolo : Str -> Adj = \solo -> 
    let 
      sol = Predef.tk 1 solo
    in
    mkAdj solo (sol + "a") (sol + "os") (sol + "as") (sol + "amente") ;

  adjUtil : Str -> Str -> Adj = \util,utiles -> 
    mkAdj util util utiles utiles (util + "mente") ;

  adjBlu : Str -> Adj = \blu -> 
    mkAdj blu blu blu blu blu ; --- 


--2 Personal pronouns
--
-- All the eight personal pronouns can be built by the following macro.
-- The use of "ne" as atonic genitive is debatable.
-- We follow the rule that the atonic nominative is empty.

  mkPronoun : (_,_,_,_,_,_,_,_ : Str) -> 
              PronGen -> Number -> Person -> ClitType -> Pronoun =
    \il,le,lui,Lui,son,sa,ses,see,g,n,p,c ->
    {s = table {
       Ton Nom => il ;
       Ton x => prepCase x ++ Lui ;
       Aton Nom => il ; ---- [] ;
       Aton Acc => le ;
----       Aton (CPrep P_de) => "ne" ; --- hmm
       Aton (CPrep P_a) => lui ;
       Aton (CPrep q) => strPrep q ++ Lui ; ---- GF bug with c or p! 
       Poss Sg Masc => son ;
       Poss Sg Fem  => sa ;
       Poss Pl Masc => ses ;
       Poss Pl Fem  => see
       } ;
     g = g ;
     n = n ;
     p = p ;
     c = c
    } ;


--2 Reflexive pronouns
--
-- It is simply a function depending on number and person.

  pronRefl : Number -> Person -> Str = \n,p -> case <n,p> of {
    <Sg,P1> => "me" ;
    <Sg,P2> => "te" ;
    <_, P3> => "se" ;
    <Pl,P1> => "nos" ;
    <Pl,P2> => "vos"
    } ;


--2 Determiners
--
-- Determiners, traditionally called indefinite pronouns, are inflected
-- in gender and number, like adjectives.

  pronForms : Adj -> Gender -> Number -> Str = \tale,g,n -> tale.s ! AF g n ;

  qualPron : Gender -> Number -> Str = pronForms (adjUtil "cu�l" "cuales") ;

  talPron : Gender -> Number -> Str = pronForms (adjUtil "t�l" "tales") ;

  tuttoPron : Gender -> Number -> Str = pronForms (adjSolo "todo") ;

--2 Articles
--
-- The definite article has quite some variation: three parameters and
-- elision. This is the simples definition we have been able to find.

  artDefTable : Gender => Number => Case => Str = \\g,n,c => case <g,n,c> of {
    <Masc,Sg, CPrep P_de> => "del" ;
    <Masc,Sg, CPrep P_a>  => "al" ;
    <Masc,Sg, _>          => prepCase c ++ "el" ;

    <Fem ,Sg, _> => prepCase c ++ "la" ;
    <Masc,Pl, _> => prepCase c ++ "los" ;
    <Fem ,Pl, _> => prepCase c ++ "las"
    } ;

--2 Verbs
--
--3 The Bescherelle conjugations.
--
-- The following conjugations tables were generated using FM software
-- from a Haskell source.
--
-- The verb "essere" is often used in syntax.

  verbSer   = verbPres (ser_7 "ser") AHabere ;
  verbHaber = verbPres (haber_10 "haber")  AHabere ;

-- machine-generated GF code

oper zurrar_3 : Str -> Verbum = \zurrar -> 
  let zurr_ = Predef.tk 2 zurrar in
 {s = table {
    VI Infn=> zurr_ + "ar" ;
    VI Ger => zurr_ + "ando" ;
    VI Part => zurr_ + "ado" ;
    VP (Pres Ind Sg P1) => zurr_ + "o" ;
    VP (Pres Ind Sg P2) => zurr_ + "as" ;
    VP (Pres Ind Sg P3) => zurr_ + "a" ;
    VP (Pres Ind Pl P1) => zurr_ + "amos" ;
    VP (Pres Ind Pl P2) => zurr_ + "�is" ;
    VP (Pres Ind Pl P3) => zurr_ + "an" ;
    VP (Pres Subj Sg P1) => zurr_ + "e" ;
    VP (Pres Subj Sg P2) => zurr_ + "es" ;
    VP (Pres Subj Sg P3) => zurr_ + "e" ;
    VP (Pres Subj Pl P1) => zurr_ + "emos" ;
    VP (Pres Subj Pl P2) => zurr_ + "�is" ;
    VP (Pres Subj Pl P3) => zurr_ + "en" ;
    VP (Past Ind Sg P1) => zurr_ + "aba" ;
    VP (Past Ind Sg P2) => zurr_ + "abas" ;
    VP (Past Ind Sg P3) => zurr_ + "aba" ;
    VP (Past Ind Pl P1) => zurr_ + "�bamos" ;
    VP (Past Ind Pl P2) => zurr_ + "abais" ;
    VP (Past Ind Pl P3) => zurr_ + "aban" ;
    VP (Past Subj Sg P1) => variants {zurr_ + "ara" ; zurr_ + "ase"} ;
    VP (Past Subj Sg P2) => variants {zurr_ + "aras" ; zurr_ + "ases"} ;
    VP (Past Subj Sg P3) => variants {zurr_ + "ara" ; zurr_ + "ase"} ;
    VP (Past Subj Pl P1) => variants {zurr_ + "�ramos" ; zurr_ + "�semos"} ;
    VP (Past Subj Pl P2) => variants {zurr_ + "arais" ; zurr_ + "aseis"} ;
    VP (Past Subj Pl P3) => variants {zurr_ + "aran" ; zurr_ + "asen"} ;
    VP (Pret Sg P1) => zurr_ + "�" ;
    VP (Pret Sg P2) => zurr_ + "aste" ;
    VP (Pret Sg P3) => zurr_ + "�" ;
    VP (Pret Pl P1) => zurr_ + "amos" ;
    VP (Pret Pl P2) => zurr_ + "asteis" ;
    VP (Pret Pl P3) => zurr_ + "aron" ;
    VP (Fut Ind Sg P1) => zurr_ + "ar�" ;
    VP (Fut Ind Sg P2) => zurr_ + "ar�s" ;
    VP (Fut Ind Sg P3) => zurr_ + "ar�" ;
    VP (Fut Ind Pl P1) => zurr_ + "aremos" ;
    VP (Fut Ind Pl P2) => zurr_ + "ar�is" ;
    VP (Fut Ind Pl P3) => zurr_ + "ar�n" ;
    VP (Fut Subj Sg P1) => zurr_ + "are" ;
    VP (Fut Subj Sg P2) => zurr_ + "ares" ;
    VP (Fut Subj Sg P3) => zurr_ + "are" ;
    VP (Fut Subj Pl P1) => zurr_ + "�remos" ;
    VP (Fut Subj Pl P2) => zurr_ + "areis" ;
    VP (Fut Subj Pl P3) => zurr_ + "aren" ;
    VP (Cond Sg P1) => zurr_ + "ar�a" ;
    VP (Cond Sg P2) => zurr_ + "ar�as" ;
    VP (Cond Sg P3) => zurr_ + "ar�a" ;
    VP (Cond Pl P1) => zurr_ + "ar�amos" ;
    VP (Cond Pl P2) => zurr_ + "ar�ais" ;
    VP (Cond Pl P3) => zurr_ + "ar�an" ;
    VP (Imp Sg P1) => variants {} ;
    VP (Imp Sg P2) => zurr_ + "a" ;
    VP (Imp Sg P3) => zurr_ + "e" ;
    VP (Imp Pl P1) => zurr_ + "emos" ;
    VP (Imp Pl P2) => zurr_ + "ad" ;
    VP (Imp Pl P3) => zurr_ + "en" ;
    VP (Pass Sg Masc) => zurr_ + "ado" ;
    VP (Pass Sg Fem) => zurr_ + "ada" ;
    VP (Pass Pl Masc) => zurr_ + "ados" ;
    VP (Pass Pl Fem) => zurr_ + "adas"
    }
  } ;

oper vender_4 : Str -> Verbum = \vender -> 
  let vend_ = Predef.tk 2 vender in
 {s = table {
    VI Infn=> vend_ + "er" ;
    VI Ger => vend_ + "iendo" ;
    VI Part => vend_ + "ido" ;
    VP (Pres Ind Sg P1) => vend_ + "o" ;
    VP (Pres Ind Sg P2) => vend_ + "es" ;
    VP (Pres Ind Sg P3) => vend_ + "e" ;
    VP (Pres Ind Pl P1) => vend_ + "emos" ;
    VP (Pres Ind Pl P2) => vend_ + "�is" ;
    VP (Pres Ind Pl P3) => vend_ + "en" ;
    VP (Pres Subj Sg P1) => vend_ + "a" ;
    VP (Pres Subj Sg P2) => vend_ + "as" ;
    VP (Pres Subj Sg P3) => vend_ + "a" ;
    VP (Pres Subj Pl P1) => vend_ + "amos" ;
    VP (Pres Subj Pl P2) => vend_ + "�is" ;
    VP (Pres Subj Pl P3) => vend_ + "an" ;
    VP (Past Ind Sg P1) => vend_ + "�a" ;
    VP (Past Ind Sg P2) => vend_ + "�as" ;
    VP (Past Ind Sg P3) => vend_ + "�a" ;
    VP (Past Ind Pl P1) => vend_ + "�amos" ;
    VP (Past Ind Pl P2) => vend_ + "�ais" ;
    VP (Past Ind Pl P3) => vend_ + "�an" ;
    VP (Past Subj Sg P1) => variants {vend_ + "iera" ; vend_ + "iese"} ;
    VP (Past Subj Sg P2) => variants {vend_ + "ieras" ; vend_ + "ieses"} ;
    VP (Past Subj Sg P3) => variants {vend_ + "iera" ; vend_ + "iese"} ;
    VP (Past Subj Pl P1) => variants {vend_ + "i�ramos" ; vend_ + "i�semos"} ;
    VP (Past Subj Pl P2) => variants {vend_ + "ierais" ; vend_ + "ieseis"} ;
    VP (Past Subj Pl P3) => variants {vend_ + "ieran" ; vend_ + "iesen"} ;
    VP (Pret Sg P1) => vend_ + "�" ;
    VP (Pret Sg P2) => vend_ + "iste" ;
    VP (Pret Sg P3) => vend_ + "i�" ;
    VP (Pret Pl P1) => vend_ + "imos" ;
    VP (Pret Pl P2) => vend_ + "isteis" ;
    VP (Pret Pl P3) => vend_ + "ieron" ;
    VP (Fut Ind Sg P1) => vend_ + "er�" ;
    VP (Fut Ind Sg P2) => vend_ + "er�s" ;
    VP (Fut Ind Sg P3) => vend_ + "er�" ;
    VP (Fut Ind Pl P1) => vend_ + "eremos" ;
    VP (Fut Ind Pl P2) => vend_ + "er�is" ;
    VP (Fut Ind Pl P3) => vend_ + "er�n" ;
    VP (Fut Subj Sg P1) => vend_ + "iere" ;
    VP (Fut Subj Sg P2) => vend_ + "ieres" ;
    VP (Fut Subj Sg P3) => vend_ + "iere" ;
    VP (Fut Subj Pl P1) => vend_ + "i�remos" ;
    VP (Fut Subj Pl P2) => vend_ + "iereis" ;
    VP (Fut Subj Pl P3) => vend_ + "ieren" ;
    VP (Cond Sg P1) => vend_ + "er�a" ;
    VP (Cond Sg P2) => vend_ + "er�as" ;
    VP (Cond Sg P3) => vend_ + "er�a" ;
    VP (Cond Pl P1) => vend_ + "er�amos" ;
    VP (Cond Pl P2) => vend_ + "er�ais" ;
    VP (Cond Pl P3) => vend_ + "er�an" ;
    VP (Imp Sg P1) => variants {} ;
    VP (Imp Sg P2) => vend_ + "e" ;
    VP (Imp Sg P3) => vend_ + "a" ;
    VP (Imp Pl P1) => vend_ + "amos" ;
    VP (Imp Pl P2) => vend_ + "ed" ;
    VP (Imp Pl P3) => vend_ + "an" ;
    VP (Pass Sg Masc) => vend_ + "ido" ;
    VP (Pass Sg Fem) => vend_ + "ida" ;
    VP (Pass Pl Masc) => vend_ + "idos" ;
    VP (Pass Pl Fem) => vend_ + "idas"
    }
  } ;

oper zurrir_5 : Str -> Verbum = \zurrir -> 
  let zurr_ = Predef.tk 2 zurrir in
 {s = table {
    VI Infn=> zurr_ + "ir" ;
    VI Ger => zurr_ + "iendo" ;
    VI Part => zurr_ + "ido" ;
    VP (Pres Ind Sg P1) => zurr_ + "o" ;
    VP (Pres Ind Sg P2) => zurr_ + "es" ;
    VP (Pres Ind Sg P3) => zurr_ + "e" ;
    VP (Pres Ind Pl P1) => zurr_ + "imos" ;
    VP (Pres Ind Pl P2) => zurr_ + "�s" ;
    VP (Pres Ind Pl P3) => zurr_ + "en" ;
    VP (Pres Subj Sg P1) => zurr_ + "a" ;
    VP (Pres Subj Sg P2) => zurr_ + "as" ;
    VP (Pres Subj Sg P3) => zurr_ + "a" ;
    VP (Pres Subj Pl P1) => zurr_ + "amos" ;
    VP (Pres Subj Pl P2) => zurr_ + "�is" ;
    VP (Pres Subj Pl P3) => zurr_ + "an" ;
    VP (Past Ind Sg P1) => zurr_ + "�a" ;
    VP (Past Ind Sg P2) => zurr_ + "�as" ;
    VP (Past Ind Sg P3) => zurr_ + "�a" ;
    VP (Past Ind Pl P1) => zurr_ + "�amos" ;
    VP (Past Ind Pl P2) => zurr_ + "�ais" ;
    VP (Past Ind Pl P3) => zurr_ + "�an" ;
    VP (Past Subj Sg P1) => variants {zurr_ + "iera" ; zurr_ + "iese"} ;
    VP (Past Subj Sg P2) => variants {zurr_ + "ieras" ; zurr_ + "ieses"} ;
    VP (Past Subj Sg P3) => variants {zurr_ + "iera" ; zurr_ + "iese"} ;
    VP (Past Subj Pl P1) => variants {zurr_ + "i�ramos" ; zurr_ + "i�semos"} ;
    VP (Past Subj Pl P2) => variants {zurr_ + "ierais" ; zurr_ + "ieseis"} ;
    VP (Past Subj Pl P3) => variants {zurr_ + "ieran" ; zurr_ + "iesen"} ;
    VP (Pret Sg P1) => zurr_ + "�" ;
    VP (Pret Sg P2) => zurr_ + "iste" ;
    VP (Pret Sg P3) => zurr_ + "i�" ;
    VP (Pret Pl P1) => zurr_ + "imos" ;
    VP (Pret Pl P2) => zurr_ + "isteis" ;
    VP (Pret Pl P3) => zurr_ + "ieron" ;
    VP (Fut Ind Sg P1) => zurr_ + "ir�" ;
    VP (Fut Ind Sg P2) => zurr_ + "ir�s" ;
    VP (Fut Ind Sg P3) => zurr_ + "ir�" ;
    VP (Fut Ind Pl P1) => zurr_ + "iremos" ;
    VP (Fut Ind Pl P2) => zurr_ + "ir�is" ;
    VP (Fut Ind Pl P3) => zurr_ + "ir�n" ;
    VP (Fut Subj Sg P1) => zurr_ + "iere" ;
    VP (Fut Subj Sg P2) => zurr_ + "ieres" ;
    VP (Fut Subj Sg P3) => zurr_ + "iere" ;
    VP (Fut Subj Pl P1) => zurr_ + "i�remos" ;
    VP (Fut Subj Pl P2) => zurr_ + "iereis" ;
    VP (Fut Subj Pl P3) => zurr_ + "ieren" ;
    VP (Cond Sg P1) => zurr_ + "ir�a" ;
    VP (Cond Sg P2) => zurr_ + "ir�as" ;
    VP (Cond Sg P3) => zurr_ + "ir�a" ;
    VP (Cond Pl P1) => zurr_ + "ir�amos" ;
    VP (Cond Pl P2) => zurr_ + "ir�ais" ;
    VP (Cond Pl P3) => zurr_ + "ir�an" ;
    VP (Imp Sg P1) => variants {} ;
    VP (Imp Sg P2) => zurr_ + "e" ;
    VP (Imp Sg P3) => zurr_ + "a" ;
    VP (Imp Pl P1) => zurr_ + "amos" ;
    VP (Imp Pl P2) => zurr_ + "id" ;
    VP (Imp Pl P3) => zurr_ + "an" ;
    VP (Pass Sg Masc) => zurr_ + "ido" ;
    VP (Pass Sg Fem) => zurr_ + "ida" ;
    VP (Pass Pl Masc) => zurr_ + "idos" ;
    VP (Pass Pl Fem) => zurr_ + "idas"
    }
  } ;

oper zullarse_6 : Str -> Verbum = \zullarse -> 
  let zull_ = Predef.tk 4 zullarse in
 {s = table {
    VI Infn=> zull_ + "arse" ;
    VI Ger => zull_ + "ando" ;
    VI Part => zull_ + "ado" ;
    VP (Pres Ind Sg P1) => zull_ + "o" ;
    VP (Pres Ind Sg P2) => zull_ + "as" ;
    VP (Pres Ind Sg P3) => zull_ + "a" ;
    VP (Pres Ind Pl P1) => zull_ + "amos" ;
    VP (Pres Ind Pl P2) => zull_ + "�is" ;
    VP (Pres Ind Pl P3) => zull_ + "an" ;
    VP (Pres Subj Sg P1) => zull_ + "e" ;
    VP (Pres Subj Sg P2) => zull_ + "es" ;
    VP (Pres Subj Sg P3) => zull_ + "e" ;
    VP (Pres Subj Pl P1) => zull_ + "emos" ;
    VP (Pres Subj Pl P2) => zull_ + "�is" ;
    VP (Pres Subj Pl P3) => zull_ + "en" ;
    VP (Past Ind Sg P1) => zull_ + "aba" ;
    VP (Past Ind Sg P2) => zull_ + "abas" ;
    VP (Past Ind Sg P3) => zull_ + "aba" ;
    VP (Past Ind Pl P1) => zull_ + "�bamos" ;
    VP (Past Ind Pl P2) => zull_ + "abais" ;
    VP (Past Ind Pl P3) => zull_ + "aban" ;
    VP (Past Subj Sg P1) => variants {zull_ + "ara" ; zull_ + "ase"} ;
    VP (Past Subj Sg P2) => variants {zull_ + "aras" ; zull_ + "ases"} ;
    VP (Past Subj Sg P3) => variants {zull_ + "ara" ; zull_ + "ase"} ;
    VP (Past Subj Pl P1) => variants {zull_ + "�ramos" ; zull_ + "�semos"} ;
    VP (Past Subj Pl P2) => variants {zull_ + "arais" ; zull_ + "aseis"} ;
    VP (Past Subj Pl P3) => variants {zull_ + "aran" ; zull_ + "asen"} ;
    VP (Pret Sg P1) => zull_ + "�" ;
    VP (Pret Sg P2) => zull_ + "aste" ;
    VP (Pret Sg P3) => zull_ + "�" ;
    VP (Pret Pl P1) => zull_ + "amos" ;
    VP (Pret Pl P2) => zull_ + "asteis" ;
    VP (Pret Pl P3) => zull_ + "aron" ;
    VP (Fut Ind Sg P1) => zull_ + "ar�" ;
    VP (Fut Ind Sg P2) => zull_ + "ar�s" ;
    VP (Fut Ind Sg P3) => zull_ + "ar�" ;
    VP (Fut Ind Pl P1) => zull_ + "aremos" ;
    VP (Fut Ind Pl P2) => zull_ + "ar�is" ;
    VP (Fut Ind Pl P3) => zull_ + "ar�n" ;
    VP (Fut Subj Sg P1) => zull_ + "are" ;
    VP (Fut Subj Sg P2) => zull_ + "ares" ;
    VP (Fut Subj Sg P3) => zull_ + "are" ;
    VP (Fut Subj Pl P1) => zull_ + "�remos" ;
    VP (Fut Subj Pl P2) => zull_ + "areis" ;
    VP (Fut Subj Pl P3) => zull_ + "aren" ;
    VP (Cond Sg P1) => zull_ + "ar�a" ;
    VP (Cond Sg P2) => zull_ + "ar�as" ;
    VP (Cond Sg P3) => zull_ + "ar�a" ;
    VP (Cond Pl P1) => zull_ + "ar�amos" ;
    VP (Cond Pl P2) => zull_ + "ar�ais" ;
    VP (Cond Pl P3) => zull_ + "ar�an" ;
    VP (Imp Sg P1) => variants {} ;
    VP (Imp Sg P2) => zull_ + "a" ;
    VP (Imp Sg P3) => zull_ + "e" ;
    VP (Imp Pl P1) => zull_ + "emos" ;
    VP (Imp Pl P2) => zull_ + "ad" ;
    VP (Imp Pl P3) => zull_ + "en" ;
    VP (Pass Sg Masc) => zull_ + "ado" ;
    VP (Pass Sg Fem) => zull_ + "ada" ;
    VP (Pass Pl Masc) => zull_ + "ados" ;
    VP (Pass Pl Fem) => zull_ + "adas"
    }
  } ;

oper ser_7 : Str -> Verbum = \ser -> 
  let x_ = Predef.tk 3 ser in
 {s = table {
    VI Infn=> x_ + "ser" ;
    VI Ger => x_ + "siendo" ;
    VI Part => x_ + "sido" ;
    VP (Pres Ind Sg P1) => x_ + "soy" ;
    VP (Pres Ind Sg P2) => x_ + "eres" ;
    VP (Pres Ind Sg P3) => x_ + "es" ;
    VP (Pres Ind Pl P1) => x_ + "somos" ;
    VP (Pres Ind Pl P2) => x_ + "sois" ;
    VP (Pres Ind Pl P3) => x_ + "son" ;
    VP (Pres Subj Sg P1) => x_ + "sea" ;
    VP (Pres Subj Sg P2) => x_ + "seas" ;
    VP (Pres Subj Sg P3) => x_ + "sea" ;
    VP (Pres Subj Pl P1) => x_ + "seamos" ;
    VP (Pres Subj Pl P2) => x_ + "se�is" ;
    VP (Pres Subj Pl P3) => x_ + "sean" ;
    VP (Past Ind Sg P1) => x_ + "era" ;
    VP (Past Ind Sg P2) => x_ + "eras" ;
    VP (Past Ind Sg P3) => x_ + "era" ;
    VP (Past Ind Pl P1) => x_ + "�ramos" ;
    VP (Past Ind Pl P2) => x_ + "erais" ;
    VP (Past Ind Pl P3) => x_ + "eran" ;
    VP (Past Subj Sg P1) => variants {x_ + "fuera" ; x_ + "fuese"} ;
    VP (Past Subj Sg P2) => variants {x_ + "fueras" ; x_ + "fueses"} ;
    VP (Past Subj Sg P3) => variants {x_ + "fuera" ; x_ + "fuese"} ;
    VP (Past Subj Pl P1) => variants {x_ + "fu�ramos" ; x_ + "fu�semos"} ;
    VP (Past Subj Pl P2) => variants {x_ + "fuerais" ; x_ + "fueseis"} ;
    VP (Past Subj Pl P3) => variants {x_ + "fueran" ; x_ + "fuesen"} ;
    VP (Pret Sg P1) => x_ + "fui" ;
    VP (Pret Sg P2) => x_ + "fuiste" ;
    VP (Pret Sg P3) => x_ + "fue" ;
    VP (Pret Pl P1) => x_ + "fuimos" ;
    VP (Pret Pl P2) => x_ + "fuisteis" ;
    VP (Pret Pl P3) => x_ + "fueron" ;
    VP (Fut Ind Sg P1) => x_ + "ser�" ;
    VP (Fut Ind Sg P2) => x_ + "ser�s" ;
    VP (Fut Ind Sg P3) => x_ + "ser�" ;
    VP (Fut Ind Pl P1) => x_ + "seremos" ;
    VP (Fut Ind Pl P2) => x_ + "ser�is" ;
    VP (Fut Ind Pl P3) => x_ + "ser�n" ;
    VP (Fut Subj Sg P1) => x_ + "fuere" ;
    VP (Fut Subj Sg P2) => x_ + "fueres" ;
    VP (Fut Subj Sg P3) => x_ + "fuere" ;
    VP (Fut Subj Pl P1) => x_ + "fu�remos" ;
    VP (Fut Subj Pl P2) => x_ + "fuereis" ;
    VP (Fut Subj Pl P3) => x_ + "fueren" ;
    VP (Cond Sg P1) => x_ + "ser�a" ;
    VP (Cond Sg P2) => x_ + "ser�as" ;
    VP (Cond Sg P3) => x_ + "ser�a" ;
    VP (Cond Pl P1) => x_ + "ser�amos" ;
    VP (Cond Pl P2) => x_ + "ser�ais" ;
    VP (Cond Pl P3) => x_ + "ser�an" ;
    VP (Imp Sg P1) => variants {} ;
    VP (Imp Sg P2) => x_ + "s�" ;
    VP (Imp Sg P3) => x_ + "sea" ;
    VP (Imp Pl P1) => x_ + "seamos" ;
    VP (Imp Pl P2) => x_ + "sed" ;
    VP (Imp Pl P3) => x_ + "sean" ;
    VP (Pass Sg Masc) => x_ + "sido" ;
    VP (Pass Sg Fem) => x_ + "sida" ;
    VP (Pass Pl Masc) => x_ + "sidos" ;
    VP (Pass Pl Fem) => x_ + "sidas"
    }
  } ;

oper ir_8 : Str -> Verbum = \ir -> 
  let x_ = Predef.tk 2 ir in
 {s = table {
    VI Infn=> x_ + "ir" ;
    VI Ger => x_ + "yendo" ;
    VI Part => x_ + "ido" ;
    VP (Pres Ind Sg P1) => x_ + "voy" ;
    VP (Pres Ind Sg P2) => x_ + "vas" ;
    VP (Pres Ind Sg P3) => x_ + "va" ;
    VP (Pres Ind Pl P1) => x_ + "vamos" ;
    VP (Pres Ind Pl P2) => x_ + "vais" ;
    VP (Pres Ind Pl P3) => x_ + "van" ;
    VP (Pres Subj Sg P1) => x_ + "vaya" ;
    VP (Pres Subj Sg P2) => x_ + "vayas" ;
    VP (Pres Subj Sg P3) => x_ + "vaya" ;
    VP (Pres Subj Pl P1) => x_ + "vayamos" ;
    VP (Pres Subj Pl P2) => x_ + "vay�is" ;
    VP (Pres Subj Pl P3) => x_ + "vayan" ;
    VP (Past Ind Sg P1) => x_ + "iba" ;
    VP (Past Ind Sg P2) => x_ + "ibas" ;
    VP (Past Ind Sg P3) => x_ + "iba" ;
    VP (Past Ind Pl P1) => x_ + "�bamos" ;
    VP (Past Ind Pl P2) => x_ + "ibais" ;
    VP (Past Ind Pl P3) => x_ + "iban" ;
    VP (Past Subj Sg P1) => variants {x_ + "fuera" ; x_ + "fuese"} ;
    VP (Past Subj Sg P2) => variants {x_ + "fueras" ; x_ + "fueses"} ;
    VP (Past Subj Sg P3) => variants {x_ + "fuera" ; x_ + "fuese"} ;
    VP (Past Subj Pl P1) => variants {x_ + "fu�ramos" ; x_ + "fu�semos"} ;
    VP (Past Subj Pl P2) => variants {x_ + "fuerais" ; x_ + "fueseis"} ;
    VP (Past Subj Pl P3) => variants {x_ + "fueran" ; x_ + "fuesen"} ;
    VP (Pret Sg P1) => x_ + "fui" ;
    VP (Pret Sg P2) => x_ + "fuiste" ;
    VP (Pret Sg P3) => x_ + "fue" ;
    VP (Pret Pl P1) => x_ + "fuimos" ;
    VP (Pret Pl P2) => x_ + "fuisteis" ;
    VP (Pret Pl P3) => x_ + "fueron" ;
    VP (Fut Ind Sg P1) => x_ + "ir�" ;
    VP (Fut Ind Sg P2) => x_ + "ir�s" ;
    VP (Fut Ind Sg P3) => x_ + "ir�" ;
    VP (Fut Ind Pl P1) => x_ + "iremos" ;
    VP (Fut Ind Pl P2) => x_ + "ir�is" ;
    VP (Fut Ind Pl P3) => x_ + "ir�n" ;
    VP (Fut Subj Sg P1) => x_ + "fuere" ;
    VP (Fut Subj Sg P2) => x_ + "fueres" ;
    VP (Fut Subj Sg P3) => x_ + "fuere" ;
    VP (Fut Subj Pl P1) => x_ + "fu�remos" ;
    VP (Fut Subj Pl P2) => x_ + "fuereis" ;
    VP (Fut Subj Pl P3) => x_ + "fueren" ;
    VP (Cond Sg P1) => x_ + "ir�a" ;
    VP (Cond Sg P2) => x_ + "ir�as" ;
    VP (Cond Sg P3) => x_ + "ir�a" ;
    VP (Cond Pl P1) => x_ + "ir�amos" ;
    VP (Cond Pl P2) => x_ + "ir�ais" ;
    VP (Cond Pl P3) => x_ + "ir�an" ;
    VP (Imp Sg P1) => variants {} ;
    VP (Imp Sg P2) => x_ + "ve" ;
    VP (Imp Sg P3) => x_ + "vaya" ;
    VP (Imp Pl P1) => variants {x_ + "vamos" ; x_ + "vayamos"} ;
    VP (Imp Pl P2) => x_ + "id" ;
    VP (Imp Pl P3) => x_ + "vayan" ;
    VP (Pass Sg Masc) => x_ + "ido" ;
    VP (Pass Sg Fem) => x_ + "ida" ;
    VP (Pass Pl Masc) => x_ + "idos" ;
    VP (Pass Pl Fem) => x_ + "idas"
    }
  } ;

oper estar_9 : Str -> Verbum = \estar -> 
  let est_ = Predef.tk 2 estar in
 {s = table {
    VI Infn=> est_ + "ar" ;
    VI Ger => est_ + "ando" ;
    VI Part => est_ + "ado" ;
    VP (Pres Ind Sg P1) => est_ + "oy" ;
    VP (Pres Ind Sg P2) => est_ + "�s" ;
    VP (Pres Ind Sg P3) => est_ + "�" ;
    VP (Pres Ind Pl P1) => est_ + "amos" ;
    VP (Pres Ind Pl P2) => est_ + "�is" ;
    VP (Pres Ind Pl P3) => est_ + "�n" ;
    VP (Pres Subj Sg P1) => est_ + "�" ;
    VP (Pres Subj Sg P2) => est_ + "�s" ;
    VP (Pres Subj Sg P3) => est_ + "�" ;
    VP (Pres Subj Pl P1) => est_ + "emos" ;
    VP (Pres Subj Pl P2) => est_ + "�is" ;
    VP (Pres Subj Pl P3) => est_ + "�n" ;
    VP (Past Ind Sg P1) => est_ + "aba" ;
    VP (Past Ind Sg P2) => est_ + "abas" ;
    VP (Past Ind Sg P3) => est_ + "aba" ;
    VP (Past Ind Pl P1) => est_ + "�bamos" ;
    VP (Past Ind Pl P2) => est_ + "abais" ;
    VP (Past Ind Pl P3) => est_ + "aban" ;
    VP (Past Subj Sg P1) => variants {est_ + "uviera" ; est_ + "uviese"} ;
    VP (Past Subj Sg P2) => variants {est_ + "uvieras" ; est_ + "uvieses"} ;
    VP (Past Subj Sg P3) => variants {est_ + "uviera" ; est_ + "uviese"} ;
    VP (Past Subj Pl P1) => variants {est_ + "uvi�ramos" ; est_ + "uvi�semos"} ;
    VP (Past Subj Pl P2) => variants {est_ + "uvierais" ; est_ + "uvieseis"} ;
    VP (Past Subj Pl P3) => variants {est_ + "uvieran" ; est_ + "uviesen"} ;
    VP (Pret Sg P1) => est_ + "uve" ;
    VP (Pret Sg P2) => est_ + "uviste" ;
    VP (Pret Sg P3) => est_ + "uvo" ;
    VP (Pret Pl P1) => est_ + "uvimos" ;
    VP (Pret Pl P2) => est_ + "uvisteis" ;
    VP (Pret Pl P3) => est_ + "uvieron" ;
    VP (Fut Ind Sg P1) => est_ + "ar�" ;
    VP (Fut Ind Sg P2) => est_ + "ar�s" ;
    VP (Fut Ind Sg P3) => est_ + "ar�" ;
    VP (Fut Ind Pl P1) => est_ + "aremos" ;
    VP (Fut Ind Pl P2) => est_ + "ar�is" ;
    VP (Fut Ind Pl P3) => est_ + "ar�n" ;
    VP (Fut Subj Sg P1) => est_ + "uviere" ;
    VP (Fut Subj Sg P2) => est_ + "uvieres" ;
    VP (Fut Subj Sg P3) => est_ + "uviere" ;
    VP (Fut Subj Pl P1) => est_ + "uvi�remos" ;
    VP (Fut Subj Pl P2) => est_ + "uviereis" ;
    VP (Fut Subj Pl P3) => est_ + "uvieren" ;
    VP (Cond Sg P1) => est_ + "ar�a" ;
    VP (Cond Sg P2) => est_ + "ar�as" ;
    VP (Cond Sg P3) => est_ + "ar�a" ;
    VP (Cond Pl P1) => est_ + "ar�amos" ;
    VP (Cond Pl P2) => est_ + "ar�ais" ;
    VP (Cond Pl P3) => est_ + "ar�an" ;
    VP (Imp Sg P1) => variants {} ;
    VP (Imp Sg P2) => est_ + "�" ;
    VP (Imp Sg P3) => est_ + "�" ;
    VP (Imp Pl P1) => est_ + "emos" ;
    VP (Imp Pl P2) => est_ + "ad" ;
    VP (Imp Pl P3) => est_ + "�n" ;
    VP (Pass Sg Masc) => est_ + "ado" ;
    VP (Pass Sg Fem) => est_ + "ada" ;
    VP (Pass Pl Masc) => est_ + "ados" ;
    VP (Pass Pl Fem) => est_ + "adas"
    }
  } ;

oper haber_10 : Str -> Verbum = \haber -> 
  let h_ = Predef.tk 4 haber in
 {s = table {
    VI Infn=> h_ + "aber" ;
    VI Ger => h_ + "abiendo" ;
    VI Part => h_ + "abido" ;
    VP (Pres Ind Sg P1) => h_ + "e" ;
    VP (Pres Ind Sg P2) => h_ + "as" ;
    VP (Pres Ind Sg P3) => variants {h_ + "a" ; h_ + "ay"} ;
    VP (Pres Ind Pl P1) => h_ + "emos" ;
    VP (Pres Ind Pl P2) => h_ + "ab�is" ;
    VP (Pres Ind Pl P3) => h_ + "an" ;
    VP (Pres Subj Sg P1) => h_ + "aya" ;
    VP (Pres Subj Sg P2) => h_ + "ayas" ;
    VP (Pres Subj Sg P3) => h_ + "aya" ;
    VP (Pres Subj Pl P1) => h_ + "ayamos" ;
    VP (Pres Subj Pl P2) => h_ + "ay�is" ;
    VP (Pres Subj Pl P3) => h_ + "ayan" ;
    VP (Past Ind Sg P1) => h_ + "ab�a" ;
    VP (Past Ind Sg P2) => h_ + "ab�as" ;
    VP (Past Ind Sg P3) => h_ + "ab�a" ;
    VP (Past Ind Pl P1) => h_ + "ab�amos" ;
    VP (Past Ind Pl P2) => h_ + "ab�ais" ;
    VP (Past Ind Pl P3) => h_ + "ab�an" ;
    VP (Past Subj Sg P1) => variants {h_ + "ubiera" ; h_ + "ubiese"} ;
    VP (Past Subj Sg P2) => variants {h_ + "ubieras" ; h_ + "ubieses"} ;
    VP (Past Subj Sg P3) => variants {h_ + "ubiera" ; h_ + "ubiese"} ;
    VP (Past Subj Pl P1) => variants {h_ + "ubi�ramos" ; h_ + "ubi�semos"} ;
    VP (Past Subj Pl P2) => variants {h_ + "ubierais" ; h_ + "ubieseis"} ;
    VP (Past Subj Pl P3) => variants {h_ + "ubieran" ; h_ + "ubiesen"} ;
    VP (Pret Sg P1) => h_ + "ube" ;
    VP (Pret Sg P2) => h_ + "ubiste" ;
    VP (Pret Sg P3) => h_ + "ubo" ;
    VP (Pret Pl P1) => h_ + "ubimos" ;
    VP (Pret Pl P2) => h_ + "ubisteis" ;
    VP (Pret Pl P3) => h_ + "ubieron" ;
    VP (Fut Ind Sg P1) => h_ + "abr�" ;
    VP (Fut Ind Sg P2) => h_ + "abr�s" ;
    VP (Fut Ind Sg P3) => h_ + "abr�" ;
    VP (Fut Ind Pl P1) => h_ + "abremos" ;
    VP (Fut Ind Pl P2) => h_ + "abr�is" ;
    VP (Fut Ind Pl P3) => h_ + "abr�n" ;
    VP (Fut Subj Sg P1) => h_ + "ubiere" ;
    VP (Fut Subj Sg P2) => h_ + "ubieres" ;
    VP (Fut Subj Sg P3) => h_ + "ubiere" ;
    VP (Fut Subj Pl P1) => h_ + "ubi�remos" ;
    VP (Fut Subj Pl P2) => h_ + "ubiereis" ;
    VP (Fut Subj Pl P3) => h_ + "ubieren" ;
    VP (Cond Sg P1) => h_ + "abr�a" ;
    VP (Cond Sg P2) => h_ + "abr�as" ;
    VP (Cond Sg P3) => h_ + "abr�a" ;
    VP (Cond Pl P1) => h_ + "abr�amos" ;
    VP (Cond Pl P2) => h_ + "abr�ais" ;
    VP (Cond Pl P3) => h_ + "abr�an" ;
    VP (Imp Sg P1) => variants {} ;
    VP (Imp Sg P2) => variants {} ;
    VP (Imp Sg P3) => variants {} ;
    VP (Imp Pl P1) => variants {} ;
    VP (Imp Pl P2) => variants {} ;
    VP (Imp Pl P3) => variants {} ;
    VP (Pass Sg Masc) => h_ + "abido" ;
    VP (Pass Sg Fem) => h_ + "abida" ;
    VP (Pass Pl Masc) => h_ + "abidos" ;
    VP (Pass Pl Fem) => h_ + "abidas"
    }
  } ;

oper saber_11 : Str -> Verbum = \saber -> 
  let s_ = Predef.tk 4 saber in
 {s = table {
    VI Infn=> s_ + "aber" ;
    VI Ger => s_ + "abiendo" ;
    VI Part => s_ + "abido" ;
    VP (Pres Ind Sg P1) => s_ + "�" ;
    VP (Pres Ind Sg P2) => s_ + "abes" ;
    VP (Pres Ind Sg P3) => s_ + "abe" ;
    VP (Pres Ind Pl P1) => s_ + "abemos" ;
    VP (Pres Ind Pl P2) => s_ + "ab�is" ;
    VP (Pres Ind Pl P3) => s_ + "aben" ;
    VP (Pres Subj Sg P1) => s_ + "epa" ;
    VP (Pres Subj Sg P2) => s_ + "epas" ;
    VP (Pres Subj Sg P3) => s_ + "epa" ;
    VP (Pres Subj Pl P1) => s_ + "epamos" ;
    VP (Pres Subj Pl P2) => s_ + "ep�is" ;
    VP (Pres Subj Pl P3) => s_ + "epan" ;
    VP (Past Ind Sg P1) => s_ + "ab�a" ;
    VP (Past Ind Sg P2) => s_ + "ab�as" ;
    VP (Past Ind Sg P3) => s_ + "ab�a" ;
    VP (Past Ind Pl P1) => s_ + "ab�amos" ;
    VP (Past Ind Pl P2) => s_ + "ab�ais" ;
    VP (Past Ind Pl P3) => s_ + "ab�an" ;
    VP (Past Subj Sg P1) => variants {s_ + "upiera" ; s_ + "upiese"} ;
    VP (Past Subj Sg P2) => variants {s_ + "upieras" ; s_ + "upieses"} ;
    VP (Past Subj Sg P3) => variants {s_ + "upiera" ; s_ + "upiese"} ;
    VP (Past Subj Pl P1) => variants {s_ + "upi�ramos" ; s_ + "upi�semos"} ;
    VP (Past Subj Pl P2) => variants {s_ + "upierais" ; s_ + "upieseis"} ;
    VP (Past Subj Pl P3) => variants {s_ + "upieran" ; s_ + "upiesen"} ;
    VP (Pret Sg P1) => s_ + "upe" ;
    VP (Pret Sg P2) => s_ + "upiste" ;
    VP (Pret Sg P3) => s_ + "upo" ;
    VP (Pret Pl P1) => s_ + "upimos" ;
    VP (Pret Pl P2) => s_ + "upisteis" ;
    VP (Pret Pl P3) => s_ + "upieron" ;
    VP (Fut Ind Sg P1) => s_ + "abr�" ;
    VP (Fut Ind Sg P2) => s_ + "abr�s" ;
    VP (Fut Ind Sg P3) => s_ + "abr�" ;
    VP (Fut Ind Pl P1) => s_ + "abremos" ;
    VP (Fut Ind Pl P2) => s_ + "abr�is" ;
    VP (Fut Ind Pl P3) => s_ + "abr�n" ;
    VP (Fut Subj Sg P1) => s_ + "upiere" ;
    VP (Fut Subj Sg P2) => s_ + "upieres" ;
    VP (Fut Subj Sg P3) => s_ + "upiere" ;
    VP (Fut Subj Pl P1) => s_ + "upi�remos" ;
    VP (Fut Subj Pl P2) => s_ + "upiereis" ;
    VP (Fut Subj Pl P3) => s_ + "upieren" ;
    VP (Cond Sg P1) => s_ + "abr�a" ;
    VP (Cond Sg P2) => s_ + "abr�as" ;
    VP (Cond Sg P3) => s_ + "abr�a" ;
    VP (Cond Pl P1) => s_ + "abr�amos" ;
    VP (Cond Pl P2) => s_ + "abr�ais" ;
    VP (Cond Pl P3) => s_ + "abr�an" ;
    VP (Imp Sg P1) => variants {} ;
    VP (Imp Sg P2) => s_ + "abe" ;
    VP (Imp Sg P3) => s_ + "epa" ;
    VP (Imp Pl P1) => s_ + "epamos" ;
    VP (Imp Pl P2) => s_ + "abed" ;
    VP (Imp Pl P3) => s_ + "epan" ;
    VP (Pass Sg Masc) => s_ + "abido" ;
    VP (Pass Sg Fem) => s_ + "abida" ;
    VP (Pass Pl Masc) => s_ + "abidos" ;
    VP (Pass Pl Fem) => s_ + "abidas"
    }
  } ;

oper venir_12 : Str -> Verbum = \venir -> 
  let v_ = Predef.tk 4 venir in
 {s = table {
    VI Infn=> v_ + "enir" ;
    VI Ger => v_ + "iniendo" ;
    VI Part => v_ + "enido" ;
    VP (Pres Ind Sg P1) => v_ + "engo" ;
    VP (Pres Ind Sg P2) => v_ + "ienes" ;
    VP (Pres Ind Sg P3) => v_ + "iene" ;
    VP (Pres Ind Pl P1) => v_ + "enimos" ;
    VP (Pres Ind Pl P2) => v_ + "en�s" ;
    VP (Pres Ind Pl P3) => v_ + "ienen" ;
    VP (Pres Subj Sg P1) => v_ + "enga" ;
    VP (Pres Subj Sg P2) => v_ + "engas" ;
    VP (Pres Subj Sg P3) => v_ + "enga" ;
    VP (Pres Subj Pl P1) => v_ + "engamos" ;
    VP (Pres Subj Pl P2) => v_ + "eng�is" ;
    VP (Pres Subj Pl P3) => v_ + "engan" ;
    VP (Past Ind Sg P1) => v_ + "en�a" ;
    VP (Past Ind Sg P2) => v_ + "en�as" ;
    VP (Past Ind Sg P3) => v_ + "en�a" ;
    VP (Past Ind Pl P1) => v_ + "en�amos" ;
    VP (Past Ind Pl P2) => v_ + "en�ais" ;
    VP (Past Ind Pl P3) => v_ + "en�an" ;
    VP (Past Subj Sg P1) => variants {v_ + "iniera" ; v_ + "iniese"} ;
    VP (Past Subj Sg P2) => variants {v_ + "inieras" ; v_ + "inieses"} ;
    VP (Past Subj Sg P3) => variants {v_ + "iniera" ; v_ + "iniese"} ;
    VP (Past Subj Pl P1) => variants {v_ + "ini�ramos" ; v_ + "ini�semos"} ;
    VP (Past Subj Pl P2) => variants {v_ + "inierais" ; v_ + "inieseis"} ;
    VP (Past Subj Pl P3) => variants {v_ + "inieran" ; v_ + "iniesen"} ;
    VP (Pret Sg P1) => v_ + "ine" ;
    VP (Pret Sg P2) => v_ + "iniste" ;
    VP (Pret Sg P3) => v_ + "ino" ;
    VP (Pret Pl P1) => v_ + "inimos" ;
    VP (Pret Pl P2) => v_ + "inisteis" ;
    VP (Pret Pl P3) => v_ + "inieron" ;
    VP (Fut Ind Sg P1) => v_ + "endr�" ;
    VP (Fut Ind Sg P2) => v_ + "endr�s" ;
    VP (Fut Ind Sg P3) => v_ + "endr�" ;
    VP (Fut Ind Pl P1) => v_ + "endremos" ;
    VP (Fut Ind Pl P2) => v_ + "endr�is" ;
    VP (Fut Ind Pl P3) => v_ + "endr�n" ;
    VP (Fut Subj Sg P1) => v_ + "iniere" ;
    VP (Fut Subj Sg P2) => v_ + "inieres" ;
    VP (Fut Subj Sg P3) => v_ + "iniere" ;
    VP (Fut Subj Pl P1) => v_ + "ini�remos" ;
    VP (Fut Subj Pl P2) => v_ + "iniereis" ;
    VP (Fut Subj Pl P3) => v_ + "inieren" ;
    VP (Cond Sg P1) => v_ + "endr�a" ;
    VP (Cond Sg P2) => v_ + "endr�as" ;
    VP (Cond Sg P3) => v_ + "endr�a" ;
    VP (Cond Pl P1) => v_ + "endr�amos" ;
    VP (Cond Pl P2) => v_ + "endr�ais" ;
    VP (Cond Pl P3) => v_ + "endr�an" ;
    VP (Imp Sg P1) => variants {} ;
    VP (Imp Sg P2) => v_ + "en" ;
    VP (Imp Sg P3) => v_ + "enga" ;
    VP (Imp Pl P1) => v_ + "engamos" ;
    VP (Imp Pl P2) => v_ + "enid" ;
    VP (Imp Pl P3) => v_ + "engan" ;
    VP (Pass Sg Masc) => v_ + "enido" ;
    VP (Pass Sg Fem) => v_ + "enida" ;
    VP (Pass Pl Masc) => v_ + "enidos" ;
    VP (Pass Pl Fem) => v_ + "enidas"
    }
  } ;

oper romper_13 : Str -> Verbum = \romper -> 
  let ro_ = Predef.tk 4 romper in
 {s = table {
    VI Infn=> ro_ + "mper" ;
    VI Ger => ro_ + "mpiendo" ;
    VI Part => ro_ + "to" ;
    VP (Pres Ind Sg P1) => ro_ + "mpo" ;
    VP (Pres Ind Sg P2) => ro_ + "mpes" ;
    VP (Pres Ind Sg P3) => ro_ + "mpe" ;
    VP (Pres Ind Pl P1) => ro_ + "mpemos" ;
    VP (Pres Ind Pl P2) => ro_ + "mp�is" ;
    VP (Pres Ind Pl P3) => ro_ + "mpen" ;
    VP (Pres Subj Sg P1) => ro_ + "mpa" ;
    VP (Pres Subj Sg P2) => ro_ + "mpas" ;
    VP (Pres Subj Sg P3) => ro_ + "mpa" ;
    VP (Pres Subj Pl P1) => ro_ + "mpamos" ;
    VP (Pres Subj Pl P2) => ro_ + "mp�is" ;
    VP (Pres Subj Pl P3) => ro_ + "mpan" ;
    VP (Past Ind Sg P1) => ro_ + "mp�a" ;
    VP (Past Ind Sg P2) => ro_ + "mp�as" ;
    VP (Past Ind Sg P3) => ro_ + "mp�a" ;
    VP (Past Ind Pl P1) => ro_ + "mp�amos" ;
    VP (Past Ind Pl P2) => ro_ + "mp�ais" ;
    VP (Past Ind Pl P3) => ro_ + "mp�an" ;
    VP (Past Subj Sg P1) => variants {ro_ + "mpiera" ; ro_ + "mpiese"} ;
    VP (Past Subj Sg P2) => variants {ro_ + "mpieras" ; ro_ + "mpieses"} ;
    VP (Past Subj Sg P3) => variants {ro_ + "mpiera" ; ro_ + "mpiese"} ;
    VP (Past Subj Pl P1) => variants {ro_ + "mpi�ramos" ; ro_ + "mpi�semos"} ;
    VP (Past Subj Pl P2) => variants {ro_ + "mpierais" ; ro_ + "mpieseis"} ;
    VP (Past Subj Pl P3) => variants {ro_ + "mpieran" ; ro_ + "mpiesen"} ;
    VP (Pret Sg P1) => ro_ + "mp�" ;
    VP (Pret Sg P2) => ro_ + "mpiste" ;
    VP (Pret Sg P3) => ro_ + "mpi�" ;
    VP (Pret Pl P1) => ro_ + "mpimos" ;
    VP (Pret Pl P2) => ro_ + "mpisteis" ;
    VP (Pret Pl P3) => ro_ + "mpieron" ;
    VP (Fut Ind Sg P1) => ro_ + "mper�" ;
    VP (Fut Ind Sg P2) => ro_ + "mper�s" ;
    VP (Fut Ind Sg P3) => ro_ + "mper�" ;
    VP (Fut Ind Pl P1) => ro_ + "mperemos" ;
    VP (Fut Ind Pl P2) => ro_ + "mper�is" ;
    VP (Fut Ind Pl P3) => ro_ + "mper�n" ;
    VP (Fut Subj Sg P1) => ro_ + "mpiere" ;
    VP (Fut Subj Sg P2) => ro_ + "mpieres" ;
    VP (Fut Subj Sg P3) => ro_ + "mpiere" ;
    VP (Fut Subj Pl P1) => ro_ + "mpi�remos" ;
    VP (Fut Subj Pl P2) => ro_ + "mpiereis" ;
    VP (Fut Subj Pl P3) => ro_ + "mpieren" ;
    VP (Cond Sg P1) => ro_ + "mper�a" ;
    VP (Cond Sg P2) => ro_ + "mper�as" ;
    VP (Cond Sg P3) => ro_ + "mper�a" ;
    VP (Cond Pl P1) => ro_ + "mper�amos" ;
    VP (Cond Pl P2) => ro_ + "mper�ais" ;
    VP (Cond Pl P3) => ro_ + "mper�an" ;
    VP (Imp Sg P1) => variants {} ;
    VP (Imp Sg P2) => ro_ + "mpe" ;
    VP (Imp Sg P3) => ro_ + "mpa" ;
    VP (Imp Pl P1) => ro_ + "mpamos" ;
    VP (Imp Pl P2) => ro_ + "mped" ;
    VP (Imp Pl P3) => ro_ + "mpan" ;
    VP (Pass Sg Masc) => ro_ + "to" ;
    VP (Pass Sg Fem) => ro_ + "ta" ;
    VP (Pass Pl Masc) => ro_ + "tos" ;
    VP (Pass Pl Fem) => ro_ + "tas"
    }
  } ;

oper adir_14 : Str -> Verbum = \adir -> 
  let adir_ = Predef.tk 0 adir in
 {s = table {
    VI Infn=> adir_ + "" ;
    VI Ger => variants {} ;
    VI Part => variants {} ;
    VP (Pres Ind Sg P1) => variants {} ;
    VP (Pres Ind Sg P2) => variants {} ;
    VP (Pres Ind Sg P3) => variants {} ;
    VP (Pres Ind Pl P1) => variants {} ;
    VP (Pres Ind Pl P2) => variants {} ;
    VP (Pres Ind Pl P3) => variants {} ;
    VP (Pres Subj Sg P1) => variants {} ;
    VP (Pres Subj Sg P2) => variants {} ;
    VP (Pres Subj Sg P3) => variants {} ;
    VP (Pres Subj Pl P1) => variants {} ;
    VP (Pres Subj Pl P2) => variants {} ;
    VP (Pres Subj Pl P3) => variants {} ;
    VP (Past Ind Sg P1) => variants {} ;
    VP (Past Ind Sg P2) => variants {} ;
    VP (Past Ind Sg P3) => variants {} ;
    VP (Past Ind Pl P1) => variants {} ;
    VP (Past Ind Pl P2) => variants {} ;
    VP (Past Ind Pl P3) => variants {} ;
    VP (Past Subj Sg P1) => variants {} ;
    VP (Past Subj Sg P2) => variants {} ;
    VP (Past Subj Sg P3) => variants {} ;
    VP (Past Subj Pl P1) => variants {} ;
    VP (Past Subj Pl P2) => variants {} ;
    VP (Past Subj Pl P3) => variants {} ;
    VP (Pret Sg P1) => variants {} ;
    VP (Pret Sg P2) => variants {} ;
    VP (Pret Sg P3) => variants {} ;
    VP (Pret Pl P1) => variants {} ;
    VP (Pret Pl P2) => variants {} ;
    VP (Pret Pl P3) => variants {} ;
    VP (Fut Ind Sg P1) => variants {} ;
    VP (Fut Ind Sg P2) => variants {} ;
    VP (Fut Ind Sg P3) => variants {} ;
    VP (Fut Ind Pl P1) => variants {} ;
    VP (Fut Ind Pl P2) => variants {} ;
    VP (Fut Ind Pl P3) => variants {} ;
    VP (Fut Subj Sg P1) => variants {} ;
    VP (Fut Subj Sg P2) => variants {} ;
    VP (Fut Subj Sg P3) => variants {} ;
    VP (Fut Subj Pl P1) => variants {} ;
    VP (Fut Subj Pl P2) => variants {} ;
    VP (Fut Subj Pl P3) => variants {} ;
    VP (Cond Sg P1) => variants {} ;
    VP (Cond Sg P2) => variants {} ;
    VP (Cond Sg P3) => variants {} ;
    VP (Cond Pl P1) => variants {} ;
    VP (Cond Pl P2) => variants {} ;
    VP (Cond Pl P3) => variants {} ;
    VP (Imp Sg P1) => variants {} ;
    VP (Imp Sg P2) => variants {} ;
    VP (Imp Sg P3) => variants {} ;
    VP (Imp Pl P1) => variants {} ;
    VP (Imp Pl P2) => variants {} ;
    VP (Imp Pl P3) => variants {} ;
    VP (Pass Sg Masc) => variants {} ;
    VP (Pass Sg Fem) => variants {} ;
    VP (Pass Pl Masc) => variants {} ;
    VP (Pass Pl Fem) => variants {}
    }
  } ;

oper abrir_15 : Str -> Verbum = \abrir -> 
  let ab_ = Predef.tk 3 abrir in
 {s = table {
    VI Infn=> ab_ + "rir" ;
    VI Ger => ab_ + "riendo" ;
    VI Part => ab_ + "ierto" ;
    VP (Pres Ind Sg P1) => ab_ + "ro" ;
    VP (Pres Ind Sg P2) => ab_ + "res" ;
    VP (Pres Ind Sg P3) => ab_ + "re" ;
    VP (Pres Ind Pl P1) => ab_ + "rimos" ;
    VP (Pres Ind Pl P2) => ab_ + "r�s" ;
    VP (Pres Ind Pl P3) => ab_ + "ren" ;
    VP (Pres Subj Sg P1) => ab_ + "ra" ;
    VP (Pres Subj Sg P2) => ab_ + "ras" ;
    VP (Pres Subj Sg P3) => ab_ + "ra" ;
    VP (Pres Subj Pl P1) => ab_ + "ramos" ;
    VP (Pres Subj Pl P2) => ab_ + "r�is" ;
    VP (Pres Subj Pl P3) => ab_ + "ran" ;
    VP (Past Ind Sg P1) => ab_ + "r�a" ;
    VP (Past Ind Sg P2) => ab_ + "r�as" ;
    VP (Past Ind Sg P3) => ab_ + "r�a" ;
    VP (Past Ind Pl P1) => ab_ + "r�amos" ;
    VP (Past Ind Pl P2) => ab_ + "r�ais" ;
    VP (Past Ind Pl P3) => ab_ + "r�an" ;
    VP (Past Subj Sg P1) => variants {ab_ + "riera" ; ab_ + "riese"} ;
    VP (Past Subj Sg P2) => variants {ab_ + "rieras" ; ab_ + "rieses"} ;
    VP (Past Subj Sg P3) => variants {ab_ + "riera" ; ab_ + "riese"} ;
    VP (Past Subj Pl P1) => variants {ab_ + "ri�ramos" ; ab_ + "ri�semos"} ;
    VP (Past Subj Pl P2) => variants {ab_ + "rierais" ; ab_ + "rieseis"} ;
    VP (Past Subj Pl P3) => variants {ab_ + "rieran" ; ab_ + "riesen"} ;
    VP (Pret Sg P1) => ab_ + "r�" ;
    VP (Pret Sg P2) => ab_ + "riste" ;
    VP (Pret Sg P3) => ab_ + "ri�" ;
    VP (Pret Pl P1) => ab_ + "rimos" ;
    VP (Pret Pl P2) => ab_ + "risteis" ;
    VP (Pret Pl P3) => ab_ + "rieron" ;
    VP (Fut Ind Sg P1) => ab_ + "rir�" ;
    VP (Fut Ind Sg P2) => ab_ + "rir�s" ;
    VP (Fut Ind Sg P3) => ab_ + "rir�" ;
    VP (Fut Ind Pl P1) => ab_ + "riremos" ;
    VP (Fut Ind Pl P2) => ab_ + "rir�is" ;
    VP (Fut Ind Pl P3) => ab_ + "rir�n" ;
    VP (Fut Subj Sg P1) => ab_ + "riere" ;
    VP (Fut Subj Sg P2) => ab_ + "rieres" ;
    VP (Fut Subj Sg P3) => ab_ + "riere" ;
    VP (Fut Subj Pl P1) => ab_ + "ri�remos" ;
    VP (Fut Subj Pl P2) => ab_ + "riereis" ;
    VP (Fut Subj Pl P3) => ab_ + "rieren" ;
    VP (Cond Sg P1) => ab_ + "rir�a" ;
    VP (Cond Sg P2) => ab_ + "rir�as" ;
    VP (Cond Sg P3) => ab_ + "rir�a" ;
    VP (Cond Pl P1) => ab_ + "rir�amos" ;
    VP (Cond Pl P2) => ab_ + "rir�ais" ;
    VP (Cond Pl P3) => ab_ + "rir�an" ;
    VP (Imp Sg P1) => variants {} ;
    VP (Imp Sg P2) => ab_ + "re" ;
    VP (Imp Sg P3) => ab_ + "ra" ;
    VP (Imp Pl P1) => ab_ + "ramos" ;
    VP (Imp Pl P2) => ab_ + "rid" ;
    VP (Imp Pl P3) => ab_ + "ran" ;
    VP (Pass Sg Masc) => ab_ + "rido" ;
    VP (Pass Sg Fem) => ab_ + "rida" ;
    VP (Pass Pl Masc) => ab_ + "ridos" ;
    VP (Pass Pl Fem) => ab_ + "ridas"
    }
  } ;

oper abolir_16 : Str -> Verbum = \abolir -> 
  let abol_ = Predef.tk 2 abolir in
 {s = table {
    VI Infn=> abol_ + "ir" ;
    VI Ger => abol_ + "iendo" ;
    VI Part => abol_ + "ido" ;
    VP (Pres Ind Sg P1) => variants {} ;
    VP (Pres Ind Sg P2) => variants {} ;
    VP (Pres Ind Sg P3) => variants {} ;
    VP (Pres Ind Pl P1) => abol_ + "imos" ;
    VP (Pres Ind Pl P2) => abol_ + "�s" ;
    VP (Pres Ind Pl P3) => variants {} ;
    VP (Pres Subj Sg P1) => variants {} ;
    VP (Pres Subj Sg P2) => variants {} ;
    VP (Pres Subj Sg P3) => variants {} ;
    VP (Pres Subj Pl P1) => variants {} ;
    VP (Pres Subj Pl P2) => variants {} ;
    VP (Pres Subj Pl P3) => variants {} ;
    VP (Past Ind Sg P1) => abol_ + "�a" ;
    VP (Past Ind Sg P2) => abol_ + "�as" ;
    VP (Past Ind Sg P3) => abol_ + "�a" ;
    VP (Past Ind Pl P1) => abol_ + "�amos" ;
    VP (Past Ind Pl P2) => abol_ + "�ais" ;
    VP (Past Ind Pl P3) => abol_ + "�an" ;
    VP (Past Subj Sg P1) => variants {abol_ + "iera" ; abol_ + "iese"} ;
    VP (Past Subj Sg P2) => variants {abol_ + "ieras" ; abol_ + "ieses"} ;
    VP (Past Subj Sg P3) => variants {abol_ + "iera" ; abol_ + "iese"} ;
    VP (Past Subj Pl P1) => variants {abol_ + "i�ramos" ; abol_ + "i�semos"} ;
    VP (Past Subj Pl P2) => variants {abol_ + "ierais" ; abol_ + "ieseis"} ;
    VP (Past Subj Pl P3) => variants {abol_ + "ieran" ; abol_ + "iesen"} ;
    VP (Pret Sg P1) => abol_ + "�" ;
    VP (Pret Sg P2) => abol_ + "iste" ;
    VP (Pret Sg P3) => abol_ + "i�" ;
    VP (Pret Pl P1) => abol_ + "imos" ;
    VP (Pret Pl P2) => abol_ + "isteis" ;
    VP (Pret Pl P3) => abol_ + "ieron" ;
    VP (Fut Ind Sg P1) => abol_ + "ir�" ;
    VP (Fut Ind Sg P2) => abol_ + "ir�s" ;
    VP (Fut Ind Sg P3) => abol_ + "ir�" ;
    VP (Fut Ind Pl P1) => abol_ + "iremos" ;
    VP (Fut Ind Pl P2) => abol_ + "ir�is" ;
    VP (Fut Ind Pl P3) => abol_ + "ir�n" ;
    VP (Fut Subj Sg P1) => abol_ + "iere" ;
    VP (Fut Subj Sg P2) => abol_ + "ieres" ;
    VP (Fut Subj Sg P3) => abol_ + "iere" ;
    VP (Fut Subj Pl P1) => abol_ + "i�remos" ;
    VP (Fut Subj Pl P2) => abol_ + "iereis" ;
    VP (Fut Subj Pl P3) => abol_ + "ieren" ;
    VP (Cond Sg P1) => abol_ + "ir�a" ;
    VP (Cond Sg P2) => abol_ + "ir�as" ;
    VP (Cond Sg P3) => abol_ + "ir�a" ;
    VP (Cond Pl P1) => abol_ + "ir�amos" ;
    VP (Cond Pl P2) => abol_ + "ir�ais" ;
    VP (Cond Pl P3) => abol_ + "ir�an" ;
    VP (Imp Sg P1) => variants {} ;
    VP (Imp Sg P2) => variants {} ;
    VP (Imp Sg P3) => variants {} ;
    VP (Imp Pl P1) => variants {} ;
    VP (Imp Pl P2) => abol_ + "id" ;
    VP (Imp Pl P3) => variants {} ;
    VP (Pass Sg Masc) => abol_ + "ido" ;
    VP (Pass Sg Fem) => abol_ + "ida" ;
    VP (Pass Pl Masc) => abol_ + "idos" ;
    VP (Pass Pl Fem) => abol_ + "idas"
    }
  } ;

oper ahincar_17 : Str -> Verbum = \ahincar -> 
  let ah_ = Predef.tk 5 ahincar in
 {s = table {
    VI Infn=> ah_ + "incar" ;
    VI Ger => ah_ + "incando" ;
    VI Part => ah_ + "incado" ;
    VP (Pres Ind Sg P1) => ah_ + "�nco" ;
    VP (Pres Ind Sg P2) => ah_ + "�ncas" ;
    VP (Pres Ind Sg P3) => ah_ + "�nca" ;
    VP (Pres Ind Pl P1) => ah_ + "incamos" ;
    VP (Pres Ind Pl P2) => ah_ + "inc�is" ;
    VP (Pres Ind Pl P3) => ah_ + "�ncan" ;
    VP (Pres Subj Sg P1) => ah_ + "�nque" ;
    VP (Pres Subj Sg P2) => ah_ + "�nques" ;
    VP (Pres Subj Sg P3) => ah_ + "�nque" ;
    VP (Pres Subj Pl P1) => ah_ + "inquemos" ;
    VP (Pres Subj Pl P2) => ah_ + "inqu�is" ;
    VP (Pres Subj Pl P3) => ah_ + "�nquen" ;
    VP (Past Ind Sg P1) => ah_ + "incaba" ;
    VP (Past Ind Sg P2) => ah_ + "incabas" ;
    VP (Past Ind Sg P3) => ah_ + "incaba" ;
    VP (Past Ind Pl P1) => ah_ + "inc�bamos" ;
    VP (Past Ind Pl P2) => ah_ + "incabais" ;
    VP (Past Ind Pl P3) => ah_ + "incaban" ;
    VP (Past Subj Sg P1) => variants {ah_ + "incara" ; ah_ + "incase"} ;
    VP (Past Subj Sg P2) => variants {ah_ + "incaras" ; ah_ + "incases"} ;
    VP (Past Subj Sg P3) => variants {ah_ + "incara" ; ah_ + "incase"} ;
    VP (Past Subj Pl P1) => variants {ah_ + "inc�ramos" ; ah_ + "inc�semos"} ;
    VP (Past Subj Pl P2) => variants {ah_ + "incarais" ; ah_ + "incaseis"} ;
    VP (Past Subj Pl P3) => variants {ah_ + "incaran" ; ah_ + "incasen"} ;
    VP (Pret Sg P1) => ah_ + "inqu�" ;
    VP (Pret Sg P2) => ah_ + "incaste" ;
    VP (Pret Sg P3) => ah_ + "inc�" ;
    VP (Pret Pl P1) => ah_ + "incamos" ;
    VP (Pret Pl P2) => ah_ + "incasteis" ;
    VP (Pret Pl P3) => ah_ + "incaron" ;
    VP (Fut Ind Sg P1) => ah_ + "incar�" ;
    VP (Fut Ind Sg P2) => ah_ + "incar�s" ;
    VP (Fut Ind Sg P3) => ah_ + "incar�" ;
    VP (Fut Ind Pl P1) => ah_ + "incaremos" ;
    VP (Fut Ind Pl P2) => ah_ + "incar�is" ;
    VP (Fut Ind Pl P3) => ah_ + "incar�n" ;
    VP (Fut Subj Sg P1) => ah_ + "incare" ;
    VP (Fut Subj Sg P2) => ah_ + "incares" ;
    VP (Fut Subj Sg P3) => ah_ + "incare" ;
    VP (Fut Subj Pl P1) => ah_ + "inc�remos" ;
    VP (Fut Subj Pl P2) => ah_ + "incareis" ;
    VP (Fut Subj Pl P3) => ah_ + "incaren" ;
    VP (Cond Sg P1) => ah_ + "incar�a" ;
    VP (Cond Sg P2) => ah_ + "incar�as" ;
    VP (Cond Sg P3) => ah_ + "incar�a" ;
    VP (Cond Pl P1) => ah_ + "incar�amos" ;
    VP (Cond Pl P2) => ah_ + "incar�ais" ;
    VP (Cond Pl P3) => ah_ + "incar�an" ;
    VP (Imp Sg P1) => variants {} ;
    VP (Imp Sg P2) => ah_ + "�nca" ;
    VP (Imp Sg P3) => ah_ + "�nque" ;
    VP (Imp Pl P1) => ah_ + "inquemos" ;
    VP (Imp Pl P2) => ah_ + "incad" ;
    VP (Imp Pl P3) => ah_ + "�nquen" ;
    VP (Pass Sg Masc) => ah_ + "incado" ;
    VP (Pass Sg Fem) => ah_ + "incada" ;
    VP (Pass Pl Masc) => ah_ + "incados" ;
    VP (Pass Pl Fem) => ah_ + "incadas"
    }
  } ;

oper andar_18 : Str -> Verbum = \andar -> 
  let and_ = Predef.tk 2 andar in
 {s = table {
    VI Infn=> and_ + "ar" ;
    VI Ger => and_ + "ando" ;
    VI Part => and_ + "ado" ;
    VP (Pres Ind Sg P1) => and_ + "o" ;
    VP (Pres Ind Sg P2) => and_ + "as" ;
    VP (Pres Ind Sg P3) => and_ + "a" ;
    VP (Pres Ind Pl P1) => and_ + "amos" ;
    VP (Pres Ind Pl P2) => and_ + "�is" ;
    VP (Pres Ind Pl P3) => and_ + "an" ;
    VP (Pres Subj Sg P1) => and_ + "e" ;
    VP (Pres Subj Sg P2) => and_ + "es" ;
    VP (Pres Subj Sg P3) => and_ + "e" ;
    VP (Pres Subj Pl P1) => and_ + "emos" ;
    VP (Pres Subj Pl P2) => and_ + "�is" ;
    VP (Pres Subj Pl P3) => and_ + "en" ;
    VP (Past Ind Sg P1) => and_ + "aba" ;
    VP (Past Ind Sg P2) => and_ + "abas" ;
    VP (Past Ind Sg P3) => and_ + "aba" ;
    VP (Past Ind Pl P1) => and_ + "�bamos" ;
    VP (Past Ind Pl P2) => and_ + "abais" ;
    VP (Past Ind Pl P3) => and_ + "aban" ;
    VP (Past Subj Sg P1) => variants {and_ + "uviera" ; and_ + "uviese"} ;
    VP (Past Subj Sg P2) => variants {and_ + "uvieras" ; and_ + "uvieses"} ;
    VP (Past Subj Sg P3) => variants {and_ + "uviera" ; and_ + "uviese"} ;
    VP (Past Subj Pl P1) => variants {and_ + "uvi�ramos" ; and_ + "uvi�semos"} ;
    VP (Past Subj Pl P2) => variants {and_ + "uvierais" ; and_ + "uvieseis"} ;
    VP (Past Subj Pl P3) => variants {and_ + "uvieran" ; and_ + "uviesen"} ;
    VP (Pret Sg P1) => and_ + "uve" ;
    VP (Pret Sg P2) => and_ + "uviste" ;
    VP (Pret Sg P3) => and_ + "uvo" ;
    VP (Pret Pl P1) => and_ + "uvimos" ;
    VP (Pret Pl P2) => and_ + "uvisteis" ;
    VP (Pret Pl P3) => and_ + "uvieron" ;
    VP (Fut Ind Sg P1) => and_ + "ar�" ;
    VP (Fut Ind Sg P2) => and_ + "ar�s" ;
    VP (Fut Ind Sg P3) => and_ + "ar�" ;
    VP (Fut Ind Pl P1) => and_ + "aremos" ;
    VP (Fut Ind Pl P2) => and_ + "ar�is" ;
    VP (Fut Ind Pl P3) => and_ + "ar�n" ;
    VP (Fut Subj Sg P1) => and_ + "uviere" ;
    VP (Fut Subj Sg P2) => and_ + "uvieres" ;
    VP (Fut Subj Sg P3) => and_ + "uviere" ;
    VP (Fut Subj Pl P1) => and_ + "uvi�remos" ;
    VP (Fut Subj Pl P2) => and_ + "uviereis" ;
    VP (Fut Subj Pl P3) => and_ + "uvieren" ;
    VP (Cond Sg P1) => and_ + "ar�a" ;
    VP (Cond Sg P2) => and_ + "ar�as" ;
    VP (Cond Sg P3) => and_ + "ar�a" ;
    VP (Cond Pl P1) => and_ + "ar�amos" ;
    VP (Cond Pl P2) => and_ + "ar�ais" ;
    VP (Cond Pl P3) => and_ + "ar�an" ;
    VP (Imp Sg P1) => variants {} ;
    VP (Imp Sg P2) => and_ + "a" ;
    VP (Imp Sg P3) => and_ + "e" ;
    VP (Imp Pl P1) => and_ + "emos" ;
    VP (Imp Pl P2) => and_ + "ad" ;
    VP (Imp Pl P3) => and_ + "en" ;
    VP (Pass Sg Masc) => and_ + "ado" ;
    VP (Pass Sg Fem) => and_ + "ada" ;
    VP (Pass Pl Masc) => and_ + "ados" ;
    VP (Pass Pl Fem) => and_ + "adas"
    }
  } ;

oper astri�ir_19 : Str -> Verbum = \astri�ir -> 
  let astri�_ = Predef.tk 2 astri�ir in
 {s = table {
    VI Infn=> astri�_ + "ir" ;
    VI Ger => astri�_ + "endo" ;
    VI Part => astri�_ + "ido" ;
    VP (Pres Ind Sg P1) => astri�_ + "o" ;
    VP (Pres Ind Sg P2) => astri�_ + "es" ;
    VP (Pres Ind Sg P3) => astri�_ + "e" ;
    VP (Pres Ind Pl P1) => astri�_ + "imos" ;
    VP (Pres Ind Pl P2) => astri�_ + "�s" ;
    VP (Pres Ind Pl P3) => astri�_ + "en" ;
    VP (Pres Subj Sg P1) => astri�_ + "a" ;
    VP (Pres Subj Sg P2) => astri�_ + "as" ;
    VP (Pres Subj Sg P3) => astri�_ + "a" ;
    VP (Pres Subj Pl P1) => astri�_ + "amos" ;
    VP (Pres Subj Pl P2) => astri�_ + "�is" ;
    VP (Pres Subj Pl P3) => astri�_ + "an" ;
    VP (Past Ind Sg P1) => astri�_ + "�a" ;
    VP (Past Ind Sg P2) => astri�_ + "�as" ;
    VP (Past Ind Sg P3) => astri�_ + "�a" ;
    VP (Past Ind Pl P1) => astri�_ + "�amos" ;
    VP (Past Ind Pl P2) => astri�_ + "�ais" ;
    VP (Past Ind Pl P3) => astri�_ + "�an" ;
    VP (Past Subj Sg P1) => variants {astri�_ + "era" ; astri�_ + "ese"} ;
    VP (Past Subj Sg P2) => variants {astri�_ + "eras" ; astri�_ + "eses"} ;
    VP (Past Subj Sg P3) => variants {astri�_ + "era" ; astri�_ + "ese"} ;
    VP (Past Subj Pl P1) => variants {astri�_ + "�ramos" ; astri�_ + "�semos"} ;
    VP (Past Subj Pl P2) => variants {astri�_ + "erais" ; astri�_ + "eseis"} ;
    VP (Past Subj Pl P3) => variants {astri�_ + "eran" ; astri�_ + "esen"} ;
    VP (Pret Sg P1) => astri�_ + "�" ;
    VP (Pret Sg P2) => astri�_ + "iste" ;
    VP (Pret Sg P3) => astri�_ + "�" ;
    VP (Pret Pl P1) => astri�_ + "imos" ;
    VP (Pret Pl P2) => astri�_ + "isteis" ;
    VP (Pret Pl P3) => astri�_ + "eron" ;
    VP (Fut Ind Sg P1) => astri�_ + "ir�" ;
    VP (Fut Ind Sg P2) => astri�_ + "ir�s" ;
    VP (Fut Ind Sg P3) => astri�_ + "ir�" ;
    VP (Fut Ind Pl P1) => astri�_ + "iremos" ;
    VP (Fut Ind Pl P2) => astri�_ + "ir�is" ;
    VP (Fut Ind Pl P3) => astri�_ + "ir�n" ;
    VP (Fut Subj Sg P1) => astri�_ + "ere" ;
    VP (Fut Subj Sg P2) => astri�_ + "eres" ;
    VP (Fut Subj Sg P3) => astri�_ + "ere" ;
    VP (Fut Subj Pl P1) => astri�_ + "�remos" ;
    VP (Fut Subj Pl P2) => astri�_ + "ereis" ;
    VP (Fut Subj Pl P3) => astri�_ + "eren" ;
    VP (Cond Sg P1) => astri�_ + "ir�a" ;
    VP (Cond Sg P2) => astri�_ + "ir�as" ;
    VP (Cond Sg P3) => astri�_ + "ir�a" ;
    VP (Cond Pl P1) => astri�_ + "ir�amos" ;
    VP (Cond Pl P2) => astri�_ + "ir�ais" ;
    VP (Cond Pl P3) => astri�_ + "ir�an" ;
    VP (Imp Sg P1) => variants {} ;
    VP (Imp Sg P2) => astri�_ + "e" ;
    VP (Imp Sg P3) => astri�_ + "a" ;
    VP (Imp Pl P1) => astri�_ + "amos" ;
    VP (Imp Pl P2) => astri�_ + "id" ;
    VP (Imp Pl P3) => astri�_ + "an" ;
    VP (Pass Sg Masc) => astri�_ + "ido" ;
    VP (Pass Sg Fem) => astri�_ + "ida" ;
    VP (Pass Pl Masc) => astri�_ + "idos" ;
    VP (Pass Pl Fem) => astri�_ + "idas"
    }
  } ;

oper abstraer_20 : Str -> Verbum = \abstraer -> 
  let abstra_ = Predef.tk 2 abstraer in
 {s = table {
    VI Infn=> abstra_ + "er" ;
    VI Ger => abstra_ + "yendo" ;
    VI Part => abstra_ + "�do" ;
    VP (Pres Ind Sg P1) => abstra_ + "o" ;
    VP (Pres Ind Sg P2) => abstra_ + "es" ;
    VP (Pres Ind Sg P3) => abstra_ + "e" ;
    VP (Pres Ind Pl P1) => abstra_ + "emos" ;
    VP (Pres Ind Pl P2) => abstra_ + "�is" ;
    VP (Pres Ind Pl P3) => abstra_ + "en" ;
    VP (Pres Subj Sg P1) => abstra_ + "a" ;
    VP (Pres Subj Sg P2) => abstra_ + "as" ;
    VP (Pres Subj Sg P3) => abstra_ + "a" ;
    VP (Pres Subj Pl P1) => abstra_ + "amos" ;
    VP (Pres Subj Pl P2) => abstra_ + "�is" ;
    VP (Pres Subj Pl P3) => abstra_ + "an" ;
    VP (Past Ind Sg P1) => abstra_ + "�a" ;
    VP (Past Ind Sg P2) => abstra_ + "�as" ;
    VP (Past Ind Sg P3) => abstra_ + "�a" ;
    VP (Past Ind Pl P1) => abstra_ + "�amos" ;
    VP (Past Ind Pl P2) => abstra_ + "�ais" ;
    VP (Past Ind Pl P3) => abstra_ + "�an" ;
    VP (Past Subj Sg P1) => variants {abstra_ + "yera" ; abstra_ + "yese"} ;
    VP (Past Subj Sg P2) => variants {abstra_ + "yeras" ; abstra_ + "yeses"} ;
    VP (Past Subj Sg P3) => variants {abstra_ + "yera" ; abstra_ + "yese"} ;
    VP (Past Subj Pl P1) => variants {abstra_ + "y�ramos" ; abstra_ + "y�semos"} ;
    VP (Past Subj Pl P2) => variants {abstra_ + "yerais" ; abstra_ + "yeseis"} ;
    VP (Past Subj Pl P3) => variants {abstra_ + "yeran" ; abstra_ + "yesen"} ;
    VP (Pret Sg P1) => abstra_ + "�" ;
    VP (Pret Sg P2) => abstra_ + "�ste" ;
    VP (Pret Sg P3) => abstra_ + "y�" ;
    VP (Pret Pl P1) => abstra_ + "�mos" ;
    VP (Pret Pl P2) => abstra_ + "�steis" ;
    VP (Pret Pl P3) => abstra_ + "yeron" ;
    VP (Fut Ind Sg P1) => abstra_ + "er�" ;
    VP (Fut Ind Sg P2) => abstra_ + "er�s" ;
    VP (Fut Ind Sg P3) => abstra_ + "er�" ;
    VP (Fut Ind Pl P1) => abstra_ + "eremos" ;
    VP (Fut Ind Pl P2) => abstra_ + "er�is" ;
    VP (Fut Ind Pl P3) => abstra_ + "er�n" ;
    VP (Fut Subj Sg P1) => abstra_ + "yere" ;
    VP (Fut Subj Sg P2) => abstra_ + "yeres" ;
    VP (Fut Subj Sg P3) => abstra_ + "yere" ;
    VP (Fut Subj Pl P1) => abstra_ + "y�remos" ;
    VP (Fut Subj Pl P2) => abstra_ + "yereis" ;
    VP (Fut Subj Pl P3) => abstra_ + "yeren" ;
    VP (Cond Sg P1) => abstra_ + "er�a" ;
    VP (Cond Sg P2) => abstra_ + "er�as" ;
    VP (Cond Sg P3) => abstra_ + "er�a" ;
    VP (Cond Pl P1) => abstra_ + "er�amos" ;
    VP (Cond Pl P2) => abstra_ + "er�ais" ;
    VP (Cond Pl P3) => abstra_ + "er�an" ;
    VP (Imp Sg P1) => variants {} ;
    VP (Imp Sg P2) => abstra_ + "e" ;
    VP (Imp Sg P3) => abstra_ + "a" ;
    VP (Imp Pl P1) => abstra_ + "amos" ;
    VP (Imp Pl P2) => abstra_ + "ed" ;
    VP (Imp Pl P3) => abstra_ + "an" ;
    VP (Pass Sg Masc) => abstra_ + "�do" ;
    VP (Pass Sg Fem) => abstra_ + "�da" ;
    VP (Pass Pl Masc) => abstra_ + "�dos" ;
    VP (Pass Pl Fem) => abstra_ + "�das"
    }
  } ;

oper cocer_21 : Str -> Verbum = \cocer -> 
  let c_ = Predef.tk 4 cocer in
 {s = table {
    VI Infn=> c_ + "ocer" ;
    VI Ger => c_ + "ociendo" ;
    VI Part => c_ + "ocido" ;
    VP (Pres Ind Sg P1) => c_ + "uezo" ;
    VP (Pres Ind Sg P2) => c_ + "ueces" ;
    VP (Pres Ind Sg P3) => c_ + "uece" ;
    VP (Pres Ind Pl P1) => c_ + "ocemos" ;
    VP (Pres Ind Pl P2) => c_ + "oc�is" ;
    VP (Pres Ind Pl P3) => c_ + "uecen" ;
    VP (Pres Subj Sg P1) => c_ + "ueza" ;
    VP (Pres Subj Sg P2) => c_ + "uezas" ;
    VP (Pres Subj Sg P3) => c_ + "ueza" ;
    VP (Pres Subj Pl P1) => c_ + "ozamos" ;
    VP (Pres Subj Pl P2) => c_ + "oz�is" ;
    VP (Pres Subj Pl P3) => c_ + "uezan" ;
    VP (Past Ind Sg P1) => c_ + "oc�a" ;
    VP (Past Ind Sg P2) => c_ + "oc�as" ;
    VP (Past Ind Sg P3) => c_ + "oc�a" ;
    VP (Past Ind Pl P1) => c_ + "oc�amos" ;
    VP (Past Ind Pl P2) => c_ + "oc�ais" ;
    VP (Past Ind Pl P3) => c_ + "oc�an" ;
    VP (Past Subj Sg P1) => variants {c_ + "ociera" ; c_ + "ociese"} ;
    VP (Past Subj Sg P2) => variants {c_ + "ocieras" ; c_ + "ocieses"} ;
    VP (Past Subj Sg P3) => variants {c_ + "ociera" ; c_ + "ociese"} ;
    VP (Past Subj Pl P1) => variants {c_ + "oci�ramos" ; c_ + "oci�semos"} ;
    VP (Past Subj Pl P2) => variants {c_ + "ocierais" ; c_ + "ocieseis"} ;
    VP (Past Subj Pl P3) => variants {c_ + "ocieran" ; c_ + "ociesen"} ;
    VP (Pret Sg P1) => c_ + "oc�" ;
    VP (Pret Sg P2) => c_ + "ociste" ;
    VP (Pret Sg P3) => c_ + "oci�" ;
    VP (Pret Pl P1) => c_ + "ocimos" ;
    VP (Pret Pl P2) => c_ + "ocisteis" ;
    VP (Pret Pl P3) => c_ + "ocieron" ;
    VP (Fut Ind Sg P1) => c_ + "ocer�" ;
    VP (Fut Ind Sg P2) => c_ + "ocer�s" ;
    VP (Fut Ind Sg P3) => c_ + "ocer�" ;
    VP (Fut Ind Pl P1) => c_ + "oceremos" ;
    VP (Fut Ind Pl P2) => c_ + "ocer�is" ;
    VP (Fut Ind Pl P3) => c_ + "ocer�n" ;
    VP (Fut Subj Sg P1) => c_ + "ociere" ;
    VP (Fut Subj Sg P2) => c_ + "ocieres" ;
    VP (Fut Subj Sg P3) => c_ + "ociere" ;
    VP (Fut Subj Pl P1) => c_ + "oci�remos" ;
    VP (Fut Subj Pl P2) => c_ + "ociereis" ;
    VP (Fut Subj Pl P3) => c_ + "ocieren" ;
    VP (Cond Sg P1) => c_ + "ocer�a" ;
    VP (Cond Sg P2) => c_ + "ocer�as" ;
    VP (Cond Sg P3) => c_ + "ocer�a" ;
    VP (Cond Pl P1) => c_ + "ocer�amos" ;
    VP (Cond Pl P2) => c_ + "ocer�ais" ;
    VP (Cond Pl P3) => c_ + "ocer�an" ;
    VP (Imp Sg P1) => variants {} ;
    VP (Imp Sg P2) => c_ + "uece" ;
    VP (Imp Sg P3) => c_ + "ueza" ;
    VP (Imp Pl P1) => c_ + "ozamos" ;
    VP (Imp Pl P2) => c_ + "oced" ;
    VP (Imp Pl P3) => c_ + "uezan" ;
    VP (Pass Sg Masc) => c_ + "ocido" ;
    VP (Pass Sg Fem) => c_ + "ocida" ;
    VP (Pass Pl Masc) => c_ + "ocidos" ;
    VP (Pass Pl Fem) => c_ + "ocidas"
    }
  } ;

oper abnegar_22 : Str -> Verbum = \abnegar -> 
  let abn_ = Predef.tk 4 abnegar in
 {s = table {
    VI Infn=> abn_ + "egar" ;
    VI Ger => abn_ + "egando" ;
    VI Part => abn_ + "egado" ;
    VP (Pres Ind Sg P1) => abn_ + "iego" ;
    VP (Pres Ind Sg P2) => abn_ + "iegas" ;
    VP (Pres Ind Sg P3) => abn_ + "iega" ;
    VP (Pres Ind Pl P1) => abn_ + "egamos" ;
    VP (Pres Ind Pl P2) => abn_ + "eg�is" ;
    VP (Pres Ind Pl P3) => abn_ + "iegan" ;
    VP (Pres Subj Sg P1) => abn_ + "iegue" ;
    VP (Pres Subj Sg P2) => abn_ + "iegues" ;
    VP (Pres Subj Sg P3) => abn_ + "iegue" ;
    VP (Pres Subj Pl P1) => abn_ + "eguemos" ;
    VP (Pres Subj Pl P2) => abn_ + "egu�is" ;
    VP (Pres Subj Pl P3) => abn_ + "ieguen" ;
    VP (Past Ind Sg P1) => abn_ + "egaba" ;
    VP (Past Ind Sg P2) => abn_ + "egabas" ;
    VP (Past Ind Sg P3) => abn_ + "egaba" ;
    VP (Past Ind Pl P1) => abn_ + "eg�bamos" ;
    VP (Past Ind Pl P2) => abn_ + "egabais" ;
    VP (Past Ind Pl P3) => abn_ + "egaban" ;
    VP (Past Subj Sg P1) => variants {abn_ + "egara" ; abn_ + "egase"} ;
    VP (Past Subj Sg P2) => variants {abn_ + "egaras" ; abn_ + "egases"} ;
    VP (Past Subj Sg P3) => variants {abn_ + "egara" ; abn_ + "egase"} ;
    VP (Past Subj Pl P1) => variants {abn_ + "eg�ramos" ; abn_ + "eg�semos"} ;
    VP (Past Subj Pl P2) => variants {abn_ + "egarais" ; abn_ + "egaseis"} ;
    VP (Past Subj Pl P3) => variants {abn_ + "egaran" ; abn_ + "egasen"} ;
    VP (Pret Sg P1) => abn_ + "egu�" ;
    VP (Pret Sg P2) => abn_ + "egaste" ;
    VP (Pret Sg P3) => abn_ + "eg�" ;
    VP (Pret Pl P1) => abn_ + "egamos" ;
    VP (Pret Pl P2) => abn_ + "egasteis" ;
    VP (Pret Pl P3) => abn_ + "egaron" ;
    VP (Fut Ind Sg P1) => abn_ + "egar�" ;
    VP (Fut Ind Sg P2) => abn_ + "egar�s" ;
    VP (Fut Ind Sg P3) => abn_ + "egar�" ;
    VP (Fut Ind Pl P1) => abn_ + "egaremos" ;
    VP (Fut Ind Pl P2) => abn_ + "egar�is" ;
    VP (Fut Ind Pl P3) => abn_ + "egar�n" ;
    VP (Fut Subj Sg P1) => abn_ + "egare" ;
    VP (Fut Subj Sg P2) => abn_ + "egares" ;
    VP (Fut Subj Sg P3) => abn_ + "egare" ;
    VP (Fut Subj Pl P1) => abn_ + "eg�remos" ;
    VP (Fut Subj Pl P2) => abn_ + "egareis" ;
    VP (Fut Subj Pl P3) => abn_ + "egaren" ;
    VP (Cond Sg P1) => abn_ + "egar�a" ;
    VP (Cond Sg P2) => abn_ + "egar�as" ;
    VP (Cond Sg P3) => abn_ + "egar�a" ;
    VP (Cond Pl P1) => abn_ + "egar�amos" ;
    VP (Cond Pl P2) => abn_ + "egar�ais" ;
    VP (Cond Pl P3) => abn_ + "egar�an" ;
    VP (Imp Sg P1) => variants {} ;
    VP (Imp Sg P2) => abn_ + "iega" ;
    VP (Imp Sg P3) => abn_ + "iegue" ;
    VP (Imp Pl P1) => abn_ + "eguemos" ;
    VP (Imp Pl P2) => abn_ + "egad" ;
    VP (Imp Pl P3) => abn_ + "ieguen" ;
    VP (Pass Sg Masc) => abn_ + "egado" ;
    VP (Pass Sg Fem) => abn_ + "egada" ;
    VP (Pass Pl Masc) => abn_ + "egados" ;
    VP (Pass Pl Fem) => abn_ + "egadas"
    }
  } ;

oper adormir_23 : Str -> Verbum = \adormir -> 
  let ad_ = Predef.tk 5 adormir in
 {s = table {
    VI Infn=> ad_ + "ormir" ;
    VI Ger => ad_ + "urmiendo" ;
    VI Part => ad_ + "ormido" ;
    VP (Pres Ind Sg P1) => ad_ + "uermo" ;
    VP (Pres Ind Sg P2) => ad_ + "uermes" ;
    VP (Pres Ind Sg P3) => ad_ + "uerme" ;
    VP (Pres Ind Pl P1) => ad_ + "ormimos" ;
    VP (Pres Ind Pl P2) => ad_ + "orm�s" ;
    VP (Pres Ind Pl P3) => ad_ + "uermen" ;
    VP (Pres Subj Sg P1) => ad_ + "uerma" ;
    VP (Pres Subj Sg P2) => ad_ + "uermas" ;
    VP (Pres Subj Sg P3) => ad_ + "uerma" ;
    VP (Pres Subj Pl P1) => ad_ + "urmamos" ;
    VP (Pres Subj Pl P2) => ad_ + "urm�is" ;
    VP (Pres Subj Pl P3) => ad_ + "uerman" ;
    VP (Past Ind Sg P1) => ad_ + "orm�a" ;
    VP (Past Ind Sg P2) => ad_ + "orm�as" ;
    VP (Past Ind Sg P3) => ad_ + "orm�a" ;
    VP (Past Ind Pl P1) => ad_ + "orm�amos" ;
    VP (Past Ind Pl P2) => ad_ + "orm�ais" ;
    VP (Past Ind Pl P3) => ad_ + "orm�an" ;
    VP (Past Subj Sg P1) => variants {ad_ + "urmiera" ; ad_ + "urmiese"} ;
    VP (Past Subj Sg P2) => variants {ad_ + "urmieras" ; ad_ + "urmieses"} ;
    VP (Past Subj Sg P3) => variants {ad_ + "urmiera" ; ad_ + "urmiese"} ;
    VP (Past Subj Pl P1) => variants {ad_ + "urmi�ramos" ; ad_ + "urmi�semos"} ;
    VP (Past Subj Pl P2) => variants {ad_ + "urmierais" ; ad_ + "urmieseis"} ;
    VP (Past Subj Pl P3) => variants {ad_ + "urmieran" ; ad_ + "urmiesen"} ;
    VP (Pret Sg P1) => ad_ + "orm�" ;
    VP (Pret Sg P2) => ad_ + "ormiste" ;
    VP (Pret Sg P3) => ad_ + "urmi�" ;
    VP (Pret Pl P1) => ad_ + "ormimos" ;
    VP (Pret Pl P2) => ad_ + "ormisteis" ;
    VP (Pret Pl P3) => ad_ + "urmieron" ;
    VP (Fut Ind Sg P1) => ad_ + "ormir�" ;
    VP (Fut Ind Sg P2) => ad_ + "ormir�s" ;
    VP (Fut Ind Sg P3) => ad_ + "ormir�" ;
    VP (Fut Ind Pl P1) => ad_ + "ormiremos" ;
    VP (Fut Ind Pl P2) => ad_ + "ormir�is" ;
    VP (Fut Ind Pl P3) => ad_ + "ormir�n" ;
    VP (Fut Subj Sg P1) => ad_ + "urmiere" ;
    VP (Fut Subj Sg P2) => ad_ + "urmieres" ;
    VP (Fut Subj Sg P3) => ad_ + "urmiere" ;
    VP (Fut Subj Pl P1) => ad_ + "urmi�remos" ;
    VP (Fut Subj Pl P2) => ad_ + "urmiereis" ;
    VP (Fut Subj Pl P3) => ad_ + "urmieren" ;
    VP (Cond Sg P1) => ad_ + "ormir�a" ;
    VP (Cond Sg P2) => ad_ + "ormir�as" ;
    VP (Cond Sg P3) => ad_ + "ormir�a" ;
    VP (Cond Pl P1) => ad_ + "ormir�amos" ;
    VP (Cond Pl P2) => ad_ + "ormir�ais" ;
    VP (Cond Pl P3) => ad_ + "ormir�an" ;
    VP (Imp Sg P1) => variants {} ;
    VP (Imp Sg P2) => ad_ + "uerme" ;
    VP (Imp Sg P3) => ad_ + "uerma" ;
    VP (Imp Pl P1) => ad_ + "urmamos" ;
    VP (Imp Pl P2) => ad_ + "ormid" ;
    VP (Imp Pl P3) => ad_ + "uerman" ;
    VP (Pass Sg Masc) => ad_ + "ormido" ;
    VP (Pass Sg Fem) => ad_ + "ormida" ;
    VP (Pass Pl Masc) => ad_ + "ormidos" ;
    VP (Pass Pl Fem) => ad_ + "ormidas"
    }
  } ;

oper colegir_24 : Str -> Verbum = \colegir -> 
  let col_ = Predef.tk 4 colegir in
 {s = table {
    VI Infn => col_ + "egir" ;
    VI Ger => col_ + "igiendo" ;
    VI Part => col_ + "egido" ;
    VP (Pres Ind Sg P1) => col_ + "ijo" ;
    VP (Pres Ind Sg P2) => col_ + "iges" ;
    VP (Pres Ind Sg P3) => col_ + "ige" ;
    VP (Pres Ind Pl P1) => col_ + "egimos" ;
    VP (Pres Ind Pl P2) => col_ + "eg�s" ;
    VP (Pres Ind Pl P3) => col_ + "igen" ;
    VP (Pres Subj Sg P1) => col_ + "ija" ;
    VP (Pres Subj Sg P2) => col_ + "ijas" ;
    VP (Pres Subj Sg P3) => col_ + "ija" ;
    VP (Pres Subj Pl P1) => col_ + "ijamos" ;
    VP (Pres Subj Pl P2) => col_ + "ij�is" ;
    VP (Pres Subj Pl P3) => col_ + "ijan" ;
    VP (Past Ind Sg P1) => col_ + "eg�a" ;
    VP (Past Ind Sg P2) => col_ + "eg�as" ;
    VP (Past Ind Sg P3) => col_ + "eg�a" ;
    VP (Past Ind Pl P1) => col_ + "eg�amos" ;
    VP (Past Ind Pl P2) => col_ + "eg�ais" ;
    VP (Past Ind Pl P3) => col_ + "eg�an" ;
    VP (Past Subj Sg P1) => variants {col_ + "igiera" ; col_ + "igiese"} ;
    VP (Past Subj Sg P2) => variants {col_ + "igieras" ; col_ + "igieses"} ;
    VP (Past Subj Sg P3) => variants {col_ + "igiera" ; col_ + "igiese"} ;
    VP (Past Subj Pl P1) => variants {col_ + "igi�ramos" ; col_ + "igi�semos"} ;
    VP (Past Subj Pl P2) => variants {col_ + "igierais" ; col_ + "igieseis"} ;
    VP (Past Subj Pl P3) => variants {col_ + "igieran" ; col_ + "igiesen"} ;
    VP (Pret Sg P1) => col_ + "eg�" ;
    VP (Pret Sg P2) => col_ + "egiste" ;
    VP (Pret Sg P3) => col_ + "igi�" ;
    VP (Pret Pl P1) => col_ + "egimos" ;
    VP (Pret Pl P2) => col_ + "egisteis" ;
    VP (Pret Pl P3) => col_ + "igieron" ;
    VP (Fut Ind Sg P1) => col_ + "egir�" ;
    VP (Fut Ind Sg P2) => col_ + "egir�s" ;
    VP (Fut Ind Sg P3) => col_ + "egir�" ;
    VP (Fut Ind Pl P1) => col_ + "egiremos" ;
    VP (Fut Ind Pl P2) => col_ + "egir�is" ;
    VP (Fut Ind Pl P3) => col_ + "egir�n" ;
    VP (Fut Subj Sg P1) => col_ + "igiere" ;
    VP (Fut Subj Sg P2) => col_ + "igieres" ;
    VP (Fut Subj Sg P3) => col_ + "igiere" ;
    VP (Fut Subj Pl P1) => col_ + "igi�remos" ;
    VP (Fut Subj Pl P2) => col_ + "igiereis" ;
    VP (Fut Subj Pl P3) => col_ + "igieren" ;
    VP (Cond Sg P1) => col_ + "egir�a" ;
    VP (Cond Sg P2) => col_ + "egir�as" ;
    VP (Cond Sg P3) => col_ + "egir�a" ;
    VP (Cond Pl P1) => col_ + "egir�amos" ;
    VP (Cond Pl P2) => col_ + "egir�ais" ;
    VP (Cond Pl P3) => col_ + "egir�an" ;
    VP (Imp Sg P1) => variants {} ;
    VP (Imp Sg P2) => col_ + "ige" ;
    VP (Imp Sg P3) => col_ + "ija" ;
    VP (Imp Pl P1) => col_ + "ijamos" ;
    VP (Imp Pl P2) => col_ + "egid" ;
    VP (Imp Pl P3) => col_ + "ijan" ;
    VP (Pass Sg Masc) => col_ + "egido" ;
    VP (Pass Sg Fem) => col_ + "egida" ;
    VP (Pass Pl Masc) => col_ + "egidos" ;
    VP (Pass Pl Fem) => col_ + "egidas"
    }
  } ;






-- for Numerals

param DForm = unit  | teen  | ten  | hundred  ;
param Modif = mod  | unmod  | conj  ;
}
