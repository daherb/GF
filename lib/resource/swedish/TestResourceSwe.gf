--# -path=.:../scandinavian:../abstract:../../prelude

concrete TestResourceSwe of TestResource = 
RulesSwe, 
ClauseSwe,
StructuralSwe 
** 
  open Prelude, MorphoSwe, SyntaxSwe in {

flags startcat=Phr ; lexer=text ; unlexer=text ;

-- a random sample from the lexicon

lin
  Big = stor_25 ;
  Small = liten_1146 ;
  Old = gammal_16 ;
  Young = ung_29 ;
  American = extAdjective (aFin "amerikansk") ;
  Finnish = extAdjective (aFin "finsk") ;
  Happy = aFin "lycklig" ;
  Married = extAdjective (aAbstrakt "gift") ** {s2 = "med"} ;
  Man = extCommNounMasc man_1144 ;
  Bar = extCommNoun (sSak "bar") ;
  Bottle = extCommNoun (sApa "flask") ;
  Woman = extCommNoun (sApa "kvinn") ;
  Car = extCommNoun (sBil "bil") ;
  House = extCommNoun (sHus "hus") ;
  Light = extCommNoun (sHus "ljus") ;
  Wine = extCommNoun (sParti "vin") ;
  Walk = vNopart (mkVerb "g�" "g�r" "g�" "gick" "g�tt" "g�ngen") ;
  Run = vNopart (vFinna "spring" "sprang" "sprung") ;
  Drink = extTransVerb (vFinna "drick" "drack" "druck") [] ;
  Love = extTransVerb (vNopart (vTala "�lsk")) [] ;
  Send = extTransVerb (vNopart (vTala "skick")) [] ;
  Wait = extTransVerb (vNopart (vTala "v�nt")) "p�" ;
  Give = extTransVerb (vNopart (mkVerb "ge" "ger" "ge" "gav" "givit" "given")) [] ** {s3 = "till"} ;
  Prefer = extTransVerb (vNopart (vFinna "f�redrag" "f�redrog" "f�redrag")) [] ** 
           {s3 = "framf�r"} ; --- f�redra

  Say = vNopart (mkVerb "s�ga" "s�ger" "s�g" "sade" "sagt" "sagd") ;
  Prove = vNopart (vTala "bevis") ;
  SwitchOn = mkDirectVerb (vFinna "s�tt" "satte" "satt" ** {s1 = "p�"}) ;
  SwitchOff = mkDirectVerb (vLeka "st�ng" ** {s1 = "av"}) ;

  Mother = mkFun (extCommNoun mor_1) "till" ;
  Uncle = mkFun (extCommNounMasc farbror_8) "till" ;
  Connection = mkFun (extCommNoun (sVarelse "f�rbindelse")) "fr�n" ** 
               {s3 = "till"} ;

  Always = advPre "alltid" ;
  Well = advPost "bra" ;

  John = mkProperName "Johan" (NUtr Masc) ;
  Mary = mkProperName "Maria" (NUtr NoMasc) ;

--- next
   AlreadyAdv = advPre "redan" ;
   NowAdv = advPre "nu" ;

   Paint = extTransVerb (vNopart (vTala "m�l")) [] ;
   Green = aFin "gr�n" ;
   Beg = extTransVerb (mkVerbPart "be" "ber" "be" "bad" "bett" "bedd" []) [] ** {s3 = "att"} ;
   Promise = extTransVerb (vNopart (vTala "lov")) [] ** {s3 = "att"} ;
   Wonder = extTransVerb (vNopart (vTala "undr")) [] ;
   Ask = extTransVerb (vNopart (vTala "fr�g")) [] ;
   Tell = extTransVerb (vNopart (vTala "ber�tt")) [] ;
   Look = extTransVerb (mkVerbPart "se" "ser" "se" "s�g" "sett" "sedd" "ut") [] ;

   Try = extTransVerb (vNopart (vLeka "f�rs�k")) [] ** {s3 = "att"} ;
   Important = extAdjective (aFin "viktig") ** {s2 = "f�r"} ;
   Probable = extAdjective (aFin "sannolik") ;
   Easy = extAdjective (aAbstrakt "l�tt") ** {s2 = "f�r"} ;
   Rain = extTransVerb (vNopart (vTala "regn")) [] ;


} ;
