--# -path=.:../abstract:../../prelude

concrete TestResourceSwe of TestResource = StructuralSwe ** open SyntaxSwe, ParadigmsSwe in {

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
  Man = extCommNoun masculine man_1144 ;
  Bar = extCommNoun nonmasculine (sSak "bar") ;
  Bottle = extCommNoun nonmasculine (sApa "flask") ;
  Woman = extCommNoun nonmasculine (sApa "kvinn") ;
  Car = extCommNoun nonmasculine (sBil "bil") ;
  House = extCommNoun nonmasculine (sHus "hus") ;
  Light = extCommNoun nonmasculine (sHus "ljus") ;
  Wine = extCommNoun nonmasculine (sParti "vin") ;
  Walk = extVerb active g�_1174 ;
  Run = extVerb active (vFinna "spring" "sprang" "sprung") ;
  Drink = extTransVerb (vFinna "drick" "drack" "druck") [] ;
  Love = extTransVerb (vTala "�lsk") [] ;
  Send = extTransVerb (vTala "skick") [] ;
  Wait = extTransVerb (vTala "v�nt") "p�" ;
  Give = extTransVerb (vFinna "giv" "gav" "giv") [] ** {s3 = "till"} ; --- ge
  Prefer = extTransVerb (vFinna "f�redrag" "f�redrog" "f�redrag") [] ** 
           {s3 = "framf�r"} ; --- f�redra

  Say = extVerb active (vLeka "s�g") ; --- works in present tense...
  Prove = extVerb active (vTala "bevis") ;
  SwitchOn = mkDirectVerb (extVerbPart active (vFinna "s�tt" "satte" "satt") "p�") ;
  SwitchOff = mkDirectVerb (extVerbPart active (vLeka "st�ng") "av") ;

  Mother = mkFun (extCommNoun nonmasculine mor_1**{lock_N = <>}) "till" ;
  Uncle = mkFun (extCommNoun masculine farbror_8 **{lock_N = <>}) "till" ;
  Connection = mkFun (extCommNoun nonmasculine (sVarelse "f�rbindelse")**{lock_N = <>}) "fr�n" ** 
               {s3 = "till"} ;

  Always = advPre "alltid" ;
  Well = advPost "bra" ;

  John = mkProperName "Johan" utrum masculine ;
  Mary = mkProperName "Maria" utrum nonmasculine ;
} ;
