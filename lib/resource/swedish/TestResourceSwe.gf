--# -path=.:../abstract:../../prelude

concrete TestResourceSwe of TestResource = RulesSwe, StructuralSwe ** open MorphoSwe, SyntaxSwe in {

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
  Man = extCommNoun Masc man_1144 ;
  Bar = extCommNoun NoMasc (sSak "bar") ;
  Bottle = extCommNoun NoMasc (sApa "flask") ;
  Woman = extCommNoun NoMasc (sApa "kvinn") ;
  Car = extCommNoun NoMasc (sBil "bil") ;
  House = extCommNoun NoMasc (sHus "hus") ;
  Light = extCommNoun NoMasc (sHus "ljus") ;
  Wine = extCommNoun NoMasc (sParti "vin") ;
  Walk = vNopart g�_1174 ;
  Run = vNopart (vFinna "spring" "sprang" "sprung") ;
  Drink = extTransVerb (vFinna "drick" "drack" "druck") [] ;
  Love = extTransVerb (vNopart (vTala "�lsk")) [] ;
  Send = extTransVerb (vNopart (vTala "skick")) [] ;
  Wait = extTransVerb (vNopart (vTala "v�nt")) "p�" ;
  Give = extTransVerb (vNopart (vFinna "giv" "gav" "giv")) [] ** {s3 = "till"} ; --- ge
  Prefer = extTransVerb (vNopart (vFinna "f�redrag" "f�redrog" "f�redrag")) [] ** 
           {s3 = "framf�r"} ; --- f�redra

  Say = vNopart (vLeka "s�g") ; --- works in present tense...
  Prove = vNopart (vTala "bevis") ;
  SwitchOn = mkDirectVerb (vFinna "s�tt" "satte" "satt" ** {s1 = "p�"}) ;
  SwitchOff = mkDirectVerb (vLeka "st�ng" ** {s1 = "av"}) ;

  Mother = mkFun (extCommNoun NoMasc mor_1) "till" ;
  Uncle = mkFun (extCommNoun Masc farbror_8) "till" ;
  Connection = mkFun (extCommNoun NoMasc (sVarelse "f�rbindelse")) "fr�n" ** 
               {s3 = "till"} ;

  Always = advPre "alltid" ;
  Well = advPost "bra" ;

  John = mkProperName "Johan" Utr Masc ;
  Mary = mkProperName "Maria" Utr NoMasc ;
} ;
