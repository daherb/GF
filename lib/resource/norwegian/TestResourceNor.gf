--# -path=.:../scandinavian:../abstract:../../prelude

concrete TestResourceNor of TestResource = RulesNor, StructuralNor ** open MorphoNor, SyntaxNor in {

flags startcat=Phr ; lexer=text ; unlexer=text ;

-- a random sample from the lexicon

lin
  Big = mkAdjective "stor" "stort" "store" "st�rre" "st�rst" ;
  Small = mkAdjective "liten" "litet" "sm�" "mindre" "minst" ; ---- ?
  Old = mkAdjective "gammel" "gammelt" "gamle" "eldre" "eldst" ;
  Young = mkAdjective "ung" "ungt" "unge" "yngre" "yngst" ;
  American = extAdjective (aAbstrakt "amerikansk") ;
  Finnish = extAdjective (aAbstrakt "finsk") ;
  Happy = aAbstrakt "heldig" ;
  Married = extAdjective (aAbstrakt "gift") ** {s2 = "med"} ;
  Man = extCommNoun (mkSubstantive "mann" "mannen" "menn" "mennen" ** {h1 = masc}) ;
  Bar = extCommNoun (nBil "bar") ; ---- ?
  Bottle = extCommNoun (nUke "flaske") ;
  Woman = extCommNoun (nUke "kvinne") ;
  Car = extCommNoun (nBil "bil") ;
  House = extCommNoun (nHus "hus") ;
  Light = extCommNoun (nHus "lys") ;
  Wine = extCommNoun (nHus "vin") ; ---- ?
  Walk = mkVerb "g�" "g�r" "g�s" "gikk" "g�tt" "g�" ** {s1 = []} ; 
  Run = mkVerb "springe" "springer" "springes" "sprang" "sprunget" "spring" ** {s1 = []} ; 
  Drink = extTransVerb (mkVerb "drikke" "drikker" "drikkes" "drakk" "drukket" "drikk" ** {s1 = []}) [] ;
  Love = extTransVerb (vNopart (vHusk "elsk")) [] ;
  Send = extTransVerb (vNopart (vSpis "send")) [] ; ---- ?
  Wait = extTransVerb (vNopart (vSpis "vent")) "p�" ;
  Give = extTransVerb (vNopart (mkVerb "gi" "gir" "gives" "gav" "givet" "gi")) [] ** {s3 = "til"} ; ---- ?
  Prefer = extTransVerb (vNopart (vSpis "foretrekk")) [] ** {s3 = "for"} ;

  Say = vNopart (mkVerb "si" "sier" "sies" "sagde" "sagt" "sig") ;  ---- ?
  Prove = vNopart (vSpis "bevis") ;
  SwitchOn = mkDirectVerb (vHusk "lukk" ** {s1 = "opp"}) ;
  SwitchOff = mkDirectVerb (vHusk "slukk" ** {s1 = []}) ;

  Mother = mkFun (extCommNoun (mkSubstantive "mor" "moderen" "m�dre" "m�drene" ** {h1 = fem})) "til" ; ---- ?
  Uncle = mkFun (extCommNoun (mkSubstantive "onkel" "onkelen" "onkler" "onklene" ** {h1 = masc})) "til" ; ---- ? 
  Connection = mkFun (extCommNoun (nUke "forbindelse")) "fra" ** {s3 = "til"} ;

  Always = advPre "altid" ;
  Well = advPost "godt" ;

  John = mkProperName "Johan" (NUtr Masc) ;
  Mary = mkProperName "Maria" (NUtr NoMasc) ;
} ;
