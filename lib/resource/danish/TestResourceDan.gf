--# -path=.:../scandinavian:../abstract:../../prelude

concrete TestResourceDan of TestResource = RulesDan, StructuralDan ** 
  open Prelude, MorphoDan, SyntaxDan in {

flags startcat=Phr ; lexer=text ; unlexer=text ;

-- a random sample from the lexicon

lin
  Big = mkAdjective "stor" "stort" "store" "st�rre" "st�rst" ;
  Small = mkAdjective "lille" "lille" "sm�" "mindre" "mindst" ;
  Old = mkAdjective "gammel" "gammelt" "gamle" "�ldre" "�ldst" ;
  Young = mkAdjective "ung" "ungt" "unge" "yngre" "yngst" ;
  American = extAdjective (aRod "amerikansk") ;
  Finnish = extAdjective (aRod "finsk") ;
  Happy = aRod "lykkelig" ;
  Married = extAdjective (aAbstrakt "gift") ** {s2 = "med"} ;
  Man = extCommNoun (mkSubstantive "mand" "manden" "m�nd" "m�nden" ** {h1 = Utr}) ;
  Bar = extCommNoun (nBil "bar") ; ---- ?
  Bottle = extCommNoun (nUge "flaske") ;
  Woman = extCommNoun (nUge "kvinde") ;
  Car = extCommNoun (nBil "bil") ;
  House = extCommNoun (nHus "hus") ;
  Light = extCommNoun (nHus "lys") ;
  Wine = extCommNoun (nHus "vin") ; ---- ?
  Walk = mkVerb "g�" "g�r" "g�s" "gik" "g�et" "g�" ** {s1 = []} ; 
  Run = mkVerb "springe" "springer" "springes" "sprang" "sprunget" "spring" ** {s1 = []} ; 
  Drink = extTransVerb (mkVerb "drikke" "drikker" "drikkes" "drak" "drukket" "drikk" ** {s1 = []}) [] ;
  Love = extTransVerb (vNopart (vHusk "�lsk")) [] ;
  Send = extTransVerb (vNopart (vSpis "send")) [] ; ---- ?
  Wait = extTransVerb (vNopart (vSpis "vent")) "p�" ;
  Give = extTransVerb (vNopart (mkVerb "give" "giver" "gives" "gav" "givet" "giv")) [] ** {s3 = "til"} ;
  Prefer = extTransVerb (vNopart (vSpis "foretr�kk")) [] ** {s3 = "for"} ;

  Say = vNopart (mkVerb "sige" "siger" "siges" "sagde" "sagt" "sig") ;
  Prove = vNopart (vSpis "bevis") ;
  SwitchOn = mkDirectVerb (vHusk "lukk" ** {s1 = "op"}) ;
  SwitchOff = mkDirectVerb (vHusk "slukk" ** {s1 = []}) ;

  Mother = mkFun (extCommNoun (mkSubstantive "moder" "moderen" "m�dre"
  "m�drene" ** {h1 = Utr})) "til" ; ---- ?
  Uncle = mkFun (extCommNoun (mkSubstantive "onkel" "onkelen" "onkler" "onklene" ** {h1 = Utr})) "til" ; ---- ? 
  Connection = mkFun (extCommNoun (nUge "forbindelse")) "fra" ** {s3 = "til"} ;

  Always = advPre "altid" ;
  Well = advPost "godt" ;

  John = mkProperName "Johan" NUtr ;
  Mary = mkProperName "Maria" NUtr ;

--- next
   AlreadyAdv = advPre "allerede" ;
   NowAdv = advPre "nu" ;

   Paint = extTransVerb (vNopart (vHusk "m�l")) [] ;
   Green = mkAdjective "gr�n" "gr�nt" "gr�ne" "gr�nnere" "gr�nnest" ;

   Beg = extTransVerb (mkVerb "bede" "beder" "bedes" "bad" "bedt" "bed") [] ** {s3 = "at"} ;
   Promise  = extTransVerb (vNopart (vSpis "lov")) [] ** {isAux = False} ;
   Promise2 = extTransVerb (vNopart (vSpis "lov")) [] ** {s3 = "att"} ;
   Wonder = extTransVerb (vNopart (vHusk "undr")) [] ;
   Ask = extTransVerb (mkVerb "sp�rge" "sp�rger""sp�rges""spurgte""spurgt""sp�rg") [] ;
   Tell = extTransVerb (mkVerb "fort�lle" "fort�ller" "fort�lles"
   "fortalte" "fortalt" "fort�ll") [] ;
   Look = extTransVerb (mkVerb "se" "ser" "ses" "s�" "set" "sedd") []
   ; ---- ut

} ;
