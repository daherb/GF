-- use this path to read the grammar from the same directory
--# -path=.:../abstract:../../prelude

concrete TestDeu of TestAbs = ResDeu ** open Syntax in {

flags startcat=Phr ; lexer=text ; parser=chart ; unlexer=text ;

-- a random sample from the lexicon

lin
  Big = adjCompReg3 "gross" "gr�sser" "gr�sst";
  Small = adjCompReg "klein" ;
  Old = adjCompReg3 "alt" "�lter" "�ltest";
  Young = adjCompReg3 "jung" "j�nger" "j�ngst";
  American = adjReg "Amerikanisch" ;
  Finnish = adjReg "Finnisch" ;
  Married = adjReg "verheiratet" ** {s2 = "mit" ; c = Dat} ;
  Man = declN2u "Mann" "M�nner" ;
  Woman = declN1 "Frau" ;
  Car = declNs "Auto" ;
  House = declN3uS "Haus" "H�user" ;
  Light = declN3 "Licht" ;
  Walk = mkVerbSimple (verbLaufen "gehen" "geht" "gegangen") ;
  Run = mkVerbSimple (verbLaufen "laufen" "l�uft" "gelaufen") ; 
  Say = mkVerbSimple (regVerb "sagen") ;
  Prove = mkVerbSimple (regVerb "beweisen") ;
  Send = mkTransVerb (mkVerbSimple (verbLaufen "senden" "sendet" "gesandt")) [] Acc;
  Love = mkTransVerb (mkVerbSimple (regVerb "lieben")) [] Acc ;
  Wait = mkTransVerb (mkVerbSimple (verbWarten "warten")) "auf" Acc ;
  Give = mkDitransVerb 
           (mkVerbSimple (verbLaufen "geben" "gibt" "gegeben")) [] Dat [] Acc ;
  Prefer = mkDitransVerb 
           (mkVerb (verbLaufen "ziehen" "zieht" "gezogen") "vor") [] Acc "vor" Dat ;
  Mother = mkFunC (n2n (declN2uF "Mutter" "M�tter")) "von" Dat ;
  Uncle = mkFunC (n2n (declN2i "Onkel")) "von" Dat ;
  Connection = mkFunC (n2n (declN1 "Verbindung")) "von" Dat ** 
                                     {s3 = "nach" ; c2 = Dat} ;

  Always = mkAdverb "immer" ;
  Well = mkAdverb "gut" ;

  SwitchOn  = mkTransVerb (mkVerb (verbWarten "schalten") "auf") [] Acc  ;
  SwitchOff = mkTransVerb (mkVerb (verbWarten "schalten") "aus") [] Acc  ;

  John = mkProperName "Johann" ;
  Mary = mkProperName "Maria" ;

} ;

