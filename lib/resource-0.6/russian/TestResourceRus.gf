-- use this path to read the grammar from the same directory
--# -path=.:../abstract:../../prelude
concrete TestResourceRus of TestResource = StructuralRus ** open SyntaxRus in {

flags 
  coding=utf8 ;
  startcat=Phr ; lexer=text ; parser=chart ; unlexer=text ;

-- a random sample from the lexicon

lin
  Big = bolshoj ;
  Small = malenkij ;
  Old = staruj ;
  Young = molodoj ;

  --Connection = cnNoHum (nounReg "connection") ** {s2 = "from" ; s3 = "to"} ;  Fun2
 -- American = adj1Malenkij "американск" ;
 -- Finnish = adj1Malenkij "финск" ;
 -- Married = adjInvar "замужем" ** {s2 = "за"; c = instructive} ;
  --Give = mkDitransVerb (verbNoPart (mkVerb "give" "gave" "given")) [] [] ;  V3
  --Prefer = mkDitransVerb (mkVerb "prefer" "preferred" "preferred")) [] "to" ; V3

  Man = muzhchina ;
  Woman = zhenchina ;
  Car = mashina ;
  House = dom ;
  Light = svet ;
  Walk = extVerb verbGulyat Act Present ;
  Run = extVerb verbBegat Act Present ;
  Love = mkDirectVerb (extVerb verbLubit Act Present ) ;
  Send = mkDirectVerb (extVerb verbOtpravlyat Act Present ) ;
  Wait = mkDirectVerb (extVerb verbZhdat Act Present );
  Say = extVerb verbGovorit Act Present ; --- works in present tense...
  Prove = extVerb verbDokazuvat Act Present ;
  SwitchOn = mkDirectVerb (extVerb verbVkluchat Act Present ) ;
  SwitchOff = mkDirectVerb (extVerb verbVukluchat Act Present ) ;

  Mother = funGen mama ;
  Uncle = funGen dyadya ;

  Always = vsegda ;
  Well = chorosho ;

  John = mkProperNameMasc "Иван" Animate ;
  Mary = mkProperNameFem "Маш" Animate ;
};
