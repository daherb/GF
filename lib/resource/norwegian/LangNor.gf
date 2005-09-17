--# -path=.:../scandinavian:../abstract:../../prelude

concrete LangNor of Lang = 
  RulesNor, 
  ClauseNor, 
  StructuralNor,  
  BasicNor,
  TimeNor,
  CountryNor,
  MathNor

   ** open Prelude, ParadigmsNor in {

lin
  AdvDate d = prefixSS "p�" d ;
  AdvTime t = prefixSS "klokken" t ;
  NWeekday w = w ;
  PNWeekday w = nounPN w ;

  PNCountry x = x ;
  ANationality x = x ;
  NLanguage x = x ;
}
