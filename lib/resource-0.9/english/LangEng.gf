--# -path=.:../abstract:../../prelude

-- # -path=.:resource/english:resource/abstract:prelude

concrete LangEng of Lang = 
  RulesEng, 
  ClauseEng, 
  StructuralEng,  
  BasicEng,
  TimeEng,
  CountryEng,
  MathEng

   ** open Prelude, ParadigmsEng in {

lin
  AdvDate d = prefixSS "on" d ;
  AdvTime t = prefixSS "at" t ;
  NWeekday w = w ;
  PNWeekday w = nounPN w ;

  PNCountry x = x ;
  ANationality x = x ;
  NLanguage x = x ;

}