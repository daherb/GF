--# -path=.:present:prelude

concrete AgendaSwe of Agenda = 
  DialogueSwe, WeekdaySwe ** open LangSwe, ParadigmsSwe, IrregSwe in {

  lin
    Day       = UseN (regN "dag") ;
    Meeting   = UseN (regGenN "m�te" neutrum) ;
    Add       = dirV3 (partV l�gga_V "till") (mkPreposition "p�") ;
    Remove    = dirV2 (partV taga_V "bort") ;
    Interrupt = avbryta_V ;
   
    day = UsePN ;

}

