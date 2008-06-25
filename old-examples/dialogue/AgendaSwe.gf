--# -path=.:multimodal:alltenses:prelude

concrete AgendaSwe of Agenda = 
  DialogueSwe, WeekdaySwe ** open MultiSwe, ParadigmsSwe, IrregSwe in {

  lin
    Day       = UseN (regN "dag") ;
    Meeting   = UseN (regGenN "m�te" neutrum) ;
    Add       = dirV3 (partV l�gga_V "till") (mkPrep "p�") ;
    Remove    = dirV2 (partV taga_V "bort") ;
    Interrupt = avbryta_V ;
   
    day = UsePN ;

}

