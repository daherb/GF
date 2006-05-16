--# -path=.:present:prelude

concrete AgendaFre of Agenda = 
  DialogueFre, WeekdayFre ** open LangFre, ParadigmsFre, IrregFre in {

  lin
    Day       = UseN (regN "jour") ;
    Meeting   = UseN (regN "r�union") ;
    Add       = dirdirV3 (regV "ajouter") ;
    Remove    = dirV2 (regV "�ter") ;
    Interrupt = interrompre_V2 ;
   
    day = UsePN ;

}

