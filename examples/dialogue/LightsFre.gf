--# -path=.:present:prelude

concrete LightsFre of Lights = 
  DialogueFre ** open LangFre, ParadigmsFre, IrregFre, AuxFre in {

  lin
    Light       = UseN (regN "lampe") ;
    Room        = UseN (regN "chambre") ;
    SwitchOnIn  = dirV3 (regV "allumer")  (mkPreposition "dans") ;
    SwitchOffIn = dirV3 �teindre_V2 (mkPreposition "dans") ;
    SwitchOn    = dirV2 (regV "allumer") ;
    SwitchOff   = dirV2 �teindre_V2 ;

    LivingRoom  = defN (regN "salon") ;
    Kitchen     = defN (regN "cuisine") ;

    MorningMode = mkMove ["le mode matinal"] ;

}
