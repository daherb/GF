--# -path=.:multimodal:alltenses:prelude

concrete LightsFin of Lights = 
  DialogueFin ** open MultiFin, ParadigmsFin, AuxFin in {

  lin
    Light       = UseN (regN "valo") ;
    Room        = UseN (regN "huone") ;
    SwitchOnIn  = dirV3 (regV "sytytt��")  inessive ;
    SwitchOffIn = dirV3 (regV "sammuttaa") inessive ;
    SwitchOn    = dirV2 (regV "sytytt��") ;
    SwitchOff   = dirV2 (regV "sammuttaa") ;

    LivingRoom  = defN (regN "olohuone") ;
    Kitchen     = defN (regN "keitti�") ;

    MorningMode = mkMove ["aamuvalaistus"] ;

}
