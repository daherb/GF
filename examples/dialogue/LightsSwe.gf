--# -path=.:multimodal:alltenses:prelude


concrete LightsSwe of Lights = 
  DialogueSwe ** open MultiSwe, ParadigmsSwe, AuxSwe in {

  lin
    Light       = UseN (regN "lampa") ;
    Room        = UseN (mkN "rum" "rummet" "rum" "rummen") ;
    SwitchOnIn  = dirV3 (regV "t�nder")  (mkPreposition "i") ;
    SwitchOffIn = dirV3 (regV "sl�cker") (mkPreposition "i") ;
    SwitchOn    = dirV2 (regV "t�nder") ;
    SwitchOff   = dirV2 (regV "sl�cker") ;

    LivingRoom  = defN (mkN "vardagsrum" "vardagsrummet" "vardagsrum" "vardagsrummen") ;
    Kitchen     = defN (mk2N "k�k" "k�k") ;

    MorningMode = mkMove ["morgonl�get"] ;

}
