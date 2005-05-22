--# -path=.:resource/swedish:resource/scandinavian:resource/abstract:resource/../prelude

concrete AnimalsSwe of Animals = QuestionsSwe **
  open ResourceSwe, ParadigmsSwe, VerbsSwe in {

  lin
    Dog = regN "hund" utrum ;
    Cat = mk2N "katt" "katter" ;
    Mouse = mkN "mus" "musen" "m�ss" "m�ssen" ;
    Lion = mk2N "lejon" "lejon" ;
    Zebra = regN "zebra" utrum ;
    Chase = dirV2 (regV "jaga") ;
    Eat = dirV2 �ta_V ;
    Like = mkV2 (mk2V "tycka" "tycker") "om" ;
}
