resource StoneageResSwe = open ResourceSwe, SyntaxSwe, ParadigmsSwe in {

oper
  PresV : V -> NP -> Phr = \v,s -> PresCl (SPredV s v) ;
  PresV2 : V2 -> NP -> NP -> Phr = \v,s,o -> PresCl (SPredV2 s v o) ;
  PresV3 : V3 -> NP -> NP -> NP -> Phr = \v,s,o,r -> PresCl (SPredV3 s v o r) ;
  PresVasV2 : V -> NP -> NP -> Phr = \ v -> PresV2 (dirV2 v) ;

  PresCl : Cl -> Phr = 
    \c -> defaultSentence (UseCl (PosTP TPresent ASimul) c) ** {lock_Phr = <>} ;
 
  ModPosA : ADeg -> CN -> CN = \a -> ModAP (PositADeg a) ;
  ModA : A -> CN -> CN = \a -> ModAP (UseA a) ;

}