resource StoneageResEng = open ResourceEng, ParadigmsEng in {

oper
  PresV : V -> NP -> Phr = \v,s -> PresCl (SPredV s v) ;
  PresV2 : V2 -> NP -> NP -> Phr = \v,s,o -> PresCl (SPredV2 s v o) ;
  PresVasV2 : V -> NP -> NP -> Phr = \ v -> PresV2 (dirV2 v) ;

  PresCl : Cl -> Phr = 
    \c -> { s = (UseCl (PosTP TPresent ASimul) c).s } ** {lock_Phr = <>} ;
 
  ModPosA : ADeg -> CN -> CN = \a -> ModAP (PositADeg a) ;
  ModA : A -> CN -> CN = \a -> ModAP (UseA a) ;

}