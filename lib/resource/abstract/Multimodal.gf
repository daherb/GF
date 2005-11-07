--# -path=.:../../prelude

abstract Multimodal = 
  Rules, 
  Structural, 
  Basic, 
  Time,
  Demonstrative

  ** {

  flags startcat=Phr ;

  fun

-- Interface to $Demonstrative$.

   DemNP    : NP  -> DNP ; 
   DemAdv   : Adv -> DAdv -> DAdv ; 
   SentMS   : Pol -> MS  -> Phr ;
   QuestMS  : Pol -> MS  -> Phr ;
   QuestMQS : Pol -> MQS -> Phr ;
   ImpMImp  : Pol -> MImp -> Phr ;

-- Mount $Time$.

   AdvDate : Date -> Adv ;
   AdvTime : Time -> Adv ;

}

{-
> p -cat=Phr "I go from here to here ; foo bar"
SentMS (DemV go_V (DemNP i_NP) 
  (here7from_DAdv (MkPoint "foo") (here7to_DAdv (MkPoint "bar") NoDAdv)))

> p -cat=Phr "which cars go from here to here ; foo bar"
QuestMQ (QDemV go_V (IDetCN which8many_IDet (UseN car_N)) 
  (here7from_DAdv (MkPoint "foo") (here7to_DAdv (MkPoint "bar") NoDAdv)))
-}
