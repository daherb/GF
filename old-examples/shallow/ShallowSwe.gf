--# -path=.:alltenses:prelude

concrete ShallowSwe of Shallow = GrammarSwe - [
  VP, 
  ImpersCl, 
  GenericCl,
  ProgrVP,  
  ImpPl1,   
  UttVP,    
  QuestVP,  
  RelVP,    
  PredVP,   
  PredSCVP, 
  ImpVP,    
  EmbedVP,  
  UseV    , 
  ComplV2 , 
  ComplV3 , 
  ComplVV , 
  ComplVS , 
  ComplVQ , 
  ComplVA , 
  ComplV2A, 
  ReflV2  , 
  UseComp , 
  PassV2  , 
  AdvVP   , 
  AdVVP     
  ]

** ShallowI with 
  (Grammar = GrammarSwe) ;

