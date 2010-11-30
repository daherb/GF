
-- other functions needed for parsing 

abstract Extension =  {



cat
  PolSentence;
  StmtS ;
  [CN]{2};
  N; N2; A; V; V2; CN; NP; Cl; Pol; Prep; Conj; -- redefined from Cat
fun 

VerbToNounV2 : V2 -> N2 ; -- discovering
VerbToNoun : V -> N ; -- walking is healthy
VerbToGerundA : V -> A ; -- singing bird
VerbToParticipeA : V -> A ; -- the required number 
ConjCN  : Conj -> [CN] -> CN ;   -- set or class
mkPolSent : Cl -> PolSentence ; 
sentToNoun : PolSentence -> NP ;
UsePolSentence : Pol -> PolSentence -> StmtS ;

at_Prep : Prep ; 
per_Prep : Prep ; 
O1 : NP ;
O2 : NP ;
O3 : NP ;
O4 : NP ;
O5 : NP ;


};
