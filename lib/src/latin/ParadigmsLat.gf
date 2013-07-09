--# -path=.:../abstract:../prelude:../common

--1 Latin Lexical Paradigms
--
-- Aarne Ranta 2008, Extended Herbert Lange 2013
--
-- This is an API for the user of the resource grammar 
-- for adding lexical items. It gives functions for forming
-- expressions of open categories: nouns, adjectives, verbs.
-- 
-- Closed categories (determiners, pronouns, conjunctions) are
-- accessed through the resource syntax API, $Structural.gf$. 

resource ParadigmsLat = open 
  (Predef=Predef), 
  Prelude, 
  ResLat,
  MorphoLat,
  CatLat
  in {

--2 Parameters 
--
-- To abstract over gender names, we define the following identifiers.

oper
  masculine : Gender ;
  feminine  : Gender ;
  neuter    : Gender ;

  mkN = overload {
    mkN : (verbum : Str) -> N 
      = \n -> lin N ( noun n ) ;
    mkN : (verbum, verbi : Str) -> Gender -> N 
      = \x,y,z -> lin N ( noun_ngg x y z ) ;
  } ;
  
  mkA = overload {
    mkA : (verbum : Str) -> A 
      = \n -> lin A ( adj n ** {isPre = False } ) ;
    mkA : (verbum, verbi : Str) -> A 
      = \x,y -> lin A ( adj123 x y ** {isPre = False } ) ;
    mkA : (bonus,bona,bonum : N) -> A 
      = \x,y,z -> 
      let compsup = comp_super x in
      lin A ( mkAdjective x y z compsup.p1 compsup.p2 ** {isPre = False } ) ;
  } ;
  

  mkV = overload {
    mkV : (tacere : Str) -> V
      = \v -> lin V ( verb v ) ; 
    mkV : (iacio,ieci,iactus,iacere : Str) -> V
      = \v,x,y,z -> verb_pppi v x y z ** {lock_V = <>} ; 
  } ;

  mkV2 = overload {
    mkV2 : (amare : Str) -> V2
      = \v -> lin V2 ( verb v ** {c = {s = [] ; c = Acc} } ) ; 
    mkV2 : (facere : V) -> V2
      = \v -> lin V2 ( v ** {c = {s = [] ; c = Acc} } ) ; 
    } ;
--.
  masculine = Masc ;
  feminine = Fem ;
  neuter = Neutr ;

-- To be implemented, just place holders
  mkPN : N -> PN = \n -> lin PN n ;
  mkN2 : N -> Prep -> N2 = \n,p -> lin N2 n ;
  mkN3 : N -> Prep -> Prep -> N3 = \n,p1,p2 -> lin N3 n ;
}
