--# -path=.:../abstract:../../prelude

--1 A Small Predication Library
--
-- (c) Aarne Ranta 2003 under Gnu GPL.
--
-- This library is built on a language-independent API of
-- resource grammars. It has a common part, the type signatures
-- (defined here), and language-dependent parts. The user of
-- the library should only have to look at the type signatures.

resource Predication = open Deutsch in {

-- We first define a set of predication patterns.

oper
  predV1 : V -> NP -> S ;               -- one-place verb: "John walks"
  predV2 : TV -> NP -> NP -> S ;        -- two-place verb: "John loves Mary"
  predV3 : TV -> NP -> NP -> NP -> S ;  -- three-place verb: "John gives Mary beer"
  predVColl : V -> NP -> NP -> S ;      -- collective verb: "John and Mary fight"
  predA1 : Adj1 -> NP -> S ;            -- one-place adjective: "John is old"
  predA2 : Adj2 -> NP -> NP -> S ;      -- two-place adj: "John is married to Mary"
  predAComp : AdjDeg -> NP -> NP -> S ; -- compar adj: "John is older than Mary"
  predAColl : Adj1 -> NP -> NP -> S ;   -- collect adj: "John and Mary are married"
  predN1 : N -> NP -> S ;               -- one-place noun: "John is a man"
  predN2 : Fun -> NP -> NP -> S ;       -- two-place noun: "John is a lover of Mary"
  predNColl : N -> NP -> NP -> S ;      -- collect noun: "John and Mary are lovers"

-- Individual-valued function applications.

  appFun1 : Fun -> NP -> NP ;          -- one-place function: "the successor of x"
  appFun2 : Fun2 -> NP -> NP -> NP ;   -- two-place function: "the line from x to y"
  appFunColl : Fun -> NP -> NP -> NP ; -- collective function: "the sum of x and y"

-- Families of types, expressed by common nouns depending on arguments.

  appFam1 : Fun -> NP -> CN ;          -- one-place family: "divisor of x"
  appFam2 : Fun2 -> NP -> NP -> CN ;   -- two-place family: "line from x to y"
  appFamColl : Fun -> NP -> NP -> CN ; -- collective family: "path between x and y"

-- Type constructor, similar to a family except that the argument is a type.

  constrTyp1 : Fun -> CN -> CN ;

-- Logical connectives on two sentences.

  conjS : S -> S -> S ;  -- A and B
  disjS : S -> S -> S ;  -- A or B
  implS : S -> S -> S ;  -- if A, B

-- A variant of implication.

  ifThenS : S -> S -> S ;  -- if A, then B

-- As an auxiliary, we need two-place conjunction of names ("John and Mary"), 
-- used in collective predication.

  conjNP : NP -> NP -> NP ;


-----------------------------

---- what follows should be an implementation of the preceding

oper
  predV1 = \F, x -> PredVP x (PosV F) ;
  predV2 = \F, x, y -> PredVP x (PosTV F y) ;
  predVColl = \F, x, y -> PredVP (conjNP x y) (PosV F) ;
  predA1 = \F, x -> PredVP x (PosA (AdjP1 F)) ;
  predA2 = \F, x, y -> PredVP x (PosA (ComplAdj F y)) ;
  predAComp = \F, x, y -> PredVP x (PosA (ComparAdjP F y)) ;
  predAColl = \F, x, y -> PredVP (conjNP x y) (PosA (AdjP1 F)) ;
  predN1 = \F, x -> PredVP x (PosCN (UseN F)) ;
  predN2 = \F, x, y -> PredVP x (PosCN (AppFun F y)) ;
  predNColl = \F, x, y -> PredVP (conjNP x y) (PosCN (UseN F)) ;

  appFun1 = \f, x -> DefOneNP (AppFun f x) ;
  appFun2 = \f, x, y -> DefOneNP (AppFun (AppFun2 f x) y) ;
  appFunColl = \f, x, y -> DefOneNP (AppFun f (conjNP x y)) ;

  appFam1 = \F, x -> AppFun F x ;
  appFam2 = \F, x, y -> AppFun (AppFun2 F x) y ;
  appFamColl = \F, x, y -> AppFun F (conjNP x y) ;

  conjS = \A, B -> ConjS AndConj (TwoS A B) ;
  disjS = \A, B -> ConjS OrConj (TwoS A B) ;
  implS = \A, B -> SubjS IfSubj A B ;

  ifThenS = \A,B -> 
    SubjS IfSubj A {s = \\o => "then" ++ B.s ! o ; lock_S = <>} ; --- not in Res

  constrTyp1 = \F, A -> AppFun F (IndefManyNP A) ;

  conjNP = \x, y -> ConjNP AndConj (TwoNP x y) ;

} ;
