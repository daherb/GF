--1 Swedish Word Classes and Morphological Parameters
--
-- This is a resource module for Swedish morphology, defining the
-- morphological parameters and word classes of Italian. 
-- The morphology is so far only
-- complete w.r.t. the syntax part of the resource grammar.
-- It does not include those parameters that are not needed for
-- analysing individual words: such parameters are defined in syntax modules.

instance TypesSwe of TypesScand = {

param
  NounGender = NUtr Sex | NNeutr ;

oper
  genNoun = \s -> case s of {NUtr _ => Utr ; NNeutr => Neutr} ;
  sexNoun = \s -> case s of {NUtr x => x ; NNeutr => NoMasc} ;
  gen2nounGen = \s -> case s of {Utr => NUtr NoMasc ; Neutr => NNeutr} ;

param
  AdjFormPos = Strong GenNum | Weak SexNum ;

  VFin = 
   Pres Mode Voice
 | Pret Mode Voice
 | Imper ;         --- no passive
 
  VInf =
   Inf Voice
 | Supin Voice
 | PtPres Case
 | PtPret AdjFormPos Case ;
}
