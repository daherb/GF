--# -path=.:../present:prelude

concrete MathematicalFre of Mathematical = 
  NounFre - [ComplN2], --- to avoid ambiguity 
--  VerbFre, 
  AdjectiveFre,
  AdverbFre,
  NumeralFre,
--  SentenceFre,
  QuestionFre,
  RelativeFre,
  ConjunctionFre,
  PhraseFre,
  TextX,
  IdiomFre,
  StructuralFre,
  
  SymbolFre,
  PredicationFre - [predV3], ---- gf bug

  LexiconFre
  ** {

flags startcat = Phr ;

} ;
