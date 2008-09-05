--# -path=.:../scandinavian:../abstract:../common:prelude

concrete GrammarNor of Grammar = 
  NounNor, 
  VerbNor, 
  AdjectiveNor,
  AdverbNor,
  NumeralNor,
  SentenceNor,
  QuestionNor,
  RelativeNor,
  ConjunctionNor,
  PhraseNor,
  TextX,
  IdiomNor,
  StructuralNor
  ** {

flags startcat = Phr ; unlexer = text ; lexer = text ;

} ;
