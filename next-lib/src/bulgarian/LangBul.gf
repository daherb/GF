--# -path=.:../abstract:../common:../slavic

concrete LangBul of Lang = 
  GrammarBul,
  LexiconBul
  ** {
  flags coding=cp1251 ;


flags startcat = Phr ; unlexer = text ; lexer = text ; erasing = on ; coding = cp1251 ;

} ;
