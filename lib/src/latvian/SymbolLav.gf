--# -path=.:../abstract:../common:../prelude

concrete SymbolLav of Symbol = CatLav ** open
  Prelude,
  ResLav
  in {

flags
  coding = utf8 ;

lin

  SymbPN i = {s = \\_ => i.s ; g = Masc ; n = Sg} ;
  IntPN i  = {s = \\_ => i.s ; g = Masc ; n = Pl} ;
  FloatPN i = {s = \\_ => i.s ; g = Masc ; n = Pl} ;
  NumPN i = {s = \\_ => i.s ! Masc ! Nom ; g = Masc ; n = Pl} ;

  CNIntNP cn i = {
    s = \\_ => cn.s ! Indef ! Sg ! Nom ++ i.s ;
    a = agrgP3 Sg cn.g ; 
    isNeg = False
  } ;

  CNSymbNP det cn xs = {
    s = \\_ => det.s ! cn.g ! Nom ++ cn.s ! det.d ! det.n ! Nom ++ xs.s ;
    a = agrgP3 det.n cn.g ;
    isNeg = False
  } ;

  CNNumNP cn i = {
    s = \\_ => cn.s ! Indef ! Sg ! Nom ++ i.s ! Masc ! Nom ;
    a = agrgP3 Sg cn.g ;
    isNeg = False
  } ;

  SymbS sy = sy ;

  SymbNum sy = { s = \\_,_ => sy.s ; n = Pl } ;
  SymbOrd sy = { s = \\_,_ => sy.s ++ "."} ;

lincat

  Symb, [Symb] = SS ;

lin

  MkSymb s = s ;

  BaseSymb = infixSS "un" ;
  ConsSymb = infixSS "," ;

}
