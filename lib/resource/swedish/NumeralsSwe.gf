concrete NumeralsSwe of Numerals = open MorphoSwe, Prelude in {

lincat 
  Numeral = { s : Str } ;
  Digit = {s : DForm => Str} ;
  Sub10 = {s : DForm => Str} ;

lin 
  num x = x ;

  n2 = mkTal  "tv�"  "tolv"    "tjugo" ;
  n3 = mkTal  "tre"  "tretton" "trettio" ;
  n4 = mkTal  "fyra" "fjorton" "fyrtio" ;
  n5 = regTal "fem" ;
  n6 = regTal "sex" ;
  n7 = mkTal  "sju"  "sjutton" "sjuttio" ;
  n8 = mkTal  "�tta" "arton"   "�ttio" ;
  n9 = mkTal  "nio"  "nitton"   "nittio" ;

  pot01 = {s = table {f => "ett"}} ;
  pot0 d = {s = table {f => d.s ! f}} ;
  pot110 = ss "tio" ;
  pot111 = ss "elva" ;
  pot1to19 d = ss (d.s ! ton) ;
  pot0as1 n = ss (n.s ! ental) ;
  pot1 d = ss (d.s ! tiotal) ;
  pot1plus d e = ss (d.s ! tiotal ++ e.s ! ental) ;
  pot1as2 n = n ;
  pot2 d = ss (d.s ! ental ++ "hundra") ;
  pot2plus d e = ss (d.s ! ental ++ "hundra" ++ e.s) ;
  pot2as3 n = n ;
  pot3 n = ss (n.s ++ "tusen") ;
  pot3plus n m = ss (n.s ++ "tusen" ++ m.s) ;

}