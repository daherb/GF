include numerals.Abs.gf ;
flags coding=latinasupplement ;

-- D^ is from implosive d IPA symbol
-- N Num 

param Size = sg | two | three | other ;

oper LinDigit = {s : Str ; size : Size} ;
lincat Digit = LinDigit ;
lincat Sub10 = LinDigit ;
lincat Sub100 = LinDigit ;
lincat Sub1000 = LinDigit ;
lincat Sub1000000 = {s : Str} ;

oper mkNum : Str -> LinDigit = \kunun ->
  {s = kunun ; size = other} ;

lin num x0 =
  {s = "/L" ++ x0.s ++ "L/"} ; -- for D^ 

lin n2 = {s = variants {"p�ll�w" ; "f�ll�w"} ; size = two }; 
lin n3 = {s = "k�n�n" ; size = three }  ;
lin n4 = mkNum (variants {"p�D^�w" ; "f�D^�w"}) ;
lin n5 = mkNum (variants {"p�aD^�" ; "f�aD^�"}) ;
lin n6 = mkNum (variants {"p�y�nd�" ; "f�y�nd�"}) ;
lin n7 = mkNum (variants {"p�p�ll�w" ; "f�p�ll�w"}) ;
lin n8 = mkNum (variants {"p�w�rD^�w" ; "f�w�rD^�w"}) ;
lin n9 = mkNum "l�mb�D^�" ;

oper thirty : Str = variants {("k�u" ++ "k�n�n") ; "t�l�at�n"} ;
oper two100 : Str = variants {"d�lm�g�" ++ "p�ll�w" ; "m�et�n"} ;
oper thousand : Str = variants {("d�lm�g�" ++ "k�m�") ; "d�b�k" ; "d�b�k"} ;

lin pot01  =
  {s = "m�nd�" ; size = sg};
lin pot0 d = d ;
lin pot110 = mkNum "k�m�" ; 
lin pot111 = mkNum ("k�m�" ++ "k�n" ++ "m�nd�") ;
lin pot1to19 d = mkNum ((variants {"k�m�" ++ "k�n" ; "t�r�"}) ++ d.s ) ;
lin pot0as1 n = n ;
lin pot1 d = mkNum (table {three => thirty ; _ => "k�u" ++ d.s} ! d.size) ; 
lin pot1plus d e = mkNum ((table {three => thirty ; _ => "k�u" ++ d.s} ! d.size) ++ "k�n" ++ e.s) ;
lin pot1as2 n = n ;
lin pot2 d = mkNum (table {sg => (variants {"d�lm�g�" ; "d�lm�k"}) ; two => two100 ; _ => "d�lm�g�" ++ d.s } ! d.size) ; 
lin pot2plus d e = mkNum ((table {two => two100 ; sg => (variants {"d�lm�g�" ; "d�lm�k"}) ; _ => "d�lm�g�" ++ d.s } ! d.size) ++ "k�n" ++ e.s) ;
lin pot2as3 n = {s = n.s} ;
lin pot3 n = {s = table {sg => thousand ; _ => "d�b�k" ++ n.s} ! n.size } ;
lin pot3plus n m = {s = table {sg => thousand ; _ => "d�b�k" ++ n.s} ! n.size ++ m.s} ;