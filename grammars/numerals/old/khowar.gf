include numerals.Abs.gf ;

-- 2 has a non-general variant "joow�loo" ;

param DForm = unit | ten S100 | teen ; 
param Size = sg | pl | more100;
param Par20 = even | odd ; 
param S100 = attr | preceded ;
param S1000 = indep | dep | lakh ;

oper LinDigit = {s : DForm => Str ; size : Size ; par20 : Par20} ;

lincat Numeral = {s : Str} ;
lincat Digit = LinDigit ;
lincat Sub10 = LinDigit ;
lincat Sub100 = {s : S100 => Str ; size : Size} ;
lincat Sub1000 = {s : S1000 => Str ; size : Size } ;
lincat Sub1000000 = {s : Str} ;
lin num x0 =
  {s = "/L" ++ x0.s ++ "L/"} ; -- Latin A Supplement

oper mkNum : Str -> Str -> Par20 -> LinDigit = \s -> \tw -> \p20 -> 
  {s = table {unit => s ; teen => "jo.sh" + "-" + s ; ten _ => tw ++ "b�sher"} ; size = pl ; par20 = p20} ;

-- lin n1 = mkNum variants {"�" ; "�w�loo"} ; 
lin n2 = 
  {s = table {unit => "joo" ; teen => "jo.sh" + "-" + "joo" ; ten attr => "b�sher" ; ten preceded => "�" ++ "b�sher" } ; size = pl ; par20 = even };
lin n3 = 
  {s = table {unit => "troi" ; teen => "jo.sh" + "-" + "troi" ; ten attr => "b�sher" ; ten preceded => "�" ++ "b�sher" } ; size = pl ; par20 = odd };
lin n4 = mkNum "cho.r" "joo" even ;
lin n5 = mkNum "po.nj" "joo" odd ;
lin n6 = mkNum "ch�i" "troi" even ;
lin n7 = mkNum "so.t" "troi" odd ;
lin n8 = mkNum "o.sht" "ch�i" even ;
lin n9 = mkNum "nyun" "ch�i" odd ;

lin pot01  =
  {s = table {unit => "�" ; _ => "dummy" } ; size = sg ; par20 = odd};
lin pot0 d = d ;
lin pot110 = {s = table {_ => "jo.sh" } ; size = pl} ;
lin pot111 = {s = table {_ => "jo.sh" + "-" + "�" } ; size = pl} ;
lin pot1to19 d = {s = table {_ => d.s ! teen }; size = pl} ;
lin pot0as1 n = {s = table {_ => n.s ! unit } ; size = n.size} ;
lin pot1 d = {s = table {f => table {even => d.s ! ten f ; odd => d.s ! ten f ++ "jo.sh" } ! d.par20 } ; size = pl} ;
lin pot1plus d e = {s = table {f => table {even => d.s ! ten f ++ e.s ! unit ; odd => d.s ! ten f ++ e.s ! teen } ! d.par20 }; size = pl} ; 
lin pot1as2 n = {s = table {indep => n.s ! attr ; dep => n.s ! preceded ; lakh => "dummy"} ; size = n.size} ;
lin pot2 d = 
  {s = table {lakh => table {sg => "lakh" ; _ => d.s ! unit ++ "lakh"} ! d.size ; 
              _ => table {sg => "sho.r" ; _ => d.s ! unit ++ "sho.r" } ! d.size } ; 
   size = more100 };
lin pot2plus d e = 
  {s = table {lakh => table {sg => "lakh" ; _ => d.s ! unit ++ "lakh"} ! d.size ++ table {sg => [] ; _ => e.s ! preceded } ! e.size ++ "haz�r" ; 
	      _ => table {sg => "sho.r" ; _ => d.s ! unit ++ "sho.r" } ! d.size ++ "och�" ++ e.s ! preceded } ;
   size = more100} ;
lin pot2as3 n = {s = table {sg => [] ++ variants {"�" ; "�w�loo"} ; _ => n.s ! indep} ! n.size } ;
lin pot3 n = {s = table {pl => n.s ! indep ++ "haz�r" ; sg => "haz�r" ; more100 => n.s ! lakh} ! n.size} ;
lin pot3plus n m = {s = table {pl => n.s ! indep ++ "haz�r" ; sg => "haz�r" ; more100 => n.s ! lakh} ! n.size ++ m.s ! dep} ;
