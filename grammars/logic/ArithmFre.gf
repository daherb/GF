--# -path=.:../prelude

concrete ArithmFre of Arithm = LogicFre ** open ResFre in {

lin Nat = {g = masc ; s = nomReg "nombre"} ;
zero = {g = masc ; s = table {c => (prep ! c) ++ "z�ro"}} ;
succ n =
  {g = masc ; s = table {c => defin ! sg ! masc ! c ++ "successeur" ++ n.s ! dd}} ;
EqNat k n = mkPropA2 aa k (adjAl "�ga") n ;
LtNat k n = mkPropA2 aa k (adjReg "inf�rieur") n ;
Div k n = mkPropA2 nom k (table {_ => nomReg "divisible"}) n ; --- par !

Even n = mkPropA1 n (adjReg "pair") ;
Odd n = mkPropA1 n (adjReg "impair") ;
Prime n = mkPropA1 n (adjEr "premi") ;

lin one  =
  {g = masc ; s = table {c => (prep ! c) ++ "un"}} ;
lin two  =
  {g = masc ; s = table {c => (prep ! c) ++ "deux"}} ;
lin sum m n = {g = fem ; s = table {
  c => defin ! sg ! fem ! c ++ "somme" ++ m.s ! dd ++ "et" ++ n.s ! dd}} ;
lin prod m n = {g = masc ; s = table {
  c => defin!sg!fem!c ++ "produit" ++ m.s ! dd ++ "et" ++ n.s ! dd}} ;
lin evax1  =
  {s = "par"++"le"++"premier"++"axiome"++"de"++"parit�,"++"z�ro"++"est"++"pair"} ;
lin evax2 n c =
  {s = c.s ++ "."++"Par"++"le"++"deuxi�me"++"axiome"++"de"++"parit�,"++"le"++"successeur" ++ (n.s ! dd) ++ "est"++"impair"} ;
lin evax3 n c =
  {s = c.s ++ "."++"Par"++"le"++"troisi�me"++"axiome"++"de"++"parit�,"++"le"++"successeur" ++ (n.s ! dd) ++ "est"++"pair"} ;
lin eqax1  =
  {s = "par"++"le"++"premier"++"axiome"++"d'�galit�,"++"z�ro"++"est"++"�gal"++"a"++"lui-m�me"} ;
lin eqax2 m n c =
  {s = c.s ++ "."++"Par"++"le"++"deuxi�me"++"axiome"++"d'�galit�,"++"le"++"successeur" ++ (m.s ! dd) ++ "est"++"�gal"++"au"++"successeur" ++ n.s ! dd} ;
lin IndNat C d e =
  {s = "nous"++"nous"++"servons"++"d'induction."++"Pour"++"la"++"base," ++ d.s ++ "."++"Pour"++"le"++"pas"++"d'induction,"++"consid�rons"++"un"++"nombre" ++ e.$0 ++ "et"++"supposons" ++ que ++ (C.s ! ind) ++ "(" ++ e.$1 ++ ")" ++ "." ++ e.s ++ "Donc,"++"pour"++"tous"++"les"++"nombres" ++ C.$0 ++ "," ++ C.s ! ind} ;
}
