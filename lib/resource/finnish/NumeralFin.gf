concrete NumeralFin of Numeral = CatFin **  open Prelude, ParadigmsFin, MorphoFin in {

-- Notice: possessive forms are not used. They get wrong, since every
-- part is made to agree in them.

flags optimize = all_subs ;

lincat 
  Sub1000000 = {s : CardOrd => Str ; n : Number} ;
  Digit = {s : CardOrd => Str} ;
  Sub10, Sub100, Sub1000 = {s : NumPlace => CardOrd => Str ; n : Number} ;

lin 
  num x = x ;
  n2 = co
    (nhn (mkSubst "a" "kaksi" "kahde" "kahte" "kahta" "kahteen" "kaksi" "kaksi"
    "kaksien" "kaksia" "kaksiin")) 
    (ordN "a" "kahdes") ; --- toinen
  n3 = co 
    (nhn (mkSubst "a" "kolme" "kolme" "kolme" "kolmea" "kolmeen" "kolmi" "kolmi"
    "kolmien" "kolmia" "kolmiin"))
    (ordN "a" "kolmas") ;
  n4 = co (regN "nelj�") (ordN "�" "nelj�s") ;
  n5 = co (reg3N "viisi" "viiden" "viisi�") (ordN "�" "viides") ;
  n6 = co (reg3N "kuusi" "kuuden" "kuusia") (ordN "a" "kuudes") ; 
  n7 = co 
    (nhn (mkSubst "�" "seitsem�n" "seitsem�" "seitsem�" "seitsem��" 
    "seitsem��n" "seitsemi" "seitsemi" "seitsemien" "seitsemi�"
    "seitsemiin"))
    (ordN "�" "seitsem�s") ;
  n8 = co 
    (nhn (mkSubst "a" "kahdeksan" "kahdeksa" "kahdeksa" "kahdeksaa" 
    "kahdeksaan" "kahdeksi" "kahdeksi" "kahdeksien" "kahdeksia"
    "kahdeksiin"))
    (ordN "a" "kahdeksas") ;
  n9 = co
     (nhn (mkSubst "�" "yhdeks�n" "yhdeks�" "yhdeks�" "yhdeks��" 
    "yhdeks��n" "yhdeksi" "yhdeksi" "yhdeksien" "yhdeksi�" "yhdeksiin"))
     (ordN "�" "yhdeks�s") ;

  pot01 = 
   {s = table {
      NumAttr => \\_ => [] ; 
      NumIndep => yksiN.s
      } ;
    n = Sg
    } ;
  pot0 d = {n = Pl ; s = \\_ => d.s} ;
  pot110 =
   {s = \\_ => kymmenenN.s ;
    n = Pl
    } ;

  pot111 = {n = Pl ; s = \\_,c => yksiN.s ! c ++"toista"} ; ---- yhdes
  pot1to19 d = {n = Pl ; s = \\_,c => d.s ! c ++"toista"} ;
  pot0as1 n = n ;

  pot1 d = {n = Pl ; s = \\_,c => d.s ! c ++ kymmentaN.s ! c} ;
  pot1plus d e = {
    n = Pl ; 
    s = \\_,c => d.s ! c ++ kymmentaN.s ! c ++ e.s ! NumIndep ! c
    } ;
  pot1as2 n = n ;
  pot2 d = {n = Pl ; s = \\_,c => d.s ! NumAttr ! c ++ sataaN.s ! d.n ! c} ; ----
  pot2plus d e = {
    n = Pl ; 
    s = \\_,c => d.s ! NumAttr ! c ++ sataaN.s ! d.n ! c ++ e.s ! NumIndep ! c
    } ;
  pot2as3 n = {n = n.n  ; s = n.s ! NumIndep} ;
  pot3 d = {n = Pl ; s = \\c => d.s ! NumAttr ! c ++ tuhattaN.s ! d.n ! c} ; ----
  pot3plus d e = {
    n = Pl ;
    s = \\c => d.s ! NumAttr ! c ++ tuhattaN.s ! d.n ! c ++ e.s ! NumIndep ! c
    } ;

oper
  co : (c,o : {s : NForm => Str}) -> {s : CardOrd => Str} = \c,o -> {
    s = table {
      NCard nf => c.s ! nf ;
      NOrd  nf => o.s ! nf
      }
    } ;

-- Too much trouble to infer vowel, cf. "kuudes" vs. "viides".

  ordN : Str -> Str -> {s : NForm => Str} = \a,sadas -> 
    let
      sada = init sadas
    in
    mkN 
      sadas (sada + "nnen") (sada + "nten" + a) (sada + "tt" + a) (sada + "nteen")
      (sada + "nsin" + a) (sada + "nsiss" + a) (sada + "nsien")
      (sada + "nsi" + a) (sada + "nsiin") ;

param 
  NumPlace = NumIndep | NumAttr  ;

oper
  yksiN = co 
    (nhn (mkSubst "�" "yksi" "yhde" "yhte" "yht�" "yhteen" "yksi" "yksi" 
     "yksien" "yksi�" "yksiin")) 
    (ordN "�" "yhdes") ; ---- ensimm�inen
  kymmenenN = co 
    (nhn (mkSubst "�" "kymmenen" "kymmene" "kymmene" "kymment�" 
    "kymmeneen" "kymmeni" "kymmeni" "kymmenien" "kymmeni�" "kymmeniin")) 
    (ordN "�" "kymmenes") ;
  sataN = co 
    (nhn (sLukko "sata")) 
    (ordN "a" "sadas") ;

  tuhatN = co
    (nhn (mkSubst "a" "tuhat" "tuhanne" "tuhante" "tuhatta" "tuhanteen"
    "tuhansi" "tuhansi" "tuhansien" "tuhansia" "tuhansiin"))
    (ordN "a" "tuhannes")  ;

  kymmentaN =
   {s = table {
      NCard (NCase Sg Nom) => "kymment�" ;
      k => kymmenenN.s ! k
      }
    } ;

  sataaN : {s : Number => CardOrd => Str} = {s = table {
    Sg => sataN.s ;
    Pl => table {
      NCard (NCase Sg Nom) => "sataa" ;
      k => sataN.s ! k
      }
    } 
  } ;

  tuhattaN = {s = table {
    Sg => tuhatN.s ;
    Pl => table {
      NCard (NCase Sg Nom) => "tuhatta" ;
      k => tuhatN.s ! k
      }
    }
  } ;

}

