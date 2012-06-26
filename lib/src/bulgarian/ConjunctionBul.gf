concrete ConjunctionBul of Conjunction = 
  CatBul ** open ResBul, Coordination, Prelude, Predef in {
  flags coding=cp1251 ;


  flags optimize=all_subs ;

  lin
    ConjS conj ss = {
      s = (linCoordSep [])!conj.distr!conj.conj++ss.s!conj.distr!conj.conj;
      } ;

    ConjAdv conj ss = {
      s = (linCoordSep [])!conj.distr!conj.conj++ss.s!conj.distr!conj.conj;
      } ;

    ConjNP conj ss = {
      s = \\role => (linCoordSep [])!conj.distr!conj.conj++ss.s!conj.distr!conj.conj!role;
      a = {gn = conjGenNum (gennum (AMasc NonHuman) conj.n) ss.a.gn; p = ss.a.p}
      } ;

    ---- RS rules by AR 7/4/2010 to make API compile
    ConjRS conj ss = {
      s = \\role => (linCoordSep [])!conj.distr!conj.conj++ss.s!conj.distr!conj.conj!role
      } ;

    ConjAP conj ss = {
      s     = \\aform => (linCoordSep [])!conj.distr!conj.conj++ss.s!conj.distr!conj.conj!aform;
      adv   =            (linCoordSep [])!conj.distr!conj.conj++ss.adv!conj.distr!conj.conj;
      isPre = ss.isPre
      } ;

-- These fun's are generated from the list cat's.
    BaseS x y  = {s  = \\d,t=>x.s++linCoord!t++ y.s} ; 
    ConsS x xs = {s  = \\d,t=>x.s++(linCoordSep comma)!d!t++xs.s!d!t} ;

    BaseAdv x y  = {s  = \\d,t=>x.s++linCoord!t++ y.s} ; 
    ConsAdv x xs = {s  = \\d,t=>x.s++(linCoordSep comma)!d!t++xs.s!d!t} ;

    BaseNP x y =
      {s = \\d,t,role=>x.s!role++linCoord!t++y.s!role; 
       a = conjAgr x.a y.a} ;
    ConsNP x xs =
      {s = \\d,t,role=>x.s!role++(linCoordSep comma)!d!t++xs.s!d!t!role; 
       a = conjAgr xs.a x.a} ;

    BaseRS x y =
      {s = \\d,t,role=>x.s!role++linCoord!t++y.s!role} ;
    ConsRS x xs =
      {s = \\d,t,role=>x.s!role++(linCoordSep comma)!d!t++xs.s!d!t!role} ;

    BaseAP x y =
      {s  = \\d,t,aform=>x.s!aform++linCoord!t++y.s!aform; 
       adv= \\d,t      =>x.adv    ++linCoord!t++y.adv;
       isPre = andB x.isPre y.isPre} ; 
    ConsAP x xs =
      {s  = \\d,t,aform=>x.s!aform++(linCoordSep comma)!d!t++xs.s!d!t!aform; 
       adv= \\d,t      =>x.adv    ++(linCoordSep comma)!d!t++xs.adv!d!t;
       isPre = andB x.isPre xs.isPre} ; 

  lincat
    [S] = {s : Bool => Ints 2 => Str} ;
    [Adv] = {s : Bool => Ints 2 => Str} ;
    [NP] = {s : Bool => Ints 2 => Role  => Str; a : Agr} ;
    [RS] = {s : Bool => Ints 2 => Agr   => Str} ;
    [AP] = {s : Bool => Ints 2 => AForm => Str; adv : Bool => Ints 2 => Str; isPre : Bool} ;
}
