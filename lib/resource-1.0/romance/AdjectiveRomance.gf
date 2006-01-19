incomplete concrete AdjectiveRomance of Adjective = 
  CatRomance ** open DiffRomance, ResRomance, Prelude in {

  lin

    PositA  a = {
      s = \\ap => a.s ! AF (APosit ap) Nom ;
      isPre = True
      } ;
    ComparA a np = {
      s = \\_ => a.s ! AF ACompar Nom ++ conjThan ++ np.s ! nominative ; 
      isPre = False
      } ;

-- $SuperlA$ belongs to determiner syntax in $Noun$.

    ComplA2 a np = {
      s = \\ap => a.s ! AF (APosit ap) Nom ++ a.c2 ++ np.s ! accusative ; 
      isPre = False
      } ;

    ReflA2 a = {
      s = \\ap => a.s ! AF (APosit ap) Nom ++ a.c2 ++ 
                  reflPron (agrP3 Utr Sg) ; ---- 
      isPre = False
      } ;

    SentAP ap sc = {
      s = \\a => ap.s ! a ++ sc.s ; 
      isPre = False
      } ;

    AdAP ada ap = {
      s = \\a => ada.s ++ ap.s ! a ;
      isPre = ap.isPre
      } ;

    UseA2 a = a ;

}
