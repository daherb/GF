concrete AdjectiveBul of Adjective = CatBul ** open ResBul, Prelude in {
  lin
    PositA  a = {
      s = \\aform => a.s ! aform ;
      adv = a.adv ;
      isPre = True
      } ;

    ComparA a np = {
      s = \\aform => "��" ++ "-" ++ a.s ! aform ++ "��" ++ np.s ! RObj Acc ; 
      adv = "��" ++ "-" ++ a.adv ++ "��" ++ np.s ! RObj Acc ;
      isPre = True
      } ;

-- $SuperlA$ belongs to determiner syntax in $Noun$.

    ComplA2 a np = {
      s = \\aform => a.s ! aform ++ a.c2 ++ np.s ! RObj Acc ; 
      adv = a.adv ++ a.c2 ++ np.s ! RObj Acc ; 
      isPre = True
      } ;

    ReflA2 a = {
      s = \\aform => a.s ! aform ++ a.c2 ++ ["���� ��"] ; 
      adv = a.adv ++ a.c2 ++ ["���� ��"] ; 
      isPre = False
      } ;

    SentAP ap sc = {
      s = \\a => ap.s ! a ++ sc.s ;
      adv = ap.adv ++ sc.s ;
      isPre = False
      } ;

    AdAP ada ap = {
      s = \\a => ada.s ++ ap.s ! a ;
      adv = ada.s ++ ap.adv ;
      isPre = ap.isPre
      } ;

    UseA2 a = a ;
}
