concrete AdverbBul of Adverb = CatBul ** open ResBul, Prelude in {
  lin
    PositAdvAdj a = {s = a.adv} ;
    ComparAdvAdj cadv a np = {
      s = cadv.s ++ "��" ++ "-" ++ a.s ! ASg Neut Indef ++ "��" ++ np.s ! RObj Acc
      } ;
    ComparAdvAdjS cadv a s = {
      s = cadv.s ++ "��" ++ "-" ++ a.s ! ASg Neut Indef ++ "��" ++ "�������" ++ s.s
      } ;

    PrepNP prep np = {s = prep.s ++ np.s ! RObj prep.c} ;

    AdAdv = cc2 ;

    SubjS = cc2 ;

    AdnCAdv cadv = {s = cadv.sn ++ "��"} ;
}
