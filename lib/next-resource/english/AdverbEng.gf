concrete AdverbEng of Adverb = CatEng ** open ResEng, Prelude in {

  lin
    PositAdvAdj a = {s = a.s ! AAdv} ;
    ComparAdvAdj cadv a np = {
      s = cadv.s ++ a.s ! AAdv ++ "than" ++ np.s ! Nom
      } ;
    ComparAdvAdjS cadv a s = {
      s = cadv.s ++ a.s ! AAdv ++ "than" ++ s.s
      } ;

    PrepNP prep np = {s = prep.s ++ np.s ! Acc} ;

    AdAdv = cc2 ;

    SubjS = cc2 ;
---b    AdvSC s = s ; --- this rule give stack overflow in ordinary parsing

    AdnCAdv cadv = {s = cadv.s ++ "than"} ;

}
