concrete ExtraNor of ExtraNorAbs = ExtraScandNor ** open CommonScand, ResNor in {

  lin
    PossNP np pro = {
      s = \\c => np.s ! NPNom ++ pro.s ! NPPoss (gennumAgr np.a) ; ---- c 
      a = np.a
      } ;
}
