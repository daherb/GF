concrete AdverbLav of Adverb = CatLav ** open ResLav, Prelude in {

  lin
  
    PositAdvAdj a = {s = a.s ! (AAdv Posit)} ;
	
    ComparAdvAdj cadv a np = {
      s = cadv.s ++ a.s ! (AAdv cadv.d) ++ cadv.p ++ np.s ! Nom -- TODO vajag ar� '�tr�ks par J�ni' un '�tr�ks nek� J�nis' pie more_CAdv  
	  -- TODO - vai te tie��m veido '�tr�k par J�ni', kas ir pareizais adverbs? nevis '�tr�ks par j�ni'...
      } ;
    ComparAdvAdjS cadv a s = {
      s = cadv.s ++ a.s ! (AAdv cadv.d) ++ cadv.p ++ s.s
      } ;   

    PrepNP prep np = {s = prep.s ++ np.s ! (prep.c ! (fromAgr np.a).n)} ; --FIXME - postpoz�cijas priev�rdi

    AdAdv = cc2 ;
    SubjS = cc2 ;

    AdnCAdv cadv = {
	  s = case cadv.d of {
		Posit => cadv.s ++ cadv.p;
		_ => NON_EXISTENT
	  }
	};
}
