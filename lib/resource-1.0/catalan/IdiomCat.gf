concrete IdiomCat of Idiom = CatCat ** 
  open MorphoCat, ParadigmsCat, BeschCat, Prelude in {

  flags optimize=all_subs ;

  lin
    ExistNP np = mkClause [] (agrP3 Masc Sg) 
        (insertClit2 "hi" (insertComplement (\\_ => np.s ! Ton Acc) (predV haver_V))) ;
    GenericCl vp = mkClause "hom" (agrP3 Masc Sg) vp ;
    ImpersCl vp = mkClause [] (agrP3 Masc Sg) vp ;


    ProgrVP vp = 
      insertComplement 
        (\\agr => 
           let 
             clpr = pronArg agr.n agr.p vp.clAcc vp.clDat ;
             obj  = clpr.p2 ++ vp.comp ! agr ++ vp.ext ! Pos ---- pol
           in
           (vp.s ! VPGerund).inf ! (aagr agr.g agr.n) ++ clpr.p1 ++ obj
        )
        (predV (verbV (estar_54 "estar"))) ;

}
