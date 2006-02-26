concrete IdiomNor of Idiom = CatNor ** 
  open MorphoNor, ParadigmsNor, IrregNor, Prelude in {

  flags optimize=all_subs ;

  lin
    ExistNP np = 
      mkClause "det" (agrP3 neutrum Sg) (insertObj 
        (\\_ => np.s ! accusative) (predV (depV finne_V))) ;
    ImpersCl vp = mkClause "det" (agrP3 neutrum Sg) vp ;
    GenericCl vp = mkClause "man" (agrP3 neutrum Sg) vp ;

    ProgrVP vp = 
      insertObj (\\a => ["ved �"] ++ infVP vp a) (predV verbBe) ;

}

