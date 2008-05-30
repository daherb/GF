incomplete concrete VerbScand of Verb = CatScand ** open CommonScand, ResScand in {

  flags optimize=all_subs ;

  lin
    UseV = predV ;
{-
    ComplV2 v np = insertObj (\\_ => v.c2 ++ np.s ! accusative) (predV v) ;
    ComplV3 v np np2 = 
      insertObj 
        (\\_ => v.c2 ++ np.s ! accusative ++ v.c3 ++ np2.s ! accusative) 
        (predV v) ;
-}
    ComplVV v vp = insertObj (\\a => v.c2 ++ infVP vp a) (predV v) ;
    ComplVS v s  = insertObj (\\_ => conjThat ++ s.s ! Sub) (predV v) ;
    ComplVQ v q  = insertObj (\\_ => q.s ! QIndir) (predV v) ;
    ComplVA  v ap = 
      insertObj (\\a => ap.s ! agrAdj a.gn DIndef) (predV v) ;
{-
    ComplV2V v np vp = 
      insertObj
        (\\a => v.c3 ++ infVP vp a)
        (insertObj (\\_ => v.c2 ++ np.s ! accusative) (predV v)) ;
    ComplV2S v np s = 
      insertObj
        (\\_ => conjThat ++ s.s ! Sub)
        (insertObj (\\_ => v.c2 ++ np.s ! accusative) (predV v)) ;
    ComplV2Q v np q = 
      insertObj
        (\\_ => q.s ! QIndir)
        (insertObj (\\_ => v.c2 ++ np.s ! accusative) (predV v)) ;
    ComplV2A v np ap = 
      insertObj
        (\\_ => ap.s ! agrAdj np.a.gn DIndef)
        (insertObj (\\_ => v.c2 ++ np.s ! accusative) (predV v)) ;
-}
    UseComp comp = insertObj (\\a => comp.s ! agrAdj a.gn DIndef) (predV verbBe) ;

    CompAP ap = ap ;
    CompNP np = {s = \\_ => np.s ! accusative} ;
    CompAdv a = {s = \\_ => a.s} ;

    AdvVP vp adv = insertAdv adv.s vp ;
    AdVVP adv vp = insertAdV adv.s vp ;


----    ReflV2 v = insertObj (\\a => v.c2 ++ reflPron a) (predV v) ;

    PassV2 v = 
      insertObj 
        (\\a => v.s ! VI (VPtPret (agrAdj a.gn DIndef) Nom)) 
        (predV verbBecome) ;

}
