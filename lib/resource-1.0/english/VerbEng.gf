concrete VerbEng of Verb = CatEng ** open ResEng in {

  flags optimize=all_subs ;

  lin
    UseV = predV ;
    ComplV2 v np = insertObj (\\_ => v.c2 ++ np.s ! Acc) (predV v) ;
    ComplV3 v np np2 = 
      insertObj (\\_ => v.c2 ++ np.s ! Acc ++ v.c3 ++ np2.s ! Acc) (predV v) ;

    ComplVV v vp = insertObj (\\a => v.c2 ++ infVP vp a) (predV v) ;
    ComplVS v s  = insertObj (\\_ => conjThat ++ s.s) (predV v) ;
    ComplVQ v q  = insertObj (\\_ => q.s ! QIndir) (predV v) ;

    ComplVA  v    ap = insertObj (ap.s) (predV v) ;
    ComplV2A v np ap = 
      insertObj (\\_ => v.c2 ++ np.s ! Acc ++ ap.s ! np.a) (predV v) ;

    UseComp comp = insertObj comp.s (predAux auxBe) ;

    AdvVP vp adv = insertObj (\\_ => adv.s) vp ;
----    AdVVP adv vp = insertAdV adv.s vp ;

    ReflV2 v = insertObj (\\a => v.c2 ++ reflPron ! a) (predV v) ;

    PassV2 v = {s = \\_ => v.s ! VPPart} ;

    UseVV, UseVS, UseVQ = \vv -> {s = vv.s ; c2 = []} ; -- no "to"

    CompAP ap = ap ;
    CompNP np = {s = \\_ => np.s ! Acc} ;
    CompAdv a = {s = \\_ => a.s} ;

    EmbedS  s  = {s = conjThat ++ s.s} ;
    EmbedQS qs = {s = qs.s ! QIndir} ;
    EmbedVP vp = {s = infVP vp (agrP3 Sg)} ; --- agr

}
