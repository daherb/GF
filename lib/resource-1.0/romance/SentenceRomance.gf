incomplete concrete SentenceRomance of Sentence = 
  CatRomance ** open Prelude, CommonRomance, ResRomance in {

  flags optimize=all_subs ;

  lin
    PredVP np vp = mkClause (np.s ! Aton Nom) np.a vp ;

    PredSCVP sc vp = mkClause sc.s (agrP3 Masc Sg) vp ;

    ImpVP vp = {
      s = \\pol,aag => 
        let 
          agr   = aag ** {p = P2} ;
          verb  = (vp.s ! VPImperat).fin ! agr
        in
        verb ++ vp.comp ! agr ++ vp.ext ! pol ---- neg,clit
      } ;

    SlashV2 np v2 = 
      mkClause 
        (np.s ! Aton Nom) np.a 
        (predV v2) **
      {c2 = v2.c2} ;

    SlashVVV2 np vv v2 = 
      mkClause
        (np.s ! Aton Nom) np.a
        (insertComplement (\\a => prepCase vv.c2.c ++ v2.s ! VInfin) (predV v2)) ** 
      {c2 = v2.c2} ;

    AdvSlash slash adv = {
      s  = \\t,a,b,m => slash.s ! t ! a ! b ! m ++ adv.s ;
      c2 = slash.c2
      } ;

    SlashPrep cl prep = cl ** {c2 = {s = prep.s ; c = prep.c ; isDir = False}} ;

    EmbedS  s  = {s = conjThat ++ s.s ! Indic} ; --- mood
    EmbedQS qs = {s = qs.s ! QIndir} ;
    EmbedVP vp = {s = infVP vp (agrP3 Masc Sg)} ; --- agr

}
