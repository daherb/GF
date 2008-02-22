concrete SentenceBul of Sentence = CatBul ** open Prelude, ResBul in {

  flags optimize=all_subs ;

  lin
    PredVP np vp = mkClause (np.s ! Nom) np.a vp ;

    ImpVP vp = {
      s = \\p,gn => 
        let agr = {gn = gn ; p = P2} ;
            verb = vp.imp ! p ! numGenNum gn ;
            compl = vp.s2 ! agr
        in
        verb ++ compl
    } ;

    SlashV2 np v2 = 
      mkClause (np.s ! Nom) np.a (predV v2) ** {c2 = v2.c2} ;

    EmbedS  s  = {s = "," ++ "��" ++ s.s} ;
    EmbedQS qs = {s = qs.s ! QIndir} ;

    UseCl t a p cl = {
      s = t.s ++ a.s ++ p.s ++ cl.s ! t.t ! a.a ! p.p ! ODir
    } ;
    UseQCl t a p cl = {
      s = \\q => t.s ++ a.s ++ p.s ++ cl.s ! t.t ! a.a ! p.p ! q
    } ;
}