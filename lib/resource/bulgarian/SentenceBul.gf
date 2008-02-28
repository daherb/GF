concrete SentenceBul of Sentence = CatBul ** open Prelude, ResBul in {

  flags optimize=all_subs ;

  lin
    PredVP np vp = mkClause (np.s ! vp.subjRole) np.a vp ;

    PredSCVP sc vp = mkClause sc.s {gn=GSg Masc; p=P3} vp ;

    ImpVP vp = {
      s = \\p,gn => 
        let agr = {gn = gn ; p = P2} ;
            verb = vp.imp ! p ! numGenNum gn ;
            compl = vp.s2 ! agr
        in
        verb ++ compl
    } ;

    SlashV2 np v2 = 
      mkClause (np.s ! RSubj) np.a (predV v2) ** {c2 = v2.c2} ;

    SlashVVV2 np vv v2 = 
      mkClause (np.s ! RSubj) np.a
        (let vp = predV vv
         in { s   = \\t,a,p,agr,q => vp.s ! t ! a ! p ! agr ! q ++ "��" ++ v2.s ! (VPres (numGenNum agr.gn) agr.p) ;
              imp = vp.imp ;
              s2 = vp.s2 ;
              subjRole = vp.subjRole
            }) **
        {c2 = v2.c2} ;

    AdvSlash slash adv = {
      s  = \\t,a,b,o => slash.s ! t ! a ! b ! o ++ adv.s ;
      c2 = slash.c2
    } ;

    SlashPrep cl prep = cl ** {c2 = prep} ;
    
    SlashVS np vs slash = 
      mkClause (np.s ! RSubj) np.a 
        (insertObj (\\_ => "��" ++ slash.s) (predV vs))  **
      {c2 = slash.c2} ;

    EmbedS  s  = {s = "," ++ "��" ++ s.s} ;
    EmbedQS qs = {s = qs.s ! QIndir} ;

    UseCl t a p cl = {
      s = t.s ++ a.s ++ p.s ++ cl.s ! t.t ! a.a ! p.p ! Main
    } ;
    UseQCl t a p cl = {
      s = \\q => t.s ++ a.s ++ p.s ++ cl.s ! t.t ! a.a ! p.p ! q
    } ;
    UseRCl t a p cl = {
      s    = \\r => t.s ++ a.s ++ p.s ++ cl.s ! t.t ! a.a ! p.p ! r ;
      role = cl.role
    } ;
    UseSlash t a p cl = {
      s = t.s ++ a.s ++ p.s ++ cl.s ! t.t ! a.a ! p.p ! Main ;
      c2 = cl.c2
    } ;

    AdvS a s = {s = a.s ++ "," ++ s.s} ;
}