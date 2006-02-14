incomplete concrete NounRomance of Noun =
   CatRomance ** open CommonRomance, ResRomance, Prelude in {

  flags optimize=all_subs ;

  lin
    DetCN det cn = 
      let 
        g = cn.g ;
        n = det.n
      in {
        s = \\c => det.s ! g ! npform2case c ++ cn.s ! n ;
        a = agrP3 g n ;
        hasClit = False
        } ;

    UsePN = pn2np ;

    UsePron p = p ;

    PredetNP pred np = {
      s = \\c => pred.s ! aagr (np.a.g) (np.a.n) ! npform2case c ++  --- subtype
                 np.s ! case2npform pred.c ;
      a = np.a ;
      hasClit = False
      } ;

    DetSg quant ord = {
      s = \\g,c => quant.s ! g ! c ++ ord.s ! aagr g Sg ;
      n = Sg
      } ;
    DetPl quant num ord = {
      s = \\g,c => quant.s ! g ! c ++ num.s ! g ++ ord.s ! aagr g Pl ;
      n = Pl
      } ;

    SgQuant q = {s = q.s ! Sg} ;
    PlQuant q = {s = q.s ! Pl} ;

    PossPron p = {
      s = \\n,g,c => prepCase c ++ p.s ! Poss (aagr g n) ---- il mio!
      } ;

    NoNum = {s = \\_ => []} ;
    NoOrd = {s = \\_ => []} ;

    NumInt n = {s = \\_ => n.s} ;
    OrdInt n = {s = \\_ => n.s ++ "ème"} ; ---

    NumNumeral numeral = {s = \\g => numeral.s ! NCard g} ;
    OrdNumeral numeral = {s = \\a => numeral.s ! NOrd a.g a.n} ;

    AdNum adn num = {s = \\a => adn.s ++ num.s ! a} ;

    OrdSuperl adj = {s = \\a => adj.s ! Superl ! AF a.g a.n} ;

    DefArt = {
      s = \\n,g,c => artDef g n c
      } ;

    IndefArt = {
      s = \\n,g,c => artIndef g n c
      } ;

    MassDet = {
      s = \\g,c => partitive g c ; 
      n = Sg
      } ;

-- This is based on record subtyping.

    UseN, UseN2, UseN3 = \noun -> noun ;

    ComplN2 f x = {
      s = \\n => f.s ! n ++ appCompl f.c2 x.s ;
      g = f.g ;
      } ;
    ComplN3 f x = {
      s = \\n => f.s ! n ++ appCompl f.c2 x.s ;
      g = f.g ;
      c2 = f.c3
      } ;

    AdjCN ap cn = 
      let 
        g = cn.g 
      in {
        s = \\n => preOrPost ap.isPre (ap.s ! (AF g n)) (cn.s ! n) ;
        g = g ;
        } ;

    RelCN cn rs = let g = cn.g in {
      s = \\n => cn.s ! n ++ rs.s ! Indic ! agrP3 g n ; --- mood
      g = g
      } ;
    SentCN  cn sc = let g = cn.g in {
      s = \\n => cn.s ! n ++ sc.s ;
      g = g
      } ;
    AdvCN  cn sc = let g = cn.g in {
      s = \\n => cn.s ! n ++ sc.s ;
      g = g
      } ;

}
