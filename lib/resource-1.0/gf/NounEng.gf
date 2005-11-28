concrete NounEng of Noun = CatEng ** open ResEng, Prelude in {

  flags optimize=all_subs ;

  lin
    DetCN det cn = {s = \\c => det.s ++ cn.s ! det.n ! c} ** agrP3 det.n ;
    UsePN pn = pn ** agrP3 Sg ;
    UsePron p = p ;

    MkDet pred quant num = {
      s = pred.s ++ quant.s ++ num.s ; 
      n = quant.n
      } ;

    PossPronSg p = {s = p.s ! Gen ; n = Sg} ;
    PossPronPl p = {s = p.s ! Gen ; n = Pl} ;

    NoNum, NoPredet = {s = []} ;
    NumInt n = n ;

    CardNumeral numeral = {s = numeral.s ! NCard} ;
    OrdNumeral  numeral = {s = numeral.s ! NOrd} ;

    NumSuperl a = {s = a.s ! AAdj Superl} ;

    DefSg = {s = "the" ; n = Sg} ;
    DefPl = {s = "the" ; n = Pl} ;

    IndefSg = {s = "a" ; n = Sg} ;
    IndefPl = {s = []  ; n = Pl} ;

    ComplN2 f x = {s = \\n,c => f.s ! n ! Nom ++ f.c2 ++ x.s ! c} ;
    ComplN3 f x = {s = \\n,c => f.s ! n ! Nom ++ f.c2 ++ x.s ! c ; c2 = f.c3} ;

    AdjCN ap cn = {s = \\n,c => preOrPost ap.isPre ap.s (cn.s ! n ! c)} ;

    SentCN cn s = {s = \\n,c => cn.s ! n ! c ++ conjThat ++ s.s} ;
    QuestCN cn qs = {s = \\n,c => cn.s ! n ! c ++ qs.s ! QIndir} ;

    UseN n = n ;

}
