--# -path=.:../abstract:../common:../../prelude

concrete IdiomRus of Idiom = CatRus ** open Prelude, ResRus, MorphoRus in {

  flags optimize=all_subs ;  coding=utf8 ;

  lin
    ExistNP = \bar ->
    {s =\\b,clf => case b of 
        {Pos =>  verbByut.s ! (getActVerbForm clf (pgen2gen bar.g) Sg P3) 
           ++ bar.s ! PF Nom No NonPoss;
        Neg => "не" ++ verbByut.s ! (getActVerbForm clf (pgen2gen bar.g) Sg P3) 
           ++ bar.s ! PF Nom No NonPoss
       }
} ;

    ExistIP Kto =
    let {  kto = Kto.s ! (PF Nom No NonPoss) } in 
       {s =  \\b,clf,_ => case b of 
        {Pos =>  kto ++ verbByut.s ! (getActVerbForm clf (pgen2gen Kto.g) Sg P3) ;
        Neg => kto ++ "не" ++ verbByut.s ! (getActVerbForm clf (pgen2gen Kto.g) Sg P3) 
       }
    } ;

    CleftAdv adv sen = {s= \\ b, clf =>  let ne= case b of {Pos =>[]; Neg =>"не"}
      in 
      "это" ++ ne ++ adv.s  ++ sen.s }; 

    CleftNP np rs = {s= \\ b, clf =>  let ne= case b of {Pos =>[]; Neg =>"не"}
      in 
      "это" ++ ne ++ np.s ! (PF Nom No NonPoss)  ++ rs.s ! ASg Masc!Nom!Animate  }; 

    ImpPl1 vp = {s= "давайте" ++ vp.s! (ClIndic Future Simul)! APl ! P2  }; 

    ImpersCl vp = {s= \\ b, clf =>  let ne= case b of {Pos =>[]; Neg =>"не"}
      in 
      ne ++ vp.s! clf! (ASg Neut) ! P3  }; 

-- No direct correspondance in Russian. Usually expressed by infinitive:
-- "Если очень захотеть, можно в космос улететь" 
-- (If one really wants one can fly into the space).
-- Note that the modal verb "can" is trasferred into adverb 
-- "можно" (it is possible) in Russian
-- The closest subject is "ты" (you), which is omitted in the final sentence:
-- "Если очень захочешь, можешь в космос улететь"

    GenericCl vp = {s= \\ b, clf =>  let ne= case b of {Pos =>[]; Neg =>""}
      in 
      ne ++ vp.s! clf! (ASg Masc) ! P3  }; 

    ProgrVP vp = vp ;

}

