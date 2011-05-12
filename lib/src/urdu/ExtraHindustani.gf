--concrete ExtraUrd of ExtraUrdAbs = CatUrd ** 
--  open ResUrd, Coordination, Prelude, MorphoUrd, ParadigmsUrd in {
incomplete concrete ExtraHindustani of ExtraHindustaniAbs = CatHindustani ** 
   open CommonHindustani,Coordination,ResHindustani, ParamX in {
  lin
--    GenNP np = {s = \\_,_,_ => np.s ! NPC Obl ++ "كا" ; a = np.a} ;
   GenNP np = {s = \\n,g,c => 
     case <n,g,c> of {
     <_,Masc,_> => np.s ! NPC Obl ++ "كا" ;
     <_,Fem,_> => np.s ! NPC Obl ++ "كی"
     };
     
   a = np.a} ;

    each_Det = mkDet  "ہر كوی" "ہر كوی" "ہر كوی" "ہر كوی" Sg ;
    have_V = mkV "راكھنا";
    IAdvAdv adv = {s = "كتنی" ++ adv.s} ;
    ICompAP ap = {s = "كتنے" ++ ap.s ! Sg ! Masc ! Dir ! Posit} ;
    cost_V = mkV "قیمت" ;
    
    -- added for causitives
    make_CV = mkVerb "نoتہiنگ"   ** {c2 = "" };

-- for VP conjunction
} 
