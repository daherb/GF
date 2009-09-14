concrete VerbRon of Verb = 
  CatRon ** open Prelude, ResRon in {

  flags optimize=all_subs ;

  lin
    UseV = \verb -> 
    {
    s = verb.s ; 
    isRefl = verb.isRefl;
    nrClit = verb.nrClit;
    isFemSg = False ; pReflClit = verb.pReflClit ;
    neg    = table {Pos => ""; Neg => "nu"} ;
    clAcc  = RNoAg ;  nrClit = verb.nrClit; 
    clDat  = RNoAg ; 
    comp   = \\a => [] ;
    ext    = \\p => [] ; 
    } ;

    ComplVV v vp =insertSimpObj (\\a => "s�"  ++ (flattenSimpleClitics vp.nrClit vp.clAcc vp.clDat (vp.isRefl ! a)) ++ conjVP vp a ++vp.comp ! a ++ vp.ext ! Pos) (UseV v) ;


    ComplVS v s  = insertExtrapos (\\b => conjThat ++ s.s ! (v.m ! b)) (predV v) ;
    ComplVQ v q  = insertExtrapos (\\_ => q.s ! QIndir) (predV v) ;
 

    ComplVA v ap = 
    insertSimpObj (\\a => ap.s ! AF a.g a.n Indef ANomAcc) (UseV v) ;


    SlashV2a verb = {s = verb.s ; isRefl = verb.isRefl; nrClit = verb.nrClit;     
                     isFemSg = False ; pReflClit = verb.pReflClit ;
                     neg = table {Pos => ""; Neg => "nu"} ;
                     clAcc  = RNoAg ; 
                     clDat  = RNoAg ; 
                     comp   = \\a => [] ;
                     ext    = \\p => [] ;
                     c2 = verb.c2 ; needAgr = False ; needClit = True ; lock_VP = <>};
  



    Slash2V3 v np = let  s1 = v.c2.s ++(np.s ! (v.c2.c)).comp ;
                         ss = if_then_Str np.hasRef (v.c2.prepDir ++ s1) s1; 
                         sir = if_then_Str np.isPronoun "" ss ;
                         vcDa = if_then_else VClit np.hasRef (nextClit v.nrClit PDat) v.nrClit;
                         vcAc = if_then_else VClit np.hasRef (nextClit v.nrClit PAcc) v.nrClit   
                         in
                               case v.c2.isDir of
                                  {Dir PAcc => (insertObje (\\_ => sir) (clitFromNoun np Ac) RNoAg (isAgrFSg np.a) vcAc (UseV v)) ** {needAgr = False ; needClit = True ; c2 = v.c3} ;
                                   Dir PDat => (insertObje (\\_ => sir) RNoAg (clitFromNoun np Da) False vcDa (UseV v)) ** {needAgr = False ; needClit = True ; c2 = v.c3};
                                    _ => (insertSimpObjPre (\\_ => ss) (UseV v)) ** {needAgr = False ; needClit = True ; c2 = v.c3}
                                    };
    
    Slash3V3 v np = let s1 = v.c3.s ++ (np.s ! (v.c3.c)).comp ;
                        ss = if_then_Str np.hasRef (v.c3.prepDir ++ s1) s1 ;
                        sir = if_then_Str np.isPronoun "" ss ;
                        vcDa = if_then_else VClit np.hasRef (nextClit v.nrClit PDat) v.nrClit;
                        vcAc = if_then_else VClit np.hasRef (nextClit v.nrClit PAcc) v.nrClit  
                            in
                           case v.c3.isDir of
                            {Dir PAcc => (insertObje (\\_ => sir) (clitFromNoun np Ac) RNoAg (isAgrFSg np.a) vcAc (UseV v)) ** {needAgr = False ; needClit = True ; c2 = v.c2}  ;
                             Dir PDat => (insertObje (\\_ => sir) RNoAg (clitFromNoun np Da) False vcDa (UseV v)) ** {needAgr = False ; needClit = True ; c2 = v.c2}  ;
                            _ => (insertSimpObjPre (\\_ => ss) (UseV v)) ** {needAgr = False ; needClit = True ;c2 = v.c2}
                             };

-- needs fixing - agreement for the added verb must be made accordingly to what we add in ComplSlash !!! 
-- fixed with extra parameter !

    SlashV2V v vp =  (insertSimpObj (\\a =>  "s�" ++ (flattenSimpleClitics vp.nrClit vp.clAcc vp.clDat (vp.isRefl ! a)) ++ conjVP vp a ++ vp.comp ! a ++ vp.ext ! Pos) (UseV v)) ** {needAgr = True ; needClit = True ;c2 = v.c2} ; 


    SlashV2S v s = (insertExtrapos (\\b => conjThat ++ s.s ! Indic) (UseV v)) ** {needAgr = False; needClit = True ;c2 = v.c2}; 

    SlashV2Q v q = (insertExtrapos (\\_ => q.s ! QIndir) (UseV v)) ** {needAgr = False ; needClit = False ;c2 = v.c2 } ; 

   

 -- more usually the adverbial form is used, hence no agreement
 
   SlashV2A v ap =  
     (insertSimpObj  (\\a => v.c3.s ++ ap.s ! (AF Masc Sg Indef (convCase v.c3.c)))  
(UseV v)) ** {needAgr = False ; needClit = True ; c2 = v.c2} ;

    ComplSlash vp np =  let  s1 = vp.c2.s ++(np.s ! (vp.c2.c)).comp ;
                             ss = if_then_Str np.hasRef (vp.c2.prepDir ++ s1) s1 ; 
                             sir = if_then_Str np.isPronoun "" ss  ;
                             vcDa = if_then_else VClit np.hasRef (nextClit vp.nrClit PDat) vp.nrClit;
                             vcAc = if_then_else VClit np.hasRef (nextClit vp.nrClit PAcc) vp.nrClit;  
                             vpp =  case vp.c2.isDir of
                          {Dir PAcc => insertObje (\\_ => sir) (clitFromNoun np Ac) RNoAg (isAgrFSg np.a) vcAc vp  ;
                           Dir PDat => insertObje (\\_ => sir) RNoAg (clitFromNoun np Da) False vcDa vp;
                           _ => insertSimpObjPre (\\_ => ss) vp 
                             }
                            in 
                         {isRefl = vpp.isRefl; 
                          s = vpp.s ; isFemSg = vpp.isFemSg ; pReflClit = vp.pReflClit ;
                          nrClit = vpp.nrClit; clAcc = vpp.clAcc ; 
                          clDat = vpp.clDat ; neg   = vpp.neg ;
                          comp  = case vp.needAgr of 
                                     {True => \\a => vpp.comp ! (np.a);
                                      _    => \\a => vpp.comp ! a 
                                      };
                          ext   = vpp.ext ;
                          lock_VP = <> };

 


--add reflexive clitics 
    ReflVP v = {isRefl = case v.c2.c of
                           {Da => \\a => dRefl a;
                            _  => \\a => aRefl a
                            };
                s     = v.s ; isFemSg = v.isFemSg ;                 
                nrClit = case v.nrClit of 
                            {VNone => VRefl;
                             _     => VMany };
                clAcc = v.clAcc ; 
                pReflClit = case v.c2.c of
                                      {Ac => Short ;
                                       _  => Composite};
                clDat = v.clDat ; 
                neg   = v.neg ;
                comp  = v.comp ;
                ext   = v.ext ;
                lock_VP = <> 
                };
      

    SlashVV v vp = 
              insertObjc (\\a => "s�" ++ (flattenSimpleClitics vp.nrClit vp.clAcc vp.clDat (vp.isRefl ! a)) ++ conjVP vp a ++ vp.comp ! a ++ vp.ext ! Pos) ((UseV v) **{c2=vp.c2; needAgr= vp.needAgr ; needClit = False; lock_VPSlash = <>}) ;

    SlashV2VNP v np vp = let  s1 = v.c2.s ++(np.s ! (v.c2.c)).comp ;
                              ss = if_then_Str np.hasRef (v.c2.prepDir ++ s1) s1; 
                              sir = if_then_Str np.isPronoun "" ss ;
                              vcDa = if_then_else VClit np.hasRef (nextClit v.nrClit PDat) v.nrClit;
                              vcAc = if_then_else VClit np.hasRef (nextClit v.nrClit PAcc) v.nrClit ;  
                              vcomp = (getConjComp vp np.a).s
                           in   
                              case v.c2.isDir  of
                                {Dir PAcc => (insertObje (\\a => sir ++ vcomp ! a) (clitFromNoun np Ac) RNoAg (isAgrFSg np.a) vcAc (UseV v)) ** {needAgr = vp.needAgr ; needClit = False ;c2 = vp.c2} ;
                                
                                 Dir PDat =>  (insertObje (\\a => sir ++ vcomp ! a) RNoAg (clitFromNoun np Da) False vcDa (UseV v)) ** {needAgr = vp.needAgr ; needClit = False ; c2 = vp.c2};
                                 
                                 _        => (insertSimpObjPre (\\a => ss ++ vcomp ! a) (UseV v)) ** {needAgr = vp.needAgr ; needClit = False ; c2 = vp.c2}  
                                };


    UseComp comp = insertSimpObj comp.s (UseV copula) ;

    CompAP ap = {s = \\ag => ap.s ! AF ag.g ag.n Indef ANomAcc} ;
    CompNP np = {s = \\_  => (np.s ! No).comp} ;
    CompAdv a = {s = \\_  => a.s} ;


    AdvVP vp adv = insertAdv adv.s vp ;
    AdVVP adv vp = insertAdv adv.s vp ;

    PassV2 v = insertSimpObj (\\a => v.s ! PPasse a.g a.n Indef ANomAcc) (UseV auxPassive) ;



oper
insertAdv : Str -> VP -> VP = \co,vp -> { 
    s     = vp.s ;
    isRefl = vp.isRefl;
    isFemSg = vp.isFemSg ; pReflClit = vp.pReflClit ;
    clAcc = vp.clAcc ; nrClit = vp.nrClit ;
    clDat = vp.clDat ; 
    neg   = vp.neg ; 
    comp  = \\a => vp.comp ! a ++ co ;
    ext   = vp.ext ;
    lock_VP = <>
    } ;







oper auxPassive = copula ; 

mkVPSlash : Compl -> VP -> VP ** {c2 : Compl} = \c,vp -> vp ** {c2 = c; needAgr = False; needClit = True} ;


insertObjc : (Agr => Str) -> VPSlash -> VPSlash = \obj,vp -> 
    insertSimpObj obj vp ** {c2 = vp.c2; needAgr = False ; needClit = True ; lock_VPSlash = <>} ;



getConjComp : VP -> Agr -> {s: Agr => Str} = \vp,ag ->
 {s  = \\a => "s�" ++ (flattenSimpleClitics vp.nrClit vp.clAcc vp.clDat (vp.isRefl ! a)) ++ conjVP vp ag ++ vp.comp ! a ++ vp.ext ! Pos};

-- discuss example 
-- l -table (ComplSlash (Slash3V3 sell_V3 (UsePN john_PN)) (UsePN paris_PN))
-- in English the direct object always comes first, which could lead to incorrect longer examples
-- while in French it always comes last
-- ?!?
};
