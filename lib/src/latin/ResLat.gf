--# -path=.:../abstract:../common:../prelude

--1 Latin auxiliary operations.

resource ResLat = ParamX ** open Prelude in {

param
  Case = Nom | Acc | Gen | Dat | Abl | Voc ;
  Gender = Masc | Fem | Neutr ;
--  Degree = DPos | DComp | DSup ;

oper
  Noun : Type = {s : Number => Case => Str ; g : Gender} ;
  Adjective : Type = {s : Degree => Gender => Number => Case => Str ; comp_adv : Str ; super_adv : Str } ;

-- To file as a bug :
--  consonant : pattern Str = stop | fricative;
--  test : Str -> Str =
--    \n ->
--    case n of {
--      #consonant + rest => "Got it";
--      full => "Nope"
--    };
-- Results in src/compiler/GF/Compile/Compute/ConcreteLazy.hs:(320,16)-(321,51): Non-exhaustive patterns in case

-- nouns
  mkNoun : (n1,_,_,_,_,_,_,_,_,n10 : Str) -> Gender -> Noun = 
    \sn,sa,sg,sd,sab,sv,pn,pa,pg,pd,g -> {
      s = table {
	Sg => table {
          Nom => sn ;
          Acc => sa ;
          Gen => sg ;
          Dat => sd ;
          Abl => sab ;
          Voc => sv
          } ;
	Pl => table {
          Nom | Voc => pn ;
          Acc => pa ;
          Gen => pg ;
          Dat | Abl => pd
          }
	} ;
      g = g
    } ;
  
-- to change the default gender

  nounWithGen : Gender -> Noun -> Noun = \g,n ->
    {s = n.s ; g = g} ;

-- also used for adjectives and so on

-- adjectives

  mkAdjective : (_,_,_ : Noun) -> 
    ( (Gender => Number => Case => Str) * Str ) -> 
    ( (Gender => Number => Case => Str) * Str ) -> Adjective = 
    \bonus,bona,bonum,melior,optimus ->
    {
      s = table {
	Posit => table {
	  Masc  => bonus.s ;
	  Fem   => bona.s ;
	  Neutr => bonum.s 
	  } ;
	Compar => melior.p1 ;
	Superl => optimus.p1 
	} ;
      comp_adv = melior.p2 ;
      super_adv = optimus.p2
    } ;


  noun3adj : Str -> Str -> Gender -> Noun = \audax,audacis,g ->
    let 
      audac   = Predef.tk 2 audacis ;
      audacem = case g of {Neutr => audax ; _ => audac + "em"} ;
      audaces = case g of {Neutr => audac +"ia" ; _ => audac + "es"} ;
      audaci  = audac + "i" ;
    in
    mkNoun
      audax audacem (audac + "is") audaci audaci audax
      audaces audaces (audac + "ium") (audac + "ibus") 
      g ;



-- verbs

param 
  VActForm  = VAct VAnter VTense Number Person ;
  VPassForm = VPass VTense Number Person ; -- No anteriority because perfect forms are built using participle
  VInfForm  = VInfActPres | VInfActPerf | VInfActFut Gender;
  VImpForm  = VImp1 Number | VImp2 Number Person ;
  VGerund   = VGenAcc | VGenGen |VGenDat | VGenAbl ;
  VSupine   = VSupAcc | VSupAbl ;

  VAnter = VSim | VAnt ;
  VTense = VPres VMood | VImpf VMood | VFut ; 
  VMood  = VInd | VConj ;

  oper
  Verb : Type = {
    act   : VActForm => Str ;
    pass  : VPassForm => Str ;
    inf   : VInfForm => Str ;
    imp   : VImpForm => Str ;
    ger   : VGerund => Str ;
    geriv : Gender => Number => Case => Str ; 
    sup   : VSupine => Str ;
    partActPres  : Number => Case => Str ;
    partActFut   : Gender => Number => Case => Str ;
    partPassPerf : Gender => Number => Case => Str ;
    } ;

  mkVerb : 
    (cela,cela,cele,celab,celo,celant,celare,celavi,celatus,celabo,celabunt,celabi,celaris,celantur,cela : Str) 
      -> Verb = 
    \pres_ind_stem,pres_ind,pres_conj_stem,impf_ind_stem,pres_ind_sg_p1,pres_ind_pl_p3,inf_pres_act,perf_ind_sg_p1,inf_perf_pass,fut_I_sg_p1,fut_I_pl_p3,fut_I_stem,impf_conj_pass_stem,pres_ind_pass_pl_p3,imp_I_sg -> 
    let
      perf_stem = init perf_ind_sg_p1 ;
      tustatum = table {
      	Masc =>  table Number [ "tus" ; "ti" ] ;
      	Fem =>   table Number [ "ta" ; "tae" ] ;
      	Neutr => table Number [ "tum" ; "ta" ] 
      	} ;
      part_stem : Str = Predef.tk 3 inf_perf_pass
    in 
    {
      act = table {
        VAct VSim (VPres VInd)  Sg P1 => pres_ind_sg_p1 ; -- Present Indicative
        VAct VSim (VPres VInd)  Pl P3 => pres_ind_pl_p3 ; -- Present Indicative
        VAct VSim (VPres VInd)  n  p  => pres_ind + actPresEnding n p ; -- Present Indicative
        VAct VSim (VPres VConj) n  p  => pres_conj_stem + actPresEnding n p ; -- Present Conjunctive
        VAct VSim (VImpf VInd)  n  p  => impf_ind_stem + "ba" + actPresEnding n p ; -- Imperfect Indicative
        VAct VSim (VImpf VConj) n  p  => inf_pres_act + actPresEnding n p ; -- Imperfect Conjunctive
        VAct VSim VFut          Sg P1 => fut_I_sg_p1 ; -- Future I 
	VAct VSim VFut          Pl P3 => fut_I_pl_p3 ; -- Future I
        VAct VSim VFut          n  p  => fut_I_stem + actPresEnding n p ; -- Future I
        VAct VAnt (VPres VInd)  n  p  => perf_stem + actPerfEnding n p ; -- Prefect Indicative
        VAct VAnt (VPres VConj) n  p  => perf_stem + "eri" + actPresEnding n p ; -- Prefect Conjunctive
        VAct VAnt (VImpf VInd)  n  p  => perf_stem + "era" + actPresEnding n p ; -- Plusperfect Indicative
        VAct VAnt (VImpf VConj) n  p  => perf_stem + "isse" + actPresEnding n p ; -- Plusperfect Conjunctive
        VAct VAnt VFut          Sg P1 => perf_stem + "ero" ; -- Future II 
        VAct VAnt VFut          n  p  => perf_stem + "eri" + actPresEnding n p -- Future II
        } ;
      pass = table {
	VPass (VPres VInd)  Sg P1 => pres_ind_sg_p1 + passPresEnding Sg P1 ;
	VPass (VPres VInd)  Sg P2 => impf_conj_pass_stem + passPresEnding Sg P2 ;
	VPass (VPres VInd)  Pl P3 => pres_ind_pass_pl_p3 ;
	VPass (VPres VInd)  n  p  => pres_ind + passPresEnding n p ;
	VPass (VPres VConj) n  p  => pres_conj_stem + passPresEnding n p ;
	VPass (VImpf VInd)  n  p  => impf_ind_stem + "ba" + passPresEnding n p ;
	VPass (VImpf VConj) n  p  => impf_conj_pass_stem + "re" + passPresEnding n p ;
	VPass VFut          n  p  => pres_ind_stem + passFutEnding pres_ind n p 
	} ;
      inf = table {
        VInfActPres      => inf_pres_act ;
        VInfActPerf      => perf_stem + "isse" ;
	VInfActFut Masc  => part_stem + "turum" ;
	  
	VInfActFut Fem   => part_stem + "turam" ; 
	VInfActFut Neutr => part_stem + "turum"
        } ;
      imp = table {
	VImp1 Sg => imp_I_sg ;
	VImp1 Pl => pres_ind + "te" ;
	VImp2 Sg ( P2 | P3 ) => pres_ind + "to" ;
	VImp2 Pl P2 => pres_ind + "tote" ;
	VImp2 Pl P3 => pres_ind_pl_p3 + "o" ;
	_ => "######" -- No imperative form
	} ;
      ger = table {
	VGenAcc => impf_ind_stem + "ndum" ;
	VGenGen => impf_ind_stem + "ndi" ;
	VGenDat => impf_ind_stem + "ndo" ;
	VGenAbl => impf_ind_stem + "ndo" 
	} ;
--      geriv = ( adj ( cela + "ndus" ) ).s!Posit ;
      geriv = ( mkAdjective
		  ( mkNoun ( impf_ind_stem + "ndus" ) ( impf_ind_stem + "ndum" ) ( impf_ind_stem + "ndi" ) 
		      ( impf_ind_stem + "ndo" ) ( impf_ind_stem + "ndo" ) ( impf_ind_stem + "nde" ) 
		      ( impf_ind_stem + "ndi" ) ( impf_ind_stem + "ndos" ) ( impf_ind_stem + "ndorum" ) 
		      ( impf_ind_stem + "ndis" ) 
		       Masc )
		  ( mkNoun ( impf_ind_stem + "nda" ) ( impf_ind_stem + "ndam" ) ( impf_ind_stem + "ndae" ) 
		      ( impf_ind_stem + "ndae" ) ( impf_ind_stem + "nda" ) ( impf_ind_stem + "nda" ) 
		      ( impf_ind_stem + "ndae" ) ( impf_ind_stem + "ndas" ) (impf_ind_stem +"ndarum" ) 
		      ( impf_ind_stem + "ndis" ) 
		      Fem )
		  ( mkNoun ( impf_ind_stem + "ndum" ) ( impf_ind_stem + "ndum" ) ( impf_ind_stem + "ndi" ) 
		      ( impf_ind_stem + "ndo" ) ( impf_ind_stem + "ndo" ) ( impf_ind_stem + "ndum" ) 
		      ( impf_ind_stem + "nda" ) ( impf_ind_stem + "nda" ) ( impf_ind_stem + "ndorum" ) 
		      ( impf_ind_stem + "ndis" ) 
		      Neutr )
		  < \\_,_,_ => "" , "" >
		  < \\_,_,_ => "" , "" >
	).s!Posit ;
      sup = table {
	VSupAcc => part_stem + "tum" ;
	VSupAbl => part_stem + "tu" 
	} ;
--      partActPres = ( adj123 ( cela + "ns" ) ( cela + "ntis" ) ).s!Posit ;
      partActPres = ( mkNoun ( impf_ind_stem + "ns" ) ( impf_ind_stem + "ntem" ) ( impf_ind_stem + "ntis" ) 
			( impf_ind_stem + "nti" ) ( impf_ind_stem + "nte" ) ( impf_ind_stem + "ns" ) 
			( impf_ind_stem + "ntes" ) ( impf_ind_stem + "ntes" ) ( impf_ind_stem + "ntium" ) 
			( impf_ind_stem + "ntibus" ) 
 			Masc ).s ;
      partActFut = ( mkAdjective
		       ( mkNoun ( part_stem + "turus" ) ( part_stem + "turum" ) ( part_stem + "turi" ) 
			   ( part_stem + "turo" ) ( part_stem + "turo" ) ( part_stem + "ture" ) ( part_stem + "turi" ) 
			   ( part_stem + "turos" ) ( part_stem + "turorum" ) ( part_stem + "turis" ) 
			   Masc )
		       ( mkNoun ( part_stem + "tura" ) ( part_stem + "turam" ) ( part_stem + "turae" ) 
			   ( part_stem + "turae" ) ( part_stem + "tura" ) ( part_stem + "tura" )( part_stem + "turae" ) 
			   ( part_stem + "turas" ) ( part_stem +"turarum" ) ( part_stem + "turis" ) 
			   Fem )
		       ( mkNoun ( part_stem + "turum" ) ( part_stem + "turum" ) ( part_stem + "turi" ) 
			   ( part_stem + "turo" ) ( part_stem + "turo" ) ( part_stem + "turum" ) ( part_stem + "tura" ) 
			   ( part_stem + "tura" ) ( part_stem + "turorum" ) ( part_stem + "turis" ) 
			   Neutr )
		       < \\_,_,_ => "" , "" >
		       < \\_,_,_ => "" , "" >
	).s!Posit ;
--      partPassPerf = ( adj ( cela + "tus" ) ).s!Posit
      partPassPerf = ( mkAdjective
			 ( mkNoun ( part_stem + "tus" ) ( part_stem + "tum" ) ( part_stem + "ti" ) ( part_stem + "to" ) 
			     ( part_stem + "to" ) ( part_stem + "te" ) ( part_stem + "ti" ) ( part_stem + "tos" ) 
			     ( part_stem + "torum" ) ( part_stem + "tis" ) 
			     Masc )
			 ( mkNoun ( part_stem + "ta" ) ( part_stem + "tam" ) ( part_stem + "tae" ) ( part_stem + "tae" ) 
			     ( part_stem + "ta" ) ( part_stem + "ta" ) ( part_stem + "tae" ) ( part_stem + "tas" ) 
			     ( part_stem + "tarum" ) ( part_stem + "tis" ) 
			     Fem )
			 ( mkNoun ( part_stem + "tum" ) ( part_stem + "tum" ) ( part_stem + "ti" ) ( part_stem + "to" ) 
			     ( part_stem + "to" ) ( part_stem + "tum" ) ( part_stem + "ta" ) ( part_stem + "ta" ) 
			     ( part_stem + "torum" ) ( part_stem + "tis" ) 
			     Neutr ) 
			 < \\_,_,_ => "" , "" >
			 < \\_,_,_ => "" , "" >
	).s!Posit ;
    } ;

  actPresEnding : Number -> Person -> Str = 
    useEndingTable <"m", "s", "t", "mus", "tis", "nt"> ;

  actPerfEnding : Number -> Person -> Str = 
    useEndingTable <"i", "isti", "it", "imus", "istis", "erunt"> ;

  passPresEnding : Number -> Person -> Str =
    useEndingTable <"r", "ris", "tur", "mur", "mini", "ntur"> ;

  passFutEnding : Str -> Number -> Person -> Str = 
    \lauda,n,p ->
    let endings : Str * Str * Str * Str * Str * Str = case lauda of {
	  ( _ + "a" ) | 
	    ( _ + "e" ) => < "bo" , "be" , "bi" , "bi" , "bi" , "bu" > ;
	  _             => < "a"  , "e"  , "e"  , "e"  , "e"  , "e"  >
	  }
    in
    (useEndingTable endings n p) + passPresEnding n p ;
    
  useEndingTable : (Str*Str*Str*Str*Str*Str) -> Number -> Person -> Str = 
    \es,n,p -> case n of {
      Sg => case p of {
        P1 => es.p1 ;
        P2 => es.p2 ;
        P3 => es.p3
        } ;
      Pl => case p of {
        P1 => es.p4 ;
        P2 => es.p5 ;
        P3 => es.p6
        }
      } ;

  be_Aux : Verb = 
    {
      act = table VActForm {
	VAct VSim (VPres VInd)  n  p  => table Number [ table Person [ "sum" ; "es" ; "est" ] ;
							table Person [ "sumus" ; "estis" ; "sunt" ]
	  ]! n ! p ;
       	VAct VSim (VPres VConj) n  p  => "si" + actPresEnding n p ;
       	VAct VSim (VImpf VInd)  n  p  => "era" + actPresEnding n p ;
       	VAct VSim (VImpf VConj) n  p  => "esse" + actPresEnding n p ;
       	VAct VSim VFut          Sg P1 => "ero" ;
       	VAct VSim VFut          Pl P3 => "erunt" ;
       	VAct VSim VFut          n  p  => "eri" + actPresEnding n p ;
      	VAct VAnt (VPres VInd)  Pl P3 => "fu" + actPerfEnding Pl P3 ;
       	VAct VAnt (VPres VInd)  n  p  => "fui" + actPerfEnding n p ;
       	VAct VAnt (VPres VConj) n  p  => "fueri" + actPresEnding n p ;
       	VAct VAnt (VImpf VInd)  n  p  => "fuera" + actPresEnding n p ;
       	VAct VAnt (VImpf VConj) n  p  => "fuisse" + actPresEnding n p ;
       	VAct VAnt VFut          Sg P1 => "fuero" ;
       	VAct VAnt VFut          n  p  => "fueri" + actPresEnding n p 
       	} ;
      pass = \\_ => "######" ; -- No passive form
      inf = table {
        VInfActPres      => "esse" ;
        VInfActPerf      => "fuisse" ;
       	VInfActFut Masc  => "futurum" ;
	VInfActFut Fem   => "futuram" ;
	VInfActFut Neutr => "futurum"
        } ;
      imp = table {
	VImp1 Sg => "es" ;
	VImp1 Pl => "este" ;
	VImp2 Sg ( P2 | P3 ) => "esto" ;
	VImp2 Pl P2 => "estote" ;
	VImp2 Pl P3 => "sunto" ;
	_ => "######" -- No such imperative form of esse
	} ;
      ger = table {
	_ => "######" -- No gerund form of esse
	} ;
      geriv = \\_,_,_ => "######" ; -- No gerundive form of esse
      sup = table {
	_ => "######" -- No supin form of esse
	} ;
--      partActPres = ( adj123 "ens" "entis" ).s!Posit ; -- only medieval latin cp. http://en.wiktionary.org/wiki/ens#Latin
      partActPres = ( mkNoun "ens" "entem" "entis" "enti" "ente" "ens" 
			"entes" "entes" "entium" "entibus" 
			Masc ).s ;
      partActFut = \\_,_,_ => "######" ; -- No future active participle of esse
      partPassPerf = \\_,_,_ => "######" -- No prefect passive participle of esse

    };

  want_V : Verb = 
    {
      act = table {
  	VAct VSim (VPres VInd)  n  p  => table Number [ table Person [ "volo" ; "vis" ; "vult" ] ;
  							table Person [ "volumus" ; "vultis" ; "volunt" ]
  	  ]! n ! p ;
  	VAct VSim (VPres VConj) n  p  => "veli" + actPresEnding n p ;
       	VAct VSim (VImpf VInd)  n  p  => "voleba" + actPresEnding n p ;
       	VAct VSim (VImpf VConj) n  p  => "velle" + actPresEnding n p ;
       	VAct VSim VFut          Sg P1 => "volam" ;
       	VAct VSim VFut          n  p  => "vole" + actPresEnding n p ;
       	VAct VAnt (VPres VInd)  n  p  => "volu" + actPerfEnding n p ;
       	VAct VAnt (VPres VConj) n  p  => "volueri" + actPresEnding n p ;
       	VAct VAnt (VImpf VInd)  n  p  => "voluera" + actPresEnding n p ;
       	VAct VAnt (VImpf VConj) n  p  => "voluisse" + actPresEnding n p ;
       	VAct VAnt VFut          Sg P1 => "voluero" ;
       	VAct VAnt VFut          n  p  => "volueri" + actPresEnding n p 
       	} ;
      ger = \\_ => "######" ; -- no gerund form for velle
      geriv = \\_,_,_ => "######" ; -- no gerundive form for velle
      imp = \\_ =>  "######" ; -- no imperative form for velle
      inf = table {
  	VInfActPres => "velle" ;
  	VInfActPerf => "voluisse" ;
  	_           => "######" -- No infinitive future
  	} ;
      partActFut = \\_,_,_ => "######" ; -- no participle future active
      partActPres = ( mkNoun "volens" "volentem" "volentis" "volenti" "volente" "volens"
  			"volentes" "volentes" "volentium" "volentibus" 
  			Masc ).s ;
      partPassPerf = \\_,_,_ => "######" ; -- no participle perfect passive
      pass = \\_ => "######" ; -- no passive forms
      sup = \\_ => "######" -- no supin forms
    } ;

-- pronouns

  Pronoun : Type = {
    s : Case => Str ;
    g : Gender ;
    n : Number ;
    p : Person ;
    } ;

  mkPronoun : (_,_,_,_,_ : Str) -> Gender -> Number -> Person -> Pronoun = 
    \ego,me,mei,mihi,mee,g,n,p -> {
      s = pronForms ego me mei mihi mee ;
      g = g ;
      n = n ;
      p = p
      } ;

  pronForms : (_,_,_,_,_ : Str) -> Case => Str = 
    \ego,me,mei,mihi,mee -> table Case [ego ; me ; mei ; mihi ; mee ; ego] ;

  personalPronoun : Gender -> Number -> Person -> Pronoun = \g,n,p -> {
    s = case <g,n,p> of {
      <_,Sg,P1> => pronForms "ego" "me" "mei" "mihi" "me" ;
      <_,Sg,P2> => pronForms "tu"  "te" "tui" "tibi" "te" ;
      <_,Pl,P1> => pronForms "nos" "nos" "nostri" "nobis" "nobis" ; --- nostrum
      <_,Pl,P2> => pronForms "vos" "vos" "vestri" "vobis" "vobis" ; --- vestrum
      <Masc, Sg,P3> => pronForms "is" "eum" "eius" "ei" "eo" ;
      <Fem,  Sg,P3> => pronForms "ea" "eam" "eius" "ei" "ea" ;
      <Neutr,Sg,P3> => pronForms "id" "id"  "eius" "ei" "eo" ;
      <Masc, Pl,P3> => pronForms "ii" "eos" "eorum" "iis" "iis" ;
      <Fem,  Pl,P3> => pronForms "ii" "eas" "earum" "iis" "iis" ;
      <Neutr,Pl,P3> => pronForms "ea" "ea"  "eorum" "iis" "iis"
      } ;
    g = g ;
    n = n ;
    p = p
    } ;

-- prepositions

  Preposition : Type = {s : Str ; c : Case} ;

-- Bayer-Lindauer $149ff.
  about_P = lin Prep (mkPrep "de" Gen ) ; -- L...
  at_P = lin Prep (mkPrep "ad" Acc ) ; -- L...
  for_P = lin Prep (mkPrep "pro" Abl ) ; -- L...
  from_P = lin Prep ( mkPrep "ab" Abl ) ; -- L...
  in_P = lin Prep ( mkPrep "in" ( variants { Abl ; Acc } ) ) ; -- L...
  on_P = lin Prep ( mkPrep "ad" Gen ) ; -- L...
  to_P = lin Prep ( mkPrep "ad" Acc ) ; -- L...
  Gen_Prep = lin Prep ( mkPrep "" Gen ) ;
  Acc_Prep = lin Prep ( mkPrep "" Acc ) ;
  Dat_Prep = lin Prep ( mkPrep "" Dat ) ;

  VP : Type = {
    fin : VActForm => Str ;
    inf : VInfForm => Str ;
    obj : Str ;
    adj : Gender => Number => Str
  } ;

  VPSlash = VP ** {c2 : Preposition} ;

  predV : Verb -> VP = \v -> {
    fin = v.act ;
    inf = v.inf ;
    obj = [] ;
    adj = \\_,_ => []
  } ;

  predV2 : (Verb ** {c : Preposition}) -> VPSlash = \v -> predV v ** {c2 = v.c} ;

  appPrep : Preposition -> (Case => Str) -> Str = \c,s -> c.s ++ s ! c.c ;

  insertObj : Str -> VP -> VP = \obj,vp -> {
    fin = vp.fin ;
    inf = vp.inf ;
    obj = obj ++ vp.obj ;
    adj = vp.adj
  } ;

  insertAdj : (Gender => Number => Case => Str) -> VP -> VP = \adj,vp -> {
    fin = vp.fin ;
    inf = vp.inf ;
    obj = vp.obj ;
    adj = \\g,n => adj ! g ! n ! Nom ++ vp.adj ! g ! n
  } ;

  Clause = {s : VAnter => VTense => Polarity => Str} ;

  mkClause : Pronoun -> VP -> Clause = \np,vp -> {
    s = \\a,t,p => np.s ! Nom ++ vp.obj ++ vp.adj ! np.g ! np.n ++ negation p ++ 
        vp.fin ! VAct a t np.n np.p
  } ;
    
  negation : Polarity -> Str = \p -> case p of {
    Pos => [] ;   
    Neg => "non"
  } ;

-- determiners

  Determiner : Type = {
    s,sp : Gender => Case => Str ;
    n : Number
    } ;

  Quantifier : Type = {
    s,sp : Number => Gender => Case => Str ;
    } ;

  mkQuantifG : (_,_,_,_,_ : Str) -> (_,_,_,_ : Str) -> (_,_,_ : Str) -> 
    Gender => Case => Str = 
    \mn,ma,mg,md,mab, fno,fa,fg,fab, nn,ng,nab -> table {
      Masc  => pronForms mn  ma mg md mab ;
      Fem   => pronForms fno fa fg md fab ;
      Neutr => pronForms nn  nn ng md nab     
    } ;
      
  mkQuantifier : (sg,pl : Gender => Case => Str) -> Quantifier = \sg,pl ->
    let ssp = table {Sg => sg ; Pl => pl}
    in {
      s  = ssp ;
      sp = ssp 
      } ;

  hic_Quantifier = mkQuantifier
    (mkQuantifG 
       "hic" "hunc" "huius" "huic" "hoc"  "haec" "hanc" "huius" "hac"  "hoc" "huius" "hoc")
    (mkQuantifG 
       "hi" "hos" "horum" "his" "his"  "hae" "has" "harum" "his"  "haec" "horum" "his")
    ;

  ille_Quantifier = mkQuantifier
    (mkQuantifG 
       "ille" "illum" "illius" "illi" "illo"  
       "illa" "illam" "illius" "illa"  
       "illud" "illius" "illo")
    (mkQuantifG 
       "illi" "illos" "illorum" "illis" "illis"  
       "illae" "illas" "illarum" "illis"  
       "illa" "illorum" "illis")
    ;

  mkPrep : Str -> Case -> Preposition  = \s,c -> lin Preposition {s = s ; c = c} ;

  mkAdv : Str -> { s: Str } = \adv -> { s = adv } ;

param
  Unit = one | ten | hundred | thousand | ten_thousand | hundred_thousand ;

}

