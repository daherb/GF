--# -path=.:../abstract:../common:../prelude

--1 Latin auxiliary operations.

resource ResLat = ParamX ** open Prelude in {

param
  Case = Nom | Acc | Gen | Dat | Abl | Voc ;
  Gender = Masc | Fem | Neutr ;
--  Degree = DPos | DComp | DSup ;

oper
  consonant : pattern Str = #( "p" | "b" | "f" | "v" | "m" | "t" | "d" | "s" | "z" | "n" | "r" | "c" | "g" | "l" | "q" | "qu" | "h" );

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
  VInfForm  = VInfActPres | VInfActPerf Gender | VInfActFut Gender;
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
    (regere,reg,regi,rega,regeba,regere,rege,regi,rex,rex,rexeri,rexera,rexisse,rexeri,rect : Str) 
    -> Verb = 
    \inf_act_pres,pres_stem,pres_ind_base,pres_conj_base,impf_ind_base,impf_conj_base,fut_I_base,imp_base,
    perf_stem,perf_ind_base,perf_conj_base,pqperf_ind_base,pqperf_conj_base,fut_II_base,part_stem -> 
    let
      fill : Str * Str * Str = case pres_stem of {
	_ + ( "a" | "e" ) => < "" , "" , "" > ;
	_ + #consonant => < "e" , "u" , "i" > ;
	_ => < "e" , "u" , "" >
	} ;
    in 
    {
      act = 
	table {
          VAct VSim (VPres VInd)  Sg P1 => -- Present Indicative
	    ( case pres_ind_base of {
		_ + "a" =>  ( init pres_ind_base ) ;
		_ => pres_ind_base
		}
	    ) + actPresEnding Sg P1 ;
	  VAct VSim (VPres VInd)  Pl P3 => -- Present Indicative
	    pres_ind_base + fill.p2 + actPresEnding Pl P3 ;
          VAct VSim (VPres VInd)  n  p  =>  -- Present Indicative
	    pres_ind_base + fill.p3 + actPresEnding n p ;
          VAct VSim (VPres VConj) n  p  => -- Present Conjunctive
	    pres_conj_base + actPresEnding n p ; 
          VAct VSim (VImpf VInd)  n  p  => -- Imperfect Indicative
	    impf_ind_base + actPresEnding n p ; 
          VAct VSim (VImpf VConj) n  p  => -- Imperfect Conjunctive
	    impf_conj_base + actPresEnding n p ; 
          VAct VSim VFut          Sg P1 => -- Future I
	    case fut_I_base of {
	      _ + "bi" => ( init fut_I_base ) + "o" ;
	      _  => ( init fut_I_base ) + "a" + actPresEnding Sg P1 
	    } ;
	  VAct VSim VFut          Pl P3 => -- Future I
	    ( case fut_I_base of {
		_ + "bi" => ( init fut_I_base ) + "u";
		_ => fut_I_base
		} 
	    ) + actPresEnding Pl P3 ;
          VAct VSim VFut          n  p  => -- Future I
	    fut_I_base + actPresEnding n p ; 
          VAct VAnt (VPres VInd)  n  p  => -- Prefect Indicative
	    perf_ind_base + actPerfEnding n p ; 
          VAct VAnt (VPres VConj) n  p  => -- Prefect Conjunctive
	    perf_conj_base + actPresEnding n p ; 
          VAct VAnt (VImpf VInd)  n  p  => -- Plusperfect Indicative
	    pqperf_ind_base + actPresEnding n p ; 
          VAct VAnt (VImpf VConj) n  p  => -- Plusperfect Conjunctive
	    pqperf_conj_base + actPresEnding n p ; 
          VAct VAnt VFut          Sg P1 => -- Future II 
	    ( init fut_II_base ) + "o" ; 
          VAct VAnt VFut          n  p  => -- Future II 
	    fut_II_base + actPresEnding n p 
        } ;
      pass = 
	table {
	  VPass (VPres VInd)  Sg P1 => -- Present Indicative
	    ( case pres_ind_base of
		{
		  _ + "a" => (init pres_ind_base ) ;
		  _ => pres_ind_base
		}
	    )  + "o" + passPresEnding Sg P1 ;
	  VPass (VPres VInd)  Sg P2 => -- Present Indicative
	    ( case imp_base of {
		_ + #consonant => 
		  ( case pres_ind_base of {
		      _ + "i" => ( init pres_ind_base ) ;
		      _ => pres_ind_base 
		      }
		  ) + "e" ;
		_ => pres_ind_base 
		}
	    ) + passPresEnding Sg P2 ;
	  VPass (VPres VInd)  Pl P3 => -- Present Indicative
	    pres_ind_base + fill.p2 + passPresEnding Pl P3 ;
	  VPass (VPres VInd)  n  p  => -- Present Indicative
	    pres_ind_base + fill.p3 + passPresEnding n p ;
	  VPass (VPres VConj) n  p  => -- Present Conjunctive
	    pres_conj_base + passPresEnding n p ;
	  VPass (VImpf VInd)  n  p  => -- Imperfect Indicative
	    impf_ind_base + passPresEnding n p ;
	  VPass (VImpf VConj) n  p  => -- Imperfect Conjunctive
	    impf_conj_base + passPresEnding n p ;
	  VPass VFut          Sg P1 => -- Future I
	    ( case fut_I_base of {
		_ + "bi" => ( init fut_I_base ) + "o" ;
		_ => ( init fut_I_base ) + "a"
		}
	    ) + passPresEnding Sg P1 ;
	  VPass VFut          Sg P2 => -- Future I
	    ( init fut_I_base ) + "e" + passPresEnding Sg P2 ;
	  VPass VFut          Pl P3 => -- Future I
	    ( case fut_I_base of {
		_ + "bi" => ( init fut_I_base ) + "u" ;
		_ => fut_I_base
		}
	    ) + passPresEnding Pl P3 ;
	  VPass VFut          n  p  => -- Future I
	    fut_I_base + passPresEnding n p
	} ;
      inf = 
	table {
          VInfActPres      => -- Infinitive Active Present
	    inf_act_pres ;
          VInfActPerf _    => -- Infinitive Active Perfect
	    perf_stem + "isse" ;
	  VInfActFut Masc  => -- Infinitive Active Future
	    part_stem + "urum" ;
	  VInfActFut Fem   => -- Infinitive Active Future
	    part_stem + "uram" ; 
	  VInfActFut Neutr => -- Infinitive Active Future
	    part_stem + "urum"
        } ;
      imp = 
	let 
	  imp_fill : Str * Str =
	    case imp_base of {
	      _ + #consonant => < "e" , "i" > ;
	      _ => < "" , "" >
	    };
	  in
	table {
	  VImp1 Sg           => -- Imperative I
	    imp_base + imp_fill.p1 ;
	  VImp1 Pl           => -- Imperative I
	    imp_base + imp_fill.p2 + "te" ;
	VImp2 Sg ( P2 | P3 ) => -- Imperative II
	  imp_base + imp_fill.p2 + "to" ;
	VImp2 Pl P2          => -- Imperative II
	  imp_base +
	  ( case imp_base of {
	      _ + #consonant => "i" ;
	      _ => fill.p3
	      }
	  ) + "tote" ;
	VImp2 Pl P3          => -- Imperative II 
	  pres_stem + fill.p2 + "nto" ;
	_ => "######" -- No imperative form
	} ;
      ger = 
	table {
	  VGenAcc => -- Gerund
	    pres_stem + fill.p1 + "ndum" ;
	  VGenGen => -- Gerund
	    pres_stem + fill.p1 + "ndi" ;
	  VGenDat => -- Gerund
	    pres_stem + fill.p1 + "ndo" ;
	  VGenAbl => -- Gerund
	    pres_stem + fill.p1 + "ndo" 
	} ;
      geriv = 
	( mkAdjective
	    ( mkNoun ( pres_stem + fill.p1 + "ndus" ) ( pres_stem + fill.p1 + "ndum" ) ( pres_stem + fill.p1 + "ndi" ) 
		( pres_stem + fill.p1 + "ndo" ) ( pres_stem + fill.p1 + "ndo" ) ( pres_stem + fill.p1 + "nde" ) 
		( pres_stem + fill.p1 + "ndi" ) ( pres_stem + fill.p1 + "ndos" ) ( pres_stem + fill.p1 + "ndorum" ) 
		( pres_stem + fill.p1 + "ndis" ) 
		Masc )
	    ( mkNoun ( pres_stem + fill.p1 + "nda" ) ( pres_stem + fill.p1 + "ndam" ) ( pres_stem + fill.p1 + "ndae" ) 
		( pres_stem + fill.p1 + "ndae" ) ( pres_stem + fill.p1 + "nda" ) ( pres_stem + fill.p1 + "nda" ) 
		( pres_stem + fill.p1 + "ndae" ) ( pres_stem + fill.p1 + "ndas" ) (pres_stem + fill.p1 +"ndarum" ) 
		( pres_stem + fill.p1 + "ndis" ) 
		Fem )
	    ( mkNoun ( pres_stem + fill.p1 + "ndum" ) ( pres_stem + fill.p1 + "ndum" ) ( pres_stem + fill.p1 + "ndi" ) 
		( pres_stem + fill.p1 + "ndo" ) ( pres_stem + fill.p1 + "ndo" ) ( pres_stem + fill.p1 + "ndum" ) 
		( pres_stem + fill.p1 + "nda" ) ( pres_stem + fill.p1 + "nda" ) ( pres_stem + fill.p1 + "ndorum" ) 
		( pres_stem + fill.p1 + "ndis" ) 
		Neutr )
	    < \\_,_,_ => "" , "" >
	    < \\_,_,_ => "" , "" >
	).s!Posit ;
      sup = 
	table {
	  VSupAcc => -- Supin
	    part_stem + "um" ;
	  VSupAbl => -- Supin
	    part_stem + "u" 
	} ;
      partActPres =
	( mkNoun ( pres_stem + fill.p1 + "ns" ) ( pres_stem + fill.p1 + "ntem" ) ( pres_stem + fill.p1 + "ntis" ) 
	    ( pres_stem + fill.p1 + "nti" ) ( pres_stem + fill.p1 + "nte" ) ( pres_stem + fill.p1 + "ns" ) 
	    ( pres_stem + fill.p1 + "ntes" ) ( pres_stem + fill.p1 + "ntes" ) ( pres_stem + fill.p1 + "ntium" ) 
	    ( pres_stem + fill.p1 + "ntibus" ) 
 	    Masc ).s ;
      partActFut = 
	( mkAdjective
	    ( mkNoun ( part_stem + "urus" ) ( part_stem + "urum" ) ( part_stem + "uri" ) 
		( part_stem + "uro" ) ( part_stem + "uro" ) ( part_stem + "ure" ) ( part_stem + "uri" ) 
		( part_stem + "uros" ) ( part_stem + "urorum" ) ( part_stem + "uris" ) 
		Masc )
	    ( mkNoun ( part_stem + "ura" ) ( part_stem + "uram" ) ( part_stem + "urae" ) 
		( part_stem + "urae" ) ( part_stem + "ura" ) ( part_stem + "ura" )( part_stem + "urae" ) 
		( part_stem + "uras" ) ( part_stem +"urarum" ) ( part_stem + "uris" ) 
		Fem )
	    ( mkNoun ( part_stem + "urum" ) ( part_stem + "urum" ) ( part_stem + "uri" ) 
		( part_stem + "uro" ) ( part_stem + "uro" ) ( part_stem + "urum" ) ( part_stem + "ura" ) 
		( part_stem + "ura" ) ( part_stem + "urorum" ) ( part_stem + "uris" ) 
		Neutr )
	    < \\_,_,_ => "" , "" >
	    < \\_,_,_ => "" , "" >
	).s!Posit ;
      partPassPerf = 
	( mkAdjective
	    ( mkNoun ( part_stem + "us" ) ( part_stem + "um" ) ( part_stem + "i" ) ( part_stem + "o" ) 
		( part_stem + "o" ) ( part_stem + "e" ) ( part_stem + "i" ) ( part_stem + "os" ) 
		( part_stem + "orum" ) ( part_stem + "is" ) 
		Masc )
	    ( mkNoun ( part_stem + "a" ) ( part_stem + "am" ) ( part_stem + "ae" ) ( part_stem + "ae" ) 
		( part_stem + "a" ) ( part_stem + "a" ) ( part_stem + "ae" ) ( part_stem + "as" ) 
		( part_stem + "arum" ) ( part_stem + "is" ) 
		Fem )
	    ( mkNoun ( part_stem + "um" ) ( part_stem + "um" ) ( part_stem + "i" ) ( part_stem + "o" ) 
		( part_stem + "o" ) ( part_stem + "um" ) ( part_stem + "a" ) ( part_stem + "a" ) 
		( part_stem + "orum" ) ( part_stem + "is" ) 
		Neutr ) 
	    < \\_,_,_ => "" , "" >
	    < \\_,_,_ => "" , "" >
	).s!Posit ;
    } ;
 

  mkDeponent : ( sequi,sequ,sequi,sequa,sequeba,sequere,seque,sequi,secut : Str ) -> Verb =
    \inf_pres,pres_stem,pres_ind_base,pres_conj_base,impf_ind_base,impf_conj_base,fut_I_base,imp_base,part_stem -> 
    let fill : Str * Str =
	  case pres_ind_base of {
	    _ + ( "a" | "e" ) => < "" , "" >;
	    _ => < "u" , "e" > 
	  }
    in
    {
      act = 
	table {
          VAct VSim (VPres VInd)  Sg P1 => -- Present Indicative
	    ( case pres_ind_base of {
		_ + "a" =>  ( init pres_ind_base ) ;
		_ => pres_ind_base
		}
	    ) + "o" + passPresEnding Sg P1 ;
	  VAct VSim (VPres VInd)  Sg P2 => -- Present Indicative
	    ( case inf_pres of {
		_ + "ri" => pres_ind_base  ;
		_ => ( case pres_ind_base of {
			 _ + "i" => init pres_ind_base ;
			 _ => pres_ind_base
			 }
		  ) + "e"
		}
	    ) + passPresEnding Sg P2 ;
          VAct VSim (VPres VInd)  Pl P3 => -- Present Indicative
	    pres_ind_base + fill.p1 + passPresEnding Pl P3 ;
          VAct VSim (VPres VInd)  n  p  => -- Present Indicative
	    pres_ind_base +
	    ( case pres_ind_base of {
		_ + #consonant => "i" ;
		_ => ""
		}
	    ) + passPresEnding n p ;
          VAct VSim (VPres VConj) n  p  => -- Present Conjunctive
	    pres_conj_base + passPresEnding n p ; 
          VAct VSim (VImpf VInd)  n  p  => -- Imperfect Indicative
	    impf_ind_base + passPresEnding n p ;
          VAct VSim (VImpf VConj) n  p  => -- Imperfect Conjunctive
	    impf_conj_base + passPresEnding n p ;
          VAct VSim VFut          Sg P1 => -- Future I
	    (init fut_I_base ) + 
	    ( case fut_I_base of {
		_ + "bi" => "o" ;
		_ => "a" 
		}
	    ) + passPresEnding Sg P1 ;
	  VAct VSim VFut          Sg P2 => -- Future I
	    ( case fut_I_base of {
		_ + "bi" => ( init fut_I_base ) + "e" ;
		_ => fut_I_base
		}
	    ) + passPresEnding Sg P2 ;
	  VAct VSim VFut          Pl P3 => -- Future I
	    (init fut_I_base ) + 
	    ( case fut_I_base of {
		_ + "bi" => "u" ;
		_ => "e" 
		}
	    ) + passPresEnding Pl P3 ;

          VAct VSim VFut          n  p  => -- Future I
	    fut_I_base + passPresEnding n p ;
          VAct VAnt (VPres VInd)  n  p  => -- Prefect Indicative
	    "######" ; -- Use participle
          VAct VAnt (VPres VConj) n  p  => -- Prefect Conjunctive
	    "######" ; -- Use participle
          VAct VAnt (VImpf VInd)  n  p  => -- Plusperfect Indicative
	    "######" ; -- Use participle
          VAct VAnt (VImpf VConj) n  p  => -- Plusperfect Conjunctive
	    "######" ; -- Use participle
          VAct VAnt VFut          n  p  => -- Future II 
	    "######" -- Use participle
        } ; 
      pass = 
	\\_ => "######" ; -- no passive forms
      inf = 
	table {
          VInfActPres       => -- Infinitive Present
	    inf_pres ;
          VInfActPerf Masc  => -- Infinitive Perfect
	    part_stem + "um" ;
	  VInfActPerf Fem   => -- Infinitive Perfect
	    part_stem + "am" ;
	  VInfActPerf Neutr => -- Infinitive Perfect
	    part_stem + "um" ;
	  VInfActFut Masc   => -- Infinitive Future
	    part_stem + "urum" ;
	  VInfActFut Fem    => -- Infinitive Perfect
	    part_stem + "uram" ; 
	  VInfActFut Neutr  => -- Infinitive Perfect
	    part_stem + "urum"
        } ;
      imp = 
	table {
	  VImp1 Sg             => -- Imperative I
	    ( case inf_pres of {
		_ + "ri" => imp_base ;
		_ => (init imp_base ) + "e" 
		}
	    ) + "re" ;
	  VImp1 Pl             => -- Imperative I
	    imp_base + "mini" ;
	  VImp2 Sg ( P2 | P3 ) => -- Imperative II
	    imp_base + "tor" ;
	  VImp2 Pl P2          => -- Imperative II
	    "######" ; -- really no such form?
	  VImp2 Pl P3          => -- Imperative II
	    pres_ind_base + fill.p1 + "ntor" ;
	  _ => "######" -- No imperative form
	} ;
      ger = 
	table {
	  VGenAcc => -- Gerund
	    pres_stem + fill.p2 + "ndum" ;
	  VGenGen => -- Gerund
	    pres_stem + fill.p2 + "ndi" ;
	  VGenDat => -- Gerund
	    pres_stem + fill.p2 + "ndo" ;
	  VGenAbl => -- Gerund
	    pres_stem + fill.p2 + "ndo" 
	} ;
      geriv =
	( mkAdjective
	    ( mkNoun ( pres_stem + fill.p2 + "ndus" ) ( pres_stem + fill.p2 + "ndum" ) 
		( pres_stem + fill.p2 + "ndi" ) ( pres_stem + fill.p2 + "ndo" ) ( pres_stem + fill.p2 + "ndo" ) 
		( pres_stem + fill.p2 + "nde" ) ( pres_stem + fill.p2 + "ndi" ) ( pres_stem + fill.p2 + "ndos" ) 
		( pres_stem + fill.p2 + "ndorum" ) ( pres_stem + fill.p2 + "ndis" ) 
		Masc )
	    ( mkNoun ( pres_stem + fill.p2 + "nda" ) ( pres_stem + fill.p2 + "ndam" ) 
		( pres_stem + fill.p2 + "ndae" ) ( pres_stem + fill.p2 + "ndae" ) ( pres_stem + fill.p2 + "nda" ) 
		      ( pres_stem + fill.p2 + "nda" ) ( pres_stem + fill.p2 + "ndae" ) ( pres_stem + fill.p2 + "ndas" ) 
		(pres_stem + fill.p2 +"ndarum" ) ( pres_stem + fill.p2 + "ndis" ) 
		Fem )
	    ( mkNoun ( pres_stem + fill.p2 + "ndum" ) ( pres_stem + fill.p2 + "ndum" ) 
		( pres_stem + fill.p2 + "ndi" ) ( pres_stem + fill.p2 + "ndo" ) ( pres_stem + fill.p2 + "ndo" ) 
		( pres_stem + fill.p2 + "ndum" ) ( pres_stem + fill.p2 + "nda" ) ( pres_stem + fill.p2 + "nda" ) 
		( pres_stem + fill.p2 + "ndorum" ) ( pres_stem + fill.p2 + "ndis" ) 
		      Neutr )
	    < \\_,_,_ => "" , "" >
	    < \\_,_,_ => "" , "" >
	).s!Posit ;
      sup = 
	table {
	  VSupAcc => -- Supin
	    part_stem + "um" ;
	  VSupAbl => -- Supin
	    part_stem + "u" 
	} ;
      partActPres = 
	( mkNoun ( pres_stem + fill.p2 + "ns" ) ( pres_stem + fill.p2 + "ntem" ) 
	    ( pres_stem + fill.p2 + "ntis" ) ( pres_stem + fill.p2 + "nti" ) ( pres_stem + fill.p2 + "nte" ) 
	    ( pres_stem + fill.p2 + "ns" ) ( pres_stem + fill.p2 + "ntes" ) ( pres_stem + fill.p2 + "ntes" ) 
	    ( pres_stem + fill.p2 + "ntium" ) ( pres_stem + fill.p2 + "ntibus" ) 
 	    Masc ).s ;
      partActFut = 
	( mkAdjective
	    ( mkNoun ( part_stem + "urus" ) ( part_stem + "urum" ) ( part_stem + "uri" ) 
		( part_stem + "uro" ) ( part_stem + "uro" ) ( part_stem + "ure" ) ( part_stem + "uri" ) 
		( part_stem + "uros" ) ( part_stem + "urorum" ) ( part_stem + "uris" ) 
		Masc )
	    ( mkNoun ( part_stem + "ura" ) ( part_stem + "uram" ) ( part_stem + "urae" ) 
		( part_stem + "urae" ) ( part_stem + "ura" ) ( part_stem + "ura" )( part_stem + "urae" ) 
		( part_stem + "uras" ) ( part_stem +"urarum" ) ( part_stem + "uris" ) 
		Fem )
	    ( mkNoun ( part_stem + "urum" ) ( part_stem + "urum" ) ( part_stem + "uri" ) 
		( part_stem + "uro" ) ( part_stem + "uro" ) ( part_stem + "urum" ) ( part_stem + "ura" ) 
		( part_stem + "ura" ) ( part_stem + "urorum" ) ( part_stem + "uris" ) 
		Neutr )
	    < \\_,_,_ => "" , "" >
	    < \\_,_,_ => "" , "" >
	).s!Posit ;
      partPassPerf = 
	( mkAdjective
	    ( mkNoun ( part_stem + "us" ) ( part_stem + "um" ) ( part_stem + "i" ) 
		( part_stem + "o" ) ( part_stem + "o" ) ( part_stem + "e" ) 
		( part_stem + "i" ) ( part_stem + "os" ) ( part_stem + "orum" ) 
		( part_stem + "is" ) 
		Masc )
	    ( mkNoun ( part_stem + "a" ) ( part_stem + "am" ) ( part_stem + "ae" ) 
		( part_stem + "ae" ) ( part_stem + "a" ) ( part_stem + "a" ) 
		( part_stem + "ae" ) ( part_stem + "as" ) ( part_stem + "arum" ) 
		( part_stem + "is" ) 
		Fem )
	    ( mkNoun ( part_stem + "um" ) ( part_stem + "um" ) ( part_stem + "i" ) 
		( part_stem + "o" ) ( part_stem + "o" ) ( part_stem + "um" ) 
		( part_stem + "a" ) ( part_stem + "a" ) ( part_stem + "orum" ) 
		( part_stem + "is" ) 
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
        VInfActPerf _    => "fuisse" ;
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
  	VInfActPres   => "velle" ;
  	VInfActPerf _ => "voluisse" ;
  	_             => "######" -- No infinitive future
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

