--# -path=.:prelude:../abstract:../common

concrete IrregLat of IrregLatAbs = CatLat ** open Prelude, ParadigmsLat, ResLat in {
--
--flags optimize=values ;
--
--  lin

  lin
    be_V = 
      {
	act = 
	  table VActForm {
	    VAct VSim (VPres VInd)  n  p  => table Number [ table Person [ "sum" ; "es" ; "est" ] ;
							    table Person [ "sumus" ; "estis" ; "sunt" ]
	      ]! n ! p ;
       	    VAct VSim (VPres VConj) n  p  => "si" + actPresEnding n p ;
       	    VAct VSim (VImpf VInd)  n  p  => "era" + actPresEnding n p ;
       	    VAct VSim (VImpf VConj) n  p  => "esse" + actPresEnding n p ;
       	    VAct VSim VFut          Sg P1 => "ero" ;
       	    VAct VSim VFut          Pl P3 => "erunt" ;
       	    VAct VSim VFut          n  p  => "eri" + actPresEnding n p ;
       	    VAct VAnt (VPres VInd)  n  p  => "fu" + actPerfEnding n p ;
       	    VAct VAnt (VPres VConj) n  p  => "fueri" + actPresEnding n p ;
       	    VAct VAnt (VImpf VInd)  n  p  => "fuera" + actPresEnding n p ;
       	    VAct VAnt (VImpf VConj) n  p  => "fuisse" + actPresEnding n p ;
       	    VAct VAnt VFut          Sg P1 => "fuero" ;
       	    VAct VAnt VFut          n  p  => "fueri" + actPresEnding n p 
       	  } ;
	pass = 
	  \\_ => "######" ; -- No passive form
	inf = 
	  table {
            VInfActPres      => "esse" ;
            VInfActPerf _    => "fuisse" ;
       	    VInfActFut Masc  => "futurum" ;
	    VInfActFut Fem   => "futuram" ;
	    VInfActFut Neutr => "futurum"
          } ;
	imp = 
	  table {
	    VImp1 Sg => "es" ;
	    VImp1 Pl => "este" ;
	    VImp2 Sg ( P2 | P3 ) => "esto" ;
	    VImp2 Pl P2 => "estote" ;
	    VImp2 Pl P3 => "sunto" ;
	    _ => "######" -- No such imperative form of esse
	  } ;
	ger = 
	    \\_ => "######" ; -- No gerund form of esse
	geriv = 
	  \\_,_,_ => "######" ; -- No gerundive form of esse
	sup = 
	  \\_ => "######" ; -- No supin form of esse	  
	partActPres = 
	  ( mkNoun "ens" "entem" "entis" "enti" "ente" "ens" 
	      "entes" "entes" "entium" "entibus" 
	      Masc ).s ;
	partActFut = 
	  \\_,_,_ => "######" ; -- No future active participle of esse
	partPassPerf = 
	  \\_,_,_ => "######" -- No prefect passive participle of esse
      };

    can_VV = 
      let
    	pres_stem = "" ;
    	pres_ind_base = "" ;
    	pres_conj_base = "possi" ;
    	impf_ind_base = "potera" ;
    	impf_conj_base = "posse" ;
    	fut_I_base = "poteri" ;
    	imp_base = "" ;
    	perf_stem = "potu" ;
    	perf_ind_base = "potu" ;
    	perf_conj_base = "potueri" ;
    	pqperf_ind_base = "potuera" ;
    	pqperf_conj_base = "potuisse" ;
    	fut_II_base = "potueri" ;
    	part_base = "" ;
    	verb = mkVerb "posse" pres_stem pres_ind_base pres_conj_base impf_ind_base impf_conj_base fut_I_base
    	  imp_base perf_stem perf_ind_base perf_conj_base pqperf_ind_base pqperf_conj_base fut_II_base part_base ;
      in
      {
    	act =
    	  table {
    	    VAct VSim (VPres VInd)  n  p  => 
	      table Number [ table Person [ "possum" ; "potes" ; "potest" ] ;
    			     table Person [ "possumus" ; "potestis" ; "possunt" ]
    	      ] ! n ! p ;
    	    a => verb.act ! a
    	  } ;
    	pass = 
    	  \\_,_,_ => "######" ; -- no passive forms
    	inf = 
    	  \\a => verb.inf ! a ;
    	imp = 
    	  \\a => verb.imp ! a ;
    	sup =
    	  \\a => verb.sup ! a ;
    	ger =
    	  \\a => verb.ger ! a ;
    	geriv = 
    	  \\g,n,c => verb.geriv ! g ! n ! c ;
    	partActFut =>
    	  \\_,_,_ => "######" ; -- no such participle
    	partActPres = 
    	  \\g,n,c => verb.partActPres ! g ! n ! c ;
    	partPassPerf =>
    	  \\_,_,_ => "######" ; -- no such participle
    	isAux = False
      };
	  
    -- want_VV = 
    --   {
    -- 	act = table {
    -- 	  VAct VSim (VPres VInd)  n  p  => table Number [ table Person [ "volo" ; "vis" ; "vult" ] ;
    -- 							  table Person [ "volumus" ; "vultis" ; "volunt" ]
    -- 	    ]! n ! p ;
    -- 	  VAct VSim (VPres VConj) n  p  => "veli" + actPresEnding n p ;
    --    	  VAct VSim (VImpf VInd)  n  p  => "voleba" + actPresEnding n p ;
    --    	  VAct VSim (VImpf VConj) n  p  => "velle" + actPresEnding n p ;
    --    	  VAct VSim VFut          Sg P1 => "volam" ;
    --    	  VAct VSim VFut          n  p  => "vole" + actPresEnding n p ;
    --    	  VAct VAnt (VPres VInd)  n  p  => "volu" + actPerfEnding n p ;
    --    	  VAct VAnt (VPres VConj) n  p  => "volueri" + actPresEnding n p ;
    --    	  VAct VAnt (VImpf VInd)  n  p  => "voluera" + actPresEnding n p ;
    --    	  VAct VAnt (VImpf VConj) n  p  => "voluisse" + actPresEnding n p ;
    --    	  VAct VAnt VFut          Sg P1 => "voluero" ;
    --    	  VAct VAnt VFut          n  p  => "volueri" + actPresEnding n p 
    --    	  } ;
    -- 	ger = \\_ => "######" ; -- no gerund form for velle
    -- 	geriv = \\_,_,_ => "######" ; -- no gerundive form for velle
    -- 	imp = \\_ =>  "######" ; -- no imperative form for velle
    -- 	inf = table {
    -- 	  VInfActPres   => "velle" ;
    -- 	  VInfActPerf _ => "voluisse" ;
    -- 	  _             => "######" -- No infinitive future
    -- 	  } ;
    -- 	partActFut = \\_,_,_ => "######" ; -- no participle future active
    -- 	partActPres = ( mkNoun "volens" "volentem" "volentis" "volenti" "volente" "volens"
    -- 			  "volentes" "volentes" "volentium" "volentibus" 
    -- 			  Masc ).s ;
    -- 	partPassPerf = \\_,_,_ => "######" ; -- no participle perfect passive
    -- 	pass = \\_ => "######" ; -- no passive forms
    -- 	sup = \\_ => "######" -- no supin forms
    --   } ;
}
