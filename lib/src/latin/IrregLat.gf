--# -path=.:prelude:../abstract:../common

concrete IrregLat of IrregLatAbs = CatLat ** open Prelude, ParadigmsLat, ResLat in {
--
--flags optimize=values ;
--

  lin
    -- Bayer-Lindauer 93 1
    be_V =
      let
	pres_stem = "s" ;
	pres_ind_base = "su" ;
	pres_conj_base = "si" ;
	impf_ind_base = "era" ;
	impf_conj_base = "esse" ;
	fut_I_base = "eri" ;
	imp_base = "es" ;
	perf_stem = "fu" ;
	perf_ind_base = "fu" ;
	perf_conj_base = "fueri" ;
	pqperf_ind_base = "fuera" ;
	pqperf_conj_base = "fuisse" ;
	fut_II_base = "fueri" ;
	part_stem = "fut" ;
	verb = mkVerb "esse" pres_stem pres_ind_base pres_conj_base impf_ind_base impf_conj_base fut_I_base
    	  imp_base perf_stem perf_ind_base perf_conj_base pqperf_ind_base pqperf_conj_base fut_II_base part_stem ;
      in
      {
	act = 
	  table {
    	    VAct VSim (VPres VInd)  n  p  => 
	      table Number [ table Person [ "sum" ; "es" ; "est" ] ;
    			     table Person [ "sumus" ; "estis" ; "sunt" ]
    	      ] ! n ! p ;
    	    a => verb.act ! a
	  };
	pass =
	  \\_ => "######" ; -- no passive forms 
	inf =
	  verb.inf ;
	imp =
	  table {
	    VImp1 Sg => "es" ;
	    VImp1 Pl => "este" ;
	    VImp2 Pl P2 => "estote" ;
	    a => verb.imp ! a
	  } ;
	sup =
	  \\_ => "######" ; -- no supin forms
	ger =
	  \\_ => "######" ; -- no gerund forms
	geriv = 
	  \\_,_,_ => "######" ; -- no gerundive forms
	partActFut =
	  verb.partActFut ;
	partActPres = 
	  \\_,_,_ => "######" ; -- no such participle
	partPassPerf =
	  \\_,_,_ => "######" -- no such participle
      } ;

    -- Bayer-Lindauer 93 2.2
    can_VV = 
      let
    	pres_stem = "pos" ;
    	pres_ind_base = "pos" ;
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
    	part_stem = "" ;
    	verb = mkVerb "posse" pres_stem pres_ind_base pres_conj_base impf_ind_base impf_conj_base fut_I_base
    	  imp_base perf_stem perf_ind_base perf_conj_base pqperf_ind_base pqperf_conj_base fut_II_base part_stem ;
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
    	  \\_ => "######" ; -- no passive forms
    	inf = 
	  table {
	    VInfActFut _ => "######" ;
	    a => verb.inf ! a
	  } ;
    	imp = 
	  \\_ => "######" ;
    	sup = 
	  \\_ => "######" ;
    	ger =
	  \\_ => "######" ;
    	geriv =
	  \\_,_,_ => "######" ;
    	partActFut =
    	  \\_,_,_ => "######" ; -- no such participle
    	partActPres = 
	  \\_,_,_ => "######" ; -- no such participle
    	partPassPerf =
    	  \\_,_,_ => "######" ; -- no such participle
    	isAux = False
      };

    -- Bayer-Lindauer 94
    bring_V = 
      let
    	pres_stem = "fer" ;
    	pres_ind_base = "fer" ;
    	pres_conj_base = "fera" ;
    	impf_ind_base = "fereba" ;
    	impf_conj_base = "ferre" ;
    	fut_I_base = "fere" ;
    	imp_base = "fer" ;
    	perf_stem = "tul" ;
    	perf_ind_base = "tul" ;
    	perf_conj_base = "tuleri" ;
    	pqperf_ind_base = "tulera" ;
    	pqperf_conj_base = "tulisse" ;
    	fut_II_base = "tuleri" ;
    	part_stem = "lat" ;
    	verb = mkVerb "ferre" pres_stem pres_ind_base pres_conj_base impf_ind_base impf_conj_base fut_I_base
    	  imp_base perf_stem perf_ind_base perf_conj_base pqperf_ind_base pqperf_conj_base fut_II_base part_stem ;
      in
      {
    	act =
	  table {
	    VAct VSim (VPres VInd) n p => 
	      table Number [ table Person [ "fero" ; "fers" ; "fert" ] ;
			     table Person [ "ferimus" ; "fertis" ; "ferunt" ] 
	      ] ! n ! p ;
	    a => verb.act ! a
	  } ;
    	pass = 
	  table {
	    VPass (VPres VInd) n p => 
	      table Number [ table Person [ "feror" ; "ferris" ; "fertur" ] ;
			     table Person [ "ferimur" ; "ferimini" ; "feruntur" ]
	      ] ! n ! p ;
	    a => verb.pass ! a
	  } ;
    	inf = 
	  verb.inf ;	  
    	imp =
	  table {
	    VImp1 n => table Number [ "fer" ; "ferte" ] ! n ;
	    VImp2 Sg ( P2 | P3 ) => "ferto" ;
	    VImp2 Pl P2 => "fertote" ;
	    a => verb.imp ! a 
	  } ; 
    	sup = 
	  verb.sup ;
    	ger =
	  verb.ger ;
    	geriv =
	  verb.geriv ;
    	partActFut =
	  verb.partActFut ;
    	partActPres = 
	  verb.partActPres ;
    	partPassPerf =
	  verb.partPassPerf
      };

    -- Bayer-Lindauer 95
    want_VV = 
      let
	pres_stem = "vel" ;
	pres_ind_base = "vol" ;
	pres_conj_base = "veli" ;
	impf_ind_base = "voleba" ;
	impf_conj_base = "volle" ;
	fut_I_base = "vole" ;
	imp_base = "" ;
	perf_stem = "volu" ;
	perf_ind_base = "volu" ;
	perf_conj_base = "volueri" ;
	pqperf_ind_base = "voluera" ;
	pqperf_conj_base = "voluisse" ;
	fut_II_base = "volueri" ;
	part_stem = "volet" ;
	verb = mkVerb "velle" pres_stem pres_ind_base pres_conj_base impf_ind_base impf_conj_base fut_I_base
    	  imp_base perf_stem perf_ind_base perf_conj_base pqperf_ind_base pqperf_conj_base fut_II_base part_stem ;
      in
      {
	act =
	  table {
	    VAct VSim (VPres VInd)  n  p  => 
	      table Number [ table Person [ "volo" ; "vis" ; "vult" ] ;
    			     table Person [ "volumus" ; "vultis" ; "volunt" ]
    	      ] ! n ! p ;
    	    a => verb.act ! a
	  } ;
	  pass =
	    \\_ => "######" ;
	  ger = 
	    verb.ger ;
	  geriv =
	    verb.geriv ;
	  imp = 
	    \\_ => "######" ;
	  inf = 
	    verb.inf ;
	  partActFut =
	    \\_,_,_ => "######" ;
	  partActPres =
	    verb.partActPres ;
	  partPassPerf =
	    \\_,_,_ => "######" ;
	  sup =
	    verb.sup ;
	  isAux = False ;
      } ;

    -- Bayer-Lindauer 96 1
    go_V = 
      let
	pres_stem = "i" ;
	pres_ind_base = "i" ;
	pres_conj_base = "ea" ;
	impf_ind_base = "iba" ;
	impf_conj_base = "ire" ;
	fut_I_base = "ibi" ;
	imp_base = "i" ;
	perf_stem = "i" ;
	perf_ind_base = "i" ;
	perf_conj_base = "ieri" ;
	pqperf_ind_base = "iera" ;
	pqperf_conj_base = "isse" ;
	fut_II_base = "ieri" ;
	part_stem = "it" ;
	verb = mkVerb "ire" pres_stem pres_ind_base pres_conj_base impf_ind_base impf_conj_base fut_I_base
    	  imp_base perf_stem perf_ind_base perf_conj_base pqperf_ind_base pqperf_conj_base fut_II_base part_stem ;
      in
      {
	act =
	  table {
	    VAct VSim (VPres VInd)  n  p  => 
	      table Number [ table Person [ "eo" ; "is" ; "it" ] ;
    			     table Person [ "imus" ; "itis" ; "eunt" ]
    	      ] ! n ! p ;
	    VAct VAnt (VPres VInd)  Sg P2 => "isti" ;
	    VAct VAnt (VPres VInd)  Pl P2 => "istis" ;
    	    a => verb.act ! a
	  } ;
	pass = 
	  \\_ => "######"; -- no passive forms
	ger = 
	  table VGerund [ "eundum" ; "eundi" ; "eundo" ; "eundo" ] ;
	geriv =
	  verb.geriv ;
	imp =
	  table {
	    VImp2 Pl P3 => "eunto" ;
	    a => verb.imp ! a
	  } ;
	inf =
	  table {
	    VInfActPerf _ => "isse" ;
	    a =>verb.inf ! a
	  };
	partActFut = 
	  verb.partActFut ;
	partActPres = 
	  table {
	    Fem | Masc =>
	      ( mkNoun ( "iens" ) ( "euntem" ) ( "euntis" ) 
		  ( "eunti" ) ( "eunte" ) ( "iens" ) 
		  ( "euntes" ) ( "euntes" ) ( "euntium" ) 
		  ( "euntibus" ) 
 		  Masc ).s ;
	    Neutr =>
	      ( mkNoun ( "iens" ) ( "iens" ) ( "euntis" ) 
		  ( "eunti" ) ( "eunte" ) ( "iens" ) 
		  ( "euntia" ) ( "euntia" ) ( "euntium" ) 
		  ( "euntibus" ) 
 		  Masc ).s 
	  } ;
	partPassPerf = 
	  \\_,_,_ => "######" ; -- no such participle
	sup = 
	  \\_ => "######" -- really no such form?
      } ;

    -- Bayer-Lindauer 97
    become_V = 
      let
	pres_stem = "fi" ;
	pres_ind_base = "fi" ;
	pres_conj_base = "fia" ;
	impf_ind_base = "fieba" ;
	impf_conj_base = "fiere" ;
	fut_I_base = "fie" ;
	imp_base = "fi" ;
	perf_stem = "" ;
	perf_ind_base = "" ;
	perf_conj_base = "" ;
	pqperf_ind_base = "" ;
	pqperf_conj_base = "" ;
	fut_II_base = "" ;
	part_stem = "fact" ;

	verb = 
	  mkVerb "fieri" pres_stem pres_ind_base pres_conj_base impf_ind_base impf_conj_base fut_I_base imp_base
	  perf_stem perf_ind_base perf_conj_base pqperf_ind_base pqperf_conj_base fut_II_base part_stem ;
      in
      {
	act = 
	  table {
	    VAct VSim (VPres VInd) Sg P1 => "fio" ;
	    VAct VAnt _            _  _  => "######" ; -- perfect expressed by participle
	    a => verb.act ! a 
	  } ;
	pass =
	  \\_ => "######" ; -- no passive forms
	ger =
	  \\_ => "######" ; -- no gerund form
	geriv = 
	  \\_,_,_ => "######" ; -- no gerundive form
	imp = 
	  verb.imp ;
	inf = 
	  table {
	    VInfActPerf _ => "factus" ;
	    VInfActFut Masc => "futurum" ;
	    VInfActFut Fem => "futura" ;
	    VInfActFut Neutr => "futurum" ;
	    a => verb.inf ! a
	  } ;
	partActFut = 
	  \\_,_,_ => "######" ; -- no such participle
	partActPres = 
	  \\_,_,_ => "######" ; -- no such participle
	partPassPerf =
	  verb.partPassPerf ;
	sup = 
	  \\_ => "######" -- no supin
      } ;
	
}
