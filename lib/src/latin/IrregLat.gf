--# -path=.:prelude:../abstract:../common

concrete IrregLat of IrregLatAbs = CatLat ** open ParadigmsLat, ResLat in {
--
--flags optimize=values ;
--
--  lin

  lin
    be_V : Verb = 
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
      	    VAct VAnt (VPres VInd)  Pl P3 => "fu" + actPerfEnding Pl P3 ;
       	    VAct VAnt (VPres VInd)  n  p  => "fui" + actPerfEnding n p ;
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
	  table {
	    _ => "######" -- No gerund form of esse
	  } ;
	geriv = 
	  \\_,_,_ => "######" ; -- No gerundive form of esse
	sup = 
	  table {
	    _ => "######" -- No supin form of esse
	  } ;
	partActPres = 
	  ( mkNoun "ens" "entem" "entis" "enti" "ente" "ens" 
	      "entes" "entes" "entium" "entibus" 
	      Masc ).s ;
	partActFut = 
	  \\_,_,_ => "######" ; -- No future active participle of esse
	partPassPerf = 
	  \\_,_,_ => "######" -- No prefect passive participle of esse
      };

    want_V = 
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
}
