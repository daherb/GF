--# -path=.:../abstract:../common:../prelude

--1 Latlish auxiliary operations.

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
    (cela,cele,celab,celo,celant,celare,celavi,celatus,celabo,celabunt,celabi : Str) 
      -> Verb = 
    \cela,cele,celab,celo,celant,celare,celavi,celatus,celabo,celabunt,celabi -> 
    let
      celav = init celavi ;
      tustatum = table {
      	Masc =>  table Number [ "tus" ; "ti" ] ;
      	Fem =>   table Number [ "ta" ; "tae" ] ;
      	Neutr => table Number [ "tum" ; "ta" ] 
      	}
    in {
      act = table {
        VAct VSim (VPres VInd)  Sg P1 => celo ; -- Present Indicative
        VAct VSim (VPres VInd)  Pl P3 => celant ; -- Present Indicative
        VAct VSim (VPres VInd)  n  p  => cela + actPresEnding n p ; -- Present Indicative
        VAct VSim (VPres VConj) n  p  => cele + actPresEnding n p ; -- Present Conjunctive
        VAct VSim (VImpf VInd)  n  p  => celab + "ba" + actPresEnding n p ; -- Imperfect Indicative
        VAct VSim (VImpf VConj) n  p  => celare + actPresEnding n p ; -- Imperfect Conjunctive
        VAct VSim VFut          Sg P1 => celabo ; -- Future I 
	VAct VSim VFut          Pl P3 => celabunt ; -- Future I
        VAct VSim VFut          n  p  => celabi + actPresEnding n p ; -- Future I
        VAct VAnt (VPres VInd)  Pl P3 => celav + "erunt" ;  -- Perfect Indicative
        VAct VAnt (VPres VInd)  n  p  => celavi + actPerfEnding n p ; -- Prefect Indicative
        VAct VAnt (VPres VConj) n  p  => celav + "eri" + actPresEnding n p ; -- Prefect Conjunctive
        VAct VAnt (VImpf VInd)  n  p  => celav + "era" + actPresEnding n p ; -- Plusperfect Indicative
        VAct VAnt (VImpf VConj) n  p  => celav + "isse" + actPresEnding n p ; -- Plusperfect Conjunctive
        VAct VAnt VFut          Sg P1 => celav + "ero" ; -- Future II 
        VAct VAnt VFut          n  p  => celav + "eri" + actPresEnding n p -- Future II
        } ;
      pass = table {
	VPass (VPres VInd)  Sg P1 => celo + passPresEnding Sg P1 ;
	VPass (VPres VInd)  n  p  => cela + passPresEnding n p ;
	VPass (VPres VConj) n  p  => cele + passPresEnding n p ;
	VPass (VImpf VInd)  n  p  => cela + "ba" + passPresEnding n p ;
	VPass (VImpf Ind)   n  p  => cela + "re" + passPresEnding n p ;
	VPass VFut          Sg P1 => cela + "bo" + passPresEnding Sg P1 ;
	VPass VFut          Sg P2 => cela + "be" + passPresEnding Sg P2 ;
	VPass VFut          Pl P3 => cela + "bu" + passPresEnding Pl P3 ;
	VPass VFut          n  p  => cela + "bi" + passPresEnding n p 
	} ;
      inf = table {
        VInfActPres      => celare ;
        VInfActPerf      => celav + "isse" ;
	VInfActFut Masc  => cela + "turum" ;
	VInfActFut Fem   => cela + "turam" ; 
	VInfActFut Neutr => cela + "turum"
        } ;
      imp = table {
	VImp1 Sg => cela ;
	VImp1 Pl => cela + "te" ;
	VImp2 Sg ( P2 | P3 ) => cela + "to" ;
	VImp2 Pl P2 => cela + "tote" ;
	VImp2 Pl P3 => cela + "nto" ;
	_ => "No imperative form"
	} ;
      ger = table {
	VGenAcc => cela + "ndum" ;
	VGenGen => cela + "ndi" ;
	VGenDat => cela + "ndo" ;
	VGenAbl => cela + "ndo" 
	} ;
--      geriv = ( adj ( cela + "ndus" ) ).s!Posit ;
      geriv = ( mkAdjective
		  ( mkNoun ( cela + "ndus" ) ( cela + "ndum" ) ( cela + "ndi" ) ( cela + "ndo" ) ( cela + "ndo" ) 
		      ( cela + "nde" ) ( cela + "ndi" ) ( cela + "ndos" ) ( cela + "ndorum" ) ( cela + "ndis" ) 
		       Masc )
		  ( mkNoun ( cela + "nda" ) ( cela + "ndam" ) ( cela + "ndae" ) ( cela + "ndae" ) ( cela + "nda" ) 
		      ( cela + "nda" ) ( cela + "ndae" ) ( cela + "ndas" ) (cela +"ndarum" ) ( cela + "ndis" ) Fem )
		  ( mkNoun ( cela + "ndum" ) ( cela + "ndum" ) ( cela + "ndi" ) ( cela + "ndo" ) ( cela + "ndo" ) 
		      ( cela + "ndum" ) ( cela + "nda" ) ( cela + "nda" ) ( cela + "ndorum" ) ( cela + "ndis" ) Neutr )
		  < \\_,_,_ => "" , "" >
		  < \\_,_,_ => "" , "" >
	).s!Posit ;
      sup = table {
	VSupAcc => cela + "tum" ;
	VSupAbl => cela + "tu" 
	} ;
--      partActPres = ( adj123 ( cela + "ns" ) ( cela + "ntis" ) ).s!Posit ;
      partActPres = ( mkNoun ( cela + "ns" ) ( cela + "ntem" ) ( cela + "ntis" ) ( cela + "nti" ) ( cela + "nte" ) 
 			( cela + "ns" ) ( cela + "ntes" ) ( cela + "ntes" ) ( cela + "ntium" ) ( cela + "ntibus" ) 
 			Masc ).s ;
      partActFut = ( mkAdjective
		       ( mkNoun ( cela + "turus" ) ( cela + "turum" ) ( cela + "turi" ) ( cela + "turo" ) 
			   ( cela + "turo" ) ( cela + "ture" ) ( cela + "turi" ) ( cela + "turos" ) ( cela + "turorum" ) 
			   ( cela + "turis" ) Masc )
		       ( mkNoun ( cela + "tura" ) ( cela + "turam" ) ( cela + "turae" ) ( cela + "turae" ) 
			   ( cela + "tura" ) ( cela + "tura" )( cela + "turae" ) ( cela + "turas" ) ( cela +"turarum" ) 
			   ( cela + "turis" ) Fem )
		       ( mkNoun ( cela + "turum" ) ( cela + "turum" ) ( cela + "turi" ) ( cela + "turo" ) ( cela + "turo" )
			   ( cela + "turum" ) ( cela + "tura" ) ( cela + "tura" ) ( cela + "turorum" ) ( cela + "turis" ) 
			   Neutr )
		       < \\_,_,_ => "" , "" >
		       < \\_,_,_ => "" , "" >
	).s!Posit ;
--      partPassPerf = ( adj ( cela + "tus" ) ).s!Posit
      partPassPerf = ( mkAdjective
			 ( mkNoun ( cela + "tus" ) ( cela + "tum" ) ( cela + "ti" ) ( cela + "to" ) ( cela + "to" ) ( cela + "te" ) 
			     ( cela + "ti" ) ( cela + "tos" ) ( cela + "torum" ) ( cela + "tis" ) Masc )
			 ( mkNoun ( cela + "ta" ) ( cela + "tam" ) ( cela + "tae" ) ( cela + "tae" ) ( cela + "ta" ) 
			     ( cela + "ta" ) ( cela + "tae" ) ( cela + "tas" ) ( cela + "tarum" ) ( cela + "tis" ) Fem )
			 ( mkNoun ( cela + "tum" ) ( cela + "tum" ) ( cela + "ti" ) ( cela + "to" ) ( cela + "to" ) 
			     ( cela + "tum" ) ( cela + "ta" ) ( cela + "ta" ) ( cela + "torum" ) ( cela + "tis" ) Neutr ) 
			 < \\_,_,_ => "" , "" >
			 < \\_,_,_ => "" , "" >
	).s!Posit ;
    } ;

  actPresEnding : Number -> Person -> Str = 
    useEndingTable <"m", "s", "t", "mus", "tis", "nt"> ;

  actPerfEnding : Number -> Person -> Str = 
    useEndingTable <"", "sti", "t", "mus", "stis", "erunt"> ;

  passPresEnding : Number -> Person -> Str =
    useEndingTable <"r", "ris", "tur", "mur", "mini", "ntur"> ;

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

  esse_V : Verb = 
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
      pass = \\_ => "No passive form" ;
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
	_ => "No such imperative form of esse"	  
	} ;
      ger = table {
	_ => "No gerund form of esse"
	} ;
      geriv = \\_,_,_ => "No gerundive form of esse" ;
      sup = table {
	_ => "No supin form of esse"
	} ;
--      partActPres = ( adj123 "ens" "entis" ).s!Posit ; -- only medieval latin cp. http://en.wiktionary.org/wiki/ens#Latin
      partActPres = ( mkNoun "ens" "entem" "entis" "enti" "ente" "ens" 
			"entes" "entes" "entium" "entibus" 
			Masc ).s ;
      partActFut = \\_,_,_ => "No future active participle of esse" ;
      partPassPerf = \\_,_,_ => "No prefect passive participle of esse"

    };
	  
    
    -- esse_V : Verb = 
    --   let
    --     esse = mkVerb "es" "si" "era" "sum" "sunt" "esse" "fui" "*futus"
    --                   "ero" "erunt" "eri" ;
  --   in {
  --     act = table {
  --       VAct VSim (VPres VInd)  Sg P2 => "es" ; 
  --       VAct VSim (VPres VInd)  Pl P1 => "sumus" ; 
  --       v => esse.act ! v
  --       } ;
  --     inf = esse.inf
  --     } ;

  verb1 : Str -> Verb = \celare ->
    let 
      cela = Predef.tk 2 celare ;
      cel  = init cela ;
      celo = cel + "o" ;
      cele = cel + "e" ;
      celavi = cela + "vi" ;
      celatus = cela + "tus" ;
    in mkVerb cela cele cela celo (cela + "nt") celare celavi celatus 
              (cela + "bo") (cela + "bunt") (cela + "bi") ;

  verb2 : Str -> Verb = \habere ->
    let 
      habe = Predef.tk 2 habere ;
      hab  = init habe ;
      habeo = habe + "o" ;
      habea = habe + "a" ;
      habui = hab + "ui" ;
      habitus = hab + "itus" ;
    in mkVerb habe habea habe habeo (habe + "nt") habere habui habitus
              (habe + "bo") (habe + "bunt") (habe + "bi") ;

  verb3 : (_,_,_ : Str) -> Verb = \gerere,gessi,gestus ->
    let 
      gere = Predef.tk 2 gerere ;
      ger  = init gere ;
      gero = ger + "o" ;
      geri = ger + "i" ;
      gera = ger + "a" ;
    in mkVerb geri gera gere gero (ger + "unt") gerere gessi gestus
              (ger + "am") (ger + "ent") gere ; 

  verb3i : (_,_,_ : Str) -> Verb = \iacere,ieci,iactus ->
    let 
      iac   = Predef.tk 3 iacere ;
      iaco  = iac + "io" ;
      iaci  = iac + "i" ;
      iacie = iac + "ie" ;
      iacia = iac + "ia" ;
    in mkVerb iaci iacia iacie iaco (iaci + "unt") iacere ieci iactus
              (iac + "iam") (iac + "ient") iacie ; 

  verb4 : (_,_,_ : Str) -> Verb = \sentire,sensi,sensus ->
    let 
      senti  = Predef.tk 2 sentire ;
      sentio = senti + "o" ;
      sentia = senti + "a" ;
      sentie = senti + "e" ;
    in mkVerb senti sentia sentie sentio (senti + "unt") sentire sensi sensus
              (senti + "am") (senti + "ent") sentie ; 


-- smart paradigms

  verb_pppi : (iacio,ieci,iactus,iacere : Str) -> Verb = 
    \iacio,ieci,iactus,iacere ->
    case iacere of {
    _ + "are" => verb1 iacere ;
    _ + "ire" => verb4 iacere ieci iactus ;
    _ + "ere" => case iacio of {
      _ + "eo" => verb2 iacere ;
      _ + "io" => verb3i iacere ieci iactus ;
      _ => verb3 iacere ieci iactus
      } ;
    _ => Predef.error ("verb_pppi: illegal infinitive form" ++ iacere) 
    } ;

  verb : (iacere : Str) -> Verb = 
    \iacere ->
    case iacere of {
    _ + "are" => verb1 iacere ;
    _ + "ire" => let iaci = Predef.tk 2 iacere 
                 in verb4 iacere (iaci + "vi") (iaci + "tus") ;
    _ + "ere" => verb2 iacere ;
    _ => Predef.error ("verb: illegal infinitive form" ++ iacere) 
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

  Preposition : Type = {s : Str ; c : Case} ;

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

  mkPrep : Str -> Case -> {s : Str ; c : Case} = \s,c -> {s = s ; c = c} ;

  mkAdv : Str -> { s: Str } = \adv -> { s = adv } ;

param
  Unit = one | ten | hundred | thousand | ten_thousand | hundred_thousand ;

}

