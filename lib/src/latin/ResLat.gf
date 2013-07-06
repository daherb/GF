--# -path=.:../abstract:../common:../prelude

--1 Latlish auxiliary operations.

resource ResLat = ParamX ** open Prelude in {

param
  Gender = Masc | Fem | Neutr ;
  Case = Nom | Acc | Gen | Dat | Abl | Voc ;
--  Degree = DPos | DComp | DSup ;

oper
  Noun : Type = {s : Number => Case => Str ; g : Gender} ;
  Adjective : Type = {s : Degree => Gender => Number => Case => Str} ;

  -- sounds and sound changes
  vowel : pattern Str = #( "a" | "e" | "o" | "u" | "y" );
  consonant : pattern Str = #( "p" | "b" | "f" | "v" | "m" | "t" | "d" | "s" | "z" | "n" | "r" | "c" | "g" | "l" | "q" | "h" );
  semivowel : pattern Str = #( "j" | "w" );
  stop : pattern Str = #( "p" | "b" | "t" | "d" | "c" | "q" | "q" ); 
  fricative : pattern Str = #( "f" | "v" | "s" | "z" | "h" );
  nasal : pattern Str = #( "m" | "n" );
  liquid : pattern Str = #( "r" | "l" );

-- To file as a bug :
--  consonant : pattern Str = stop | fricative;
--  test : Str -> Str =
--    \n ->
--    case n of {
--      #consonant + rest => "Got it";
--      full => "Nope"
--    };
-- Results in src/compiler/GF/Compile/Compute/ConcreteLazy.hs:(320,16)-(321,51): Non-exhaustive patterns in case

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
  
    
  -- declensions

  noun1 : Str -> Noun = \mensa ->
    let 
      mensae = mensa + "e" ;
      mensis = init mensa + "is" ;
    in
    mkNoun 
      mensa (mensa +"m") mensae mensae mensa mensa
      mensae (mensa + "s") (mensa + "rum") mensis
      Fem ;

  noun2us : Str -> Noun = \servus ->
    let
      serv = Predef.tk 2 servus ;
      servum = serv + "um" ;
      servi = serv + "i" ;
      servo = serv + "o" ;
    in
    mkNoun 
      servus servum servi servo servo (serv + "e")
      servi (serv + "os") (serv + "orum") (serv + "is")
      Masc ;

  noun2er : Str -> Str -> Noun = \liber,libri ->
    let
      libr : Str = Predef.tk 1 libri;
      librum = libr + "um" ;
      libri = libr + "i" ;
      libro = libr + "o" ;
    in
    mkNoun 
      liber librum libri libro libro liber
      libri ( libr + "os" ) ( libr + "orum" ) ( libr + "is" )
      Masc ;

  noun2um : Str -> Noun = \bellum ->
    let
      bell = Predef.tk 2 bellum ;
      belli = bell + "i" ;
      bello = bell + "o" ;
      bella = bell + "a" ;
    in
    mkNoun 
      bellum bellum belli bello bello (bell + "um")
      bella bella (bell + "orum") (bell + "is")
      Neutr ;

-- Consonant declension
  noun3c : Str -> Str -> Gender -> Noun = \rex,regis,g ->
    let
      reg : Str = Predef.tk 2 regis ;
      regemes : Str * Str = case g of {
	Masc | Fem => < reg + "em" , reg + "es" > ;
	Neutr => < rex , reg + "a" > 
	} ;
    in
    mkNoun
      rex regemes.p1 ( reg + "is" ) ( reg + "i" ) ( reg + "e" ) rex
      regemes.p2 regemes.p2 ( reg + "um" ) ( reg + "ibus" ) 
      g ;

-- i-declension
  noun3i : Str -> Str -> Gender -> Noun = \ars,artis,g ->
    let 
      art : Str = Predef.tk 2 artis ;
      artemes : Str * Str = case g of {
	Masc | Fem => < art + "em" , art + "es" > ;
	Neutr => case art of {
	  _ + #consonant + #consonant => < ars , art + "a" > ; -- maybe complete fiction but may be working
	  _ => < ars , art + "ia" > -- Bayer-Landauer 32 4
	  }
	} ;
      arte : Str = case ars of {
	_ + ( "e" | "al" | "ar" ) => art + "i" ;
	_ => art + "e"
	};
    in
    mkNoun
      ars artemes.p1 ( art + "is" ) ( art + "i" ) arte ars
      artemes.p2 artemes.p2 ( art + "ium" ) ( art + "ibus" ) 
      g ;

-- smart paradigm for declensions 1&2

  noun12 : Str -> Noun = \verbum -> 
    case verbum of {
      _ + "a"  => noun1 verbum ;
      _ + "us" => noun2us verbum ;
      _ + "um" => noun2um verbum ;
      _ + ( "er" | "ir" ) => 
	let
	  puer = verbum ; 
	  pue = Predef.tk 1 puer ; 
	  e = case puer of {
	    -- Exception of nouns where e is part of the word stem Bayer-Landauer 27 4.2
	    "puer" | "socer" | "gener" | "vesper" => "e" ;
	    -- Exception of adjectives where e is part of the word stem 31 3.2
	    ("asper" | "miser" | "tener" | "frugifer") + _ => "e";
	    -- "liber" => ( "e"  | "" ) ; conflicting with noun liber
	    _ => ""
	    } ;
	  pu = Predef.tk 1 pue ;
	  in noun2er verbum ( pu + e + "ri" );
      _  => Predef.error ("noun12 does not apply to" ++ verbum)
      } ;

--  noun3 = overload {
  noun3 : Str -> Str -> Gender -> Noun = \rex,regis,g ->
    let
      reg : Str = Predef.tk 2 regis ;
    in
    case <rex,reg> of {
      -- Bos has to many exceptions to be handled correctly
      < "bos" , "bov" > => mkNoun "bos" "bovem" "bovis" "bovi" "bove" "bos" "boves" "boves" "boum" "bobus" g;
      -- Some exceptions with no fitting rules
      < "nix" , _ > => noun3i rex regis g; -- L...
      < ( "sedes" | "canis" | "iuvenis" | "mensis" | "sal" ) , _ > => noun3c rex regis g ;  -- Bayer-Landauer 31 3 and Exercitia Latina 32 b), sal must be handled here because it will be handled wrongly by the next rule 
      < _ + ( "e" | "al" | "ar" ) , _ > => noun3i rex regis g ; -- Bayer-Landauer 32 2.3
      < _ + "ter", _ + "tr" > => noun3c rex regis g ; -- might not be right but seems fitting for Bayer-Landauer 31 2.2 
      < _ , _ + #consonant + #consonant > => noun3i rex regis g ; -- Bayer-Landauer 32 2.2
      < _ + ( "is" | "es" ) , _ > => 
	if_then_else 
	  Noun 
	  -- assumption based on Bayer-Landauer 32 2.1
	  ( pbool2bool ( Predef.eqInt ( Predef.length rex ) ( Predef.length regis ) ) ) 
	  ( noun3i rex regis g ) 
	  ( noun3c rex regis g ) ;
      _ => noun3c rex regis g
    } ;

--   noun3 : Str -> Noun = \labor -> 
--     case labor of {
--       _    + "r"   => noun3c labor (labor + "is")    Masc ;
--       fl   + "os"  => noun3c labor (fl    + "oris")  Masc ;
--       lim  + "es"  => noun3c labor (lim   + "itis")  Masc ;
--       cod  + "ex"  => noun3c labor (cod   + "icis")  Masc ;
--       poem + "a"   => noun3c labor (poem  + "atis")  Neutr ;
--       calc + "ar"  => noun3c labor (calc  + "aris")  Neutr ;
--       mar  + "e"   => noun3c labor (mar   + "is")    Neutr ;
--       car  + "men" => noun3c labor (car   + "minis") Neutr ;
--       rob  + "ur"  => noun3c labor (rob   + "oris")  Neutr ;
--       temp + "us"  => noun3c labor (temp  + "oris")  Neutr ;
--       vers + "io"  => noun3c labor (vers  + "ionis") Fem ;
--       imag + "o"   => noun3c labor (imag  + "inis")  Fem ;
--       ae   + "tas" => noun3c labor (ae    + "tatis") Fem ;
--       vo   + "x"   => noun3c labor (vo    + "cis")   Fem ;
--       pa   + "rs"  => noun3c labor (pa    + "rtis")  Fem ;
--       cut  + "is"  => noun3c labor (cut   + "is")    Fem ;
--       urb  + "s"   => noun3c labor (urb   + "is")    Fem ;
--       _  => Predef.error ("noun3 does not apply to" ++ labor)
--       } ;
-- };

  noun4us : Str -> Noun = \fructus -> 
    let
      fructu = init fructus ;
      fruct  = init fructu
    in
    mkNoun
      fructus (fructu + "m") fructus (fructu + "i") fructu fructus
      fructus fructus (fructu + "um") (fruct + "ibus")
      Masc ;

  noun4u : Str -> Noun = \cornu -> 
    let
      corn = init cornu ;
      cornua = cornu + "a"
    in
    mkNoun
      cornu cornu (cornu + "s") cornu cornu cornu
      cornua cornua (cornu + "um") (corn + "ibus")
      Neutr ;

  noun5 : Str -> Noun = \res -> 
    let
      re = init res ;
      rei = re + "i"
    in
    mkNoun
      res (re+ "m") rei rei re res
      res res (re + "rum") (re + "bus")
      Fem ;

-- to change the default gender

    nounWithGen : Gender -> Noun -> Noun = \g,n ->
      {s = n.s ; g = g} ;

-- smart paradigms

  noun_ngg : Str -> Str -> Gender -> Noun = \verbum,verbi,g -> 
    let s : Noun = case <verbum,verbi> of {
      <_ + "a",  _ + "ae"> => noun1 verbum ;
      <_ + "us", _ + "i">  => noun2us verbum ;
      <_ + "um", _ + "i">  => noun2um verbum ;
      <_ + ( "er" | "ir" ) , _ + "i">  => noun2er verbum verbi ;

      <_ + "us", _ + "us"> => noun4us verbum ;
      <_ + "u",  _ + "us"> => noun4u verbum ;
      <_ + "es", _ + "ei"> => noun5 verbum ;
      _  => noun3 verbum verbi g
      }
    in  
    nounWithGen g s ;

  noun : Str -> Noun = \verbum -> 
    case verbum of {
      _ + "a"  => noun1 verbum ;
      _ + "us" => noun2us verbum ;
      _ + "um" => noun2um verbum ;
      _ + ( "er" | "ir" ) => noun2er verbum ( (Predef.tk 2 verbum) + "ri" ) ;
      _ + "u"  => noun4u verbum ;
      _ + "es" => noun5 verbum ;
      _  => Predef.error ("3rd declinsion cannot be applied to just one noun form " ++ verbum)
      } ;

-- adjectives

  mkAdjective : (_,_,_ : Noun) -> Adjective = \bonus,bona,bonum ->
    let comp_super : ( Gender => Number => Case => Str ) * ( Gender => Number => Case => Str ) =
	  case bonus.s!Sg!Gen of {
	    -- Exception Bayer-Landauer 50 1
	    "boni" => < comp "meli" , table Gender [ (noun1 "optimus").s ; (noun2us "optima").s ; (noun2um "optimum").s ] > ;
	    "mali" => < comp "pei" , super "pessus" > ;
	    "magni" => < comp "mai" , table Gender [ (noun1 "maximus").s; (noun2us "maxima").s ; (noun2um "maximum").s ] > ;
	    "parvi" => < comp "mini" , table Gender [ (noun1 "minimus").s ; (noun2us "minima").s ; (noun2um "minimum").s ] >;
	    --Exception Bayer-Landauer 50.3
	    "novi" => < comp "recenti" , super "recens" > ;
	    "feri" => < comp "feroci" , super "ferox" > ;
	    "sacris" => < comp "sancti" , super "sanctus" >;
	    "frugiferi" => < comp "fertilis" , super "fertilis" > ;
	    "veti" => < comp "vetusti" , super "vetustus" >;
	    "inopis" => < comp "egentis" , super "egens" >;
	    -- Default Case use Singular Genetive to determine comparative
	    sggen => < comp sggen , super (bonus.s!Sg!Nom) >
	  }
    in
    {
      s = table {
	Posit => table {
	  Masc  => bonus.s ;
	  Fem   => bona.s ;
	  Neutr => bonum.s 
	  };
	Compar => comp_super.p1 ;
	Superl => comp_super.p2 
	}
    } ;
    
  adj12 : Str -> Adjective = \bonus ->
    let
      bon : Str = case bonus of {
	-- Exceptions Bayer-Landauer 41 3.2
	("asper" | "liber" | "miser" | "tener" | "frugifer") => bonus ;
	-- Usual cases
	pulch + "er" => pulch + "r" ;
	bon + "us" => bon ;
	_ => Predef.error ("adj12 does not apply to" ++ bonus)
	}
    in
    mkAdjective (noun12 bonus) (noun1 (bon + "a")) (noun2um (bon + "um")) ;

  adj3x : (_,_ : Str) -> Adjective = \acer,acris ->
   let
     ac = Predef.tk 2 acer ;
     acrise : Str * Str = case acer of {
       _ + "er" => <ac + "ris", ac + "re"> ; 
       _ + "is" => <acer      , ac + "e"> ;
       _        => <acer      , acer> 
       }
   in
   mkAdjective 
     (noun3adj acer acris Masc) 
     (noun3adj acrise.p1 acris Fem) 
     (noun3adj acrise.p2 acris Neutr) ;

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

  comp : Str -> ( Gender => Number => Case => Str ) = \boni -> -- Bayer-Landauer 46 2
    case boni of {
      bon + ( "i" | "is" ) => 
	table
	{
	  Fem | Masc => table {
	    Sg => table Case [ bon + "ior" ; 
			       bon + "iorem" ; 
			       bon + "ioris" ; 
			       bon + "iori" ; 
			       bon + "iore"; 
			       bon + "ior" ] ;
	    Pl => table Case [ bon + "iores" ; 
			       bon + "iores" ; 
			       bon + "iorum" ; 
			       bon + "ioribus" ; 
			       bon + "ioribus" ; 
			       bon + "iores" ]
	    } ;
	  Neutr => table {
	    Sg => table Case [ bon + "ius" ; 
			       bon + "ius" ; 
			       bon + "ioris" ; 
			       bon + "iori" ; 
			       bon + "iore" ; 
			       bon + "ius" ] ;
	    Pl => table Case [ bon + "iora" ; 
			       bon + "iora" ; 
			       bon + "iorum" ; 
			       bon + "ioribus" ; 
			       bon + "ioribus" ; 
			       bon + "iora" ] 
	    }
	}
    } ;

  super : Str -> (Gender => Number => Case => Str) = \bonus ->
    let
      prefix : Str = case bonus of {
	ac + "er" => bonus ; -- Bayer-Landauer 48 2
	faci + "lis" => faci + "l" ; -- Bayer-Landauer 48 3
	feli + "x" => feli + "c" ; -- Bayer-Landauer 48 1
	ege + "ns" => ege + "nt" ; -- Bayer-Landauer 48 1
	bon + ( "us" | "is") => bon -- Bayer-Landauer 48 1
	};
      suffix : Str = case bonus of {
	  ac + "er" => "rim" ; -- Bayer-Landauer 48 2
	  faci + "lis" => "lim" ; -- Bayer-Landauer 48 3
	  _ => "issim" -- Bayer-Landauer 48 1
	  };
    in
    table {
      Fem => (noun1 ( prefix + suffix + "a" )).s ;
      Masc => (noun2us ( prefix + suffix + "us" )).s ;
      Neutr => (noun2um ( prefix + suffix + "um" )).s
    } ;

-- smart paradigm

  adj123 : Str -> Str -> Adjective = \bonus,boni ->
    case <bonus,boni> of {
      <_ + ("us" | "er"), _ + "i" > => adj12 bonus ;
      <_ + ("us" | "er"), _ + "is"> => adj3x bonus boni ;
      <_                , _ + "is"> => adj3x bonus boni ;
      <_ + "is"         , _ + "e" > => adj3x bonus boni ;
      _ => Predef.error ("adj123: not applicable to" ++ bonus ++ boni)
    } ;

  adj : Str -> Adjective = \bonus ->
    case bonus of {
      _ + ("us" | "er") => adj12 bonus ;
      facil + "is"      => adj3x bonus bonus ;
      feli  + "x"       => adj3x bonus (feli + "cis") ;
      _                 => adj3x bonus (bonus + "is") ---- any example?
    } ;


-- verbs

  param 
  VActForm  = VAct VAnter VTense Number Person ;
  VPassForm = VPass VTense Gender Number Person ; -- No anteriority because perfect forms are built using participle
  VInfForm  = VInfActPres | VInfActPerf | VInfActFut ;
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
    partActPres  : Gender => Number => Case => Str ;
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
	VPass (VPres VInd)  g Sg P1 => celo + passPresEnding Sg P1 ;
	VPass (VPres VInd)  g n  p  => cela + passPresEnding n p ;
	VPass (VPres VConj) g n  p  => cele + passPresEnding n p ;
	VPass (VImpf VInd)  g n  p  => cela + passPresEnding n p ;
	VPass (VImpf Ind)   g n  p  => cela + "re" + passPresEnding n p ;
	VPass VFut          g Sg P1 => cela + "bo" + passPresEnding Sg P1 ;
	VPass VFut          g Sg P2 => cela + "be" + passPresEnding Sg P2 ;
	VPass VFut          g Pl P3 => cela + "bu" + passPresEnding Pl P3 ;
	VPass VFut          g n  p  => cela + "bi" + passPresEnding n p 
	} ;
      inf = table {
        VInfActPres => celare ;
        VInfActPerf => celav + "isse" ;
	VInfActFut => cela + "turum"
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
      geriv = ( adj ( cela + "ndus" ) ).s!Posit ;
      sup = table {
	VSupAcc => cela + "tum" ;
	VSupAbl => cela + "tu" 
	} ;
      partActPres = ( adj123 ( cela + "ns" ) ( cela + "ntis" ) ).s!Posit ;
      partActFut = ( adj ( cela + "turus" ) ).s!Posit ;
      partPassPerf = ( adj ( cela + "tus" ) ).s!Posit
    } ;

  actPresEnding : Number -> Person -> Str = 
    useEndingTable <"m", "s", "t", "mus", "tis", "nt"> ;

  actPerfEnding : Number -> Person -> Str = 
    useEndingTable <"", "sti", "t", "mus", "stis", "erunt"> ;

  passPresEnding : Number -> Person -> Str =
    useEndingTable <"r", "ris", "tur", "mur", "mini", "mur"> ;

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
        VInfActPres => "esse" ;
        VInfActPerf => "fuisse" ;
       	VInfActFut => "futurum esse"
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
      partActPres = ( adj123 "ens" "entis" ).s!Posit ; -- only medieval latin cp. http://en.wiktionary.org/wiki/ens#Latin
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

