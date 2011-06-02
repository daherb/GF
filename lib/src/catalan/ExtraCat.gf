concrete ExtraCat of ExtraCatAbs = ExtraRomanceCat ** 
  open CommonRomance, ParadigmsCat, PhonoCat, MorphoCat, ParamX, ResCat in {

lin
	i8fem_Pron =  mkPronoun
      	"jo" "em" "em" "mi"  ["el meu"] ["la meva"] ["els meus"] ["les meves"]
		Fem Sg P1 ;

      these8fem_NP = makeNP "aquestes" Fem Pl ;
      they8fem_Pron = mkPronoun
      "elles" "les" "les" "elles"
      "llur" "llur" "llurs" "llurs"
      Fem Pl P3 ;
    this8fem_NP = pn2np (mkPN ["aquesta"] Fem) ;
    those8fem_NP = makeNP ["aquestes"] Fem Pl ;

    we8fem_Pron = 
	  mkPronoun 
	    "nosaltres" "ens" "ens" "nosaltres"
	    ["el nostre"] ["la nostra"] ["els nostres"] ["les nostres"]
      	Fem Pl P1 ;

    whoPl8fem_IP = {s = \\c => prepCase c ++ "qui" ; a = aagr Fem Pl} ;
    whoSg8fem_IP = {s = \\c => prepCase c ++ "qui" ; a = aagr Fem Sg} ;

    youSg8fem_Pron = mkPronoun 
  		"tu" "et" "et" "tu"
    	["el teu"] ["la teva"] ["els teus"] ["les teves"]
      	Fem Sg P2 ;
    youPl8fem_Pron = mkPronoun
      "vosaltres" "us" "us" "vosaltres"
      ["el vostre"] ["la vostra"] ["els vostres"] ["les vostres"]
      Fem Pl P2 ;
    youPol8fem_Pron = mkPronoun
      "vost�" "la" "li" "vost�"
      ["el seu"] ["la seva"] ["els seus"] ["les seves"]
      Fem Sg P3 ;

oper
	vostePl : ParadigmsCat.Gender -> Pron = \g -> lin Pron (mkPronoun
      "vost�s" "els" "li" "vost�s"
      "llur" "llur" "llurs" "llurs"
      g Pl P3) ;
lin
    youPolPl_Pron = vostePl Masc;
    youPolPl8fem_Pron = vostePl Fem;


}