concrete LexSwe of Lex = CatSwe ** open ResSwe, Prelude in {

  lin
    walk_V = 
      mkVerb "g�" "g�r" "g�" "gick" "g�tt" "g�ngen" "g�nget" "g�ngna" ;
    help_V2 = 
      mkVerb "hj�lpa" "hj�lper" "hj�lp" "hj�lpte" "hj�lpt" "hj�lpt" "hj�lpt" "hj�lpta"
      ** {c2 = []} ;
    show_V3 = 
      mkVerb "visa" "visar" "visa" "visade" "visat" "visad" "visat" "visade"
      ** {c2 = [] ; c3 = "to"} ;
    want_VV = 
      mkVerb "vilja" "vill" "vilj" "ville" "velat" "velad" "velat" "velade" --- 
      ** {c2 = []} ;
    claim_VS = 
      mkVerb "h�vda" "h�vdar" "h�vda" "h�vdade" "h�vdat" "h�vdad" "h�vdat" "h�vdade" ;
    ask_VQ = 
      mkVerb "fr�ga" "fr�gar" "fr�ga" "fr�gade" "fr�gat" "fr�gad" "fr�gat" "fr�gade" ;

    dog_N  = mkNoun "hund" "hunden" "hundar" "hundarna" utrum ;
    son_N2 = mkNoun "son" "sonen" "s�ner" "s�nerna" utrum ** {c2 = "till"} ;
    way_N3 = mkNoun "v�g" "v�gen" "v�gar" "v�garna" utrum ** {c2 = "fr�n" ; c3 = "till"} ;

    warm_A = 
      mkAdjective "varm" "varmt" "varma" "varma" "varmare" "varmast" "varmaste" ;
    close_A2 = 
      mkAdjective "n�ra" "n�ra" "n�ra" "n�ra" "n�rmare" "n�rmast" "n�rmaste"
      ** {c2 = "till"} ;

    here_Adv = {s = "h�r"} ;
    very_AdA = {s = "mycket"} ;
    always_AdV = {s = "alltid"} ;

    only_Predet = {s = \\_ => "bara"} ;
    all_Predet = {s = gennumForms "all" "allt" "alla"} ;
    this_Quant = {s = \\_ => genderForms "denna" "detta" ; n = Sg ; det = DDef Indef} ;
    these_Quant = {s = \\_,_ => "dessa" ; n = Pl ; det = DDef Indef} ;
    
    i_Pron  = mkNP "jag"  "mig"  "min" "mitt" "mina"  SgUtr P1 ;
    he_Pron = mkNP "han"  "honom"  "hans" "hans" "hans"  SgUtr P3 ;
    we_Pron = mkNP "vi"  "oss"  "v�r" "v�rt" "v�ra"  Plg P1 ;

    whoSg_IP = {s = vem.s ; gn = SgUtr} ;
    whoPl_IP = {s = vem.s ; gn = Plg} ;

    when_IAdv = {s = "n�r"} ;
    where_IAdv = {s = "var"} ;
    why_IAdv = {s = "varf�r"} ;

    whichSg_IDet = {s = genderForms "vilken" "vilket" ; n = Sg ; det = DDef Indef} ;
    whichPl_IDet = {s = \\_ => "vilka" ;                n = Pl ; det = DDef Indef} ;

    forty_Numeral = {
      s = table {
        NCard _ => "fyrtio" ; 
        NOrd _  => "fyrtionde"
        } ; 
      n = Sg
      } ;

    in_Prep = {s = "i"} ;
    of_Prep = {s = "av"} ;

    and_Conj = {s = "och" ; n = Pl} ;
    either7or_DConj = {s1 = "antingen" ; s2 = "eller" ; n = Sg} ;

    if_Subj = ss "om" ;
    because_Subj = ss "eftersom" ;

    but_PConj = {s = "men"} ;
   
    please_Voc = {s = "," ++ "tack"} ;

    more_CAdv = ss "mera" ;
    less_CAdv = ss "mindre" ;

-- Auxiliaries that are used repeatedly.

  oper
    vem = mkNP "vem" "vem" "vems" "vems" "vems" SgUtr P3 ;

}
