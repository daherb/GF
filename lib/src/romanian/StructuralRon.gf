--# -path=.:../abstract:../romance:../common:prelude

concrete StructuralRon of Structural = CatRon ** 
  open  MorphoRon, ParadigmsRon, BeschRon, Prelude,(X = ConstructX) in {

  flags optimize=all ; 
           --coding=utf8 ;

lin

  above_Prep = mkPrep "deasupra" Ge ;
  after_Prep = mkPrep "dup�" Ac True;
  all_Predet = {
    s = \\a => table { AGenDat => aagrForms nonExist nonExist "tuturor" "tuturor" ! a ;
                       _       => aagrForms "tot" "toat�" "to�i" "toate" ! a 
                     };
    c = No
    } ;
  almost_AdA, almost_AdN = ss "aproape" ;
  always_AdV = ss "mereu" ;
  although_Subj = ss "de�i" ;
  and_Conj = {s1 = [] ; s2 = "�i" ; n = Pl} ;
  because_Subj = ss "deoarece" ;
  before_Prep = mkPrep "�naintea" Ge ;
  behind_Prep = mkPrep "�napoia" Ge ;
  between_Prep = mkPrep "�ntre" Ac True ;
  both7and_DConj = {s1,s2 = "�i" ; n = Pl} ;
  but_PConj = ss "dar" ;
  by8agent_Prep = mkPrep "de c�tre" Ac True;
  by8means_Prep = mkPrep "de" Ac True;
  can8know_VV = mkVV (v_besch68 "putea") ;
  can_VV = mkVV (v_besch68 "putea") ;
  during_Prep = mkPrep "�n timpul" Ge ;
  either7or_DConj = {s1,s2 = "sau" ; n = Pl} ;
  everybody_NP = mkNP "to�i" "tuturor" Pl Masc True; -- form for Fem needed also !
  every_Det = mkDet "orice" "orice" "oric�rui" "oric�rei" "orice" "orice" "oric�ruia" "oric�reia" Sg ; 
  everything_NP = mkNP "totul" nonExist Sg Masc False;
  everywhere_Adv = ss "pretutindeni" ;
  few_Det  = mkDet "c��iva" "c�teva" "c�torva" "c�torva" Pl ;
  for_Prep = mkPrep "pentru" Ac True;
  from_Prep = mkPrep "de la" Ac True; 
  
  he_Pron = 
    mkPronoun
      "el" "el" "lui" "lui" [] "s�u" "sa" "s�i" "sale"  Masc Sg P3 ;
  
  here7from_Adv = ss "de aici" ;
  here7to_Adv = ss "p�n� aici" ;
  here_Adv = ss "aici" ;
  how_IAdv = ss "cum" ;
  how8many_IDet = {s = \\g,c => case <g,c> of
                                   { <Fem,AGenDat> => "c�tor"; <Fem,_> => "c�te" ;
                                     <Masc,AGenDat> => "c�tor" ; _ => "c��i" 
                                     };
                   n = Pl
                    } ;
  if_Subj = ss "dac�" ;
  in8front_Prep = mkPrep "�n fa�a" Ge ;
  i_Pron = mkPronoun "eu" "mine" "mie" [] [] "meu" "mea" "mei" "mele" Masc Sg P1 ;
  in_Prep = mkPrep "�n" Ac True;
  it_Pron = 
     mkPronoun
      "" "el" "lui" "lui" [] "s�u" "sa" "s�i" "sale"  Masc Sg P3 ;
  
  have_V2 = dirV2 (v_have) ;
  less_CAdv = {s = "mai pu�in" ; sNum = ""; p = conjThan ; lock_CAdv = <> } ; 
  many_Det = mkDet "mul�i" "multe" "multor" "multor" "mul�i" "multe" "multora" "multora" Pl; 
  more_CAdv = {s = "mai" ; sNum = "mult" ; p =conjThan ; lock_CAdv = <>};
  most_Predet = {
    s = \\a => table { AGenDat => "marii par�i a" ;
                       ANomAcc => "marea parte a"; 
                       AVoc    => "mare parte a"
                     };
    c = Ge
    };
  much_Det = mkDet "mult" "mult�" nonExist nonExist Sg ;
  must_VV = mkVV (v_besch140 "trebui") ;
  no_Utt = ss "nu" ;
  on_Prep = mkPrep "pe" Ac True;
  only_Predet = {s = \\_,c => "doar" ; c = No} ; 
  or_Conj = {s1 = [] ; s2 = "sau" ; n = Sg} ;
  otherwise_PConj = ss "altfel" ;
  part_Prep = mkPrep "din" Ac True;
  please_Voc = ss ["v� rog"] ;
  possess_Prep = mkPrep "" Ge ; -- required forms for Fem Sg, Masc Pl and Fem Pl - maybe variants
  quite_Adv = ss "chiar" ;
  she_Pron = 
    mkPronoun
       "ea" "ea" "ei" "ei" [] "s�u" "sa" "s�i" "sale"  
        Fem Sg P3 ;

  so_AdA = ss "a�a" ;
  somebody_NP = mkNP "cineva" "cuiva" Sg Masc True;
somePl_Det = mkDet "unii" "unele" "unor" "unor" "unii" "unele" "unora" "unora" Pl ;
someSg_Det = mkDet "ni�te" "ni�te" "la ni�te" "la ni�te" Sg ;
  something_NP = mkNP "ceva" "a ceva" Sg Masc False;
  somewhere_Adv = ss ["undeva"] ; --- ne - pas

that_Quant = {
    s = \\_ => table {
      Sg => table {Masc => table { AGenDat => "acelui";
                                   _       => "acel"
                                 };
                   Fem  => table {AGenDat => "acelei";
                                  _       => "acea"
                                 }
                  };
      Pl => table { Masc => table {AGenDat => "acelor";
                                   _       => "acei" 
                                  };
                    Fem  => table {AGenDat => "acelor";
                                   _       => "acele" 
                                  }
                   }
                      } ;
    sp = table { 
      Sg => table {Masc => table { AGenDat => "aceluia";
                                   _       => "acela"
                                 };
                   Fem  => table {AGenDat => "aceleia";
                                  _       => "aceea"
                                 }
                  };
      Pl => table {Masc => table {AGenDat => "acelora";
                                  _       => "aceia" 
                                  };
                   Fem  => table {AGenDat => "acelora";
                                  _       => "acelea" 
                                 }
                  }
              }; 
  isDef = False ; isPost = False ; hasRef = False
};

  there7from_Adv = ss ["de acolo"] ;
  there7to_Adv = ss "p�n� acolo" ; 
  there_Adv = ss "acolo" ;
  therefore_PConj = ss "astfel" ;
  --these_NP = mkNP "ace�tia" "acestora" Masc Pl True; --form for Fem needed also !
  they_Pron = mkPronoun
      "ei" "ei" "lor" "lor" [] "lor" "lor" "lor" "lor"  
        Masc Pl P3 ;
  this_Quant = {
    s = \\_ => table {
      Sg => table {Masc => table { AGenDat => "acestui";
                                   _       => "acest"
                                 };
                   Fem  => table {AGenDat => "acestei";
                                  _       => "aceast�"
                                 }
                  };
      Pl => table { Masc => table {AGenDat => "acestor";
                                   _       => "ace�ti" 
                                  };
                    Fem  => table {AGenDat => "acestor";
                                   _       => "aceste" 
                                  }
                   }
                      } ;
    sp = table { 
      Sg => table {Masc => table { AGenDat => "acestuia";
                                   _       => "acesta"
                                 };
                   Fem  => table {AGenDat => "acesteia";
                                  _       => "aceasta"
                                 }
                  };
      Pl => table {Masc => table {AGenDat => "acestora";
                                  _       => "ace�tia" 
                                  };
                   Fem  => table {AGenDat => "acestora";
                                  _       => "acestea" 
                                 }
                  }
              } ;
   isDef = False ; isPost = False ; hasRef = False
 };
  through_Prep = mkPrep "prin" Ac True;
  too_AdA = ss "prea" ;
  to_Prep = mkPrep "la" Ac True;
  under_Prep = mkPrep "sub" Ac True;
  very_AdA = ss "foarte" ;
  want_VV = mkVV (v_besch74 "vrea") ; 
  we_Pron =  mkPronoun
    "noi" "noi" "nou�" [] [] "nostru" "noastr�" "no�tri" "noastre"  
        Masc Pl P1 ; 
whatSg_IP = 
    {s = \\c => case c of
                { Da => "c�ruia"  ;
                  Ge => "a c�ruia" ; 
                  _      => "ce" };
     a = aagr Masc Sg;
     hasRef = False
    };

whatPl_IP = 
   {s = \\c => case c of
                { Da => "c�rora" ;
                  Ge => "a c�rora" ; 
                  _      => "ce" };
     a = aagr Masc Pl;
     hasRef = False
    };
  when_IAdv = ss "c�nd" ;
  when_Subj = ss "c�nd" ;
  where_IAdv = ss "unde" ;
  which_IQuant = {s = table {
      Sg => table {Masc => table { AGenDat => "c�rui";
                                   _       => "care"
                                 };
                   Fem  => table {AGenDat => "c�rei";
                                  _       => "care"
                                 }
                  };
      Pl => \\g => table {AGenDat => "c�ror";
                                   _       => "care" 
                                  }
                   
                    };
   isDef = False 
  };

  whoPl_IP = {s = \\c => case c of
                { Da => "cui" ;
                  Ge => "a cui" ; 
                  _      => "cine" };
     a = aagr Masc Pl;
     hasRef = True
    };

  whoSg_IP = {s = \\c => case c of
                { Da => "cui" ;
                  Ge => "a cui" ; 
                  _      => "cine" };
     a = aagr Masc Sg;
     hasRef = True
    };
  why_IAdv = ss "de ce" ;
  without_Prep = mkPrep "f�r�" Ac True;
  with_Prep = mkPrep "cu" Ac ;
  yes_Utt = ss "da" ; 

  youSg_Pron = mkPronoun 
    "tu" "tine" "�ie" [] "tu" "t�u" "ta" "t�i" "tale"  
        Masc Sg P2 ;
  youPl_Pron, youPol_Pron = 
    mkPronoun
      "voi" "voi" "vou�" [] "voi" "vostru" "voastr�" "vo�tri" "voastre"  
         Masc Pl P2 ;

 not_Predet = {s = \\a,c => "nu" ; c = No} ;

  no_Quant = 
{
    s = \\_ => table {
      Sg => table {Masc => table { AGenDat => "niciunui";
                                   _       => "niciun"
                                 };
                   Fem  => table {AGenDat => "niciunei";
                                  _       => "nicio"
                                 }
                  };
      Pl => table { Masc => table {AGenDat => "niciunor";
                                   _       => "niciunii" 
                                  };
                    Fem  => table {AGenDat => "niciunor";
                                   _       => "niciunele" 
                                  }
                   }
                      } ;
    sp = table { 
      Sg => table {Masc => table { AGenDat => "nim�nui";
                                   _       => "nimeni"
                                 };
                   Fem  => table {AGenDat => "nim�nui";
                                  _       => "nimeni"
                                 }
                  };
      Pl => table {Masc => table {AGenDat => "niciunora";
                                  _       => "niciunii" 
                                  };
                   Fem  => table {AGenDat => "niciunora";
                                  _       => "niciunele" 
                                 }
                  }
              } ;
 isDef = False ; isPost = False ; hasRef = False
};
  if_then_Conj = {s1 = "dac�" ; s2 = "atunci" ; n = Sg ; lock_Conj = <>} ;
  nobody_NP = mkNP "nimeni" "nim�nui" Sg Masc True;
 
  nothing_NP = mkNP "nimic" "nimicului" Sg Masc False;
  at_least_AdN = ss "cel pu�in" ;
  at_most_AdN = ss "cel mult" ;

  except_Prep = mkPrep "cu excep�ia" Ge ;

  as_CAdv = { s = "la fel de"; sNum = "mult"; p = "ca" ; lock_CAdv = <> };

}

