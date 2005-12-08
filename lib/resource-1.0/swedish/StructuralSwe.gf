concrete StructuralSwe of Structural = CatSwe ** 
  open MorphoSwe, Prelude in {

  flags optimize=all ;

  lin
  above_Prep = ss "ovanf�r" ;
  after_Prep = ss "efter" ;
  by8agent_Prep = ss "av" ;
  all_Predet = {s = gennumForms "all" "allt" "alla"} ;
  almost_AdA, almost_AdN = ss "n�stan" ;
  although_Subj = ss "fast" ;
  always_AdV = ss "alltid" ;
  and_Conj = ss "och" ** {n = Pl} ;
  because_Subj = ss "eftersom" ;
  before_Prep = ss "f�re" ;
  behind_Prep = ss "bakom" ;
  between_Prep = ss "mellan" ;
  both7and_DConj = sd2 "b�de" "och" ** {n = Pl} ;
  but_PConj = ss "men" ;
  by8means_Prep = ss "med" ;
  can8know_VV, can_VV = 
    mkVerb6 "kunna" "kan" "kunn" "kunde" "kunnat" "kunnen" **
    {c2 = [] ; lock_VV = <>} ;
  during_Prep = ss "under" ;
  either7or_DConj = sd2 "antingen" "eller" ** {n = Sg} ;
  everybody_NP = regNP "alla" "allas" Plg ;
  every_Det = {s = \\_ => "varje" ; n = Sg ; det = DDef Indef} ;
  everything_NP = regNP "allting" "alltings" SgNeutr ;
  everywhere_Adv = ss "�verallt" ;
  from_Prep = ss "fr�n" ;
  he_Pron = mkNP "han"  "honom"  "hans" "hans" "hans"  SgUtr P3 ;
  here_Adv = ss "h�r" ;
  here7to_Adv = ss "hit" ;
  here7from_Adv = ss "h�rifr�n" ;
  how_IAdv = ss "hur" ;
  how8many_IDet = {s = \\_ => ["hur m�nga"] ; n = Pl ; det = DDef Indef} ;
  if_Subj = ss "om" ;
  in8front_Prep = ss "framf�r" ;
  i_Pron = mkNP "jag"  "mig"  "min" "mitt" "mina"  SgUtr P1 ;
  in_Prep = ss "i" ;
  it_Pron = regNP "det" "dess" SgNeutr ;
  less_CAdv = ss "mindre" ;
  many_Det = {s = \\_ => "m�nga" ; n = Pl ; det = DDef Indef} ;
  more_CAdv = ss "mer" ;
  most_Predet = {s = gennumForms ["den mesta"] ["det mesta"] ["de flesta"]} ;
  much_Det = {s = \\_ => "mycket" ; n = Pl ; det = DDef Indef} ;
  must_VV = 
    mkVerb6 "f�" "m�ste" "f�" "fick" "m�st" "m�st" ** {c2 = [] ; lock_VV = <>} ;
  no_Phr = ss ["Nej"] ;
  on_Prep = ss "p�" ;
  only_Predet = {s = \\_ => "bara"} ;
  or_Conj = ss "eller" ** {n = Sg} ;
  otherwise_PConj = ss "annars" ;
  part_Prep = ss "av" ;
  please_Voc = ss "tack" ; ---
  possess_Prep = ss "av" ;
  quite_Adv = ss "ganska" ;
  she_Pron = mkNP "hon" "henne" "hennes" "hennes" "hennes"  SgUtr P3 ;
  so_AdA = ss "s�" ;
  someSg_Det = {s = genderForms "n�gon" "n�got" ; n = Sg ; det = DDef Indef} ;
  somePl_Det = {s = \\_ => "n�gra" ; n = Pl ; det = DDef Indef} ;
  somebody_NP = regNP "n�gon" "n�gons" SgUtr ;
  something_NP = regNP "n�got" "n�gots" SgNeutr ;
  somewhere_Adv = ss "n�gonstans" ;
  that_Quant = {s = genderForms ["den d�r"] ["det d�r"] ; n = Sg ; det = DDef Def} ;
  that_NP = regNP ["det d�r"] ["det d�rs"] SgNeutr ;
  there_Adv = ss "d�r" ;
  there7to_Adv = ss "dit" ;
  there7from_Adv = ss "d�rifr�n" ;
  therefore_PConj = ss "d�rf�r" ;
  these_NP = regNP ["de h�r"] ["det h�rs"] Plg ;
  these_Quant = {s = \\_ => ["de h�r"] ; n = Pl ; det = DDef Def} ;
  they_Pron = mkNP "de" "dem" "deras" "deras" "deras" Plg P1 ;
  this_Quant = {s = genderForms ["den h�r"] ["det h�r"] ; n = Sg ; det = DDef Def} ;
  this_NP = regNP ["det h�r"] ["det h�rs"] SgNeutr ;
  those_NP = regNP ["de d�r"] ["det d�rs"] Plg ;
  those_Quant = {s = \\_ => ["de d�r"] ; n = Pl ; det = DDef Def} ;
  thou_Pron = mkNP "du" "dig" "din" "ditt" "dina" SgUtr P2 ;
  through_Prep = ss "genom" ;
  too_AdA = ss "f�r" ;
  to_Prep = ss "till" ;
  under_Prep = ss "under" ;
  very_AdA = ss "mycket" ;
  want_VV = 
    mkVerb6 "vilja" "vill" "vilj" "ville" "velat" "velad" ** 
    {c2 = [] ; lock_VV = <>} ;
  we_Pron = mkNP "vi"  "oss"  "v�r" "v�rt" "v�ra"  Plg P1 ;
----  whatPl_IP = intPronWhat plural ;
----  whatSg_IP = intPronWhat singular ;
  when_IAdv = ss "n�r" ;
  when_Subj = ss "n�r" ;
  where_IAdv = ss "var" ;
----  whichPl_IDet = vilkenDet ;
----  whichSg_IDet = mkDeterminerPl "vilka" IndefP ;
  whoSg_IP = {s = vem.s ; gn = SgUtr} ;
  whoPl_IP = {s = vem.s ; gn = Plg} ;
  why_IAdv = ss "varf�r" ;
  without_Prep = ss "utan" ;
  with_Prep = ss "med" ;
  ye_Pron = mkNP "ni" "er" "er" "ert" "era"  Plg P2 ;
  yes_Phr = ss ["ja"] ;
  you_Pron = mkNP "ni" "er" "er" "ert" "era"  SgUtr P2 ; --- wrong in refl

-- Auxiliaries that are used repeatedly.

  oper
    vem = mkNP "vem" "vem" "vems" "vems" "vems" SgUtr P3 ;

}

