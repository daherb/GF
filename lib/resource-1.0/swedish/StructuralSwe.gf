concrete StructuralSwe of Structural = CatSwe ** 
  open MorphoSwe, ParadigmsSwe, Prelude in {

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
    mkV "kunna" "kan" "kunn" "kunde" "kunnat" "kunnen" **
    {c2 = [] ; lock_VV = <>} ;
  during_Prep = ss "under" ;
  either7or_DConj = sd2 "antingen" "eller" ** {n = Sg} ;
  everybody_NP = regNP "alla" "allas" Plg ;
  every_Det = {s = \\_,_ => "varje" ; n = Sg ; det = DDef Indef} ;
  everything_NP = regNP "allting" "alltings" SgNeutr ;
  everywhere_Adv = ss "�verallt" ;
  few_Det  = {s = \\_,_ => "f�" ; n = Pl ; det = DDef Indef} ;
  first_Ord = {s = "f�rsta" ; isDet = True} ;
  from_Prep = ss "fr�n" ;
  he_Pron = MorphoSwe.mkNP "han"  "honom"  "hans" "hans" "hans"  SgUtr P3 ;
  here_Adv = ss "h�r" ;
  here7to_Adv = ss "hit" ;
  here7from_Adv = ss "h�rifr�n" ;
  how_IAdv = ss "hur" ;
  how8many_IDet = {s = \\_ => ["hur m�nga"] ; n = Pl ; det = DDef Indef} ;
  if_Subj = ss "om" ;
  in8front_Prep = ss "framf�r" ;
  i_Pron = MorphoSwe.mkNP "jag"  "mig"  "min" "mitt" "mina"  SgUtr P1 ;
  in_Prep = ss "i" ;
  it_Pron = MorphoSwe.regNP "det" "dess" SgNeutr ;
  less_CAdv = ss "mindre" ;
  many_Det = {s = \\_,_ => "m�nga" ; n = Pl ; det = DDef Indef} ;
  more_CAdv = ss "mer" ;
  most_Predet = {s = gennumForms ["den mesta"] ["det mesta"] ["de flesta"]} ;
  much_Det = {s = \\_,_ => "mycket" ; n = Pl ; det = DDef Indef} ;
  must_VV = 
    mkV "f�" "m�ste" "f�" "fick" "m�st" "m�st" ** {c2 = [] ; lock_VV = <>} ;
  no_Phr = ss ["nej"] ;
  on_Prep = ss "p�" ;
  one_Quant = {s = \\_ => genderForms ["en"] ["ett"] ; n = Sg ; det = DIndef} ;
  only_Predet = {s = \\_ => "bara"} ;
  or_Conj = ss "eller" ** {n = Sg} ;
  otherwise_PConj = ss "annars" ;
  part_Prep = ss "av" ;
  please_Voc = ss "tack" ; ---
  possess_Prep = ss "av" ;
  quite_Adv = ss "ganska" ;
  she_Pron = MorphoSwe.mkNP "hon" "henne" "hennes" "hennes" "hennes"  SgUtr P3 ;
  so_AdA = ss "s�" ;
  someSg_Det = {s = \\_ => genderForms "n�gon" "n�got" ; n = Sg ; det = DIndef} ;
  somePl_Det = {s = \\_,_ => "n�gra" ; n = Pl ; det = DIndef} ;
  somebody_NP = regNP "n�gon" "n�gons" SgUtr ;
  something_NP = regNP "n�got" "n�gots" SgNeutr ;
  somewhere_Adv = ss "n�gonstans" ;
  that_Quant = 
    {s = table {
       Sg => \\_ => genderForms ["den d�r"] ["det d�r"] ; 
       Pl => \\_,_ => ["de d�r"]
       } ;
     det = DDef Def
    } ;
  that_NP = regNP ["det d�r"] ["det d�rs"] SgNeutr ;
  there_Adv = ss "d�r" ;
  there7to_Adv = ss "dit" ;
  there7from_Adv = ss "d�rifr�n" ;
  therefore_PConj = ss "d�rf�r" ;
  these_NP = regNP ["de h�r"] ["det h�rs"] Plg ;
  they_Pron = MorphoSwe.mkNP "de" "dem" "deras" "deras" "deras" Plg P1 ;
  this_Quant = 
    {s = table {
       Sg => \\_ => genderForms ["den h�r"] ["det h�r"] ; 
       Pl => \\_,_ => ["de h�r"]
       } ;
     det = DDef Def
    } ;
  this_NP = regNP ["det h�r"] ["det h�rs"] SgNeutr ;
  those_NP = regNP ["de d�r"] ["det d�rs"] Plg ;
  through_Prep = ss "genom" ;
  too_AdA = ss "f�r" ;
  to_Prep = ss "till" ;
  under_Prep = ss "under" ;
  very_AdA = ss "mycket" ;
  want_VV = 
    mkV "vilja" "vill" "vilj" "ville" "velat" "velad" ** 
    {c2 = [] ; lock_VV = <>} ;
  we_Pron = MorphoSwe.mkNP "vi"  "oss"  "v�r" "v�rt" "v�ra"  Plg P1 ;
  whatSg_IP = {s = \\_ => "vad" ; gn = SgUtr} ; ---- infl
  whatPl_IP = {s = \\_ => "vad" ; gn = Plg} ; ---- infl
  when_IAdv = ss "n�r" ;
  when_Subj = ss "n�r" ;
  where_IAdv = ss "var" ;
  whichPl_IDet = {s = \\_ => "vilka" ; n = Pl ; det = DIndef} ;
  whichSg_IDet = {s = genderForms "vilken" "vilket" ; n = Sg ; det = DIndef} ;
  whoSg_IP = {s = vem.s ; gn = SgUtr} ;
  whoPl_IP = {s = vem.s ; gn = Plg} ;
  why_IAdv = ss "varf�r" ;
  without_Prep = ss "utan" ;
  with_Prep = ss "med" ;
  yes_Phr = ss ["ja"] ;
  youSg_Pron = MorphoSwe.mkNP "du" "dig" "din" "ditt" "dina" SgUtr P2 ;
  youPl_Pron = MorphoSwe.mkNP "ni" "er" "er" "ert" "era"  Plg P2 ;
  youPol_Pron = MorphoSwe.mkNP "ni" "er" "er" "ert" "era"  SgUtr P2 ; --- wrong in refl

-- Auxiliaries that are used repeatedly.

  oper
    vem = MorphoSwe.mkNP "vem" "vem" "vems" "vems" "vems" SgUtr P3 ;

}

