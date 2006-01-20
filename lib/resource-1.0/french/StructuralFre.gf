concrete StructuralFre of Structural = CatFre ** 
  open PhonoFre, MorphoFre, ParadigmsFre, VerbsFre, Prelude in {

  flags optimize=all ;

lin

  above_Prep = {s = ["au dessus"] ; c = genitive ; isDir = False} ;
  after_Prep = mkPreposition "apr�s" ;
  all_Predet = {s = aagrForms "tout" "toute" "tous" "toutes"} ;
  almost_AdA, almost_AdN = ss "presque" ;
  always_AdV = ss "toujours" ;
  although_Subj = ss ("bien" ++ elisQue) ** {m = Conjunct} ;
  and_Conj = ss "et" ** {n = Pl} ;
  because_Subj = ss ("parce" ++ elisQue) ** {m = Indic} ;
  before_Prep = mkPreposition "avant" ;
  behind_Prep = mkPreposition "derri�re" ;
  between_Prep = mkPreposition "entre" ;
  both7and_DConj = {s1,s2 = "et" ; n = Pl} ;
  but_PConj = ss "mais" ;
  by8agent_Prep = mkPreposition "par" ;
  by8means_Prep = mkPreposition "par" ;
  can8know_VV = mkVV (savoir_V2 ** {lock_V = <>}) ;
  can_VV = mkVV pouvoir_V ;
  during_Prep = mkPreposition "pendant" ;
  either7or_DConj = {s1,s2 = "ou" ; n = Pl} ;
--  everybody_NP = mkNameNounPhrase ["tout le monde"] Masc ;
  every_Det = {s = \\_,_ => "chaque" ; n = Sg} ;
--  everything_NP = mkNameNounPhrase ["tout"] Masc ;
  everywhere_Adv = ss "partout" ;
  first_Ord = {s = \\ag => (regA "premier").s ! Posit ! AF ag.g ag.n} ;
  from_Prep = complGen ; ---
  he_Pron = 
    mkPronoun
      "il" (elision "l") "lui" "lui" "son" (elisPoss "s") "ses"
      Masc Sg P3 Clit2 ;
  here7from_Adv = ss "d'ici" ;
  here7to_Adv = ss "ici" ;
  here_Adv = ss "ici" ;
  how_IAdv = ss "comment" ;
  how8many_IDet = {s = \\_ => "combien" ++ elisDe ; n = Pl} ;
  if_Subj = ss elisSi ** {m = Indic} ;
  in8front_Prep = mkPreposition "devant" ;
  i_Pron = 
    mkPronoun
      (elision "j") (elision "m") (elision "m") "moi" "mon" (elisPoss "m") "mes"
      Fem Sg P1 Clit1 ;
  in_Prep = mkPreposition "dans" ;
  it_Pron = 
    mkPronoun
      "il" (elision "l") "lui" "lui" "son" (elisPoss "s") "ses"
      Masc Sg P3 Clit2 ;
  less_CAdv = ss "moins" ;
--  many_Det = mkDeterminer1 plural "plusieurs" ;
--  most8many_Det = plupartDet ;
--  most_Det = mkDeterminer1 singular (["la plupart"] ++ elisDe) ; --- de
--  much_Det = mkDeterminer1 singular ("beaucoup" ++ elisDe) ; --- de
  must_VV = mkVV (devoir_V2 ** {lock_V = <>}) ;
  no_Phr = ss "non" ; --- and also Si!
  on_Prep = mkPreposition "sur" ;
  one_Quant = {s = \\g,c => prepCase c ++ genForms "un" "une" ! g} ;
  only_Predet = {s = \\_ => "seulement"} ; --- seul(e)(s)
  or_Conj = {s = "ou" ; n = Sg} ;
  otherwise_PConj = ss "autrement" ;
  part_Prep = complGen ;
  possess_Prep = complGen ;
  quite_Adv = ss "assez" ;
  she_Pron = 
    mkPronoun
      "elle" elisLa "lui" "elle" "son" (elisPoss "s") "ses"
      Fem Sg P3 Clit2 ;

  so_AdA = ss "si" ;
--  somebody_NP = mkNameNounPhrase ["quelqu'un"] Masc ;
--  some_Det = mkDeterminer1 singular "quelque" ;
--  some_NDet = mkDeterminerNum "quelques" "quelques" ;
--  something_NP = mkNameNounPhrase ["quelque chose"] Masc ;
  somewhere_Adv = ss ["quelque part"] ; --- ne - pas
  that_Quant = {s = \\g,c => prepCase c ++ genForms "ce" "cette" ! g} ; ---- cet
  that_NP = pn2np (mkPN ["ceci"] Masc) ;
  there7from_Adv = ss ["de l�"] ;
  there7to_Adv = ss "l�" ; --- y
  there_Adv = ss "l�" ;
  therefore_PConj = ss "donc" ;
--  these_NDet = mkDeterminerNum "ces" "ces" ; --- ci
--  they_Pron = pronNounPhrase pronIls ;
--  they8fem_Pron = pronNounPhrase pronElles ;
  this_Quant = {s = \\g,c => prepCase c ++ genForms "ce" "cette" ! g} ; ---- cet
  this_NP = pn2np (mkPN ["ceci"] Masc) ;
--  those_NDet = mkDeterminerNum "ces" "ces" ; --- l�
  thou_Pron = mkPronoun 
    "tu" (elision "t") (elision "t") "toi" "ton" (elisPoss "t") "tes"
    Fem Sg P2 Clit1 ;
  through_Prep = mkPreposition "par" ;
  too_AdA = ss "trop" ;
  to_Prep = complDat ;
  under_Prep = mkPreposition "sous" ;
  very_AdA = ss "tr�s" ;
  want_VV = mkVV (vouloir_V2 ** {lock_V = <>}) ;
  we_Pron = 
    mkPronoun "nous" "nous" "nous" "nous" "notre" "notre" "nos"
    Fem Pl P1 Clit3 ;
  whatSg_IP = {s = \\c => prepCase c ++ "quoi" ; a = aagr Fem Sg} ;
  whatPl_IP = {s = \\c => prepCase c ++ "quoi" ; a = aagr Fem Pl} ;
  when_IAdv = ss "quand" ;
  when_Subj = ss "quand" ** {m = Indic} ;
  where_IAdv = ss "o�" ;
--  which8many_IDet = mkDeterminerNum "quels" "quelles" ** {n = Pl} ;
--  which8one_IDet = quelDet ;
  whoSg_IP = {s = \\c => prepCase c ++ "qui" ; a = aagr Fem Sg} ;
  whoPl_IP = {s = \\c => prepCase c ++ "qui" ; a = aagr Fem Pl} ;
  why_IAdv = ss "pourquoi" ;
  without_Prep = mkPreposition "sans" ;
  with_Prep = mkPreposition "avec" ;
  ye_Pron, you_Pron = 
    mkPronoun
      "vous" "vous" "vous" "vous" "votre" "votre" "vos"
       Fem Pl P2 Clit3 ;
  yes_Phr = ss "oui" ; --- si

}


{-
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
  every_Det = {s = \\_,_ => "varje" ; n = Sg ; det = DDef Indef} ;
  everything_NP = regNP "allting" "alltings" SgNeutr ;
  everywhere_Adv = ss "�verallt" ;
  first_Ord = {s = "f�rsta" ; isDet = True} ;
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
  many_Det = {s = \\_,_ => "m�nga" ; n = Pl ; det = DDef Indef} ;
  more_CAdv = ss "mer" ;
  most_Predet = {s = gennumForms ["den mesta"] ["det mesta"] ["de flesta"]} ;
  much_Det = {s = \\_,_ => "mycket" ; n = Pl ; det = DDef Indef} ;
  must_VV = 
    mkVerb6 "f�" "m�ste" "f�" "fick" "m�st" "m�st" ** {c2 = [] ; lock_VV = <>} ;
  no_Phr = ss ["Nej"] ;
  on_Prep = ss "p�" ;
  one_Quant = {s = \\_ => genderForms ["en"] ["ett"] ; n = Sg ; det = DIndef} ;
  only_Predet = {s = \\_ => "bara"} ;
  or_Conj = ss "eller" ** {n = Sg} ;
  otherwise_PConj = ss "annars" ;
  part_Prep = ss "av" ;
  please_Voc = ss "tack" ; ---
  possess_Prep = ss "av" ;
  quite_Adv = ss "ganska" ;
  she_Pron = mkNP "hon" "henne" "hennes" "hennes" "hennes"  SgUtr P3 ;
  so_AdA = ss "s�" ;
  someSg_Det = {s = \\_ => genderForms "n�gon" "n�got" ; n = Sg ; det = DIndef} ;
  somePl_Det = {s = \\_,_ => "n�gra" ; n = Pl ; det = DIndef} ;
  somebody_NP = regNP "n�gon" "n�gons" SgUtr ;
  something_NP = regNP "n�got" "n�gots" SgNeutr ;
  somewhere_Adv = ss "n�gonstans" ;
  that_Quant = 
    {s = \\_ => genderForms ["den d�r"] ["det d�r"] ; n = Sg ; det = DDef Def} ;
  that_NP = regNP ["det d�r"] ["det d�rs"] SgNeutr ;
  there_Adv = ss "d�r" ;
  there7to_Adv = ss "dit" ;
  there7from_Adv = ss "d�rifr�n" ;
  therefore_PConj = ss "d�rf�r" ;
  these_NP = regNP ["de h�r"] ["det h�rs"] Plg ;
  these_Quant = {s = \\_,_ => ["de h�r"] ; n = Pl ; det = DDef Def} ;
  they_Pron = mkNP "de" "dem" "deras" "deras" "deras" Plg P1 ;
  this_Quant = 
    {s = \\_ => genderForms ["den h�r"] ["det h�r"] ; n = Sg ; det = DDef Def} ;
  this_NP = regNP ["det h�r"] ["det h�rs"] SgNeutr ;
  those_NP = regNP ["de d�r"] ["det d�rs"] Plg ;
  those_Quant = {s = \\_,_ => ["de d�r"] ; n = Pl ; det = DDef Def} ;
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
  ye_Pron = mkNP "ni" "er" "er" "ert" "era"  Plg P2 ;
  yes_Phr = ss ["ja"] ;
  you_Pron = mkNP "ni" "er" "er" "ert" "era"  SgUtr P2 ; --- wrong in refl

-- Auxiliaries that are used repeatedly.

  oper
    vem = mkNP "vem" "vem" "vems" "vems" "vems" SgUtr P3 ;

}

-}
