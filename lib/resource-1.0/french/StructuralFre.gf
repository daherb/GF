concrete StructuralFre of Structural = CatFre ** 
  open PhonoFre, MorphoFre, ParadigmsFre, IrregFre, Prelude in {

  flags optimize=all ;

lin

  above_Prep = {s = ["au dessus"] ; c = MorphoFre.genitive ; isDir = False} ;
  after_Prep = mkPreposition "apr�s" ;
  all_Predet = {
    s = \\a,c => prepCase c ++ aagrForms "tout" "toute" "tous" "toutes" ! a ;
    c = Nom
    } ;
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
  everybody_NP = pn2np (mkPN ["tout le monde"] Masc) ;
  every_Det = {s = \\_,_ => "chaque" ; n = Sg} ;
  everything_NP = pn2np (mkPN ["tout"] Masc) ;
  everywhere_Adv = ss "partout" ;
  first_Ord = {s = \\ag => (regA "premier").s ! Posit ! AF ag.g ag.n} ;
  from_Prep = complGen ; ---
  he_Pron = 
    mkPronoun
      "il" (elision "l") "lui" "lui" "son" (elisPoss "s") "ses"
      Masc Sg P3 ;
  here7from_Adv = ss "d'ici" ;
  here7to_Adv = ss "ici" ;
  here_Adv = ss "ici" ;
  how_IAdv = ss "comment" ;
  how8many_IDet = {s = \\_,c => prepCase c ++ "combien" ++ elisDe ; n = Pl} ;
  if_Subj = ss elisSi ** {m = Indic} ;
  in8front_Prep = mkPreposition "devant" ;
  i_Pron = 
    mkPronoun
      (elision "j") (elision "m") (elision "m") "moi" "mon" (elisPoss "m") "mes"
      Fem Sg P1 ;
  in_Prep = mkPreposition "dans" ;
  it_Pron = 
    mkPronoun
      "il" (elision "l") "lui" "lui" "son" (elisPoss "s") "ses"
      Masc Sg P3 ;
  less_CAdv = ss "moins" ;
  many_Det = {s = \\_,c => prepCase c ++ "plusieurs" ; n = Pl} ;
  more_CAdv = ss "plus" ;
  most_Predet = {s = \\_,c => prepCase c ++ ["la plupart"] ; c = CPrep P_de} ;
  much_Det = {s = \\_,c => prepCase c ++ "beaucoup" ++ elisDe ; n = Pl} ;
  must_VV = mkVV (devoir_V2 ** {lock_V = <>}) ;
  no_Phr = ss "non" ;
  on_Prep = mkPreposition "sur" ;
  one_Quant = {s = \\g,c => prepCase c ++ genForms "un" "une" ! g} ;
  only_Predet = {s = \\_,c => prepCase c ++ "seulement" ; c = Nom} ; --- seul(e)(s)
  or_Conj = {s = "ou" ; n = Sg} ;
  otherwise_PConj = ss "autrement" ;
  part_Prep = complGen ;
  please_Voc = ss ["s'il vous pla�t"] ;
  possess_Prep = complGen ;
  quite_Adv = ss "assez" ;
  she_Pron = 
    mkPronoun
      "elle" elisLa "lui" "elle" "son" (elisPoss "s") "ses"
      Fem Sg P3 ;

  so_AdA = ss "si" ;
  somebody_NP = pn2np (mkPN ["quelqu'un"] Masc) ;
  somePl_Det = {s = \\_,c => prepCase c ++ "quelques" ; n = Pl} ;
  someSg_Det = {s = \\_,c => prepCase c ++ elision "quelqu" ; n = Sg} ;
  something_NP = pn2np (mkPN ["quelque chose"] Masc) ;
  somewhere_Adv = ss ["quelque part"] ; --- ne - pas
  that_Quant = {s = \\_ => 
    table {
      Sg => \\g,c => prepCase c ++ genForms "ce" "cette" ! g ;  ---- cet ; l�
      Pl => \\_,_ => "ces"
      }
    } ;
  that_NP = mkNP ["cela"] Masc Sg ;
  there7from_Adv = ss ["de l�"] ;
  there7to_Adv = ss "l�" ; --- y
  there_Adv = ss "l�" ;
  therefore_PConj = ss "donc" ;
  these_NP = mkNP ["celles-ci"] Fem Pl ;
  they_Pron = mkPronoun
    "elles" "les" "leur" "eux" "leur" "leur" "leurs"
    Fem Pl P3 ;
  this_Quant = {s = \\_ => 
    table {
      Sg => \\g,c => prepCase c ++ genForms "ce" "cette" ! g ;  ---- cet ; ci
      Pl => \\_,_ => "ces"
      }
    } ;
  this_NP = pn2np (mkPN ["ceci"] Masc) ;
  those_NP = mkNP ["celles-l�"] Fem Pl ;
  through_Prep = mkPreposition "par" ;
  too_AdA = ss "trop" ;
  to_Prep = complDat ;
  under_Prep = mkPreposition "sous" ;
  very_AdA = ss "tr�s" ;
  want_VV = mkVV (vouloir_V2 ** {lock_V = <>}) ;
  we_Pron = 
    mkPronoun "nous" "nous" "nous" "nous" "notre" "notre" "nos"
    Fem Pl P1 ;
  whatSg_IP = {s = \\c => prepCase c ++ "quoi" ; a = aagr Fem Sg} ;
  whatPl_IP = {s = \\c => prepCase c ++ "quoi" ; a = aagr Fem Pl} ;
  when_IAdv = ss "quand" ;
  when_Subj = ss "quand" ** {m = Indic} ;
  where_IAdv = ss "o�" ;
  whichPl_IDet = {s = \\g,c => prepCase c ++ genForms "quel" "quelle" ! g ; n = Sg} ;
  whichSg_IDet = {s = \\g,c => prepCase c ++ genForms "quels" "quelles" ! g; n = Pl} ;
  whoPl_IP = {s = \\c => prepCase c ++ "qui" ; a = aagr Fem Pl} ;
  whoSg_IP = {s = \\c => prepCase c ++ "qui" ; a = aagr Fem Sg} ;
  why_IAdv = ss "pourquoi" ;
  without_Prep = mkPreposition "sans" ;
  with_Prep = mkPreposition "avec" ;
  yes_Phr = ss "oui" ; --- si
  youSg_Pron = mkPronoun 
    "tu" (elision "t") (elision "t") "toi" "ton" (elisPoss "t") "tes"
    Fem Sg P2 ;
  youPl_Pron, youPol_Pron = 
    mkPronoun
      "vous" "vous" "vous" "vous" "votre" "votre" "vos"
       Fem Pl P2 ;

}

