concrete StructuralLat of Structural = CatLat ** 
  open ResLat, (P = ParadigmsLat), Prelude, IrregLat in 
  {

  flags optimize=all ;

  lin
  above_Prep = mkPrep "super" Abl ; -- abl. L...
  after_Prep = mkPrep "post" Acc ; -- acc. L...
  all_Predet = ss "cuncti" ; -- L...
  almost_AdA, almost_AdN = ss "quasi" ; -- L...
  although_Subj = ss "quamquam" ; -- L...
  always_AdV = ss "semper" ; -- L...
  and_Conj = sd2 [] "et" ** {n = Pl} ;
-----b  and_Conj = ss "and" ** {n = Pl} ;
  because_Subj = ss "cum" ; -- L...
  before_Prep = mkPrep "ante" Acc ; -- acc. L...
  behind_Prep = mkPrep "behind" Acc ; -- acc. L...
  between_Prep = mkPrep "inter" Acc ; -- acc. L...
  both7and_DConj = sd2 "et" "et" ** {n = Pl} ; --L...
  but_PConj = ss "sed" ; -- L...
  by8agent_Prep = mkPrep "per" Abl ; -- L...
  by8means_Prep = Abl_Prep ; -- L...
  can8know_VV, can_VV = IrregLat.can_irreg_VV ; --L...
  during_Prep = mkPrep "inter" Acc ; -- L...
  either7or_DConj = sd2 "aut" "aut" ** {n = Sg} ; -- L...
--  everybody_NP = regNP "quisquae" Sg ; -- L...
--  every_Det = mkDeterminer Sg "omnis" ; -- Pons
--  everything_NP = regNP "omnia" Pl ; -- L...
  everywhere_Adv = ss "ubique" ; -- L...
--  few_Det = mkDeterminer Pl "paulum" ; -- L...
-----  first_Ord = ss "first" ; DEPRECATED
  for_Prep = mkPrep "pro" Abl ; -- abl. L...
  from_Prep = mkPrep "de" Abl ; -- abl. L...
  he_Pron = mkPronoun Masc Sg P3 ;
  here_Adv = ss "hic" ; -- L...
  here7to_Adv = ss "huc" ; -- L...
  here7from_Adv = ss "hinc" ; -- L...
  how_IAdv = ss "qui" ; -- L...
--  how8many_IDet = mkDeterminer Pl "quantus" ; -- L...
  if_Subj = ss "si" ; -- L...
  in8front_Prep = mkPrep "coram" Abl ;
  i_Pron = mkPronoun Masc Sg P1 ;
  in_Prep = mkPrep "in" ( variants { Abl ; Acc } ) ; -- L...
  it_Pron = mkPronoun Neutr Sg P3 ;
  less_CAdv =  { s = "minus" ; p = "" } ; -- L...
--  many_Det = mkDeterminer Pl "multi" ;
--  more_CAdv = ss "magis" ;
--  most_Predet = ss "plurimi" ;
--  much_Det = mkDeterminer Sg "multus" ;
--  must_VV = {
--    s = table {
--      VVF VInf => ["have to"] ;
--      VVF VPres => "must" ;
--      VVF VPPart => ["had to"] ;
--      VVF VPresPart => ["having to"] ;
--      VVF VPast => ["had to"] ;      --# notpresent
--      VVPastNeg => ["hadn't to"] ;      --# notpresent
--      VVPresNeg => "mustn't"
--      } ;
--    isAux = True
--    } ;
-----b  no_Phr = ss "immo" ;
  no_Utt = ss "non" ;
--  on_Prep = ss "???" ;
------  one_Quant = mkDeterminer Sg "one" ; -- DEPRECATED
  only_Predet = ss "tantum" ;
--  or_Conj = sd2 [] "aut" ** {n = Sg} ;
--  otherwise_PConj = ss "praeterea" ; -- Pons
  part_Prep = mkPrep [] Gen ;
--  please_Voc = ss "queso" ;
  possess_Prep = mkPrep [] Gen ;
--  quite_Adv = ss "???" ;
  she_Pron = mkPronoun Fem Sg P3 ;
  so_AdA = ss "sic" ;
--  somebody_NP = regNP "somebody" Sg ;
--  someSg_Det = mkDeterminer Sg "some" ;
--  somePl_Det = mkDeterminer Pl "some" ;
--  something_NP = regNP "something" Sg ;
--  somewhere_Adv = ss "somewhere" ;
  that_Quant = ille_Quantifier ;
--  there_Adv = ss "there" ;
--  there7to_Adv = ss "there" ;
--  there7from_Adv = ss ["from there"] ;
--  therefore_PConj = ss "therefore" ;
  they_Pron = mkPronoun Masc Pl P3 ;
  this_Quant = hic_Quantifier ;
--  through_Prep = ss "through" ;
--  too_AdA = ss "too" ;
  to_Prep = mkPrep "ad" Acc;
  under_Prep = mkPrep "sub" Acc ;
  very_AdA = ss "valde" ;
  want_VV = IrregLat.want_irreg_VV ;
  we_Pron = mkPronoun Masc Pl P1 ;
--  whatPl_IP = mkIP "what" "what" "what's" Pl ;
--  whatSg_IP = mkIP "what" "what" "what's" Sg ;
--  when_IAdv = ss "when" ;
--  when_Subj = ss "when" ;
--  where_IAdv = ss "where" ;
--  which_IQuant = {s = \\_ => "which"} ;
-----b  whichPl_IDet = mkDeterminer Pl ["which"] ;
-----b  whichSg_IDet = mkDeterminer Sg ["which"] ;
--  whoPl_IP = mkIP "who" "whom" "whose" Pl ;
--  whoSg_IP = mkIP "who" "whom" "whose" Sg ;
  why_IAdv = ss "cur" ; -- L...
  without_Prep = mkPrep "sine" Abl ; -- abl. L..
  with_Prep = mkPrep "cum" Abl ; -- abl. L..
  yes_Utt = ss "sane" ; -- L...
  youSg_Pron = mkPronoun Masc Sg P2 ;
  youPl_Pron = mkPronoun Masc Pl P2 ;
  youPol_Pron = youSg_Pron | youPl_Pron ;

  lin language_title_Utt = ss "latina" ;


}

