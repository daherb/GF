
--1 Basic Latin Lexicon for Structural Categories.
-- Aarne Ranta pre 2013, Herbert Lange 2013

-- This lexicon implements all the words in the abstract Lexicon.
-- For each entry a source is given, either a printed dictionary, a 
-- printed grammar book or a link to an online source. The used printed 
-- dictionaries are Langescheidts Schulwörterbuch Lateinisch 17. Edition 
-- 1984 (shorter: Langenscheidts), PONS Schulwörterbuch Latein 1. Edition 
-- 2012 (Shorter: Pons) and Der kleine Stowasser 3. Edition 1991 (shorter: 
-- Stowasser). The Grammar book is Bayer-Lindauer: Lateinische Schulgrammatik
-- 2. Edition 1994.

concrete StructuralLat of Structural = CatLat ** 
  open ResLat, ParadigmsLat, Prelude, IrregLat, ConstructX in 
  {
    
  flags optimize=all ;
	
  lin
  above_Prep = mkPrep "super" Abl ; -- abl. (Langenscheidts)
  after_Prep = mkPrep "post" Acc ; -- acc. (Langenscheidts)
  all_Predet = ss "cuncti" ; -- (Langenscheidts)
  almost_AdA, almost_AdN = ss "quasi" ; -- (Langenscheidts)
  although_Subj = ss "quamquam" ; -- (Langenscheidts)
  always_AdV = ss "semper" ; -- (Langenscheidts)
  and_Conj = sd2 [] "et" ** {n = Pl} ; -- (Langenscheidts)
-----b  and_Conj = ss "and" ** {n = Pl} ;
  because_Subj = ss "cum" ; -- (Langenscheidts)
  before_Prep = mkPrep "ante" Acc ; -- acc. (Langenscheidts)
  behind_Prep = mkPrep "a tergo" Acc ; -- acc. (Langenscheidts)
  between_Prep = mkPrep "inter" Acc ; -- acc. (Langenscheidts)
  both7and_DConj = sd2 "et" "et" ** {n = Pl} ; --(Langenscheidts)
  but_PConj = ss "sed" ; -- (Langenscheidts)
  by8agent_Prep = mkPrep "per" Abl ; -- (Langenscheidts)
  by8means_Prep = Abl_Prep ; -- (Langenscheidts)
  can8know_VV, can_VV = IrregLat.can_VV ; --(Langenscheidts)
  during_Prep = mkPrep "inter" Acc ; -- (Langenscheidts)
  either7or_DConj = sd2 "aut" "aut" ** {n = Sg} ; -- (Langenscheidts)
  everybody_NP = regNP  "quisque" "quemque" "cuiusque" "cuique" "quoque" "quisque" ( Masc | Fem ) Sg ;-- regNP "quisquae" Sg ; -- (Langenscheidts)
  every_Det = mkDeterminer ( mkA "omnis" ) Pl ; -- (Pons)
  everything_NP = regNP "omnia" "omnia" "omnium" "omnis" "omnis" "omnia" Neutr Pl ; --regNP "omnia" Pl ; -- (Langenscheidts)
  everywhere_Adv = ss "ubique" ; -- (Langenscheidts)
  few_Det = mkDeterminer ( mkA "paulus" ) Pl ; -- (Langenscheidts)
-----  first_Ord = ss "first" ; DEPRECATED
  for_Prep = mkPrep "pro" Abl ; -- abl. (Langenscheidts)
  from_Prep = mkPrep "de" Abl ; -- abl. (Langenscheidts)
  he_Pron = mkPronoun Masc Sg P3 ;
  here_Adv = ss "hic" ; -- (Langenscheidts)
  here7to_Adv = ss "huc" ; -- (Langenscheidts)
  here7from_Adv = ss "hinc" ; -- (Langenscheidts)
  how_IAdv = ss "qui" ; -- (Langenscheidts)
  how8many_IDet = mkDeterminer (mkA "quantus" ) Pl ; -- (Pons)
  how8much_IAdv = ss "quantum" ; -- (Langenscheidts)
  if_Subj = ss "si" ; -- (Langenscheidts)
  in8front_Prep = mkPrep "ante" Acc ; -- acc. (Langenscheidts)
  i_Pron = mkPronoun Masc Sg P1 ;
  in_Prep = mkPrep "in" ( variants { Abl ; Acc } ) ; -- (Langenscheidts)
  it_Pron = mkPronoun Neutr Sg P3 ; 
  less_CAdv = mkCAdv "minus" "quam" ; -- (Langenscheidts)
  many_Det = mkDeterminer ( mkA "multus" ) Pl ; -- (Langenscheidts)
  more_CAdv = mkCAdv "magis" "quam" ; -- (Langenscheidts)
  most_Predet = ss "plurimi" ; -- (Langenscheidts)
  much_Det = mkDeterminer ( mkA "multus" ) Sg ; -- (Langenscheidts)
  must_VV = mkVV ( mkV "debere" ) True ; -- (Langenscheidts)
-----b  no_Phr = ss "immo" ;
  no_Utt = ss "non est" ; -- should be expressed by a short negated sentence (Langenscheidts)
  on_Prep = mkPrep "in" ( Acc | Abl ) ; -- (Langenscheidts)
------  one_Quant = mkDeterminer Sg "one" ; -- DEPRECATED
  only_Predet = ss "solum" ; -- (Langenscheidts)
  or_Conj = sd2 [] "aut" ** {n = Sg} ; -- (Langenscheidts)
  otherwise_PConj = ss "praeterea" ; -- (Pons)
  part_Prep = mkPrep [] Gen ; -- (Bayer-Lindauer $127)
  please_Voc = ss "queso" ; -- (Langenscheidts)
  possess_Prep = mkPrep [] Gen ; -- (Bayer-Lindauer $125.2)
  quite_Adv = ss "admodum" ; -- or by comparation (Langenscheidts)
  she_Pron = mkPronoun Fem Sg P3 ;
  so_AdA = ss "sic" ; -- (Langenscheidts)
  somebody_NP = regNP "aliquis" "aliquem" "alicuius" "clicui" "aliquo" "aliquis" ( Masc | Fem ) Sg ; -- (Bayer-Lindauer $60.1)
  someSg_Det = mkDeterminer ( mkA "aliquis" ) Sg ; -- (Langenscheidts)
  somePl_Det = mkDeterminer ( mkA "nonnullus" ) Pl ; -- (Langenscheidts)
  something_NP = regNP "aliquid" "aliquid" "alicuius rei" "alicui rei" "aliqua re" "aliquid" Masc Sg ; -- (Bayer-Lindauer $60.1)
  somewhere_Adv = ss "usquam" ; -- (Langenscheidts)
  that_Quant = ille_Quantifier ;
  that_Subj = ss "ut" ; -- (Langenscheidts)
  there_Adv = ss "ibi" ; -- loc. (Langenscheidts)
  there7to_Adv = ss "eo" ; -- (Pons)
  there7from_Adv = ss "inde" ; -- (Pons)
  therefore_PConj = ss "ergo" ; -- (Langenscheidts)
  they_Pron = mkPronoun Masc Pl P3 ;
  this_Quant = hic_Quantifier ;
  through_Prep = mkPrep "per" Acc ; -- (Langenscheidts)
  too_AdA = ss "quoque" ; -- (Langenscheidts)
  to_Prep = mkPrep "ad" Acc; -- (Langenscheidts)
  under_Prep = mkPrep "sub" Acc ; -- (Langenscheidts)
  very_AdA = ss "valde" ; -- (Langenscheidts)
  want_VV = mkVV IrregLat.want_V True ; -- (Langenscheidts)
  we_Pron = mkPronoun Masc Pl P1 ;
  whatSg_IP = { s =pronForms "quid" "quid" "cuius" "cui" "quo" ; n = Sg } ; -- only feminine or masculine (Bayer-Lindauer $59.1)
  whatPl_IP = { s = \\_ => "" ; n = Pl } ; -- no plural forms (Bayer-Lindauer $59.1)
  when_IAdv = ss "quando" ; -- (Langenscheidts)
  when_Subj = ss "si" ; -- (Langenscheidts)
  where_IAdv = ss "ubi" ; -- (Langenscheidts)
  which_IQuant = -- (Bayer-Lindauer §59.1.2 and §58.1)
    { s = table { 
	Ag Masc  Sg c => ( pronForms "qui" "quem" "cuius" "cui" "quo" ) ! c ;
	Ag Masc  Pl c => ( pronForms "qui" "quos" "quorum" "quibus" "quibus" ) ! c ;
	Ag Fem   Sg c => ( pronForms "quae" "quam" "cuius" "cui" "qua" ) ! c ;
	Ag Fem   Pl c => ( pronForms "quae" "quas" "quarum" "quibus" "quibus" ) ! c ;
	Ag Neutr Sg c => ( pronForms "quod" "quod" "cuius" "cui" "quo" ) ! c ;
	Ag Neutr Pl c => ( pronForms "quae" "quae" "quorum" "quibus" "quibus" ) ! c
	}
    } ;
-----b  whichPl_IDet = mkDeterminer Pl ["which"] ;
-----b  whichSg_IDet = mkDeterminer Sg ["which"] ;
  whoSg_IP = { s =pronForms "quis" "quem" "cuius" "cui" "quo" ; n = Sg } ; -- only feminine or masculine (Bayer-Lindauer §59.1)
  whoPl_IP = { s = \\_ => "" ; n = Pl } ; -- no plural forms (Bayer-Lindauer §59.1)

  why_IAdv = ss "cur" ; -- (Langenscheidts)
  without_Prep = mkPrep "sine" Abl ; -- abl. L..
  with_Prep = mkPrep "cum" Abl ; -- abl. L..
  yes_Utt = ss "sane" ; -- (Langenscheidts)
  youSg_Pron = mkPronoun Masc Sg P2 ;
  youPl_Pron = mkPronoun Masc Pl P2 ;
  youPol_Pron = youSg_Pron | youPl_Pron ;

  no_Quant = { s , sp = ( mkA "nullus" ).s ! Posit } ; -- nullus (Langenscheidts) 
  not_Predet = ss "non" ; -- (Langenscheidts)
  if_then_Conj = {s1 = "si" ; s2 = "######" ; n = Sg } ; -- no word in s2 field (Langenscheidts) 
  at_least_AdN = ss "saltem" ; -- (Langenscheidts)
  at_most_AdN = ss "summum" ; -- (Pons)
  nobody_NP = regNP "nemo" "neminem" "neminis" "nemini" "nemine" "nemo" ( Masc | Fem ) Sg ; -- (Bayer Lindauer §60.4)
  nothing_NP = regNP "nihil" "nihil" "nullius rei" "nulli rei" "nulla re" "nihil" Neutr Sg ; -- (Bayer-Lindauer §60.4)
  except_Prep = mkPrep "praeter" Acc ; -- (Langenscheidts)

  as_CAdv = mkCAdv "ita" "ut" ; -- (Langenscheidts)

  have_V2 = mkV2 (mkV "habere") ; -- habeo, -ui, -itum 2 (Langenscheidts)

  lin language_title_Utt = ss "lingua latina" ;

}

