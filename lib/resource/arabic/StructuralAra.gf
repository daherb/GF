concrete StructuralAra of Structural = CatAra ** 
  open MorphoAra, ResAra, ParadigmsAra, Prelude in {

  flags optimize=all ;

  lin
  above_Prep = ss "فَوْقَ" ;
  after_Prep = ss "بَعْدَ" ;
  all_Predet = mkPredet "كُلّ" True ;
--  almost_AdA, almost_AdN = ss "َلمْست" ;
--  although_Subj = ss "َلتهُْغه" ;
--  always_AdV = ss "َلوَيس" ;
  and_Conj = ss "وَ" ** {n = Pl} ;
--  because_Subj = ss "بعَُسي" ;
  before_Prep = ss "قَبْلَ" ;
  behind_Prep = ss "خَلْفَ" ;
  between_Prep = ss "بَيْنَ" ;
--  both7and_DConj = sd2 "بْته" "َند" ** {n = Pl} ;
--  but_PConj = ss "بُت" ;
  by8agent_Prep = ss "بِ" ;
  by8means_Prep = ss "بِ" ;
--  can8know_VV, can_VV = {
--    s = table VVForm [["بي َبلي تْ"] ; "عَن" ; "عُْلد" ; 
--         ["بّن َبلي تْ"] ; ["بِنغ َبلي تْ"] ; "عَنءت" ; "عُْلدنءت"] ; 
--    isAux = True
--    } ;
  during_Prep = ss "خِلَالَ" ;
--  either7or_DConj = sd2 "ِتهر" "ْر" ** {n = Sg} ;
--  everybody_NP = regNP "ثريبْدي" Sg ;
  every_Det = mkDet "كُلّ" Sg Const ;
--  everything_NP = regNP "ثريتهِنغ" Sg ;
--  everywhere_Adv = ss "ثريوهري" ;
  few_Det = mkDet "بَعض" Pl Const ;
--  first_Ord = ss "فِرست" ;
  from_Prep = ss "مِنَ" ;
  he_Pron = mkNP "هُوَ" "هُ" "هُ" (Per3 Masc Sg) ;
  here_Adv = ss "هُنا" ;
--  here7to_Adv = ss ["تْ هري"] ;
--  here7from_Adv = ss ["فرْم هري"] ;
  how_IAdv = ss "كَيفَ" ;
--  how8many_IDet = mkDeterminer Pl ["هْو مَني"] ;
--  if_Subj = ss "ِف" ;
  in8front_Prep = ss "مُقَابِلَ" ;
  i_Pron  = mkNP "أَنَا" "نِي" "ِي" (Per1 Sing);
  in_Prep = ss "فِي" ;
--  it_Pron  = mkNP "ِت" "ِت" "ِتس" Sg P3 ;
--  less_CAdv = ss "لسّ" ;
  many_Det = mkDet "جَمِيع" Pl Const ;
--  more_CAdv = ss "مْري" ;
  most_Predet = mkPredet  "أَكثَر" True ;
  much_Det = mkDet "الكَثِير مِنَ" Pl Const ;
--  must_VV = {
--    s = table VVForm [["بي هَثي تْ"] ; "مُست" ; ["هَد تْ"] ; 
--         ["هَد تْ"] ; ["هَثِنغ تْ"] ; "مُستنءت" ; ["هَدنءت تْ"]] ; ---- 
--    isAux = True
--    } ;
  no_Phr = ss "لا" ;
  on_Prep = ss "عَلى" ;
--- DEPREC  one_Quant = mkQuantNum "واحِد" Sg Indef ;
  only_Predet = mkPredet "فَقَط" False;
--  or_Conj = ss "ْر" ** {n = Sg} ;
--  otherwise_PConj = ss "ْتهروِسي" ;
  part_Prep = ss "مِنَ" ;
--  please_Voc = ss "ةلَسي" ;
  possess_Prep = ss "ل" ;
--  quite_Adv = ss "قُِتي" ;
--  she_Pron = mkNP "سهي" "هر" "هر" Sg P3 ;
--  so_AdA = ss "سْ" ;
--  somebody_NP = regNP "سْمبْدي" Sg ;
  someSg_Det = mkDet "أَحَد" Pl Const ;
  somePl_Det = mkDet "بَعض" Pl Const ;
--  something_NP = regNP "سْمتهِنغ" Sg ;
--  somewhere_Adv = ss "سْموهري" ;
  that_Quant = mkQuant3 "ذَلِكَ" "تِلكَ" "أُلٱِكَ" Def;
--  that_NP = regNP "تهَت" Sg ;
  there_Adv = ss "هُناك" ;
--  there7to_Adv = ss "تهري" ;
--  there7from_Adv = ss ["فرْم تهري"] ;
--  therefore_PConj = ss "تهرفْري" ;
--  these_NP = regNP "تهسي" Pl ;
 they_Pron = mkNP "هُمْ" "هُمْ" "هُمْ" (Per3 Masc Pl) ; 
  this_Quant = mkQuant7 "هَذا" "هَذِهِ" "هَذَان" "هَذَيْن" "هَاتَان" "هَاتَيْن" "هَؤُلَاء" Def;
--  this_NP = regNP "تهِس" Sg ;
--  those_NP = regNP "تهْسي" Pl ;
  through_Prep = ss "عَبْرَ" ;
--  too_AdA = ss "تّْ" ;
  to_Prep = ss "إِلى" ;
  under_Prep = ss "تَحْتَ" ;
--  very_AdA = ss "ثري" ;
--  want_VV = P.mkVV (P.regV "وَنت") ;
  we_Pron = mkNP "نَحنُ" "نا" "نا" (Per1 Plur) ;
  whatPl_IP = mkIP "ماذا" Pl ;
  whatSg_IP = mkIP "ماذا" Sg ;
  when_IAdv = ss "مَتَى" ;
--  when_Subj = ss "وهن" ;
  where_IAdv = ss "أَينَ" ;
--  whichPl_IDet = mkDeterminer Pl ["وهِعه"] ;
--  whichSg_IDet = mkDeterminer Sg ["وهِعه"] ;
  whoSg_IP = mkIP "مَنْ" Sg ;
  whoPl_IP = mkIP "مَنْ" Pl ;
--  why_IAdv = ss "وهي" ;
  without_Prep = ss "بِدُونِ" ;
  with_Prep = ss "مَع" ;
  yes_Phr = ss "نَعَم" ;
  youSg_Pron = mkNP "أَنتَ" "كَ" "كَ" (Per2 Masc Sg) ;
  youPl_Pron = mkNP "أَنتُمْ" "كُمْ" "كُمْ" (Per2 Masc Sg) ;
  youPol_Pron = mkNP "أَنتِ" "كِ" "كِ" (Per2 Fem Sg) ;

}
