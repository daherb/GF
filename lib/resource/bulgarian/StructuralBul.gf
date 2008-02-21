concrete StructuralBul of Structural = CatBul ** 
  open MorphoBul, (P = ParadigmsBul), Prelude in {

  flags optimize=all ;

  lin
  above_Prep = ss "���" ;
  after_Prep = ss "����" ;
  all_Predet = {s = table GenNum ["�������";"��������";"��������";"��������"]} ;
  almost_AdA, almost_AdN = ss "�����" ;
{-  although_Subj = ss "although" ;
  always_AdV = ss "always" ;
  and_Conj = ss "and" ** {n = Pl} ;
-}
  because_Subj = ss "������" ;
  before_Prep = ss "�����" ;
  behind_Prep = ss "���" ;
  between_Prep = ss "�����" ;
{-
  both7and_DConj = sd2 "both" "and" ** {n = Pl} ;
  but_PConj = ss "but" ;
-}
  by8agent_Prep = ss "����" ;
  by8means_Prep = ss "����" ;
{-
  can8know_VV, can_VV = {
    s = table { 
      VVF VInf => ["be able to"] ;
      VVF VPres => "can" ;
      VVF VPPart => ["been able to"] ;
      VVF VPresPart => ["being able to"] ;
      VVF VPast => "could" ;      --# notpresent
      VVPastNeg => "couldn't" ;   --# notpresent
      VVPresNeg => "can't"
      } ;
    isAux = True
    } ;
-}
  during_Prep = ss ["�� ����� ��"] ;
{-
  either7or_DConj = sd2 "either" "or" ** {n = Sg} ;
  everybody_NP = regNP "everybody" Sg ;
-}
  every_Det = mkDeterminerSg "�����" "�����" "�����";
{-
  everything_NP = regNP "everything" Sg ;
-}
  everywhere_Adv = ss "���������" ;
  few_Det = {s = \\_,_ => "�������"; n = Pl; countable = True; spec = Indef} ;
---  first_Ord = ss "first" ; DEPRECATED
  for_Prep = ss "��" ;
  from_Prep = ss "��" ;
  he_Pron = mkNP "���" "����" "����" "����" "�����" "����" "������" "����" "������" "����" "������" (GSg Masc) P3 ;
  here_Adv = ss "���" ;
  here7to_Adv = ss ["�� ���"] ;
  here7from_Adv = ss ["�� ���"] ;
  how_IAdv = ss "���" ;
  how8many_IDet = mkDeterminerPl ["����� �����"] ;
  if_Subj = ss "���" ;
  in8front_Prep = ss "����" ;
  i_Pron  = mkNP "��" "���" "���" "���" "����" "���" "�����" "���" "�����" "���" "�����" (GSg Masc) P1 ;
  in_Prep = ss (pre { "�" ; 
                      "���" / strs {"�" ; "�" ; "�" ; "�"}
                    }) ;
  it_Pron  = mkNP "��" "����" "�����" "�������" "��������" "������" "��������" "������" "��������" "������" "��������" (GSg Neut) P3 ;
  less_CAdv = ss "�������" ;
  many_Det = mkDeterminerPl "�����" ;
  more_CAdv = ss "���" ;
  most_Predet = {s = \\_ => "��������"} ;
  much_Det = mkDeterminerSg "�����" "�����" "�����";
{-
  must_VV = {
    s = table {
      VVF VInf => ["have to"] ;
      VVF VPres => "must" ;
      VVF VPPart => ["had to"] ;
      VVF VPresPart => ["having to"] ;
      VVF VPast => ["had to"] ;      --# notpresent
      VVPastNeg => ["hadn't to"] ;      --# notpresent
      VVPresNeg => "mustn't"
      } ;
    isAux = True
    } ;
-}
  no_Phr = ss "��" ;
  on_Prep = ss "��" ;
----  one_Quant = mkDeterminer Sg "one" ; -- DEPRECATED
  only_Predet = {s = \\_ => "����"} ;
{-
  or_Conj = ss "or" ** {n = Sg} ;
  otherwise_PConj = ss "otherwise" ;
-}
  part_Prep = ss "��" ;
{-
  please_Voc = ss "please" ;
-}
  possess_Prep = ss "��" ;
  quite_Adv = ss "�����" ;
  she_Pron = mkNP "��" "���" "����" "������" "�������" "�����" "�������" "�����" "�������" "�����" "�������" (GSg Fem) P3 ;
{-
  so_AdA = ss "so" ;
  somebody_NP = regNP "somebody" Sg ;
  someSg_Det = mkDeterminerSg "�����" "�����" "�����" ;
  somePl_Det = mkDeterminerPl "�����" ;
  something_NP = regNP "something" Sg ;
-}
  somewhere_Adv = ss "������" ;
  that_Quant = mkQuant "����" "�����" "�����" "�����" ;
{-
  that_NP = regNP "that" Sg ;
-}
  there_Adv = ss "���" ;
  there7to_Adv = ss ["�� ���"] ;
  there7from_Adv = ss ["�� ���"] ;
{-
  therefore_PConj = ss "therefore" ;
  these_NP = regNP "these" Pl ;
-}
  they_Pron = mkNP "��" "���" "�����" "������" "�������" "�����" "�������" "�����" "�������" "�����" "�������" GPl P3 ; 
  this_Quant = mkQuant "����" "�a��" "����" "����" ;
{-
  this_NP = regNP "this" Sg ;
  those_NP = regNP "those" Pl ;
-}
  through_Prep = ss "����" ;
{-
  too_AdA = ss "too" ;
-}
  to_Prep = ss "��" ;
  under_Prep = ss "���" ;
{-
  very_AdA = ss "very" ;
  want_VV = P.mkVV (P.regV "want") ;
-}
  we_Pron = mkNP "���" "���" "���" "�����" "������" "����" "������" "����" "������" "����" "������" GPl P1 ;
  whatPl_IP = mkIP "�����" GPl ;
  whatSg_IP = mkIP "�����" (GSg Masc) ;
  when_IAdv = ss "����" ;
{-
  when_Subj = ss "when" ;
-}
  where_IAdv = ss "����" ;
{-
  whichPl_IDet = mkDeterminer Pl ["which"] ;
  whichSg_IDet = mkDeterminer Sg ["which"] ;
-}
  whoSg_IP = mkIP "���" (GSg Masc) ;
  whoPl_IP = mkIP "���" GPl ;
  why_IAdv = ss "����" ;
  without_Prep = ss "���" ;
  with_Prep = ss (pre { "�" ; 
                        "���" / strs {"�" ; "�" ; "�" ; "�"}
                      }) ;
  yes_Phr = ss "��" ;
  youSg_Pron = mkNP "��" "���" "����" "����" "�����" "����" "������" "����" "������" "����" "������" (GSg Masc) P2 ;
  youPl_Pron = mkNP "���" "���" "���" "�����" "������" "����" "������" "����" "������" "����" "������" GPl P2 ;
  youPol_Pron = mkNP "���" "���" "���" "�����" "������" "����" "������" "����" "������" "����" "������" (GSg Masc) P2 ;
}

