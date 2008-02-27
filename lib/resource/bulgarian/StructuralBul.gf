concrete StructuralBul of Structural = CatBul ** 
  open MorphoBul, ParadigmsBul, Prelude in {

  flags optimize=all ;

  lin
  above_Prep = mkPrep "���" Acc ;
  after_Prep = mkPrep "����" Acc ;
  all_Predet = {s = table GenNum ["�������";"��������";"��������";"��������"]} ;
  almost_AdA, almost_AdN = ss "�����" ;
  although_Subj = ss ["������� ��"] ;
{-  always_AdV = ss "always" ;
  and_Conj = ss "and" ** {n = Pl} ;
-}
  because_Subj = ss "������" ;
  before_Prep = mkPrep "�����" Acc ;
  behind_Prep = mkPrep "���" Acc ;
  between_Prep = mkPrep "�����" Acc ;
{-
  both7and_DConj = sd2 "both" "and" ** {n = Pl} ;
-}
  but_PConj = ss "��" ;
  by8agent_Prep = mkPrep "����" Acc ;
  by8means_Prep = mkPrep "����" Acc ;
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
  during_Prep = mkPrep ["�� ����� ��"] Acc ;
{-
  either7or_DConj = sd2 "either" "or" ** {n = Sg} ;
-}
  everybody_NP = mkNP "�����" (GSg Masc) P3 ;
  every_Det = mkDeterminerSg "�����" "�����" "�����";
  everything_NP = mkNP "�����" (GSg Neut) P3 ;
  everywhere_Adv = ss "���������" ;
  few_Det = {s = \\_,_ => "�������"; n = Pl; countable = True; spec = Indef} ;
---  first_Ord = ss "first" ; DEPRECATED
  for_Prep = mkPrep "��" Acc ;
  from_Prep = mkPrep "��" Acc ;
  he_Pron = mkPron "���" "����" "��" "�����" "�������" "��������" "������" "��������" "������" "��������" "������" "��������" (GSg Masc) P3 ;
  here_Adv = ss "���" ;
  here7to_Adv = ss ["�� ���"] ;
  here7from_Adv = ss ["�� ���"] ;
  how_IAdv = mkIAdv "���" ;
  how8many_IDet = {s = \\_ => "�����"; n = Pl} ;
  if_Subj = ss "���" ;
  in8front_Prep = mkPrep "����" Acc ;
  i_Pron  = mkPron "��" "���" "��" "���" "���" "����" "���" "�����" "���" "�����" "���" "�����" (GSg Masc) P1 ;
  in_Prep = mkPrep (pre { "�" ; 
                          "���" / strs {"�" ; "�" ; "�" ; "�"}
                        }) Acc ;
  it_Pron  = mkPron "��" "����" "��" "�����" "�������" "��������" "������" "��������" "������" "��������" "������" "��������" (GSg Neut) P3 ;
  less_CAdv = {s="��"; sn="��-�����"} ;
  many_Det = mkDeterminerPl "�����" ;
  more_CAdv = {s=[]; sn="������"} ;
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
  on_Prep = mkPrep "��" Acc ;
----  one_Quant = mkDeterminer Sg "one" ; -- DEPRECATED
  only_Predet = {s = \\_ => "����"} ;
{-
  or_Conj = ss "or" ** {n = Sg} ;
-}
  otherwise_PConj = ss "�����" ;
  part_Prep = mkPrep "��" Acc ;
  please_Voc = ss "����" ;
  possess_Prep = mkPrep [] Dat ;
  quite_Adv = ss "�����" ;
  she_Pron = mkPron "��" "���" "�" "����" "������" "�������" "�����" "�������" "�����" "�������" "�����" "�������" (GSg Fem) P3 ;
  so_AdA = ss "�������" ;
  somebody_NP = mkNP "�����" (GSg Masc) P3 ;
  someSg_Det = mkDeterminerSg "�����" "�����" "�����" ;
  somePl_Det = mkDeterminerPl "�����" ;
  something_NP = mkNP "����" (GSg Neut) P3 ;
  somewhere_Adv = ss "������" ;
  that_Quant = mkQuant "����" "�����" "�����" "�����" ;
  that_NP = mkNP "����" (GSg Neut) P3 ;
  there_Adv = ss "���" ;
  there7to_Adv = ss ["�� ���"] ;
  there7from_Adv = ss ["�� ���"] ;
{-
  therefore_PConj = ss "therefore" ;
-}
  these_NP = mkNP "����" GPl P3 ;
  they_Pron = mkPron "��" "���" "��" "�����" "������" "�������" "�����" "�������" "�����" "�������" "�����" "�������" GPl P3 ; 
  this_Quant = mkQuant "����" "�a��" "����" "����" ;
  this_NP = mkNP "����" (GSg Masc) P3 ;
  those_NP = mkNP "����" GPl P3 ;
  through_Prep = mkPrep "����" Acc ;
  too_AdA = ss "���������" ;
  to_Prep = mkPrep "��" Acc ;
  under_Prep = mkPrep "���" Acc ;
  very_AdA = ss "�����" ;
{-
  want_VV = P.mkVV (P.regV "want") ;
-}
  we_Pron = mkPron "���" "���" "��" "���" "�����" "������" "����" "������" "����" "������" "����" "������" GPl P1 ;
  whatPl_IP = mkIP "�����" "�����" GPl ;
  whatSg_IP = mkIP "�����" "�����" (GSg Masc) ;
  when_IAdv = mkIAdv "����" ;
  when_Subj = ss "������" ;
  where_IAdv = mkIAdv "����" ;
  whichPl_IDet = {s = table GenNum ["���";"���";"���";"���"]; n = Pl} ;
  whichSg_IDet = {s = table GenNum ["���";"���";"���";"���"]; n = Sg} ;
  whoSg_IP = mkIP "���" "����" (GSg Masc) ;
  whoPl_IP = mkIP "���" "����" GPl ;
  why_IAdv = mkIAdv "����" ;
  without_Prep = mkPrep "���" Acc ;
  with_Prep = mkPrep (pre { "�" ; 
                            "���" / strs {"�" ; "�" ; "�" ; "�"}
                          }) Acc ;
  yes_Phr = ss "��" ;
  youSg_Pron = mkPron "��" "���" "��" "����" "����" "�����" "����" "������" "����" "������" "����" "������" (GSg Masc) P2 ;
  youPl_Pron = mkPron "���" "���" "��" "���" "�����" "������" "����" "������" "����" "������" "����" "������" GPl P2 ;
  youPol_Pron = mkPron "���" "���" "��" "���" "�����" "������" "����" "������" "����" "������" "����" "������" (GSg Masc) P2 ;
}

