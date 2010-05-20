concrete ExtraBul of ExtraBulAbs = CatBul ** 
  open ResBul, MorphoFunsBul, Coordination, Prelude in {
  flags coding=cp1251 ;


  lin
    PossIndefPron p = {
      s = \\_,aform => p.gen ! (indefAForm ! aform) ;
      nonEmpty = True;
      spec = Indef
      } ;
      
    ReflQuant = {
      s = \\_,aform => reflPron ! aform ;
      nonEmpty = True;
      spec = Indef
    } ;

    ReflIndefQuant = {
      s = \\_,aform => reflPron ! (indefAForm ! aform) ;
      nonEmpty = True;
      spec = Indef
    } ;

    i8fem_Pron  = mkPron "��" "���" "��" "���" "���" "����" "���" "�����" "���" "�����" "���" "�����" (GSg Fem)  P1 ;
    i8neut_Pron = mkPron "��" "���" "��" "���" "���" "����" "���" "�����" "���" "�����" "���" "�����" (GSg Neut) P1 ;
    
    whatSg8fem_IP  = mkIP "�����" "�����" (GSg Fem) ;
    whatSg8neut_IP = mkIP "�����" "�����" (GSg Neut) ;

    whoSg8fem_IP  = mkIP "���" "����" (GSg Fem) ;
    whoSg8neut_IP = mkIP "���" "����" (GSg Neut) ;
    
    youSg8fem_Pron  = mkPron "��" "���" "��" "����" "����" "�����" "����" "������" "����" "������" "����" "������" (GSg Fem) P2 ;
    youSg8neut_Pron = mkPron "��" "���" "��" "����" "����" "�����" "����" "������" "����" "������" "����" "������" (GSg Neut) P2 ;

    onePl_Num = {s = table {
                       CFMasc Indef _ | CFFem Indef | CFNeut Indef            => "����" ;
                       CFMasc Def _ | CFMascDefNom _ | CFFem Def | CFNeut Def => "������"
                     } ;
                 n = Pl;
                 nonEmpty = True
                } ;

    UttImpSg8fem  pol imp = {s = pol.s ++ imp.s ! pol.p ! GSg Fem} ;
    UttImpSg8neut pol imp = {s = pol.s ++ imp.s ! pol.p ! GSg Fem} ;
    
    IAdvAdv adv = {s = \\qf => (mkIAdv "�����").s ! qf ++ adv.s} ;

  oper
    reflPron : AForm => Str =
      table {
        ASg Masc Indef => "����" ;
        ASg Masc Def   => "����" ;
        ASgMascDefNom  => "�����" ;
        ASg Fem  Indef => "����" ;
        ASg Fem  Def   => "������" ;
        ASg Neut Indef => "����" ;
        ASg Neut Def   => "������" ;
        APl Indef      => "����" ;
        APl Def        => "������"
      } ;
      
    indefAForm : AForm => AForm =
      table {
        ASg g _       => ASg g Indef ;
        ASgMascDefNom => ASg Masc Indef ;
        APl _         => APl Indef
      } ;
} 
