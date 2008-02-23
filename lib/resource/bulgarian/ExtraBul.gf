concrete ExtraBul of ExtraBulAbs = CatBul ** 
  open ResBul, Coordination, Prelude in {

  lin
    GenNP np = {s = \\gn => np.s ! Gen (aform gn Def Nom); spec=Indef} ;
    
    GenNPIndef np = {s = \\gn => np.s ! Gen (aform gn Indef Nom); spec=Indef} ;
    
    i8fem_Pron  = mkPron "��" "���" "��" "���" "���" "����" "���" "�����" "���" "�����" "���" "�����" (GSg Fem)  P1 ;
    i8neut_Pron = mkPron "��" "���" "��" "���" "���" "����" "���" "�����" "���" "�����" "���" "�����" (GSg Neut) P1 ;
    
    whatSg8fem_IP  = mkIP "�����" "�����" (GSg Fem) ;
    whatSg8neut_IP = mkIP "�����" "�����" (GSg Neut) ;

    whoSg8fem_IP  = mkIP "���" "����" (GSg Fem) ;
    whoSg8neut_IP = mkIP "���" "����" (GSg Neut) ;
    
    youSg8fem_Pron  = mkPron "��" "���" "��" "����" "����" "�����" "����" "������" "����" "������" "����" "������" (GSg Fem) P2 ;
    youSg8neut_Pron = mkPron "��" "���" "��" "����" "����" "�����" "����" "������" "����" "������" "����" "������" (GSg Neut) P2 ;
    
    youPol8fem_Pron  = mkPron "���" "���" "��" "���" "�����" "������" "����" "������" "����" "������" "����" "������" (GSg Fem) P2 ;
    youPol8neut_Pron = mkPron "���" "���" "��" "���" "�����" "������" "����" "������" "����" "������" "����" "������" (GSg Neut) P2 ;

    onePl_Num = {s = table {
                       DMascIndef | DMascPersonalIndef | DFemIndef | DNeutIndef                             => "����" ;
                       DMascDef | DMascDefNom | DMascPersonalDef | DMascPersonalDefNom | DFemDef | DNeutDef => "������"
                     } ;
                 n = Pl;
                 empty = False
                } ;

    UttImpSg8fem  pol imp = {s = pol.s ++ imp.s ! pol.p ! GSg Fem} ;
    UttImpSg8neut pol imp = {s = pol.s ++ imp.s ! pol.p ! GSg Fem} ;
} 
