concrete ExtraBul of ExtraBulAbs = CatBul ** 
  open ResBul, Coordination, Prelude in {

  lin
    GenNP np = {s = \\aform => np.s ! Gen aform} ;
    
    i8fem_Pron  = mkNP "��" "���" "���" "���" "����" "���" "�����" "���" "�����" "���" "�����" (GSg Fem)  P1 ;
    i8neut_Pron = mkNP "��" "���" "���" "���" "����" "���" "�����" "���" "�����" "���" "�����" (GSg Neut) P1 ;
    
    whatSg8fem_IP  = mkIP "�����" (GSg Fem) ;
    whatSg8neut_IP = mkIP "�����" (GSg Neut) ;

    whoSg8fem_IP  = mkIP "���" (GSg Fem) ;
    whoSg8neut_IP = mkIP "���" (GSg Neut) ;
    
    youSg8fem_Pron  = mkNP "��" "���" "����" "����" "�����" "����" "������" "����" "������" "����" "������" (GSg Fem) P2 ;
    youSg8neut_Pron = mkNP "��" "���" "����" "����" "�����" "����" "������" "����" "������" "����" "������" (GSg Neut) P2 ;
    
    youPol8fem_Pron  = mkNP "���" "���" "���" "�����" "������" "����" "������" "����" "������" "����" "������" (GSg Fem) P2 ;
    youPol8neut_Pron = mkNP "���" "���" "���" "�����" "������" "����" "������" "����" "������" "����" "������" (GSg Neut) P2 ;
} 
