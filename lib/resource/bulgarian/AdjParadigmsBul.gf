resource AdjParadigmsBul = open
  (Predef=Predef),
  Prelude,
  MorphoBul,
  CatBul
  in {
oper
  mkA76 : Str -> A =
    \nov -> mkAdjective nov
                        (nov+"��")
                        (nov+"���")
                        (nov+"�")
                        (nov+"���")
                        (nov+"�")
                        (nov+"���")
                        (nov+"�")
                        (nov+"���")
            ** {lock_A = <>} ;
  mkA77 : Str -> A =
    \vish -> mkAdjective vish
                         (vish+"��")
                         (vish+"���")
                         (vish+"�")
                         (vish+"���")
                         (vish+"�")
                         (vish+"���")
                         (vish+"�")
                         (vish+"���")
             ** {lock_A = <>} ;
  mkA78 : Str -> A =
    \bylgarski -> 
             let bylgarsk = init bylgarski
             in mkAdjective bylgarski
                            (bylgarsk+"��")
                            (bylgarsk+"���")
                            (bylgarsk+"�")
                            (bylgarsk+"���")
                            (bylgarsk+"�")
                            (bylgarsk+"���")
                            (bylgarsk+"�")
                            (bylgarsk+"���")
                ** {lock_A = <>} ;
  mkA79 : Str -> A =
    \silen -> let siln : Str = case silen of { sil+"��" => sil+"�" }
              in mkAdjective silen
                             (siln+"��")
                             (siln+"���")
                             (siln+"�")
                             (siln+"���")
                             (siln+"�")
                             (siln+"���")
                             (siln+"�")
                             (siln+"���")
                 ** {lock_A = <>} ;
  mkA80 : Str -> A =
    \dobyr -> let dobr : Str = case dobyr of { dob+"�"+r@("�"|"�"|"�"|"�"|"�"|"�") => dob+r }
              in mkAdjective dobyr
                             (dobr+"��")
                             (dobr+"���")
                             (dobr+"�")
                             (dobr+"���")
                             (dobr+"�")
                             (dobr+"���")
                             (dobr+"�")
                             (dobr+"���")
                 ** {lock_A = <>} ;
  mkA81 : Str -> A =
    \bial ->  let bel : Str = ia2e bial
              in mkAdjective bial
                             (bel+"��")
                             (bel+"���")
                             (bial+"�")
                             (bial+"���")
                             (bial+"�")
                             (bial+"���")
                             (bel+"�")
                             (bel+"���")
                 ** {lock_A = <>} ;
  mkA82 : Str -> A =
    \ostrowryh -> let ostrowyrh : Str = case ostrowryh of { ostrow+"��"+h@("�"|"�"|"�") => ostrow+"��"+h }
                  in mkAdjective ostrowryh
                                 (ostrowyrh+"��")
                                 (ostrowyrh+"���")
                                 (ostrowyrh+"�")
                                 (ostrowyrh+"���")
                                 (ostrowyrh+"�")
                                 (ostrowyrh+"���")
                                 (ostrowyrh+"�")
                                 (ostrowyrh+"���")
                     ** {lock_A = <>} ;
  mkA82� : Str -> A =
    \dyrzyk -> let dryzk : Str = case dyrzyk of { d+"�����" => d+"����" }
                  in mkAdjective dyrzyk
                                 (dryzk+"��")
                                 (dryzk+"���")
                                 (dryzk+"�")
                                 (dryzk+"���")
                                 (dryzk+"�")
                                 (dryzk+"���")
                                 (dryzk+"�")
                                 (dryzk+"���")
                     ** {lock_A = <>} ;
  mkA83 : Str -> A =
    \riadyk ->let riadk : Str = case riadyk of { riad+"��" => riad+"�"}
              in mkAdjective riadyk
                             (ia2e riadk+"��")
                             (ia2e riadk+"���")
                             (riadk+"�")
                             (riadk+"���")
                             (riadk+"�")
                             (riadk+"���")
                             (ia2e riadk+"�")
                             (ia2e riadk+"���")
                 ** {lock_A = <>} ;
  mkA84 : Str -> A = 
    \veren -> let viarn : Str = case veren of { v + "�" + r@("�"|"�"|"�"|"�"|"�"|"�")+"��" => v+"�"+r+"�" }
              in mkAdjective veren
                             (ia2e viarn+"��")
                             (ia2e viarn+"���")
                             (viarn+"�")
                             (viarn+"���")
                             (viarn+"�")
                             (viarn+"���")
                             (ia2e viarn+"�")
                             (ia2e viarn+"���")
                 ** {lock_A = <>} ;
  mkA84� : Str -> A =
    \svesten ->
              let sviastn : Str = case svesten of { sv + "�����" => sv+"����" }
              in mkAdjective svesten
                             (ia2e sviastn+"��")
                             (ia2e sviastn+"���")
                             (sviastn+"�")
                             (sviastn+"���")
                             (sviastn+"�")
                             (sviastn+"���")
                             (ia2e sviastn+"�")
                             (ia2e sviastn+"���")
                 ** {lock_A = <>} ;
  mkA85 : Str -> A =
    \stroen ->
              let stroin : Str = case stroen of { stro + "��" => stro+"��" }
              in mkAdjective stroen
                             (stroin+"��")
                             (stroin+"���")
                             (stroin+"�")
                             (stroin+"���")
                             (stroin+"�")
                             (stroin+"���")
                             (stroin+"�")
                             (stroin+"���")
                 ** {lock_A = <>} ;
  mkA86 : Str -> A =
    \sin ->   mkAdjective sin
                          (sin+"��")
                          (sin+"���")
                          (sin+"�")
                          (sin+"���")
                          (sin+"��")
                          (sin+"����")
                          (sin+"�")
                          (sin+"���")
              ** {lock_A = <>} ;
  mkA87 : Str -> A =
    \ovchi -> let ovch : Str = case ovchi of { ovch+"�" => ovch }
              in mkAdjective ovchi
                             (ovch+"��")
                             (ovch+"���")
                             (ovch+"�")
                             (ovch+"���")
                             (ovch+"�")
                             (ovch+"���")
                             (ovch+"�")
                             (ovch+"���")
                 ** {lock_A = <>} ;
  mkA88 : Str -> A =
    \kozi ->  let koz : Str = case kozi of { koz+"�" => koz }
              in mkAdjective kozi
                             (koz+"��")
                             (koz+"���")
                             (koz+"�")
                             (koz+"���")
                             (koz+"�")
                             (koz+"���")
                             (koz+"�")
                             (koz+"���")
                 ** {lock_A = <>} ;
}