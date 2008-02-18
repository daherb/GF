--# -path=.:alltenses

resource Kotus = Declensions ** open MorphoFin,CatFin,Prelude in {

oper

  d01 : Str -> NForms -- 1780 �ljy
    = \s -> dUkko s (s + "n") ;
  d01A : Str -> NForms -- 166 y�kk�
    = \s -> dUkko s (weakGrade s + "n") ;
  d02 : Str -> NForms -- 1189 ��ntely
    = \s -> dSilakka s (s + "n") (s + "j" + getHarmony (last s)) ;
  d03 : Str -> NForms -- 481 ��nti�
    = \s -> dSilakka s (s + "n") (s + "it" + vowelHarmony s) ;
  d04A : Str -> NForms -- 273 �p�rikk�
    = \s -> let ws = weakGrade s in 
      dSilakka s (ws + "n") (ws + "it" + getHarmony (last s)) ;
  d05 : Str -> NForms -- 3212 �ljymaali
    = \s -> dPaatti s (s + "n") ;
  d05A : Str -> NForms -- 1959 �yl�tti
    = \s -> dPaatti s (weakGrade s + "n") ;
  d06 : Str -> NForms -- 1231 �ykk�ri
    = \s -> dTohtori s ;
  d07 : Str -> NForms -- 81 vuoksi
    = \s -> dArpi s (init s + "en") ;
  d07A : Str -> NForms -- 70 v�ki
    = \s -> dArpi s (init (weakGrade s) + "en") ;
  d08 : Str -> NForms -- 99 � la carte
    = \s -> dNukke s (s + "n") ;
  d08A : Str -> NForms -- 5 vinaigrette
    = \s -> dNukke s (weakGrade s + "n") ;
  d09 : Str -> NForms -- 696 ��riraja
    = \s -> let a = last s in dSilakka s         
              (s + "n")
              (init s + case a of {"a" => "o" ; _ => "�"} + "j" + a) ;
  d09A : Str -> NForms -- 1040 ��niraita
    = \s -> let a = last s in dSilakka s         
              (weakGrade s + "n")
              (init s + case a of {"a" => "o" ; _ => "�"} + "j" + a) ;
  d10 : Str -> NForms -- 2119 ��nitt�j�
    = \s -> dSilakka s (s + "n") (init s + "i" + vowelHarmony (last s)) ;
  d10A : Str -> NForms -- 284 �nkk�
    = \s -> dSilakka s (weakGrade s + "n") (init s + "i" + vowelHarmony (last s)) ;
  d11 : Str -> NForms -- 46 �deema
    = \s -> dSilakka s (weakGrade s + "n") (init s + "i" + vowelHarmony (last s)) ;
  d12 : Str -> NForms -- 1125 �rin�
    = \s -> let a = vowelHarmony (last s) in 
      dSilakka s (s + "n") 
        (init s + case a of {"a" => "o" ; _ => "�"} + "it" + a) ;
  d13 : Str -> NForms -- 157 virtaska
    = \s -> let a = vowelHarmony (last s) in 
      dSilakka s (s + "n") 
        (init s + case a of {"a" => "o" ; _ => "�"} + "j" + a) ;
  d14A : Str -> NForms -- 244 �t�kk�
    = \s -> let a = vowelHarmony (last s) ; ws = weakGrade s in 
      dSilakka s (ws + "n") 
        (init ws + case a of {"a" => "o" ; _ => "�"} + "it" + a) ;
  d15 : Str -> NForms -- 170 �re�
    = dKorkea ;
  d16 : Str -> NForms -- 2 kumpikin
    = \s -> let kumpi = Predef.take 5 s ; kin = Predef.drop 5 s in 
         \\i => (dSuurempi kumpi ! i + kin) ;
  d16A : Str -> NForms -- 20 ylempi
    = dSuurempi ;
  d17 : Str -> NForms -- 38 virkkuu
    = dPaluu ;
  d18 : Str -> NForms -- 84 yksi-ilmeinen --- ?? voi, tee, s��
    = dPuu ;
  d19 : Str -> NForms -- 6 y�
    = dSuo  ;
  d20 : Str -> NForms -- 46 voodoo
    = dPaluu ;
  d21 : Str -> NForms -- 22 tax-free
    = dPuu ;
  d22 : Str -> NForms -- 13 tournedos
    = \s -> nForms10
      s (s + "'n") (s + "'ta") (s + "'na") (s + "'hon")
      (s + "'iden") (s + "'ita") (s + "'ina") (s + "'issa") (s + "'ihin") ;
  d23 : Str -> NForms -- 9 vuohi
    = \s -> dArpi s (init s + "en") ;
  d24 : Str -> NForms -- 20 uni
    = \s -> dArpi s (init s + "en") ;
  d25 : Str -> NForms -- 9 tuomi
    = \s -> dArpi s (init s + "en") ;
  d26 : Str -> NForms -- 113 ��ri
    = \s -> dArpi s (init s + "en") ;
  d27 : Str -> NForms -- 23 vuosi
    = \s -> dArpi s (Predef.tk 2 s + "den") ;
  d28 : Str -> NForms -- 13 virsi
    = \s -> dArpi s (Predef.tk 2 s + "ren") ;
  d28A : Str -> NForms -- 1 j�lsi
    = \s -> dArpi s (Predef.tk 2 s + "len") ;
  d29 : Str -> NForms -- 1 lapsi
    = \s -> let lapsi = dArpi s (init s + "en") in 
       table {2 => Predef.tk 3 s + "ta" ; i => lapsi ! i} ;
  d30 : Str -> NForms -- 2 veitsi
    = \s -> let lapsi = dArpi s (init s + "en") in 
       table {2 => Predef.tk 3 s + "st�" ; i => lapsi ! i} ;
  d31 : Str -> NForms -- 3 yksi
    = \s -> let 
        y = Predef.tk 3 s ;
        a = vowelHarmony y
      in nForms10
        s (y + "hden") (y + "ht" + a) (y + "hten" + a) (y + "hteen")
        (s + "en") (s + a) (s + "n" + a) (s + "ss" + a) (s + "in") ;
  d32 : Str -> NForms -- 20 uumen
    = \s -> dPiennar s (s + "en") ;
  d32A : Str -> NForms -- 54 yst�v�t�r
    = \s -> dPiennar s (strongGrade (init s) + last s + "en") ;
  d33 : Str -> NForms -- 168 v�istin
    = \s -> dLiitin s (init s + "men") ;
  d33A : Str -> NForms -- 181 yllytin
    = \s -> dLiitin s (strongGrade (init s) + "men") ;
  d34 : Str -> NForms -- 1 alaston
    = \s -> let alastom = init s in 
      nForms10
        s (alastom + "an") (s + "ta") (alastom + "ana") (alastom + "aan")
        (alastom + "ien") (alastom + "ia") (alastom + "ina") (alastom + "issa")
        (alastom + "iin") ;
  d34A : Str -> NForms -- 569 ��ret�n
    = dOnneton ;
  d35A : Str -> NForms -- 1 l�mmin
    = \s -> let l�mpim = strongGrade (init s) + "m" in
      nForms10
        s (l�mpim + "�n") (s + "t�") (l�mpim + "�n�") (l�mpim + "��n")
        (l�mpim + "ien") (l�mpim + "i�") (l�mpim + "in�") (l�mpim + "iss�")
        (l�mpim + "iin") ;
  d36 : Str -> NForms -- 11 ylin
    = dSuurin ;
  d37 : Str -> NForms -- 1 vasen
    = \s -> let vasem = init s + "m" in 
      nForms10
        s (vasem + "man") (s + "ta") (vasem + "pana") (vasem + "paan")
        (vasem + "pien") (vasem + "pia") (vasem + "pina") (vasem + "missa")
        (vasem + "piin") ;
  d38 : Str -> NForms -- 4195 �ykk�rim�inen
    = dNainen ;
  d39 : Str -> NForms -- 2730 �r�hdys
    = dJalas ;
  d40 : Str -> NForms -- 2482 �ykk�rim�isyys
    = dLujuus  ;
  d41 : Str -> NForms -- 127 �yr�s
    = \s -> let is = init s in dRae s (is + last is + "n") ;
  d41A : Str -> NForms -- 401 �ljykangas
    = \s -> let is = init s in dRae s (strongGrade is + last is + "n") ;
  d42 : Str -> NForms -- 1 mies
    = \s -> let mieh = init s + "s" in 
      nForms10
        s (mieh + "en") (s + "t�") (mieh + "en�") (mieh + "een")
        (s + "ten") (mieh + "i�") (mieh + "in�") (mieh + "iss�")
        (mieh + "iin") ;
  d43 : Str -> NForms -- 11 tiehyt
    = \s -> dRae s (init s + "en") ;
  d43A : Str -> NForms -- 1 immyt
    = \s -> dRae s (strongGrade (init s) + "en") ;
  d44 : Str -> NForms -- 1 kev�t
    = \s -> let kev� = init s in 
      nForms10
        s (kev� + "�n") (s + "t�") (kev� + "�n�") (kev� + "�seen")
        (s + "iden") (kev� + "it�") (kev� + "in�") (kev� + "iss�")
        (kev� + "isiin") ;
  d45 : Str -> NForms -- 23 yhdes
    = \s -> let yhde = init s ; a = vowelHarmony s in 
      nForms10
        s (yhde + "nnen") (yhde + "tt" + a) (yhde + "nten" + a) (yhde + "nteen")
        (yhde + "nsien") (yhde + "nsi" + a) (yhde + "nsin" + a) (yhde + "nsiss" + a)
        (yhde + "nsiin") ;
  d46 : Str -> NForms -- 1 tuhat
    = \s -> let tuha = init s ; a = vowelHarmony s in 
      nForms10
        s (tuha + "nnen") (tuha + "tt" + a) (tuha + "nten" + a) (tuha + "nteen")
        (tuha + "nsien") (tuha + "nsi" + a) (tuha + "nsin" + a) (tuha + "nsiss" + a)
        (tuha + "nsiin") ;
  d47 : Str -> NForms -- 46 ylirasittunut
    = dOttanut ;
  d48 : Str -> NForms -- 346 �p�re
    = \s -> dRae s (s + "en") ;
  d48A : Str -> NForms -- 481 ��nne
    = \s -> dRae s (strongGrade s + "en") ;
  d49 : Str -> NForms -- 31 vempele
    = \s -> case last s of {
         "e" => dRae s (s + "en") ;
         _ => dPiennar s (s + "en")
        } ;
  d49A : Str -> NForms -- 11 vemmel
    = \s -> dPiennar s (strongGrade (init s) + "len") ;
{-
  d50 : Str -> NForms -- 520 v��r�s��ri
    = \s ->  ;
  d51 : Str -> NForms -- 62 vierasmies
    = \s ->  ;
  c52 : Str -> VForms -- 667 �rjy�
    = \s ->  ;
  c52A : Str -> VForms -- 1568 �ljyynty�
    = \s ->  ;
  c53 : Str -> VForms -- 605 ��nest��
    = \s ->  ;
  c53A : Str -> VForms -- 2121 �r�ht��
    = \s ->  ;
  c54 : Str -> VForms -- 2 pieks��
    = \s ->  ;
  c54A : Str -> VForms -- 316 ��nt��
    = \s ->  ;
  c55A : Str -> VForms -- 7 ylt��
    = \s ->  ;
  c56 : Str -> VForms -- 22 valaa
    = \s ->  ;
  c56A : Str -> VForms -- 28 virkkaa
    = \s ->  ;
  c57A : Str -> VForms -- 3 saartaa
    = \s ->  ;
  c58 : Str -> VForms -- 13 suitsea
    = \s ->  ;
  c58A : Str -> VForms -- 19 tunkea
    = \s ->  ;
  c59A : Str -> VForms -- 1 tuntea
    = \s ->  ;
  c60A : Str -> VForms -- 1 l�hte�
    = \s ->  ;
  c61 : Str -> VForms -- 249 �yski�
    = \s ->  ;
  c61A : Str -> VForms -- 153 v��ntelehti�
    = \s ->  ;
  c62 : Str -> VForms -- 684 �ykk�r�id�
    = \s ->  ;
  c63 : Str -> VForms -- 3 saada
    = \s ->  ;
  c64 : Str -> VForms -- 8 vied�
    = \s ->  ;
  c65 : Str -> VForms -- 1 k�yd�
    = \s ->  ;
  c66 : Str -> VForms -- 268 �rist�
    = \s ->  ;
  c66A : Str -> VForms -- 3 vavista
    = \s ->  ;
  c67 : Str -> VForms -- 704 �llistell�
    = \s ->  ;
  c67A : Str -> VForms -- 634 ��nnell�
    = \s ->  ;
  c68 : Str -> VForms -- 49 viheri�id�
    = \s ->  ;
  c69 : Str -> VForms -- 48 villit�
    = \s ->  ;
  c70 : Str -> VForms -- 3 sy�st�
    = \s ->  ;
  c71 : Str -> VForms -- 2 tehd�
    = \s ->  ;
  c72 : Str -> VForms -- 93 ylet�
    = \s ->  ;
  c72A : Str -> VForms -- 52 yhdet�
    = \s ->  ;
  c73 : Str -> VForms -- 600 �kseerata
    = \s ->  ;
  c73A : Str -> VForms -- 313 �nk�t�
    = \s ->  ;
  c74 : Str -> VForms -- 99 �ljyt�
    = \s ->  ;
  c74A : Str -> VForms -- 72 �nget�
    = \s ->  ;
  c75 : Str -> VForms -- 39 virit�
    = \s ->  ;
  c75A : Str -> VForms -- 9 siit�
    = \s ->  ;
  c76A : Str -> VForms -- 2 tiet��
    = \s ->  ;
  c77 : Str -> VForms -- 3 vipajaa
    = \s ->  ;
  c78 : Str -> VForms -- 31 �hk��
    = \s ->  ;
  c78A : Str -> VForms -- 1 tuikkaa
    = \s ->  ;
  c99 : Str -> VForms -- 5453 �ykk�rim�isesti
    = \s ->  ;
-}

}

