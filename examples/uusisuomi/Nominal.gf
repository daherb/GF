--# -path=.:alltenses

resource Nominal = ResFin ** open MorphoFin,Declensions,CatFin,Prelude in {

  flags optimize=noexpand ;

  oper

--  mkN = overload {
    mk1N : (talo : Str) -> N = \s -> nForms2N (nForms1 s) ;
    mk2N : (talo,talon : Str) -> N = \s,t -> nForms2N (nForms2 s t) ;
    mk3N : (talo,talon,taloja : Str) -> N = \s,t,u -> nForms2N (nForms3 s t u) ;
    mk4N : (talo,talon,taloa,taloja : Str) -> N = \s,t,u,v -> 
      nForms2N (nForms4 s t u v) ;
--  } ;

  nForms1 : Str -> NForms = \ukko ->
    let
      ukk = init ukko ;
      uko = weakGrade ukko ;
      ukon = uko + "n" ;
      renka = Declensions.strongGrade (init ukko) ;
      rake = Declensions.strongGrade ukko ;
    in
    case ukko of {
      _ + "nen" => dNainen ukko ;
      _ + ("aa" | "ee" | "ii" | "oo" | "uu" | "yy" |"��"|"��") => dPuu ukko ;
      _ + ("ai" | "ei" | "oi" | "ui" | "yi" | "�i" | "�i") => dPuu ukko ;
      _ + ("ie" | "uo" | "y�") => dSuo ukko ;
      _ + ("ea" | "e�") => dKorkea ukko ;
      _ + "is" => dKaunis ukko ;
      _ + ("i" | "u") + "n" => dLiitin ukko (renka + "men") ;
      _ + ("ton" | "t�n") => dOnneton ukko ;
      _ + ("ut" | "yt") => dRae ukko (ukk + "en") ;
      _ + ("as" | "�s") => dRae ukko (renka + last renka + "n") ;
      _ + "e" => dRae ukko (rake + "en") ;
      _ + "s" => dJalas ukko ; 
      _ + "i" +o@("o"|"�") => dSilakka ukko (ukko+"n") (ukko+"it"+getHarmony o);
      _ + "i" + "a" => dSilakka ukko (ukko + "n") (ukk + "oita") ;
      _ + "i" + "�" => dSilakka ukko (ukko + "n") (ukk + "�it�") ;
      _ + ("a" | "o" | "u" | "y" | "�" | "�") => dUkko ukko ukon ;
      _ + "i" => dPaatti ukko ukon ;
      _ + ("ar" | "�r") => dPiennar ukko (renka + "ren") ;
      _ + "e" + ("l" | "n") => dPiennar ukko (ukko + "en") ;
      _ => dUnix ukko
    } ;   

    nForms2 : (_,_ : Str) -> NForms = \ukko,ukon -> 
      let
        ukk = init ukko ;
      in
      case <ukko,ukon> of {
        <_ + ("aa" | "ee" | "ii" | "oo" | "uu" | "yy" | "��" | "��" | 
              "ie" | "uo" | "y�" | "ea" | "e�" | 
              "ia" | "i�" | "io" | "i�"), _ + "n"> => 
           nForms1 ukko ; --- to protect
        <_ + ("a" | "o" | "u" | "y" | "�" | "�"), _ + "n"> => 
          dUkko ukko ukon ;  -- auto,auton
        <arp + "i", arv + "en"> => dArpi ukko ukon ;
        <arp + "i", _ + "i" + ("a" | "�")> =>         -- for b-w compat.
          dArpi ukko (init (weakGrade ukko) + "en") ;
        <terv + "e", terv + "een"> => 
          dRae ukko (terv + "een") ;
        <nukk + "e", nuk + "en"> => dNukke ukko ukon ;
        <_ + ("us" | "ys"), _ + "den"> => dLujuus ukko ;
        <_, _ + ":n"> => dSDP ukko ;
        <_, _ + "n"> => nForms1 ukko ;
        _ => 
          Predef.error (["second argument should end in n, not"] ++ ukon)
       } ;

    nForms3 : (_,_,_ : Str) -> NForms = \ukko,ukon,ukkoja -> 
      let
        ukot = nForms2 ukko ukon ; 
      in
      case <ukko,ukon,ukkoja> of {
        <_ + "ea", _ + "ean", _ + "oita"> => 
          dSilakka ukko ukon ukkoja ;  -- idea, but not korkea
        <_ + ("aa" | "ee" | "ii" | "oo" | "uu" | "yy" | "��" | "��" | 
              "ie" | "uo" | "y�" | "ea" | "e�" | 
              "ia" | "i�" | "io" | "i�"), _ + "n"> => 
          nForms1 ukko ; --- to protect --- how to get "dioja"?
        <_ + "a" | "�" | "o" | "�", _ + "n", _ + ("a" | "�")> => 
          dSilakka ukko ukon ukkoja ;
        <_ + "i", _ + "n", _ + ("eita" | "eit�")> => 
          dTohtori ukko ;
        <_, _ + "n", _ + ("a" | "�")> => ukot ;
        _ => 
          Predef.error 
           (["last arguments should end in n and a/�, not"] ++ ukon ++ ukkoja)
      } ;

    nForms4 : (_,_,_,_ : Str) -> NForms = \ukko,ukon,ukkoa,ukkoja -> 
      let
        ukot = nForms3 ukko ukon ukkoja ;
      in
      case <ukko,ukon,ukkoa,ukkoja> of {
        <_,_ + "n", _ + ("a" | "�"), _ + ("a" | "�")> => 
          table {
            2 => ukkoa ;
            n => ukot ! n
          } ;
        _ => 
          Predef.error 
            (["last arguments should end in n, a/�, and a/�, not"] ++ 
            ukon ++ ukkoa ++ ukkoja)
      } ;

}
