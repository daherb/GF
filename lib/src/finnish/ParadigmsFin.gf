--# -path=.:../abstract:../common:../../prelude

--1 Finnish Lexical Paradigms
--
-- Aarne Ranta 2003--2008
--
-- This is an API to the user of the resource grammar 
-- for adding lexical items. It gives functions for forming
-- expressions of open categories: nouns, adjectives, verbs.
-- 
-- Closed categories (determiners, pronouns, conjunctions) are
-- accessed through the resource syntax API and $Structural.gf$. 
--
-- The main difference with $MorphoFin.gf$ is that the types
-- referred to are compiled resource grammar types. We have moreover
-- had the design principle of always having existing forms, rather
-- than stems, as string arguments of the paradigms.
--
-- The structure of functions for each word class $C$ is the following:
-- there is a polymorphic constructor $mkC$, which takes one or
-- a few arguments. In Finnish, one argument is enough in 80-90% of
-- cases in average.

resource ParadigmsFin = open 
  (Predef=Predef), 
  Prelude, 
  MorphoFin,
  CatFin
  in {

  flags optimize=noexpand ;

--2 Parameters 
--
-- To abstract over gender, number, and (some) case names, 
-- we define the following identifiers. The application programmer
-- should always use these constants instead of the constructors
-- defined in $ResFin$.

oper
  Number   : Type ;

  singular : Number ;
  plural   : Number ;

  Case        : Type ;
  nominative  : Case ; 
  genitive    : Case ; 
  partitive   : Case ; 
  essive      : Case ; 
  translative : Case ; 
  inessive    : Case ; 
  elative     : Case ; 
  illative    : Case ; 
  adessive    : Case ; 
  ablative    : Case ; 
  allative    : Case ;

  infFirst, infElat, infIllat : InfForm ;

-- The following type is used for defining *rection*, i.e. complements
-- of many-place verbs and adjective. A complement can be defined by
-- just a case, or a pre/postposition and a case.

  prePrep     : Case -> Str -> Prep ;  -- ilman, partitive
  postPrep    : Case -> Str -> Prep ;  -- takana, genitive
  postGenPrep :         Str -> Prep ;  -- takana
  casePrep    : Case ->        Prep ;  -- adessive

--2 Nouns

-- The worst case gives ten forms.
-- In practice just a couple of forms are needed to define the different
-- stems, vowel alternation, and vowel harmony.

oper

-- The regular noun heuristic takes just one form (singular
-- nominative) and analyses it to pick the correct paradigm.
-- It does automatic grade alternation, and is hence not usable
-- for words like "auto" (whose genitive would become "audon").
--
-- If the one-argument paradigm does not give the correct result, one can try and give 
-- two or three forms. Most notably, the two-argument variant is used
-- for nouns like "kivi - kivi�", which would otherwise become like
-- "rivi - rivej�". Three arguments are used e.g. for 
-- "auto - auton - autoja", which would otherwise become
-- "auto - audon".

  mkN : overload {
    mkN : (talo : Str) -> N ;
    mkN : (savi,savia : Str) -> N ;
    mkN : (vesi,veden,vesi� : Str) -> N ;
    mkN : (vesi,veden,vesi�,vett� : Str) -> N ;
    mkN : (olo,olon,olona,oloa,oloon,olojen,oloja,oloina,oloissa,oloihin : Str) -> N ;
    mkN : (pika : Str) -> (juna  : N) -> N ;
    mkN : (oma : N)    -> (tunto : N) -> N ; 
  } ;

-- Nouns used as functions need a case, of which the default is
-- the genitive.

  mkN2 : overload {
    mkN2 : N -> N2 ;
    mkN2 : N -> Prep -> N2
    } ;

  mkN3  : N -> Prep -> Prep -> N3 ;

-- Proper names can be formed by using declensions for nouns.
-- The plural forms are filtered away by the compiler.

  mkPN : overload {
    mkPN : Str -> PN ;
    mkPN : N -> PN
    } ;

--2 Adjectives

-- Non-comparison one-place adjectives are just like nouns.
-- The regular adjectives are based on $regN$ in the positive.
-- Comparison adjectives have three forms. 
-- The comparative and the superlative
-- are always inflected in the same way, so the nominative of them is actually
-- enough (except for the superlative "paras" of "hyv�").

  mkA : overload {
    mkA : Str -> A ;
    mkA : N -> A ;
    mkA : N -> (kivempi,kivin : Str) -> A ;
    mkA : (hyva,parempi,paras : N) -> (hyvin,paremmin,parhaiten : Str) -> A ;
  } ;

-- Two-place adjectives need a case for the second argument.

  mkA2 : A -> Prep -> A2 = \a,p -> a ** {c2 = p ; lock_A2 = <>};



--2 Verbs
--
-- The grammar does not cover the potential mood and some nominal
-- forms. One way to see the coverage is to linearize a verb to
-- a table.
-- The worst case needs twelve forms, as shown in the following.

  mkV : overload {
    mkV : (huutaa : Str) -> V ;
    mkV : (huutaa,huusi : Str) -> V ;
    mkV : (huutaa,huudan,huusi : Str) -> V ;
    mkV : (
      huutaa,huudan,huutaa,huutavat,huutakaa,huudetaan,
      huusin,huusi,huusisi,huutanut,huudettu,huutanee : Str) -> V ;
  } ;

-- All the patterns above have $nominative$ as subject case.
-- If another case is wanted, use the following.

  caseV : Case -> V -> V ;

-- The verbs "be" is special.

  vOlla : V ;


--3 Two-place verbs
--
-- Two-place verbs need an object case, and can have a pre- or postposition.
-- The default is direct (accusative) object. There is also a special case
-- with case only. The string-only argument case yields a regular verb with
-- accusative object.

  mkV2 : overload {
    mkV2 : Str -> V2 ;
    mkV2 : V -> V2 ;
    mkV2 : V -> Case -> V2 ;
    mkV2 : V -> Prep -> V2 ;
    } ;


--3 Three-place verbs
--
-- Three-place (ditransitive) verbs need two prepositions, of which
-- the first one or both can be absent.

  mkV3     : V -> Prep -> Prep -> V3 ;  -- puhua, allative, elative
  dirV3    : V -> Case -> V3 ;          -- siirt��, (accusative), illative
  dirdirV3 : V         -> V3 ;          -- antaa, (accusative), (allative)


--3 Other complement patterns
--
-- Verbs and adjectives can take complements such as sentences,
-- questions, verb phrases, and adjectives.

  mkV0  : V -> V0 ;
  mkVS  : V -> VS ;
  mkV2S : V -> Prep -> V2S ;
  mkVV  : V -> VV ;
  mkVVf : V -> InfForm -> VV ;
  mkV2V : V -> Prep -> V2V ;
  mkV2Vf : V -> Prep -> InfForm -> V2V ;
  mkVA  : V -> Prep -> VA ;
  mkV2A : V -> Prep -> Prep -> V2A ;
  mkVQ  : V -> VQ ;
  mkV2Q : V -> Prep -> V2Q ;

  mkAS  : A -> AS ;
  mkA2S : A -> Prep -> A2S ;
  mkAV  : A -> AV ;
  mkA2V : A -> Prep -> A2V ;

-- Notice: categories $AS, A2S, AV, A2V$ are just $A$, 
-- and the second argument is given
-- as an adverb. Likewise 
-- $V0$ is just $V$.

  V0 : Type ;
  AS, A2S, AV, A2V : Type ;

--.
-- The definitions should not bother the user of the API. So they are
-- hidden from the document.

  Case = MorphoFin.Case ;
  Number = MorphoFin.Number ;

  singular = Sg ;
  plural = Pl ;

  nominative = Nom ;
  genitive = Gen ;
  partitive = Part ;
  translative = Transl ;
  inessive = Iness ;
  essive  = Ess ;
  elative = Elat ;
  illative = Illat ;
  adessive = Adess ;
  ablative = Ablat ;
  allative = Allat ;

  infFirst = Inf1 ; infElat = Inf3Elat ; infIllat = Inf3Illat ;

  prePrep  : Case -> Str -> Prep = 
    \c,p -> {c = NPCase c ; s = p ; isPre = True ; lock_Prep = <>} ;
  postPrep : Case -> Str -> Prep =
    \c,p -> {c = NPCase c ; s = p ; isPre = False ; lock_Prep = <>} ;
  postGenPrep p = {
    c = NPCase genitive ; s = p ; isPre = False ; lock_Prep = <>} ;
  casePrep : Case -> Prep =
    \c -> {c = NPCase c ; s = [] ; isPre = True ; lock_Prep = <>} ;
  accPrep =  {c = NPAcc ; s = [] ; isPre = True ; lock_Prep = <>} ;

  mkN = overload {
    mkN : (talo : Str) -> N = mk1N ;
    --  \s -> nForms2N (nForms1 s) ;
    mkN : (talo,talon : Str) -> N = mk2N ;
    --  \s,t -> nForms2N (nForms2 s t) ;
    mkN : (talo,talon,taloja : Str) -> N = mk3N ;
    --  \s,t,u -> nForms2N (nForms3 s t u) ;
    mkN : (talo,talon,taloja,taloa : Str) -> N = mk4N ;
    --  \s,t,u,v -> nForms2N (nForms4 s t u v) ;
    mkN : 
      (talo,talon,taloa,talona,taloon,talojen,taloja,taloina,taloissa,taloihin
        : Str) -> N = mk10N ;
    mkN : (sora : Str) -> (tie : N) -> N = mkStrN ;
    mkN : (oma,tunto : N) -> N = mkNN ;
  } ;

  mk1A : Str -> A = \jalo -> aForms2A (nforms2aforms (nForms1 jalo)) ;
  mkNA : N -> A = \suuri -> aForms2A (nforms2aforms (n2nforms suuri)) ;

  mk1N : (talo : Str) -> N = \s -> nForms2N (nForms1 s) ;
  mk2N : (talo,talon : Str) -> N = \s,t -> nForms2N (nForms2 s t) ;
  mk3N : (talo,talon,taloja : Str) -> N = \s,t,u -> nForms2N (nForms3 s t u) ;
  mk4N : (talo,talon,taloa,taloja : Str) -> N = \s,t,u,v -> 
      nForms2N (nForms4 s t u v) ;
  mk10N : 
      (talo,talon,taloa,talona,taloon,talojen,taloja,taloina,taloissa,taloihin
        : Str) -> N = \a,b,c,d,e,f,g,h,i,j -> 
        nForms2N (nForms10 a b c d e f g h i j) ;

  mkStrN : Str -> N -> N = \sora,tie -> {
    s = \\c => sora + tie.s ! c ; lock_N = <>
    } ;
  mkNN : N -> N -> N = \oma,tunto -> {
    s = \\c => oma.s ! c + tunto.s ! c ; lock_N = <>
    } ; ---- TODO: oma in possessive suffix forms

  nForms1 : Str -> NForms = \ukko ->
    let
      ukk = init ukko ;
      uko = weakGrade ukko ;
      ukon = uko + "n" ;
      o = case last ukko of {"�" => "�" ; "a" => "o"} ; -- only used then 
      renka = strongGrade (init ukko) ;
      rake = strongGrade ukko ;
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
      _ + "e" => dRae ukko (rake + "en") ;
      _ + ("ut" | "yt") => dOttanut ukko ;
      _ + ("as" | "�s") => dRae ukko (renka + last renka + "n") ;
      _ + ("uus" | "yys" | "eus" | "eys") => dLujuus ukko ;
      _ + "s" => dJalas ukko ; 

{- heuristics for 3-syllable nouns ending a/�
      _ + ("a" | "e" | "i" | "o" | "u" | "y" | "�" | "�") + ? + 
          _ + "i" + ? + a@("a" | "�") =>  
          dSilakka ukko (ukko + "n") (ukk + o + "it" + a) ;
      _ + ("a" | "e" | "i" | "o" | "u" | "y" | "�" | "�") + ? + _ + 
          ("a" | "e" | "o" | "u" | "y" | "�" | "�") + 
          ("l" | "r" | "n") + a@("a" | "�") =>  
          dSilakka ukko (ukko + "n") (ukk + o + "it" + a) ;
      _ + ("a" | "e" | "i" | "o" | "u" | "y" | "�" | "�") + ? + _ + 
          ("a" | "e" | "i" | "o" | "u" | "y" | "�" | "�") + 
          ("n" | "k" | "s") + "k" + a@("a" | "�") =>  
          dSilakka ukko (uko + "n") (init uko + o + "it" + a) ;
      _ + ("a" | "e" | "i" | "o" | "u" | "y" | "�" | "�") + ? + _ + 
          ("a" | "e" | "i" | "o" | "u" | "y" | "�" | "�") + 
          ("n" | "t" | "s") + "t" + a@("a" | "�") =>  
          dSilakka ukko (uko + "n") (ukk + o + "j" + a) ;
      _ + ("a" | "e" | "i" | "o" | "u") + ? + _ + 
          ("a" | "e" | "o" | "u") + ? + "a" =>  
          dSilakka ukko (ukko + "n") (ukk + "ia") ;
-}
      _ + "i" +o@("o"|"�") => dSilakka ukko (ukko+"n") (ukko+"it"+getHarmony o);
      _ + "i" + "a" => dSilakka ukko (ukko + "n") (ukk + "oita") ;
      _ + "i" + "�" => dSilakka ukko (ukko + "n") (ukk + "�it�") ;
      _ + ("a" | "o" | "u" | "y" | "�" | "�") => dUkko ukko ukon ;
      _ + "i" => dPaatti ukko ukon ;
      _ + ("ar" | "�r") => dPiennar ukko (renka + "ren") ;
      _ + "e" + ("l" | "n") => dPiennar ukko (ukko + "en") ;
      _ => dUnix ukko
    } ;   


    nForms2 : (_,_ : Str) -> NForms = \ukko,ukkoja -> 
      let
        ukot = nForms1 ukko ; 
        ukon = weakGrade ukko + "n" ;
      in
      case <ukko,ukkoja> of {
        <_ + "ea", _ + "oita"> => 
          dSilakka ukko ukon ukkoja ;  -- idea, but not korkea
        <_ + ("aa" | "ee" | "ii" | "oo" | "uu" | "yy" | "��" | "��" | 
              "ie" | "uo" | "y�" | "ea" | "e�" | 
              "ia" | "i�" | "io" | "i�"), _ + ("a" | "�")> => 
          nForms1 ukko ; --- to protect --- how to get "dioja"?
        <_ + ("a" | "�" | "o" | "�"), _ + ("a" | "�")> => 
          dSilakka ukko ukon ukkoja ;
        <arp + "i", _ + "i" + ("a" | "�")> =>
          dArpi ukko (init (weakGrade ukko) + "en") ;
        <_ + "i", _ + ("eita" | "eit�")> => 
          dTohtori ukko ;
        <_ + ("ut" | "yt"),_ + ("uita" | "yit�")>  => dRae ukko (init ukko + "en") ;
        <_ + "e", nuk + ("eja" | "ej�")> => 
          dNukke ukko ukon ;
        <_, _ + ":" + _ + ("a" | "�")> => dSDP ukko ;
        <_ + ("l" | "n" | "r" | "s"), _ + ("eja" | "ej�")> => dUnix ukko ;
        <_, _ + ("a" | "�")> => ukot ;
        _ => 
          Predef.error 
           (["last argument should end in a/�, not"] ++ ukkoja)
      } ;

    nForms3 : (_,_,_ : Str) -> NForms = \ukko,ukon,ukkoja -> 
      let
        ukk = init ukko ;
        ukot = nForms2 ukko ukkoja ;
      in
      case <ukko,ukon> of {
        <_ + ("aa" | "ee" | "ii" | "oo" | "uu" | "yy" | "��" | "��" | 
              "ie" | "uo" | "y�" | "ea" | "e�" | 
              "ia" | "i�" | "io" | "i�" | "ja" | "j�"), _ + "n"> => 
           ukot ; --- to protect
        <_ + ("a" | "o" | "u" | "y" | "�" | "�"), _ + "n"> => 
          dSilakka ukko ukon ukkoja ;  -- auto,auton
        <_ + "mpi", _ + ("emman" | "emm�n")> => dSuurempi ukko ;
        <_ + "in", _ + ("imman" | "imm�n")> => dSuurin ukko ;
        <terv + "e", terv + "een"> => 
          dRae ukko ukon ;
        <taiv + ("as" | "�s"), taiv + ("aan" | "��n")> => 
          dRae ukko ukon ;
        <nukk + "e", nuk + "een"> => dRae ukko ukon ;
        <arp + "i", arv + "en"> => dArpi ukko ukon ;
        <_ + ("us" | "ys"), _ + "den"> => dLujuus ukko ;
        <_, _ + ":n"> => dSDP ukko ;
        <_, _ + "n"> => ukot ;
        _ => 
          Predef.error (["second argument should end in n, not"] ++ ukon)
       } ;

    nForms4 : (_,_,_,_ : Str) -> NForms = \ukko,ukon,ukkoja,ukkoa -> 
      let
        ukot = nForms3 ukko ukon ukkoja ;
      in
      case <ukko,ukon,ukkoja,ukkoa> of {
        <_,_ + "n", _ + ("a" | "�"), _ + ("a" | "�")> => 
          table {
            2 => ukkoa ;
            n => ukot ! n
          } ;
        _ => 
          Predef.error 
            (["last arguments should end in n, a/�, and a/�, not"] ++ 
            ukon ++ ukkoja ++ ukkoa)
      } ;

  mkN2 = overload {
    mkN2 : N -> N2 = \n -> mmkN2 n (casePrep genitive) ;
    mkN2 : N -> Prep -> N2 = mmkN2
    } ;

  mmkN2 : N -> Prep -> N2 = \n,c -> n ** {c2 = c ; isPre = mkIsPre c ; lock_N2 = <>} ;
  mkN3 = \n,c,e -> n ** {c2 = c ; c3 = e ; 
    isPre = mkIsPre c  ; -- matka Lontoosta Pariisiin
    isPre2 = mkIsPre e ;          -- Suomen voitto Ruotsista
    lock_N3 = <>
    } ;
  
  mkIsPre : Prep -> Bool = \p -> case p.c of {
    NPCase Gen => notB p.isPre ;  -- Jussin veli (prep is <Gen,"",True>, isPre becomes False)
    _ => True                     -- syyte Jussia vastaan, puhe Jussin puolesta
    } ;

  mkPN = overload {
    mkPN : Str -> PN = mkPN_1 ;
    mkPN : N -> PN = \s -> {s = \\c => s.s ! NCase Sg c ; lock_PN = <>} ;
    } ;

  mkPN_1 : Str -> PN = \s -> {s = \\c => (mk1N s).s ! NCase Sg c ; lock_PN = <>} ;

-- adjectives

  mkA = overload {
    mkA : Str -> A  = mkA_1 ;
    mkA : N -> A = \n -> noun2adjDeg n ** {lock_A = <>} ;
    mkA : N -> (kivempaa,kivinta : Str) -> A = regAdjective ;
--    mkA : (hyva,parempi,paras : N) -> (hyvin,paremmin,parhaiten : Str) -> A ;
  } ;

  mkA_1 : Str -> A = \x -> noun2adjDeg (mk1N x) ** {lock_A = <>} ;

-- auxiliaries
  mkAdjective : (_,_,_ : Adj) -> A = \hyva,parempi,paras -> 
    {s = table {
      Posit  => hyva.s ;
      Compar => parempi.s ;
      Superl => paras.s
      } ;
     lock_A = <>
    } ;
  regAdjective : Noun -> Str -> Str -> A = \kiva, kivempi, kivin ->
    mkAdjective 
      (noun2adj kiva) 
      (noun2adjComp False (nForms2N (dSuurempi kivempi))) 
      (noun2adjComp False (nForms2N (dSuurin kivin))) ;
  noun2adjDeg : Noun -> Adjective = \suuri -> 
    regAdjective 
      suuri 
      (init (suuri.s ! NCase Sg Gen) + "mpi")  ---- to check
      (suuri.s ! NInstruct) ; ----
    



-- verbs

  mkV = overload {
    mkV : (huutaa : Str) -> V = mk1V ;
    mkV : (huutaa,huusi : Str) -> V = mk2V ;
    mkV : (huutaa,huudan,huusi : Str) -> V = mk3V ;
    mkV : (
      huutaa,huudan,huutaa,huutavat,huutakaa,huudetaan,
      huusin,huusi,huusisi,huutanut,huudettu,huutanee : Str) -> V = mk12V ;
  } ;

  mk1V : Str -> V = \s -> 
    let vfs = vforms2V (vForms1 s) in 
      vfs ** {sc = NPCase Nom ; lock_V = <>} ;
  mk2V : (_,_ : Str) -> V = \x,y -> 
    let vfs = vforms2V (vForms2 x y) in vfs ** {sc = NPCase Nom ; lock_V = <>} ;
  mk3V : (huutaa,huudan,huusi : Str) -> V = \x,_,y -> mk2V x y ; ----
  mk12V : (
      huutaa,huudan,huutaa,huutavat,huutakaa,huudetaan,
      huusin,huusi,huusisi,huutanut,huudettu,huutanee : Str) -> V = 
     \a,b,c,d,e,f,g,h,i,j,k,l -> 
        vforms2V (vForms12 a b c d e f g h i j k l) ** {sc = NPCase Nom ; lock_V = <>} ;

  vForms1 : Str -> VForms = \ottaa ->
    let
      a = last ottaa ;
      otta = init ottaa ; 
      ott  = init otta ;
      ots  = init ott + "s" ;
      ota  = weakGrade otta ;
      otin = init (strongGrade (init ott)) + "elin" ;
      ot   = init ota ;
    in
    case ottaa of {
      _ + ("e" | "i" | "o" | "u" | "y" | "�") + ("a" | "�") =>
        cHukkua ottaa (ota + "n") ;
      _ + ("l" | "n" | "r") + ("taa" | "t��") => 
        cOttaa ottaa (ota + "n") (ots + "in") (ots + "i") ;
      ("" | ?) + ("a" | "e" | "i" | "o" | "u") + ? + _ + 
        ("a" | "e" | "i" | "o" | "u") + _ + "aa" => 
        cOttaa ottaa (ota + "n") (ot + "in") (ott + "i") ;
      ("" | ?) + ("a" | "e" | "i") + _ + "aa" => 
        cOttaa ottaa (ota + "n") (ot + "oin") (ott + "oi") ;
      _ + ("aa" | "��") => 
        cOttaa ottaa (ota + "n") (ot + "in") (ott + "i") ;
      _ + ("ella" | "ell�") => 
        cKuunnella ottaa otin ;
      _ + ("osta" | "�st�") => 
        cJuosta ottaa (init ott + "ksen") ;
      _ + ("st" | "nn" | "ll" | "rr") + ("a" | "�") => 
        cJuosta ottaa (ott + "en") ;
      _ + ("ita" | "it�") => 
        cHarkita ottaa ;
      _ + ("eta" | "et�" | "ota" | "ata" | "uta" | "yt�" | "�t�" | "�t�") => 
        cPudota ottaa (strongGrade ott + "si") ;
      _ + ("da" | "d�") => 
        cJuoda ottaa ;
      _ => Predef.error (["expected infinitive, found"] ++ ottaa) 
    } ;   

  vForms2 : (_,_ : Str) -> VForms = \huutaa,huusi ->
    let
      huuda = weakGrade (init huutaa) ;
      huusin = weakGrade huusi + "n" ;
      autoin = weakGrade (init huusi) + "in" ;
    in 
    case <huutaa,huusi> of {
      <_ + ("taa" | "t��"), _ + ("oi" | "�i")> =>
        cOttaa huutaa (huuda + "n") autoin huusi ;
      <_ + ("aa" | "��"), _ + "i"> =>
        cOttaa huutaa (huuda + "n") huusin huusi ;
      <_ + ("eta" | "et�"), _ + "eni"> =>
        cValjeta huutaa huusi ;
      <_ + ("sta" | "st�"), _ + "si"> =>
        vForms1 huutaa ; -- pest�, halkaista
      <_ + ("ta" | "t�"), _ + "si"> =>
        cPudota huutaa huusi ;
      <_ + ("lla" | "ll�"), _ + "li"> =>
        cKuunnella huutaa huusin ;
      _ => vForms1 huutaa
      } ;



  caseV c v = {s = v.s ; sc = NPCase c ; qp = v.qp ; lock_V = <>} ;

  vOlla = verbOlla ** {sc = NPCase Nom ; qp = "ko" ; lock_V = <>} ; ---- lieneek�

  mk2V2 : V -> Prep -> V2 = \v,c -> v ** {c2 = c ; lock_V2 = <>} ;
  caseV2 : V -> Case -> V2 = \v,c -> mk2V2 v (casePrep c) ; 
  dirV2 v = mk2V2 v accPrep ;

  mkAdv : Str -> Adv = \s -> {s = s ; lock_Adv = <>} ;

  mkV2 = overload {
    mkV2 : Str -> V2 = \s -> dirV2 (mk1V s) ;
    mkV2 : V -> V2 = dirV2 ;
    mkV2 : V -> Case -> V2 = caseV2 ;
    mkV2 : V -> Prep -> V2 = mk2V2 ;
    } ;

  mk2V2 : V -> Prep -> V2 ;
  caseV2 : V -> Case -> V2 ;
  dirV2 : V -> V2 ;

  mkV3 v p q = v ** {c2 = p ; c3 = q ; lock_V3 = <>} ; 
  dirV3 v p = mkV3 v accPrep (casePrep p) ;
  dirdirV3 v = dirV3 v allative ;

  mkVS  v = v ** {lock_VS = <>} ;
  mkVV  v = mkVVf v infFirst ;
  mkVVf  v f = v ** {vi = f ; lock_VV = <>} ;
  mkVQ  v = v ** {lock_VQ = <>} ;

  V0 : Type = V ;
  AS, A2S, AV : Type = A ;
  A2V : Type = A2 ;

  mkV0  v = v ** {lock_V = <>} ;
  mkV2S v p = mk2V2 v p ** {lock_V2S = <>} ;
  mkV2V v p = mkV2Vf v p infIllat ;
  mkV2Vf v p f = mk2V2 v p ** {vi = f ; lock_V2V = <>} ;

  mkVA  v p = v ** {c2 = p ; lock_VA = <>} ;
  mkV2A v p q = v ** {c2 = p ; c3 = q ; lock_V2A = <>} ;
  mkV2Q v p = mk2V2 v p ** {lock_V2Q = <>} ;

  mkAS  v = v ** {lock_A = <>} ;
  mkA2S v p = mkA2 v p ** {lock_A = <>} ;
  mkAV  v = v ** {lock_A = <>} ;
  mkA2V v p = mkA2 v p ** {lock_A2 = <>} ;

} ;
