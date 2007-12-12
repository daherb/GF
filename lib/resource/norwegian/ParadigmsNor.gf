--# -path=.:../scandinavian:../common:../abstract:../../prelude

--1 Norwegian Lexical Paradigms
--
-- Aarne Ranta 2003
--
-- This is an API for the user of the resource grammar 
-- for adding lexical items. It gives functions for forming
-- expressions of open categories: nouns, adjectives, verbs.
-- It covers the "bokm�l" variant of Norwegian.
--
-- Closed categories (determiners, pronouns, conjunctions) are
-- accessed through the resource syntax API, $Structural$. 
--
-- The main difference with $MorphoNor.gf$ is that the types
-- referred to are compiled resource grammar types. We have moreover
-- had the design principle of always having existing forms, rather
-- than stems, as string arguments of the paradigms.
--
-- The structure of functions for each word class $C$ is the following:
-- first we give a handful of patterns that aim to cover all
-- regular cases. Then we give a worst-case function $mkC$, which serves as an
-- escape to construct the most irregular words of type $C$.
-- However, this function should only seldom be needed: we have a
-- separate module [``IrregNor`` ../../norwegian/IrregNor],
-- which covers irregularly inflected verbs.

resource ParadigmsNor = 
  open 
    (Predef=Predef), 
    Prelude, 
    CommonScand, 
    ResNor, 
    MorphoNor, 
    CatNor in {

--2 Parameters 
--
-- To abstract over gender names, we define the following identifiers.

oper
  Gender : Type ; 

  masculine : Gender ;
  feminine  : Gender ;
  neutrum   : Gender ;

-- To abstract over number names, we define the following.

  Number : Type ; 

  singular : Number ;
  plural   : Number ;

-- To abstract over case names, we define the following.

  Case : Type ;

  nominative : Case ;
  genitive   : Case ;

-- Prepositions used in many-argument functions are just strings.

  mkPrep : Str -> Prep ;
  noPrep : Prep ;        -- empty string

--2 Nouns

-- The regular function takes the singular indefinite form
-- and computes the other forms and the gender by a heuristic.
-- The heuristic is that nouns ending "e" are feminine like "kvinne",
-- all others are masculine like "bil". 
-- Giving gender manually makes the heuristic more reliable.
-- One can also compute the gender from the definite form.
-- gender is computed from the definite form.
-- If in doubt, use the $cc$ command to test!
-- In the worst case, give all four forms. The gender is computed from the
-- last letter of the second form (if "n", then $utrum$, otherwise $neutrum$).

  mkN : overload {
    mkN : Str -> N ;
    mkN : Str -> Gender -> N ;
    mkN : (bil,bilen : Str) -> N ;
    mkN  : (dreng,drengen,drenger,drengene : Str) -> N
  } ;



--3 Compound nouns 
--
-- All the functions above work quite as well to form compound nouns,
-- such as "fotboll". 


--3 Relational nouns 
-- 
-- Relational nouns ("datter til x") need a preposition. 

  mkN2 : N -> Prep -> N2 ;

-- The most common preposition is "av", and the following is a
-- shortcut for regular, $nonhuman$ relational nouns with "av".

  regN2 : Str -> Gender -> N2 ;

-- Use the function $mkPrep$ or see the section on prepositions below to  
-- form other prepositions.
--
-- Three-place relational nouns ("forbindelse fra x til y") 
-- need two prepositions.

  mkN3 : N -> Prep -> Prep -> N3 ;


--3 Relational common noun phrases
--
-- In some cases, you may want to make a complex $CN$ into a
-- relational noun (e.g. "den gamle kongen av"). However, $N2$ and
-- $N3$ are purely lexical categories. But you can use the $AdvCN$
-- and $PrepNP$ constructions to build phrases like this.

-- 
--3 Proper names and noun phrases
--
-- Proper names, with a regular genitive, are formed as follows
-- Sometimes you can reuse a common noun as a proper name, e.g. "Bank".

  mkPN : overload {
    mkPN : Str -> PN ;       -- masculine
    mkPN : Str -> Gender -> PN ;  
    mkPN : N -> PN ;
    } ;


--2 Adjectives

-- The regular pattern works for many adjectives, e.g. those ending
-- with "ig". Two, five, or at worst five forms are sometimes needed.

  mkA : overload {
    mkA : (fin : Str) -> A ;
    mkA : (fin,fint : Str) -> A ;
    mkA : (galen,galet,galne : Str) -> A ;
    mkA : (stor,stort,store,storre,storst : Str) -> A ;

-- If comparison is formed by "mer", "mest", as in general for
-- long adjective, the following pattern is used:

    mkA : A -> A ; -- -/mer/mest norsk
  } ;
 

--3 Two-place adjectives
--
-- Two-place adjectives need a preposition for their second argument.

  mkA2 : A -> Prep -> A2 ;



--2 Adverbs

-- Adverbs are not inflected. Most lexical ones have position
-- after the verb. Some follow the verb (e.g. "altid").

  mkAdv : Str -> Adv ;  -- e.g. her
  mkAdV : Str -> AdV ;  -- e.g. altid

-- Adverbs modifying adjectives and sentences can also be formed.

  mkAdA : Str -> AdA ;


--2 Verbs
--

  mkV : overload {

-- The 'regular verb' function is the first conjugation.

    mkV : (snakke : Str) -> V ;

-- The almost regular verb function needs the infinitive and the preteritum.

    mkV : (leve,levde : Str) -> V ;

-- There is an extensive list of irregular verbs in the module $IrregNor$.
-- In practice, it is enough to give three forms, as in school books.

    mkV : (drikke, drakk, drukket  : Str) -> V ;

-- The worst case needs six forms.

    mkV : (spise,spiser,spises,spiste,spist,spis : Str) -> V ;

--3 Verbs with a particle.
--
-- The particle, such as in "lukke opp", is given as a string.

    mkV : V -> Str -> V ;
  } ;



--3 Verbs with 'v�re' as auxiliary
--
-- By default, the auxiliary is "have". This function changes it to "v�re".

  vaereV : V -> V ;



--3 Deponent verbs.
--
-- Some words are used in passive forms only, e.g. "trives", some as
-- reflexive e.g. "forestille seg".

  depV  : V -> V ;
  reflV : V -> V ;

--3 Two-place verbs
--
-- Two-place verbs need a preposition, except the special case with direct object.
-- (transitive verbs). Notice that, if a particle is needed, it comes from the $V$.

  mkV2 : overload {
    mkV2 : Str -> V2 ;
    mkV2 : V -> V2 ;
    mkV2 : V -> Prep -> V2 ;
  } ;


--3 Three-place verbs
--
-- Three-place (ditransitive) verbs need two prepositions, of which
-- the first one or both can be absent.

  mkV3     : V -> Prep -> Prep -> V3 ;    -- snakke, med, om
  dirV3    : V -> Prep -> V3 ;            -- gi,_,til
  dirdirV3 : V -> V3 ;                    -- gi,_,_

--3 Other complement patterns
--
-- Verbs and adjectives can take complements such as sentences,
-- questions, verb phrases, and adjectives.

  mkV0  : V -> V0 ;
  mkVS  : V -> VS ;
  mkV2S : V -> Prep -> V2S ;
  mkVV  : V -> VV ;
  mkV2V : V -> Prep -> Prep -> V2V ;
  mkVA  : V -> VA ;
  mkV2A : V -> Prep -> V2A ;
  mkVQ  : V -> VQ ;
  mkV2Q : V -> Prep -> V2Q ;

  mkAS  : A -> AS ;
  mkA2S : A -> Prep -> A2S ;
  mkAV  : A -> AV ;
  mkA2V : A -> Prep -> A2V ;

-- Notice: categories $V2S, V2V, V2Q$ are in v 1.0 treated
-- just as synonyms of $V2$, and the second argument is given
-- as an adverb. Likewise $AS, A2S, AV, A2V$ are just $A$.
-- $V0$ is just $V$.

  V0, V2S, V2V, V2Q : Type ;
  AS, A2S, AV, A2V : Type ;


--.
--2 Definitions of the paradigms
--
-- The definitions should not bother the user of the API. So they are
-- hidden from the document.

  Gender = MorphoNor.Gender ; 
  Number = MorphoNor.Number ;
  Case = MorphoNor.Case ;
  masculine = Utr Masc ; 
  feminine = Utr Fem ; 
  neutrum = Neutr ;
  singular = Sg ;
  plural = Pl ;
  nominative = Nom ;
  genitive = Gen ;

  mk4N x y z u = mkSubstantive x y z u ** {g = extNGen y ; lock_N = <>} ;

  regN x = regGenN x g where {
    g = case <x : Str> of {
      _ + "e" => Utr Fem ;
      _ => Utr Masc
      }
    } ;

  regGenN x g = case last x of {
    "e" => case g of {
       Utr Masc   => mk4N x (x      + "n") (x + "r") (x + "ne") ;
       Utr Fem    => mk4N x (init x + "a") (x + "r") (x + "ne") ;
       Neutr      => mk4N x (x      + "t") (x + "r") (init x + "a")
       } ;
    _ => case g of {
       Utr Masc   => mk4N x (x      + "en") (x + "er") (x + "ene") ;
       Utr Fem    => mk4N x (x      + "a")  (x + "er") (x + "ene") ;
       Neutr      => mk4N x (x      + "et") (x + "")   (x + "a")
       }
    } ;

  mk2N x y = case last y of {
    "n" => regGenN x masculine ;
    "a" => regGenN x feminine ;
    _   => regGenN x neutrum
    } ;


  mkN2 = \n,p -> n ** {lock_N2 = <> ; c2 = p.s} ;
  regN2 n g = mkN2 (regGenN n g) (mkPrep "av") ;
  mkN3 = \n,p,q -> n ** {lock_N3 = <> ; c2 = p.s ; c3 = q.s} ;

  regGenPN n g = {s = \\c => mkCase c n ; g = g} ** {lock_PN = <>} ;
  regPN n = regGenPN n utrum ;
  nounPN n = {s = n.s ! singular ! Indef ; g = n.g ; lock_PN = <>} ;

-- To form a noun phrase that can also be plural and have an irregular
-- genitive, you can use the worst-case function.

  makeNP : Str -> Str -> Number -> Gender -> NP ; 
  makeNP x y n g = 
    {s = table {NPPoss _ => x ; _ => y} ; a = agrP3 g n ;
     lock_NP = <>} ;

  mk3A a b c = (mkAdject a b c [] []) ** {isComp = False ; lock_A = <>} ;
  mk2A a b = mk3A a b (a + "e") ;
  regA a = (regADeg a) **  {isComp = False ; lock_A = <>} ;

  mkA2 a p = a ** {c2 = p.s ; lock_A2 = <>} ;

  mkADeg a b c d e = mkAdject a b c d e ** {isComp = False ; lock_A = <>} ;
  regADeg a = case Predef.dp 2 a of {
    "ig" => aBillig a ;
    "sk" => aRask a ;
    _ => aRod a
    }  ** {isComp = False ; lock_A = <>} ;
  irregADeg a b c = mkAdject a (a + "t") (a + "e") b c ** 
    {isComp = False ; lock_A = <>} ;
  mk3ADeg a b c = mkAdject a b c (a + "ere") (a + "est") ** 
    {isComp = False ; lock_A = <>} ;
  mk2ADeg a b = mkAdject a b (a + "e") (a + "ere") (a + "est") ** 
    {isComp = False ; lock_A = <>} ;

  compoundA adj = {s = adj.s ; isComp = True ; lock_A = <>} ;

  mkAdv x = ss x ** {lock_Adv = <>} ;
  mkAdV x = ss x ** {lock_AdV = <>} ;
  mkAdA x = ss x ** {lock_AdA = <>} ;

  mkPrep p = {s = p ; lock_Prep = <>} ;
  noPrep = mkPrep [] ;

  mk6V a b c d e f = mkVerb6 a b c d e f ** 
    {part = [] ; vtype = VAct ; isVaere = False ; lock_V = <>} ;

  regV a = case last a of {

--3 Verbs with a particle.
--
-- The particle, such as in "lukke opp", is given as a string.



--3 Verbs with a particle.
--
-- The particle, such as in "lukke opp", is given as a string.


    "e" => vHusk (init a) ;
    _ => vBo a
    } ** {part = [] ; vtype = VAct ; isVaere = False ; lock_V = <>} ;

  mk2V a b = regVerb a b ** {part = [] ; vtype = VAct ; isVaere = False ; lock_V = <>} ;

  irregV =
    \drikke,drakk,drukket ->
    let
      drikk = case last drikke of {
        "e" => init drikke ;
        _ => drikke
        } ;
      drikker = case last (init drikke) of {
        "r" => init drikke ;
        _   => drikke + "r"
        }
    in 
    mk6V drikke drikker (drikke + "s") drakk drukket drikk ; 

  vaereV v = {
    s = v.s ;
    part = [] ;
    vtype = v.vtype ; 
    isVaere = True ; 
    lock_V = <>
    } ;

  partV v p = {s = v.s ; part = p ; vtype = v.vtype ; isVaere = v.isVaere ; lock_V = <>} ;
  depV v = {s = v.s ; part = v.part ; vtype = VPass ; isVaere = False ; lock_V = <>} ;
  reflV v = {s = v.s ; part = v.part ; vtype = VRefl ; isVaere = False ; lock_V = <>} ;

  mk2V2 v p = v ** {c2 = p.s ; lock_V2 = <>} ;
  dirV2 v = mk2V2 v noPrep ;

  mkV3 v p q = v ** {c2 = p.s ; c3 = q.s ; lock_V3 = <>} ;
  dirV3 v p = mkV3 v noPrep p ;
  dirdirV3 v = dirV3 v noPrep ;

  mkV0  v = v ** {lock_V0 = <>} ;
  mkVS  v = v ** {lock_VS = <>} ;
  mkV2S v p = mk2V2 v p ** {lock_V2S = <>} ;
  mkVV  v = v ** {c2 = "�" ; lock_VV = <>} ;
  mkV2V v p t = mk2V2 v p ** {s3 = t ; lock_V2V = <>} ;
  mkVA  v = v ** {lock_VA = <>} ;
  mkV2A v p = mk2V2 v p ** {lock_V2A = <>} ;
  mkVQ  v = v ** {lock_VQ = <>} ;
  mkV2Q v p = mk2V2 v p ** {lock_V2Q = <>} ;

  mkAS  v = v ** {lock_A = <>} ;
  mkA2S v p = mkA2 v p ** {lock_A = <>} ;
  mkAV  v = v ** {lock_A = <>} ;
  mkA2V v p = mkA2 v p ** {lock_A = <>} ;

  V0 : Type = V ;
  V2S, V2V, V2Q : Type = V2 ;
  AS, A2S, AV : Type = A ;
  A2V : Type = A2 ;


---------

  mk2N : (bil,bilen : Str) -> N ;
  mk4N  : (dreng,drengen,drenger,drengene : Str) -> N ;
  regN : Str -> N ;
  regGenN : Str -> Gender -> N ;
  mk2N : (bil,bilen : Str) -> N ;

  mkN = overload {
    mkN : Str -> N = regN ;
    mkN : Str -> Gender -> N = regGenN ;
    mkN : (bil,bilen : Str) -> N = mk2N ;
    mkN  : (dreng,drengen,drenger,drengene : Str) -> N = mk4N
  } ;

  mkPN = overload {
    mkPN : Str -> PN = regPN ;       -- masculine
    mkPN : Str -> Gender -> PN = regGenPN ;  
    mkPN : N -> PN = nounPN ;
    } ;

  regPN    : Str -> PN ;            -- utrum
  regGenPN : Str -> Gender -> PN ;  
  nounPN : N -> PN ;

  mkA = overload {
    mkA : (fin : Str) -> A = regADeg ;
    mkA : (fin,fint : Str) -> A = mk2ADeg ;
    mkA : (galen,galet,galne : Str) -> A = mk3ADeg ;
    mkA : (stor,stort,store,storre,storst : Str) -> A = mkADeg ;
    mkA : A -> A = compoundA ; -- -/mer/mest norsk
  } ;

  mk3A : (galen,galet,galne : Str) -> A ;
  regA : Str -> A ;
  mk2A : (stor,stort : Str) -> A ;
  mkADeg : (stor,stort,store,storre,storst : Str) -> A ;
  regADeg : Str -> A ;
  irregADeg : (tung,tyngre,tyngst : Str) -> A ;
  mk3ADeg : (galen,galet,galne : Str) -> A ;
  mk2ADeg : (bred,bredt        : Str) -> A ;
  compoundA : A -> A ; -- -/mer/mest norsk

  mkV = overload {
    mkV : (snakke : Str) -> V = regV ;
    mkV : (leve,levde : Str) -> V = mk2V ;
    mkV : (drikke, drakk, drukket  : Str) -> V = irregV ;
    mkV : (spise,spiser,spises,spiste,spist,spis : Str) -> V = mk6V ;
    mkV : V -> Str -> V = partV ;
  } ;


  regV : (snakke : Str) -> V ;
  mk2V : (leve,levde : Str) -> V ;
  irregV : (drikke, drakk, drukket  : Str) -> V ;
  mk6V : (spise,spiser,spises,spiste,spist,spis : Str) -> V ;
  partV  : V -> Str -> V ;


  mkV2 = overload {
    mkV2 : Str -> V2 = \s -> dirV2 (regV s) ;
    mkV2 : V -> V2 = dirV2 ;
    mkV2 : V -> Prep -> V2 = mk2V2 ;
  } ;

  mk2V2  : V -> Prep -> V2 ;
  dirV2 : V -> V2 ;

} ;
