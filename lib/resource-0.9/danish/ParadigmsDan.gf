--# -path=.:../scandinavian:../abstract:../../prelude

--1 Sanish Lexical Paradigms
--
-- Aarne Ranta 2003
--
-- This is an API to the user of the resource grammar 
-- for adding lexical items. It gives functions for forming
-- expressions of open categories: nouns, adjectives, verbs.
-- 
-- Closed categories (determiners, pronouns, conjunctions) are
-- accessed through the resource syntax API, $Structural.gf$. 
--
-- The main difference with $MorphoDan.gf$ is that the types
-- referred to are compiled resource grammar types. We have moreover
-- had the design principle of always having existing forms, rather
-- than stems, as string arguments of the paradigms.
--
-- The structure of functions for each word class $C$ is the following:
-- first we give a handful of patterns that aim to cover all
-- regular cases. Then we give a worst-case function $mkC$, which serves as an
-- escape to construct the most irregular words of type $C$.
-- However, this function should only seldom be needed: we have a
-- separate module $IrregularEng$, which covers all irregularly inflected
-- words.
-- 
-- The following modules are presupposed:

resource ParadigmsDan = 
  open (Predef=Predef), Prelude, TypesDan, MorphoDan, SyntaxDan, CategoriesDan in {

--2 Parameters 
--
-- To abstract over gender names, we define the following identifiers.

oper
  Gender : Type ; 

  utrum   : Gender ;
  neutrum : Gender ;

-- To abstract over number names, we define the following.

  Number : Type ; 

  singular : Number ;
  plural   : Number ;

-- To abstract over case names, we define the following.

  Case : Type ;

  nominative : Case ;
  genitive   : Case ;

-- Prepositions used in many-argument functions are just strings.

  Preposition : Type = Str ;

--2 Nouns

-- Worst case: give all four forms. The gender is computed from the
-- last letter of the second form (if "n", then $utrum$, otherwise $neutrum$).

  mkN  : (dreng,drengen,drenger,drengene : Str) -> N ;

-- The regular function takes the singular indefinite form and the gender,
-- and computes the other forms by a heuristic. 
-- If in doubt, use the $cc$ command to test!

  regN : Str -> Gender -> N ;

-- This function takes the singular indefinite and definite forms; the
-- gender is computed from the definite form.

  mk2N : (bil,bilen : Str) -> N ;


--3 Compound nouns 
--
-- All the functions above work quite as well to form compound nouns,
-- such as "fotboll". 


--3 Relational nouns 
-- 
-- Relational nouns ("daughter of x") need a preposition. 

  mkN2 : N -> Preposition -> N2 ;

-- The most common preposition is "av", and the following is a
-- shortcut for regular, $nonhuman$ relational nouns with "av".

  regN2 : Str -> Gender -> N2 ;

-- Use the function $mkPreposition$ or see the section on prepositions below to  
-- form other prepositions.
--
-- Three-place relational nouns ("the connection from x to y") need two prepositions.

  mkN3 : N -> Preposition -> Preposition -> N3 ;


--3 Relational common noun phrases
--
-- In some cases, you may want to make a complex $CN$ into a
-- relational noun (e.g. "the old town hall of"). However, $N2$ and
-- $N3$ are purely lexical categories. But you can use the $AdvCN$
-- and $PrepNP$ constructions to build phrases like this.

-- 
--3 Proper names and noun phrases
--
-- Proper names, with a regular genitive, are formed as follows

  regPN : Str -> Gender -> PN ;          -- John, John's

-- Sometimes you can reuse a common noun as a proper name, e.g. "Bank".

  nounPN : N -> PN ;

-- To form a noun phrase that can also be plural and have an irregular
-- genitive, you can use the worst-case function.

  mkNP : Str -> Str -> Number -> Gender -> NP ; 

--2 Adjectives

-- Non-comparison one-place adjectives need three forms: 

  mkA : (galen,galet,galne : Str) -> A ;

-- For regular adjectives, the other forms are derived. 

  regA : Str -> A ;

-- In most cases, two forms are enough.

  mk2A : (stor,stort : Str) -> A ;
 
--3 Two-place adjectives
--
-- Two-place adjectives need a preposition for their second argument.

  mkA2 : A -> Preposition -> A2 ;

-- Comparison adjectives may need as many as five forms. 

  mkADeg : (stor,stort,store,storre,storst : Str) -> ADeg ;

-- The regular pattern works for many adjectives, e.g. those ending
-- with "ig".

  regADeg : Str -> ADeg ;

-- Just the comparison forms can be irregular.

  irregADeg : (tung,tyngre,tyngst : Str) -> ADeg ;

-- Sometimes just the positive forms are irregular.

  mk3ADeg : (galen,galet,galna : Str) -> ADeg ;
  mk2ADeg : (bred,bredt        : Str) -> ADeg ;

-- If comparison is formed by "mer, "mest", as in general for
-- long adjective, the following pattern is used:

  compoundADeg : A -> ADeg ; -- -/mer/mest norsk

-- From a given $ADeg$, it is possible to get back to $A$.

  adegA : ADeg -> A ;


--2 Adverbs

-- Adverbs are not inflected. Most lexical ones have position
-- after the verb. Some can be preverbal (e.g. "always").

  mkAdv : Str -> Adv ;
  mkAdV : Str -> AdV ;

-- Adverbs modifying adjectives and sentences can also be formed.

  mkAdA : Str -> AdA ;

--2 Prepositions
--
-- A preposition is just a string.

  mkPreposition : Str -> Preposition ;

--2 Verbs
--
-- The worst case needs six forms.

  mkV : (spise,spiser,spises,spiste,spist,spis : Str) -> V ;

-- The 'regular verb' function is the first conjugation.

  regV : (snakke : Str) -> V ;

-- The almost regular verb function needs the infinitive and the preteritum.

  mk2V : (leve,levde : Str) -> V ;

-- There is an extensive list of irregular verbs in the module $IrregularSwe$.
-- In practice, it is enough to give three forms, as in school books.

  irregV : (drikke, drakk, drukket  : Str) -> V ;


--3 Verbs with a particle.
--
-- The particle, such as in "switch on", is given as a string.

  partV  : V -> Str -> V ;

--3 Deponent verbs.
--
-- Some words are used in passive forms only, e.g. "hoppas".

  depV  : V -> V ;

--3 Two-place verbs
--
-- Two-place verbs need a preposition, except the special case with direct object.
-- (transitive verbs). Notice that a particle comes from the $V$.

  mkV2  : V -> Preposition -> V2 ;

  dirV2 : V -> V2 ;

--3 Three-place verbs
--
-- Three-place (ditransitive) verbs need two prepositions, of which
-- the first one or both can be absent.

  mkV3     : V -> Str -> Str -> V3 ;    -- speak, with, about
  dirV3    : V -> Str -> V3 ;           -- give,_,to
  dirdirV3 : V -> V3 ;                  -- give,_,_

--3 Other complement patterns
--
-- Verbs and adjectives can take complements such as sentences,
-- questions, verb phrases, and adjectives.

  mkV0  : V -> V0 ;
  mkVS  : V -> VS ;
  mkV2S : V -> Str -> V2S ;
  mkVV  : V -> VV ;
  mkV2V : V -> Str -> Str -> V2V ;
  mkVA  : V -> VA ;
  mkV2A : V -> Str -> V2A ;
  mkVQ  : V -> VQ ;
  mkV2Q : V -> Str -> V2Q ;

  mkAS  : A -> AS ;
  mkA2S : A -> Str -> A2S ;
  mkAV  : A -> AV ;
  mkA2V : A -> Str -> A2V ;


--2 Definitions of the paradigms
--
-- The definitions should not bother the user of the API. So they are
-- hidden from the document.
--.

  Gender = SyntaxDan.NounGender ; 
  Number = TypesDan.Number ;
  Case = TypesDan.Case ;
  utrum = NUtr ;
  neutrum = NNeutr ;
  singular = Sg ;
  plural = Pl ;
  nominative = Nom ;
  genitive = Gen ;

  mkN x y z u = let sb = mkSubstantive x y z u 
                in {s = \\n,b,c => sb.s ! SF n b c ; g = extNGen y ; lock_N = <>} ;
  regN x g = case last x of {
    "e" => case g of {
       NUtr        => mkN x (x      + "n") (x + "r") (x + "rne") ;
       NNeutr      => mkN x (x      + "t") (x + "r") (init x + "ene")
       } ;
    _ => case g of {
       NUtr        => mkN x (x      + "en") (x + "er") (x + "rene") ;
       NNeutr      => mkN x (x      + "et") (x + "")   (x + "ene")
       }
    } ;

  mk2N x y = case last y of {
    "n" => regN x utrum ;
    _   => regN x neutrum
    } ;


  mkN2 = \n,p -> n ** {lock_N2 = <> ; s2 = p} ;
  regN2 n g = mkN2 (regN n g) (mkPreposition "av") ;
  mkN3 = \n,p,q -> n ** {lock_N3 = <> ; s2 = p ; s3 = q} ;

  regPN n g = {s = \\c => mkCase n ! c ; g = g} ** {lock_PN = <>} ;
  nounPN n = {s = n.s ! singular ! Indef ; g = n.g ; lock_PN = <>} ;
  mkNP x y n g = 
    {s = table {PGen _ => x ; _ => y} ; g = genNoun g ; n = n ; p = P3 ;
     lock_NP = <>} ;

  mkA a b c = extractPositive (mkAdjective a b c [] []) ** {lock_A = <>} ;
  mk2A a b = mkA a b (a + "e") ;
  regA a = extractPositive (regADeg a) **  {lock_A = <>} ;

  mkA2 a p = a ** {s2 = p ; lock_A2 = <>} ;

  mkADeg a b c d e = mkAdjective a b c d e ** {lock_ADeg = <>} ;
  regADeg a = case Predef.dp 2 a of {
----    "ig" => aBillig a ;
    "sk" => aRask a ;
    _ => case last a of {
    "t" => aAbstrakt a ;
    _ => aRod a
    }}  ** {lock_ADeg = <>} ;
  irregADeg a b c = mkAdjective a (a + "t") (a + "e") b c ** {lock_ADeg = <>} ;
  mk3ADeg a b c = mkAdjective a b c (a + "ere") (a + "est") ** {lock_ADeg = <>} ;
  mk2ADeg a b = mkAdjective a b (a + "e") (a + "ere") (a + "est") ** {lock_ADeg = <>} ;

  mkAdv x = ss x ** {lock_Adv = <>} ;
  mkAdV x = ss x ** {lock_AdV = <>} ;
  mkAdA x = ss x ** {lock_AdA = <>} ;

  mkPreposition p = p ;

  mkV a b c d e f = mkVerb a b c d e f ** {s1 = [] ; lock_V = <>} ;

  regV a = case last a of {
    "e" => vHusk (init a) ;
    _ => vBo a
    } ** {s1 = [] ; lock_V = <>} ;

  mk2V a b = regVerb a b ** {s1 = [] ; lock_V = <>} ;

  irregV x y z =  irregVerb x y z
     ** {s1 = [] ; lock_V = <>} ;

  partV v p = {s = v.s ; s1 = p ; lock_V = <>} ;
  depV v = deponentVerb v ** {lock_V = <>} ;

  mkV2 v p = v ** {s = v.s ; s1 = v.s1 ; s2 = p ; lock_V2 = <>} ;
  dirV2 v = mkV2 v [] ;

  mkV3 v p q = v ** {s = v.s ; s1 = v.s1 ; s2 = p ; s3 = q ; lock_V3 = <>} ;
  dirV3 v p = mkV3 v [] p ;
  dirdirV3 v = dirV3 v [] ;

  mkV0  v = v ** {lock_V0 = <>} ;
  mkVS  v = v ** {lock_VS = <>} ;
  mkV2S v p = mkV2 v p ** {lock_V2S = <>} ;
  mkVV  v = v ** {isAux = False ; lock_VV = <>} ;
  mkV2V v p t = mkV2 v p ** {s3 = t ; lock_V2V = <>} ;
  mkVA  v = v ** {lock_VA = <>} ;
  mkV2A v p = mkV2 v p ** {lock_V2A = <>} ;
  mkVQ  v = v ** {lock_VQ = <>} ;
  mkV2Q v p = mkV2 v p ** {lock_V2Q = <>} ;

  mkAS  v = v ** {lock_AS = <>} ;
  mkA2S v p = mkA2 v p ** {lock_A2S = <>} ;
  mkAV  v = v ** {lock_AV = <>} ;
  mkA2V v p = mkA2 v p ** {lock_A2V = <>} ;

} ;
