--# -path=.:../scandinavian:../common:../abstract:../../prelude

--1 Swedish Lexical Paradigms
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
-- The main difference with $MorphoSwe.gf$ is that the types
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

resource ParadigmsSwe = 
  open 
    (Predef=Predef), 
    Prelude, 
    ResScand, 
    DiffSwe, 
    MorphoSwe, 
    CatSwe in {

--2 Parameters 
--
-- To abstract over gender names, we define the following identifiers.

oper
  Gender : Type ; 

  utrum     : Gender ;
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

  Preposition : Type = Str ;

--2 Nouns

-- Worst case: give all four forms. The gender is computed from the
-- last letter of the second form (if "n", then $utrum$, otherwise $neutrum$).

  mkN  : (apa,apan,apor,aporna : Str) -> N ;

-- The regular function takes the singular indefinite form and the gender,
-- and computes the other forms by a heuristic. 
-- If in doubt, use the $cc$ command to test!

  regN : Str -> Gender -> N ;

-- In practice the worst case is often just: give singular and plural indefinite.

  mk2N : (nyckel,nycklar : Str) -> N ;


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

-- Non-comparison one-place adjectives need for forms: 

  mkA : (galen,galet,galna : Str) -> A ;

-- For regular adjectives, the other forms are derived. 

  regA : Str -> A ;

-- In practice, two forms are enough.

  mk2A : (bred,brett : Str) -> A ;
 
--3 Two-place adjectives
--
-- Two-place adjectives need a preposition for their second argument.

  mkA2 : A -> Preposition -> A2 ;

-- Comparison adjectives may need as many as seven forms. 

  ADeg : Type ;

  mkADeg : (liten, litet, lilla, sma, mindre, minst, minsta : Str) -> ADeg ;

-- The regular pattern works for many adjectives, e.g. those ending
-- with "ig".

  regADeg : Str -> ADeg ;

-- Just the comparison forms can be irregular.

  irregADeg : (tung,tyngre,tyngst : Str) -> ADeg ;

-- Sometimes just the positive forms are irregular.

  mk3ADeg : (galen,galet,galna : Str) -> ADeg ;
  mk2ADeg : (bred,brett        : Str) -> ADeg ;


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
-- The worst case needs five forms.

  mkV : (supa,super,sup,s�p,supit,supen : Str) -> V ;

-- The 'regular verb' function is the first conjugation if the
-- infinitive ends with "a" ("tala" - "talar" - "talade" - "talat"),
-- the third in other cases ("bo" - "bor" - "bodde" - "bott").

  regV : (tala : Str) -> V ;

-- The almost regular verb function needs the infinitive and the preteritum.
-- It can deal with almost all cases in the first, second, and third
-- conjugation: "tala" - "talade", "leka" - "lekte", 
-- "gr�va" - "gr�vde", "byta" - "bytte", "v�nda" - "v�nde",
-- "tyda" - "tydde", "bo" - "bodde".

  mk2V : (leka,lekte : Str) -> V ;

-- There is an extensive list of irregular verbs in the module $IrregularSwe$.
-- In practice, it is enough to give three forms, as in school books.

  irregV : (dricka, drack, druckit  : Str) -> V ;


--3 Verbs with a particle.
--
-- The particle, such as in "passa p�", is given as a string.

  partV  : V -> Str -> V ;

--3 Deponent verbs.
--
-- Some words are used in passive forms only, e.g. "hoppas", some as
-- reflexive e.g. "�ngra sig".

  depV  : V -> V ;
  reflV : V -> V ;

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

  mkV3     : V -> Preposition -> Preposition -> V3 ; -- tala med om
  dirV3    : V -> Preposition -> V3 ;                -- ge _ till
  dirdirV3 : V -> V3 ;                               -- ge _ _

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

-- Notice: categories $V2S, V2V, V2A, V2Q$ are in v 1.0 treated
-- just as synonyms of $V2$, and the second argument is given
-- as an adverb. Likewise $AS, A2S, AV, A2V$ are just $A$.
-- $V0$ is just $V$.

  V0, V2S, V2V, V2A, V2Q : Type ;
  AS, A2S, AV, A2V : Type ;


--2 Definitions of the paradigms
--
-- The definitions should not bother the user of the API. So they are
-- hidden from the document.
--.

  Gender = DiffSwe.Gender ; 
  Number = ResScand.Number ;
  Case = ResScand.Case ;
  utrum = Utr ; 
  neutrum = Neutr ;
  singular = Sg ;
  plural = Pl ;
  nominative = Nom ;
  genitive = Gen ;

  mkN x y z u = mkNoun x y z u ** {lock_N = <>} ;
  regN x g = regNoun x g ** {lock_N = <>} ;
  mk2N x g = reg2Noun x g ** {lock_N = <>} ;

  mkN2 = \n,p -> n ** {lock_N2 = <> ; c2 = p} ;
  regN2 n g = mkN2 (regN n g) (mkPreposition "av") ;
  mkN3 = \n,p,q -> n ** {lock_N3 = <> ; c2 = p ; c3 = q} ;

  regPN n g = {s = \\c => mkCase c n ; g = g} ** {lock_PN = <>} ;
  nounPN n = {s = n.s ! singular ! Indef ; g = n.g ; lock_PN = <>} ;
  mkNP x y n g = 
    {s = table {NPPoss _ => y ; _ => x} ; a = agrP3 g n ; p = P3 ;
     lock_NP = <>} ;

  mkA a b c = (adjAlmostReg a b c) ** {lock_A = <>} ;
  mk2A a b = (adj2Reg a b) ** {lock_A = <>} ;
  regA a = (adjReg a) ** {lock_A = <>} ;

  mkA2 a p = a ** {c2 = p ; lock_A2 = <>} ;

  ADeg = A ;

  mkADeg a b c d e f g = mkAdjective a b c d e f g ** {lock_A = <>} ;
  regADeg a = adjReg a ** {lock_A = <>} ;
  irregADeg a b c = adjIrreg3 a b c ** {lock_A = <>} ;
  mk3ADeg a b c = adjAlmostReg a b c ** {lock_A = <>} ;
  mk2ADeg a b = adj2Reg a b ** {lock_A = <>} ;

  mkAdv x = ss x ** {lock_Adv = <>} ;
  mkAdV x = ss x ** {lock_AdV = <>} ;
  mkAdA x = ss x ** {lock_AdA = <>} ;

  mkPreposition p = p ;

  mkV a b c d e f = mkVerb6 a b c d e f ** {lock_V = <>} ;

  regV a = mk2V a (a + de) where {de = case last a of {"a" => "de" ; _ => "dde"}} ;
  mk2V a b = regVerb a b ** {lock_V = <>} ;

  irregV x y z = irregVerb x y z
     ** {s1 = [] ; lock_V = <>} ;

  partV v p = {s = \\f => v.s ! f ++ p ; vtype = v.vtype ; lock_V = <>} ;
  depV v = {s = v.s ; vtype = VPass ; lock_V = <>} ;
  reflV v = {s = v.s ; vtype = VRefl ; lock_V = <>} ;

  mkV2 v p = v ** {s = v.s ; c2 = p ; lock_V2 = <>} ;
  dirV2 v = mkV2 v [] ;

  mkV3 v p q = v ** {s = v.s ; c2 = p ; c3 = q ; lock_V3 = <>} ;
  dirV3 v p = mkV3 v [] p ;
  dirdirV3 v = dirV3 v [] ;


  mkV0  v = v ** {lock_V0 = <>} ;
  mkVS  v = v ** {lock_VS = <>} ;
  mkVV  v = v ** {c2 = "att" ; lock_VV = <>} ;
  mkVQ  v = v ** {lock_VQ = <>} ;

  mkVA  v = v ** {lock_VA = <>} ;
  mkV2A v p = mkV2 v p ** {lock_V2A = <>} ;

  V0 : Type = V ;
  V2S, V2V, V2Q, V2A : Type = V2 ;
  AS, A2S, AV : Type = A ;
  A2V : Type = A2 ;

  mkV2S v p = mkV2 v p ** {lock_V2 = <>} ;
  mkV2V v p t = mkV2 v p ** {s3 = t ; lock_V2 = <>} ;
  mkV2Q v p = mkV2 v p ** {lock_V2 = <>} ;

  mkAS  v = v ** {lock_A = <>} ;
  mkA2S v p = mkA2 v p ** {lock_A = <>} ;
  mkAV  v = v ** {lock_A = <>} ;
  mkA2V v p = mkA2 v p ** {lock_A = <>} ;

} ;
