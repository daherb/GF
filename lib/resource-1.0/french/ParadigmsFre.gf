--# -path=.:../romance:../common:../abstract:../../prelude

--1 French Lexical Paradigms
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
-- The main difference with $MorphoFre.gf$ is that the types
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

resource ParadigmsFre = 
  open 
    (Predef=Predef), 
    Prelude, 
    CommonRomance, 
    ResFre, 
    MorphoFre, 
    CatFre in {

  flags optimize=all ;

--2 Parameters 
--
-- To abstract over gender names, we define the following identifiers.

oper
  Gender : Type ; 

  masculine : Gender ;
  feminine  : Gender ;

-- To abstract over number names, we define the following.

  Number : Type ; 

  singular : Number ;
  plural   : Number ;

-- Prepositions used in many-argument functions are either strings
-- (including the 'accusative' empty string) or strings that
-- amalgamate with the following word (the 'genitive' "de" and the
-- 'dative' "�").

  Preposition : Type ;

  accusative : Preposition ;
  genitive   : Preposition ;
  dative     : Preposition ;

  mkPreposition : Str -> Preposition ;


--2 Nouns

-- Worst case: give both two forms and the gender. 

  mkN  : (oeil,yeux : Str) -> Gender -> N ;

-- The regular function takes the singular form and the gender,
-- and computes the plural by a heuristic. The heuristic currently
-- covers the cases "pas-pas", "prix-prix", "nez-nez", 
-- "bijou-bijoux", "cheveu-cheveux", "plateau-plateaux", "cheval-chevaux".
-- If in doubt, use the $cc$ command to test!

  regN : Str -> Gender -> N ;


--3 Compound nouns 
--
-- Some nouns are ones where the first part is inflected as a noun but
-- the second part is not inflected. e.g. "num�ro de t�l�phone". 
-- They could be formed in syntax, but we give a shortcut here since
-- they are frequent in lexica.

  compN : N -> Str -> N ;


--3 Relational nouns 
-- 
-- Relational nouns ("fille de x") need a case and a preposition. 

  mkN2 : N -> Preposition -> N2 ;

-- The most common cases are the genitive "de" and the dative "�", 
-- with the empty preposition.

  deN2 : N -> N2 ;
  aN2  : N -> N2 ;

-- Three-place relational nouns ("la connection de x � y") need two prepositions.

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
-- Proper names need a string and a gender.

  mkPN : Str -> Gender -> PN ;          -- Jean

-- To form a noun phrase that can also be plural,
-- you can use the worst-case function.

  mkNP : Str -> Gender -> Number -> NP ; 

--2 Adjectives

-- Non-comparison one-place adjectives need four forms in the worst
-- case (masc and fem singular, masc plural, adverbial).

  mkA : (banal,banale,banaux,banalement : Str) -> A ;

-- For regular adjectives, all other forms are derived from the
-- masculine singular. The heuristic takes into account certain
-- deviant endings: "banal- -banaux", "chinois- -chinois", 
-- "heureux-heureuse-heureux", "italien-italienne", "jeune-jeune",
-- "amer-am�re", "carr�- - -carr�ment", "joli- - -joliment".

  regA : Str -> A ;

-- These functions create postfix adjectives. To switch
-- them to prefix ones (i.e. ones placed before the noun in
-- modification, as in "petite maison"), the following function is
-- provided.

  prefA : A -> A ;

--3 Two-place adjectives
--
-- Two-place adjectives need a preposition for their second argument.

  mkA2 : A -> Preposition -> A2 ;

--3 Comparison adjectives 

-- Comparison adjectives are in the worst case put up from two
-- adjectives: the positive ("bon"), and the comparative ("meilleure"). 

  mkADeg : A -> A -> A ;

-- If comparison is formed by "plus", as usual in French,
-- the following pattern is used:

  compADeg : A -> A ;

-- From a given $A$, it is possible to get back to $A$.

  adegA : A -> A ;

-- For prefixed adjectives, the following function is
-- provided.

  prefA : A -> A ;

--2 Adverbs

-- Adverbs are not inflected. Most lexical ones have position
-- after the verb. 

  mkAdv : Str -> Adv ;

-- Some appear next to the verb (e.g. "toujours").

  mkAdV : Str -> AdV ;

-- Adverbs modifying adjectives and sentences can also be formed.

  mkAdA : Str -> AdA ;


--2 Verbs
--
-- Irregular verbs are given in the module $VerbsFre$. 
-- If a verb should be missing in that list, the module
-- $BeschFre$ gives all the patterns of the "Bescherelle" book.
-- 
-- Regular verbs are ones with the infinitive "er" or "ir", the
-- latter with plural present indicative forms as "finissons".
-- The regular verb function is the first conjugation recognizes
-- these endings, as well as the variations among
-- "aimer, c�der, placer, peser, jeter, placer, manger, assi�ger, payer".

  regV : Str -> V ;

-- Sometimes, however, it is not predictable which variant of the "er"
-- conjugation is to be selected. Then it is better to use the function
-- that gives the third person singular present indicative and future 
-- (("il") "jette", "jettera") as second argument.

  reg3V : (jeter,jette,jettera : Str) -> V ;

-- The function $regV$ gives all verbs the compound auxiliary "avoir".
-- To change it to "�tre", use the following function.

  etreV : V -> V ;

--3 Two-place verbs
--
-- Two-place verbs need a preposition, except the special case with direct object.
-- (transitive verbs). Notice that a particle comes from the $V$.

  mkV2  : V -> Preposition -> V2 ;

  dirV2 : V -> V2 ;

-- You can reuse a $V2$ verb in $V$.

  v2V : V2 -> V ;

--3 Three-place verbs
--
-- Three-place (ditransitive) verbs need two prepositions, of which
-- the first one or both can be absent.

  mkV3     : V -> Preposition -> Preposition -> V3 ; -- parler, �, de
  dirV3    : V -> Preposition -> V3 ;                -- donner,_,�
  dirdirV3 : V -> V3 ;                               -- donner,_,_

--3 Other complement patterns
--
-- Verbs and adjectives can take complements such as sentences,
-- questions, verb phrases, and adjectives.

  mkV0  : V -> V0 ;
  mkVS  : V -> VS ;
  mkV2S : V -> Preposition -> V2S ;
  mkVV  : V -> VV ;  -- plain infinitive: "je veux parler"
  deVV  : V -> VV ;  -- "j'essaie de parler"
  aVV   : V -> VV ;  -- "j'arrive � parler"
  mkV2V : V -> Preposition -> Preposition -> V2V ;
  mkVA  : V -> VA ;
  mkV2A : V -> Preposition -> V2A ;
  mkVQ  : V -> VQ ;
  mkV2Q : V -> Preposition -> V2Q ;

  mkAS   : A -> AS ;
  subjAS : A -> AS ;
  mkA2S : A -> Preposition -> A2S ;
  mkAV  : A -> Preposition -> AV ;
  mkA2V : A -> Preposition -> Preposition -> A2V ;

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

  Gender = MorphoFre.Gender ; 
  Number = MorphoFre.Number ;
  masculine = Masc ;
  feminine = Fem ;
  singular = Sg ;
  plural = Pl ;

  Preposition = Compl ;
  accusative = complAcc ;
  genitive = complGen ;
  dative = complDat ;
  mkPreposition p = {s = p ; c = Acc ; isDir = False} ;

  mkN x y g = mkCNomIrreg x y g ** {lock_N = <>} ;
  regN x g = mkNomReg x g ** {lock_N = <>} ;
  compN x y = {s = \\n => x.s ! n ++ y ; g = x.g ; lock_N = <>} ;

  mkN2 = \n,p -> n ** {lock_N2 = <> ; c2 = p} ;
  deN2 n = mkN2 n genitive ;
  aN2 n = mkN2 n dative ;
  mkN3 = \n,p,q -> n ** {lock_N3 = <> ; c2 = p ; c3 = q} ;

  mkPN x g = {s = x ; g = g} ** {lock_PN = <>} ;

  mkA a b c d = compADeg {s = \\_ => (mkAdj a c b d).s ; isPre = False ; lock_A = <>} ;
  regA a = compADeg {s = \\_ => (mkAdjReg a).s ; isPre = False ; lock_A = <>} ;
  prefA a = {s = a.s ; isPre = True ; lock_A = <>} ;

  mkA2 a p = a ** {c2 = p ; lock_A2 = <>} ;

  mkADeg a b = 
    {s = table {Posit => a.s ! Posit ; _ => b.s ! Posit} ; isPre = a.isPre ; lock_A = <>} ;
  compADeg a = 
    {s = table {Posit => a.s ! Posit ; _ => \\f => "plus" ++ a.s ! Posit ! f} ; isPre = a.isPre ;
               lock_A = <>} ;
  prefA a = {s = a.s ; isPre = True ; lock_A = <>} ;


  mkAdv x = ss x ** {lock_Adv = <>} ;
  mkAdV x = ss x ** {lock_AdV = <>} ;
  mkAdA x = ss x ** {lock_AdA = <>} ;

  regV x = let v = vvf (mkVerbReg x) in {s = v ; vtyp = VHabere ; lock_V = <>} ;
  reg3V x y z = let v = vvf (mkVerb3Reg x y z) in {s = v ; vtyp = VHabere ; lock_V = <>} ;
  etreV v = {s = v.s ; vtyp = VEsse ; lock_V = <>} ;

  mkV2 v p = v ** {c2 = p ; lock_V2 = <>} ;
  dirV2 v = mkV2 v accusative ;
  v2V v = v ** {lock_V = <>} ;

  mkV3 v p q = v ** {c2 = p ; c3 = q ; lock_V3 = <>} ;
  dirV3 v p = mkV3 v complAcc p ;
  dirdirV3 v = dirV3 v complDat ;

  V0 : Type = V ;
  V2S, V2V, V2Q, V2A : Type = V2 ;
  AS, AV : Type = A ;
  A2S, A2V : Type = A2 ;

  mkV0  v = v ** {lock_V0 = <>} ;
  mkVS  v = v ** {m = \\_ => Indic ; lock_VS = <>} ;  ---- more moods
  mkV2S v p = mkV2 v p ** {mn,mp = Indic ; lock_V2S = <>} ;
  mkVV  v = v ** {c2 = complAcc ; lock_VV = <>} ;
  deVV  v = v ** {c2 = complGen ; lock_VV = <>} ;
  aVV  v = v ** {c2 = complDat ; lock_VV = <>} ;
  mkV2V v p t = mkV2 v p ** {c3 = t.p1  ; s3 = p.p2 ; lock_V2V = <>} ;
  mkVA  v = v ** {lock_VA = <>} ;
  mkV2A v p = mkV2 v p ** {lock_V2A = <>} ;
  mkVQ  v = v ** {lock_VQ = <>} ;
  mkV2Q v p = mkV2 v p ** {lock_V2Q = <>} ;

  mkAS  v = v ** {lock_AS = <>} ; ---- more moods
  mkA2S v p = mkA2 v p ** {lock_A2S = <>} ;
  mkAV  v p = v ** {c = p.p1 ; s2 = p.p2 ; lock_AV = <>} ;
  mkA2V v p q = mkA2 v p ** {s3 = q.p2 ; c3 = q.p1 ; lock_A2V = <>} ;

} ;
