--# -path=.:../romance:../abstract:../../prelude

--1 Spanish Lexical Paradigms
--
-- Aarne Ranta 2005
--
-- This is an API to the user of the resource grammar 
-- for adding lexical items. It give shortcuts for forming
-- expressions of basic categories: nouns, adjectives, verbs.
-- 
-- Closed categories (determiners, pronouns, conjunctions) are
-- accessed through the resource syntax API, $resource.Abs.gf$. 
--
-- The main difference with $MorphoIta.gf$ is that the types
-- referred to are compiled resource grammar types. We have moreover
-- had the design principle of always having existing forms, not stems, as string
-- arguments of the paradigms.
--
-- The following modules are presupposed:

resource ParadigmsSpa = 
  open Prelude, (Types = TypesSpa), SyntaxSpa, MorphoSpa, BeschSpa,
  RulesSpa in {

--2 Parameters 
--
-- To abstract over gender names, we define the following identifiers.

oper
  Bool      : Type ;
  Gender    : Type ;

  masculine : Gender ;
  feminine  : Gender ;

-- To abstract over number names, we define the following.

  Number    : Type ;

  singular : Number ;
  plural   : Number ;

-- Prepositions used in many-argument functions are either strings
-- (including the 'accusative' empty string) or strings that
-- amalgamate with the following word (the 'genitive' "de" and the
-- 'dative' "�").

  Preposition    : Type ;

  accusative : Preposition ;
  dative     : Preposition ;
  genitive   : Preposition ;

  mkPreposition : Str -> Preposition ;

--2 Nouns

-- Worst case: two forms (singular + plural),
-- and the gender.

  mkN  : (_,_ : Str) -> Gender -> N ;   -- uomo, uomini, masculine

-- The regular function takes the singular form and the gender,
-- and computes the plural and the gender by a heuristic. 
-- The heuristic says that the gender is feminine for nouns
-- ending with "a" or "z", and masculine for all other words.
-- Nouns ending with "a", "o", "e" have the plural with "s",
-- those ending with "z" have "ces" in plural; all other nouns
-- have "es" as plural ending. The accent is not dealt with.

  regN : Str -> N ;

-- To force a different gender, use one of the following functions.

  mascN : N -> N ;
  femN  : N -> N ;

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

-- The most common cases are the genitive "de" and the dative "a", 
-- with the empty preposition.

  deN2 : N -> N2 ;
  aN2  : N -> N2 ;

-- Three-place relational nouns ("la connessione di x a y") need two prepositions.

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

-- Non-comparison one-place adjectives need five forms in the worst
-- case (masc and fem singular, masc plural, adverbial).

  mkA : (solo,sola,soli,sole, solamente : Str) -> A ;

-- For regular adjectives, all other forms are derived from the
-- masculine singular. The types of adjectives that are recognized are
-- "alto", "fuerte", "util".

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
-- adjectives: the positive ("bueno"), and the comparative ("mejor"). 

  mkADeg : A -> A -> ADeg ;

-- If comparison is formed by "mas", as usual in Spanish,
-- the following pattern is used:

  compADeg : A -> ADeg ;

-- The regular pattern is the same as $regA$ for plain adjectives, 
-- with comparison by "mas".

  regADeg : Str -> ADeg ;

-- From a given $ADeg$, it is possible to get back to $A$.

  adegA : ADeg -> A ;

-- For prefixed adjectives, the following function is
-- provided.

  prefADeg : ADeg -> ADeg ;

--2 Adverbs

-- Adverbs are not inflected. Most lexical ones have position
-- after the verb. 

  mkAdv : Str -> Adv ;

-- Some appear next to the verb (e.g. "siempre").

  mkAdV : Str -> AdV ;

-- Adverbs modifying adjectives and sentences can also be formed.

  mkAdA : Str -> AdA ;


--2 Verbs
--
-- Regular verbs are ones inflected like "cortar", "deber", or "vivir".
-- The regular verb function is the first conjugation ("ar") recognizes
-- the variations corresponding to the patterns
-- "actuar, cazar, guiar, pagar, sacar". The module $BeschSpa$ gives
-- the complete set of "Bescherelle" conjugations.

  regV : Str -> V ;

-- The module $BeschSpa$ gives all the patterns of the "Bescherelle"
-- book. To use them in the category $V$, wrap them with the function

  verboV : Verbum -> V ;


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


--2 Definitions of the paradigms
--
-- The definitions should not bother the user of the API. So they are
-- hidden from the document.
--.

  Bool   = Prelude.Bool ;
  Gender = SyntaxSpa.Gender ;
  Preposition = SyntaxSpa.Case * Str ;
  Number = SyntaxSpa.Number ;

  masculine = Masc ;
  feminine  = Fem ;

  accusative = <Types.accusative,[]> ;
  genitive = <Types.genitive,[]> ;
  dative = <Types.dative,[]> ;
  mkPreposition p = <Acc,p> ;

  singular = Types.singular ;
  plural = Types.plural ;

  mkN x y g = mkCNomIrreg x y g ** {lock_N = <>} ;
  regN x = mkNomReg x ** {lock_N = <>} ;
  compN x y = {s = \\n => x.s ! n ++ y ; g = x.g ; lock_N = <>} ;
  femN x = {s = x.s ; g = feminine ; lock_N = <>} ;
  mascN x = {s = x.s ; g = masculine ; lock_N = <>} ;

  mkN2 = \n,p -> n ** {lock_N2 = <> ; c = p.p1 ; s2 = p.p2} ;
  deN2 n = mkN2 n genitive ;
  aN2 n = mkN2 n dative ;
  mkN3 = \n,p,q -> n ** {lock_N3 = <> ; c = p.p1 ; s2 = p.p2 ; c3 = q.p1 ; s3 = q.p2} ;

  mkPN x g = {s = x ; g = g} ** {lock_PN = <>} ;
  mkNP x g n = let np = mkNameNounPhrase x g in
    {s = np.s ; g = np.g ; p = np.p ; c = np.c ; n = n ; lock_NP = <>} ;

  mkA a b c d e = mkAdj a b c d e ** {p = False ; lock_A = <>} ;
  regA a = mkAdjReg a ** {p = False ; lock_A = <>} ;
  prefA a = {s = a.s ; p = True ; lock_A = <>} ;

  mkA2 a p = a ** {c = p.p1 ; s2 = p.p2 ; lock_A2 = <>} ;

  mkADeg a b = {s = table {Pos => a.s ; _ => b.s} ; p = a.p ; lock_ADeg = <>} ;
  compADeg a = {s = table {Pos => a.s ; _ => \\f => "mas" ++ a.s ! f} ; p = a.p ;
               lock_ADeg = <>} ;
  regADeg a = compADeg (regA a) ;
  prefADeg a = {s = a.s ; p = True ; lock_ADeg = <>} ;

  adegA a = {s = a.s ! Pos ; p = a.p ; lock_A = <>} ;

  mkAdv x = ss x ** {lock_Adv = <>} ;
  mkAdV x = ss x ** {lock_AdV = <>} ;
  mkAdA x = ss x ** {lock_AdA = <>} ;

  regV x = -- cortar actuar cazar guiar pagar sacar
    let 
      ar = Predef.dp 2 x ;
      z  = Predef.dp 1 (Predef.tk 2 x) ;
      verb = case ar of {
        "ir" =>  vivir_7 x ;
        "er" =>  deber_6 x ;
        _ => case z of {
           "u" => actuar_9 x ;
           "z" => cazar_21 x ;
           "i" => guiar_43 x ;
           "g" => pagar_53 x ;
           "c" => sacar_72 x ;
           _   => cortar_5 x
            }
          }
    in verbPres verb AHabere ** {lock_V = <>} ;

  verboV ve = verbPres ve AHabere ** {lock_V = <>} ;

  mkV2 v p = {s = v.s ; aux = v.aux ;  s2 = p.p2 ; c = p.p1 ; lock_V2 = <>} ;
  dirV2 v = mkV2 v accusative ;
  v2V v = v ** {lock_V = <>} ;

  mkV3 v p q = {s = v.s ; aux = v.aux ; 
    s2 = p.p2 ; s3 = q.p2 ; c = p.p1 ; c3 = q.p1 ; lock_V3 = <>} ;
  dirV3 v p = mkV3 v accusative p ;
  dirdirV3 v = dirV3 v dative ;

  mkV0  v = v ** {lock_V0 = <>} ;
  mkVS  v = v ** {mn,mp = Ind ; lock_VS = <>} ;  ---- more moods
  mkV2S v p = mkV2 v p ** {mn,mp = Ind ; lock_V2S = <>} ;
  mkVV  v = v ** {c = accusative ; lock_VV = <>} ;
  deVV  v = v ** {c = genitive.p1 ; lock_VV = <>} ;
  aVV  v = v ** {c = dative.p1 ; lock_VV = <>} ;
  mkV2V v p t = mkV2 v p ** {c3 = t.p1  ; s3 = p.p2 ; lock_V2V = <>} ;
  mkVA  v = v ** {lock_VA = <>} ;
  mkV2A v p = mkV2 v p ** {lock_V2A = <>} ;
  mkVQ  v = v ** {lock_VQ = <>} ;
  mkV2Q v p = mkV2 v p ** {lock_V2Q = <>} ;

  mkAS  v = v ** {mn,mp = Ind ; lock_AS = <>} ; ---- more moods
  mkA2S v p = mkA2 v p ** {mn,mp = Ind ; lock_A2S = <>} ;
  mkAV  v p = v ** {c = p.p1 ; s2 = p.p2 ; lock_AV = <>} ;
  mkA2V v p q = mkA2 v p ** {s3 = q.p2 ; c3 = q.p1 ; lock_A2V = <>} ;

} ;
