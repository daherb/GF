--1 Finnish Lexical Paradigms
--
-- Aarne Ranta 2003
--
-- This is an API to the user of the resource grammar 
-- for adding lexical items. It give shortcuts for forming
-- expressions of basic categories: nouns, adjectives, verbs.
-- 
-- Closed categories (determiners, pronouns, conjunctions) are
-- accessed through the resource syntax API, $resource.Abs.gf$. 
--
-- The main difference with $morpho.Fin.gf$ is that the types
-- referred to are compiled resource grammar types. We have moreover
-- had the design principle of always having existing forms as string
-- arguments of the paradigms, not stems.
--
-- This is the path to read the grammar from the same directory.
--# -path=.:../abstract:../../prelude
--
-- The following modules are presupposed:

resource ParadigmsFin = open (Predef=Predef), Prelude, SyntaxFin, Finnish in {

--2 Parameters 
--
-- To abstract over gender, number, and (some) case names, 
-- we define the following identifiers.

oper
  human    : Gender ;
  nonhuman : Gender ;

  --  singular : Number ;
  --  singular : Number ;

  nominative : Case ; 
  genitive   : Case ; 
  partitive  : Case ; 
  inessive   : Case ; 
  elative    : Case ; 
  illative   : Case ; 
  adessive   : Case ; 
  ablative   : Case ; 
  allative   : Case ;

--2 Nouns

-- Worst case: give ten forms and the semantic gender.
-- In practice just a couple of forms are needed, to define the different
-- stems, vowel alternation, and vowel harmony.

oper
  mkN : (talo,talon,talona,taloa,taloon,taloina,taloissa,talojen,taloja,taloihin 
          : Str) -> Gender -> N ;

-- Nouns with partitive "a"/"�" are a large group. 
-- To determine for grade and vowel alternation, three forms are usually needed:
-- singular nominative and genitive, and plural partitive.
-- Examples: "talo", "kukko", "huippu", "koira", "kukka", "syyl�", "s�rki"...

  nKukko : (kukko,kukon,kukkoja : Str) -> Gender -> N ;

-- A special case are nouns with no alternations: 
-- the vowel harmony is inferred from the last letter,
-- which must be one of "o", "u", "�", "y".

  nTalo : (talo : Str) -> Gender -> N ;

-- Foreign words ending in consonants are actually similar to words like
-- "malli"/"mallin"/"malleja", with the exception that the "i" is not attached
-- to the singular nominative. Examples: "linux", "savett", "screen".
-- The singular partitive form is used to get the vowel harmony. (N.B. more than 
-- 1-syllabic words ending in "n" would have variant plural genitive and 
-- partitive forms, like "sultanien"/"sultaneiden", which are not covered.)

  nLinux : (linuxia : Str) -> Gender -> N ;

-- Nouns of at least 3 syllables ending with "a" or "�", like "peruna", "tavara",
-- "rytin�".

  nPeruna : (peruna : Str) -> Gender -> N ;

-- The following paradigm covers both nouns ending in an aspirated "e", such as
-- "rae", "perhe", "savuke", and also many ones ending in a consonant
-- ("rengas", "k�tkyt"). The singular nominative and essive are given.

  nRae : (rae, rakeena : Str) -> Gender -> N ;

-- The following covers nouns with partitive "ta"/"t�", such as
-- "susi", "vesi", "pieni". To get all stems and the vowel harmony, it takes
-- the singular nominative, genitive, and essive.

  nSusi : (susi,suden,sutta : Str) -> Gender -> N ;

-- Nouns ending with a long vowel, such as "puu", "p��", "pii", "leikkuu",
-- are inflected according to the following.

  nPuu : (puu : Str) -> Gender -> N ;

-- One-syllable diphthong nouns, such as "suo", "tie", "ty�", are inflected by
-- the following.

  nSuo : (suo : Str) -> Gender -> N ;

-- Many adjectives but also nouns have the nominative ending "nen" which in other
-- cases becomes "s": "nainen", "ihminen", "keltainen". 
-- To capture the vowel harmony, we use the partitive form as the argument.

  nNainen : (naista : Str) -> Gender -> N ;

-- The following covers some nouns ending with a consonant, e.g.
-- "tilaus", "kaulin", "paimen", "laidun".

  nTilaus : (tilaus,tilauksena : Str) -> Gender -> N ;

-- The following covers nouns like "nauris" and adjectives like "kallis", "tyyris".
-- The partitive form is taken to get the vowel harmony.

  nNauris : (naurista : Str) -> Gender -> N ;

-- Separately-written compound nouns, like "sambal oelek", "Urho Kekkonen",
-- have only their last part inflected.

  nComp : Str -> N -> N ;

-- Nouns used as functions need a case, of which by far the commonest is
-- the genitive.

  mkFun  : N -> Case -> Fun ;
  fGen : N -> Fun ;

-- Proper names can be formed by using declensions for nouns.

  mkPN : N -> PN ;


--2 Adjectives

-- Non-comparison one-place adjectives are just like nouns.

  mkAdj1 : N -> Adj1 ;

-- Two-place adjectives need a case for the second argument.

  mkAdj2 : N -> Case -> Adj2 ;

-- Comparison adjectives have three forms. The comparative and the superlative
-- are always inflected in the same way, so the nominative of them is actually
-- enough (except for the superlative "paras" of "hyv�").

  mkAdjDeg : (kiva : N) -> (kivempaa,kivinta : Str) -> AdjDeg ;


--2 Verbs
--
-- The fragment only has present tense so far, but in all persons.
-- The worst case needs five forms, as shown in the following.

  mkV   : (tulla,tulen,tulee,tulevat,tulkaa,tullaan : Str) -> V ;

-- A simple special case is the one with just one stem and no grade alternation.
-- It covers e.g. "sanoa", "valua", "kysy�".

  vValua : (valua : Str) -> V ;

-- With two forms, the following function covers a variety of verbs, such as
-- "ottaa", "k�ytt��", "l�yt��", "huoltaa", "hiiht��", "siirt��".

  vKattaa : (kattaa, katan : Str) -> V ;

-- When grade alternation is not present, just a one-form special case is needed
-- ("poistaa", "ryyst��").

  vOstaa : (ostaa : Str) -> V ;

-- The following covers 
-- "juosta", "piest�", "nousta", "rangaista", "k�vell�", "surra", "panna".

  vNousta : (nousta, nousen : Str) -> V ;

-- This is for one-syllable diphthong verbs like "juoda", "sy�d�".

  vTuoda : (tuoda : Str) -> V ;

-- The verbs "be" and the negative auxiliary are special.

  vOlla : V ;
  vEi   : V ;

-- Two-place verbs need a case, and can have a pre- or postposition.
-- At least one of the latter is empty, $[]$.

  mkTV : V -> Case -> (prep,postp : Str) -> TV ;

-- If both are empty, the following special function can be used.

  tvCase : V -> Case -> TV ;

-- Verbs with a direct (accusative) object
-- are special, since their complement case is finally decided in syntax.

  tvDir : V -> TV ;

-- The definitions should not bother the user of the API. So they are
-- hidden from the document.
--.
  -- singular defined in types.Fin
  -- plural defined in types.Fin

  human = Human ; 
  nonhuman = NonHuman ;

  nominative = Nom ;
  genitive = Gen ;
  partitive = Part ;
  inessive = Iness ;
  elative = Elat ;
  illative = Illat ;
  adessive = Adess ;
  ablative = Ablat ;
  allative = Allat ;

  mkN = \a,b,c,d,e,f,g,h,i,j,k -> mkNoun a b c d e f g h i j ** {g = k} ;

  nKukko = \a,b,c,g -> sKukko a b c ** {g = g} ;
  nTalo = \a,g -> sTalo a ** {g = g} ;
  nLinux = \a,g -> sLinux a ** {g = g} ;
  nPeruna = \a,g -> sPeruna a ** {g = g} ;
  nRae = \a,b,g -> sRae a b ** {g = g} ;
  nSusi = \a,b,c,g -> sSusi a b c ** {g = g} ;
  nPuu = \a,g -> sPuu a ** {g = g} ;
  nSuo = \a,g -> sSuo a ** {g = g} ;
  nNainen = \a,g -> sNainen a ** {g = g} ;
  nTilaus = \a,b,g -> sTilaus a b ** {g = g} ;
  nNauris = \a,g -> sNauris a ** {g = g} ;


  nComp = \s,n -> {s = \\c => s ++ n.s ! c ; g = n.g} ;
  mkFun = \n,c -> n2n n ** {c = NPCase c} ;
  fGen = \n -> mkFun n genitive ;
  mkPN = mkProperName ;

  mkAdj1 = \x -> {s = x.s} ;
  mkAdj2 = \x,c -> mkAdj1 x ** {c = NPCase c} ;
  mkAdjDeg = regAdjDegr ;

  mkV = mkVerb ;
  vValua = vSanoa ;
  vKattaa = vOttaa ;
  vOstaa = vPoistaa ;
  vNousta = vJuosta ;
  vTuoda = vJuoda ;
  vOlla = verbOlla ;
  vEi = verbEi ;

  mkTV = \v,c,p,o -> v ** {s3 = p ; s4 = o ; c = c} ;
  tvCase = \v,c -> mkTV v c [] [] ; 
  tvDir = mkTransVerbDir ;
} ;
