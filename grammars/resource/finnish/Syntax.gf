--1 A Small Finnish Resource Syntax
--
-- Aarne Ranta 2003
--
-- This resource grammar contains definitions needed to construct 
-- indicative, interrogative, and imperative sentences in Finnish.
--
-- The following files are presupposed:

resource Syntax = Morpho ** open Prelude, (CO = Coordination) in {

--2 Common Nouns
--
-- Simple common nouns are defined as the type $CommNoun$ in $morpho.Fin.gf$.

--3 Common noun phrases

-- In Finnish, common noun phrases behave like simple common nouns, except that
-- we need a kind of a *gender* parameter telling if the noun is human or not.
-- This parameter regulates determiners such as "joku"/"jokin" ('some') and
-- "kuka"/"mik�" ('which').
--
-- A subtle reason forces us to distinguish the parameters of common noun phrases
-- from those of morphological common nouns: the parameter value $NPossNom$ is
-- syntactically applicable to each of $Sg Nom$, $Pl Nom$, $Sg Gen$. In morphology,
-- these forms are always the same ("autoni"), but with complex common nouns, we
-- have three different forms: "iso autoni", "isot autoni", "ison autoni".

oper
  CommNoun = {s : NForm =>  Str ; g : Gender} ;

  CommNounPhrase = {s : Bool => Number => Case =>  Str ; g : Gender} ;

  noun2CommNounPhrase : CommNoun -> CommNounPhrase = \man ->
    useCN man ** {g = man.g} ;

  n2n = noun2CommNounPhrase ;

  useCN : CommonNoun -> {s : Bool => Number => Case =>  Str} = \auto -> 
    {s = table {
      True  => \\n,c => case <n,c> of {
        <_, Nom>   => auto.s ! NPossNom ; 
        <Sg,Gen>   => auto.s ! NPossNom ;
        <Pl,Gen>   => auto.s ! NPossGenPl ;
        <_,Transl> => auto.s ! NPossTransl n ;
        <_,Illat>  => auto.s ! NPossIllat n ;
        _          => auto.s ! NCase n c
      } ;
      False => \\n,c => auto.s ! NCase n c
      }
    } ; 

  cnNoHum : CommonNoun -> CommNoun = \cn -> cn ** {g = NonHuman} ;
  cnHum   : CommonNoun -> CommNoun = \cn -> cn ** {g = Human} ;

--2 Noun phrases
--
-- Two forms of *virtual accusative* are needed for nouns in singular, 
-- the nominative and the genitive one ("ostan talon"/"osta talo"). 
-- For nouns in plural, only a nominative accusative exist. Pronouns
-- have a uniform, special accusative form ("minut", etc).

param 
  NPForm = NPCase Case | NPAccNom | NPAccGen ;

-- The *person* of a noun phrase is also special, to steer the use of
-- possessive suffixes. It expresses a distinction between pronominal and
-- non-pronominal noun phrases. The pronominal ones impose possessive suffixes
-- in genitival constructions ("minun taloni", "h�nen talonsa"), the non-pronominal
-- ones don't ("Jussin talo"). As for verbal agreement, non-pronominal noun
-- phrases are third-person.

  NPPerson = NP3 | NPP Person ;

oper
  np2Person : NPPerson -> Person = \n -> case n of {
    NP3 => P3 ;
    NPP p => p
    } ;

oper
  npForm2Case : Number -> NPForm -> Case = \n,f -> case f of {
    NPCase c => c ;
    NPAccNom => Nom ;
    NPAccGen => case n of {
      Sg => Gen ;
      Pl => Nom
      } 
    } ;

  npForm2PForm : NPForm -> PForm = \f -> case f of {
    NPCase c => PCase c ;
    _ => PAcc 
    } ;

  NounPhrase : Type = {s : NPForm => Str ; n : Number ; p : NPPerson} ;

  nameNounPhrase : ProperName -> NounPhrase = \jussi -> 
    {s = \\f => jussi.s ! npForm2Case Sg f ; n = Sg ; p = NP3} ;

  singularNounPhrase : CommNounPhrase -> NounPhrase = \cn ->
    {s = \\f => cn.s ! False ! Sg ! (npForm2Case Sg f) ; n = Sg ; p = NP3} ;

  pluralNounPhrase : CommNounPhrase -> NounPhrase = \cn ->
    {s = \\f => cn.s ! False ! Pl ! (npForm2Case Pl f) ; n = Pl ; p = NP3} ;

  pronNounPhrase : Pronoun -> NounPhrase = \pron ->
    {s = \\f => pron.s ! npForm2PForm f ; n = pron.n ; p = NPP pron.p} ;

-- *Partitive noun phrases* use the partitive instead of the nominative
-- and accusative forms.

  npForm2CasePart : NPForm -> Case = \f -> case f of {
    NPCase Nom => Part ;
    NPCase c => c ;
    _ => Part
    } ;

  partNounPhrase : Number -> CommNounPhrase -> NounPhrase = \n, cn ->
    {s = \\f => cn.s ! False ! n ! (npForm2CasePart f) ; n = n ; p = NP3} ;



--2 Determiners
--
-- Most determiners are inflected like nouns. They have an inherent number
-- that is given to the noun that is being determined.

  Determiner : Type = {s : Gender => Case => Str ; n : Number} ;

  detNounPhrase : Determiner -> CommNounPhrase -> NounPhrase = \joku, mies -> 
    {s = \\f => let {c = npForm2Case joku.n f} in 
                joku.s ! mies.g ! c ++ mies.s ! False ! joku.n ! c ; 
     n = joku.n ; 
     p = NP3
    } ;

  mkDeterminerGen : Number -> (_,_ : Case => Str) -> Determiner = \n,mika,kuka -> 
    {s = table {
           NonHuman => mika ;
           Human    => kuka
         } ; 
     n = n
    } ;

  mkDeterminer : Number -> (Case => Str) -> Determiner = \n,kaikki -> 
    mkDeterminerGen n kaikki kaikki ;

  jokainenDet = mkDeterminer Sg (caseTable Sg (sNainen "jokaista")) ;
  kaikkiDet = mkDeterminer Pl kaikkiPron ;
  useimmatDet = mkDeterminer Pl (caseTable Pl (sSuurin "useinta")) ;
  mikaDet     = mkDeterminerGen Sg (mikaInt ! Sg) (kukaInt ! Sg) ;
  mitkaDet    = mkDeterminerGen Pl (mikaInt ! Pl) (kukaInt ! Pl) ;

  indefNounPhrase : Number -> CommNounPhrase -> NounPhrase = \n,mies -> 
    case n of {
      Sg => singularNounPhrase mies ;
      Pl => partNounPhrase plural mies
    } ;

  defNounPhrase : Number -> CommNounPhrase -> NounPhrase = \n,mies -> 
    case n of {
      Sg => singularNounPhrase mies ;
      Pl => pluralNounPhrase mies
    } ;


-- Genitives of noun phrases can be used like determiners, to build noun phrases.
-- The number argument makes the difference between "Jussin talo" - "Jussin talot".
-- The NP person of the 'owner' decides if there is a possessive suffix.

  npGenDet : Number -> NounPhrase -> CommNounPhrase -> NounPhrase = \n,jussi,talo ->
    {s = \\c => jussi.s ! NPCase Gen ++ 
                ifPossSuffix talo jussi.p jussi.n (npForm2Case n c) ;
     n = n ; 
     p = NP3
    } ;

  ifPossSuffix : CommNounPhrase -> NPPerson -> Number -> Case -> Str = 
    \talo,np,n,c -> case np of {
      NP3   => talo.s ! False ! n ! c ;
      NPP p => talo.s ! True ! n ! c ++ possSuffix ! n ! p
    } ;

-- *Bare plural noun phrases*, like "koivut" in "koivut ovat valkoisia", 
-- are similar to definite plurals.

  plurDet : CommNounPhrase -> NounPhrase = pluralNounPhrase ;


--2 Adjectives
--
-- Adjectival phrases are used either as attributes or in predicative position.
-- In the attributive position, all cases occur; in the predicative position, only 
-- the nominative, partitive, translative, and essive - but we ignore this 
-- restriction for simplicity. The important thing with the parameter is to
-- regulate the word order of complex adjectival phrases: cf. predicative
-- "(kuusi on) jaollinen kolmella" vs. attributive "kolmella jaollinen (luku)".
-- In comparatives, the whole construction is affected: "suurempi kuin kolme"
-- vs. "kolmea suurempi". (Actually, in the predicative position, the two
-- are in free variation, the distinguished one being the normal choice:
-- "kuusi on kolmella jaollinen" is possible, but not quite neutral.)

param
  AdjPos = APred | AAttr ;

oper
  AdjPhrase : Type = {s : AdjPos => Number => Case => Str} ;

  adj2adjPhrase : Adjective -> AdjPhrase = \uusi -> 
    {s = \\_,n,c => uusi.s ! NCase n c} ;


--3 Comparison adjectives
--
-- Each of the comparison forms has a characteristic use:
--
-- Positive forms are used alone, as adjectival phrases ("iso").

  positAdjPhrase : AdjDegr -> AdjPhrase = \iso -> 
    adj2adjPhrase {s = iso.s ! Pos} ;

-- Comparative forms are used with an object of comparison, as
-- adjectival phrases ("isompi kuin te"/"teit� isompi").

  comparAdjPhrase : AdjDegr -> NounPhrase -> AdjPhrase = \iso, te ->
    {s = let {teitaisompi : Number => Case => Str = 
              \\n,c => te.s ! NPCase Part ++ iso.s ! Comp ! NCase n c} in 
         table {
           APred => variants {
             \\n,c => iso.s ! Comp ! NCase n c ++ kuinConj ++ te.s ! NPCase Nom ;
             teitaisompi
             } ;     
           AAttr => teitaisompi
         }
    } ;

-- Superlative forms are used with a modified noun, picking out the
-- maximal representative of a domain ("isoin talo").

  superlNounPhrase : AdjDegr -> CommNounPhrase -> NounPhrase = \iso,talo ->
    {s = \\np => let {c = npForm2Case Sg np} in
                 iso.s ! Sup ! NCase Sg c ++ talo.s ! False ! Sg ! c ; 
     n = Sg ; 
     p = NP3
    } ;

--3 Two-place adjectives
--
-- A two-place adjective is an adjective with a case used after (or before)
-- the complement. The case can be the genitival accusative, which is different
-- in the singular and the plural ("rajan ylitt�v�"/"rajat ylitt�v�"). 
-- The order of the adjective and its argument depends on the case: the local
-- cases favour Adj + Noun in the predicative position ("hyv� painissa",
-- "tyytyv�inen vaalitulokseen", "jaollinen kolmella"), which is not a possible
-- order for the accusative case.

  AdjCompl = Adjective ** {c : NPForm} ;

  complAdj : AdjCompl -> NounPhrase -> AdjPhrase = \hyva,paini ->
    let {
      hyvat : Number => Case => Str = \\n,c => hyva.s ! NCase n c ;
      painissa : Str = paini.s ! hyva.c
      }
    in
    {s = table {
           AAttr => \\n,c => painissa ++ hyvat ! n ! c ; 
           APred => \\n,c => if_then_else Str 
                               (isLocalNPForm hyva.c)
                               (variants {
                                  hyvat ! n ! c ++ painissa ;
                                  painissa ++ hyvat ! n ! c
                                  }
                               )
                               (painissa ++ hyvat ! n ! c)
           }
     } ;

  isLocalNPForm : NPForm -> Bool = \c -> case c of {
     NPCase Iness => True ;
     NPCase Elat  => True ;
     NPCase Illat => True ;
     NPCase Adess => True ;
     NPCase Ablat => True ;
     NPCase Allat => True ;
     _ => False
     } ;


--3 Modification of common nouns
--
-- The two main functions of adjective are in predication ("Jussi on iso")
-- and in modification ("iso mies"). Predication will be defined
-- later, in the chapter on verbs.
--
-- Modification uses the attributive form of an adjectival phrase.
-- The adjective always comes before the noun. The possessive suffix is
-- given to the noun.

  modCommNounPhrase : AdjPhrase -> CommNounPhrase -> CommNounPhrase = \iso,mies -> 
    {s = \\p,n,c => iso.s ! AAttr ! n ! c ++ mies.s ! p ! n ! c ;
     g = mies.g
    } ;

--2 Function expressions

-- A function expression is a common noun together with the
-- case taken by its argument ("x'n vaimo").
-- The type is analogous to two-place adjectives and transitive verbs;
-- but here the genitive is by far the commonest case. The possessive suffix
-- is then needed with pronominal arguments.

  Function = CommNounPhrase ** {c : NPForm} ;

-- The application of a function gives, in the first place, a common noun:
-- "Jussi vaimo/vaimot". From this, other rules of the resource grammar 
-- give noun phrases, such as "Jussi vaimo", "Jussin vaimot",
-- "Jussin ja Marin �idit", and "Jussin ja Marin �iti" (the
-- latter two corresponding to distributive and collective functions,
-- respectively). Semantics will eventually tell when each
-- of the readings is meaningful.

  appFunComm : Function -> NounPhrase -> CommNounPhrase = \vaimo, jussi -> 
    {s = \\p,n,c => case vaimo.c of {
           NPCase Gen => jussi.s ! NPCase Gen ++ 
                         ifPossSuffix vaimo jussi.p jussi.n c ;
           h => vaimo.s ! False ! n ! c ++ jussi.s ! h
          } ;  
     g = vaimo.g
    } ;

-- Notice the switched word order in other cases than the genitive, e.g.
-- "veli Jussille".
--
-- It is possible to use a function word as a common noun; the semantics is
-- often existential or indexical.

  funAsCommNounPhrase : Function -> CommNounPhrase = \x -> x ;

-- The following is an aggregate corresponding to function application
-- producing "John's mother" and "the mother of John". It does not appear in the
-- resource grammar API as a primitive.

  appFun : Bool -> Function -> NounPhrase -> NounPhrase = \coll, vaimo,jussi -> 
    let {n = jussi.n ; nf = if_then_else Number coll Sg n} in 
    npGenDet nf jussi vaimo ;      

-- The commonest case is functions with the genitive case.

  funGen : CommNounPhrase -> Function = \vaimo -> 
    vaimo ** {c = NPCase Gen} ;

-- Two-place functions add one argument place.

  Function2 = Function ** {c2 : NPForm} ;

-- There application starts by filling the first place.

  appFun2 : Function2 -> NounPhrase -> Function = \juna, turku ->
    {s = \\p,n,c => juna.s ! False ! n ! c ++ turku.s ! juna.c ;  
     g = juna.g ;
     c = juna.c2
    } ;


--2 Verbs
--
--3 Verb phrases
--
-- Verb phrases are discontinuous: the two parts of a verb phrase are
-- (s) an inflected verb, (s2) a complement.
-- For instance: "on" - "kaunis" ; "ei" - "ole kaunis" ; "sis�lt��" - "rikki�".

  VerbPhrase = Verb ** {s2 : VForm => Str} ;

-- From the inflection table, we select the finite form as function 
-- of person and number:

  indicVerb : Verb -> Person -> Number -> Str = \v,p,n -> 
    v.s ! Ind n p ;

-- A simple verb can be made into a verb phrase with an empty complement, e.g.
-- "ui" - [].
-- There are two versions, depending on if we want to negate the verb.
-- In the negated form, the negative verb "ei" becomes the verb, and the
-- complement is a special infinite form of the verb (usually similar to the
-- 2nd person singular imperative): "ei" - "ui".
-- 
-- N.B. negation is *not* a function applicable to a verb phrase, since
-- double negations with "ei" are not grammatical.

  predVerb : Bool -> Verb -> VerbPhrase = \b,walk ->
     let {
       noCompl  : {s2 : VForm => Str} = {s2 = \\_ => []} ;
       infCompl : {s2 : VForm => Str} = {s2 = table {
                                                Imper Pl => walk.s ! ImpNegPl ;
                                                _ => walk.s ! vFormNeg
                                                }
                                        }
       } 
     in if_then_else VerbPhrase b (walk ** noCompl) (verbEi ** infCompl) ; 

-- (N.B. local definitions workaround for poor type inference in GF 1.2).

-- Sometimes we want to extract the verb part of a verb phrase. Not strictly
-- necessary since this is a consequence of record subtyping.

  verbOfPhrase : VerbPhrase -> Verb = \v -> {s = v.s} ;

-- Verb phrases can also be formed from adjectives ("on vanha"),
-- common nouns ("on mies"), and noun phrases ("on Jussi").
-- The third rule is overgenerating: "on jokainen mies" has to be ruled out
-- on semantic grounds.
--
-- For adjectives and common nouns, notice the case difference in the complement
-- depending on number: "on kaunis" - "ovat kauniita". We ignore the forms
-- "on kaunista", used with mass terms, and "ovat kauniit", used in 
-- constructions of the "plurale tantum" kind. The adjective rule can be defined
-- in terms of the common noun rule.

  predAdjective : Bool -> AdjPhrase -> VerbPhrase = \b,iso ->
    let {isot : CommNounPhrase = {s = \\_ => iso.s ! APred ; g = NonHuman}} 
    in predCommNoun b isot ;

  predCommNoun : Bool -> CommNounPhrase -> VerbPhrase = \b,mies ->
    let {
      miehia : VForm => Str = \\v => case vform2number v of {
        Sg => mies.s ! False ! Sg ! Nom ; 
        Pl => mies.s ! False ! Pl ! Part
        } ;
      olemiehia : VForm => Str = 
        \\v => verbOlla.s ! vFormNeg ++ miehia ! v
      }
    in if_then_else VerbPhrase b 
         (verbOlla ** {s2 = miehia})
         (verbEi   ** {s2 = olemiehia}) ;

  predNounPhrase : Bool -> NounPhrase -> VerbPhrase = \b,jussi ->
    let {jussia : Bool => Number => Case => Str = \\_,_,_ => jussi.s ! NPCase Nom}
    in predCommNoun b {s = jussia ; g = Human} ; --- gender does not matter


--3 Transitive verbs
--
-- Transitive verbs are verbs with a case and, possibly, a preposition
-- or a postposition for the complement,
-- in analogy with two-place adjectives and functions.
-- One might prefer to use the term "2-place verb", since
-- "transitive" traditionally means that the inherent preposition is empty.
-- Such a verb is one with a *direct object*.

param
  ComplCase = CCase Case | CAcc ;

oper
  TransVerb : Type = Verb ** {s3, s4 : Str ; c : ComplCase} ;

-- The rule for using transitive verbs is the complementization rule.
--
-- N.B. One or both of the pre- and postposition are empty.

  complTransVerb : Bool -> TransVerb -> NounPhrase -> VerbPhrase = \b,ostaa,talo ->
    let {
      ostan = predVerb b ostaa ;
      talon : VForm => Str = \\v => 
                ostaa.s3 ++ talo.s ! complementCase b ostaa.c v ++ ostaa.s4
      }
    in {
      s  = ostan.s ;
      s2 = \\v => ostan.s2 ! v ++ talon ! v
      } ;

-- N.B. If the case is accusative, it becomes partitive in negated verb phrases.
-- The choice between the nominative and genitive accusatives depends on the verb
-- form.

  complementCase : Bool -> ComplCase -> VForm -> NPForm = \b,c,v -> case c of {
    CCase k => NPCase k ;
    CAcc => case b of {
      True => case v of {
        Inf => NPAccNom ;
        Ind _ _ => NPAccGen ;
        Imper _ => NPAccNom ;
        ImpNegPl => NPCase Part
        } ;
      _ => NPCase Part
      }
    } ;

-- Verbs that take their object with a case other than the accusative, 
-- without pre- or postposition:

  mkTransVerbCase : Verb -> Case -> TransVerb = \nauraa,c -> 
    nauraa ** {s3 = [] ; s4 = [] ; c = CCase c} ;

-- Verbs that take direct object with the accusative:

  mkTransVerbDir : Verb -> TransVerb = \ostaa -> 
    ostaa ** {s3 = [] ; s4 = [] ; c = CAcc} ;

-- Transitive verbs can be used elliptically as verbs. The semantics
-- is left to applications. The definition is trivial, due to record
-- subtyping.

  transAsVerb : TransVerb -> Verb = \juoda -> 
    juoda ;

-- *Ditransitive verbs* are verbs with three argument places.
-- We treat so far only the rule in which the ditransitive
-- verb takes both complements to form a verb phrase.

  DitransVerb = TransVerb  ** {s5, s6 : Str ; c2 : ComplCase} ;

  complDitransVerb : 
    Bool -> DitransVerb -> NounPhrase -> NounPhrase -> VerbPhrase = 
    \b,ostaa,talo,me ->
    let {
      ostan = predVerb b ostaa ;
      talon : VForm => Str = \\v => 
                ostaa.s3 ++ talo.s ! complementCase b ostaa.c v ++ ostaa.s4 ;
      meille : VForm => Str = \\v => 
                ostaa.s5 ++ me.s ! complementCase b ostaa.c2 v ++ ostaa.s6
      }
    in {
      s  = ostan.s ;
      s2 = \\v => ostan.s2 ! v ++ talon ! v ++ meille ! v
      } ;


--2 Adverbials
--
-- Adverbials are not inflected (we ignore comparison, and treat
-- compared adverbials as separate expressions; this could be done another way).

  Adverb : Type = SS ;

-- This rule adds the adverbial as a prefix or a suffix to the complement,
-- in free variation.

  adVerbPhrase : VerbPhrase -> Adverb -> VerbPhrase = \laulaa, hyvin ->
    {s = laulaa.s ;
     s2 = \\v => bothWays (laulaa.s2 ! v) hyvin.s 
    } ;

  advAdjPhrase : Adverb -> AdjPhrase -> AdjPhrase = \liian, iso ->
    {s = \\p,n,c => liian.s ++ iso.s ! p ! n ! c
    } ;

-- Adverbials are typically generated by case, prepositions, or postpositions.
-- The rule for creating locative noun phrases by the inessive case
-- is a shaky, since the adessive is often required.

  prepPhrase : Str -> Case -> NounPhrase -> Adverb = \ennen,c,talvi ->
    ss (ennen ++ talvi.s ! NPCase c) ;

  postpPhrase : Str -> Case -> NounPhrase -> Adverb = \aikana,c,talvi ->
    ss (talvi.s ! NPCase c ++ aikana) ;

  caseAdv : Case -> NounPhrase -> Adverb = prepPhrase [] ;

  locativeNounPhrase : NounPhrase -> Adverb = \np -> --- caseAdv Iness ;
    ss (np.s ! NPCase Iness) ;

-- This is a source of the "mann with a telescope" ambiguity, and may produce
-- strange things, like "autot aina" (while "autot t�n��n" is OK).
-- Semantics will have to make finer distinctions among adverbials.

  advCommNounPhrase : CommNounPhrase -> Adverb -> CommNounPhrase = \auto,nyt ->
   {s = \\b,n,c => auto.s ! b ! n ! c ++ nyt.s ;
    g = auto.g
   } ;

--2 Sentences
--
-- Sentences are not inflected in this fragment of Finnish without tense.

  Sentence : Type = SS ;

-- This is the traditional $S -> NP VP$ rule. It takes care of
-- agreement between subject and verb. Recall that the VP may already
-- contain negation. 

  predVerbPhrase : NounPhrase -> VerbPhrase -> Sentence = \jussi,uida ->
    let {p = np2Person jussi.p} in
    ss (jussi.s ! NPCase Nom ++ uida.s ! Ind jussi.n p ++ uida.s2 ! Ind jussi.n p) ;

-- This is a macro for simultaneous predication and complementization.

  predTransVerb : Bool -> NounPhrase -> TransVerb -> NounPhrase -> Sentence = 
    \b,you,see,john -> 
    predVerbPhrase you (complTransVerb b see john) ;

--3 Sentence-complement verbs
--
-- Sentence-complement verbs take sentences as complements.

  SentenceVerb : Type = Verb ;

-- To generate "sanoo ett� Jussi ui" / "ei sano ett� Jussi ui"

  complSentVerb : Bool -> SentenceVerb -> Sentence -> VerbPhrase = 
    \b,sanoa,jussiui ->
    let {
      sanon = predVerb b sanoa
      }
    in {
      s  = sanon.s ;
      s2 = \\v => sanon.s2 ! v ++ conjEtta ++ jussiui.s
      } ;


--2 Sentences missing noun phrases
--
-- This is one instance of Gazdar's *slash categories*, corresponding to his
-- $S/NP$.
-- We cannot have - nor would we want to have - a productive slash-category former.
-- Perhaps a handful more will be needed.
--
-- Notice that the slash category has a similar relation to sentences as
-- transitive verbs have to verbs: it's like a *sentence taking a complement*.
--
-- Interestingly, the distinction between prepositions and postpositions 
-- neutralizes: even prepositions are attached after relative and interrogative
-- pronouns: "jota ennen" cf. "ennen talvea". Otherwise, the category and
-- the rules are very similar to transitive verbs. Notice that the case gets
-- fixed by the Boolean parameter and the subject.

  SentenceSlashNounPhrase = Sentence ** {s2 : Str ; c : Case} ;

  slashTransVerb : Bool -> NounPhrase -> TransVerb -> SentenceSlashNounPhrase = 
    \b,jussi,ostaa ->
    predVerbPhrase jussi (predVerb b ostaa) ** {
      s2 = ostaa.s3 ++ ostaa.s4 ;
      c  = npForm2Case jussi.n 
                       (complementCase b ostaa.c (Ind jussi.n (np2Person jussi.p)))
      } ;

--2 Relative pronouns and relative clauses
--
-- As described in $types.Fin.gf$, relative pronouns are inflected like 
-- common nouns, in number and case.
--
-- We get the simple relative pronoun "joka" from $morpho.Fin.gf$.

  identRelPron : RelPron = relPron ;

  funRelPron : Function -> RelPron -> RelPron = \vaimo, joka -> 
    {s = \\n,c => joka.s ! n ! npForm2Case n vaimo.c ++ vaimo.s ! False ! n ! c} ;

-- Relative clauses can be formed from both verb phrases ("joka ui") and
-- slash expressions ("jonka sin� n�et", "jonka kautta sin� k�yt"). 

  RelClause : Type = {s : Number => Str} ;

  relVerbPhrase : RelPron -> VerbPhrase -> RelClause = \joka,ui ->
    {s = \\n => joka.s ! n ! Nom ++ ui.s ! Ind n P3 ++ ui.s2 ! Ind n P3} ;

  relSlash : RelPron -> SentenceSlashNounPhrase -> RelClause = \joka,saat ->
    {s = \\n => joka.s ! n ! saat.c ++ saat.s2 ++ saat.s} ;

-- A 'degenerate' relative clause is the one often used in mathematics, e.g.
-- "luku x siten ett� x on parillinen".

  relSuch : Sentence -> RelClause = \A ->
    {s = \\_ => advSiten ++ conjEtta ++ A.s} ;

-- N.B. the construction "sellainen ett�" is not possible with the present
-- typing of the relative clause, since it should also be inflected in
-- case. Ordinary relative clauses have a fixed case.
--
-- The main use of relative clauses is to modify common nouns.
-- The result is a common noun, out of which noun phrases can be formed
-- by determiners. We use no comma before these relative clauses, even though
-- conservative standard Finnish does.

  modRelClause : CommNounPhrase -> RelClause -> CommNounPhrase = \mies,jokaui ->
    {s = \\b,n,c => mies.s ! b ! n ! c ++ jokaui.s ! n ;
     g = mies.g
    } ;

-- N.B: the possessive suffix, if attached here, comes to wrong place! Solution:
-- make $CommNounPhrase$ discontinuos.


--2 Interrogative pronouns
--
-- If relative pronouns are like common nouns (and adjectives), 
-- interrogative pronouns are like noun phrases, having a fixed number.
-- They also need to handle an NP-like accusative case. But person is
-- not needed, since it is uniformly $NP3$.

  IntPron : Type = {s : NPForm => Str ; n : Number} ; 

-- In analogy with relative pronouns, we have a rule for applying a function
-- to a relative pronoun to create a new one. 

  funIntPron : Function -> IntPron -> IntPron = \vaimo,kuka -> 
    {s = \\c => kuka.s ! vaimo.c ++ 
                vaimo.s ! False ! kuka.n ! npForm2Case kuka.n c ;
     n = kuka.n
    } ;

-- There is a variety of simple interrogative pronouns:
-- "mik� talo" / "kuka mies", "kuka", "mik�". The construction with a noun
-- is the reason why nouns in Finnish need a gender.

  nounIntPron : Number -> CommNounPhrase -> IntPron = \n, talo ->
    {s = \\c => let {nc = npForm2Case n c} in 
                mikakukaInt ! talo.g ! n ! nc ++ talo.s ! False ! n ! nc ;
     n = n
    } ; 

  intPronWho : Number -> IntPron = \num -> {
    s = \\c => mikakukaInt ! Human ! num ! (npForm2Case num c) ;
    n = num
  } ;

  intPronWhat : Number -> IntPron = \num -> {
    s = \\c => mikakukaInt ! NonHuman ! num ! (npForm2Case num c) ;
    n = num
  } ;


--2 Utterances

-- By utterances we mean complete phrases, such as 
-- 'can be used as moves in a language game': indicatives, questions, imperative,
-- and one-word utterances. The rules are far from complete.
--
-- N.B. we have not included rules for texts, which we find we cannot say much
-- about on this level. In semantically rich GF grammars, texts, dialogues, etc, 
-- will of course play an important role as categories not reducible to utterances.
-- An example is proof texts, whose semantics show a dependence between premises
-- and conclusions. Another example is intersentential anaphora.

  Utterance = SS ;
  
  indicUtt : Sentence -> Utterance = \x -> ss (x.s ++ stopPunct) ;
  interrogUtt : Question -> Utterance = \x -> ss (x.s ++ questPunct) ;


--2 Questions
--
-- Questions are either direct or indirect, but the forms in Finnish are
-- always identical. So we don't need a $QuestForm$ parameter as in other languages.

oper
  Question = SS ;

--3 Yes-no questions 
--
-- Yes-no questions are formed by inversed predication, with the clitic "ko" / "k�"
-- particle attached to the verb part of the verb phrase.

  questVerbPhrase : NounPhrase -> VerbPhrase -> Question = \jussi,ui ->
    let {np = Ind jussi.n (np2Person jussi.p)} in
    ss (ui.s ! np ++ koPart ++ jussi.s ! NPCase Nom ++ ui.s2 ! np) ;


--3 Wh-questions
--
-- Wh-questions are of two kinds: ones that are like $NP - VP$ sentences
-- ("kuka ui?") others that are line $S/NP - NP$ sentences ("kenet sin� tapaat?").

  intVerbPhrase : IntPron -> VerbPhrase -> Question = \kuka,ui ->
    predVerbPhrase (kuka ** {p = NP3}) ui ;

  intSlash : IntPron -> SentenceSlashNounPhrase -> Question = \kuka,tapaat ->
    ss (kuka.s ! NPCase tapaat.c ++ tapaat.s2 ++ tapaat.s) ;


--3 Interrogative adverbials
--
-- These adverbials will be defined in the lexicon: they include
-- "koska", "miss�", "kuinka", "miksi", etc, which are all invariant one-word
-- expressions. In addition, they can be formed by adding cases and postpositions
-- to interrogative pronouns, in the same way as adverbials are formed
-- from noun phrases; notice that even prepositions are used as postpositions
-- when attached to interrogative pronouns.

  IntAdverb = SS ;

  prepIntAdverb : Str -> Case -> IntPron -> IntAdverb = \ennen,c,kuka ->
    ss (kuka.s ! NPCase c ++ ennen) ;

-- A question adverbial can be applied to anything, and whether this makes
-- sense is a semantic question. The syntax is very simple: just prefix the
-- adverbial to the predication.

  questAdverbial : IntAdverb -> NounPhrase -> VerbPhrase -> Question = 
    \miksi, jussi, ui ->
    cc2 miksi (predVerbPhrase jussi ui) ;

--2 Imperatives
--
-- We only consider second-person imperatives. 

  Imperative = SS1 Number ;

  imperVerbPhrase : VerbPhrase -> Imperative = \ui -> 
    {s = \\n => ui.s ! Imper n ++ ui.s2 ! Imper n} ;

  imperUtterance : Number -> Imperative -> Utterance = \n,I ->
    ss (I.s ! n ++ exclPunct) ;

--2 Sentence adverbials
--
-- This class covers adverbials such as "muuten", "siksi", which are prefixed
-- to a sentence to form a phrase.

  advSentence : Adverb -> Sentence -> Utterance = \siksi,sataa ->
    ss (siksi.s ++ sataa.s ++ ".") ;


--2 Coordination
--
-- Coordination is to some extent orthogonal to the rest of syntax, and
-- has been treated in a generic way in the module $CO$ in the file
-- $coordination.gf$. The overall structure is independent of category,
-- but there can be differences in parameter dependencies.
--
--3 Conjunctions
--
-- Coordinated phrases are built by using conjunctions, which are either
-- simple ("ja", "tai") or distributed ("sek� - ett�", "joko - tai").
--
-- The conjunction has an inherent number, which is used when conjoining
-- noun phrases: "Jussi ja Mari ovat..." vs. "Jussi tai Mari on..."; in the
-- case of "tai", the result is however plural if any of the disjuncts is.

  Conjunction = CO.Conjunction ** {n : Number} ;
  ConjunctionDistr = CO.ConjunctionDistr ** {n : Number} ;

--3 Coordinating sentences
--
-- We need a category of lists of sentences. It is a discontinuous
-- category, the parts corresponding to 'init' and 'last' segments
-- (rather than 'head' and 'tail', because we have to keep track of the slot between
-- the last two elements of the list). A list has at least two elements.

  ListSentence : Type = SD2 ;

  twoSentence : (_,_ : Sentence) -> ListSentence = CO.twoSS ;

  consSentence : ListSentence -> Sentence -> ListSentence =
    CO.consSS CO.comma ;

-- To coordinate a list of sentences by a simple conjunction, we place
-- it between the last two elements; commas are put in the other slots,
-- e.g. "du rauchst, er trinkt und ich esse".

  conjunctSentence : Conjunction -> ListSentence -> Sentence = \c,xs ->
    ss (CO.conjunctX c xs) ;

-- To coordinate a list of sentences by a distributed conjunction, we place
-- the first part (e.g. "either") in front of the first element, the second
-- part ("or") between the last two elements, and commas in the other slots.
-- For sentences this is really not used.

  conjunctDistrSentence : ConjunctionDistr -> ListSentence -> Sentence = 
    \c,xs ->
    ss (CO.conjunctDistrX c xs) ;


--3 Coordinating adjective phrases
--
-- The structure is the same as for sentences. Parameters are passed to components.

  ListAdjPhrase : Type = 
    {s1,s2 : AdjPos => Number => Case => Str} ;

  twoAdjPhrase : (_,_ : AdjPhrase) -> ListAdjPhrase = \x,y ->
    CO.twoTable3 AdjPos Number Case x y ;

  consAdjPhrase : ListAdjPhrase -> AdjPhrase -> ListAdjPhrase =  \xs,x ->
    CO.consTable3 AdjPos Number Case CO.comma xs x ;

  conjunctAdjPhrase : Conjunction -> ListAdjPhrase -> AdjPhrase = \c,xs ->
    CO.conjunctTable3 AdjPos Number Case c xs ;

  conjunctDistrAdjPhrase : ConjunctionDistr -> ListAdjPhrase -> AdjPhrase = \c,xs ->
    CO.conjunctDistrTable3 AdjPos Number Case c xs ;


--3 Coordinating noun phrases
--
-- The structure is the same as for sentences. The result is either always plural
-- or plural if any of the components is, depending on the conjunction.

  ListNounPhrase : Type = {s1,s2 : NPForm => Str ; n : Number ; p : NPPerson} ;

  twoNounPhrase : (_,_ : NounPhrase) -> ListNounPhrase = \x,y ->
    CO.twoTable NPForm x y ** {n = conjNumber x.n y.n ; p = conjPerson x.p y.p} ;

  consNounPhrase : ListNounPhrase -> NounPhrase -> ListNounPhrase =  \xs,x ->
    CO.consTable NPForm CO.comma xs x ** 
       {n = conjNumber xs.n x.n ; p = conjPerson xs.p x.p} ;

  conjunctNounPhrase : Conjunction -> ListNounPhrase -> NounPhrase = \c,xs ->
    CO.conjunctTable NPForm c xs ** {n = conjNumber c.n xs.n ; p = xs.p} ;

  conjunctDistrNounPhrase : ConjunctionDistr -> ListNounPhrase -> NounPhrase = 
    \c,xs ->
    CO.conjunctDistrTable NPForm c xs ** {n = conjNumber c.n xs.n ; p = xs.p} ;

-- We have to define a calculus of numbers of persons. For numbers,
-- it is like the conjunction with $Pl$ corresponding to $False$.

  conjNumber : Number -> Number -> Number = \m,n -> case <m,n> of {
    <Sg,Sg> => Sg ;
    _ => Pl 
    } ;

-- For persons, we let the latter argument win ("either you or I am absent"
-- but "either I or you are absent"). This is not quite clear.

  conjPerson : NPPerson -> NPPerson -> NPPerson = \_,p -> 
    p ;



--2 Subjunction
--
-- Subjunctions ("kun", "jos", etc) 
-- are a different way to combine sentences than conjunctions.
-- The main clause can be a sentences, an imperatives, or a question,
-- but the subjoined clause must be a sentence.
--
-- There are uniformly two variant word orders, e.g. 
-- "jos poltat min� suutun"
-- and "min� suutun jos poltat".

  Subjunction = SS ;

  subjunctSentence : Subjunction -> Sentence -> Sentence -> Sentence = 
    \if, A, B -> 
    ss (subjunctVariants if A.s B.s) ;

  subjunctImperative : Subjunction -> Sentence -> Imperative -> Imperative = 
    \if, A, B -> 
    {s = \\n => subjunctVariants if A.s (B.s ! n)} ;

  subjunctQuestion : Subjunction -> Sentence -> Question -> Question = 
    \if, A, B ->
    {s = subjunctVariants if A.s B.s} ;

  subjunctVariants : Subjunction -> Str -> Str -> Str = \if,A,B ->
    variants {if.s ++ A ++ commaPunct ++ B ; B ++ commaPunct ++ if.s ++ A} ;

--2 One-word utterances
-- 
-- An utterance can consist of one phrase of almost any category, 
-- the limiting case being one-word utterances. These
-- utterances are often (but not always) in what can be called the
-- default form of a category, e.g. the nominative.
-- This list is far from exhaustive.

  useNounPhrase : NounPhrase -> Utterance = \john ->
    postfixSS stopPunct (defaultNounPhrase john) ;

  useCommonNounPhrase : Number -> CommNounPhrase -> Utterance = \n,car -> 
    useNounPhrase (indefNounPhrase n car) ;

-- Here are some default forms.

  defaultNounPhrase : NounPhrase -> SS = \john -> 
    ss (john.s ! NPCase Nom) ;

  defaultQuestion : Question -> SS = \whoareyou ->
    whoareyou ;

  defaultSentence : Sentence -> Utterance = \x -> 
    x ;
} ;
