--1 A Small Scandinavian Resource Syntax
--
-- Aarne Ranta 2002
--
-- This resource grammar contains definitions needed to construct 
-- indicative, interrogative, and imperative sentences in Swedish.
--
-- The following modules are presupposed:

interface SyntaxScand = TypesScand ** open Prelude, (CO = Coordination) in {

--2 Common Nouns
--
--3 Simple common nouns

oper
  CommNoun : Type = {s : Number => Species => Case => Str ; g : NounGender} ;

-- When common nouns are extracted from lexicon, the composite noun form is ignored.
-- The latter is only relevant for Swedish.

  extCommNoun : Subst -> CommNoun = \sb ->
    {s = \\n,b,c => sb.s ! SF n b c ; 
     g = gen2nounGen sb.h1 
    } ;

  extCommNounMasc : Subst -> CommNoun ;

-- These constants are used for data abstraction over the parameter type $Num$.
  singular = Sg ;
  plural = Pl ;

--3 Common noun phrases

-- The need for this more complex type comes from the variation in the way in
-- which a modifying adjective is inflected after different determiners:
-- "(en) ful orm" / "(den) fula ormen" / "(min) fula orm".
param
  SpeciesP = IndefP | DefP Species ;  

-- We also have to be able to decide if a $CommNounPhrase$ is complex
-- (to form the definite form: "bilen" / "den stora bilen").

oper
  IsComplexCN : Type = Bool ;         

-- Coercions between simple $Species$ and $SpeciesP$:
  unSpeciesP : SpeciesP -> Species = \b -> 
    case b of {IndefP => Indef ; DefP p => p} ;    -- bil/bil/bilen
  unSpeciesAdjP : SpeciesP -> Species = \b -> 
    case b of {IndefP => Indef ; DefP _ => Def} ;  -- gammal/gamla/gamla

-- Here's the type itself.
  CommNounPhrase : Type = 
    {s : Number => SpeciesP => Case => Str ; 
     g : NounGender ; p : IsComplexCN} ;

-- To use a $CommNoun$ as $CommNounPhrase$.
  noun2CommNounPhrase : CommNoun -> CommNounPhrase = \hus ->
    {s = \\n,b,c => hus.s ! n ! unSpeciesP b ! c ; 
     g = hus.g ; p = False} ;

  n2n = noun2CommNounPhrase ;


--2 Noun Phrases
--
-- The worst case for noun phrases is pronouns, which have inflection
-- in (what is syntactically) their genitive. Most noun phrases can
-- ignore this variation.

oper
  npCase : NPForm -> Case = \c -> case c of {PGen _ => Gen ; _ => Nom} ;
  mkNPForm : Case -> NPForm = \c -> case c of {Gen => PGen APl ; _ => PNom} ;

  NounPhrase : Type = {
    s : NPForm => Str ; g : Gender ; n : Number ; p : Person
    } ;

-- Proper names are a simple kind of noun phrases. However, we want to
-- anticipate the rule that proper names can be modified by 
-- adjectives, even though noun phrases in general cannot - hence the sex.

  ProperName : Type = {s : Case => Str ; g : NounGender} ;

  mkProperName : Str -> NounGender -> ProperName = \john,g -> 
    {s = table {Nom => john ; Gen => john + "s"} ; g = g} ;
   
  nameNounPhrase : ProperName -> NounPhrase = \john -> 
    {s = table {c => john.s ! npCase c} ; g = genNoun john.g ; n = Sg ; p = P3} ;

  regNameNounPhrase : Str -> NounGender -> NounPhrase = \john,g ->
    nameNounPhrase (mkProperName john g) ;

  pronNounPhrase : ProPN -> NounPhrase = \jag -> 
    {s = jag.s ; g = jag.h1 ; n = jag.h2 ; p = jag.h3} ;

-- The following construction has to be refined for genitive forms:
-- "vi tre", "oss tre" are OK, but "v�r tres" is not.

  Numeral : Type = {s : Case => Str} ;

  pronWithNum : ProPN -> Numeral -> ProPN = \we,two ->
    {s = \\c => we.s ! c ++ two.s ! npCase c ; 
     h1 = we.h1 ; 
     h2 = we.h2 ;
     h3 = we.h3
    } ;

  noNum : Numeral = {s = \\_ => []} ;

-- Formal subjects

  npMan : NounPhrase ;
  npDet : NounPhrase ;

--2 Determiners
--
-- Determiners are inflected according to noun in gender and sex. 
-- The number and species of the noun are determined by the determiner.

  Determiner : Type = {s : NounGender => Str ; n : Number ; b : SpeciesP} ;

  artIndef : Gender => Str ;

  artDef : Bool => GenNum => Str ;

-- This is the rule for building noun phrases.

  detNounPhrase : Determiner -> CommNounPhrase -> NounPhrase = \en, man -> 
    {s = table {c => en.s ! man.g ++ man.s ! en.n ! en.b ! npCase c} ;
     g = genNoun man.g ; n = en.n ; p = P3} ;

-- The following macros are sufficient to define most determiners.
-- All $SpeciesP$ values come into question: 
-- "en god v�n" - "min gode v�n" - "den gode v�nnen".

  DetSg : Type = NounGender => Str ;
  DetPl : Type = Str ;

  mkDeterminerSg :  DetSg -> SpeciesP -> Determiner = \en, b -> 
    {s = en ; n = Sg ; b = b} ;

  mkDeterminerPl :  DetPl -> SpeciesP -> Determiner = \alla,b -> 
    mkDeterminerPlNum alla b noNum ;

  mkDeterminerPlNum : DetPl -> SpeciesP -> Numeral -> Determiner = \alla,b,n -> 
    {s = \\_ => alla ++ n.s ! Nom ; 
     n = Pl ; 
     b = b
    } ;

  detSgInvar : Str -> DetSg = \varje -> table {_ => varje} ;

-- A large class of determiners can be built from a gender-dependent table.

  mkDeterminerSgGender : (Gender => Str) -> SpeciesP -> Determiner = \en -> 
    mkDeterminerSg (\\g => en ! genNoun g) ;

  mkDeterminerSgGender2 : Str -> Str -> SpeciesP -> Determiner = \en,ett -> 
    mkDeterminerSgGender3 en en ett ;

-- This is only needed in Norwegian.

  mkDeterminerSgGender3 : Str -> Str -> Str -> SpeciesP -> Determiner ;

-- Here are some examples. We are in fact doing some ad hoc morphology here, 
-- instead of importing the lexicon.

  varjeDet : Determiner ;
  allaDet  : Determiner ;
  enDet    : Determiner = mkDeterminerSgGender artIndef IndefP ;

  flestaDet : Determiner ;
  vilkenDet : Determiner = 
    mkDeterminerSgGender 
                (\\g => pronVilken ! ASg g) IndefP ;
  vilkaDet  : Determiner = mkDeterminerPl (pronVilken ! APl) IndefP ;

  vilkDet : Number -> Determiner = \n -> case n of {
    Sg => vilkenDet ;
    Pl => vilkaDet
    } ;

  n�gDet : Number -> Determiner = \n -> case n of {
    Sg => mkDeterminerSgGender 
                 (\\g => pronN�gon ! ASg g) IndefP ;
    Pl =>  mkDeterminerPl (pronN�gon ! APl) IndefP
    } ;


-- Genitives of noun phrases can be used like determiners, to build noun phrases.
-- The number argument makes the difference between "min bil" - "mina bilar".

  npGenDet : Number -> Numeral -> NounPhrase -> CommNounPhrase -> NounPhrase = 
    \n,tre,huset,vin -> {
       s = \\c => case n of {
             Sg => huset.s ! PGen (ASg (genNoun vin.g)) ++ 
                   vin.s ! Sg ! DefP Indef ! npCase c ;
             Pl => huset.s ! PGen APl ++ tre.s ! Nom ++
                   vin.s ! Pl ! DefP Indef ! npCase c
             } ;
       g = genNoun vin.g ;
       n = n ;
       p = P3
       } ;

-- *Bare plural noun phrases* like "m�n", "goda v�nner", are built without a 
-- determiner word. But a $Numeral$ may occur.

  plurDet : CommNounPhrase -> NounPhrase = plurDetNum noNum ;

  plurDetNum : Numeral -> CommNounPhrase -> NounPhrase = \num,cn -> 
    {s = \\c => num.s ! Nom ++ cn.s ! Pl ! IndefP ! npCase c ; 
     g = genNoun cn.g ; 
     n = Pl ;
     p = P3
    } ;

-- Definite phrases in Swedish are special, since determiner may be absent 
-- depending on if the noun is complex: "bilen" - "den nya bilen".
-- In Danish, "den nye bil".

  denDet : CommNounPhrase -> NounPhrase = \cn -> 
    detNounPhrase 
      (mkDeterminerSgGender (table {g => artDef ! cn.p ! ASg g}) 
      (DefP  (specDefPhrase cn.p))) cn ;
  deDet : Numeral -> CommNounPhrase -> NounPhrase = \n,cn -> 
    detNounPhrase 
      (mkDeterminerPlNum (artDef ! cn.p ! APl) 
      (DefP (specDefPhrase cn.p)) n) cn ;

-- This is uniformly $Def$ in Swedish, but in Danish, $Indef$ for
-- compounds with determiner.

  specDefPhrase : Bool -> Species ;

-- It is useful to have macros for indefinite and definite, singular and plural
-- noun-phrase-like syncategorematic expressions.

  indefNounPhrase : Number -> CommNounPhrase -> NounPhrase = \n -> 
    indefNounPhraseNum n noNum ;

  indefNounPhraseNum : Number -> Numeral -> CommNounPhrase -> NounPhrase = 
   \n,num,hus ->
    case n of {
      Sg => detNounPhrase enDet hus ;
      Pl => plurDetNum num hus
      } ;

  defNounPhrase : Number -> CommNounPhrase -> NounPhrase = \n ->
    defNounPhraseNum n noNum ;

  defNounPhraseNum : Number -> Numeral -> CommNounPhrase -> NounPhrase = 
    \n,num,hus -> case n of {
      Sg => denDet hus ;
      Pl => deDet num  hus
      } ;

  indefNoun : Number -> CommNounPhrase -> Str = \n,man -> case n of {
    Sg => artIndef ! genNoun man.g ++ man.s ! Sg ! IndefP ! Nom ;
    Pl => man.s ! Pl ! IndefP ! Nom
    } ;

-- Constructions like "tanken att tv� �r j�mnt" are formed at the
-- first place as common nouns, so that one can also have "ett f�rslag att...".

  nounThatSentence : CommNounPhrase -> Sentence -> CommNounPhrase = \tanke,x -> 
    {s = \\n,d,c => tanke.s ! n ! d ! c ++ infinAtt ++ x.s ! Sub ; 
     g = tanke.g ;
     p = tanke.p
    } ;


--2 Adjectives
--3 Simple adjectives
--
-- A special type of adjectives just having positive forms (for semantic reasons) 
-- is useful, e.g. "finsk", "trekantig".
 
  Adjective : Type = {s : AdjFormPos => Case => Str} ;

  extAdjective : Adj -> Adjective = \adj ->
    {s = table {f => table {c => adj.s ! AF (Posit f) c}}} ;

  adjPastPart : Verb -> Adjective ;
 

-- Coercions between the compound gen-num type and gender and number:

  gNum : Gender -> Number -> GenNum = \g,n -> 
    case n of {Sg => ASg g ; Pl => APl} ;

  genGN : GenNum -> Gender = \gn -> 
    case gn of {ASg g => g ; _ => utrum} ;
  numGN : GenNum -> Number = \gn -> 
    case gn of {ASg _ => Sg ; APl => Pl} ;

--3 Adjective phrases
-- 
-- An adjective phrase may contain a complement, e.g. "yngre �n Rolf".
-- Then it is used as postfix in modification, e.g. "en man yngre �n Rolf".

  IsPostfixAdj = Bool ;

  AdjPhrase : Type = Adjective ** {p : IsPostfixAdj} ;

-- Simple adjectives are not postfix:

  adj2adjPhrase : Adjective -> AdjPhrase = \ny -> ny ** {p = False} ;

--3 Comparison adjectives

-- We take comparison adjectives directly from 
-- the lexicon, which has full adjectives:

  AdjDegr = Adj ; 

-- Each of the comparison forms has a characteristic use:
--
-- Positive forms are used alone, as adjectival phrases ("ung").

  positAdjPhrase : AdjDegr -> AdjPhrase = \ung ->
    {s = table {a => \\c => ung.s ! AF (Posit a) c} ; 
     p = False
    } ;

-- Comparative forms are used with an object of comparison, as
-- adjectival phrases ("yngre �n Rolf").

  comparAdjPhrase : AdjDegr -> NounPhrase -> AdjPhrase = \yngre,rolf ->
    {s = \\_, c => yngre.s ! AF Compar Nom ++ prep�n ++ rolf.s ! mkNPForm c ;
     p = True
    } ;

-- Superlative forms are used with a modified noun, picking out the
-- maximal representative of a domain ("den yngste mannen").

  superlNounPhrase : AdjDegr -> CommNounPhrase -> NounPhrase = \yngst,man ->
    {s = \\c => let {gn = gNum (genNoun man.g) Sg} in 
                artDef ! True ! gn ++ 
                yngst.s ! AF (Super SupWeak) Nom ++
                man.s ! Sg ! DefP superlSpecies ! npCase c ; 
     g = genNoun man.g ; 
     n = Sg ;
     p = P3
    } ;

-- In Danish, however, "den yngste mand" - therefore a parametric species.

  superlSpecies : Species ;

-- Moreover, superlatives can be used alone as adjectival phrases
-- ("yngst", "den yngste" - in free variation). 
-- N.B. the former is only permitted in predicative position.

  superlAdjPhrase : AdjDegr -> AdjPhrase = \ung ->
    {s = \\a,c => variants {
    ---       artDef ! True ! gn ++ yngst.s ! AF (Super SupWeak) c
           ung.s ! AF (Super SupStrong) c 
           } ; 
     p = False
    } ;

--3 Two-place adjectives
--
-- A two-place adjective is an adjective with a preposition used before
-- the complement. (Rem. $Preposition = Str$).

  AdjCompl = Adjective ** {s2 : Preposition} ;

  complAdj : AdjCompl -> NounPhrase -> AdjPhrase = \f�rtjust,dig ->
    {s = \\a,c => f�rtjust.s ! a ! c ++ f�rtjust.s2 ++ dig.s ! PAcc ;
     p = True
    } ;


--3 Modification of common nouns
--
-- The two main functions of adjective are in predication ("Johan �r ung")
-- and in modification ("en ung man"). Predication will be defined
-- later, in the chapter on verbs.

  modCommNounPhrase : AdjPhrase -> CommNounPhrase -> CommNounPhrase = \God,Nybil ->
    {s = \\n, b, c =>
           let {
             god   = God.s ! mkAdjForm (unSpeciesAdjP b) n Nybil.g ! Nom ;
             nybil = Nybil.s ! n ! b ! c
             } in
           preOrPost God.p nybil god ;
     g = Nybil.g ; 
     p = True} ;    

-- A special case is modification of a noun that has not yet been modified.
-- But it is simply a special case.

  modCommNoun : Adjective -> CommNoun -> CommNounPhrase = \god,bil ->
    modCommNounPhrase (adj2adjPhrase god) (n2n bil) ;

-- We have used a straightforward 
-- method building adjective forms from simple parameters.

  mkAdjForm : Species -> Number -> NounGender -> AdjFormPos ;

--2 Function expressions

-- A function expression is a common noun together with the
-- preposition prefixed to its argument ("mor till x").
-- The type is analogous to two-place adjectives and transitive verbs.

  Function = CommNoun ** {s2 : Preposition} ;

  mkFun : CommNoun -> Preposition -> Function = \f,p ->
    f ** {s2 = p} ;

-- The application of a function gives, in the first place, a common noun:
-- "mor/m�drar till Johan". From this, other rules of the resource grammar 
-- give noun phrases, such as "modern till Johan", "m�drarna till Johan",
-- "m�drarna till Johan och Maria", and "modern till Johan och Maria" (the
-- latter two corresponding to distributive and collective functions,
-- respectively). Semantics will eventually tell when each
-- of the readings is meaningful.

  appFunComm : Function -> NounPhrase -> CommNounPhrase = \v�rde,x -> 
    noun2CommNounPhrase
      {s = \\n,b => table {
              Gen => nonExist ;
              _ => v�rde.s ! n ! b ! Nom ++ v�rde.s2 ++ x.s ! PAcc
              } ;
       g = v�rde.g ;
      } ;

-- It is possible to use a function word as a common noun; the semantics is
-- often existential or indexical.

  funAsCommNounPhrase : Function -> CommNounPhrase = 
    noun2CommNounPhrase ;

-- The following is an aggregate corresponding to the original function application
-- producing "Johans mor" and "modern till Johan". It does not appear in the
-- resource grammar API any longer.

  appFun : Bool -> Function -> NounPhrase -> NounPhrase = \coll,v�rde,x -> 
    let {n = x.n ; nf = if_then_else Number coll Sg n} in 
    variants {
      defNounPhrase nf (appFunComm v�rde x) ;
      npGenDet nf noNum x (noun2CommNounPhrase v�rde)
      } ;

-- Two-place functions add one argument place.

  Function2 = Function ** {s3 : Preposition} ;

-- Their application starts by filling the first place.

  appFun2 : Function2 -> NounPhrase -> Function = \flyg, paris ->
    {s  = \\n,d,c => flyg.s ! n ! d ! c ++ flyg.s2 ++ paris.s ! PAcc ;
     g  = flyg.g ;
     s2 = flyg.s3
    } ;


--2 Verbs

-- Although the Swedish lexicon has full verb inflection, 
-- we have limited this first version of the resource syntax to
-- verbs in present tense. Their mode can be infinitive, imperative, and indicative.


--3 Verb phrases
--
-- Sentence forms are tense-mood combinations used in sentences and
-- verb phrases.

param
  Tense = Present | Past | Future | Condit ;
  Anteriority = Simul | Anter ; 
  SForm = 
     VFinite  Tense Anteriority
   | VImperat
   | VInfinit Anteriority ;

oper
  verbSForm : Verbum -> Voice -> SForm -> {fin,inf : Str} = \se,vo,sf -> 
     let
       simple : VerbForm -> {fin,inf : Str} = \v -> {
         fin = se.s ! v ; 
         inf = []
         } ;
       compound : Str -> Str -> {fin,inf : Str} = \x,y -> {
         fin = x ; 
         inf = y
         } ;
       see  : Voice -> Str = \v -> (se.s ! (VI (Inf v))) ; 
       sett : Voice -> Str = \v -> (se.s ! (VI (Supin v))) ;
       hasett : Voice -> Str = \v -> auxHa ++ sett v

     in case sf of {
       VFinite Present Simul => simple   (VF (Pres Ind vo)) ; 
       VFinite Present Anter => compound auxHar (sett vo) ;
       VFinite Past    Simul => simple   (VF (Pret Ind vo)) ; 
       VFinite Past    Anter => compound auxHade (sett vo) ;
       VFinite Future  Simul => compound auxSka (see vo) ; 
       VFinite Future  Anter => compound auxSka (hasett vo) ; 
       VFinite Condit  Simul => compound auxSkulle (see vo) ;
       VFinite Condit  Anter => compound auxSkulle (hasett vo) ; 
       VImperat             => simple   (VF Imper) ; --- no passive
       VInfinit Simul       => simple   (VI (Inf vo)) ;
       VInfinit Anter       => compound auxHa (sett vo)
     } ;

  useVerb : Verb -> (Gender => Number => Person => Str) -> VerbGroup = \verb,arg -> 
    let aer = verbSForm verb Act in {
      s  = \\sf => (aer sf).fin ;
      s2 = negation ; 
      s3 = \\sf,g,n,p => (aer sf).inf ++ arg ! g ! n ! p
      } ;

-- Verb phrases are discontinuous: the parts of a verb phrase are
-- (s) an inflected verb, (s2) verb adverbials (such as negation), and
-- (s3) complement. This discontinuity is needed in sentence formation
-- to account for word order variations. No particle needs to be retained.

  VerbPhrase : Type = {
    s  : Str ; 
    s2 : Str ; 
    s3 : Gender => Number => Person => Str
    } ;
  VerbGroup  : Type = {
    s  : SForm => Str ; 
    s2 : Bool => Str ; 
    s3 : SForm => Gender => Number => Person => Str
    } ;

  predVerbGroup : Bool -> Tense -> Anteriority -> VerbGroup -> VerbPhrase = \b,t,a,vg -> {
    s  = vg.s ! VFinite t a ;
    s2 = vg.s2 ! b ;
    s3 = vg.s3 ! VFinite t a
    } ;

  predVerbGroupTrue = predVerbGroup True Present Simul ; ---- temporary

-- A simple verb can be made into a verb phrase with an empty complement.
-- There are two versions, depending on if we want to negate the verb.
-- N.B. negation is *not* a function applicable to a verb phrase, since
-- double negations with "inte" are not grammatical.

  predVerb : Verb -> VerbGroup = \se -> useVerb se (\\_,_,_ => se.s1) ;

  negation : Bool => Str = \\b => if_then_Str b [] negInte ;

  predVerb0 : Verb -> Clause = \regna -> 
    predVerbGroupClause npDet (predVerb regna) ;


-- Verb phrases can also be formed from adjectives ("�r sn�ll"),
-- common nouns ("�r en man"), and noun phrases ("�r den yngste mannen").
-- The third rule is overgenerating: "�r varje man" has to be ruled out
-- on semantic grounds.

  vara : (Gender => Number => Person => Str) -> VerbGroup = 
    useVerb (verbVara ** {s1 = []}) ;

  predAdjective : Adjective -> VerbGroup = \arg ->
    vara (\\g,n,_ => arg.s ! predFormAdj g n ! Nom) ;

  predFormAdj : Gender -> Number -> AdjFormPos = \g,n -> 
     mkAdjForm Indef n (gen2nounGen g) ;

  predCommNoun : CommNounPhrase -> VerbGroup = \man ->
    vara (\\_,n,_ => indefNoun n man) ;

  predNounPhrase : NounPhrase -> VerbGroup = \john ->
    vara (\\_,_,_ => john.s ! PNom) ;

  predAdverb : Adverb -> VerbGroup = \ute ->
    vara (\\_,_,_ => ute.s) ;

  predAdjSent : Adjective -> Sentence -> Clause = \bra,hansover ->
    predVerbGroupClause
      npDet
      (vara (
        \\g,n,_ => bra.s ! predFormAdj g n ! Nom ++ infinAtt ++ hansover.s ! Sub)) ;

  predAdjSent2 : AdjCompl -> NounPhrase -> Adjective = \bra,han ->
   {s = \\af,c => bra.s ! af ! c ++ bra.s2 ++ han.s ! PAcc} ;


--3 Transitive verbs
--
-- Transitive verbs are verbs with a preposition for the complement,
-- in analogy with two-place adjectives and functions.
-- One might prefer to use the term "2-place verb", since
-- "transitive" traditionally means that the inherent preposition is empty.
-- Such a verb is one with a *direct object*.

  TransVerb : Type = Verb ** {s2 : Preposition} ; 

  mkTransVerb : Verb -> Preposition -> TransVerb = \v,p -> 
    v ** {s2 = p} ;

  mkDirectVerb : Verb -> TransVerb = \v -> 
    mkTransVerb v nullPrep ;

  nullPrep : Preposition = [] ;


  extTransVerb : Verbum -> Preposition -> TransVerb = \v,p ->
    mkTransVerb (v ** {s1 = []}) p ;


-- The rule for using transitive verbs is the complementization rule:

  complTransVerb : TransVerb -> NounPhrase -> VerbGroup = \se,dig ->
    useVerb se (\\_,_,_ => se.s1 ++ se.s2 ++ dig.s ! PAcc) ;

-- Transitive verbs with accusative objects can be used passively. 
-- The function does not check that the verb is transitive.
-- Therefore, the function can also be used for "han l�ps", etc.
-- The syntax is the same as for active verbs, with the choice of the
-- "s" passive form.

  passVerb : Verb -> VerbGroup = \se ->
    let ses = verbSForm se Pass in {
      s  = \\sf => (ses sf).fin ;
      s2 = negation ; 
      s3 = \\sf,g,n,_ => (ses sf).inf ++ se.s1
      } ;

-- Transitive verbs can be used elliptically as verbs. The semantics
-- is left to applications. The definition is trivial, due to record
-- subtyping.

  transAsVerb : TransVerb -> Verb = \love -> 
    love ;

  reflTransVerb : TransVerb -> VerbGroup = \se ->
    useVerb se (\\_,n,p => se.s1 ++ se.s2 ++ reflPron n p) ;

  reflPron : Number -> Person -> Str ;

-- *Ditransitive verbs* are verbs with three argument places.
-- We treat so far only the rule in which the ditransitive
-- verb takes both complements to form a verb phrase.

  DitransVerb = TransVerb ** {s3 : Preposition} ; 

  mkDitransVerb : Verb -> Preposition -> Preposition -> DitransVerb = \v,p1,p2 -> 
    v ** {s2 = p1 ; s3 = p2} ;

  complDitransVerb : 
    DitransVerb -> NounPhrase -> TransVerb = \ge,dig ->
      {s  = ge.s ;
       s1 = ge.s1 ++ ge.s2 ++ dig.s ! PAcc ;
       s2 = ge.s3
      } ;

---      useVerb 
---        ge 
---        (\\_,_ => ge.s1 ++ ge.s2 ++ dig.s ! PAcc ++ ge.s3 ++ vin.s ! PAcc) ;

-- Adjective-complement ditransitive verbs.

  DitransAdjVerb = TransVerb ; 

  mkDitransAdjVerb : Verb -> Preposition -> DitransAdjVerb = \v,p1 -> 
    v ** {s2 = p1} ;

  complDitransAdjVerb : 
    DitransAdjVerb -> NounPhrase -> AdjPhrase -> VerbGroup = \gor,dig,sur ->
      useVerb 
        gor 
        (\\_,_,_ => gor.s1 ++ gor.s2 ++ dig.s ! PAcc ++ 
                    sur.s ! predFormAdj dig.g dig.n ! Nom) ;

  complAdjVerb : 
    Verb -> AdjPhrase -> VerbGroup = \seut,sur ->
      useVerb 
        seut 
        (\\g,n,_ => sur.s ! predFormAdj g n ! Nom ++ seut.s1) ;

--2 Adverbs
--
-- Adverbs that modify verb phrases are either post- or pre-verbal.
-- As a rule of thumb, simple adverbs ("bra","alltid") are pre-verbal,
-- but this is not always the case ("h�r" is post-verbal).
-- Even prepositional phrases can be both 
-- ("att han i alla fall skulle komma").

  Adverb : Type = SS ** {isPost : Bool} ;
  PrepPhrase : Type = Adverb ;

  advPre  : Str -> Adverb = \alltid -> ss alltid ** {isPost = False} ;
  advPost : Str -> Adverb = \bra    -> ss bra    ** {isPost = True} ;

  adVerbPhrase : VerbPhrase -> Adverb -> VerbPhrase = \spelar, bra ->
    let {postp = bra.isPost} in
    {
  --- this unfortunately generates  VP#2 ::= VP#2
     s  = spelar.s ; 
     s2 = (if_then_else Str postp [] bra.s) ++ spelar.s2 ;
     s3 = \\g,n,p => spelar.s3 ! g ! n ! p ++ (if_then_else Str postp bra.s [])
    } ;

  advAdjPhrase : SS -> AdjPhrase -> AdjPhrase = \mycket, dyr ->
    {s = \\a,c => mycket.s ++ dyr.s ! a ! c ;
     p = dyr.p
    } ;

-- Adverbials are typically generated by prefixing prepositions.
-- The rule for creating locative noun phrases by the preposition "i"
-- is a little shaky: "i Sverige" but "p� Island".

  prepPhrase : Preposition -> NounPhrase -> Adverb = \i,huset ->
    advPost (i ++ huset.s ! PAcc) ;

  locativeNounPhrase : NounPhrase -> Adverb = 
    prepPhrase "i" ;

-- This is a source of the "mannen med teleskopen" ambiguity, and may produce
-- strange things, like "bilar alltid" (while "bilar idag" is OK).
-- Semantics will have to make finer distinctions among adverbials.

  advCommNounPhrase : CommNounPhrase -> PrepPhrase -> CommNounPhrase = \bil,idag ->
    {s = \\n, b, c => bil.s ! n ! b ! c ++ idag.s ;
     g = bil.g ; 
     p = bil.p} ;    


--2 Sentences
--
-- Sentences depend on a *word order parameter* selecting between main clause,
-- inverted, and subordinate clause.

param
  Order = Main | Inv | Sub ;

oper
  Sentence : Type = SS1 Order ;

-- This is the traditional $S -> NP VP$ rule. It takes care of both
-- word order and agreement.

 ----- obsolete
  predVerbPhrase : NounPhrase -> VerbPhrase -> Sentence = 
    \Jag, serdiginte -> 
    let {
      jag  = Jag.s ! PNom ; 
      ser  = serdiginte.s ;
      dig  = serdiginte.s3 ! Jag.g ! Jag.n ! Jag.p ;
      inte = serdiginte.s2
    } in
    {s = table {
       Main => jag ++ ser ++ inte ++ dig ;  
       Inv  => ser ++ jag ++ inte ++ dig ;
       Sub  => jag ++ inte ++ ser ++ dig
       }
    } ;

param
  ClForm = 
     ClFinite   Tense Anteriority Order
   | ClInfinite Anteriority      -- "naked infinitive" clauses
    ;

oper 
  cl2s : ClForm -> {o : Order ; sf : SForm} = \c -> case c of {
    ClFinite t a o   => {o = o ; sf = VFinite t a} ;
    ClInfinite a     => {o = Sub ; sf = VInfinit a} -- "jag s�g John inte h�lsa"
    } ;
  s2cl : SForm -> Order -> ClForm = \s,o -> case s of {
    VFinite t a  => ClFinite t a o ;
    VInfinit a   => ClInfinite a ;
    _ => ClInfinite Simul ---- ??
    } ;

  Clause = {s : Bool => ClForm => Str} ;

  predVerbGroupClause : NounPhrase -> VerbGroup -> Clause = 
    \Jag, serdiginte -> {
     s = \\b,c => let {
      jag  = Jag.s ! (case c of {ClInfinite _ => PAcc ; _ => PNom}) ;
      osf  = cl2s c ;
      t    = osf.sf ;
      o    = osf.o ; 
      ser  = serdiginte.s ! t ;
      dig  = serdiginte.s3 ! t ! Jag.g ! Jag.n ! Jag.p ;
      inte = serdiginte.s2 ! b
    } in
    case o of {
       Main => jag ++ ser ++ inte ++ dig ;  
       Inv  => ser ++ jag ++ inte ++ dig ;
       Sub  => jag ++ inte ++ ser ++ dig
       }
    } ;


--3 Sentence-complement verbs
--
-- Sentence-complement verbs take sentences as complements.

  SentenceVerb : Type = Verb ;

  complSentVerb : SentenceVerb -> Sentence -> VerbGroup = \se,duler ->
    useVerb se (\\_,_,_ => se.s1 ++ optStr infinAtt ++ duler.s ! Main) ;

  complQuestVerb : SentenceVerb -> QuestionSent -> VerbGroup = \se,omduler ->
    useVerb se (\\_,_,_ => se.s1 ++ omduler.s ! IndirQ) ;

  complDitransSentVerb : TransVerb -> NounPhrase -> Sentence -> VerbGroup = 
    \sa,honom,duler ->
      useVerb sa 
        (\\_,_,_ => sa.s1 ++ sa.s2 ++ honom.s ! PAcc ++ optStr infinAtt ++ duler.s ! Main) ;

  complDitransQuestVerb : TransVerb -> NounPhrase -> QuestionSent -> VerbGroup = 
    \sa,honom,omduler ->
      useVerb sa 
        (\\_,_,_ => sa.s1 ++ sa.s2 ++ honom.s ! PAcc ++ omduler.s ! IndirQ) ;

--3 Verb-complement verbs
--
-- Verb-complement verbs take verb phrases as complements.
-- They can be auxiliaries ("kan", "m�ste") or ordinary verbs
-- ("f�rs�ka"); this distinction cannot be done in the multilingual
-- API and leads to some anomalies in Swedish, but less so than in English.

  VerbVerb : Type = Verb ** {s3 : Str} ;

  complVerbVerb : VerbVerb -> VerbGroup -> VerbGroup = \vilja, simma ->
    useVerb vilja 
      (\\g,n,p => 
              vilja.s1 ++
              vilja.s3 ++
              simma.s ! VInfinit Simul ++ simma.s2 ! True ++ ---- Anter!
              simma.s3 ! VInfinit Simul ! g ! n ! p) ;

  transVerbVerb : VerbVerb -> TransVerb -> TransVerb = \vilja,hitta ->
    {s  = vilja.s ;
     s1 = vilja.s1 ++ vilja.s3 ++
          hitta.s ! VI (Inf Act) ++ hitta.s1 ;            ---- Anter!
     s2 = hitta.s2
    } ;

  complVerbAdj : Adjective -> VerbGroup -> VerbGroup = \grei, simma ->
    vara
      (\\g,n,p => 
              grei.s ! predFormAdj g n ! Nom ++ 
              infinAtt ++
              simma.s ! VInfinit Simul ++ simma.s2 ! True ++ ---- Anter!
              simma.s3 ! VInfinit Simul ! g ! n ! p) ;

-- Notice agreement to object vs. subject:

  DitransVerbVerb = TransVerb ** {s3 : Str} ;

  complDitransVerbVerb : 
    Bool -> DitransVerbVerb -> NounPhrase -> VerbGroup -> VerbGroup = 
     \obj,be,dig,simma ->
      useVerb be 
        (\\g,n,p => be.s1 ++ be.s2 ++ dig.s ! PAcc ++ be.s3 ++ 
              simma.s ! VInfinit Simul ++ simma.s2 ! True ++ ---- Anter!
              if_then_Str obj 
                 (simma.s3 ! VInfinit Simul ! dig.g ! dig.n ! dig.p)
                 (simma.s3 ! VInfinit Simul ! g ! n ! p)
        ) ;

  complVerbAdj2 : 
    Bool -> AdjCompl -> NounPhrase -> VerbGroup -> VerbGroup = \obj,grei,dig,simma ->
    vara
      (\\g,n,p =>
              grei.s ! predFormAdj g n ! Nom ++ 
              grei.s2 ++ dig.s ! PAcc ++
              infinAtt ++
              simma.s ! VInfinit Simul ++ simma.s2 ! True ++ ---- Anter!
              if_then_Str obj 
                 (simma.s3 ! VInfinit Simul ! dig.g ! dig.n ! dig.p)
                 (simma.s3 ! VInfinit Simul ! g ! n ! p)
      ) ;

--2 Sentences missing noun phrases
--
-- This is one instance of Gazdar's *slash categories*, corresponding to his
-- $S/NP$.
-- We cannot have - nor would we want to have - a productive slash-category former.
-- Perhaps a handful more will be needed.
--
-- Notice that the slash category has the same relation to sentences as
-- transitive verbs have to verbs: it's like a *sentence taking a complement*.

  ClauseSlashNounPhrase : Type = Clause ** {s2 : Preposition} ;

  slashTransVerb : NounPhrase -> TransVerb -> ClauseSlashNounPhrase = 
    \jag, se -> 
      predVerbGroupClause jag (useVerb se (\\_,_,_ => se.s1)) ** {s2 = se.s2} ;
 
--2 Relative pronouns and relative clauses
--
-- Relative pronouns can be nominative, accusative, or genitive, and
-- they depend on gender and number just like adjectives.
-- Moreover they may or may not carry their own genders: for instance,
-- "som" just transmits the gender of a noun ("tal som �r primt"), whereas
-- "vars efterf�ljare" is $Utrum$ independently of the noun 
-- ("tal vars efterf�ljare �r prim"). 
-- This variation is expressed by the $RelGender$ type.

  RelPron : Type = {s : RelCase => GenNum => Str ; g : RelGender} ;

param
  RelGender = RNoGen | RG Gender ;

-- The following functions are selectors for relative-specific parameters.
 
oper
  -- this will be needed in "tal som �r j�mnt" / "tal vars efterf�ljare �r j�mn"
  mkGenderRel : RelGender -> Gender -> Gender = \rg,g -> case rg of {
    RG gen => gen ;
    _      => g
    } ;

  relCase : RelCase -> Case = \c -> case c of {
    RGen => Gen ;
    _    => Nom
    } ; 

-- The simplest relative pronoun has no gender of its own. As accusative variant,
-- it has the omission of the pronoun ("mannen (som) jag ser").

  identRelPron : RelPron = 
    {s = table {
      RNom  => \\_ => "som" ;
      RAcc  => \\_ => variants {"som" ; []} ;
      RGen  => \\_ => pronVars ;
      RPrep => pronVilken
      } ;
     g = RNoGen
    } ;

-- Composite relative pronouns have the same variation as function
-- applications ("efterf�ljaren till vilket" - "vars efterf�ljare").

  funRelPron : Function -> RelPron -> RelPron = \v�rde,vilken -> 
    {s = \\c,gn => 
           variants {
             vilken.s ! RGen ! gn ++ v�rde.s ! numGN gn ! Indef ! relCase c ; 
             v�rde.s ! numGN gn ! Def ! Nom ++ v�rde.s2 ++ vilken.s ! RPrep ! gn
             } ;
     g = RG (genNoun v�rde.g)
    } ;

-- Relative clauses can be formed from both verb phrases ("som sover") and
-- slash expressions ("som jag ser"). The latter has moreover the variation
-- as for the place of the preposition ("som jag talar om" - "om vilken jag talar").

  RelClause : Type = {s : Bool => SForm => GenNum => Person => Str} ;
  RelSent   : Type = {s :                  GenNum => Person => Str} ;

  relVerbGroup : RelPron -> VerbGroup -> RelClause = \som,sover ->
    {s = \\b,sf,gn,p => 
       som.s ! RNom ! gn ++ sover.s2 ! b ++ sover.s ! sf ++  
       sover.s3 ! sf ! mkGenderRel som.g (genGN gn) ! numGN gn ! p
    } ;

  relSlash : RelPron -> ClauseSlashNounPhrase -> RelClause = \som,jagTalar ->
    {s = \\b,sf,gn,p => 
           let 
             jagtalar = jagTalar.s ! b ! s2cl sf Sub ; 
             om = jagTalar.s2
           in variants {
             som.s ! RAcc ! gn ++ jagtalar ++ om ;
             om ++ som.s ! RPrep ! gn ++ jagtalar
             }
    } ;

-- A 'degenerate' relative clause is the one often used in mathematics, e.g.
-- "tal x s�dant att x �r primt".

  relSuch : Clause -> RelClause = \A ->
    {s = \\b,sf,g,p => pronS�dan ! g ++ infinAtt ++ A.s ! b ! s2cl sf Sub} ;

-- The main use of relative clauses is to modify common nouns.
-- The result is a common noun, out of which noun phrases can be formed
-- by determiners.

  modRelClause : CommNounPhrase -> RelSent -> CommNounPhrase = \man,somsover ->
    {s = \\n,b,c => 
           man.s ! n ! b ! c ++ somsover.s ! gNum (genNoun man.g) n ! P3 ;
     g = man.g ;
     p = False
    } ;

-- N.B. we do not get the determinative pronoun
-- construction "den man som sover" in this way, but only "mannen som sover".
-- Thus we need an extra rule:

  detRelClause : Number -> CommNounPhrase -> RelSent -> NounPhrase = 
    \n,man,somsover ->
    {s = \\c => let {gn = gNum (genNoun man.g) n} in 
                artDef ! True ! gn ++ 
                man.s ! n ! DefP Indef ! npCase c ++ somsover.s ! gn ! P3;
     g = genNoun man.g ;
     n = n ;
     p = P3
    } ;


--2 Interrogative pronouns
--
-- If relative pronouns are adjective-like, interrogative pronouns are
-- noun-phrase-like. Actually we can use the very same type!

  IntPron : Type = NounPhrase ; 

-- In analogy with relative pronouns, we have a rule for applying a function
-- to a relative pronoun to create a new one. We can reuse the rule applying
-- functions to noun phrases!

  funIntPron : Function -> IntPron -> IntPron = 
    appFun False ; 

-- There is a variety of simple interrogative pronouns:
-- "vilken bil", "vem", "vad".

  nounIntPron : Number -> CommNounPhrase -> IntPron = \n ->
    detNounPhrase (vilkDet n) ;

  intPronWho : Number -> IntPron = \num -> {
    s = table {
      PGen _ => pronVems ;
      _      => pronVem
      } ;
    g = utrum ;
    n = num ;
    p = P3
  } ;

  intPronWhat : Number -> IntPron = \num -> {
    s = table {
      PGen  _ => nonExist ; ---
      _ => pronVad
      } ;
    n = num ;
    g = Neutr ;
    p = P3
  } ;

--2 Utterances

-- By utterances we mean whole phrases, such as 
-- 'can be used as moves in a language game': indicatives, questions, imperative,
-- and one-word utterances. The rules are far from complete.
--
-- N.B. we have not included rules for texts, which we find we cannot say much
-- about on this level. In semantically rich GF grammars, texts, dialogues, etc, 
-- will of course play an important role as categories not reducible to utterances.
-- An example is proof texts, whose semantics show a dependence between premises
-- and conclusions. Another example is intersentential anaphora.

  Utterance = SS ;
  
  indicUtt : Sentence -> Utterance = \x -> postfixSS "." (defaultSentence x) ;
  interrogUtt : {s : QuestForm => Str} -> Utterance = \x -> postfixSS "?" (defaultQuestion x) ;


--2 Questions
--
-- Questions are either direct ("vem tog bollen") or indirect 
-- ("vem som tog bollen").

param 
  QuestForm = DirQ | IndirQ ;

oper
  Question = {s : Bool => SForm => QuestForm => Str} ;
  QuestionSent = {s :              QuestForm => Str} ;

--3 Yes-no questions 
--
-- Yes-no questions are used both independently ("tog du bollen")
-- and after interrogative adverbials ("varf�r tog du bollen").
-- It is economical to handle with these two cases by the one
-- rule, $questVerbPhrase'$. The only difference is if "om" appears
-- in the indirect form.

  questVerbPhrase : NounPhrase -> VerbGroup -> Question = 
    questVerbPhrase' False ;

  questVerbPhrase' : Bool -> NounPhrase -> VerbGroup -> Question = 
    \adv,du,sover ->
    {s = \\b,sf => 
      let 
        dusover : Order => Str = \\o => (predVerbGroupClause du sover).s ! b ! s2cl sf o
      in
      table {
        DirQ   => dusover ! Inv ;
        IndirQ => (if_then_else Str adv [] conjOm) ++ dusover ! Sub
        }
    } ;

--3 Wh-questions
--
-- Wh-questions are of two kinds: ones that are like $NP - VP$ sentences,
-- others that are line $S/NP - NP$ sentences.

  intVerbPhrase : IntPron -> VerbGroup -> Question = \vem,sover ->
    let 
      vemsom : NounPhrase = 
           {s = \\c => vem.s ! c ++ "som" ; g = vem.g ; n = vem.n ; p = P3}
    in
    {s = \\b,sf => 
      table {
        DirQ   => (predVerbGroupClause vem    sover).s ! b ! s2cl sf Main ;
        IndirQ => (predVerbGroupClause vemsom sover).s ! b ! s2cl sf Sub 
        }
    } ;

  intSlash : IntPron -> ClauseSlashNounPhrase -> Question = \Vem, jagTalar ->
    let
      vem = Vem.s ! PAcc ; 
      om = jagTalar.s2
    in
    {s = \\b,sf => 
      let
        cf = s2cl sf ;
        talarjag = jagTalar.s ! b ! cf Inv ; 
        jagtalar = jagTalar.s ! b ! cf Sub 
      in
      table {
        DirQ => variants {
                vem ++ talarjag ++ om ;
                om ++ vem ++ talarjag
                } ;
        IndirQ => variants {
                vem ++ jagtalar ++ om ;
                om ++ vem ++ jagtalar
                }
      } 
    } ;

--3 Interrogative adverbials
--
-- These adverbials will be defined in the lexicon: they include
-- "n�r", "var", "hur", "varf�r", etc, which are all invariant one-word
-- expressions. In addition, they can be formed by adding prepositions
-- to interrogative pronouns, in the same way as adverbials are formed
-- from noun phrases. N.B. we rely on record subtyping when ignoring the
-- position component.

  IntAdverb = SS ;

  prepIntAdverb : Preposition -> IntPron -> IntAdverb =
    prepPhrase ;

-- A question adverbial can be applied to anything, and whether this makes
-- sense is a semantic question.

  questAdverbial : IntAdverb -> NounPhrase -> VerbGroup -> Question = 
    \hur, du, m�r ->
    {s = \\b,sf,q => hur.s ++ (questVerbPhrase' True du m�r).s ! b ! sf ! q} ;

--2 Imperatives
--
-- We only consider second-person imperatives.

  Imperative = SS1 Number ;

  imperVerbPhrase : VerbPhrase -> Imperative = \titta -> 
    {s = \\n => titta.s ++ titta.s2 ++ titta.s3 ! utrum ! n ! P2} ;

  imperUtterance : Number -> Imperative -> Utterance = \n,I ->
    ss (I.s ! n ++ "!") ;

--2 Sentence adverbials
--
-- This class covers adverbials such as "annars", "d�rf�r", which are prefixed
-- to a sentence to form a phrase.

  advSentence : SS -> Sentence -> Utterance = \annars,soverhan ->
    ss (annars.s ++ soverhan.s ! Inv ++ ".") ;


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
-- simple ("och", "eller") or distributed ("b�de - och", "antingen - eller").
--
-- The conjunction has an inherent number, which is used when conjoining
-- noun phrases: "John och Mary �r rika" vs. "John eller Mary �r rik"; in the
-- case of "eller", the result is however plural if any of the disjuncts is.

  Conjunction = CO.Conjunction ** {n : Number} ;
  ConjunctionDistr = CO.ConjunctionDistr ** {n : Number} ;


--3 Coordinating sentences
--
-- We need a category of lists of sentences. It is a discontinuous
-- category, the parts corresponding to 'init' and 'last' segments
-- (rather than 'head' and 'tail', because we have to keep track of the slot between
-- the last two elements of the list). A list has at least two elements.

  ListSentence : Type = {s1,s2 : Order => Str} ; 

  twoSentence : (_,_ : Sentence) -> ListSentence = 
    CO.twoTable Order ;

  consSentence : ListSentence -> Sentence -> ListSentence = 
    CO.consTable Order CO.comma ;

-- To coordinate a list of sentences by a simple conjunction, we place
-- it between the last two elements; commas are put in the other slots,
-- e.g. "m�nen lyser, solen skiner och stj�rnorna blinkar".

  conjunctSentence : Conjunction -> ListSentence -> Sentence = 
    CO.conjunctTable Order ;

  conjunctOrd : Bool -> Conjunction -> CO.ListTable Order -> {s : Order => Str} = 
    \b,or,xs ->
    {s = \\p => xs.s1 ! p ++ or.s ++ xs.s2 ! p} ;


-- To coordinate a list of sentences by a distributed conjunction, we place
-- the first part (e.g. "antingen") in front of the first element, the second
-- part ("eller") between the last two elements, and commas in the other slots.
-- For sentences this is really not used.

  conjunctDistrSentence : ConjunctionDistr -> ListSentence -> Sentence = 
    CO.conjunctDistrTable Order ;

--3 Coordinating adjective phrases
--
-- The structure is the same as for sentences. The result is a prefix adjective
-- if and only if all elements are prefix.

  ListAdjPhrase : Type = 
    {s1,s2 : AdjFormPos => Case => Str ; p : Bool} ;

  twoAdjPhrase : (_,_ : AdjPhrase) -> ListAdjPhrase = \x,y ->
    CO.twoTable2 AdjFormPos Case x y ** {p = andB x.p y.p} ;
  consAdjPhrase : ListAdjPhrase -> AdjPhrase -> ListAdjPhrase =  \xs,x ->
    CO.consTable2 AdjFormPos Case CO.comma xs x ** {p = andB xs.p x.p} ;

  conjunctAdjPhrase : Conjunction -> ListAdjPhrase -> AdjPhrase = \c,xs ->
    CO.conjunctTable2 AdjFormPos Case c xs ** {p = xs.p} ;

  conjunctDistrAdjPhrase : ConjunctionDistr -> ListAdjPhrase -> AdjPhrase = \c,xs ->
    CO.conjunctDistrTable2 AdjFormPos Case c xs ** {p = xs.p} ;


--3 Coordinating noun phrases
--
-- The structure is the same as for sentences. The result is either always plural
-- or plural if any of the components is, depending on the conjunction.
-- The gender is neuter if any of the components is.

  ListNounPhrase : Type = {s1,s2 : NPForm => Str ; g : Gender ; n : Number ; p : Person} ;

  twoNounPhrase : (_,_ : NounPhrase) -> ListNounPhrase = \x,y ->
    CO.twoTable NPForm x y ** 
    {n = conjNumber x.n y.n ; g = conjGender x.g y.g ; p = conjPerson x.p y.p} ;

  consNounPhrase : ListNounPhrase -> NounPhrase -> ListNounPhrase =  \xs,x ->
    CO.consTable NPForm CO.comma xs x ** 
       {n = conjNumber xs.n x.n ; g = conjGender xs.g x.g ; p = conjPerson xs.p x.p} ;

  conjunctNounPhrase : Conjunction -> ListNounPhrase -> NounPhrase = \c,xs ->
    CO.conjunctTable NPForm c xs ** 
    {n = conjNumber c.n xs.n ; g = xs.g ; p = xs.p} ;

  conjunctDistrNounPhrase : ConjunctionDistr -> ListNounPhrase -> NounPhrase = 
    \c,xs ->
    CO.conjunctDistrTable NPForm c xs ** 
    {n = conjNumber c.n xs.n ; g = xs.g ; p = xs.p} ;

-- We have to define a calculus of numbers of genders. For numbers,
-- it is like the conjunction with $Pl$ corresponding to $False$. For genders,
-- $Neutr$ corresponds to $False$.

  conjNumber : Number -> Number -> Number = \m,n -> case <m,n> of {
    <Sg,Sg> => Sg ;
    _ => Pl 
    } ;

  conjPerson : Person -> Person -> Person = \m,n -> case <m,n> of {
    <P3,P3> => P3 ;
    <P3,P2> => P2 ;
    <P2,P3> => P2 ;
    <P2,P2> => P2 ;
    _ => P1 
    } ;

  conjGender : Gender -> Gender -> Gender ;


--2 Subjunction
--
-- Subjunctions ("om", "n�r", etc) 
-- are a different way to combine sentences than conjunctions.
-- The main clause can be a sentences, an imperatives, or a question,
-- but the subjoined clause must be a sentence.
--
-- There are uniformly two variant word orders, e.g. "om du sover kommer bj�rnen"
-- and "bj�rnen kommer om du sover".

  Subjunction = SS ;

  subjunctSentence : Subjunction -> Sentence -> Sentence -> Sentence = \if, A, B ->
    let {As = A.s ! Sub} in 
    {s = table {
           Main => variants {if.s ++ As ++ "," ++ B.s ! Inv ; 
                             B.s ! Main ++ "," ++ if.s ++ As} ;
           o    => B.s ! o ++ "," ++ if.s ++ As
           } 
     } ;

  subjunctImperative : Subjunction -> Sentence -> Imperative -> Imperative = 
    \if, A, B -> 
    {s = \\n => subjunctVariants if A (B.s ! n)} ;

  subjunctQuestion : Subjunction -> Sentence -> QuestionSent -> QuestionSent = \if, A, B ->
    {s = \\q => subjunctVariants if A (B.s ! q)} ;

  subjunctVariants : Subjunction -> Sentence -> Str -> Str = \if,A,B ->
    let {As = A.s ! Sub} in 
    variants {if.s ++ As ++ "," ++ B ; B ++ "," ++ if.s ++ As} ;

  subjunctVerbPhrase : VerbPhrase -> Subjunction -> Sentence -> VerbPhrase =
    \V, if, A -> 
    adVerbPhrase V (advPost (if.s ++ A.s ! Sub)) ;

--2 One-word utterances
-- 
-- An utterance can consist of one phrase of almost any category, 
-- the limiting case being one-word utterances. These
-- utterances are often (but not always) in what can be called the
-- default form of a category, e.g. the nominative.
-- This list is far from exhaustive.

  useNounPhrase : NounPhrase -> Utterance = \john ->
    postfixSS "." (defaultNounPhrase john) ;
  useCommonNounPhrase : Number -> CommNounPhrase -> Utterance = \n,car -> 
    useNounPhrase (indefNounPhrase n car) ;

-- Here are some default forms.

  defaultNounPhrase : NounPhrase -> SS = \john -> 
    ss (john.s ! PNom) ;

  defaultQuestion : {s : QuestForm => Str} -> SS = \whoareyou ->
    ss (whoareyou.s ! DirQ) ;

  defaultSentence : Sentence -> Utterance = \x -> ss (x.s ! Main) ;

----------- changes when parametrizing 20/1/2005

---- moved from Morphology

-- Prepositions are just strings.
  Preposition = Str ;

-- Relative pronouns have a special case system. $RPrep$ is the form used
-- after a preposition (e.g. "det hus i vilket jag bor").
param
  RelCase = RNom | RAcc | RGen | RPrep ;
-- A simplified verb category: present tense only (no more!).

oper
  relPronForms : RelCase => GenNum => Str ;
 
  pronVilken : GenNum => Str ;

  pronS�dan : GenNum => Str ;

  pronN�gon : GenNum => Str ;

  deponentVerb : Verb -> Verb ;

  verbFinnas : Verb ;
  verbVara : Verb ;
  verbHava : Verb ;

  auxHar, auxHade, auxHa, auxSka, auxSkulle : Str ;

  infinAtt : Str ;
  prep�n : Str ;
  negInte : Str ;
  conjOm : Str ;

  pronVars, pronVem, pronVems : Str ;

} ;
