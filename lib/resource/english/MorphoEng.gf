--# -path=.:../../prelude

--1 A Simple English Resource Morphology
--
-- Aarne Ranta 2002
--
-- This resource morphology contains definitions needed in the resource
-- syntax. It moreover contains the most usual inflectional patterns.
--
-- We use the parameter types and word classes defined in $Types.gf$.

resource MorphoEng = TypesEng ** open Prelude, (Predef=Predef) in {

--2 Phonology
--
-- To regulate the use of endings for both nouns, adjectives, and verbs:

oper
  y2ie : Str -> Str -> Str = \fly,s -> 
    let y = last (init fly) in
    case y of {
      "a" => fly + s ;
      "e" => fly + s ;
      "o" => fly + s ;
      "u" => fly + s ;
    _   => init fly + "ie" + s
    } ;



--2 Nouns
--
-- For conciseness and abstraction, we define a worst-case macro for
-- noun inflection. It is used for defining special case that
-- only need one string as argument.

oper
  mkNoun  : (_,_,_,_ : Str) -> CommonNoun = 
    \man,men, mans, mens -> {s = table {
       Sg => table {Nom => man ; Gen => mans} ;
       Pl => table {Nom => men ; Gen => mens}
      }} ;

  nounReg : Str -> CommonNoun = \dog -> 
    mkNoun dog (dog + "s") (dog + "'s") (dog + "s'");

  nounS   : Str -> CommonNoun = \kiss -> 
    mkNoun kiss (kiss + "es") (kiss + "'s") (kiss + "es'") ;

  nounY   : Str -> CommonNoun = \fl -> 
    mkNoun (fl + "y") (fl + "ies") (fl + "y's") (fl + "ies'") ;

  nounGen : Str -> CommonNoun = \dog -> case last dog of {
    "y" => nounY "dog" ;
    "s" => nounS (init "dog") ;
    _   => nounReg "dog"
    } ;

--3 Proper names
--
-- Regular proper names are inflected with "'s" in the genitive.

  nameReg : Str -> Gender -> ProperName = \john,g -> 
    {s = table {Nom => john ; Gen => john + "'s"} ; g = g} ;


--2 Pronouns
--
-- Here we define personal and relative pronouns.

  mkPronoun : (_,_,_,_ : Str) -> Number -> Person -> Gender -> Pronoun = 
   \I,me,my,mine,n,p,g -> 
    {s = table {NomP => I ; AccP => me ; GenP => my ; GenSP => mine} ; 
     n = n ; p = p ; g = g} ;

  human : Gender = Masc ; --- doesn't matter

  pronI = mkPronoun "I" "me" "my" "mine" Sg P1 human ;
  pronYouSg = mkPronoun "you" "you" "your" "yours" Sg P2 human ; -- verb form still OK
  pronHe = mkPronoun "he" "him" "his" "his" Sg P3 Masc ;
  pronShe = mkPronoun "she" "her" "her" "hers" Sg P3 Fem ;
  pronIt = mkPronoun "it" "it" "its" "it" Sg P3 Neutr ;

  pronWe = mkPronoun "we" "us" "our" "ours" Pl P1 human ;
  pronYouPl = mkPronoun "you" "you" "your" "yours" Pl P2 human ;
  pronThey = mkPronoun "they" "them" "their" "theirs" Pl P3 human ; ---

-- Relative pronouns in the accusative have the 'no pronoun' variant.
-- The simple pronouns do not really depend on number.

  relPron : RelPron = {s = table {
    Neutr => \\_ => table {
      NomP => variants {"that" ; "which"} ;
      AccP => variants {"that" ; "which" ; []} ;
      GenP => variants {"whose"} ;
      GenSP => variants {"which"}
      } ;
    _ => \\_ => table {
      NomP => variants {"that" ; "who"} ;
      AccP => variants {"that" ; "who" ; "whom" ; []} ;
      GenP => variants {"whose"} ;
      GenSP => variants {"whom"}
      }
    }
  } ;


--3 Determiners
--
-- We have just a heuristic definition of the indefinite article.
-- There are lots of exceptions: consonantic "e" ("euphemism"), consonantic
-- "o" ("one-sided"), vocalic "u" ("umbrella").

  artIndef = pre {"a" ; 
                  "an" / strs {"a" ; "e" ; "i" ; "o" ; "A" ; "E" ; "I" ; "O" }} ;

  artDef = "the" ;

--2 Adjectives
--
-- To form the adjectival and the adverbial forms, two strings are needed
-- in the worst case.

  mkAdjective : Str -> Str -> Adjective = \free,freely -> {
    s = table {
      AAdj => free ;
      AAdv => freely
      }
    } ;
  
-- However, the ending "iy" is sufficient for most cases. This function 
-- automatically changes the word-final "y" to "i" ("happy" - "happily").
-- N.B. this is not correct for "shy", but $mkAdjective$ has to be used.

  regAdjective : Str -> Adjective = \free -> 
    let 
      y = Predef.dp 1 free
    in mkAdjective 
         free 
         (ifTok Str y "y" (Predef.tk 1 free + ("ily")) (free + "ly")) ;

-- For the comparison of adjectives, six forms are needed to cover all cases.
-- But there is no adjective that actually needs all these.

  mkAdjDegrWorst : (_,_,_,_,_,_ : Str) -> AdjDegr = 
    \good,well,better,betterly,best,bestly -> 
    {s = table {
       Pos => (mkAdjective good well).s ;
       Comp => (mkAdjective better betterly).s ; 
       Sup => (mkAdjective best bestly).s
       }
    } ;

-- What is usually needed for irregular comparisons are just three forms,
-- since the adverbial form is the same (in comparative or superlative)
-- or formed in the regular way (positive).

  adjDegrIrreg : (_,_,_ : Str) -> AdjDegr = \bad,worse,worst ->
    let badly = (regAdjective bad).s ! AAdv
    in mkAdjDegrWorst bad badly worse worse worst worst ;

-- Like above, the regular formation takes account of final "y".

  adjDegrReg : Str -> AdjDegr = \happy ->
    let happi = ifTok Str (Predef.dp 1 happy) "y" (Predef.tk 1 happy + "i") happy
    in adjDegrIrreg happy (happi + "er") (happi + "est") ;

-- Many adjectives are 'inflected' by adding a comparison word.

  adjDegrLong : Str -> AdjDegr = \ridiculous ->
    adjDegrIrreg ridiculous ("more" ++ ridiculous) ("most" ++ ridiculous) ;


--3 Verbs
--
-- Except for "be", the worst case needs four forms.

  mkVerbP3worst : (_,_,_,_,_: Str) -> VerbP3 = \go,goes,went,gone,going -> 
    {s = table {
       InfImp => go ; 
       Indic Sg => goes ; 
       Indic _ => go ; 
       Pastt   => went ;
       PPart => gone ;
       PresPart => going
       }
    } ;

  mkVerbP3 : (_,_,_,_: Str) -> VerbP3 = \go,goes,went,gone -> 
    let going = case last go of {
      "e" => init go + "ing" ;
      _ => go + "ing"
      }
    in
    mkVerbP3worst go goes went gone going ;

-- This is what we use to derive the irregular forms in almost all cases

  mkVerbIrreg : (_,_,_ : Str) -> VerbP3 = \bite,bit,bitten -> 
    let bites = case last bite of {
      "y" => y2ie bite "s" ;
      "s" => init bite + "es" ;
      _   => bite + "s"
      } 
    in mkVerbP3 bite bites bit bitten ;

-- This is used to derive regular forms.

  mkVerbReg : Str -> VerbP3 = \soak -> 
    let 
      soaks = case last soak of {
        "y" => y2ie soak "s" ;
        "s" => init soak + "es" ;
        _   => soak + "s"
        } ;
      soaked = case last soak of {
        "e" => init soak + "s" ;
        _   => soak + "ed"
        }
    in 
    mkVerbP3 soak soaks soaked soaked ;

  mkVerb : (_,_,_ : Str) -> VerbP3 = \ring,rang,rung ->
    mkVerbP3 ring (ring + "s") rang rung ;

  regVerbP3 : Str -> VerbP3 = \walk -> 
    mkVerb walk (walk + "ed") (walk + "ed") ;

  verbP3s   : Str -> VerbP3 = \kiss -> 
    mkVerbP3 kiss (kiss + "es") (kiss + "ed") (kiss + "ed") ;

  verbP3e   : Str -> VerbP3 = \love -> 
    mkVerbP3 love (love + "s") (love + "d") (love + "d") ;

  verbP3y   : Str -> VerbP3 = \cr -> 
    mkVerbP3 (cr + "y") (cr + "ies") (cr + "ied") (cr + "ied") ;

  verbGen : Str -> VerbP3 = \kill -> case last kill of {
    "y" => verbP3y (init kill) ;
    "e" => verbP3y (init kill) ;
    "s" => verbP3s (init kill) ;
    _   => regVerbP3 kill
    } ;

  verbP3Have = mkVerbP3 "have" "has" "had" "had" ;

  verbP3Do   = mkVerbP3 "do" "does" "did" "done" ;

  auxVerbBe : AuxVerb = {s = table {
    AInfImp => "be" ; 
    AIndic P1 b => if_then_Str b "am" ["am not"] ; 
    AIndic P2 b => negAux b "are" ;
    AIndic P3 b => negAux b "is" ;
    APastt Sg b => negAux b "was" ;
    APastt Pl b => negAux b "were" ;
    APPart => "been" ;
    APresPart => "being"
    }
  } ;

-- The negative forms are not used; 
--- the particle $want.s1$ disappears - is it ever needed?

  verb2aux : Verb -> AuxVerb = \want -> {s = table {
    AInfImp     => want.s ! InfImp ; 
    AIndic P3 b => want.s ! Indic Sg ;
    AIndic _ b  => want.s ! Indic Pl ;
    APastt _ b  => want.s ! Pastt ;
    APPart      => want.s ! PPart ;
    APresPart   => want.s ! PresPart 
    }
  } ;

  aux2verb : AuxVerb -> Verb = \want -> {s = table {
    InfImp     => want.s ! AInfImp ; 
    Indic Sg   => want.s ! AIndic P3 True ;
    Indic _    => want.s ! AIndic P2 True ;
    Pastt      => want.s ! APastt Pl True ;
    PPart      => want.s ! APPart ;
    PresPart   => want.s ! APresPart 
    } ;
   s1 = []
  } ;

-- The three most important example auxiliaries.

  mkVerbAux : (_,_,_,_: Str) -> AuxVerb = \beable, can, could, beenable -> 
    {s = table {
       AInfImp    => beable ; 
       AIndic _ b => negAux b can ; 
       APastt _ b => negAux b could ;
       APPart     => beenable ;
       APrepPart  => nonExist ---- fix!
       } ;
    } ;


  verbPart : VerbP3 -> Particle -> Verb = \v,p ->
    v ** {s1 = p} ;

  verbNoPart : VerbP3 -> Verb = \v -> verbPart v [] ;

  negAux : Bool -> Str -> Str = \b,is -> if_then_Str b is (is + "n't") ;

-- The optional negation contraction is a useful macro e.g. for "do".

  contractNot : Str -> Str = \is -> variants {is ++ "not" ; is + "n't"} ;

  dont = contractNot (verbP3Do.s ! InfImp) ;

-- From $numerals$.

param DForm = unit  | teen  | ten  ;
oper mkNum : Str -> Str -> Str -> {s : DForm => Str} = 
  \two -> \twelve -> \twenty -> 
  {s = table {unit => two ; teen => twelve ; ten => twenty}} ;
oper regNum : Str -> {s : DForm => Str} = 
  \six -> mkNum six (six + "teen") (six + "ty") ;

} ;

