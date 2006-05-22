--1 Infrastructure with common implementations.

-- This module defines the categories that uniformly have the linearization
-- ${s : Str}$ in all languages. They are given lock fields that guarantee
-- grammatical correctness via type checking.

-- Moreover, this module defines the abstract parameters of tense, polarity, and
-- anteriority, which are used in [Phrase Phrase.html] to generate different
-- forms of sentences. Together they give 2 x 4 x 4 = 16 sentence forms.

-- These tenses are defined for all languages in the library. More tenses
-- can be defined in the language extensions, e.g. the "pass� simple" of
-- Romance languages.

abstract Common = {

  cat

--2 Top-level units

-- Constructed in [Text Text.html]: $Text$.

    Text ;   -- text consisting of several phrases
    Phr ;    -- phrase in a text                    e.g. "But come here my darling."

-- Constructed in [Phrase Phrase.html]: $Phr$ and

    Utt ;   -- sentence, question, word...         e.g. "be quiet"
    Voc ;   -- vocative or "please"                e.g. "my darling"
    PConj ; -- phrase-beginning conj.              e.g. "therefore"

    SC ;    -- embedded sentence or question       e.g. "that it rains"

    SC ;
    Adv ; 
    AdV ; 
    AdA ; 
    AdS ; 
    AdN ;

--2 Adverbs

-- Constructed in [Adverb Adverb.html].  
-- Many adverbs are constructed in [Structural Structural.html].

    Adv ;   -- verb-phrase-modifying adverb,       e.g. "in the house"
    AdV ;   -- adverb directly attached to verb    e.g. "always"
    AdA ;   -- adjective-modifying adverb,         e.g. "very"
    AdN ;   -- numeral-modifying adverb,           e.g. "more than"
    IAdv ;  -- interrogative adverb                e.g. "why"
    CAdv ;  -- comparative adverb                  e.g. "more"

    Pol ;
    Tense ;
    Ant ;

  fun
    PPos, PNeg : Pol ;             -- I sleep/don't sleep

    TPres  : Tense ;                
    ASimul : Ant ;
    TPast, TFut, TCond : Tense ;   -- I slept/will sleep/would sleep --# notpresent
    AAnter : Ant ;                 -- I have slept                   --# notpresent

}
