concrete CatLat of Cat = CommonX ** open ResLat, Prelude in {

  flags optimize=all_subs ;

  lincat

---- Tensed/Untensed
--
--    S  = {s : Str} ;
--    QS = {s : QForm => Str} ;
--    RS = {s : Agr => Str ; c : Case} ; -- c for it clefts
--    SSlash = {s : Str ; c2 : Str} ;
--
---- Sentence
--
    Cl = {s : VAnter => VTense => Polarity => Str} ;
--    ClSlash = {
--      s : ResLat.Tense => Anteriority => CPolarity => Order => Str ;
--      c2 : Str
--      } ;
--    Imp = {s : CPolarity => ImpForm => Str} ;
--
---- Question
--
--    QCl = {s : ResLat.Tense => Anteriority => CPolarity => QForm => Str} ;
--    IP = {s : Case => Str ; n : Number} ;
--    IComp = {s : Str} ;    
--    IDet = {s : Str ; n : Number} ;
--    IQuant = {s : Number => Str} ;
--
---- Relative
--
--    RCl = {
--      s : ResLat.Tense => Anteriority => CPolarity => Agr => Str ; 
--      c : Case
--      } ;
--    RP = {s : RCase => Str ; a : RAgr} ;
--
---- Verb
--
    VP = ResLat.VP ;
    VPSlash = ResLat.VP ** {c2 : Preposition} ;
    Comp = {s : Gender => Number => Case => Str} ; 
--
---- Adjective
--
--    AP = Adjective ** {isPre : Bool} ; ---- {s : Agr => Str ; isPre : Bool} ; 
    AP = 
      { 
	s : APForm => Str ;
--	isPre : Bool ; -- should have no use in latin because adjectives can appear variably before and after nouns
      } ;
--
---- Noun
--
    CN = ResLat.CommonNoun ;
    NP = ResLat.NounPhrase ;
    Pron = ResLat.Pronoun ;
    Det = Determiner ;
--    Predet, Ord = {s : Str} ;
    Num  = {s : Gender => Case => Str ; n : Number} ;
--    Card = {s : Str ; n : Number} ;
    Quant = Quantifier ;
--
---- Numeral
--
--    Numeral = {s : CardOrd => Str ; n : Number} ;
    Digits  = {s : Str ; unit : Unit} ;
--
---- Structural
--
    Conj = {s1,s2 : Str ; n : Number} ;
--    Subj = {s : Str} ;
    Prep = ResLat.Preposition ;
--
---- Open lexical classes, e.g. Lexicon

--    V = Verb ;
    V, VS, VQ, VA = Verb ; -- = {s : VForm => Str} ;
    V2, V2A, V2Q, V2S = Verb ** {c : Prep } ;
--    V2, V2A, V2Q, V2S = Verb ** {c2 : Str} ;
    V3 = Verb ** {c2, c3 : Prep} ;
    VV = Verb ** { isAux : Bool } ;
    V2V = Verb ** {c2 : Str ; isAux : Bool} ;
--
    A = Adjective ** {isPre : Bool} ;

--
    N = Noun ;
-- To be really implemented
    N2 = Noun ;
    N3 = Noun ;
    PN = Noun ;
    A2 = Adjective ** { c2 : Prep} ;
--    N2 = {s : Number => Case => Str ; g : Gender} ** {c2 : Str} ;
--    N3 = {s : Number => Case => Str ; g : Gender} ** {c2,c3 : Str} ;
--    PN = {s : Case => Str ; g : Gender} ;
--
}
