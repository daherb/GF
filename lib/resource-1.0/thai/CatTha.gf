concrete CatTha of Cat = CommonX ** open ResTha, Prelude in {

  flags optimize=all_subs ;

  lincat

---- Tensed/Untensed
--
--    S  = {s : Str} ;
--    QS = {s : QForm => Str} ;
--    RS = {s : Agr => Str ; c : Case} ; -- c for it clefts
--
---- Sentence
--
--    Cl = {s : Tense => Anteriority => CPolarity => Order => Str} ;
--    Slash = {
--      s : Tense => Anteriority => CPolarity => Order => Str ;
--      c2 : Str
--      } ;
--    Imp = {s : CPolarity => ImpForm => Str} ;
--
---- Question
--
--    QCl = {s : Tense => Anteriority => CPolarity => QForm => Str} ;
--    IP = {s : Case => Str ; n : Number} ;
--    IComp = {s : Str} ;    
--    IDet = {s : Str ; n : Number} ;
--
---- Relative
--
--    RCl = {s : Tense => Anteriority => CPolarity => Agr => Str ; c : Case} ;
--    RP = {s : RCase => Str ; a : RAgr} ;
--
---- Verb
--
--    VP = {
--      s : Tense => Anteriority => CPolarity => Order => Agr => {fin, inf : Str} ;
--      prp : Str ; -- present participle 
--      inf : Str ; -- infinitive
--      ad  : Str ;
--      s2  : Agr => Str
--      } ;
--
--    Comp = {s : Agr => Str} ; 
--
---- Adjective
--
--    AP = {s : Agr => Str ; isPre : Bool} ; 
--
-- Noun
--
    CN = Noun ;
    NP, Pron = SS ;
    Det = Determiner ; 
--    Predet, Ord = {s : Str} ;
    Num, Quant, QuantSg, QuantPl = {s : Str ; hasC : Bool} ;

-- Numeral

    Numeral = {s : Str} ;

---- Structural
--
--    Conj = {s : Str ; n : Number} ;
--    DConj = {s1,s2 : Str ; n : Number} ;
--    Subj = {s : Str} ;
--    Prep = {s : Str} ;
--
---- Open lexical classes, e.g. Lexicon
--
--    V, VS, VQ, VA = Verb ; -- = {s : VForm => Str} ;
--    V2, V2A = Verb ** {c2 : Str} ;
--    V3 = Verb ** {c2, c3 : Str} ;
--    VV = {s : VVForm => Str ; isAux : Bool} ;
--
--    A = {s : AForm => Str} ;
--    A2 = {s : AForm => Str ; c2 : Str} ;
--
    N = Noun ;
--    N2 = {s : Number => Case => Str} ** {c2 : Str} ;
--    N3 = {s : Number => Case => Str} ** {c2,c3 : Str} ;
--    PN = {s : Case => Str} ;
--
}
