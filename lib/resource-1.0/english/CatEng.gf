concrete CatEng of Cat = open ResEng, Prelude in {

  flags optimize=all_subs ;

  lincat

-- Phrase

    Text, Phr, Utt, Voc = {s : Str} ;

-- Tensed/Untensed

    S  = {s : Str} ;
    QS = {s : QForm => Str} ;
    RS = {s : Agr => Str} ;

-- Sentence

    Cl = {s : Tense => Anteriority => Polarity => Order => Str} ;
    Slash = {s : Tense => Anteriority => Polarity => Order => Str} ** {c2 : Str} ;
    Imp = {s : Polarity => Number => Str} ;

-- Question

    QCl = {s : Tense => Anteriority => Polarity => QForm => Str} ;
    IP = {s : Case => Str ; n : Number} ;
    IAdv = {s : Str} ;    
    IDet = {s : Str ; n : Number} ;

-- Relative

    RCl = {s : Tense => Anteriority => Polarity => Agr => Str} ;
    RP = {s : Case => Str ; a : RAgr} ;

-- Verb

    VP = {
      s  : Tense => Anteriority => Polarity => Order => Agr => {fin, inf : Str} ; 
      s2 : Agr => Str
      } ;
    Comp = {s : Agr => Str} ; 
    SC = {s : Str} ;

-- Adjective

    AP = {s : Agr => Str ; isPre : Bool} ; 

-- Noun

    CN = {s : Number => Case => Str} ;
    NP, Pron = {s : Case => Str ; a : Agr} ;
    Det = {s : Str ; n : Number} ;
    Predet, QuantSg, QuantPl, Num, Ord = {s : Str} ;

-- Adverb

    Adv, AdV, AdA, AdS, AdN = {s : Str} ;

-- Numeral

    Numeral = {s : CardOrd => Str ; n : Number} ;

-- Structural

    Conj = {s : Str ; n : Number} ;
    DConj = {s1,s2 : Str ; n : Number} ;
    PConj = {s : Str} ;    
    CAdv = {s : Str} ;    
    Subj = {s : Str} ;
    Prep = {s : Str} ;

-- Open lexical classes, e.g. Basic

    V, VS, VQ, VA = Verb ; -- = {s : VForm => Str} ;
    V2, VV, V2A = Verb ** {c2 : Str} ;
    V3 = Verb ** {c2, c3 : Str} ;

    A = {s : AForm => Str} ;
    A2 = {s : AForm => Str ; c2 : Str} ;

    N = {s : Number => Case => Str} ;
    N2 = {s : Number => Case => Str} ** {c2 : Str} ;
    N3 = {s : Number => Case => Str} ** {c2,c3 : Str} ;
    PN = {s : Case => Str} ;

}
