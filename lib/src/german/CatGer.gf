concrete CatGer of Cat = 
  CommonX - [Tense,Temp] ** 
  open ResGer, Prelude in {

  flags optimize=all_subs ;

  lincat

-- Tensed/Untensed

    S  = {s : Order => Str} ;
    QS = {s : QForm => Str} ;
    RS = {s : GenNum => Str ; c : Case} ;
    SSlash = {s : Order => Str} ** {c2 : Preposition} ;

-- Sentence

    Cl = {s : Mood => ResGer.Tense => Anteriority => Polarity => Order => Str} ;
    ClSlash = {
      s : Mood => ResGer.Tense => Anteriority => Polarity => Order => Str ; 
      c2 : Preposition
      } ;
    Imp = {s : Polarity => ImpForm => Str} ;

-- Question

    QCl = {s : Mood => ResGer.Tense => Anteriority => Polarity => QForm => Str} ;
    IP = {s : Case => Str ; n : Number} ;
    IComp = {s : Agr => Str} ; 
    IDet = {s : Gender => Case => Str ; n : Number} ;
    IQuant = {s : Number => Gender => Case => Str} ;

-- Relative

    RCl = {s : Mood => ResGer.Tense => Anteriority => Polarity => GenNum => Str ; c : Case} ;
    RP = {s : GenNum => Case => Str ; a : RAgr} ;

-- Verb

    VP = ResGer.VP ;
    VPSlash = ResGer.VP ** {c2 : Preposition} ;
    Comp = {s : Agr => Str} ; 

-- Adjective

    AP = {s : AForm => Str ; isPre : Bool} ; 

-- Noun

    CN = {s : Adjf => Number => Case => Str ; g : Gender} ;
    NP = {s : Case => Str ; a : Agr} ;
    Pron = {s : NPForm => Str ; a : Agr} ;
    Det = {s,sp : Gender => Case => Str ; n : Number ; a : Adjf} ;
    Quant = {
      s  : Bool => Number => Gender => Case => Str ; 
      sp : Number => Gender => Case => Str ; 
      a  : Adjf
      } ;
    Predet = {
      s : Number => Gender => Case => Str ; 
      c : {p : Str ; k : PredetCase} ;
      a : PredetAgr -- if an agr is forced, e.g. jeder von uns ist ...
      } ;
    Num = {s : Gender => Case => Str ; n : Number ; isNum : Bool} ;
    Card = {s : Gender => Case => Str ; n : Number} ;
    Ord = {s : AForm => Str} ;

-- Numeral

    Numeral = {s : CardOrd => Str ; n : Number } ;
    Digits = {s : CardOrd => Str ; n : Number } ;

-- Structural

    Conj = {s1,s2 : Str ; n : Number} ;
    Subj = {s : Str} ;
    Prep = {s : Str ; c : Case} ;

-- Open lexical classes, e.g. Lexicon

    V, VS, VQ, VA = ResGer.Verb ; -- = {s : VForm => Str} ;
    VV = Verb ** {isAux : Bool} ;
    V2, V2A, V2S, V2Q = Verb ** {c2 : Preposition} ;
    V2V = Verb ** {c2 : Preposition ; isAux : Bool} ;
    V3 = Verb ** {c2, c3 : Preposition} ;

    A  = {s : Degree => AForm => Str} ;
    A2 = {s : Degree => AForm => Str ; c2 : Preposition} ;

    N  = {s : Number => Case => Str ; g : Gender} ;
    N2 = {s : Number => Case => Str ; g : Gender} ** {c2 : Preposition} ;
    N3 = {s : Number => Case => Str ; g : Gender} ** {c2,c3 : Preposition} ;
    PN = {s : Case => Str} ;

-- tense with possibility to choose conjunctive forms

    Temp = {s : Str ; t : ResGer.Tense ; a : Anteriority ; m : Mood} ;
    Tense = {s : Str ; t : ResGer.Tense ; m : Mood} ;

}
