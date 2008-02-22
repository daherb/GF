concrete CatBul of Cat = open ResBul, Prelude, (R = ParamX) in {

  flags optimize=all_subs ;


  lincat

-- Text, Phrase, Utterance

    Text = {s : Str} ;
    Phr = {s : Str} ;
    Utt = {s : Str} ;
    Voc = {s : Str} ;
    PConj = {s : Str} ;

-- Tense, Anteriority, Polarity

    Tense = {s : Str ; t : R.Tense} ;
    Ant   = {s : Str ; a : R.Anteriority} ;
    Pol   = {s : Str ; p : R.Polarity} ;
    
-- Tensed/Untensed

    S  = {s : Str} ;
    QS = {s : QForm => Str} ;
    SC  = {s : Str} ;

-- Sentence

    Cl = {s : ResBul.Tense => Anteriority => Polarity => Order => Str} ;
    Imp = {s : Polarity => GenNum => Str} ;

-- Question

    QCl = {s : ResBul.Tense => Anteriority => Polarity => QForm => Str} ;
    IP = {s : Str ; gn : GenNum} ;
    IComp = {s : Str} ;    
    IDet = {s : GenNum => Str; n : Number} ;

-- Verb

    VP = {
      s : ResBul.Tense => Anteriority => Polarity => Agr => Str ;
      imp : Polarity => Number => Str ;
      s2 : Agr => Str
    } ;

    Comp = {s : Agr => Str} ; 
    AdV = {s : Str} ; --lock_AdV : {}} ;

-- Adjective

    AP = {s : AForm => Str; isPre : Bool} ; 

-- Adjective

    Adv = {s : Str} ;
    CAdv = {s : Str; sn : Str} ;
    IAdv = {s : Str} ;
    AdA = {s : Str} ;

-- Noun

    CN = {s : NForm => Str; g : DGender} ;
    NP = {s : Case => Str; a : Agr} ;
    Pron = {s : Case => Str; gen : AForm => Str; a : Agr} ;
    Det = {s : DGender => Case => Str ; n : Number; countable : Bool; spec : Species} ;
    Predet = {s : GenNum => Str} ;
    Ord = {s : AForm => Str; nonEmpty : Bool} ;
    Num = {s : DGenderSpecies => Str; n : Number; nonEmpty : Bool} ;
    Quant = {s : GenNum => Str; spec : Species} ;

-- Numeral

    Numeral = {s : CardOrd => Str; n : Number} ;
    Digits  = {s : CardOrd => Str; n : Number; tail : DTail} ;
    AdN = {s : Str} ;

-- Structural

    Subj = {s : Str} ;
    Prep = {s : Str} ;

-- Open lexical classes, e.g. Lexicon

    V, VS, VQ, VA = Verb ;
    V2, V2A = Verb ** {c2 : Str} ;
    V3 = Verb ** {c2, c3 : Str} ;

    A = {s : AForm => Str} ;
    A2 = {s : AForm => Str ; c2 : Str} ;
    
    N = {s : NForm => Str; g : DGender} ;
    N2 = {s : NForm => Str; g : DGender} ** {c2 : Str} ;
    N3 = {s : NForm => Str; g : DGender} ** {c2,c3 : Str} ;
    PN = {s : Str; g : Gender} ;


-- Tense, Anteriority and Polarity functions

  lin
    PPos  = {s = []} ** {p = R.Pos} ;
    PNeg  = {s = []} ** {p = R.Neg} ;
    TPres = {s = []} ** {t = R.Pres} ;
    TPast = {s = []} ** {t = R.Past} ;   --# notpresent
    TFut  = {s = []} ** {t = R.Fut} ;    --# notpresent
    TCond = {s = []} ** {t = R.Cond} ;   --# notpresent
    ASimul = {s = []} ** {a = R.Simul} ;
    AAnter = {s = []} ** {a = R.Anter} ; --# notpresent
}