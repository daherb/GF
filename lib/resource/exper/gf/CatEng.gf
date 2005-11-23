concrete CatEng of Cat = open ResEng in {

  lincat
    S     = {s : Str} ;
    Cl    = {s : Tense => Anteriority => Polarity => Ord => Str} ;
    Slash = {s : Tense => Anteriority => Polarity => Ord => Str} ** {c2 : Str} ;

    VP = {
      s  : Tense => Anteriority => Polarity => Ord => Agr => {fin, inf : Str} ; 
      s2 : Agr => Str
      } ;

    AP = {s : Str} ; 
    Comp = {s : Agr => Str} ; 

    V, VS, VQ = Verb ; -- = {s : VForm => Str} ;
    V2, VV = Verb ** {c2 : Str} ;
    V3 = Verb ** {c2, c3 : Str} ;

    Adv = {s : Str} ;

    Det, Quant = {s : Str ; n : Number} ;
    Predet, Num = {s : Str} ;

    CN,N = {s : Number => Case => Str} ;
    PN = {s : Case => Str} ;
    Pron, NP = {s : Case => Str ; a : Agr} ;
    N2 = {s : Number => Case => Str} ** {c2 : Str} ;
    N3 = {s : Number => Case => Str} ** {c2,c3 : Str} ;

}
