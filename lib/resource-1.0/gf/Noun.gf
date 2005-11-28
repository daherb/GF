--1 The construction of nouns, noun phrases, and determiners

abstract Noun = Cat ** {

  fun
    DetCN   : Det -> CN -> NP ;
    UsePN   : PN -> NP ;
    UsePron : Pron -> NP ;

    MkDet : Predet -> Quant -> Num -> Det ;
    
    PossPronSg, PossPronPl : Pron -> Quant ; --- PossNP not in romance

    NoNum  : Num ;
    NumInt : Int -> Num ;

    CardNumeral : Numeral -> Num ;
    OrdNumeral  : Numeral -> Num ;
    
    NumSuperl : A -> Num ;

    NoPredet : Predet ;

    DefSg,   DefPl   : Quant ;
    IndefSg, IndefPl : Quant ;

    ComplN2 : N2 -> NP -> CN ;
    ComplN3 : N3 -> NP -> N2 ;

    AdjCN   : AP -> CN -> CN ;
    SentCN  : CN -> S  -> CN ;
    QuestCN : CN -> QS -> CN ;

    UseN : N -> CN ;

} ;
