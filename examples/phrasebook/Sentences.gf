abstract Sentences = Numeral ** {

  cat
    Phrase ;
    Sentence ; Question ; 
    Object ; Item ; Kind ; Quality ; 
    Place ; PlaceKind ; Currency ; Price ; Language ;
    Person ; Action ;

    -- abstract parameters
    Politeness ; 
    -- Gender ; 

  fun
    -- these phrases are formed here, not in Phrasebook, as they are functorial
    PSentence : Politeness -> Sentence -> Phrase ;
    PQuestion : Politeness -> Question -> Phrase ;

    PObject   : Object   -> Phrase ;
    PKind     : Kind     -> Phrase ;
    PQuality  : Quality  -> Phrase ;
    PNumeral  : Numeral  -> Phrase ;
    PPlace    : Place    -> Phrase ;
    PPlaceKind: PlaceKind-> Phrase ;
    PCurrency : Currency -> Phrase ;
    PPrice    : Price    -> Phrase ;
    PLanguage : Language -> Phrase ;

    Is    : Item -> Quality -> Sentence ;
    IsNot : Item -> Quality -> Sentence ;

    WhetherIs : Item -> Quality -> Question ;
    WhereIs   : Place -> Question ;

    SAction : Action -> Sentence ;
    SNotAction : Action -> Sentence ;
    QAction : Action -> Question ;

    HowMuchCost : Item -> Question ;
    ItCost : Item -> Price -> Sentence ;
    AmountCurrency : Numeral -> Currency -> Price ;

    ObjItem : Item -> Object ;
    ObjNumber : Numeral -> Kind -> Object ;
    
    This, That, These, Those, The, Thes : Kind -> Item ;
    SuchKind : Quality -> Kind -> Kind ;
    Very : Quality -> Quality ;
    Too : Quality -> Quality ;

    ThePlace : PlaceKind -> Place ;

    I, You : Person ;

    Polite, Familiar : Politeness ;
    -- Male, Female : Gender ;

}
