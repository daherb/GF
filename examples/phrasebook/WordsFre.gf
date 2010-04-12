-- (c) 2009 Ramona Enache and Aarne Ranta under LGPL

concrete WordsFre of Words = SentencesFre ** open
  SyntaxFre,
  IrregFre,
  (E = ExtraFre),
  (L = LexiconFre),
  ParadigmsFre,
  (P = ParadigmsFre),
  Prelude in {

lin

-- kinds

    Apple = mkCN L.apple_N ;
    Beer = mkCN L.beer_N ;
    Bread = mkCN L.bread_N ;
    Cheese = mkCN (mkN "fromage" masculine) ;
    Chicken = mkCN (mkN "poulet") ;
    Coffee = mkCN (mkN "caf�") ;
    Fish = mkCN L.fish_N ;
    Meat = mkCN (mkN "viande") ;
    Milk = mkCN L.milk_N ;
    Pizza = mkCN (mkN "pizza" feminine) ;
    Salt = mkCN L.salt_N ;
    Tea = mkCN (mkN "th�") ;
    Water = mkCN L.water_N ;
    Wine = mkCN L.wine_N ;

-- properties

    Bad = L.bad_A ;
    Boring = mkA "ennuyeux" ;
    Cheap = let bm = "bon march�" in mkA bm bm bm bm ;
    Cold = L.cold_A ;
    Delicious = mkA "d�licieux" ;
    Expensive = mkA "cher" ;
    Fresh = mkA "frais" "fra�che" "frais" "fra�chement" ;
    Good = L.good_A ;
    Suspect = mkA "suspect" ;
    Warm = L.warm_A ;

-- places

    Airport = mkPlace (mkN "a�roport") dative ;
    Bar = mkPlace (mkN "bar") in_Prep ;
    Church = mkPlace (mkN "�glise") in_Prep ;
    Cinema = mkPlace (mkN "cin�ma" masculine) in_Prep ;
    Hospital = mkPlace (mkN "h�pital") dative ;
    Hotel = mkPlace (mkN "h�tel") dative ;
    Museum = mkPlace (mkN "mus�e" masculine) in_Prep ;
    Park = mkPlace (mkN "parc") in_Prep ;
    Restaurant = mkPlace (mkN "restaurant") in_Prep ;
    School = mkPlace (mkN "�cole") dative ;
    Shop = mkPlace (mkN "magasin") in_Prep ;
    Station = mkPlace (mkN "gare") dative ;
    Theatre = mkPlace (mkN "th��tre" masculine) in_Prep ;
    Toilet = mkPlace (mkN "toilette") in_Prep ;
    University = mkPlace (mkN "universit�" feminine) dative ;

-- currencies

    DanishCrown = mkCN (mkA "danois") (mkN "couronne") | mkCN (mkN "couronne") ;
    Dollar = mkCN (mkN "dollar") ;
    Euro = mkCN (mkN "euro") ;
    Lei = mkCN (mkN "leu" "lei" masculine) ;
    SwedishCrown = mkCN (mkA "su�dois") (mkN "couronne") | mkCN (mkN "couronne") ;

-- nationalities

    Belgian = mkA "belge" ;
    Belgium = mkNP (mkPN "Belgique") ;
    English = mkNat "anglais" "Angleterre" ;
    Finnish = mkNat "finlandais" "Finlande" ;
    Flemish = mkNP (mkPN "flamand") ;
    French = mkNat "fran�ais" "France" ; 
    Italian = mkNat "italien" "Italie" ;
    Romanian = mkNat "roumain" "Roumanie" ;
    Swedish = mkNat "su�dois" "Su�de" ;

-- actions

    AHasAge p num = mkCl p.name have_V2 (mkNP num L.year_N) ;
    AHasChildren p num = mkCl p.name have_V2 (mkNP num L.child_N) ;
    AHasRoom p num = mkCl p.name have_V2 
      (mkNP (mkNP a_Det (mkN "chambre")) 
        (SyntaxFre.mkAdv for_Prep (mkNP num (mkN "personne")))) ;
    AHasTable p num = mkCl p.name have_V2 
      (mkNP (mkNP a_Det (mkN "table")) 
        (SyntaxFre.mkAdv for_Prep (mkNP num (mkN "personne")))) ;
    AMarried p = mkCl p.name (mkA "mari�") ;
    AWant p obj = mkCl p.name vouloir_V2 obj ;
    ALike p item = mkCl item plaire_V2 p.name ;
    ASpeak p lang = mkCl p.name  (mkV2 (mkV "parler")) lang ;
    ALove p q = mkCl p.name (mkV2 (mkV "aimer")) q.name ;
    AHungry p = mkCl p.name (E.ComplCN have_V2 (mkCN (mkN "faim" feminine))) ;
    AReady p = mkCl p.name (mkA "pr�t") ;
    AThirsty p = mkCl p.name (E.ComplCN have_V2 (mkCN (mkN "soif" feminine))) ;
    ATired p = mkCl p.name (mkA "fatigu�") ;
    AScared p = mkCl p.name (E.ComplCN have_V2 (mkCN (mkN "peur" feminine))) ;
    AIll p = mkCl p.name (mkA "malade") ;
    AUnderstand p = mkCl p.name (mkV IrregFre.comprendre_V2) ;
    AKnow p = mkCl p.name (mkV IrregFre.savoir_V2) ;
    AWantGo p place = mkCl p.name want_VV (mkVP (mkVP L.go_V) place.to) ;
    AHasName p name = mkCl p.name (mkV2 (reflV (mkV "appeler"))) name ;
    ALive p co = mkCl p.name (mkVP (mkVP (mkV "habiter")) (SyntaxFre.mkAdv (mkPrep "en") co)) ;

-- miscellaneous

    QWhatName p = mkQS (mkQCl how_IAdv (mkCl p.name (reflV (mkV "appeler")))) ;
    QWhatAge p = mkQS (mkQCl (mkIP whichSg_IDet (mkN "�ge" masculine)) p.name have_V2) ; 

    PropOpen p = mkCl p.name open_A ;
    PropClosed p = mkCl p.name closed_A ;
    PropOpenDate p d = mkCl p.name (mkVP (mkVP open_A) d) ; 
    PropClosedDate p d = mkCl p.name (mkVP (mkVP closed_A) d) ; 
    PropOpenDay p d = mkCl p.name (mkVP (mkVP open_A) d.habitual) ; 
    PropClosedDay p d = mkCl p.name (mkVP (mkVP closed_A) d.habitual) ; 

    HowMuchCost item = mkQS (mkQCl how8much_IAdv (mkCl item (mkV "co�ter"))) ; 
    ItCost item price = mkCl item (mkV2 (mkV "co�ter")) price ;

-- Building phrases from strings is complicated: the solution is to use
-- mkText : Text -> Text -> Text ;

    PSeeYou d = mkText (lin Text (ss ("on se verra"))) (mkPhrase (mkUtt d)) ;
    PSeeYouPlace p d = 
      mkText (lin Text (ss ("on se verra"))) 
        (mkText (mkPhrase (mkUtt p.at)) (mkPhrase (mkUtt d))) ;

-- Relations are expressed as "my wife" or "the wife of my son", as defined by $xOf$
-- below. Languages with productive genitives can use an equivalent of
-- "my son's wife" for non-pronouns, as e.g. in English.


    Wife = xOf sing (mkN "femme") ;
    Husband = xOf sing (mkN "mari") ;
    Son = xOf sing (mkN "fils") ;
    Daughter = xOf sing (mkN "fille") ;
    Children = xOf plur L.child_N ;

-- week days

    Monday = mkDay "lundi" ;
    Tuesday = mkDay "mardi" ;
    Wednesday = mkDay "mercredi" ;
    Thursday = mkDay "jeudi" ;
    Friday = mkDay "vendredi" ;
    Saturday = mkDay "samedi" ;
    Sunday = mkDay "dimanche" ;

    Tomorrow = ParadigmsFre.mkAdv "demain" ;


  oper
    mkNat : Str -> Str -> NPNationality = \nat,co -> 
      mkNPNationality (mkNP (mkPN nat)) (mkNP (mkPN co)) (mkA nat) ;

    mkDay : Str -> {name : NP ; point : Adv ; habitual : Adv} = \d ->
      let day = mkNP (mkPN d) in
      mkNPDay day (P.mkAdv d) (P.mkAdv ("le" ++ d)) ;

    mkPlace : N -> Prep -> {name : CN ; at : Prep ; to : Prep} = \p,i ->
      mkCNPlace (mkCN p) i dative ;

    open_A = P.mkA "ouvert" ;
    closed_A = P.mkA "ferm�" ;

    xOf : GNumber -> N -> NPPerson -> NPPerson = \n,x,p -> mkRelative n (mkCN x) p ; 

}
