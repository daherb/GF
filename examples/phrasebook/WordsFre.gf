-- (c) 2009 Ramona Enache and Aarne Ranta under LGPL

concrete WordsFre of Words = SentencesFre ** open
  SyntaxFre,
  IrregFre,
  (E = ExtraFre),
  ParadigmsFre,
  (P = ParadigmsFre) in {

lin

Wine = mkCN (mkN "vin") ;
    Beer = mkCN (mkN "bi�re") ;
    Water = mkCN (mkN "eau" feminine) ;
    Coffee = mkCN (mkN "caf�") ;
    Tea = mkCN (mkN "th�") ;

Cheese = mkCN (mkN "fromage" masculine) ;
Fish = mkCN (mkN "poisson" masculine) ;
Pizza = mkCN (mkN "pizza" feminine) ;

Fresh = mkA "frais" "fra�che" "frais" "fra�chement" ;
Warm = mkA "chaud" ;
Expensive = mkA "cher" ;
Delicious = mkA "d�licieux" ;
Boring = mkA "ennuyeux" ;
Good = prefixA (mkA "bon" "bonne" "bons" "bien") ;

    Restaurant = mkPlace (mkN "restaurant") in_Prep ;
    Bar = mkPlace (mkN "bar") in_Prep ;
    Toilet = mkPlace (mkN "toilette") in_Prep ;
    Museum = mkPlace (mkN "mus�e" masculine) in_Prep ;
    Airport = mkPlace (mkN "a�roport") dative ;
    Station = mkPlace (mkN "gare") dative ;
    Hospital = mkPlace (mkN "h�pital") dative ;
    Church = mkPlace (mkN "�glise") in_Prep ;

    Euro = mkCN (mkN "euro") ;
    Dollar = mkCN (mkN "dollar") ;
    Lei = mkCN (mkN "leu" "lei" masculine) ;

    English = mkNat "anglais" "Angleterre" ;
    Finnish = mkNat "finlandais" "Finlande" ;
    French = mkNat "fran�ais" "France" ; 
    Italian = mkNat "italien" "Italie" ;
    Romanian = mkNat "roumain" "Roumanie" ;
    Swedish = mkNat "su�dois" "Su�de" ;

    Belgian = mkA "belge" ;
    Flemish = mkNP (mkPN "flamand") ;
    Belgium = mkNP (mkPN "Belgique") ;

    Monday = mkDay "lundi" ;
    Tuesday = mkDay "mardi" ;
    Wednesday = mkDay "mercredi" ;
    Thursday = mkDay "jeudi" ;
    Friday = mkDay "vendredi" ;
    Saturday = mkDay "samedi" ;
    Sunday = mkDay "dimanche" ;

    AWant p obj = mkCl p.name vouloir_V2 obj ;
    ALike p item = mkCl item plaire_V2 p.name ;
    ASpeak p lang = mkCl p.name  (mkV2 (mkV "parler")) lang ;
    ALove p q = mkCl p.name (mkV2 (mkV "aimer")) q.name ;
    AHungry p = mkCl p.name (E.ComplCN have_V2 (mkCN (mkN "faim" feminine))) ;
    AThirsty p = mkCl p.name (E.ComplCN have_V2 (mkCN (mkN "soif" feminine))) ;
    ATired p = mkCl p.name (mkA "fatigu�") ;
    AScared p = mkCl p.name (E.ComplCN have_V2 (mkCN (mkN "peur" feminine))) ;
    AIll p = mkCl p.name (mkA "malade") ;
    AUnderstand p = mkCl p.name (mkV IrregFre.comprendre_V2) ;
    AKnow p = mkCl p.name (mkV IrregFre.savoir_V2) ;
    AWantGo p place = 
      mkCl p.name want_VV (mkVP (mkVP IrregFre.aller_V) place.to) ;
    AHasName p name = mkCl p.name (mkV2 (reflV (mkV "appeler"))) name ;
    ALive p co = 
      mkCl p.name (mkVP (mkVP (mkV "habiter")) 
        (SyntaxFre.mkAdv (mkPrep "en") co)) ;

    QWhatName p = mkQS (mkQCl how_IAdv (mkCl p.name (reflV (mkV "appeler")))) ;

    PropOpen p = mkCl p.name open_A ;
    PropClosed p = mkCl p.name closed_A ;
    PropOpenDate p d = mkCl p.name (mkVP (mkVP open_A) d) ; 
    PropClosedDate p d = mkCl p.name (mkVP (mkVP closed_A) d) ; 
    PropOpenDay p d = mkCl p.name (mkVP (mkVP open_A) d.habitual) ; 
    PropClosedDay p d = mkCl p.name (mkVP (mkVP closed_A) d.habitual) ; 

    HowMuchCost item = mkQS (mkQCl how8much_IAdv (mkCl item (mkV "co�ter"))) ; 
    ItCost item price = mkCl item (mkV2 (mkV "co�ter")) price ;

  oper
    mkNat : Str -> Str -> {lang : NP ; prop : A ; country : NP} = \nat,co -> 
      {lang = mkNP (mkPN nat) ; prop = mkA nat ; country = mkNP (mkPN co)} ;

    mkDay : Str -> {name : NP ; point : Adv ; habitual : Adv} = \d ->
      let day = mkNP (mkPN d) in
      {name = day ; 
       point = P.mkAdv d ; 
       habitual = P.mkAdv ("le" ++ d) ;
      } ;

    mkPlace : N -> Prep -> {name : CN ; at : Prep ; to : Prep} = \p,i -> {
      name = mkCN p ;
      at = i ;
      to = dative
      } ;

    open_A = P.mkA "ouvert" ;
    closed_A = P.mkA "ferm�" ;

}
