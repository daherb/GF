-- (c) 2009 Aarne Ranta under LGPL

concrete WordsDan of Words = SentencesDan ** 
    open SyntaxDan, ParadigmsDan, IrregDan, (L = LexiconDan), ExtraDan, Prelude in {

  lin

-- kinds of food

    Apple = mkCN L.apple_N ;
    Beer = mkCN L.beer_N ;
    Bread = mkCN L.bread_N ;
--    Cheese = mkCN (mkN "ost") ;
--    Chicken = mkCN (mkN "kyckling") ;
--    Coffee = mkCN (mkN "kaffe" neutrum) ;
    Fish = mkCN L.fish_N ;
--    Meat = mkCN (mkN "k�tt" "k�tt") ;
    Milk = mkCN L.milk_N ;
--    Pizza = mkCN (mkN "pizza") ;
    Salt = mkCN L.salt_N ;
--    Tea = mkCN (mkN "te" neutrum) ;
    Water = mkCN L.water_N ;
    Wine = mkCN L.wine_N ;

-- properties

    Bad = L.bad_A ;
--    Cheap = mkA "billig" ;
--    Boring = mkA "tr�kig" ;
    Cold = L.cold_A ;
--    Delicious = mkA "l�cker" ;
--    Expensive = mkA "dyr" ;
--    Fresh = mkA "f�rsk" ;
    Good = L.good_A ;
--    Suspect = mkA "suspekt" "suspekt" ;
    Warm = L.warm_A ;

-- places

--    Airport = mkPlace (mkN "flygplats" "flygplatser") "p�" ;
--    Bar = mkPlace (mkN "bar" "barer") "i" ;
--    Church = mkPlace (mkN "kyrka") "i" ;
--    Cinema = mkPlace (mkN "bio" "bio" "bion" "biona") "p�" ; ---- ?
--    Hospital = mkPlace (mkN "sjukhus" "sjukhus") "p�" ;
--    Hotel = mkPlace (mkN "hotell" "hotell") "p�" ;
--    Museum = mkPlace (mkN "museum" "museet" "museer" "museerna") "p�" ;
--    Park = mkPlace (mkN "park" "parker") "i" ;
--    Restaurant = mkPlace (mkN "restaurang" "restauranger") "p�" ;
--    Shop = mkPlace (mkN "aff�r" "aff�r") "i" ;
--    School = mkPlace (mkN "skola") "p�" ;
--    Station = mkPlace (mkN "station" "stationer") "p�" ;
--    Theatre = mkPlace (mkN "teater" "teatrar") "p�" ;
--    Toilet = mkPlace (mkN "toalett" "toaletter") "p�" ;
--    University = mkPlace (mkN "universitet" "universitet") "p�" ;

-- currencies

--    DanishCrown = mkCN (mkA "dansk") (mkN "krona") | mkCN (mkN "krona") ;
--    Dollar = mkCN (mkN "dollar" "dollar") ;
--    Euro = mkCN (mkN "euro" "euro") ;
--    Lei = mkCN (mkN "lei" "lei") ;
--    SwedishCrown = mkCN (mkA "svensk") (mkN "krona") | mkCN (mkN "krona") ;

-- nationalities

--    Belgian = mkA "belgisk" ;
--    Belgium = mkNP (mkPN "Belgien") ;
--    English = mkNat "engelsk" "England" ;
--    Finnish = mkNat "finsk" "Finland" ;
--    Flemish = mkNP (mkPN "flaml�ndska") ;
--    French = mkNat "fransk" "Frankrike" ; 
--    Italian = mkNat "italiensk" "Italien" ;
--    Romanian = mkNat "rum�nsk" "Rum�nien" ;
--    Swedish = mkNat "svensk" "Sverige" ;

-- actions

--    AHasAge p num = mkCl p.name (mkNP num L.year_N) ;
--    AHasName p name = mkCl p.name (mkV2 (mkV "heter")) name ;
    AHasChildren p num = mkCl p.name have_V2 (mkNP num L.child_N) ;
--    AHasRoom p num = mkCl p.name have_V2 
--      (mkNP (mkNP a_Det (mkN "rum" "rum")) 
--        (SyntaxDan.mkAdv for_Prep (mkNP num (mkN "person" "personer")))) ;
--    AHasTable p num = mkCl p.name have_V2 
--      (mkNP (mkNP a_Det (mkN "bord" "bord")) 
--        (SyntaxDan.mkAdv for_Prep (mkNP num (mkN "person" "personer")))) ;
--    AHungry p = mkCl p.name (mkA "hungrig") ;
--    AIll p = mkCl p.name (mkA "sjuk") ;
--    AKnow p = mkCl p.name (mkV "veta" "vet" "vet" "visste" "vetat" "visst") ; 
--    ALike p item = mkCl p.name (mkV2 (mkV "tycker") (mkPrep "om")) item ;
--    ALive p co = mkCl p.name (mkVP (mkVP (mkV "bo")) (SyntaxDan.mkAdv in_Prep co)) ;
--    ALove p q = mkCl p.name (mkV2 (mkV "�lska")) q.name ;
--    AMarried p = mkCl p.name (mkA "gift") ;
--    AReady p = mkCl p.name (mkA "f�rdig") ;
--    AScared p = mkCl p.name (mkA "r�dd") ;
--    ASpeak p lang = mkCl p.name  (mkV2 (mkV "tala")) lang ;
--    AThirsty p = mkCl p.name (mkA "t�rstig") ;
--    ATired p = mkCl p.name (mkA "tr�tt") ;
--    AUnderstand p = mkCl p.name (mkV "f�rst�" "f�rstod" "f�rst�tt") ;
--    AWant p obj = mkCl p.name want_VV (mkVP have_V2 obj) ;
--    AWantGo p place = mkCl p.name want_VV (mkVP (mkVP L.go_V) place.to) ;

-- miscellaneous

--    QWhatName p = mkQS (mkQCl whatSg_IP p.name (mkV2 (mkV "heter"))) ;
--    QWhatAge p = mkQS (mkQCl (ICompAP (mkAP L.old_A)) p.name) ;
--    HowMuchCost item = mkQS (mkQCl how8much_IAdv (mkCl item (mkV "kosta"))) ; 
--    ItCost item price = mkCl item (mkV2 (mkV "kosta")) price ;

--    PropOpen p = mkCl p.name open_A ;
--    PropClosed p = mkCl p.name closed_A ;
--    PropOpenDate p d = mkCl p.name (mkVP (mkVP open_A) d) ; 
--    PropClosedDate p d = mkCl p.name (mkVP (mkVP closed_A) d) ; 
--    PropOpenDay p d = mkCl p.name (mkVP (mkVP open_A) d.habitual) ; 
--    PropClosedDay p d = mkCl p.name (mkVP (mkVP closed_A) d.habitual) ; 

-- Building phrases from strings is complicated: the solution is to use
-- mkText : Text -> Text -> Text ;

--    PSeeYou d = mkText (lin Text (ss ("vi ses"))) (mkPhrase (mkUtt d)) ;
--    PSeeYouPlace p d = 
--      mkText (lin Text (ss ("vi ses"))) 
--        (mkText (mkPhrase (mkUtt p.at)) (mkPhrase (mkUtt d))) ;

-- Relations are expressed as "my wife" or "my son's wife", as defined by $xOf$
-- below. Languages without productive genitives must use an equivalent of
-- "the wife of my son" for non-pronouns.

--    Wife = xOf sing (mkN "fru" "fruar") ;
--    Husband = xOf sing L.man_N ;
--    Son = xOf sing (mkN "son" "s�ner") ;
--    Daughter = xOf sing (mkN "dotter" "d�ttrar") ;
--    Children = xOf plur L.child_N ;

-- week days

--    Monday = mkDay "m�ndag" ;
--    Tuesday = mkDay "tisdag" ;
--    Wednesday = mkDay "onsdag" ;
--    Thursday = mkDay "torsdag" ;
--    Friday = mkDay "fredag" ;
--    Saturday = mkDay "l�rdag" ;
--    Sunday = mkDay "s�ndag" ;

--    Tomorrow = ParadigmsDan.mkAdv "imorgon" ;

--  oper
--    mkNat : Str -> Str -> NPNationality = \nat,co -> 
--      mkNPNationality (mkNP (mkPN (nat + "a"))) (mkNP (mkPN co)) (mkA nat) ;

--    mkDay : Str -> {name : NP ; point : Adv ; habitual : Adv} = \d ->
--      let day = mkNP (mkPN d) in 
--      mkNPDay day (SyntaxDan.mkAdv on_Prep day) 
--        (SyntaxDan.mkAdv on_Prep (mkNP a_Quant plNum (mkCN (mkN d)))) ;

--    mkPlace : N -> Str -> {name : CN ; at : Prep ; to : Prep} = \p,i -> 
--      mkCNPlace (mkCN p) (mkPrep i) to_Prep ;

--    open_A = mkA "�ppen" "�ppet" ;
--    closed_A = mkA "st�ngd" "st�ngt" ;

--    xOf : GNumber -> N -> NPPerson -> NPPerson = \n,x,p -> 
--      relativePerson n (mkCN x) (\a,b,c -> mkNP (GenNP b) a c) p ;


--}
}
