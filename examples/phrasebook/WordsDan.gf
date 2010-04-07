-- (c) 2009 Aarne Ranta under LGPL

concrete WordsDan of Words = SentencesDan ** 
    open SyntaxDan, ParadigmsDan, IrregDan, (L = LexiconDan), Prelude in {

  lin
 
-- kinds of food

    Apple = mkCN L.apple_N ;
    Beer = mkCN L.beer_N ;
    Bread = mkCN L.bread_N ;
--     Cheese = mkCN (mkN "ost") ;
--     Coffee = mkCN (mkN "kaffe" neutrum) ;
--     Fish = mkCN L.fish_N ;
--     Milk = mkCN L.milk_N ;
--     Pizza = mkCN (mkN "pizza") ;
    Salt = mkCN L.salt_N ;
--     Tea = mkCN (mkN "te" neutrum) ;
    Water = mkCN L.water_N ;
    Wine = mkCN L.wine_N ;

-- properties
-- 
    Bad = L.bad_A ;
--     Boring = mkA "tr�kig" ;
    Cold = L.cold_A ;
--     Delicious = mkA "l�cker" ;
--     Expensive = mkA "dyr" ;
--     Fresh = mkA "f�rsk" ;
    Good = L.good_A ;
    Warm = L.warm_A ;
-- 
-- places
-- 
--     Airport = mkPlace (mkN "flygplats" "flygplatser") "p�" ;
--     Bar = mkPlace (mkN "bar" "barer") "i" ;
--     Church = mkPlace (mkN "kyrka") "i" ;
--     Hospital = mkPlace (mkN "sjukhus" "sjukhus") "p�" ;
--     Museum = mkPlace (mkN "museum" "museet" "museer" "museerna") "p�" ;
--     Restaurant = mkPlace (mkN "restaurang" "restauranger") "p�" ;
--     Station = mkPlace (mkN "station" "stationer") "p�" ;
--     Toilet = mkPlace (mkN "toalett" "toaletter") "p�" ;
-- 
-- currencies
-- 
--     DanishCrown = mkCN (mkA "dansk") (mkN "krona") ;
--     Dollar = mkCN (mkN "dollar" "dollar") ;
--     Euro = mkCN (mkN "euro" "euro") ;
--     Lei = mkCN (mkN "lei" "lei") ;
--     SwedishCrown = mkCN (mkA "svensk") (mkN "krona") ;
-- 
-- nationalities
-- 
--     Belgian = mkA "belgisk" ;
--     Belgium = mkNP (mkPN "Belgien") ;
--     English = mkNat "engelsk" "England" ;
--     Finnish = mkNat "finsk" "Finland" ;
--     Flemish = mkNP (mkPN "flaml�ndska") ;
--     French = mkNat "fransk" "Frankrike" ; 
--     Italian = mkNat "italiensk" "Italien" ;
--     Romanian = mkNat "rum�nsk" "Rum�nien" ;
--     Swedish = mkNat "svensk" "Sverige" ;
-- 
-- actions
-- 
--     AHasName p name = mkCl (nameOf p) name ;
--     AHungry p = mkCl p.name (mkA "hungrig") ;
--     AIll p = mkCl p.name (mkA "sjuk") ;
--     AKnow p = mkCl p.name (mkV "veta" "vet" "vet" "visste" "vetat" "visst") ; 
--     ALike p item = mkCl p.name (mkV2 (mkV "tycker") (mkPrep "om")) item ;
--     ALive p co = mkCl p.name (mkVP (mkVP (mkV "bo")) (SyntaxDan.mkAdv in_Prep co)) ;
--     ALove p q = mkCl p.name (mkV2 (mkV "�lska")) q.name ;
--     AScared p = mkCl p.name (mkA "r�dd") ;
--     ASpeak p lang = mkCl p.name  (mkV2 (mkV "tala")) lang ;
--     AThirsty p = mkCl p.name (mkA "t�rstig") ;
--     ATired p = mkCl p.name (mkA "tr�tt") ;
--     AUnderstand p = mkCl p.name (mkV "f�rst�" "f�rstod" "f�rst�tt") ;
--     AWant p obj = mkCl p.name want_VV (mkVP have_V2 obj) ;
--     AWantGo p place = mkCl p.name want_VV (mkVP (mkVP L.go_V) place.to) ;
-- 
-- miscellaneous
-- 
--     QWhatName p = mkQS (mkQCl whatSg_IP (mkVP (nameOf p))) ;
-- 
--     PropOpen p = mkCl p.name open_A ;
--     PropClosed p = mkCl p.name closed_A ;
--     PropOpenDate p d = mkCl p.name (mkVP (mkVP open_A) d) ; 
--     PropClosedDate p d = mkCl p.name (mkVP (mkVP closed_A) d) ; 
--     PropOpenDay p d = mkCl p.name (mkVP (mkVP open_A) d.habitual) ; 
--     PropClosedDay p d = mkCl p.name (mkVP (mkVP closed_A) d.habitual) ; 
-- 
--     HowMuchCost item = mkQS (mkQCl how8much_IAdv (mkCl item (mkV "kosta"))) ; 
--     ItCost item price = mkCl item (mkV2 (mkV "kosta")) price ;
-- 
-- week days
-- 
--     Monday = mkDay "m�ndag" ;
--     Tuesday = mkDay "tisdag" ;
--     Wednesday = mkDay "onsdag" ;
--     Thursday = mkDay "torsdag" ;
--     Friday = mkDay "fredag" ;
--     Saturday = mkDay "l�rdag" ;
--     Sunday = mkDay "s�ndag" ;
-- 
--   oper
--     mkNat : Str -> Str -> {lang : NP ; prop : A ; country : NP} = \nat,co -> 
--       {lang = mkNP (mkPN (nat + "a")) ; 
--        prop = mkA nat ; country = mkNP (mkPN co)} ;
-- 
--     mkDay : Str -> {name : NP ; point : Adv ; habitual : Adv} = \d ->
--       let day = mkNP (mkPN d) in
--       {name = day ; 
--        point = SyntaxDan.mkAdv on_Prep day ; 
--        habitual = SyntaxDan.mkAdv on_Prep (mkNP a_Quant plNum (mkCN (mkN d)))
--       } ;
-- 
--     mkPlace : N -> Str -> {name : CN ; at : Prep ; to : Prep} = \p,i -> {
--       name = mkCN p ;
--       at = mkPrep i ;
--       to = to_Prep
--       } ;
-- 
--     open_A = mkA "�ppen" "�ppet" ;
--     closed_A = mkA "st�ngd" "st�ngt" ;
-- 
--     nameOf : {name : NP ; isPron : Bool ; poss : Det} -> NP = \p -> 
--       case p.isPron of {
--         True => mkNP p.poss (mkN "namn" "namn") ;
--         _    => mkNP (mkNP the_Det (mkN "namn" "namn")) 
--                        (SyntaxDan.mkAdv possess_Prep p.name)
--         } ;
-- }
}
