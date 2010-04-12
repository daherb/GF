-- (c) 2009 Aarne Ranta under LGPL

concrete WordsFin of Words = SentencesFin ** 
  open 
    SyntaxFin, ParadigmsFin, (L = LexiconFin), 
    Prelude, (E = ExtraFin) in {

  lin

-- kinds

    Apple = mkCN L.apple_N ;
    Beer = mkCN L.beer_N ;
    Bread = mkCN L.bread_N ;
    Cheese = mkCN (mkN "juusto") ;
    Chicken = mkCN (mkN "kana") ;
    Coffee = mkCN (mkN "kahvi") ;
    Fish = mkCN L.fish_N ;
    Meat = mkCN (mkN "liha") ;
    Milk = mkCN L.milk_N ;
    Pizza = mkCN (mkN "pizza") ;
    Salt = mkCN L.salt_N ;
    Tea = mkCN (mkN "tee") ;
    Water = mkCN L.water_N ;
    Wine = mkCN L.wine_N ;

-- qualities

    Bad = L.bad_A ;
    Boring = mkA "tyls�" ;
    Cheap = mkA "halpa" ;
    Cold = L.cold_A ;
    Delicious = mkA "herkullinen" ;
    Expensive = mkA "kallis" ;
    Fresh = mkA "tuore" ;
    Good = L.good_A ;
    Suspect = mkA "ep�ilytt�v�" ;
    Warm = L.warm_A ;

-- places

    Restaurant = mkPlace (mkN "ravintola") ssa ;
    Bar = mkPlace (mkN "baari") ssa ;
    Toilet = mkPlace (mkN "vessa") ssa ;
    Museum = mkPlace (mkN "museo") ssa ;
    Airport = mkPlace (mkN "lento" (mkN "kentt�")) lla ;
    Station = mkPlace (mkN "asema") lla ;
    Hospital = mkPlace (mkN "sairaala") ssa ;
    Church = mkPlace (mkN "kirkko") ssa ;
    Cinema = mkPlace (mkN "elokuva" (mkN "teatteri")) ssa ;
    Theatre = mkPlace (mkN "teatteri") ssa ;
    Shop = mkPlace (mkN "kauppa") ssa ;
    Park = mkPlace (mkN "puisto") ssa ;
    Hotel = mkPlace (mkN "hotelli") ssa ;
    University = mkPlace (mkN "yliopisto") lla ;
    School = mkPlace (mkN "koulu") lla ;

-- currencies

    DanishCrown = mkCN (mkN "Tanskan kruunu") | mkCN (mkN "kruunu") ;
    Dollar = mkCN (mkN "dollari") ;
    Euro = mkCN (mkN "euro") ;
    Lei = mkCN (mkN "lei") ;
    SwedishCrown = mkCN (mkN "Ruotsin kruunu") | mkCN (mkN "kruunu") ;

-- nationalities

    Belgian = mkA "belgialainen" ;
    Belgium = mkNP (mkPN "Belgia") ;
    English = mkNat (mkPN "englanti") (mkPN "Englanti") (mkA "englantilainen") ;
    Finnish = 
      mkNat (mkPN (mkN "suomi" "suomia")) (mkPN (mkN "Suomi" "Suomia")) 
            (mkA "suomalainen") ;
    Flemish = mkNP (mkPN "flaami") ;
    French = mkNat (mkPN "ranska") (mkPN "Ranska") (mkA "ranskalainen") ; 
    Italian = mkNat (mkPN "italia") (mkPN "Italia") (mkA "italialainen") ;
    Romanian = mkNat (mkPN "romania") (mkPN "Romania") (mkA "romanialainen") ;
    Swedish = mkNat (mkPN "ruotsi") (mkPN "Ruotsi") (mkA "ruotsalainen") ;

    ---- it would be nice to have a capitalization Predef function

-- actions

    AHasAge p num = mkCl p.name (mkNP num L.year_N) ;
    AHasChildren p num = mkCl p.name have_V2 (mkNP num L.child_N) ;
    AHasName p name = mkCl (nameOf p) name ;
    AHasRoom p = haveForPerson p.name (mkCN (mkN "huone")) ;
    AHasTable p = haveForPerson p.name (mkCN (mkN "p�yt�")) ;
    AHungry p = E.AdvExistNP (SyntaxFin.mkAdv on_Prep p.name) (mkNP (mkN "n�lk�")) ;
    AIll p = mkCl p.name (mkA "sairas") ;
    AKnow p = mkCl p.name (mkV "tiet��") ;
    ALike p item = mkCl p.name L.like_V2 item ;
    ALive p co = mkCl p.name (mkVP (mkVP (mkV "asua")) (SyntaxFin.mkAdv in_Prep co)) ;
    ALove p q = mkCl p.name (mkV2 (mkV "rakastaa") partitive) q.name ;
    AMarried p = mkCl p.name (ParadigmsFin.mkAdv "naimisissa") ;
    AReady p = mkCl p.name (ParadigmsFin.mkA "valmis") ;
    AScared p = mkCl p.name (caseV partitive (mkV "pelottaa")) ;
    ASpeak p lang = mkCl p.name  (mkV2 (mkV "puhua") partitive) lang ;
    AThirsty p = E.AdvExistNP (SyntaxFin.mkAdv on_Prep p.name) (mkNP (mkN "jano")) ;
    ATired p = mkCl p.name (caseV partitive (mkV "v�sytt��")) ;
    AUnderstand p = mkCl p.name (mkV "ymm�rt��") ;
    AWant p obj = mkCl p.name (mkV2 "haluta") obj ;
    AWantGo p place = mkCl p.name want_VV (mkVP (mkVP L.go_V) place.to) ;

-- miscellaneous

    QWhatName p = mkQS (mkQCl whatSg_IP (mkVP (nameOf p))) ;
    QWhatAge p = mkQS (mkQCl (E.ICompAP (mkAP L.old_A)) p.name) ;
    HowMuchCost item = mkQS (mkQCl how8much_IAdv (mkCl item (mkV "maksaa"))) ; 
    ItCost item price = mkCl item (mkV2 (mkV "maksaa")) price ;

    PropOpen p = mkCl p.name open_Adv ;
    PropClosed p = mkCl p.name closed_Adv ;
    PropOpenDate p d = mkCl p.name (mkVP (mkVP open_Adv) d) ; 
    PropClosedDate p d = mkCl p.name (mkVP (mkVP closed_Adv) d) ; 
    PropOpenDay p d = mkCl p.name (mkVP (mkVP open_Adv) d.habitual) ; 
    PropClosedDay p d = mkCl p.name (mkVP (mkVP closed_Adv) d.habitual) ; 


-- Building phrases from strings is complicated: the solution is to use
-- mkText : Text -> Text -> Text ;

    PSeeYou d = mkText (lin Text (ss ("n�hd��n"))) (mkPhrase (mkUtt d)) ;
    PSeeYouPlace p d = 
      mkText (lin Text (ss ("n�hd��n"))) 
        (mkText (mkPhrase (mkUtt p.at)) (mkPhrase (mkUtt d))) ;

-- Relations are expressed as "my wife" or "my son's wife", as defined by $xOf$
-- below. Languages without productive genitives must use an equivalent of
-- "the wife of my son" for non-pronouns.

    Wife = xOf sing (mkN "vaimo") ;
    Husband = xOf sing L.man_N ;
    Son = xOf sing L.boy_N ;
    Daughter = xOf sing (mkN "tyt�r") ;
    Children = xOf plur L.child_N ;

-- week days

    Monday = let d = "maanantai" in mkDay (mkPN d) (d + "sin") ;
    Tuesday = let d = "tiistai" in mkDay (mkPN d) (d + "sin") ;
    Wednesday = let d = "keskiviikko" in mkDay (mkPN d) (d + "isin") ;
    Thursday = let d = "torstai" in mkDay (mkPN d) (d + "sin") ;
    Friday = let d = "perjantai" in mkDay (mkPN d) (d + "sin") ;
    Saturday = let d = "lauantai" in mkDay (mkPN d) (d + "sin") ;
    Sunday = let d = "sunnuntai" in mkDay (mkPN d) (d + "sin") ;

    Tomorrow = ParadigmsFin.mkAdv "huomenna" ;

  oper
    mkNat : PN -> PN -> A -> 
      {lang : NP ; prop : A ; country : NP} = \nat,co,pro ->
        {lang = mkNP nat ; 
         prop = pro ;
         country = mkNP co
        } ;

    ---- using overloaded paradigms slows down compilation dramatically
    mkDay : PN -> Str -> {name : NP ; point : Adv ; habitual : Adv} = \d,s ->
      let day = mkNP d in
      {name = day ; 
       point = SyntaxFin.mkAdv (casePrep essive) day ; 
       habitual = ParadigmsFin.mkAdv s
      } ;

    mkPlace : N -> Bool -> {name : CN ; at : Prep ; to : Prep} = \p,e -> {
      name = mkCN p ;
      at = casePrep (if_then_else Case e adessive inessive) ;  -- True: external
      to = casePrep (if_then_else Case e allative illative) ;
      } ;
    ssa = False ;
    lla = True ;

    xOf : GNumber -> N -> NPPerson -> NPPerson = \n,x,p -> 
      relativePerson n (mkCN x) (\a,b,c -> mkNP (E.GenNP b) a c) p ;

    nameOf : NPPerson -> NP = \p -> (xOf sing L.name_N p).name ;

  oper 
    -- do you have a table for five persons
    haveForPerson : NP -> CN -> Card -> Cl = \p,a,n ->
      mkCl p have_V2 
----      (mkNP (E.PartCN a)  ---- partitive works in questions 
        (mkNP (mkNP a_Det a)
           (SyntaxFin.mkAdv for_Prep (mkNP n (mkN "henki" "henki�")))) ;

    open_Adv = ParadigmsFin.mkAdv "avoinna" ;
    closed_Adv = ParadigmsFin.mkAdv "kiinni" ;

}
