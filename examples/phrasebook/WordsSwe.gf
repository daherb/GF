-- (c) 2009 Aarne Ranta under LGPL

concrete WordsSwe of Words = SentencesSwe ** 
    open SyntaxSwe, ParadigmsSwe in {
  lin
    Wine = mkCN (mkN "vin" "vinet" "viner" "vinerna") ;
    Beer = mkCN (mkN "�l" neutrum) ;
    Water = mkCN (mkN "vatten" "vattnet" "vatten" "vattnen") ;
    Coffee = mkCN (mkN "kaffe" neutrum) ;
    Tea = mkCN (mkN "te" neutrum) ;

    Pizza = mkCN (mkN "pizza") ;
    Cheese = mkCN (mkN "ost") ;
    Fish = mkCN (mkN "fisk") ;
    Fresh = mkAP (mkA "f�rsk") ;
    Warm = mkAP (mkA "varm") ;
    Italian = mkAP (mkA "italiensk") ;
    Expensive = mkAP (mkA "dyr") ;
    Delicious = mkAP (mkA "l�cker") ;
    Boring = mkAP (mkA "tr�kig") ;

    Restaurant = mkCN (mkN "restaurang" "restauranger") ;
    Bar = mkCN (mkN "bar" "barer") ;
    Toilet = mkCN (mkN "toalett" "toaletter") ;

    Euro = mkCN (mkN "euro" "euro") ;
    Dollar = mkCN (mkN "dollar" "dollar") ;
    Lei = mkCN (mkN "lei" "lei") ;

    English = mkNP (mkPN "engelska") ;
    Finnish = mkNP (mkPN "finska") ;
    French = mkNP (mkPN "franska") ; 
    Romanian = mkNP (mkPN "rum�nska") ;
    Swedish = mkNP (mkPN "svenska") ;

    AWant p obj = {s = \\r => mkCl (p.s ! r) want_VV (mkVP have_V2 obj)} ;
    ALike p item = {s = \\r => mkCl (p.s ! r) (mkV2 (mkV "tycker") (mkPrep "om")) item} ;
    AHave p kind = {s = \\r => mkCl (p.s ! r) have_V2 (mkNP kind)} ;
    ASpeak p lang = {s = \\r => mkCl (p.s ! r)  (mkV2 (mkV "tala")) lang} ;
    ALove p q = {s = \\r => mkCl (p.s ! r) (mkV2 (mkV "�lska")) (q.s ! r)} ;


}
