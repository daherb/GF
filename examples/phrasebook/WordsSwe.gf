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

}
