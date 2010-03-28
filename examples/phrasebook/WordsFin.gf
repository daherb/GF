-- (c) 2009 Aarne Ranta under LGPL

concrete WordsFin of Words = SentencesFin ** 
    open SyntaxFin, ParadigmsFin in {
  lin
    Wine = mkCN (mkN "viini") ;
    Beer = mkCN (mkN "olut") ;
    Water = mkCN (mkN "vesi" "veden" "vesi�") ;
    Coffee = mkCN (mkN "kahvi") ;
    Tea = mkCN (mkN "tee") ;

    Pizza = mkCN (mkN "pizza") ;
    Cheese = mkCN (mkN "juusto") ;
    Fish = mkCN (mkN "kala") ;
    Fresh = mkAP (mkA "tuore") ;
    Warm = mkAP (mkA 
    (mkN "l�mmin" "l�mpim�n" "l�mmint�" "l�mpim�n�" "l�mpim��n" 
         "l�mpimin�" "l�mpimi�" "l�mpimien" "l�mpimiss�" "l�mpimiin"
	 ) 
    "l�mpim�mpi" "l�mpimin") ;
    Italian = mkAP (mkA "italialainen") ;
    Expensive = mkAP (mkA "kallis") ;
    Delicious = mkAP (mkA "herkullinen") ;
    Boring = mkAP (mkA "tyls�") ;

    Restaurant = mkCN (mkN "ravintola") ;
    Bar = mkCN (mkN "baari") ;
    Toilet = mkCN (mkN "vessa") ;

    Euro = mkCN (mkN "euro") ;
    Dollar = mkCN (mkN "dollari") ;
    Lei = mkCN (mkN "lei") ;

-- oper ---- optimization lasts forever
--  mkCNN : Str -> CN = \s -> mkCN (mkN s) ;
--  mkAPA : Str -> AP = \s -> mkAP (mkA s) ;
}
