-- (c) 2009 Ramona Enache and Aarne Ranta under LGPL

concrete WordsIta of Words = SentencesIta ** open
  SyntaxIta,
  DiffPhrasebookIta,
  BeschIta,
  ParadigmsIta in {

lin

Wine = mkCN (mkN "vino") ;
    Beer = mkCN (mkN "birra") ;
    Water = mkCN (mkN "acqua") ;
    Coffee = mkCN (mkN "caff�") ;
--   Tea = mkCN (mkN "t�") ; ----

Cheese = mkCN (mkN "formaggio") ;
Fish = mkCN (mkN "pesce") ;
Pizza = mkCN (mkN "pizza") ;

Itash = mkAP (mkA "frasco") ;
Warm = mkAPA "caldo" ;
Italian = mkAPA "italiano" ;
Expensive = mkAPA "caro" ;
Delicious = mkAPA "delizioso" ;
Boring = mkAPA "noioso" ;

    Restaurant = mkCN (mkN "ristorante") ;
    Bar = mkCN (mkN "bar") ;
    Toilet = mkCN (mkN "bagno") ;

    Euro = mkCN (mkN "euro" "euro" masculine) ;
    Dollar = mkCN (mkN "dollar") ;
    Lei = mkCN (mkN "lei") ; ---- ?

    English = mkNP (mkPN "inglese") ;
    Finnish = mkNP (mkPN "finnico") ;
    Itanch = mkNP (mkPN "francese") ; 
    Romanian = mkNP (mkPN "romano") ;
    Swedish = mkNP (mkPN "svedese") ;

    AWant p obj = {s = \\r => mkCl (p.s ! r) want_V2 obj} ;
    ALike p item = {s = \\r => mkCl item (mkV2 (mkV (piacere_64 "piacere")) dative) (p.s ! r)} ;
    AHave p kind = {s = \\r => mkCl (p.s ! r) have_V2 (mkNP kind)} ;
    ASpeak p lang = {s = \\r => mkCl (p.s ! r) (mkV2 (mkV "parlare")) lang} ;
    ALove p q = {s = \\r => mkCl (p.s ! r) (mkV2 (mkV "amare")) (q.s ! r)} ;

oper
mkAPA : (_ : Str) -> AP = \x -> mkAP (mkA x) ;

}
