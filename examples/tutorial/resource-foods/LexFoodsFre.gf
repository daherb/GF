--# -path=.:../foods:present:prelude

instance LexFoodsFre of LexFoods = open SyntaxFre,ParadigmsFre in {
  oper
    wine_N = mkN "vin" ;
    pizza_N = mkN "pizza" feminine ;
    cheese_N = mkN "fromage" masculine ;
    fish_N = mkN "poisson" ;
    fresh_A = mkA "frais" "fra�che" "frais" "fra�ches";
    warm_A = mkA "chaud" ;
    italian_A = mkA "italien" ;
    expensive_A = mkA "cher" ;
    delicious_A = mkA "d�licieux" ;
    boring_A = mkA "ennuyeux" ;
}
