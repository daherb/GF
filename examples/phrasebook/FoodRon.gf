-- (c) 2009 Ramona Enache under LGPL

concrete FoodRon of Food = SentencesRon ** open
  SyntaxRon,
  ParadigmsRon in
{
flags coding=utf8 ;

lin

Wine = mkCN (mkN "vin" "vinuri" neuter) ;
Cheese = mkCN (mkN "br�nz�" "br�nzeturi" feminine) ;
Fish = mkCN (mkN "pe�te" "pe�ti" masculine) ;
Pizza = mkCN (mkN "pizza" "pizze" feminine) ;

Fresh = mkAPA "proasp�t" "proasp�t�" "proaspe�i" "proaspete" ;
Warm = mkAPA "cald" "cald�" "calzi" "calde" ;
Italian = mkAPA "italian" "italian�" "italieni" "italiene" ;
Expensive = mkAPA "scump" "scump�" "scumpi" "scumpe" ;
Delicious = mkAPA "delicios" "delcioas�" "delicio�i" "delicioase" ;
Boring = mkAPA "plictisitor" "plictisitoare" "plictisitori" "plictisitoare" ;

oper
mkAPA : (_,_,_,_ : Str) -> AP = \x,y,z,u -> mkAP (mkA x y z u) ;

}
