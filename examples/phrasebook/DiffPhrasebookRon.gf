instance DiffPhrasebookRon of DiffPhrasebook = open 
  SyntaxRon,
  BeschRon,
  ParadigmsRon 
in {

flags coding = utf8 ;

oper
  want_V2 = dirV2 (lin V want_VV)  ;  -- mkVV (v_besch74 "vrea")
  like_V2 = dirV2 (v_besch71 "plăcea") ;

  cost_V2 = dirV2(v_besch18 "costa") ;

  cost_V  = v_besch18 "costa" ;

}
