instance DiffPhrasebookFre of DiffPhrasebook = open 
  SyntaxFre,
  IrregFre,
  ParadigmsFre 
in {

flags coding = utf8 ;

oper
  want_V2 = vouloir_V2 ;
  like_V2 = mkV2 (mkV "aimer") ;

  cost_V2 = mkV2 (mkV "co�ter") ;
  cost_V  = mkV "co�ter" ;

}
