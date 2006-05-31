concrete RelativeEng of Relative = CatEng ** open ResEng in {

  flags optimize=all_subs ;

  lin

    RelCl cl = {
      s = \\t,a,p,_ => "such" ++ "that" ++ cl.s ! t ! a ! p ! ODir ; 
      c = Nom
      } ;

    RelVP rp vp = {
      s = \\t,ant,b,ag => 
        let 
          agr = case rp.a of {
            RNoAg => ag ;
            RAg a => a
            } ;
          cl = mkClause (rp.s ! RC Nom) agr vp
        in
        cl.s ! t ! ant ! b ! ODir ;
      c = Nom
      } ;

-- Preposition stranding: "that we are looking at". Pied-piping is
-- deferred to $ExtEng.gf$ ("at which we are looking").

    RelSlash rp slash = {
      s = \\t,a,p,_ => rp.s ! RC Acc ++ slash.s ! t ! a ! p ! ODir ++ slash.c2 ;
      c = Acc
      } ;

    FunRP p np rp = {
      s = \\c => np.s ! Acc ++ p.s ++ rp.s ! RPrep ;
      a = RAg np.a
      } ;

    IdRP = {
      s = table {
        RC Gen => "whose" ; 
        RC _   => "that" ;
        RPrep  => "which"
        } ;
      a = RNoAg
      } ;

}
