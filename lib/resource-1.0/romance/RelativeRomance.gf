incomplete concrete RelativeRomance of Relative = 
  CatRomance ** open DiffRomance, ResRomance in {

  flags optimize=all_subs ;

  lin

    RelCl cl = {
      s = \\t,a,p,ag => pronSuch ! ag.gn ++ conjThat ++ cl.s ! t ! a ! p ! Sub
      } ;

    RelVP rp vp = {
      s = \\t,ant,b,ag => 
        let 
          agr = case rp.a of {
            RNoAg => ag ;
            RAg a => a
            } ;
          cl = mkClause (rp.s ! ag.gn ! RNom) agr vp
        in
        cl.s ! t ! ant ! b ! Sub
      } ;

--- We make this easy by using "som" and preposition stranding. It would be
--- a proble to determine whether $slash$ takes a direct object, since
--- $slash.c2$ is defined to be just a string. 
--
-- The empty relative is left to $ExtRomance$.

    RelSlash rp slash = {
      s = \\t,a,p,ag => 
          rp.s ! ag.gn ! RNom ++ slash.s ! t ! a ! p ! Sub ++ slash.c2
      } ;

--- The case here could be genitive.

    FunRP p np rp = {
      s = \\gn,c => np.s ! nominative ++ p.s ++ rp.s ! gn ! RPrep ;
      a = RAg np.a
      } ;

    IdRP = {s = relPron ; a = RNoAg} ;

}
