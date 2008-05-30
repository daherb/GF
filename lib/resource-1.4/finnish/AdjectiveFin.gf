concrete AdjectiveFin of Adjective = CatFin ** open ResFin, Prelude in {

  flags optimize=all_subs ; -- gfc size from 2864336 to 6786 - i.e. factor 422

  lin

    PositA  a = {
      s = \\_ => a.s ! Posit
      } ;
    ComparA a np = {
      s = \\isMod,af => case isMod of {
        True => np.s ! NPCase Part ++ a.s ! Compar ! af ;        -- minua isompi
        _    => a.s ! Compar ! af ++ "kuin" ++ np.s ! NPCase Nom -- isompi kuin min�
        } 
      } ;

-- $SuperlA$ belongs to determiner syntax in $Noun$.

    ComplA2 adj np = {
      s = \\isMod,af => 
          preOrPost isMod (appCompl True Pos adj.c2 np) (adj.s ! Posit ! af)
      } ;

    ReflA2 adj = {
      s = \\isMod,af => 
          preOrPost isMod 
            (appCompl True Pos adj.c2 (reflPron (agrP3 Sg))) (adj.s ! Posit ! af)
      } ;

    SentAP ap sc = {
      s = \\b,a => ap.s ! b ! a ++ sc.s
      } ;

    AdAP ada ap = {
      s = \\b,af => ada.s ++ ap.s ! b ! af
      } ;

    UseA2 a = a ;

}
