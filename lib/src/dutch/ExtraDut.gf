concrete ExtraDut of ExtraDutAbs = CatDut ** 
  open ResDut, Coordination, Prelude, IrregDut in 
{
--{
--
--  lincat
--    VPI   = {s : Bool => Str} ;
--    [VPI] = {s1,s2 : Bool => Str} ;
--  lin
--    BaseVPI = twoTable Bool ;
--    ConsVPI = consrTable Bool comma ;
--
--    MkVPI vp = {s = \\b => useInfVP b vp} ;
--    ConjVPI = conjunctDistrTable Bool ;
--
--    ComplVPIVV v vpi = 
--        insertInf (vpi.s ! v.isAux) (
--            predVGen v.isAux v) ; ----
--{-
--      insertExtrapos vpi.p3 (
--        insertInf vpi.p2 (
--          insertObj vpi.p1 (
--            predVGen v.isAux v))) ;
---}
--
--    PPzuAdv cn = {s = case cn.g of {
--      Masc | Neutr => "zum" ;
--      Fem => "zur"
--      } ++ cn.s ! adjfCase Weak Dat ! Sg ! Dat 
--    } ;
--
--    TImpfSubj  = {s = [] ; t = Past ; m = MConjunct} ;   --# notpresent
--
--    moegen_VV = auxVV m�gen_V ;
--
--} 


lin
    ICompAP ap = {s = \\_ => "hoe" ++ ap.s ! APred} ; 

    IAdvAdv adv = {s = "hoe" ++ adv.s} ;

}
