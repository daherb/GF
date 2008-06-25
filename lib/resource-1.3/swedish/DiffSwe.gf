instance DiffSwe of DiffScand = open CommonScand, Prelude in {

-- Parameters.

  param
    Gender = Utr | Neutr ;

  oper
    utrum = Utr ; 
    neutrum = Neutr ;

    gennumN : Gender -> Number -> GenNum = \g,n -> Plg ; -----
    gennum : Gender -> Number -> GenNum = \g,n ->
{-
--- debugging Compute 9/11/2007
      case n of {
        Sg => case g of {
          Utr => SgUtr ;
          Neutr => SgNeutr
          } ;
        _  => Plg
        } ;
-}
      case <<g,n> : Gender * Number> of {
        <Utr,Sg> => SgUtr ;
        <Neutr,Sg> => SgNeutr ;
        _  => Plg
        } ;

    detDef : Species = Def ;

    Verb : Type = {
      s : VForm => Str ;
      part : Str ;
      vtype : VType
      } ;

    hasAuxBe _ = False ;


-- Strings.

    conjThat = "att" ;
    conjThan = "�n" ;
    conjAnd = "och" ;
    infMark  = "att" ;
    compMore = "mera" ;

    subjIf = "om" ;

    artIndef : Gender => Str = table {
      Utr => "en" ;
      Neutr => "ett"
      } ;

    verbHave = 
      mkVerb "ha" "har" "ha" "hade" "haft" "havd" "havt" "havda" ** noPart ;
    verbBe = 
      mkVerb "vara" "�r" "var" "var" "varit" "varen" "varet" "varna" 
      ** noPart ;
    verbBecome = 
      mkVerb "bli" "blir" "bli" "blev" "blivit" "bliven" "blivet" "blivna"
      ** noPart ;

    -- auxiliary
    noPart = {part = []} ;

    auxFut = "ska" ;      -- "skall" in ExtSwe
    auxCond = "skulle" ;

    negation : Polarity => Str = table {
      Pos => [] ;
      Neg => "inte"
      } ;

    genderForms : (x1,x2 : Str) -> Gender => Str = \all,allt -> 
      table {
        Utr => all ;
        Neutr => allt
        } ;

    relPron : GenNum => RCase => Str = \\gn,c => case c of {
      RNom  => "som" ;
      RGen  => "vars" ;
      RPrep => gennumForms "vilken" "vilket" "vilka" ! gn
      } ;

    pronSuch = gennumForms "s�dan" "s�dant" "s�dana" ;

    reflPron : Agr -> Str = \a -> case a of {
      {gn = Plg ; p = P1} => "oss" ;
      {gn = Plg ; p = P2} => "er" ;
      {p = P1} => "mig" ;
      {p = P2} => "dig" ;
      {p = P3} => "sig"
      } ;

}
