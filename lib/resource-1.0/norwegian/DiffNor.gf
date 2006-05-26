instance DiffNor of DiffScand = open CommonScand, Prelude in {

-- Parameters.

  param
    Gender = Utr Sex | Neutr ;
    Sex    = Masc | Fem ;

  oper
    utrum = Utr Masc ; 
    neutrum = Neutr ;

    gennum : Gender -> Number -> GenNum = \g,n ->
      case <g,n> of {
        <Utr _,Sg> => SgUtr ;
        <Neutr,Sg> => SgNeutr ;
        _  => Plg
        } ;

    detDef : Species = Indef ;

    Verb : Type = {
      s : VForm => Str ;
      part : Str ;
      vtype : VType
      } ;

    hasAuxBe _ = False ;

-- Strings.

    conjThat = "at" ;
    conjThan = "enn" ;
    conjAnd = "og" ;
    infMark  = "�" ;

    subjIf = "hvis" ;

    artIndef : Gender => Str = table {
      Utr Masc => "en" ;
      Utr Fem  => "ei" ;
      Neutr    => "et"
      } ;

    verbHave = 
      mkVerb "ha" "har" "ha" "hadde" "hatt" nonExist nonExist nonExist 
      ** noPart ;
    verbBe = 
      mkVerb "v�re" "er" "var" "var" "v�rt" "v�ren" "v�ret" "v�rne" 
      ** noPart ;
    verbBecome = 
      mkVerb "bli" "blir" "bli" "ble" "blitt" "bliven" "blivet" "blivne" 
      ** noPart ;

    -- auxiliary
    noPart = {part = []} ;

    auxFut = "vil" ;      -- "skal" in ExtNor
    auxCond = "ville" ;

    negation : Polarity => Str = table {
      Pos => [] ;
      Neg => "ikke"
      } ;

    genderForms : (x1,x2 : Str) -> Gender => Str = \all,allt -> 
      table {
        Utr _ => all ;
        Neutr => allt
        } ;

    relPron : GenNum => RCase => Str = \\gn,c => case c of {
      RNom  => "som" ;
      RGen  => "hvis" ;
      RPrep => gennumForms "hvilken" "hvilket" "hvilke" ! gn
      } ;

    pronSuch = gennumForms "s�dan" "s�dant" "s�danne" ;

    reflPron : Agr -> Str = \a -> case a of {
      {gn = Plg ; p = P1} => "oss" ;
      {gn = Plg ; p = P2} => "jer" ;
      {p = P1} => "meg" ;
      {p = P2} => "deg" ;
      {p = P3} => "seg"
      } ;

}
