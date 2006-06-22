instance DiffDan of DiffScand = open CommonScand, Prelude in {

-- Parameters.

  param
    Gender = Utr | Neutr ;

  oper
    utrum = Utr ; 
    neutrum = Neutr ;

    gennum : Gender -> Number -> GenNum = \g,n ->
      case <g,n> of {
        <Utr,  Sg> => SgUtr ;
        <Neutr,Sg> => SgNeutr ;
        _  => Plg
        } ;

    detDef : Species = Indef ;

    Verb : Type = {
      s : VForm => Str ;
      part : Str ;
      vtype : VType ;
      isVaere : Bool
      } ;

    hasAuxBe v = v.isVaere ;

-- Strings.

    conjThat = "at" ;
    conjThan = "end" ;
    conjAnd = "og" ;
    infMark  = "at" ;
    compMore = "mere" ;

    subjIf = "hvis" ;

    artIndef : Gender => Str = table {
      Utr   => "en" ;
      Neutr => "et"
      } ;

    verbHave = 
      mkVerb "have" "har" "hav" "havde" "haft" nonExist nonExist nonExist **
      {part = [] ; isVaere = False} ;
    verbBe = 
      mkVerb "v�re" "er" "var" "var" "v�ret" "v�ren" "v�ret" "v�rne" **
      {part = [] ; isVaere = False} ;
    verbBecome = 
      mkVerb "blive" "bliver" "bliv" "blev" "blevet" 
        "bliven" "blivet" "blivne"  **
      {part = [] ; isVaere = True} ;

    auxFut = "vil" ;      -- "skal" in ExtDan
    auxCond = "ville" ;

    negation : Polarity => Str = table {
      Pos => [] ;
      Neg => "ikke"
      } ;

    genderForms : (x1,x2 : Str) -> Gender => Str = \all,allt -> 
      table {
        Utr  => all ;
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
      {p = P1} => "mig" ;
      {p = P2} => "dig" ;
      {p = P3} => "sig"
      } ;

}
