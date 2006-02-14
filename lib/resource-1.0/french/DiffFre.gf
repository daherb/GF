--# -path=.:../romance:../abstract:../common:prelude

instance DiffFre of DiffRomance = open CommonRomance, PhonoFre, Prelude in {

  param 
    Prep = P_de | P_a ;
    NPForm = Ton Case | Aton Case | Poss {g : Gender ; n : Number} ; --- AAgr
    VType = VHabere | VEsse | VRefl ;

  oper
    dative   : Case = CPrep P_a ;
    genitive : Case = CPrep P_de ;

    prepCase : Case -> Str = \c -> case c of {
      Nom => [] ;
      Acc => [] ; 
      CPrep P_a => "�" ;
      CPrep P_de => elisDe
      } ;

    artDef : Gender -> Number -> Case -> Str = \g,n,c ->
      case <g,n,c> of {
        <Masc,Sg, CPrep P_de> => pre {"du" ; ["de l'"] / voyelle} ;
        <Masc,Sg, CPrep P_a>  => pre {"au" ; ["� l'"]  / voyelle} ;
        <Masc,Sg, _>    => elisLe ;
        <Fem, Sg, _>    => prepCase c ++ elisLa ;
        <_,   Pl, CPrep P_de> => "des" ;
        <_,   Pl, CPrep P_a>  => "aux" ;
        <_,   Pl, _ >   => "les"
        } ;

-- In these two, "de de/du/des" becomes "de".

    artIndef = \g,n,c -> case <n,c> of {
      <Sg,_>   => prepCase c ++ genForms "un" "une" ! g ;
      <Pl,CPrep P_de> => elisDe ;
      _        => prepCase c ++ "des"
      } ;

    partitive = \g,c -> case c of {
      CPrep P_de => elisDe ;
      _ => prepCase c ++ artDef g Sg (CPrep P_de)
      } ;

    conjunctCase : NPForm -> NPForm = \c -> c ;

    auxVerb : VType -> (VF => Str) = \vtyp -> case vtyp of {
      VHabere => avoir_V.s ;
      _ => copula.s
      } ;

    partAgr : VType -> VPAgr = \vtyp -> case vtyp of {
      VHabere => vpAgrNone ;
      _ => VPAgrSubj
      } ;

    vpAgrClit : Agr -> VPAgr = \a ->
      VPAgrClit (aagr a.g a.n) ; --- subty

    placeNewClitic = \ci,c,pro,isc,old ->
      let new = if_then_Str isc (pro.s ! Aton c) [] 
      in
      case pro.a.p of {
        P1 | P2 => new ++ old ;
        _ => old ++ new
        } ;

    negation : Polarity => (Str * Str) = table {
      Pos => <[],[]> ;
      Neg => <elisNe,"pas">
      } ;

    conjThan = elisQue ;
    conjThat = elisQue ;

    clitInf cli inf = cli ++ inf ;

    relPron : Bool => AAgr => Case => Str = \\b,a,c => 
      let
        lequel = artDef a.g a.n c + quelPron ! a
      in
      case b of {
      False => case c of {
        Nom => "qui" ;
        Acc => elisQue ;
        CPrep P_de => "dont" ;
        _ => lequel
        } ;
      _   => lequel
      } ;

    pronSuch : AAgr => Str = aagrForms "tel" "telle" "tels" "telles" ;

    quelPron : AAgr => Str = aagrForms "quel" "quelle" "quels" "quelles" ;

    partQIndir = elision "c" ;

    reflPron : Number => Person => Case => Str = 
      let 
        cases : (x,y : Str) -> (Case => Str) = \me,moi -> table {
          Acc | CPrep P_a => me ;
          _ => moi
          } ;
      in 
      \\n,p => case <n,p> of { 
        <Sg,P1> => cases (elision "m") "moi" ;
        <Sg,P2> => cases (elision "t") "toi" ;
        <Pl,P1> => \\_ => "nous" ;
        <Pl,P2> => \\_ => "vous" ;
        _ => cases (elision "s") "soi"
        } ;

    vRefl   : VType = VRefl ;
    isVRefl : VType -> Bool = \ty -> case ty of {
      VRefl => True ;
      _ => False
      } ;

    auxPassive : Verb = copula ;

    copula : Verb = {s = table VF ["�tre";"suis";"es";"est";"sommes";"�tes";"sont";"sois";"sois";"soit";"soyons";"soyez";"soient";"�tais";"�tais";"�tait";"�tions";"�tiez";"�taient";"fusse";"fusses";"f�t";"fussions";"fussiez";"fussent";"fus";"fus";"fut";"f�mes";"f�tes";"furent";"serai";"seras";"sera";"serons";"serez";"seront";"serais";"serais";"serait";"serions";"seriez";"seraient";"sois";"soyons";"soyez";"�t�";"�t�s";"�t�e";"�t�es";"�tant"]; vtyp=VHabere} ;

    avoir_V : Verb = {s=table VF ["avoir";"ai";"as";"a";"avons";"avez";"ont";"aie";"aies";"ait";"ayons";"ayez";"aient";"avais";"avais";"avait";"avions";"aviez";"avaient";"eusse";"eusses";"e�t";"eussions";"eussiez";"eussent";"eus";"eus";"eut";"e�mes";"e�tes";"eurent";"aurai";"auras";"aura";"aurons";"aurez";"auront";"aurais";"aurais";"aurait";"aurions";"auriez";"auraient";"aie";"ayons";"ayez";"eu";"eus";"eue";"eues";"ayant"];vtyp=VHabere};

}
