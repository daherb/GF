--# -path=.:../romance:../abstract:../common:prelude

instance DiffFre of DiffRomance = open CommonRomance, PhonoFre, Prelude in {

  flags optimize=noexpand ;
--  flags optimize=all ;

  param 
    Prep = P_de | P_a ;
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

    possCase = \_,_,c -> prepCase c ;

    partitive = \g,c -> case c of {
      CPrep P_de => elisDe ;
      _ => prepCase c ++ artDef g Sg (CPrep P_de)
      } ;

    conjunctCase : NPForm -> NPForm = \c -> case c of {
      Aton k => Ton k ;
      _ => c
      } ;

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

----    pronArg = pronArgGen Neg ; --- takes more space and time

    pronArg : Number -> Person -> CAgr -> CAgr -> Str * Str = \n,p,acc,dat ->
      let 
        pacc = case acc of {
          CRefl => case p of {
            P3 => elision "s" ;  --- use of reflPron incred. expensive
            _  => argPron Fem n p Acc
            } ;
          CPron a => argPron a.g a.n a.p Acc ;
          _ => []
          } ;
       in
       case dat of {
          CPron a => let pdat = argPron a.g a.n a.p dative in case a.p of {
            P3 => <pacc ++ pdat,[]> ;
            _  => <pdat ++ pacc,[]>
            } ;
          _ => <pacc, []>
          } ;


-- Positive polarity is used in the imperative: stressed for 1st and
-- 2nd persons.

    pronArgGen : Polarity -> Number -> Person -> CAgr -> CAgr -> Str * Str = \b,n,p,acc,dat ->
      let 
        cas : Person -> Case -> Case = \pr,c -> case <pr,b> of {
          <P1 | P2, Pos> => CPrep P_de ; --- encoding in argPron
          _ => c
          } ;
        pacc = case acc of {
          CRefl => case p of {
            P3 => elision "s" ;  --- use of reflPron incred. expensive
            _  => argPron Fem n p (cas p Acc)
            } ;
          CPron a => argPron a.g a.n a.p (cas a.p Acc) ;
          _ => []
          } ;
        pdat = case dat of {
          CPron a => argPron a.g a.n a.p (cas a.p dative) ;
          _ => []
          } ;
       in
       case dat of {
          CPron {p = P3} => <pacc ++ pdat,[]> ;
          _ => <pdat ++ pacc, []>
          } ;

    mkImperative p vp = {
      s = \\pol,aag => 
        let 
          agr   = aag ** {p = p} ;
          verb  = (vp.s ! VPImperat).fin ! agr ;
          neg   = vp.neg ! pol ;
          clpr  = pronArgGen pol agr.n agr.p vp.clAcc vp.clDat ;
          compl = neg.p2 ++ clpr.p2 ++ vp.comp ! agr ++ vp.ext ! pol
        in
        case pol of {
          Pos => verb ++ clpr.p1 ++ compl ;
          Neg => neg.p1 ++ clpr.p1 ++ verb ++ compl
          } 
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

    reflPron : Number -> Person -> Case -> Str = \n,p,c ->
      let pron = argPron Fem n p c in
      case <p,c> of {
        <P3,  Acc | CPrep P_a> => elision "s" ;
        <P3, _> => prepCase c ++ "soi" ;
        _ => pron
        } ;

    argPron : Gender -> Number -> Person -> Case -> Str = 
      let 
        cases : (x,y : Str) -> Case -> Str = \me,moi,c -> case c of {
          Acc | CPrep P_a => me ;
          _ => moi
          } ;
        cases3 : (x,y,z : Str) -> Case -> Str = \les,leur,eux,c -> case c of {
          Acc => les ;
          CPrep P_a => leur ;
          _ => eux
          } ;
      in 
      \g,n,p -> case <g,n,p> of { 
        <_,Sg,P1> => cases (elision "m") "moi" ;
        <_,Sg,P2> => cases (elision "t") "toi" ;
        <_,Pl,P1> => \_ -> "nous" ;
        <_,Pl,P2> => \_ -> "vous" ;
        <Fem,Sg,P3> => cases3 elisLa "lui" "elle" ;
        <_,Sg,P3> => cases3 (elision "l") "lui" "lui" ;
        <Fem,Pl,P3> => cases3 "les" "leur" "elles" ;
        <_,Pl,P3> => cases3 "les" "leur" "eux"
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
