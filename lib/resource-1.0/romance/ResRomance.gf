--1 Romance auxiliary operations.
--

interface ResRomance = DiffRomance ** open CommonRomance, Prelude in {

flags optimize=all ;

--2 Constants uniformly defined in terms of language-dependent constants

oper

  nominative : Case = Nom ;
  accusative : Case = Acc ;

  Pronoun = {s : NPForm => Str ; a : Agr ; hasClit : Bool} ;

  Compl : Type = {s : Str ; c : Case ; isDir : Bool} ;

  complAcc : Compl = {s = [] ; c = accusative ; isDir = True} ;
  complGen : Compl = {s = [] ; c = genitive ; isDir = False} ;
  complDat : Compl = {s = [] ; c = dative ; isDir = True} ;

  pn2np : {s : Str ; g : Gender} -> Pronoun = \pn -> {
      s = \\c => prepCase (npform2case c) ++ pn.s ; 
      a = agrP3 pn.g Sg ;
      hasClit = False
      } ;

  npform2case : NPForm -> Case = \p -> case p of {
    Ton  x => x ;
    Poss _ => genitive ;
    Aton x => x ;
    _      => dative ---- Ita PreClit
    } ;

  case2npform : Case -> NPForm = \c -> case c of {
    Nom => Ton Nom ;
    Acc => Ton Acc ;
    _   => Ton c
    } ;

-- Pronouns in $NP$ lists are always in stressed forms.

  stressedCase : NPForm -> NPForm = \c -> case c of {
    Aton k => Ton k ;
    _ => c
    } ;

  appCompl : Compl -> (NPForm => Str) -> Str = \comp,np ->
    comp.s ++ np ! Ton comp.c ;

  predV : Verb -> VP = \verb -> 
    let
      vfin  : TMood -> Agr -> Str = \tm,a -> verb.s ! VFin tm a.n a.p ;
      vpart : AAgr -> Str = \a -> verb.s ! VPart a.g a.n ;
      vinf  = verb.s ! VInfin ;

      typ = verb.vtyp ;
      aux = auxVerb typ ;

      habet  : TMood -> Agr -> Str = \tm,a -> aux ! VFin tm a.n a.p ;
      habere : Str = aux ! VInfin ;

      vf : (Agr -> Str) -> (AAgr -> Str) -> {
          fin : Agr => Str ; 
          inf : AAgr => Str
        } = 
        \fin,inf -> {
          fin = \\a => fin a ; 
          inf = \\a => inf a
        } ;

    in {
    s = table {
      VPFinite t Simul => vf (vfin t) (\_ -> []) ;
      VPFinite t Anter => vf (habet t) vpart ; 
      VPImperat        => vf (\_ -> verb.s ! VImper SgP2) (\_ -> []) ; ----
      VPInfinit Simul  => vf (\_ -> []) (\_ -> vinf) ;
      VPInfinit Anter  => vf (\_ -> []) (\a -> habere ++ vpart a)
      } ;
    agr    = partAgr typ ;
    neg    = negation ;
    clAcc  = case isVRefl typ of {
          True => CRefl ;
          _    => CNone
          } ;
    clDat  = CNone ; --- no dative refls
    clit2  = [] ;
    comp   = \\a => [] ;
    ext    = \\p => []
    } ;

  insertObject : Compl -> Pronoun -> VP -> VP = \c,np,vp -> 
    let
      vpacc = vp.clAcc ; 
      vpdat = vp.clDat ;
      vpagr = vp.agr ;
      npa   = np.a ;
      noNewClit = <vpacc, vpdat, appCompl c np.s, vpagr> ;

      cc : CAgr * CAgr * Str * VPAgr = case <np.hasClit,c.isDir> of {
        <True,True> => case c.c of {
          Acc => <CPron npa,  vpdat,   [], vpAgrClit npa> ;
          _   => <vpacc,    CPron npa, [], vpagr> -- must be dat
          } ;
        _   => noNewClit
        } ;

    in {
      s     = vp.s ;
      agr   = cc.p4 ;
      clAcc = cc.p1 ;
      clDat = cc.p2 ;
      clit2 = vp.clit2 ;
      neg   = vp.neg ;
      comp  = \\a => vp.comp ! a ++ cc.p3 ;
      ext   = vp.ext ;
    } ;

  insertComplement : (Agr => Str) -> VP -> VP = \co,vp -> { 
    s     = vp.s ;
    agr   = vp.agr ;
    clAcc = vp.clAcc ; 
    clDat = vp.clDat ; 
    clit2 = vp.clit2 ; 
    neg   = vp.neg ;
    comp  = \\a => vp.comp ! a ++ co ! a ;
    ext   = vp.ext ;
    } ;

  insertAdv : Str -> VP -> VP = \co,vp -> { 
    s     = vp.s ;
    agr   = vp.agr ;
    clAcc = vp.clAcc ; 
    clDat = vp.clDat ; 
    clit2 = vp.clit2 ; 
    neg   = vp.neg ;
    comp  = \\a => vp.comp ! a ++ co ;
    ext   = vp.ext ;
    } ;

  insertExtrapos : (Polarity => Str) -> VP -> VP = \co,vp -> { 
    s     = vp.s ;
    agr   = vp.agr ;
    clAcc = vp.clAcc ; 
    clDat = vp.clDat ; 
    clit2 = vp.clit2 ; 
    neg   = vp.neg ;
    comp  = vp.comp ;
    ext   = \\p => vp.ext ! p ++ co ! p ;
    } ;

  mkClause : Str -> Agr -> VP -> 
    {s : Tense => Anteriority => Polarity => Mood => Str} =
    \subj,agr,vp -> {
      s = \\t,a,b,m => 
        let 
          tm = case t of {
            Pres => VPres m ;
            Past => VImperf m ;
            Fut  => VFut ;
            Cond => VCondit
            } ;
          vps   = vp.s ! VPFinite tm a ;
          verb  = vps.fin ! agr ;
          inf   = vps.inf ! (appVPAgr vp.agr (aagr agr.g agr.n)) ; --- subtype bug
          neg   = vp.neg ! b ;
          clpr  = pronArg agr.n agr.p vp.clAcc vp.clDat ;
          compl = clpr.p2 ++ vp.comp ! agr ++ vp.ext ! b
        in
        subj ++ neg.p1 ++ clpr.p1 ++ verb ++ neg.p2 ++ inf ++ compl
    } ;

  infVP : VP -> Agr -> Str = \vp,agr ->
      let
        inf  = (vp.s ! VPInfinit Simul).inf ! (aagr agr.g agr.n) ;
        neg  = vp.neg ! Pos ; --- Neg not in API
        clpr = pronArg agr.n agr.p vp.clAcc vp.clDat ;
        obj  = clpr.p2 ++ vp.comp ! agr
      in
      clitInf clpr.p1 inf ++ obj ;

}

-- insertObject:
-- p -cat=Cl -tr "la femme te l' envoie"
-- PredVP (DetCN (DetSg DefSg NoOrd) (UseN woman_N)) 
--  (ComplV3 send_V3 (UsePron he_Pron) (UsePron thou_Pron))
-- la femme te l' a envoy�
--
-- p -cat=Cl -tr "la femme te lui envoie"
-- PredVP (DetCN (DetSg DefSg NoOrd) (UseN woman_N)) 
--   (ComplV3 send_V3 (UsePron thou_Pron) (UsePron he_Pron))
-- la femme te lui a envoy�e
