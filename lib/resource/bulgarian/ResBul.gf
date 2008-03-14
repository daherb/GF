--# -path=.:../abstract:../common:../../prelude

--1 Bulgarian auxiliary operations.

-- This module contains operations that are needed to make the
-- resource syntax work. To define everything that is needed to
-- implement $Test$, it moreover contains regular lexical
-- patterns needed for $Lex$.

resource ResBul = ParamX ** open Prelude in {

  flags optimize=all ;

-- Some parameters, such as $Number$, are inherited from $ParamX$.

--2 For $Noun$

-- This is the worst-case $Case$ needed for pronouns.

  param
    Role = RSubj | RObj Case | RVoc ;
    Case = Acc | Dat;

    NForm = 
        NF Number Species
      | NFSgDefNom
      | NFPlCount
      | NFVocative
      ;

    GenNum = GSg Gender | GPl ;

-- Agreement of $NP$ is a record. We'll add $Gender$ later.

  oper
    Agr = {gn : GenNum ; p : Person} ;

  param
    Gender = Masc | Fem | Neut ;
    
    Species = Indef | Def ;
 
-- The plural never makes a gender distinction.

--2 For $Verb$

    VForm = 
       VPres      Number Person
     | VAorist    Number Person
     | VImperfect Number Person
     | VPerfect    AForm
     | VPluPerfect AForm
     | VPassive    AForm
     | VPresPart   AForm
     | VImperative Number
     | VGerund
     ;
     
    VType =
       VNormal
     | VMedial  Case
     | VPhrasal Case
     ;

-- The order of sentence is needed already in $VP$.

    Order = Main | Inv | Quest ;

--2 For $Adjective$

    AForm = 
       ASg Gender Species
     | ASgMascDefNom
     | APl Species
     ;

--2 For $Numeral$

    DGender =
       DMasc
     | DMascPersonal
     | DFem
     | DNeut
     ;
    
    DGenderSpecies = 
       DMascIndef
     | DMascDef
     | DMascDefNom
     | DMascPersonalIndef
     | DMascPersonalDef
     | DMascPersonalDefNom
     | DFemIndef
     | DFemDef
     | DNeutIndef
     | DNeutDef
     ;

    CardOrd = NCard DGenderSpecies | NOrd AForm ;
    DForm = unit | teen | ten | hundred ;

--2 Transformations between parameter types

  oper
    agrP3 : GenNum -> Agr = \gn -> 
      {gn = gn; p = P3} ;

    conjGenNum : GenNum -> GenNum -> GenNum = \a,b ->
      case <a,b> of {
        <GSg _,GSg g> => GSg g ;
        _             => GPl
    } ;

    conjAgr : Agr -> Agr -> Agr = \a,b -> {
      gn = conjGenNum a.gn b.gn ;
      p  = conjPerson a.p b.p
      } ;

    gennum : DGender -> Number -> GenNum = \g,n ->
      case n of {
        Sg => GSg (case g of {
                     DMasc         => Masc ;
                     DMascPersonal => Masc ;
                     DFem          => Fem ;
                     DNeut         => Neut
                   }) ;
        Pl => GPl
        } ;

    numGenNum : GenNum -> Number = \gn -> 
      case gn of {
        GSg _  => Sg ;
        GPl    => Pl
      } ;

    aform : GenNum -> Species -> Role -> AForm = \gn,spec,role -> 
      case gn of {
        GSg g  => case <g,spec,role> of {
                    <Masc,Def,RSubj> => ASgMascDefNom ;
                    _                => ASg g spec
                  } ;
        GPl    => APl spec
      } ;

    dgenderSpecies : DGender -> Species -> Role -> DGenderSpecies =
      \g,spec,role -> case <g,spec> of {
                        <DMasc,Indef> => DMascIndef ;
                        <DMasc,Def>   => case role of {
                                           RSubj => DMascDefNom ;
                                           _     => DMascDef
                                         } ;
                        <DMascPersonal,Indef> => DMascPersonalIndef ;
                        <DMascPersonal,Def>   => case role of {
                                                   RSubj => DMascPersonalDefNom ;
                                                   _     => DMascPersonalDef
                                                 } ;
                        <DFem ,Indef> => DFemIndef ;
                        <DFem ,Def>   => DFemDef ;
                        <DNeut,Indef> => DNeutIndef ;
                        <DNeut,Def>   => DNeutDef
                      } ;

    nform2aform : NForm -> DGender -> AForm
      = \nf,g -> case nf of {
                   NF n spec  => aform (gennum g n) spec (RObj Acc) ;
                   NFSgDefNom => aform (gennum g Sg) Def RSubj ;
                   NFPlCount  => APl Indef ;
                   NFVocative => aform (gennum g Sg) Indef (RObj Acc)
                 } ;

    indefNForm : NForm -> NForm
      = \nf -> case nf of {
                 NF n spec  => NF n  Indef ;
                 NFSgDefNom => NF Sg Indef ;
                 NFPlCount  => NFPlCount ;
                 NFVocative => NFVocative
               } ;

    numNForm : NForm -> Number
      = \nf -> case nf of {
                 NF n spec  => n ;
                 NFSgDefNom => Sg ;
                 NFPlCount  => Pl ;
                 NFVocative => Sg
               } ;
      
  oper
-- For $Verb$.
    Verb : Type = {
      s  : VForm => Str ;
      vtype : VType
    } ;

    VP : Type = {
      s   : Tense => Anteriority => Polarity => Agr => Bool => Str ;
      imp : Polarity => Number => Str ;
      ad  : Bool => Str ;          -- sentential adverb
      s2  : Agr => Str ;
      subjRole : Role
    } ;

    predV : Verb -> VP =
      \verb -> 
        { s = \\t,a,p,agr,q => let 
                                 clitic = case verb.vtype of {
                                               VNormal    => {s=[]; agr=agr} ;
                                               VMedial c  => {s=reflClitics ! c; agr=agr} ;
                                               VPhrasal c => {s=personalClitics ! c ! agr.gn ! agr.p; agr={gn=GSg Neut; p=P3}}
                                             } ;

                                 present = verb.s ! (VPres   (numGenNum clitic.agr.gn) clitic.agr.p) ;
                                 aorist  = verb.s ! (VAorist (numGenNum clitic.agr.gn) clitic.agr.p) ;
                                 perfect = verb.s ! (VPerfect (aform clitic.agr.gn Indef (RObj Acc))) ;
                                 
                                 auxPres    = auxBe clitic.s ! VPres (numGenNum clitic.agr.gn) clitic.agr.p ;
                                 auxAorist  = auxBe clitic.s ! VAorist (numGenNum clitic.agr.gn) clitic.agr.p ;
                                 auxPerfect = auxBe clitic.s ! VPerfect (aform clitic.agr.gn Indef (RObj Acc)) ;
                                 auxCondS   = auxWould clitic.s ! VAorist (numGenNum clitic.agr.gn) clitic.agr.p ;
                                 auxCondA   = auxCondS ++
                                              auxBe [] ! VPerfect (aform clitic.agr.gn Indef (RObj Acc)) ;

                                 verbs : {aux:Str; main:Str}
                                       = case <t,a> of {
                                           <Pres,Simul> => {aux=clitic.s; main=present} ;
                                           <Pres,Anter> => {aux=auxPres; main=perfect} ;
                                           <Past,Simul> => {aux=clitic.s; main=aorist} ;
                                           <Past,Anter> => {aux=auxAorist; main=perfect} ;
                                           <Fut, Simul> => {aux=clitic.s; main=present} ;
                                           <Fut, Anter> => {aux=auxPres; main=perfect} ;
                                           <Cond,Simul> => {aux=auxCondS; main=perfect} ;
                                           <Cond,Anter> => {aux=auxCondA; main=perfect}
                                         } ;

                                 li = case q of {True => "��"; False => []} ;
                                 aux = case p of {
                                         Pos => case t of {
                                                  Fut => {s1="��"++verbs.aux; s2=li} ;
                                                  _   => case q of {True  => {s1=[]; s2="��"++verbs.aux};
                                                                    False => {s1=verbs.aux; s2=[]}}
                                                } ;
                                         Neg => case t of {
                                                  Fut => {s1="��"++"��"++verbs.aux; s2=li} ;
                                                  _   => case q of {True  => {s1="��"++verbs.aux; s2="��"};
                                                                    False => {s1="��"++verbs.aux; s2=[]}}
                                                }
                                       }

                             in aux.s1 ++ verbs.main ++ aux.s2;
             imp = \\p,n => let ne = case p of {Pos => []; Neg => "��"} ;
                            in ne ++ verb.s ! VImperative n ;
             ad = \\_ => [] ;
             s2 = \\_ => [] ;
             subjRole = case verb.vtype of {
                          VNormal    => RSubj ;
                          VMedial  _ => RSubj ;
                          VPhrasal c => RObj c
                        }
           } ;

    insertObj : (Agr => Str) -> VP -> VP = \obj,vp -> {
      s   = vp.s ;
      imp = vp.imp ;
      ad  = vp.ad ;
      s2 = \\a => vp.s2 ! a ++ obj ! a ;
      subjRole = vp.subjRole
      } ;

    auxBe : Str -> VForm => Str = \se ->
      table {
        VPres      Sg P1  => "���" ++ se ; 
        VPres      Sg P2  => "��" ++ se ;
        VPres      Sg P3  => se ++ "�" ;
        VPres      Pl P1  => "���" ++ se ; 
        VPres      Pl P2  => "���" ++ se ;
        VPres      Pl P3  => "��" ++ se ;
        VAorist    Sg P1  => "���" ++ se ; 
        VAorist    Sg P2  => "����" ++ se ;
        VAorist    Sg P3  => se ++ "����" ;
        VAorist    Pl P1  => "�����" ++ se ; 
        VAorist    Pl P2  => "�����" ++ se ;
        VAorist    Pl P3  => "����" ++ se ;
        VImperfect Sg P1  => "���" ++ se ; 
        VImperfect Sg _   => "����" ++ se ;
        VImperfect Pl P1  => "�����" ++ se ; 
        VImperfect Pl P2  => "�����" ++ se ;
        VImperfect Pl P3  => "����" ++ se ;
        VPerfect    aform => regAdjective "���" ! aform ++ se ;
        VPluPerfect aform => regAdjective "���" ! aform ++ se ;
        VPassive    aform => regAdjective "�����" ! aform ++ se ;
        VPresPart   aform => regAdjective "�����" ! aform ++ se ;
        VImperative Sg    => "����" ++ se ;
        VImperative Pl    => "������" ++ se ;
        VGerund           => "�������" ++ se
      } ;

    auxWould : Str -> VForm => Str = \se ->
      table {
        VPres      Sg P1  => "����" ++ se ; 
        VPres      Sg P2  => "�����" ++ se ;
        VPres      Sg P3  => se ++ "����" ; 
        VPres      Pl P1  => "�����" ++ se ; 
        VPres      Pl P2  => "������" ++ se ;
        VPres      Pl P3  => "�����" ++ se ;
        VAorist    Sg P1  => "���" ++ se ; 
        VAorist    Sg _   => "��" ++ se ;
        VAorist    Pl P1  => "�����" ++ se ; 
        VAorist    Pl P2  => "�����" ++ se ;
        VAorist    Pl P3  => "����" ++ se ;
        VImperfect Sg P1  => "�����" ++ se ; 
        VImperfect Sg _   => "������" ++ se ;
        VImperfect Pl P1  => "�������" ++ se ; 
        VImperfect Pl P2  => "�������" ++ se ;
        VImperfect Pl P3  => "������" ++ se ;
        VPerfect    aform => regAdjective "���" ! aform ++ se ;
        VPluPerfect aform => regAdjective "�����" ! aform ++ se ;
        VPassive    aform => regAdjective "�����" ! aform ++ se ;
        VPresPart   aform => regAdjective "�����" ! aform ++ se ;
        VImperative Sg    => "����" ++ se ;
        VImperative Pl    => "������" ++ se ;
        VGerund           => "�������" ++ se
      } ;

    verbBe : Verb = {s=auxBe []; vtype=VNormal} ;

    reflClitics : Case => Str = table {Acc => "��"; Dat => "��"} ;

    personalClitics : Case => GenNum => Person => Str =
      table {
        Acc => table {
                 GSg g => table {
                            P1 => "��" ;
                            P2 => "��" ;
                            P3 => case g of {
                                    Masc => "��" ;
                                    Fem  => "�" ;
                                    Neut => "��"
                                  }
                          } ;
                 GPl   => table {
                            P1 => "��" ;
                            P2 => "��" ;
                            P3 => "��"
                          }
               } ;
        Dat => table {
                 GSg g => table {
                            P1 => "��" ;
                            P2 => "��" ;
                            P3 => case g of {
                                    Masc => "��" ;
                                    Fem  => "�" ;
                                    Neut => "��"
                                  }
                          } ;
                 GPl   => table {
                            P1     => "��" ;
                            P2     => "��" ;
                            P3     => "��"
                          }
               }
      } ;

    ia2e : Str -> Str =           -- to be used when the next syllable has vowel different from "�","�","�" or "�"
      \s -> case s of {
              x@(_*+_) + "�" + y@(("�"|"�"|"�"|"�"|"�"|"�"|"�"|"�"|"�"|"�"|"�"|"�"|"�"|"�"|"�"|"�"|"�"|"�"|"�"|"�")*)
                => x+"e"+y;
              _ => s
            };

  regAdjective : Str -> AForm => Str = 
    \base -> table {
          ASg Masc Indef => base  ;
          ASg Masc Def   => (base+"��") ;
          ASgMascDefNom  => (base+"���") ;
          ASg Fem  Indef => (base+"a") ;
          ASg Fem  Def   => (base+"���") ;
          ASg Neut Indef => (base+"�") ;
          ASg Neut Def   => (base+"���") ;
          APl Indef      => (ia2e base+"�") ;
          APl Def        => (ia2e base+"���")
        };
    
-- For $Sentence$.

    Clause : Type = {
      s : Tense => Anteriority => Polarity => Order => Str
      } ;

    mkClause : Str -> Agr -> VP -> Clause =
      \subj,agr,vp -> {
        s = \\t,a,b,o => 
          let 
            verb  : Bool => Str
                  = \\q => vp.ad ! q ++ vp.s ! t ! a ! b ! agr ! q ;
            compl = vp.s2 ! agr
          in case o of {
              Main  => subj ++ verb ! False ++ compl ;
              Inv   => verb ! False ++ compl ++ subj ;
              Quest => subj ++ verb ! True ++ compl
             }
      } ;
      
-- For $Numeral$.

    mkDigit : Str -> Str -> Str -> Str -> Str -> {s : DForm => CardOrd => Str} =
      \dva, dvama, dve, vtori, dvesta ->
      {s = table {
             unit                  => mkCardOrd dva dvama dve vtori ;
             teen                  => mkCardOrd (dva+"�������") (dva+"����������") (dva+"�������") (dva+"��������") ;
             ten                   => mkCardOrd (dva+"�����")   (dva+"��������")   (dva+"�����")   (dva+"������") ;
             hundred               => let dvesten : Str
                                                  = case dvesta of {
                                                      dvest+"�"        => dvest+"��" ;
                                                      chetiristot+"��" => chetiristot+"��"
                                                    }
                                      in mkCardOrd dvesta dvesta dvesta dvesten
           }
      } ;

    mkCardOrd : Str -> Str -> Str -> Str -> CardOrd => Str =
      \dva, dvama, dve, vtori ->
               table {
                 NCard dg   => digitGenderSpecies dva dvama dve ! dg ;
                 NOrd aform => let vtora = init vtori + "�" ;
                                   vtoro = init vtori + "�"
                               in case aform of {
                                    ASg Masc Indef => vtori ;
                                    ASg Masc Def   => vtori+"�" ;
                                    ASgMascDefNom  => vtori+"��" ;
                                    ASg Fem  Indef => vtora ;
                                    ASg Fem  Def   => vtora+"��" ;
                                    ASg Neut Indef => vtoro ;
                                    ASg Neut Def   => vtoro+"��" ;
                                    APl Indef      => vtori ;
                                    APl Def        => vtori+"��"
                                  }
               } ;

    digitGenderSpecies : Str -> Str -> Str -> DGenderSpecies => Str =
      \dva, dvama, dve
            -> let addDef : Str -> Str =
                     \s -> case s of {
		             dves+"��" => dves+"����" ;
		             dv+"�"    => dv+"���" ;
		             x         => x+"��"
                           }
               in table {
                    DMascIndef          => dva ;
                    DMascDef            => addDef dva ;
                    DMascDefNom         => addDef dva ;
                    DMascPersonalIndef  => dvama ;
                    DMascPersonalDef    => addDef dvama ;
                    DMascPersonalDefNom => addDef dvama ;
                    DFemIndef           => dve ;
                    DFemDef             => addDef dve ;
                    DNeutIndef          => dve ;
                    DNeutDef            => addDef dve
                  } ;

    mkIP : Str -> Str -> GenNum -> {s : Role => Str ; gn : GenNum} =
      \koi,kogo,gn -> {
      s = table {
            RSubj    => koi ;
            RObj Acc => kogo ;
            RObj Dat => "��" ++ kogo ;
            RVoc     => koi
          } ;
      gn = gn
      } ;

    mkPron : (az,men,mi,moj,moia,moiat,moia_,moiata,moe,moeto,moi,moite : Str) -> GenNum -> Person -> {s : Role => Str; gen : AForm => Str; a : Agr} =
      \az,men,mi,moj,moia,moiat,moia_,moiata,moe,moeto,moi,moite,gn,p -> {
      s = table {
            RSubj    => az ;
            RObj Acc => men ;
            RObj Dat => mi ;
            RVoc     => az
          } ;
      gen = table {
              ASg Masc Indef => moj ;
              ASg Masc Def   => moia ;
              ASgMascDefNom  => moiat ;
              ASg Fem  Indef => moia_ ;
              ASg Fem  Def   => moiata ;
              ASg Neut Indef => moe ;
              ASg Neut Def   => moeto ;
              APl Indef      => moi ;
              APl Def        => moite
            } ;
      a = {
           gn = gn ;
           p = p
          }
      } ;

    mkNP : Str -> GenNum -> Person -> {s : Role => Str; a : Agr} =
      \s,gn,p -> {
      s = table {
            RSubj    => s ;
            RObj Acc => s ;
            RObj Dat => "��" ++ s ;
            RVoc     => s
          } ;
      a = {
           gn = gn ;
           p = p
          }
      } ;
      
    Preposition : Type = {s : Str; c : Case};

    mkQuestion : 
      {s1,s2 : Str} -> Clause -> 
      {s : Tense => Anteriority => Polarity => QForm => Str} = \wh,cl ->
      {
      s = \\t,a,p => 
            let cls = cl.s ! t ! a ! p ;
            in table {
                 QDir   => wh.s1 ++ cls ! Inv ;
                 QIndir => wh.s2 ++ cls ! Main
               }
      } ;

    whichRP : GenNum => Str
            = table {
                GSg Masc => "�����" ;
                GSg Fem  => "�����" ;
                GSg Neut => "�����" ;
                GPl      => "�����"
              } ;

    suchRP : GenNum => Str
           = table {
               GSg Masc => "�����" ;
               GSg Fem  => "������" ;
               GSg Neut => "������" ;
               GPl      => "������"
             } ;
             
    thisRP : GenNum => Str
           = table {
               GSg Masc => "����" ;
               GSg Fem  => "�a��" ;
               GSg Neut => "����" ;
               GPl      => "����"
             }
}
