--1 English auxiliary operations.

-- This module contains operations that are needed to make the
-- resource syntax work. To define everything that is needed to
-- implement $Test$, it moreover contains regular lexical
-- patterns needed for $Lex$.

resource ResEng = ParamEng ** open Prelude in {

  flags optimize=all ;

  oper

-- For $Lex$.

-- For each lexical category, here are the worst-case constructors.

    mkNoun : (_,_,_,_ : Str) -> {s : Number => Case => Str} = 
      \man,mans,men,mens -> {
      s = table {
        Sg => table {
          Gen => mans ;
          _ => man
          } ;
        Pl => table {
          Gen => mens ;
          _ => men
          }
        }
      } ;

    mkAdjective : (_,_,_,_ : Str) -> {s : AForm => Str} = 
      \good,better,best,well -> {
      s = table {
        AAdj Posit  => good ;
        AAdj Compar => better ;
        AAdj Superl => best ;
        AAdv        => well
        }
      } ;

    mkVerb : (_,_,_,_,_ : Str) -> {s : VForm => Str} = 
      \go,goes,went,gone,going -> {
      s = table {
        VInf   => go ;
        VPres  => goes ;
        VPast  => went ;
        VPPart => gone ;
        VPresPart => going
        }
      } ;

    mkIP : (i,me,my : Str) -> Number -> {s : Case => Str ; n : Number} =
     \i,me,my,n -> let who = mkNP i me my n P3 in {s = who.s ; n = n} ;

    mkNP : (i,me,my : Str) -> Number -> Person -> {s : Case => Str ; a : Agr} =
     \i,me,my,n,p -> {
     s = table {
       Nom => i ;
       Acc => me ;
       Gen => my
       } ;
     a = {
       n = n ;
       p = p
       }
     } ;

-- These functions cover many cases; full coverage inflectional patterns are
-- in $MorphoEng$.

    regN : Str -> {s : Number => Case => Str} = \car ->
      mkNoun car (car + "'s") (car + "s") (car + "s'") ;

    regA : Str -> {s : AForm => Str} = \warm ->
      mkAdjective warm (warm + "er") (warm + "est") (warm + "ly") ;

    regV : Str -> {s : VForm => Str} = \walk ->
      mkVerb walk (walk + "s") (walk + "ed") (walk + "ed") (walk + "ing") ;

    regNP : Str -> Number -> {s : Case => Str ; a : Agr} = \that,n ->
      mkNP that that (that + "'s") n P3 ;

-- We have just a heuristic definition of the indefinite article.
-- There are lots of exceptions: consonantic "e" ("euphemism"), consonantic
-- "o" ("one-sided"), vocalic "u" ("umbrella").

    artIndef = pre {
      "a" ; 
      "an" / strs {"a" ; "e" ; "i" ; "o" ; "A" ; "E" ; "I" ; "O" }
      } ;

    artDef = "the" ;

-- For $Verb$.

  Verb : Type = {
    s : VForm => Str
    } ;

  VerbForms : Type =
    Tense => Anteriority => Polarity => Ord => Agr => {fin, inf : Str} ; 

  VP : Type = {
    s  : VerbForms ;
    s2 : Agr => Str
    } ;

  predV : Verb -> VP = \verb -> {
    s = \\t,ant,b,ord,agr => 
      let
        inf  = verb.s ! VInf ;
        fin  = presVerb verb agr ;
        past = verb.s ! VPast ;
        part = verb.s ! VPPart ;
        vf : Str -> Str -> {fin, inf : Str} = \x,y -> 
          {fin = x ; inf = y} ;
      in
      case <t,ant,b,ord> of {
        <Pres,Simul,Pos,ODir>   => vf fin          [] ;
        <Pres,Simul,Pos,OQuest> => vf (does agr)   inf ;
        <Pres,Simul,Neg,_>      => vf (doesnt agr) inf ;
        <Pres,Anter,Pos,_>      => vf (have agr)   part ;
        <Pres,Anter,Neg,_>      => vf (havent agr) part ;
        <Past,Simul,Pos,ODir>   => vf past         [] ;
        <Past,Simul,Pos,OQuest> => vf "did"        inf ;
        <Past,Simul,Neg,_>      => vf "didn't"     inf ;
        <Past,Anter,Pos,_>      => vf "had"        part ;
        <Past,Anter,Neg,_>      => vf "hadn't"     part ;
        <Fut, Simul,Pos,_>      => vf "will"       inf ;
        <Fut, Simul,Neg,_>      => vf "won't"      inf ;
        <Fut, Anter,Pos,_>      => vf "will"       ("have" ++ part) ;
        <Fut, Anter,Neg,_>      => vf "won't"      ("have" ++ part) ;
        <Cond,Simul,Pos,_>      => vf "would"      inf ;
        <Cond,Simul,Neg,_>      => vf "wouldn't"   inf ;
        <Cond,Anter,Pos,_>      => vf "would"      ("have" ++ part) ;
        <Cond,Anter,Neg,_>      => vf "wouldn't"   ("have" ++ part)
        } ;
    s2 = \\_ => []
    } ;

  predAux : Aux -> VP = \verb -> {
    s = \\t,ant,b,ord,agr => 
      let 
        inf  = verb.inf ;
        fin  = verb.pres ! b ! agr ;
        past = verb.past ! b ! agr ;
        part = verb.ppart ;
        vf : Str -> Str -> {fin, inf : Str} = \x,y -> 
          {fin = x ; inf = y} ;
      in
      case <t,ant,b,ord> of {
        <Pres,Simul,_,  _>      => vf fin          [] ;
        <Pres,Anter,Pos,_>      => vf (have agr)   part ;
        <Pres,Anter,Neg,_>      => vf (havent agr) part ;
        <Past,Simul,_,  _>      => vf past         [] ;
        <Past,Anter,Pos,_>      => vf "had"        part ;
        <Past,Anter,Neg,_>      => vf "hadn't"     part ;
        <Fut, Simul,Pos,_>      => vf "will"       inf ;
        <Fut, Simul,Neg,_>      => vf "won't"      inf ;
        <Fut, Anter,Pos,_>      => vf "will"       ("have" ++ part) ;
        <Fut, Anter,Neg,_>      => vf "won't"      ("have" ++ part) ;
        <Cond,Simul,Pos,_>      => vf "would"      inf ;
        <Cond,Simul,Neg,_>      => vf "wouldn't"   inf ;
        <Cond,Anter,Pos,_>      => vf "would"      ("have" ++ part) ;
        <Cond,Anter,Neg,_>      => vf "wouldn't"   ("have" ++ part)
        } ;
    s2 = \\_ => []
    } ;

  insertObj : (Agr => Str) -> VP -> VP = \obj,vp -> {
    s = vp.s ;
    s2 = \\a => vp.s2 ! a ++ obj ! a
    } ;

--- This is not functional.

  insertAdV : Str -> VP -> VP = \adv,vp -> {
    s = vp.s ;
    s2 = vp.s2
    } ;

  presVerb : {s : VForm => Str} -> Agr -> Str = \verb -> 
    agrVerb (verb.s ! VPres) (verb.s ! VInf) ;

  infVP : VP -> Agr -> Str = \vp,a -> 
    (vp.s ! Fut ! Simul ! Neg ! ODir ! a).inf ++ vp.s2 ! a ;

  agrVerb : Str -> Str -> Agr -> Str = \has,have,agr -> 
    case agr of {
      {n = Sg ; p = P3} => has ;
      _                 => have
      } ;

  have   = agrVerb "has"     "have" ;
  havent = agrVerb "hasn't"  "haven't" ;
  does   = agrVerb "does"    "do" ;
  doesnt = agrVerb "doesn't" "don't" ;

  Aux = {pres,past : Polarity => Agr => Str ; inf,ppart : Str} ;

  auxBe : Aux = {
    pres = \\b,a => case <b,a> of {
      <Pos,{n = Sg ; p = P1}> => "am" ; 
      <Neg,{n = Sg ; p = P1}> => ["am not"] ; --- am not I
      _ => agrVerb (posneg b "is")  (posneg b "are") a
      } ;
    past = \\b,a => agrVerb (posneg b "was") (posneg b "were") a ;
    inf  = "be" ;
    ppart = "been"
    } ;

  posneg : Polarity -> Str -> Str = \p,s -> case p of {
    Pos => s ;
    Neg => s + "n't"
    } ;

  conjThat : Str = "that" ;

  reflPron : Agr => Str = table {
    {n = Sg ; p = P1} => "myself" ;
    {n = Sg ; p = P2} => "yourself" ;
    {n = Sg ; p = P3} => "itself" ; ----
    {n = Pl ; p = P1} => "ourselves" ;
    {n = Pl ; p = P2} => "yourselves" ;
    {n = Pl ; p = P3} => "themselves"
    } ;

-- For $Sentence$.

  Clause : Type = {
    s : Tense => Anteriority => Polarity => Ord => Str
    } ;

  mkS : Str -> Agr -> VerbForms -> (Agr => Str) -> Clause =
    \subj,agr,verb,compl0 -> {
      s = \\t,a,b,o => 
        let 
          verb  = verb ! t ! a ! b ! o ! agr ;
          compl = compl0 ! agr
        in
        case o of {
          ODir   => subj ++ verb.fin ++ verb.inf ++ compl ;
          OQuest => verb.fin ++ subj ++ verb.inf ++ compl
          }
    } ;


-- For $Numeral$.

  mkNum : Str -> Str -> Str -> Str -> {s : DForm => CardOrd => Str} = 
    \two, twelve, twenty, second ->
    {s = table {
       unit => table {NCard => two ; NOrd => second} ; 
       teen => \\c => mkCard c twelve ; 
       ten  => \\c => mkCard c twenty
       }
    } ;

  regNum : Str -> {s : DForm => CardOrd => Str} = 
    \six -> mkNum six (six + "teen") (six + "ty") (regOrd six) ;

  regCardOrd : Str -> {s : CardOrd => Str} = \ten ->
    {s = table {NCard => ten ; NOrd => regOrd ten}} ;

  mkCard : CardOrd -> Str -> Str = \c,ten -> 
    (regCardOrd ten).s ! c ; 

  regOrd : Str -> Str = \ten -> 
    case last ten of {
      "y" => init ten + "ieth" ;
      _   => ten + "th"
      } ;

}
