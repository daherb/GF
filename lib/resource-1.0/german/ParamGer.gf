--1 German parameters
--
-- This module defines the parameter types specific to German.
-- Some parameters, such as $Number$, are inherited from $ParamX$.
--

resource ParamGer = ParamX ** {

--2 For $Noun$

-- These are the standard four-value case and three-value gender.

  param
    Case = Nom | Acc | Dat | Gen ;
    Gender = Masc | Fem | Neutr ;

-- Complex $CN$s, like adjectives, have strong and weak forms.

    Adjf = Strong | Weak ;

-- Gender distinctions are only made in the singular. 

    GenNum = GSg Gender | GPl ;

-- Agreement of $NP$ is a record.

  oper Agr = {n : Number ; p : Person} ;

-- Pronouns are the worst-case noun phrases, which have both case
-- and possessive forms.

  param NPForm = NPCase Case | NPPoss GenNum Case ;

--2 For $Adjective$

-- The predicative form of adjectives is not inflected further.

  param AForm = APred | AMod Adjf GenNum Case ;  


--2 For $Verb$

  param VForm = 
     VInf 
   | VPresInd  Number Person
   | VPresSubj Number Person
   | VImper    Number
   | VImpfInd  Number Person 
   | VImpfSubj Number Person 
   | VPresPart AForm 
   | VPastPart AForm ;

  param VPForm =
     VPFinite Tense Anteriority
   | VPImperat
   | VPInfinit Anteriority ;

  param VAux = VHaben | VSein ;

-- The order of sentence is depends on whether it is used as a main
-- clause, inverted, or subordinate.

  param  
    Order = Main | Inv | Sub ;


--2 For $Relative$
 
    RAgr = RNoAg | RAg {n : Number ; p : Person} ;

----2 For $Numeral$
--
--    CardOrd = NCard | NOrd ;
--    DForm = unit | teen | ten  ;

--2 Transformations between parameter types

  oper
    agrP3 : Number -> Agr = \n -> 
      {n = n ; p = P3} ;

    gennum : Gender -> Number -> GenNum = \g,n ->
      case n of {
        Sg => GSg g ;
        Pl => GPl
        } ;

-- Needed in $RelativeGer$.

    numGenNum : GenNum -> Number = \gn -> 
      case gn of {
        GSg _ => Sg ;
        GPl   => Pl
        } ;

    agrAdj : Gender -> Adjf -> Number -> Case -> AForm = \g,a,n,c ->
      AMod a (gennum g n) c ;

    vFin : Tense -> Agr -> VForm = \t,a ->
      case t of {
        Pres => VPresInd  a.n a.p ;
        Past => VImpfInd  a.n a.p ;
        _ => VInf --- never used
        } ;

--    conjAgr : Agr -> Agr -> Agr = \a,b -> {
--      n = conjNumber a.n b.n ;
--      p = conjPerson a.p b.p
--      } ;
--
}
