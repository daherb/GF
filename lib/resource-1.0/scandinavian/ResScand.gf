--1 Scandinavian auxiliary operations

interface ResScand = DiffScand ** open CommonScand, Prelude in {

--2 Constants uniformly defined in terms of language-dependent constants

  param
    CardOrd = NCard Gender | NOrd AFormSup ; -- sic! (AFormSup)

  oper  
    agrP3 : Gender -> Number -> Agr = \g,n -> {
      gn = gennum g n ;
      p = P3
      } ;

    Noun = {s : Number => Species => Case => Str ; g : Gender} ;

-- This function is here because it depends on $verbHave, auxFut, auxCond$.

   predV : Verb -> VP = \verb -> 
    let
      diath = case verb.vtype of {
        VPass => Pass ;
        _ => Act
        } ;
      vfin : Tense -> Str = \t -> verb.s ! vFin t diath ;
      vsup = verb.s ! VI (VSupin diath) ;  
      vinf = verb.s ! VI (VInfin diath) ;

      har : Tense -> Str = \t -> verbHave.s ! vFin t Act ;
      ha  : Str = verbHave.s ! VI (VInfin Act) ;

      vf : Str -> Str -> {fin,inf : Str} = \fin,inf -> {
        fin = fin ; inf = inf
        } ;

    in {
    s = table {
      VPFinite t Simul => case t of {
        Pres | Past => vf (vfin t) [] ;
        Fut  => vf auxFut vinf ;
        Cond => vf auxCond vinf
        } ;
      VPFinite t Anter => case t of {
        Pres | Past => vf (har t) vsup ;
        Fut  => vf auxFut (ha ++ vsup) ;
        Cond => vf auxCond (ha ++ vsup) 
        } ;
      VPImperat => vf (verb.s ! VF (VImper diath)) [] ;
      VPInfinit Simul => vf [] vinf ;
      VPInfinit Anter => vf [] (ha ++ vsup)
      } ;
    a1  : Polarity => Str = negation ;
    n2  : Agr  => Str = \\a => case verb.vtype of {
      VRefl => reflPron a ;
      _ => []
      } ;
    a2  : Str = [] ;
    ext : Str = [] ;
    en2,ea2,eext : Bool = False   -- indicate if the field exists
    } ;

}
