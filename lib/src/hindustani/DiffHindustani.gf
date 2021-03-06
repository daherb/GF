interface DiffHindustani = open Prelude in {
 oper
  addErgative : Str -> Str -> Str ;
 -- mkClause : NP -> VPH -> Clause ;
 -- mkSClause : Str -> Agr -> VPH -> Clause ;
  
 -- np2pronCase :  (Case => Str) -> NPCase -> Agr -> Str ;
  conjThat : Str ; -- = "kh" ;
  insertSubj : UPerson -> Str -> Str ;

  kwd : Str ;
  ky : Str ;
  agr : Str ; 
  awr : Str ; 
  jn : Str ; 
  js : Str ; 
  jw : Str ; 
  kw : Str ; 
  mt : Str ; 
  nE : Str ; 
  nh : Str ; 
  sE : Str ; 
  waN : Str ; 
  comma : Str ; 
  indfArt : Str ;
  nE : Str ;
  hE : Str ;
  
  na : Str ;
  nahen : Str ;
  xayad : Str ;
  kya : Str ;

  copula : CTense -> Number -> UPerson -> Gender -> Str ;
  raha : Gender -> Number -> Str ;
  cka : Gender -> Number -> Str ;
  hw : UPerson -> Number -> Str ;
  hwa : Agr -> Str ;
  regAdjective : Str -> Adjective ;  
}