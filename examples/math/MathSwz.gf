--# -path=.:prelude

concrete MathSwz of Mathw = open Prelude in {

flags lexer = textlit ; unlexer = textlit ;

-- lincat Section ; Context ; Typ ; Obj ; Prop ; Proof ; Var ;

lin
  SDefObj cont obj typ df = 
    ss ("Definition" ++ "." ++ cont.s ++ 
        obj.s ++ "�r" ++ "ett" ++ typ.s ++ "," ++ "definierat" ++ "som" ++ df.s ++ ".") ;  
  SDefProp cont prop df = 
    ss ("Definition" ++ "." ++ cont.s ++ "vi" ++ "s�ger" ++ 
        "att" ++ prop.s ++ "om" ++ df.s ++ ".") ;  
  SAxiom cont prop = 
    ss ("Axiom" ++ "." ++ cont.s ++ prop.s ++ ".") ;
  STheorem cont prop proof = 
    ss ("Theorem" ++ "." ++ cont.s ++ prop.s ++ "." ++ proof.s ++ ".") ;

  CEmpty = ss [] ;
  CObj vr typ co = ss ("l�t" ++ vr.s ++ "vara" ++ "ett" ++ typ.s ++ "." ++ co.s) ;
  CProp prop co = ss ("anta" ++ "att" ++ prop.s ++ "." ++ co.s) ;

  OVar v = v ;

  V_x = ss "x" ;
  V_y = ss "y" ;
  V_z = ss "z" ;

-- lexicon

  Set  = ss "m�ngd" ;
  Nat  = ss ["naturligt tal"] ;
  Zero = ss "noll" ;
  Succ = prefixSS ["efterf�ljaren till"] ;
  One  = ss "ett" ;
  Two  = ss "tv�" ;
  Even = postfixSS ["�r j�mnt"] ;
  Odd  = postfixSS ["�r udda"] ;
  Prime = postfixSS ["�r ett primtal"] ;
  Divisible = infixSS ["�r delbart med"] ;

}
