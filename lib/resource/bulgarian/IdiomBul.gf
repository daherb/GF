concrete IdiomBul of Idiom = CatBul ** open Prelude, ParadigmsBul, ResBul in {
  flags optimize=all_subs ;

  lin
    ImpersCl vp = mkClause [] (agrP3 (GSg Neut)) vp ;
    GenericCl vp = mkClause "�����" (agrP3 (GSg Neut)) vp ;

    CleftNP np rs = 
      mkClause (np.s ! RSubj)
               {gn=GSg Neut; p=np.a.p}
               (insertObj (\\_ => thisRP ! np.a.gn ++ rs.s ! np.a.gn) (predV verbBe)) ;        
        
    CleftAdv ad s =
      mkClause (ad.s)
               (agrP3 (GSg Neut)) 
               (insertObj (\\_ => thisRP ! GPl ++ s.s) (predV verbBe)) ;        

    ExistNP np = 
      { s = \\t,a,p,o => 
	          let verb = case p of {
	                       Pos => mkV186 "����" ;
	                       Neg => mkV186 "�����" 
	                     } ;
                                 
                      agr=agrP3 (GSg Neut);
                                 
                      present = verb.s ! (VPres   (numGenNum agr.gn) agr.p) ;
                      aorist  = verb.s ! (VAorist (numGenNum agr.gn) agr.p) ;
                      perfect = verb.s ! (VPerfect (aform agr.gn Indef (RObj Acc))) ;
                                 
                      auxPres    = auxBe [] ! VPres (numGenNum agr.gn) agr.p ;
                      auxAorist  = auxBe [] ! VAorist (numGenNum agr.gn) agr.p ;
                      auxPerfect = auxBe [] ! VPerfect (aform agr.gn Indef (RObj Acc)) ;
                      auxCondS   = auxWould [] ! VAorist (numGenNum agr.gn) agr.p ;
                      auxCondA   = auxCondS ++
                                   auxBe [] ! VPerfect (aform agr.gn Indef (RObj Acc)) ;

                      v : {aux1:Str; aux2:Str; main:Str}
                        = case <t,a> of {
                            <Pres,Simul> => {aux1=[]; aux2=[]; main=present} ;
                            <Pres,Anter> => {aux1=[]; aux2=auxPres;   main=perfect} ;
                            <Past,Simul> => {aux1=[]; aux2=[]; main=aorist} ;
                            <Past,Anter> => {aux1=[]; aux2=auxAorist; main=perfect} ;
                            <Fut, Simul> => {aux1="��"; aux2=[]; main=present} ;
                            <Fut, Anter> => {aux1="��"++auxPres; aux2=[]; main=perfect} ;
                            <Cond,Simul> => {aux1=auxCondS; aux2=[]; main=perfect} ;
                            <Cond,Anter> => {aux1=auxCondA; aux2=[]; main=perfect}
                          } ;

	          in case o of {
	               Main  => v.aux1 ++ v.main ++ v.aux2 ++ np.s ! RObj Acc ;
	               Inv   => np.s ! RObj Acc ++ v.aux1 ++ v.main ++ v.aux2 ;
	               Quest => v.aux1 ++ v.main ++ "��" ++ v.aux2 ++ np.s ! RObj Acc
	             }
      } ;
{-
    ExistIP ip = 
      mkQuestion (ss (ip.s ! Nom)) 
        (mkClause "there" (agrP3 ip.n) (predAux auxBe)) ;
-}
    ProgrVP vp = vp ;

    ImpPl1 vp = {s = "����" ++ vp.s ! Pres ! Simul ! Pos ! {gn = GPl ; p = P1} ! False ++ vp.s2 ! {gn = GPl ; p = P1}} ;
}

