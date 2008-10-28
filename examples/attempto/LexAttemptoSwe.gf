instance LexAttemptoSwe of LexAttempto = 
  open ExtraSwe, SyntaxSwe, ParadigmsSwe, ConstructX, IrregSwe in {

oper
  possible_A = mkA "m�jlig" ;
  necessary_A = mkA "n�dv�ndig" ;
  own_A = mkA "egen" ;
  have_VV = must_VV ;
  provably_Adv = mkAdv "bevisbart" ;
  provable_A = mkA "bevisbar" ;
  false_A = mkA "falsk" ;

  genitiveNP np = mkNP (GenNP np) ;

}
