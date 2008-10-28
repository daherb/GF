instance LexAttemptoGer of LexAttempto = 
  open ExtraGer, SyntaxGer, ParadigmsGer, ConstructX, IrregGer in {

oper
  possible_A = mkA "m�glich" ;
  necessary_A = mkA "n�tig" ;
  own_A = mkA "eigen" ;
  have_VV = SyntaxGer.must_VV ;
  provably_Adv = mkAdv "beweisbar" ;
  provable_A = mkA "beweisbar" ;
  false_A = mkA "falsch" ;

  genitiveNP np cn = mkNP (mkNP the_Art cn) (SyntaxGer.mkAdv possess_Prep np) ;

}
