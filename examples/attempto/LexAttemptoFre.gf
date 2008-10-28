instance LexAttemptoFre of LexAttempto = 
  open ExtraFre, SyntaxFre, ParadigmsFre, ConstructX, IrregFre in {

oper
  possible_A = mkA "possible" ;
  necessary_A = mkA "n�cessaire" ;
  own_A = mkA "propre" ;
  have_VV = SyntaxFre.must_VV ;
  provably_Adv = mkAdv "d�montrablement" ;
  provable_A = mkA "d�montrable" ;
  false_A = mkA "faux" ;

  genitiveNP np cn = mkNP (mkNP the_Art cn) (SyntaxFre.mkAdv possess_Prep np) ;

}
