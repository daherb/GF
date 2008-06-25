--# -path=.:../abstract:../common:../english:prelude

concrete KoeEng of Koe = CatEng ** 
  open ParadigmsEng, ConstructorsEng, CombinatorsEng, GrammarEng in {

  lin
    ex1 = mkPhr (mkS (mkCl (mkNP (regPN "John")) (mkVP (regV "walk")))) ;
    ex2 = mkPhr (mkS (pred (regV "walk") (mkNP (regPN "John")))) ;
    ex3 = mkPhr (mkS (mkCl (mkNP and_Conj (mkNP (regPN "John"))(mkNP (regPN "Mary"))) (mkVP (regV "walk")))) ;
}
