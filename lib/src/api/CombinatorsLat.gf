--# -path=.:alltenses:prelude

resource CombinatorsLat = Combinators with 
  (Cat = CatLat),
  (Structural = StructuralLat),
  (Constructors = ConstructorsLat) ;
