--# -path=.:../scandinavian:../../prelude

--1 A Small Swedish Resource Syntax
--
-- Aarne Ranta 2002 - 2005
--
instance SyntaxSwe of SyntaxScand = TypesSwe ** 
  open Prelude, (CO = Coordination), MorphoSwe in {

  flags optimize=parametrize ;

  oper 

  npDet : NounPhrase = nameNounPhrase (mkProperName "det" NNeutr) ;

  mkAdjForm : Species -> Number -> NounGender -> AdjFormPos = \b,n,g -> 
    case <b,n> of {
      <Indef,Sg> => Strong (ASg (genNoun g)) ;
      <Indef,Pl> => Strong APl ;
      <Def,  Sg> => Weak (AxSg (sexNoun g)) ;
      <Def,  Pl> => Weak AxPl
      } ;

  verbVara = vara_1200 ** {s1 = []} ;
  verbHava = hava_1198 ** {s1 = []};

  verbFinnas : Verb = deponentVerb (vFinna "finn" "fann" "funn" ** {s1 = []}) ;

  relPronForms : RelCase => GenNum => Str = table {
    RNom  => \\_ => "som" ;
    RAcc  => \\_ => variants {"som" ; []} ;
    RGen  => \\_ => "vars" ;
    RPrep => pronVilken
    } ;
  
  pronVilken = table {
      ASg Utr   => "vilken" ; 
      ASg Neutr => "vilket" ; 
      APl       => "vilka"
      } ;

  pronS�dan = table {
      ASg Utr   => "s�dan" ; 
      ASg Neutr => "s�dant" ; 
      APl       => "s�dana"
      } ;

  pronN�gon = table {
      ASg Utr   => "n�gon" ; 
      ASg Neutr => "n�got" ; 
      APl       => "n�gra"
      } ;

  specDefPhrase : Bool -> Species = \b -> 
    Def ;

  superlSpecies = Def ;

  artIndef = table {Utr => "en" ; Neutr => "ett"} ;

  artDef : Bool => GenNum => Str = table {
    True => table {
      ASg Utr => "den" ;
      ASg Neutr => "det" ;              -- det gamla huset
      APl => variants {"de" ; "dom"}
      } ;
    False => table {_ => []}            -- huset
    } ;

  auxHar = "har" ;
  auxHade = "hade" ;
  auxHa = "ha" ;
  auxSka = "ska" ;
  auxSkulle = "skulle" ;

  infinAtt,subordAtt = "att" ;

  varjeDet : Determiner = mkDeterminerSg (detSgInvar "varje") IndefP ;
  allaDet  : Determiner = mkDeterminerPl "alla" IndefP ;
  flestaDet : Determiner = mkDeterminerPl ["de flesta"] IndefP ;

  prep�n = "�n" ;
  negInte = "inte" ;

  conjOm = "om" ;

  pronVars = "vars" ;
  pronVem = "vem" ;
  pronVems = "vems" ;
  pronVad = "vad" ;

--- added with Nor

  conjGender : Gender -> Gender -> Gender = \m,n ->
    case <m,n> of {
      <Utr,Utr> => Utr ;
      _ => Neutr
      } ;

  mkDeterminerSgGender3 : Str -> Str -> Str -> SpeciesP -> Determiner = \en,_,ett -> 
    mkDeterminerSgGender (table {Utr => en ; Neutr => ett}) ;

-- next

  reflPron : Number -> Person -> Str = \n,p -> case <n,p> of {
    <Sg,P1> => "mig" ;
    <Sg,P2> => "dig" ;
    <Pl,P1> => "oss" ;
    <Pl,P2> => "er" ;
    _ => "sig"
    } ;

  progressiveVerbPhrase : VerbPhrase -> VerbGroup =
    complVerbVerb 
      (mkVerbPart "h�lla" "h�ller" "h�ll"  "h�ll" "h�llit" "h�llen" "p�" ** 
         {isAux = False}) ;

  progressiveClause : NounPhrase -> VerbPhrase -> Clause = \np,vp ->
    predVerbGroupClause np
     (complVerbVerb 
      (mkVerbPart "h�lla" "h�ller" "h�ll"  "h�ll" "h�llit" "h�llen" "p�" ** 
         {isAux = False}) ----  ;{s3 = ["p� att"]})
      vp) ;

  strPrep : ComplPrep -> Str = \p -> case p of {
    CPnoPrep => [] ;
    CPav => "av" ;
----    CPmed => "med" ;
    CPf�r => "f�r" ;
    CPi => "i" ;
    CPom => "om" ;
    CPp� => "p�" ;
    CPtill => "till"
    } ;

  conjEt = "och" ;

}
