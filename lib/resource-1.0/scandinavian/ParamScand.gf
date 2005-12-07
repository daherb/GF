resource ParamScand = ParamX ** open Prelude in {

param
  Species = Indef | Def ;
  Case    = Nom | Gen ;
  Voice   = Act | Pass ;

  Order   = Main | Inv | Sub ;

  DetSpecies = DIndef | DDef Species ;

  GenNum  = SgUtr | SgNeutr | Plg ;

  AForm   = AF AFormGrad Case ;

  AFormGrad =
     APosit  AFormPos
   | ACompar  
   | ASuperl AFormSup ;

-- The $Number$ in $Weak$ only matters in "lilla"/"sm�".

  AFormPos = Strong GenNum | Weak Number ;
  AFormSup = SupStrong | SupWeak ;

  VForm = 
     VF VFin
   | VI VInf ;

  VFin =
     VPres Voice
   | VPret Voice
   | VImper Voice ;

  VInf = 
     VInfin Voice
   | VSupin Voice
   | VPtPret AFormPos Case ;

  VPForm = 
     VPFinite Tense Anteriority
   | VPImperat
   | VPInfinit Anteriority ;

  NPForm = NPNom | NPAcc | NPPoss GenNum ;
---  AdjPronForm = APron GenNum Case ;
---  AuxVerbForm = AuxInf | AuxPres | AuxPret | AuxSup ;

  RCase = RNom | RAcc | RGen | RPrep ;

  RAgr = RNoAg | RAg {gn : GenNum ; p : Person} ;

oper
  Agr : PType = {gn : GenNum ; p : Person} ;

  nominative : NPForm = NPNom ;
  accusative : NPForm = NPAcc ;

  caseNP : NPForm -> Case = \np -> case np of {
    NPPoss _ => Gen ;
    _ => Nom
    } ;

  specDet : DetSpecies -> Species = \d -> case d of {
    DDef Def => Def ;
    _ => Indef
    } ;

-- Used in $Noun.AdjCN$.

  agrAdj : GenNum -> DetSpecies -> AFormPos = \gn,d -> case <gn,d> of {
    <_,  DIndef> => Strong gn ;
    <Plg,DDef _> => Weak Pl ;
    _            => Weak Sg
    } ;

-- Used in $DiffScand.predV$.

  vFin : Tense -> Voice -> VForm = \t,v -> case t of {
    Pres => VF (VPres v) ;
    Past => VF (VPret v) ;
    _ => VI (VInfin v) --- not to be used?
    } ;
    
-- Used in $ConjunctionScand$.

  conjGenNum : (_,_ : GenNum) -> GenNum = \g,h -> case <g,h> of {
    <SgUtr,SgUtr> => SgUtr ;
    <Plg,  _>     => Plg ;
    <_,  Plg>     => Plg ;
    _             => SgNeutr 
    } ;

  conjAgr : (_,_ : Agr) -> Agr = \a,b -> {
    gn = conjGenNum a.gn b.gn ;
    p  = conjPerson a.p  b.p
    } ;

}
