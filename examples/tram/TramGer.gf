--# -path=.:resource-1.0/abstract:resource-1.0/common:resource-1.0/multimodal:resource-1.0/german:prelude

concrete TramGer of Tram = TramI with 
  (Multimodal = MultimodalGer),
  (Math = MathGer) ;
