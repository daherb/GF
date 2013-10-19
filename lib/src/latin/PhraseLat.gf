concrete PhraseLat of Phrase = CatLat ** open Prelude, ResLat in {
  
  lin
    PhrUtt pconj utt voc = -- PConj -> Utt -> Voc -> Phr ;
      {s = pconj.s ++ utt.s ++ voc.s} ;
    --
    UttS s = -- S -> Utt
      lin Utt s ; 
    UttQS qs = -- QS  -> Utt ;
      {s = qs.s ! QDir} ;
--    UttImpSg pol imp = {s = pol.s ++ imp.s ! contrNeg True pol.p ! ImpF Sg False} ;
--    UttImpPl pol imp = {s = pol.s ++ imp.s ! contrNeg True pol.p ! ImpF Pl False} ;
--    UttImpPol pol imp = {s = pol.s ++ imp.s ! contrNeg True pol.p ! ImpF Sg True} ;
--
--    UttIP ip = {s = ip.s ! Nom} ; --- Acc also
--    UttIAdv iadv = iadv ;
--    UttNP np = {s = np.s ! Nom} ;
--    UttVP vp = {s = infVP False vp (agrP3 Sg)} ;
--    UttAdv adv = adv ;
--
    NoPConj = {s = []} ;
    PConjConj conj = {s = conj.s2} ; ---
--
    NoVoc = {s = []} ;
    VocNP np = {s = "," ++ np.s ! Voc} ;
--
}
