--# -path=.:../abstract:../common:../../prelude

concrete PhraseRus of Phrase = CatRus ** open Prelude, ResRus in {
--
--  lin
--    PhrUtt pconj utt voc = {s = pconj.s ++ utt.s ++ voc.s} ;
--
--    UttS s = s ;
--    UttQS qs = {s = qs.s ! QDir} ;
--    UttImpSg pol imp = {s = pol.s ++ imp.s ! pol.p ! Sg} ;
--    UttImpPl pol imp = {s = pol.s ++ imp.s ! pol.p ! Pl} ;
--
--    UttIP ip = {s = ip.s ! Nom} ; --- Acc also
--    UttIAdv iadv = iadv ;
--    UttNP np = {s = np.s ! Acc} ;
--    UttVP vp = {s = infVP False vp (agrP3 Sg)} ;
--    UttAdv adv = adv ;
--
--    NoPConj = {s = []} ;
--    PConjConj conj = conj ;
--
--    NoVoc = {s = []} ;
--    VocNP np = {s = "," ++ np.s ! Nom} ;
--
}
