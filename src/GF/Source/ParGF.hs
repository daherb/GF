{-# OPTIONS -fglasgow-exts -cpp #-}
{-# OPTIONS -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module GF.Source.ParGF where
import GF.Source.AbsGF
import GF.Source.LexGF
import GF.Data.ErrM
import qualified Data.ByteString.Char8 as BS
#if __GLASGOW_HASKELL__ >= 503
import Data.Array
#else
import Array
#endif
#if __GLASGOW_HASKELL__ >= 503
import GHC.Exts
#else
import GlaExts
#endif

-- parser produced by Happy Version 1.17

newtype HappyAbsSyn  = HappyAbsSyn HappyAny
#if __GLASGOW_HASKELL__ >= 607
type HappyAny = GHC.Exts.Any
#else
type HappyAny = forall a . a
#endif
happyIn8 :: (Integer) -> (HappyAbsSyn )
happyIn8 x = unsafeCoerce# x
{-# INLINE happyIn8 #-}
happyOut8 :: (HappyAbsSyn ) -> (Integer)
happyOut8 x = unsafeCoerce# x
{-# INLINE happyOut8 #-}
happyIn9 :: (String) -> (HappyAbsSyn )
happyIn9 x = unsafeCoerce# x
{-# INLINE happyIn9 #-}
happyOut9 :: (HappyAbsSyn ) -> (String)
happyOut9 x = unsafeCoerce# x
{-# INLINE happyOut9 #-}
happyIn10 :: (Double) -> (HappyAbsSyn )
happyIn10 x = unsafeCoerce# x
{-# INLINE happyIn10 #-}
happyOut10 :: (HappyAbsSyn ) -> (Double)
happyOut10 x = unsafeCoerce# x
{-# INLINE happyOut10 #-}
happyIn11 :: (LString) -> (HappyAbsSyn )
happyIn11 x = unsafeCoerce# x
{-# INLINE happyIn11 #-}
happyOut11 :: (HappyAbsSyn ) -> (LString)
happyOut11 x = unsafeCoerce# x
{-# INLINE happyOut11 #-}
happyIn12 :: (PIdent) -> (HappyAbsSyn )
happyIn12 x = unsafeCoerce# x
{-# INLINE happyIn12 #-}
happyOut12 :: (HappyAbsSyn ) -> (PIdent)
happyOut12 x = unsafeCoerce# x
{-# INLINE happyOut12 #-}
happyIn13 :: (Grammar) -> (HappyAbsSyn )
happyIn13 x = unsafeCoerce# x
{-# INLINE happyIn13 #-}
happyOut13 :: (HappyAbsSyn ) -> (Grammar)
happyOut13 x = unsafeCoerce# x
{-# INLINE happyOut13 #-}
happyIn14 :: ([ModDef]) -> (HappyAbsSyn )
happyIn14 x = unsafeCoerce# x
{-# INLINE happyIn14 #-}
happyOut14 :: (HappyAbsSyn ) -> ([ModDef])
happyOut14 x = unsafeCoerce# x
{-# INLINE happyOut14 #-}
happyIn15 :: (ModDef) -> (HappyAbsSyn )
happyIn15 x = unsafeCoerce# x
{-# INLINE happyIn15 #-}
happyOut15 :: (HappyAbsSyn ) -> (ModDef)
happyOut15 x = unsafeCoerce# x
{-# INLINE happyOut15 #-}
happyIn16 :: (ConcSpec) -> (HappyAbsSyn )
happyIn16 x = unsafeCoerce# x
{-# INLINE happyIn16 #-}
happyOut16 :: (HappyAbsSyn ) -> (ConcSpec)
happyOut16 x = unsafeCoerce# x
{-# INLINE happyOut16 #-}
happyIn17 :: ([ConcSpec]) -> (HappyAbsSyn )
happyIn17 x = unsafeCoerce# x
{-# INLINE happyIn17 #-}
happyOut17 :: (HappyAbsSyn ) -> ([ConcSpec])
happyOut17 x = unsafeCoerce# x
{-# INLINE happyOut17 #-}
happyIn18 :: (ConcExp) -> (HappyAbsSyn )
happyIn18 x = unsafeCoerce# x
{-# INLINE happyIn18 #-}
happyOut18 :: (HappyAbsSyn ) -> (ConcExp)
happyOut18 x = unsafeCoerce# x
{-# INLINE happyOut18 #-}
happyIn19 :: ([Transfer]) -> (HappyAbsSyn )
happyIn19 x = unsafeCoerce# x
{-# INLINE happyIn19 #-}
happyOut19 :: (HappyAbsSyn ) -> ([Transfer])
happyOut19 x = unsafeCoerce# x
{-# INLINE happyOut19 #-}
happyIn20 :: (Transfer) -> (HappyAbsSyn )
happyIn20 x = unsafeCoerce# x
{-# INLINE happyIn20 #-}
happyOut20 :: (HappyAbsSyn ) -> (Transfer)
happyOut20 x = unsafeCoerce# x
{-# INLINE happyOut20 #-}
happyIn21 :: (ModHeader) -> (HappyAbsSyn )
happyIn21 x = unsafeCoerce# x
{-# INLINE happyIn21 #-}
happyOut21 :: (HappyAbsSyn ) -> (ModHeader)
happyOut21 x = unsafeCoerce# x
{-# INLINE happyOut21 #-}
happyIn22 :: (ModHeaderBody) -> (HappyAbsSyn )
happyIn22 x = unsafeCoerce# x
{-# INLINE happyIn22 #-}
happyOut22 :: (HappyAbsSyn ) -> (ModHeaderBody)
happyOut22 x = unsafeCoerce# x
{-# INLINE happyOut22 #-}
happyIn23 :: (ModType) -> (HappyAbsSyn )
happyIn23 x = unsafeCoerce# x
{-# INLINE happyIn23 #-}
happyOut23 :: (HappyAbsSyn ) -> (ModType)
happyOut23 x = unsafeCoerce# x
{-# INLINE happyOut23 #-}
happyIn24 :: (ModBody) -> (HappyAbsSyn )
happyIn24 x = unsafeCoerce# x
{-# INLINE happyIn24 #-}
happyOut24 :: (HappyAbsSyn ) -> (ModBody)
happyOut24 x = unsafeCoerce# x
{-# INLINE happyOut24 #-}
happyIn25 :: ([TopDef]) -> (HappyAbsSyn )
happyIn25 x = unsafeCoerce# x
{-# INLINE happyIn25 #-}
happyOut25 :: (HappyAbsSyn ) -> ([TopDef])
happyOut25 x = unsafeCoerce# x
{-# INLINE happyOut25 #-}
happyIn26 :: (Extend) -> (HappyAbsSyn )
happyIn26 x = unsafeCoerce# x
{-# INLINE happyIn26 #-}
happyOut26 :: (HappyAbsSyn ) -> (Extend)
happyOut26 x = unsafeCoerce# x
{-# INLINE happyOut26 #-}
happyIn27 :: ([Open]) -> (HappyAbsSyn )
happyIn27 x = unsafeCoerce# x
{-# INLINE happyIn27 #-}
happyOut27 :: (HappyAbsSyn ) -> ([Open])
happyOut27 x = unsafeCoerce# x
{-# INLINE happyOut27 #-}
happyIn28 :: (Opens) -> (HappyAbsSyn )
happyIn28 x = unsafeCoerce# x
{-# INLINE happyIn28 #-}
happyOut28 :: (HappyAbsSyn ) -> (Opens)
happyOut28 x = unsafeCoerce# x
{-# INLINE happyOut28 #-}
happyIn29 :: (Open) -> (HappyAbsSyn )
happyIn29 x = unsafeCoerce# x
{-# INLINE happyIn29 #-}
happyOut29 :: (HappyAbsSyn ) -> (Open)
happyOut29 x = unsafeCoerce# x
{-# INLINE happyOut29 #-}
happyIn30 :: (ComplMod) -> (HappyAbsSyn )
happyIn30 x = unsafeCoerce# x
{-# INLINE happyIn30 #-}
happyOut30 :: (HappyAbsSyn ) -> (ComplMod)
happyOut30 x = unsafeCoerce# x
{-# INLINE happyOut30 #-}
happyIn31 :: (QualOpen) -> (HappyAbsSyn )
happyIn31 x = unsafeCoerce# x
{-# INLINE happyIn31 #-}
happyOut31 :: (HappyAbsSyn ) -> (QualOpen)
happyOut31 x = unsafeCoerce# x
{-# INLINE happyOut31 #-}
happyIn32 :: ([Included]) -> (HappyAbsSyn )
happyIn32 x = unsafeCoerce# x
{-# INLINE happyIn32 #-}
happyOut32 :: (HappyAbsSyn ) -> ([Included])
happyOut32 x = unsafeCoerce# x
{-# INLINE happyOut32 #-}
happyIn33 :: (Included) -> (HappyAbsSyn )
happyIn33 x = unsafeCoerce# x
{-# INLINE happyIn33 #-}
happyOut33 :: (HappyAbsSyn ) -> (Included)
happyOut33 x = unsafeCoerce# x
{-# INLINE happyOut33 #-}
happyIn34 :: (Def) -> (HappyAbsSyn )
happyIn34 x = unsafeCoerce# x
{-# INLINE happyIn34 #-}
happyOut34 :: (HappyAbsSyn ) -> (Def)
happyOut34 x = unsafeCoerce# x
{-# INLINE happyOut34 #-}
happyIn35 :: (TopDef) -> (HappyAbsSyn )
happyIn35 x = unsafeCoerce# x
{-# INLINE happyIn35 #-}
happyOut35 :: (HappyAbsSyn ) -> (TopDef)
happyOut35 x = unsafeCoerce# x
{-# INLINE happyOut35 #-}
happyIn36 :: (CatDef) -> (HappyAbsSyn )
happyIn36 x = unsafeCoerce# x
{-# INLINE happyIn36 #-}
happyOut36 :: (HappyAbsSyn ) -> (CatDef)
happyOut36 x = unsafeCoerce# x
{-# INLINE happyOut36 #-}
happyIn37 :: (FunDef) -> (HappyAbsSyn )
happyIn37 x = unsafeCoerce# x
{-# INLINE happyIn37 #-}
happyOut37 :: (HappyAbsSyn ) -> (FunDef)
happyOut37 x = unsafeCoerce# x
{-# INLINE happyOut37 #-}
happyIn38 :: (DataDef) -> (HappyAbsSyn )
happyIn38 x = unsafeCoerce# x
{-# INLINE happyIn38 #-}
happyOut38 :: (HappyAbsSyn ) -> (DataDef)
happyOut38 x = unsafeCoerce# x
{-# INLINE happyOut38 #-}
happyIn39 :: (DataConstr) -> (HappyAbsSyn )
happyIn39 x = unsafeCoerce# x
{-# INLINE happyIn39 #-}
happyOut39 :: (HappyAbsSyn ) -> (DataConstr)
happyOut39 x = unsafeCoerce# x
{-# INLINE happyOut39 #-}
happyIn40 :: ([DataConstr]) -> (HappyAbsSyn )
happyIn40 x = unsafeCoerce# x
{-# INLINE happyIn40 #-}
happyOut40 :: (HappyAbsSyn ) -> ([DataConstr])
happyOut40 x = unsafeCoerce# x
{-# INLINE happyOut40 #-}
happyIn41 :: (ParDef) -> (HappyAbsSyn )
happyIn41 x = unsafeCoerce# x
{-# INLINE happyIn41 #-}
happyOut41 :: (HappyAbsSyn ) -> (ParDef)
happyOut41 x = unsafeCoerce# x
{-# INLINE happyOut41 #-}
happyIn42 :: (ParConstr) -> (HappyAbsSyn )
happyIn42 x = unsafeCoerce# x
{-# INLINE happyIn42 #-}
happyOut42 :: (HappyAbsSyn ) -> (ParConstr)
happyOut42 x = unsafeCoerce# x
{-# INLINE happyOut42 #-}
happyIn43 :: (PrintDef) -> (HappyAbsSyn )
happyIn43 x = unsafeCoerce# x
{-# INLINE happyIn43 #-}
happyOut43 :: (HappyAbsSyn ) -> (PrintDef)
happyOut43 x = unsafeCoerce# x
{-# INLINE happyOut43 #-}
happyIn44 :: (FlagDef) -> (HappyAbsSyn )
happyIn44 x = unsafeCoerce# x
{-# INLINE happyIn44 #-}
happyOut44 :: (HappyAbsSyn ) -> (FlagDef)
happyOut44 x = unsafeCoerce# x
{-# INLINE happyOut44 #-}
happyIn45 :: ([Def]) -> (HappyAbsSyn )
happyIn45 x = unsafeCoerce# x
{-# INLINE happyIn45 #-}
happyOut45 :: (HappyAbsSyn ) -> ([Def])
happyOut45 x = unsafeCoerce# x
{-# INLINE happyOut45 #-}
happyIn46 :: ([CatDef]) -> (HappyAbsSyn )
happyIn46 x = unsafeCoerce# x
{-# INLINE happyIn46 #-}
happyOut46 :: (HappyAbsSyn ) -> ([CatDef])
happyOut46 x = unsafeCoerce# x
{-# INLINE happyOut46 #-}
happyIn47 :: ([FunDef]) -> (HappyAbsSyn )
happyIn47 x = unsafeCoerce# x
{-# INLINE happyIn47 #-}
happyOut47 :: (HappyAbsSyn ) -> ([FunDef])
happyOut47 x = unsafeCoerce# x
{-# INLINE happyOut47 #-}
happyIn48 :: ([DataDef]) -> (HappyAbsSyn )
happyIn48 x = unsafeCoerce# x
{-# INLINE happyIn48 #-}
happyOut48 :: (HappyAbsSyn ) -> ([DataDef])
happyOut48 x = unsafeCoerce# x
{-# INLINE happyOut48 #-}
happyIn49 :: ([ParDef]) -> (HappyAbsSyn )
happyIn49 x = unsafeCoerce# x
{-# INLINE happyIn49 #-}
happyOut49 :: (HappyAbsSyn ) -> ([ParDef])
happyOut49 x = unsafeCoerce# x
{-# INLINE happyOut49 #-}
happyIn50 :: ([PrintDef]) -> (HappyAbsSyn )
happyIn50 x = unsafeCoerce# x
{-# INLINE happyIn50 #-}
happyOut50 :: (HappyAbsSyn ) -> ([PrintDef])
happyOut50 x = unsafeCoerce# x
{-# INLINE happyOut50 #-}
happyIn51 :: ([FlagDef]) -> (HappyAbsSyn )
happyIn51 x = unsafeCoerce# x
{-# INLINE happyIn51 #-}
happyOut51 :: (HappyAbsSyn ) -> ([FlagDef])
happyOut51 x = unsafeCoerce# x
{-# INLINE happyOut51 #-}
happyIn52 :: ([ParConstr]) -> (HappyAbsSyn )
happyIn52 x = unsafeCoerce# x
{-# INLINE happyIn52 #-}
happyOut52 :: (HappyAbsSyn ) -> ([ParConstr])
happyOut52 x = unsafeCoerce# x
{-# INLINE happyOut52 #-}
happyIn53 :: ([PIdent]) -> (HappyAbsSyn )
happyIn53 x = unsafeCoerce# x
{-# INLINE happyIn53 #-}
happyOut53 :: (HappyAbsSyn ) -> ([PIdent])
happyOut53 x = unsafeCoerce# x
{-# INLINE happyOut53 #-}
happyIn54 :: (Name) -> (HappyAbsSyn )
happyIn54 x = unsafeCoerce# x
{-# INLINE happyIn54 #-}
happyOut54 :: (HappyAbsSyn ) -> (Name)
happyOut54 x = unsafeCoerce# x
{-# INLINE happyOut54 #-}
happyIn55 :: ([Name]) -> (HappyAbsSyn )
happyIn55 x = unsafeCoerce# x
{-# INLINE happyIn55 #-}
happyOut55 :: (HappyAbsSyn ) -> ([Name])
happyOut55 x = unsafeCoerce# x
{-# INLINE happyOut55 #-}
happyIn56 :: (LocDef) -> (HappyAbsSyn )
happyIn56 x = unsafeCoerce# x
{-# INLINE happyIn56 #-}
happyOut56 :: (HappyAbsSyn ) -> (LocDef)
happyOut56 x = unsafeCoerce# x
{-# INLINE happyOut56 #-}
happyIn57 :: ([LocDef]) -> (HappyAbsSyn )
happyIn57 x = unsafeCoerce# x
{-# INLINE happyIn57 #-}
happyOut57 :: (HappyAbsSyn ) -> ([LocDef])
happyOut57 x = unsafeCoerce# x
{-# INLINE happyOut57 #-}
happyIn58 :: (Exp) -> (HappyAbsSyn )
happyIn58 x = unsafeCoerce# x
{-# INLINE happyIn58 #-}
happyOut58 :: (HappyAbsSyn ) -> (Exp)
happyOut58 x = unsafeCoerce# x
{-# INLINE happyOut58 #-}
happyIn59 :: (Exp) -> (HappyAbsSyn )
happyIn59 x = unsafeCoerce# x
{-# INLINE happyIn59 #-}
happyOut59 :: (HappyAbsSyn ) -> (Exp)
happyOut59 x = unsafeCoerce# x
{-# INLINE happyOut59 #-}
happyIn60 :: (Exp) -> (HappyAbsSyn )
happyIn60 x = unsafeCoerce# x
{-# INLINE happyIn60 #-}
happyOut60 :: (HappyAbsSyn ) -> (Exp)
happyOut60 x = unsafeCoerce# x
{-# INLINE happyOut60 #-}
happyIn61 :: (Exp) -> (HappyAbsSyn )
happyIn61 x = unsafeCoerce# x
{-# INLINE happyIn61 #-}
happyOut61 :: (HappyAbsSyn ) -> (Exp)
happyOut61 x = unsafeCoerce# x
{-# INLINE happyOut61 #-}
happyIn62 :: (Exp) -> (HappyAbsSyn )
happyIn62 x = unsafeCoerce# x
{-# INLINE happyIn62 #-}
happyOut62 :: (HappyAbsSyn ) -> (Exp)
happyOut62 x = unsafeCoerce# x
{-# INLINE happyOut62 #-}
happyIn63 :: (Exp) -> (HappyAbsSyn )
happyIn63 x = unsafeCoerce# x
{-# INLINE happyIn63 #-}
happyOut63 :: (HappyAbsSyn ) -> (Exp)
happyOut63 x = unsafeCoerce# x
{-# INLINE happyOut63 #-}
happyIn64 :: (Exp) -> (HappyAbsSyn )
happyIn64 x = unsafeCoerce# x
{-# INLINE happyIn64 #-}
happyOut64 :: (HappyAbsSyn ) -> (Exp)
happyOut64 x = unsafeCoerce# x
{-# INLINE happyOut64 #-}
happyIn65 :: ([Exp]) -> (HappyAbsSyn )
happyIn65 x = unsafeCoerce# x
{-# INLINE happyIn65 #-}
happyOut65 :: (HappyAbsSyn ) -> ([Exp])
happyOut65 x = unsafeCoerce# x
{-# INLINE happyOut65 #-}
happyIn66 :: (Exps) -> (HappyAbsSyn )
happyIn66 x = unsafeCoerce# x
{-# INLINE happyIn66 #-}
happyOut66 :: (HappyAbsSyn ) -> (Exps)
happyOut66 x = unsafeCoerce# x
{-# INLINE happyOut66 #-}
happyIn67 :: (Patt) -> (HappyAbsSyn )
happyIn67 x = unsafeCoerce# x
{-# INLINE happyIn67 #-}
happyOut67 :: (HappyAbsSyn ) -> (Patt)
happyOut67 x = unsafeCoerce# x
{-# INLINE happyOut67 #-}
happyIn68 :: (Patt) -> (HappyAbsSyn )
happyIn68 x = unsafeCoerce# x
{-# INLINE happyIn68 #-}
happyOut68 :: (HappyAbsSyn ) -> (Patt)
happyOut68 x = unsafeCoerce# x
{-# INLINE happyOut68 #-}
happyIn69 :: (Patt) -> (HappyAbsSyn )
happyIn69 x = unsafeCoerce# x
{-# INLINE happyIn69 #-}
happyOut69 :: (HappyAbsSyn ) -> (Patt)
happyOut69 x = unsafeCoerce# x
{-# INLINE happyOut69 #-}
happyIn70 :: (PattAss) -> (HappyAbsSyn )
happyIn70 x = unsafeCoerce# x
{-# INLINE happyIn70 #-}
happyOut70 :: (HappyAbsSyn ) -> (PattAss)
happyOut70 x = unsafeCoerce# x
{-# INLINE happyOut70 #-}
happyIn71 :: (Label) -> (HappyAbsSyn )
happyIn71 x = unsafeCoerce# x
{-# INLINE happyIn71 #-}
happyOut71 :: (HappyAbsSyn ) -> (Label)
happyOut71 x = unsafeCoerce# x
{-# INLINE happyOut71 #-}
happyIn72 :: (Sort) -> (HappyAbsSyn )
happyIn72 x = unsafeCoerce# x
{-# INLINE happyIn72 #-}
happyOut72 :: (HappyAbsSyn ) -> (Sort)
happyOut72 x = unsafeCoerce# x
{-# INLINE happyOut72 #-}
happyIn73 :: ([PattAss]) -> (HappyAbsSyn )
happyIn73 x = unsafeCoerce# x
{-# INLINE happyIn73 #-}
happyOut73 :: (HappyAbsSyn ) -> ([PattAss])
happyOut73 x = unsafeCoerce# x
{-# INLINE happyOut73 #-}
happyIn74 :: ([Patt]) -> (HappyAbsSyn )
happyIn74 x = unsafeCoerce# x
{-# INLINE happyIn74 #-}
happyOut74 :: (HappyAbsSyn ) -> ([Patt])
happyOut74 x = unsafeCoerce# x
{-# INLINE happyOut74 #-}
happyIn75 :: (Bind) -> (HappyAbsSyn )
happyIn75 x = unsafeCoerce# x
{-# INLINE happyIn75 #-}
happyOut75 :: (HappyAbsSyn ) -> (Bind)
happyOut75 x = unsafeCoerce# x
{-# INLINE happyOut75 #-}
happyIn76 :: ([Bind]) -> (HappyAbsSyn )
happyIn76 x = unsafeCoerce# x
{-# INLINE happyIn76 #-}
happyOut76 :: (HappyAbsSyn ) -> ([Bind])
happyOut76 x = unsafeCoerce# x
{-# INLINE happyOut76 #-}
happyIn77 :: (Decl) -> (HappyAbsSyn )
happyIn77 x = unsafeCoerce# x
{-# INLINE happyIn77 #-}
happyOut77 :: (HappyAbsSyn ) -> (Decl)
happyOut77 x = unsafeCoerce# x
{-# INLINE happyOut77 #-}
happyIn78 :: (TupleComp) -> (HappyAbsSyn )
happyIn78 x = unsafeCoerce# x
{-# INLINE happyIn78 #-}
happyOut78 :: (HappyAbsSyn ) -> (TupleComp)
happyOut78 x = unsafeCoerce# x
{-# INLINE happyOut78 #-}
happyIn79 :: (PattTupleComp) -> (HappyAbsSyn )
happyIn79 x = unsafeCoerce# x
{-# INLINE happyIn79 #-}
happyOut79 :: (HappyAbsSyn ) -> (PattTupleComp)
happyOut79 x = unsafeCoerce# x
{-# INLINE happyOut79 #-}
happyIn80 :: ([TupleComp]) -> (HappyAbsSyn )
happyIn80 x = unsafeCoerce# x
{-# INLINE happyIn80 #-}
happyOut80 :: (HappyAbsSyn ) -> ([TupleComp])
happyOut80 x = unsafeCoerce# x
{-# INLINE happyOut80 #-}
happyIn81 :: ([PattTupleComp]) -> (HappyAbsSyn )
happyIn81 x = unsafeCoerce# x
{-# INLINE happyIn81 #-}
happyOut81 :: (HappyAbsSyn ) -> ([PattTupleComp])
happyOut81 x = unsafeCoerce# x
{-# INLINE happyOut81 #-}
happyIn82 :: (Case) -> (HappyAbsSyn )
happyIn82 x = unsafeCoerce# x
{-# INLINE happyIn82 #-}
happyOut82 :: (HappyAbsSyn ) -> (Case)
happyOut82 x = unsafeCoerce# x
{-# INLINE happyOut82 #-}
happyIn83 :: ([Case]) -> (HappyAbsSyn )
happyIn83 x = unsafeCoerce# x
{-# INLINE happyIn83 #-}
happyOut83 :: (HappyAbsSyn ) -> ([Case])
happyOut83 x = unsafeCoerce# x
{-# INLINE happyOut83 #-}
happyIn84 :: (Equation) -> (HappyAbsSyn )
happyIn84 x = unsafeCoerce# x
{-# INLINE happyIn84 #-}
happyOut84 :: (HappyAbsSyn ) -> (Equation)
happyOut84 x = unsafeCoerce# x
{-# INLINE happyOut84 #-}
happyIn85 :: ([Equation]) -> (HappyAbsSyn )
happyIn85 x = unsafeCoerce# x
{-# INLINE happyIn85 #-}
happyOut85 :: (HappyAbsSyn ) -> ([Equation])
happyOut85 x = unsafeCoerce# x
{-# INLINE happyOut85 #-}
happyIn86 :: (Altern) -> (HappyAbsSyn )
happyIn86 x = unsafeCoerce# x
{-# INLINE happyIn86 #-}
happyOut86 :: (HappyAbsSyn ) -> (Altern)
happyOut86 x = unsafeCoerce# x
{-# INLINE happyOut86 #-}
happyIn87 :: ([Altern]) -> (HappyAbsSyn )
happyIn87 x = unsafeCoerce# x
{-# INLINE happyIn87 #-}
happyOut87 :: (HappyAbsSyn ) -> ([Altern])
happyOut87 x = unsafeCoerce# x
{-# INLINE happyOut87 #-}
happyIn88 :: (DDecl) -> (HappyAbsSyn )
happyIn88 x = unsafeCoerce# x
{-# INLINE happyIn88 #-}
happyOut88 :: (HappyAbsSyn ) -> (DDecl)
happyOut88 x = unsafeCoerce# x
{-# INLINE happyOut88 #-}
happyIn89 :: ([DDecl]) -> (HappyAbsSyn )
happyIn89 x = unsafeCoerce# x
{-# INLINE happyIn89 #-}
happyOut89 :: (HappyAbsSyn ) -> ([DDecl])
happyOut89 x = unsafeCoerce# x
{-# INLINE happyOut89 #-}
happyIn90 :: (OldGrammar) -> (HappyAbsSyn )
happyIn90 x = unsafeCoerce# x
{-# INLINE happyIn90 #-}
happyOut90 :: (HappyAbsSyn ) -> (OldGrammar)
happyOut90 x = unsafeCoerce# x
{-# INLINE happyOut90 #-}
happyIn91 :: (Include) -> (HappyAbsSyn )
happyIn91 x = unsafeCoerce# x
{-# INLINE happyIn91 #-}
happyOut91 :: (HappyAbsSyn ) -> (Include)
happyOut91 x = unsafeCoerce# x
{-# INLINE happyOut91 #-}
happyIn92 :: (FileName) -> (HappyAbsSyn )
happyIn92 x = unsafeCoerce# x
{-# INLINE happyIn92 #-}
happyOut92 :: (HappyAbsSyn ) -> (FileName)
happyOut92 x = unsafeCoerce# x
{-# INLINE happyOut92 #-}
happyIn93 :: ([FileName]) -> (HappyAbsSyn )
happyIn93 x = unsafeCoerce# x
{-# INLINE happyIn93 #-}
happyOut93 :: (HappyAbsSyn ) -> ([FileName])
happyOut93 x = unsafeCoerce# x
{-# INLINE happyOut93 #-}
happyInTok :: Token -> (HappyAbsSyn )
happyInTok x = unsafeCoerce# x
{-# INLINE happyInTok #-}
happyOutTok :: (HappyAbsSyn ) -> Token
happyOutTok x = unsafeCoerce# x
{-# INLINE happyOutTok #-}


happyActOffsets :: HappyAddr
happyActOffsets = HappyA# "\x00\x00\xf8\x01\x28\x05\x26\x05\x12\x01\x06\x05\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x3a\x05\x00\x00\x44\x05\x7a\x02\x14\x00\x46\x05\x02\x05\xfb\x04\x00\x00\x3f\x05\x23\x02\xea\x04\x4f\x00\x12\x01\x00\x00\xea\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xd5\x00\xba\x00\x12\x01\x00\x00\x01\x05\x7a\x03\xdb\xff\x7a\x03\xf0\x04\xef\x04\x5d\x03\xeb\x04\xe7\x04\x00\x00\x00\x00\x00\x00\x00\x00\x32\x05\x41\x03\x00\x00\xe4\x04\x00\x00\x28\x00\x1e\x00\x41\x03\xe2\x04\xe1\x04\x68\x01\x0f\x05\x1d\x05\x1c\x05\xd0\x04\xd0\x04\xd0\x04\xd0\x04\xd0\x04\xd0\x04\x00\x00\x00\x00\x28\x00\x0d\x05\x00\x00\x28\x00\x28\x00\x28\x00\x2d\x08\x0c\x05\x69\x00\x2a\x02\x0b\x05\xcf\x04\x12\x01\x00\x00\xfc\xff\xb7\x04\xd1\x00\x1d\x02\x90\x00\x90\x00\xf9\x04\xfa\x04\xda\x04\xb2\x04\x35\x00\x23\x02\xc9\x04\x00\x00\xf7\x04\xf4\x04\xd8\x00\x00\x00\xe0\x04\x3a\x03\x00\x00\x00\x00\xee\x04\xf2\x04\xdb\x04\x2c\x02\xe9\x04\xde\x04\x1d\x03\x23\x00\x00\x00\x00\x00\x00\x00\xdf\x04\x00\x00\x9b\x04\x1d\x02\x1d\x02\x00\x00\x9d\x04\x00\x00\x99\x04\x90\x00\x90\x00\x53\x01\x53\x01\x53\x01\x53\x01\x53\x01\x90\x00\x9e\x04\xd9\x04\xfe\xff\xfa\x02\x00\x00\x95\x04\x00\x00\x00\x00\x98\x04\x92\x04\x00\x00\xdd\x02\x9c\x02\x00\x00\xdd\x02\xdd\x02\xdd\x02\x00\x00\x00\x00\x00\x00\x3a\x00\xc2\x04\xd1\x04\x88\x04\xb3\x04\xb2\x01\xca\x04\x00\x00\x24\x00\xc7\x04\xba\x04\x23\x02\x1b\x00\xc0\x04\x7c\x04\x00\x00\x7c\x04\xc6\x04\x90\x00\x00\x00\x00\x00\x90\x00\x90\x00\xba\x02\xaa\x04\x00\x00\xb5\x04\x90\x00\xd8\x00\x6f\x04\x23\x02\xab\x04\xa5\x04\x69\x04\x00\x00\x67\x04\x90\x00\x63\x04\xa1\x04\xa0\x04\x54\x04\x70\x01\x73\x00\x8e\x04\x51\x04\x97\x04\x90\x00\x1d\x02\x50\x04\x00\x00\x49\x04\x90\x00\x90\x00\x49\x04\x00\x00\xfb\xff\x00\x00\xa2\x00\x49\x04\x83\x00\x49\x04\x49\x04\x83\x00\x83\x00\x83\x00\x83\x00\x83\x00\x49\x04\x49\x04\x83\x00\xbe\x00\x49\x04\x83\x00\x83\x00\x00\x00\x00\x00\x00\x00\x28\x00\x00\x00\x89\x04\x00\x00\x00\x00\x62\x04\x53\x04\x00\x00\x75\x07\x3e\x04\x65\x04\x2b\x01\x00\x00\x4f\x04\x7d\x04\x3f\x00\x2d\x04\x2d\x04\x2d\x04\x2d\x04\x13\x00\x00\x00\x00\x00\x5d\x04\x00\x00\x06\x02\x4b\x01\x14\x04\x00\x00\x52\x04\x41\x04\x00\x00\x46\x04\x3c\x04\x83\x00\x83\x00\x00\x00\x36\x04\x28\x04\x00\x00\x23\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x27\x04\x00\x00\x25\x04\x20\x04\x12\x04\x00\x00\x00\x00\x17\x00\x0d\x04\x00\x00\x00\x00\x00\x00\x09\x04\x00\x00\xca\x03\x00\x00\xe2\x03\x0e\x04\x15\x00\xc7\x03\xc7\x03\xc9\x03\x00\x00\xf5\x03\x00\x00\x00\x00\xb9\x03\xe7\x03\x00\x00\x00\x02\x00\x02\x90\x00\x00\x02\x00\x00\xb1\x03\x23\x02\x00\x00\x90\x00\x90\x00\x00\x00\x00\x00\xd3\x03\x00\x00\x23\x02\x90\x00\x00\x00\x00\x02\x00\x00\x00\x00\x90\x00\x00\x00\x00\x00\xd5\x03\x00\x00\x00\x00\xdc\x03\x00\x00\x00\x00\x00\x00\x97\x03\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x97\x03\x00\x02\x00\x00\xb5\x03\x00\x00\x0e\x00\x00\x00\x24\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xb4\x03\x00\x00\x00\x00\x90\x00\xd2\x03\xcf\x03\x93\x03\x00\x00\x00\x00\x23\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x90\x00\x00\x00\x00\x00\xc5\x03\x00\x00\x82\x03\x13\x00\x82\x03\x00\x00\x13\x00\x00\x00\x75\x00\x9d\x02\x82\x03\x82\x03\x82\x03\x82\x03\x90\x00\x82\x03\x85\x03\x7c\x03\x12\x00\x00\x00\x00\x00\x90\x00\x6c\x00\x6c\x00\x00\x00\xac\x03\x90\x00\x90\x00\xb3\x03\x6c\x00\x00\x00\xb0\x03\xc8\x00\x00\x00\x00\x00\x00\x00\x00\x00\x11\x00\x74\x03\x79\x03\x9c\x03\x64\x03\x9e\x03\x58\x03\x86\x03\x4e\x03\x00\x00\x5f\x03\x96\x03\x91\x03\x35\x03\x00\x00\x00\x00\x11\x00\x00\x00\x90\x00\x00\x00\x7f\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x44\x03\x00\x00\x56\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x73\x03\x42\x03\x00\x00\x6a\x03\x00\x00\x00\x00\x00\x00\x4f\x00\x00\x00\x5d\x02\x49\x03\x33\x03\x6c\x03\x00\x00\x00\x00\x00\x00\x00\x00\x90\x00\x90\x00\x00\x00\x00\x00\x00\x00\x00\x00\x3b\x03\x11\x00\x00\x00\x1f\x03\x55\x03\x17\x03\x17\x03\x0c\x08\x17\x03\x17\x03\x9d\x02\x90\x00\x00\x00\x00\x00\x17\x02\x11\x00\x2d\x03\x11\x00\xeb\x07\x3e\x03\x00\x00\x4c\x03\x0b\x03\x00\x00\x00\x00\x51\x03\x05\x03\x00\x00\x00\x00\x01\x03\x00\x00\x00\x00\x48\x03\x31\x03\x00\x00\x00\x00\x90\x00\x00\x03\x3d\x03\x00\x00\x0a\x03\xf4\x02\x37\x03\x00\x00\x00\x00\x36\x03\x00\x00\xfe\x02\x21\x03\x18\x03\xe6\x02\x00\x00\xd2\x02\xd2\x02\xe7\x02\xca\x07\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x19\x03\xa9\x07\x00\x00\x00\x00\xd9\x02\x6b\x00\x11\x00\x11\x00\x16\x03\x14\x03\x00\x00\x00\x00\x00\x00"#

happyGotoOffsets :: HappyAddr
happyGotoOffsets = HappyA# "\xb3\x01\x2e\x00\xc8\x01\x66\x01\x08\x07\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x55\x07\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x24\x03\x15\x03\x10\x04\xd7\x03\x00\x00\x0e\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x25\x00\xa1\x00\xef\x06\x00\x00\x00\x00\xae\x06\x54\x02\x48\x06\x00\x00\x00\x00\x69\x07\x00\x00\x29\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x03\x00\x00\x00\x00\xf5\x02\x03\x00\x00\x00\xf6\x02\xfd\x02\x00\x00\x18\x00\x00\x00\x00\x00\x00\x00\xf9\x02\xf8\x02\xf1\x02\xec\x02\xe5\x02\xd6\x02\x00\x00\x00\x00\x0b\x00\x00\x00\x00\x00\x09\x00\x07\x00\x05\x00\xbe\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x77\x04\x00\x00\x00\x00\xcb\x02\xdb\x06\xa1\x03\x5e\x04\xc2\x06\x00\x00\x00\x00\x00\x00\x15\x02\xcd\x02\x7d\x00\x00\x00\x00\x00\x00\x00\x00\x00\x8b\x00\x00\x00\x00\x00\xe2\x05\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x7c\x05\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xb9\x02\x30\x04\x04\x01\x00\x00\xbb\x02\x00\x00\xf8\x00\xa2\x06\x89\x06\x28\x07\x50\x07\xdb\x02\x5b\x02\x41\x07\x75\x06\x00\x00\x00\x00\x4e\x00\x60\x07\x00\x00\xe3\x01\x00\x00\x00\x00\xb2\x02\xbe\x01\x00\x00\x16\x05\x00\x00\x00\x00\x16\x05\x16\x05\x16\x05\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x64\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe4\x02\x00\x00\x00\x00\xa4\x02\x00\x00\x9a\x02\x00\x00\x5c\x06\x00\x00\x00\x00\xbe\x03\x3c\x06\x4a\x04\x00\x00\x00\x00\x00\x00\x23\x06\x0a\x00\x00\x00\x47\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0f\x06\x15\x01\x00\x00\x00\x00\x00\x00\xcb\x01\x00\x00\x00\x00\x00\x00\x00\x00\x3d\x04\xb2\x03\x00\x00\x00\x00\x85\x01\xf6\x05\xd6\x05\x95\x02\x00\x00\x6a\x08\x00\x00\x30\x01\xad\x07\x99\x07\x60\x01\x4d\x01\x96\x07\x8a\x07\x7c\x07\x79\x07\x77\x07\x8e\x02\x64\x01\x4b\x07\x6a\x07\x8d\x02\x8a\x03\x2c\x03\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x62\x08\x00\x00\x00\x00\x00\x00\x00\x00\x74\x02\x00\x00\x00\x00\x82\x02\x13\x02\x7c\x02\x78\x02\x0b\x02\x00\x00\x00\x00\x00\x00\x00\x00\x46\x01\x00\x00\x71\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x8d\x03\x86\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x18\x02\x00\x00\x00\x00\x5f\x02\x00\x00\x1a\x02\x00\x00\x00\x00\x5c\x02\xd0\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x99\x03\x7f\x04\xbd\x05\x66\x04\x00\x00\x4e\x02\x97\x01\x00\x00\x24\x04\xac\x01\x00\x00\x00\x00\x00\x00\x00\x00\x38\x00\xa9\x05\x00\x00\xf5\x01\x00\x00\x00\x00\x90\x05\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x48\x02\x00\x00\x00\x00\x00\x00\xc3\x00\x00\x00\x00\x00\x00\x00\x8a\x00\xe5\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x70\x05\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x47\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x57\x05\x00\x00\x00\x00\x00\x00\x00\x00\x86\x01\xed\x02\xee\x00\x00\x00\xdf\x02\xb9\x01\x94\x00\x10\x00\xff\x00\xa6\x01\x97\x00\x34\x02\x43\x05\xd4\x00\x00\x00\x56\x01\x18\x01\x00\x00\x00\x00\x2a\x05\xe2\x00\xa7\x01\x00\x00\x00\x00\x0a\x05\xf1\x04\x00\x00\x38\x01\x00\x00\x00\x00\x1f\x02\x00\x00\x00\x00\x00\x00\x00\x00\xad\x02\x1a\x00\x00\x00\x00\x00\x05\x01\x00\x00\x30\x02\x00\x00\xa3\x00\xf3\x01\x00\x00\x00\x00\x00\x00\x11\x02\x00\x00\x00\x00\xf9\x01\x00\x00\xdd\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x95\x01\x00\x00\x00\x00\x00\x00\x00\x00\xe1\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf7\x03\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa5\x01\xc4\x04\x00\x00\x00\x00\x00\x00\x00\x00\xba\x01\x87\x02\x00\x00\x00\x00\x00\x00\x1f\x00\xc3\x01\xd5\x01\xbf\x01\x11\x01\x10\x00\xa4\x04\x00\x00\x00\x00\x00\x00\xf4\x01\x9f\x01\x9f\x00\x96\x01\x00\x00\x00\x00\x00\x00\xc9\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x98\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x8b\x04\x78\x01\x00\x00\x00\x00\x69\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x3f\x01\x06\x01\x00\x00\x00\x00\x00\x00\x00\x00\xbd\x02\x88\x01\x00\x00\x2a\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa0\x00\x20\x00\x00\x00\x00\x00\x8e\x00\x22\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe9\x01\x2c\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

happyDefActions :: HappyAddr
happyDefActions = HappyA# "\xf4\xff\xc3\xff\xf5\xfe\xc3\xff\x00\x00\x00\x00\xfa\xff\x6e\xff\x6f\xff\x6d\xff\x62\xff\x73\xff\x5e\xff\x52\xff\x4d\xff\x4b\xff\x49\xff\x3e\xff\x00\x00\x70\xff\x00\x00\x00\x00\x00\x00\x12\xff\x0b\xff\x6c\xff\x00\x00\x1d\xff\x1b\xff\x1a\xff\x1c\xff\x1e\xff\x00\x00\x12\xff\x00\x00\x6a\xff\x00\x00\x00\x00\x76\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x76\xff\xf9\xff\xf8\xff\xf7\xff\xf6\xff\x00\x00\x00\x00\xc2\xff\x00\x00\xcf\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc3\xff\xf3\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf2\xff\xf3\xfe\xf2\xfe\x00\x00\xf4\xfe\x00\x00\x00\x00\x00\x00\xf6\xfe\x00\x00\x7f\xff\x00\x00\x75\xff\x00\x00\x3d\xff\x73\xff\x00\x00\x00\x00\x00\x00\x76\xff\x3d\xff\x00\x00\x53\xff\x7f\xff\x00\x00\x76\xff\x00\x00\x01\xff\x00\x00\x14\xff\x11\xff\x00\x00\x12\xff\x13\xff\x00\x00\x3a\xff\x6b\xff\x51\xff\x0d\xff\x0a\xff\x00\x00\x73\xff\x00\x00\x00\x00\x00\x00\x00\x00\x30\xff\x2e\xff\x2f\xff\x33\xff\x54\xff\x00\x00\x00\x00\x08\xff\x38\xff\x00\x00\x34\xff\x19\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x5d\xff\x00\x00\x00\x00\x55\xff\x76\xff\x20\xff\x61\xff\x00\x00\x76\xff\x44\xff\x4d\xff\x4b\xff\x4c\xff\x4e\xff\x4f\xff\x50\xff\x4a\xff\x48\xff\x45\xff\x7f\xff\x00\x00\x18\xff\x00\x00\x00\x00\x33\xff\x25\xff\x22\xff\x0c\xff\x07\xff\x00\x00\x00\x00\x00\x00\x36\xff\x00\x00\x71\xff\x00\x00\x73\xff\x00\x00\x63\xff\x66\xff\x0b\xff\x00\x00\x3a\xff\x00\x00\x68\xff\x00\x00\x00\x00\x12\xff\x00\x00\x16\xff\x00\x00\x00\xff\x00\x00\x3f\xff\x00\x00\x00\x00\x00\x00\x00\x00\x3c\xff\x00\x00\x33\xff\x00\x00\x04\xff\x00\x00\x00\x00\x3d\xff\x00\x00\x00\x00\x67\xff\x76\xff\x00\x00\x00\x00\x00\x00\x72\xff\xbe\xff\xce\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf1\xfe\xf0\xfe\xef\xfe\xed\xfe\xee\xfe\x00\x00\xdc\xff\xdb\xff\x00\x00\x00\x00\xdd\xff\xbe\xff\x00\x00\x00\x00\xbb\xff\xf0\xff\xc8\xff\xd6\xff\xbd\xff\x00\x00\xbe\xff\x00\x00\x00\x00\x00\x00\xec\xfe\x7d\xff\x00\x00\xa2\xff\x7b\xff\x00\x00\x00\x00\xaf\xff\x00\x00\x00\x00\xa6\xff\x7b\xff\x00\x00\x00\x00\x00\x00\xa4\xff\x94\xff\x00\x00\xae\xff\x00\x00\xad\xff\xa5\xff\xab\xff\xac\xff\xaa\xff\x00\x00\xb3\xff\x00\x00\x00\x00\x00\x00\xa7\xff\xb1\xff\x7f\xff\x00\x00\xb2\xff\xb0\xff\xf8\xfe\x00\x00\xb4\xff\x00\x00\xe6\xff\xc8\xff\xe4\xff\xbd\xff\x00\x00\xbe\xff\x00\x00\x78\xff\x79\xff\x74\xff\x58\xff\x00\x00\x00\x00\x5c\xff\x00\x00\x00\x00\x00\x00\x00\x00\x2a\xff\x00\x00\x00\x00\x56\xff\x3d\xff\xfd\xfe\x7e\xff\x42\xff\x00\x00\x40\xff\x01\xff\x00\x00\x15\xff\x00\x00\x10\xff\x47\xff\x00\x00\x69\xff\x39\xff\x00\x00\x0d\xff\x09\xff\x00\x00\x65\xff\x5f\xff\x31\xff\x00\x00\x2b\xff\x26\xff\x2c\xff\x08\xff\x28\xff\x37\xff\x2d\xff\x19\xff\x00\x00\x32\xff\x00\x00\x1f\xff\x7f\xff\x41\xff\x21\xff\x17\xff\x06\xff\x35\xff\x0f\xff\x64\xff\x46\xff\x00\x00\x02\xff\xff\xfe\x00\x00\x00\x00\xfc\xfe\x00\x00\x3b\xff\x27\xff\x31\xff\x24\xff\x05\xff\x23\xff\x03\xff\x5a\xff\x5b\xff\x00\x00\x60\xff\xde\xff\xbd\xff\xdf\xff\xbe\xff\xcb\xff\xcd\xff\xe5\xff\xcb\xff\xf8\xfe\x8e\xff\xa0\xff\x8a\xff\x99\xff\x84\xff\x00\x00\x00\x00\x8c\xff\x00\x00\x88\xff\x82\xff\xa8\xff\xa9\xff\x00\x00\x00\x00\x86\xff\xa1\xff\x00\x00\x00\x00\x00\x00\x00\x00\x90\xff\xc6\xff\x00\x00\xc1\xff\xd9\xff\xda\xff\xd0\xff\xd1\xff\xcb\xff\xcd\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xcf\xff\x00\x00\xd5\xff\xca\xff\x00\x00\xc0\xff\xbf\xff\x00\x00\x8f\xff\x00\x00\xb7\xff\xb8\xff\x7c\xff\x85\xff\x7a\xff\x92\xff\xf8\xfe\x81\xff\x96\xff\x00\x00\x87\xff\xcf\xff\x8b\xff\x9d\xff\x91\xff\x83\xff\x9b\xff\x98\xff\x9c\xff\x00\x00\x89\xff\xf9\xfe\xf7\xfe\x12\xff\x8d\xff\x00\x00\x00\x00\x00\x00\xe3\xff\xbc\xff\x77\xff\x29\xff\x57\xff\xfd\xfe\x00\x00\x43\xff\x59\xff\xfe\xfe\xfb\xfe\xc8\xff\xcb\xff\xc7\xff\x9f\xff\x00\x00\x99\xff\x00\x00\x00\x00\x00\x00\x82\xff\x93\xff\x00\x00\xb6\xff\xd8\xff\x00\x00\xcb\xff\xc8\xff\xcb\xff\x00\x00\x00\x00\xba\xff\x00\x00\xee\xff\xb9\xff\xd7\xff\xd3\xff\x00\x00\xc9\xff\xc5\xff\x00\x00\xb5\xff\x80\xff\x00\x00\x00\x00\x9a\xff\x97\xff\x00\x00\x00\x00\xe1\xff\xe2\xff\xc8\xff\x00\x00\x00\x00\xa3\xff\x95\xff\x00\x00\xcf\xff\xc8\xff\x00\x00\xed\xff\x00\x00\xf1\xff\xee\xff\x00\x00\x00\x00\x00\x00\xc4\xff\xfa\xfe\x9e\xff\xe0\xff\xd4\xff\xcf\xff\xea\xff\xef\xff\xec\xff\xeb\xff\x00\x00\xd2\xff\xe9\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe8\xff\xe7\xff"#

happyCheck :: HappyAddr
happyCheck = HappyA# "\xff\xff\x03\x00\x01\x00\x08\x00\x01\x00\x04\x00\x01\x00\x04\x00\x01\x00\x04\x00\x01\x00\x04\x00\x01\x00\x04\x00\x04\x00\x04\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x01\x00\x05\x00\x05\x00\x05\x00\x0b\x00\x1e\x00\x07\x00\x08\x00\x09\x00\x04\x00\x07\x00\x0b\x00\x06\x00\x0b\x00\x04\x00\x09\x00\x4a\x00\x01\x00\x04\x00\x14\x00\x04\x00\x13\x00\x0b\x00\x51\x00\x09\x00\x16\x00\x11\x00\x04\x00\x0e\x00\x37\x00\x19\x00\x0c\x00\x07\x00\x0e\x00\x0f\x00\x00\x00\x01\x00\x02\x00\x40\x00\x04\x00\x1b\x00\x1f\x00\x20\x00\x45\x00\x15\x00\x32\x00\x0e\x00\x16\x00\x0b\x00\x4a\x00\x00\x00\x01\x00\x02\x00\x0b\x00\x04\x00\x51\x00\x43\x00\x44\x00\x51\x00\x40\x00\x02\x00\x04\x00\x04\x00\x05\x00\x54\x00\x55\x00\x54\x00\x55\x00\x54\x00\x4c\x00\x54\x00\x48\x00\x54\x00\x49\x00\x54\x00\x50\x00\x12\x00\x51\x00\x51\x00\x51\x00\x16\x00\x4b\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x4b\x00\x21\x00\x53\x00\x23\x00\x3b\x00\x0b\x00\x26\x00\x4e\x00\x0e\x00\x29\x00\x51\x00\x42\x00\x2c\x00\x09\x00\x00\x00\x01\x00\x02\x00\x31\x00\x04\x00\x3b\x00\x4e\x00\x4c\x00\x4d\x00\x4c\x00\x14\x00\x49\x00\x42\x00\x1e\x00\x3c\x00\x3d\x00\x3f\x00\x04\x00\x04\x00\x41\x00\x42\x00\x02\x00\x1e\x00\x04\x00\x05\x00\x47\x00\x2c\x00\x04\x00\x4a\x00\x0c\x00\x04\x00\x4d\x00\x4e\x00\x4f\x00\x50\x00\x51\x00\x1e\x00\x12\x00\x04\x00\x39\x00\x04\x00\x16\x00\x04\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x1c\x00\x11\x00\x13\x00\x23\x00\x15\x00\x4c\x00\x26\x00\x2d\x00\x3b\x00\x29\x00\x26\x00\x24\x00\x2c\x00\x51\x00\x4b\x00\x42\x00\x1e\x00\x31\x00\x2b\x00\x00\x00\x01\x00\x02\x00\x51\x00\x04\x00\x3e\x00\x4c\x00\x4d\x00\x41\x00\x3c\x00\x3d\x00\x43\x00\x44\x00\x2d\x00\x41\x00\x42\x00\x02\x00\x51\x00\x04\x00\x05\x00\x47\x00\x04\x00\x1f\x00\x4a\x00\x21\x00\x1e\x00\x4d\x00\x4e\x00\x4f\x00\x50\x00\x51\x00\x24\x00\x12\x00\x43\x00\x44\x00\x04\x00\x16\x00\x2a\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x1d\x00\x04\x00\x51\x00\x23\x00\x20\x00\x2e\x00\x26\x00\x30\x00\x21\x00\x29\x00\x27\x00\x04\x00\x2c\x00\x3b\x00\x3c\x00\x3d\x00\x2d\x00\x31\x00\x04\x00\x00\x00\x01\x00\x02\x00\x19\x00\x04\x00\x04\x00\x47\x00\x51\x00\x49\x00\x3c\x00\x3d\x00\x51\x00\x2e\x00\x2f\x00\x41\x00\x42\x00\x02\x00\x04\x00\x04\x00\x05\x00\x47\x00\x04\x00\x14\x00\x4a\x00\x04\x00\x1e\x00\x4d\x00\x4e\x00\x4f\x00\x50\x00\x51\x00\x4e\x00\x12\x00\x2d\x00\x51\x00\x28\x00\x16\x00\x51\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x2d\x00\x22\x00\x04\x00\x23\x00\x3e\x00\x0c\x00\x26\x00\x41\x00\x22\x00\x29\x00\x04\x00\x2c\x00\x2c\x00\x3b\x00\x3c\x00\x3d\x00\x2d\x00\x31\x00\x2c\x00\x1b\x00\x00\x00\x01\x00\x02\x00\x1e\x00\x04\x00\x47\x00\x1c\x00\x49\x00\x3c\x00\x3d\x00\x11\x00\x04\x00\x1a\x00\x41\x00\x42\x00\x02\x00\x26\x00\x04\x00\x05\x00\x47\x00\x04\x00\x10\x00\x4a\x00\x25\x00\x13\x00\x4d\x00\x4e\x00\x4f\x00\x50\x00\x51\x00\x04\x00\x12\x00\x2e\x00\x2f\x00\x04\x00\x16\x00\x1d\x00\x18\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x02\x00\x0d\x00\x27\x00\x05\x00\x23\x00\x21\x00\x00\x00\x26\x00\x2d\x00\x0b\x00\x16\x00\x14\x00\x0e\x00\x29\x00\x10\x00\x3b\x00\x12\x00\x13\x00\x24\x00\x21\x00\x16\x00\x17\x00\x42\x00\x04\x00\x04\x00\x2b\x00\x04\x00\x29\x00\x1e\x00\x3c\x00\x3d\x00\x21\x00\x0a\x00\x2b\x00\x41\x00\x42\x00\x2e\x00\x00\x00\x01\x00\x02\x00\x47\x00\x04\x00\x04\x00\x4a\x00\x18\x00\x19\x00\x4d\x00\x4e\x00\x4f\x00\x50\x00\x51\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x04\x00\x04\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x1b\x00\x2d\x00\x14\x00\x02\x00\x30\x00\x31\x00\x05\x00\x05\x00\x06\x00\x4a\x00\x53\x00\x4c\x00\x4d\x00\x4e\x00\x4f\x00\x0e\x00\x51\x00\x04\x00\x04\x00\x12\x00\x1f\x00\x20\x00\x04\x00\x16\x00\x17\x00\x23\x00\x00\x00\x01\x00\x02\x00\x14\x00\x04\x00\x1e\x00\x2a\x00\x3b\x00\x21\x00\x04\x00\x2e\x00\x2f\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x40\x00\x51\x00\x04\x00\x18\x00\x19\x00\x45\x00\x2d\x00\x40\x00\x04\x00\x30\x00\x31\x00\x1b\x00\x45\x00\x11\x00\x4e\x00\x4f\x00\x00\x00\x01\x00\x02\x00\x04\x00\x04\x00\x4e\x00\x4f\x00\x4a\x00\x04\x00\x15\x00\x4d\x00\x4e\x00\x4f\x00\x02\x00\x51\x00\x11\x00\x05\x00\x3b\x00\x13\x00\x02\x00\x15\x00\x51\x00\x05\x00\x0c\x00\x42\x00\x15\x00\x04\x00\x2d\x00\x0b\x00\x12\x00\x30\x00\x31\x00\x04\x00\x16\x00\x04\x00\x12\x00\x04\x00\x52\x00\x53\x00\x16\x00\x06\x00\x1e\x00\x02\x00\x15\x00\x21\x00\x05\x00\x2b\x00\x1e\x00\x02\x00\x2e\x00\x21\x00\x05\x00\x0c\x00\x13\x00\x18\x00\x19\x00\x04\x00\x14\x00\x12\x00\x3b\x00\x3c\x00\x3d\x00\x16\x00\x04\x00\x12\x00\x17\x00\x0b\x00\x04\x00\x16\x00\x10\x00\x1e\x00\x10\x00\x13\x00\x21\x00\x4a\x00\x4b\x00\x1e\x00\x2d\x00\x17\x00\x21\x00\x30\x00\x31\x00\x00\x00\x01\x00\x02\x00\x4a\x00\x04\x00\x04\x00\x4d\x00\x4e\x00\x4f\x00\x4a\x00\x51\x00\x04\x00\x4d\x00\x4e\x00\x4f\x00\x2d\x00\x51\x00\x04\x00\x30\x00\x31\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x04\x00\x04\x00\x05\x00\x04\x00\x00\x00\x01\x00\x02\x00\x4a\x00\x04\x00\x51\x00\x4d\x00\x4e\x00\x4f\x00\x4a\x00\x51\x00\x12\x00\x4d\x00\x4e\x00\x4f\x00\x16\x00\x51\x00\x04\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x04\x00\x20\x00\x04\x00\x05\x00\x04\x00\x2d\x00\x3b\x00\x26\x00\x30\x00\x31\x00\x04\x00\x0d\x00\x14\x00\x42\x00\x04\x00\x04\x00\x12\x00\x32\x00\x33\x00\x34\x00\x16\x00\x04\x00\x04\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x04\x00\x13\x00\x40\x00\x15\x00\x01\x00\x04\x00\x3b\x00\x26\x00\x04\x00\x05\x00\x07\x00\x08\x00\x09\x00\x42\x00\x4a\x00\x04\x00\x23\x00\x4d\x00\x4e\x00\x4f\x00\x50\x00\x51\x00\x12\x00\x2a\x00\x04\x00\x00\x00\x16\x00\x2e\x00\x2f\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x01\x00\x04\x00\x04\x00\x05\x00\x13\x00\x04\x00\x15\x00\x26\x00\x4a\x00\x08\x00\x09\x00\x4d\x00\x4e\x00\x4f\x00\x50\x00\x51\x00\x12\x00\x04\x00\x01\x00\x04\x00\x16\x00\x08\x00\x09\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1b\x00\x04\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x26\x00\x04\x00\x05\x00\x04\x00\x00\x00\x01\x00\x02\x00\x4a\x00\x04\x00\x04\x00\x4d\x00\x4e\x00\x4f\x00\x50\x00\x51\x00\x12\x00\x04\x00\x04\x00\x13\x00\x16\x00\x15\x00\x04\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x04\x00\x04\x00\x04\x00\x05\x00\x13\x00\x04\x00\x15\x00\x26\x00\x4a\x00\x0f\x00\x11\x00\x4d\x00\x4e\x00\x4f\x00\x50\x00\x51\x00\x12\x00\x32\x00\x33\x00\x34\x00\x16\x00\x0f\x00\x04\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x04\x00\x06\x00\x40\x00\x06\x00\x44\x00\x05\x00\x3b\x00\x26\x00\x04\x00\x05\x00\x51\x00\x00\x00\x01\x00\x02\x00\x4a\x00\x04\x00\x11\x00\x4d\x00\x4e\x00\x4f\x00\x50\x00\x51\x00\x12\x00\x04\x00\x4a\x00\x4c\x00\x16\x00\x13\x00\x37\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x06\x00\x06\x00\x04\x00\x05\x00\x4c\x00\x37\x00\x11\x00\x26\x00\x4a\x00\x08\x00\x1a\x00\x4d\x00\x4e\x00\x4f\x00\x50\x00\x51\x00\x12\x00\x4d\x00\x06\x00\x4a\x00\x16\x00\x25\x00\x51\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x08\x00\x2e\x00\x2f\x00\x51\x00\x11\x00\x20\x00\x3b\x00\x26\x00\x04\x00\x05\x00\x22\x00\x37\x00\x10\x00\x25\x00\x4a\x00\x51\x00\x4a\x00\x4d\x00\x4e\x00\x4f\x00\x50\x00\x51\x00\x12\x00\x2f\x00\x30\x00\x37\x00\x16\x00\x08\x00\x2c\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x49\x00\x13\x00\x04\x00\x05\x00\x3f\x00\x0e\x00\x2c\x00\x26\x00\x4a\x00\x44\x00\x51\x00\x4d\x00\x4e\x00\x4f\x00\x50\x00\x51\x00\x12\x00\x4b\x00\x04\x00\x4b\x00\x16\x00\x04\x00\x13\x00\x19\x00\x1a\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x00\x00\x01\x00\x02\x00\x0b\x00\x04\x00\x08\x00\x51\x00\x26\x00\x00\x00\x01\x00\x02\x00\x1a\x00\x04\x00\x20\x00\x4a\x00\x49\x00\x51\x00\x4d\x00\x4e\x00\x4f\x00\x50\x00\x51\x00\x25\x00\x23\x00\x13\x00\x00\x00\x01\x00\x02\x00\x51\x00\x04\x00\x2a\x00\x2e\x00\x2f\x00\x1e\x00\x2e\x00\x2f\x00\x0d\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x4a\x00\x4a\x00\x51\x00\x13\x00\x4d\x00\x4e\x00\x4f\x00\x50\x00\x51\x00\x20\x00\x51\x00\x2d\x00\x4a\x00\x0b\x00\x30\x00\x31\x00\x51\x00\x3b\x00\x3c\x00\x3d\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x3b\x00\x3c\x00\x3d\x00\x4c\x00\x11\x00\x0f\x00\x06\x00\x4a\x00\x4b\x00\x00\x00\x01\x00\x02\x00\x51\x00\x04\x00\x15\x00\x4a\x00\x4b\x00\x3b\x00\x3c\x00\x3d\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x4a\x00\x4b\x00\x40\x00\x2c\x00\x4c\x00\x4c\x00\x51\x00\x45\x00\x46\x00\x4c\x00\x48\x00\x20\x00\x13\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x4c\x00\x08\x00\x40\x00\x51\x00\x37\x00\x11\x00\x51\x00\x45\x00\x46\x00\x11\x00\x48\x00\x3b\x00\x3c\x00\x3d\x00\x11\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x00\x00\x01\x00\x02\x00\x13\x00\x04\x00\x10\x00\x13\x00\x40\x00\x11\x00\x11\x00\x43\x00\x44\x00\x45\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x13\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x13\x00\x40\x00\x0b\x00\x11\x00\x43\x00\x44\x00\x45\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x11\x00\x40\x00\x51\x00\x00\x00\x01\x00\x02\x00\x45\x00\x04\x00\x3b\x00\x3c\x00\x3d\x00\x11\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x32\x00\x40\x00\x51\x00\x00\x00\x01\x00\x02\x00\x45\x00\x04\x00\x3a\x00\x08\x00\x37\x00\x22\x00\x4a\x00\x36\x00\x40\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x36\x00\x10\x00\x51\x00\x04\x00\x4c\x00\x4c\x00\x40\x00\x11\x00\x4c\x00\x3b\x00\x3c\x00\x45\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x39\x00\x11\x00\x11\x00\x4c\x00\x51\x00\x4c\x00\x11\x00\x40\x00\x0d\x00\x4a\x00\x3b\x00\x3c\x00\x45\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x14\x00\x20\x00\x40\x00\x06\x00\x51\x00\x0e\x00\x15\x00\x45\x00\x07\x00\x0b\x00\x20\x00\x4c\x00\x13\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x11\x00\x51\x00\x40\x00\x4d\x00\x51\x00\x0e\x00\x4a\x00\x45\x00\x51\x00\x4e\x00\x51\x00\x0e\x00\x10\x00\x06\x00\x15\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x0b\x00\x10\x00\x36\x00\x20\x00\x0d\x00\x0b\x00\x51\x00\x40\x00\x0b\x00\x2c\x00\x0e\x00\x51\x00\x45\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x4c\x00\x11\x00\x40\x00\x11\x00\x13\x00\x11\x00\x51\x00\x45\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x13\x00\x13\x00\x40\x00\x00\x00\x51\x00\x53\x00\x4a\x00\x45\x00\x53\x00\x51\x00\x4a\x00\x4a\x00\x51\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x32\x00\x33\x00\x40\x00\x4a\x00\x0d\x00\x4b\x00\x53\x00\x45\x00\x0a\x00\x17\x00\x0e\x00\x4d\x00\x2e\x00\x2d\x00\x40\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x40\x00\xff\xff\xff\xff\xff\xff\xff\xff\x45\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\xff\xff\xff\xff\x40\x00\xff\xff\xff\xff\xff\xff\xff\xff\x45\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\xff\xff\xff\xff\x40\x00\xff\xff\xff\xff\xff\xff\xff\xff\x45\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x32\x00\x33\x00\x40\x00\xff\xff\xff\xff\xff\xff\xff\xff\x45\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x40\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x40\x00\xff\xff\xff\xff\xff\xff\xff\xff\x45\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\xff\xff\xff\xff\x40\x00\xff\xff\xff\xff\xff\xff\xff\xff\x45\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\xff\xff\xff\xff\x40\x00\xff\xff\xff\xff\xff\xff\xff\xff\x45\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x32\x00\xff\xff\x40\x00\xff\xff\xff\xff\xff\xff\xff\xff\x45\x00\x3a\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x40\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x40\x00\xff\xff\xff\xff\xff\xff\xff\xff\x45\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\xff\xff\xff\xff\x40\x00\xff\xff\xff\xff\xff\xff\xff\xff\x45\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\xff\xff\xff\xff\x40\x00\xff\xff\xff\xff\xff\xff\xff\xff\x45\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x32\x00\x33\x00\x40\x00\xff\xff\xff\xff\xff\xff\xff\xff\x45\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x40\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x40\x00\xff\xff\xff\xff\xff\xff\xff\xff\x45\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\xff\xff\xff\xff\x40\x00\xff\xff\xff\xff\xff\xff\xff\xff\x45\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\xff\xff\xff\xff\x40\x00\xff\xff\xff\xff\xff\xff\xff\xff\x45\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x32\x00\x33\x00\x40\x00\xff\xff\xff\xff\xff\xff\xff\xff\x45\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x40\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x40\x00\xff\xff\xff\xff\xff\xff\xff\xff\x45\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x40\x00\xff\xff\xff\xff\xff\xff\xff\xff\x45\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\xff\xff\xff\xff\x40\x00\xff\xff\xff\xff\xff\xff\xff\xff\x45\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x38\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\xff\xff\xff\xff\x40\x00\xff\xff\xff\xff\xff\xff\xff\xff\x45\x00\xff\xff\x04\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\x37\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x1a\x00\xff\xff\xff\xff\x40\x00\x00\x00\x01\x00\x02\x00\x03\x00\x04\x00\x04\x00\xff\xff\x25\x00\xff\xff\xff\xff\x32\x00\x33\x00\x34\x00\x35\x00\x36\x00\xff\xff\x2e\x00\x2f\x00\x04\x00\xff\xff\x04\x00\xff\xff\xff\xff\x04\x00\x40\x00\x32\x00\x33\x00\x34\x00\xff\xff\xff\xff\x32\x00\x33\x00\xff\xff\xff\xff\xff\xff\xff\xff\x23\x00\x04\x00\xff\xff\x40\x00\x1a\x00\x32\x00\x1a\x00\x2a\x00\x40\x00\x1a\x00\xff\xff\x2e\x00\x2f\x00\x04\x00\x32\x00\x25\x00\x04\x00\x25\x00\xff\xff\x40\x00\x25\x00\xff\xff\xff\xff\xff\xff\x2e\x00\x2f\x00\x2e\x00\x2f\x00\x40\x00\x2e\x00\x2f\x00\x37\x00\x23\x00\xff\xff\xff\xff\x1a\x00\x04\x00\xff\xff\x1a\x00\x2a\x00\x40\x00\xff\xff\xff\xff\x2e\x00\x2f\x00\x45\x00\x25\x00\xff\xff\xff\xff\x25\x00\x4a\x00\xff\xff\xff\xff\xff\xff\xff\xff\x2e\x00\x2f\x00\x51\x00\x2e\x00\x2f\x00\xff\xff\x1d\x00\x1e\x00\xff\xff\x24\x00\xff\xff\x26\x00\x27\x00\x28\x00\xff\xff\x2a\x00\x27\x00\x28\x00\xff\xff\xff\xff\xff\xff\xff\xff\x2d\x00\x32\x00\x33\x00\x34\x00\x35\x00\xff\xff\xff\xff\x38\x00\xff\xff\x3a\x00\x3b\x00\x3c\x00\xff\xff\x3e\x00\xff\xff\xff\xff\xff\xff\xff\xff\x43\x00\x44\x00\x24\x00\x46\x00\x26\x00\x27\x00\x28\x00\xff\xff\x2a\x00\x4c\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x32\x00\x33\x00\x34\x00\x35\x00\xff\xff\xff\xff\x38\x00\xff\xff\x3a\x00\x3b\x00\x3c\x00\xff\xff\x3e\x00\xff\xff\xff\xff\xff\xff\xff\xff\x43\x00\x44\x00\x24\x00\x46\x00\x26\x00\x27\x00\x28\x00\xff\xff\x2a\x00\x4c\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x32\x00\x33\x00\x34\x00\x35\x00\xff\xff\xff\xff\x38\x00\xff\xff\x3a\x00\x3b\x00\x3c\x00\xff\xff\x3e\x00\xff\xff\xff\xff\xff\xff\xff\xff\x43\x00\x44\x00\x24\x00\x46\x00\x26\x00\x27\x00\x28\x00\xff\xff\x2a\x00\x4c\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x32\x00\x33\x00\x34\x00\x35\x00\xff\xff\xff\xff\x38\x00\xff\xff\x3a\x00\x3b\x00\x3c\x00\xff\xff\x3e\x00\xff\xff\xff\xff\xff\xff\xff\xff\x43\x00\x44\x00\x24\x00\x46\x00\x26\x00\x27\x00\x28\x00\xff\xff\x2a\x00\x4c\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x32\x00\x33\x00\x34\x00\x35\x00\xff\xff\xff\xff\x38\x00\x04\x00\x3a\x00\x3b\x00\x3c\x00\xff\xff\x3e\x00\xff\xff\xff\xff\x04\x00\xff\xff\x43\x00\x44\x00\x10\x00\x46\x00\x12\x00\xff\xff\xff\xff\xff\xff\x0e\x00\xff\xff\x18\x00\x19\x00\x12\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x18\x00\x19\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"#

happyTable :: HappyAddr
happyTable = HappyA# "\x00\x00\x90\x00\x46\x00\xbe\xff\x46\x00\x47\x00\x46\x00\x47\x00\x46\x00\x47\x00\x46\x00\x47\x00\x46\x00\x47\x00\x62\x00\x47\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x54\x00\x83\x00\x9b\x01\xbc\x01\x9b\x01\xc1\x00\xca\x00\x84\x00\x85\x00\x86\x00\xf3\x00\x3c\x00\x7d\x01\x53\x01\xc1\x00\xc2\x01\x35\x01\x5f\x00\x67\x00\xab\x00\x87\x00\x68\x00\x86\x01\x1a\x02\x31\x00\x35\x01\x38\x00\x46\x00\x98\x01\xac\x00\xcc\xff\xa9\x01\x4b\x00\x37\x00\x4c\x00\x4d\x00\x73\x00\x74\x00\x75\x00\x2a\x01\x76\x00\xd3\x00\xc3\x01\xfc\x01\x2b\x01\x22\x02\xc7\x01\x8a\x00\x38\x00\xc1\x00\xcb\x00\x73\x00\x74\x00\x75\x00\x7d\x01\x76\x00\x31\x00\x63\x00\x45\x01\x31\x00\x13\x00\x16\x00\x8d\x00\x17\x00\x18\x00\x48\x00\xfd\x00\x48\x00\x49\x00\xe5\x00\xd2\x00\xe6\x00\x88\x00\xe7\x00\x7e\x01\xe9\x00\xc8\x01\x19\x00\x31\x00\x31\x00\x31\x00\x1a\x00\x37\x01\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x37\x01\x67\x00\xff\xff\x23\x00\xb9\x00\xc1\x00\x24\x00\x2e\x00\xd1\x00\x25\x00\x31\x00\xba\x00\x72\x00\x35\x01\x73\x00\x74\x00\x75\x00\x27\x00\x76\x00\xb9\x00\x2e\x00\xbb\x00\x69\x01\x5c\x01\x36\x01\xa0\x01\xd1\x01\x04\x01\x28\x00\x29\x00\x8e\x00\x5c\x00\x62\x00\x2a\x00\x2b\x00\x16\x00\x25\x01\x17\x00\x18\x00\x2c\x00\x21\x02\x21\x01\x2d\x00\x1d\x02\x19\x01\x07\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x04\x01\x19\x00\x98\x01\x22\x02\x62\x00\x1a\x00\x5c\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x22\x01\x1b\x02\xf2\x01\x23\x00\xab\x01\xd2\x00\x24\x00\x9c\x00\xb9\x00\x25\x00\xca\x01\x1a\x01\x26\x00\x31\x00\x37\x01\xba\x00\x25\x01\x27\x00\xc1\x01\x73\x00\x74\x00\x75\x00\x31\x00\xa0\x00\x9d\x00\xbb\x00\xbc\x00\x61\x01\x28\x00\x29\x00\x63\x00\xb5\x00\xec\x01\x2a\x00\x2b\x00\x16\x00\x31\x00\x17\x00\x18\x00\x2c\x00\x5c\x00\x66\x00\x2d\x00\x67\x00\x04\x01\x07\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x0b\x01\x19\x00\x63\x00\x64\x00\xfe\x00\x1a\x00\x0c\x01\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x16\x01\xf3\x00\x31\x00\x23\x00\x6a\x00\xae\x01\x24\x00\xaf\x01\x67\x00\x25\x00\xbe\x01\x9b\x00\x72\x00\xa1\x00\xa2\x00\xa3\x00\x18\x01\x27\x00\xc5\x01\x73\x00\x74\x00\x75\x00\xcd\x01\xa0\x00\x5c\x00\xa4\x00\x31\x00\x62\x01\x28\x00\x29\x00\x31\x00\x08\x01\xb6\x01\x2a\x00\x2b\x00\x16\x00\xb8\x01\x17\x00\x18\x00\x2c\x00\x5c\x00\x0f\x02\x2d\x00\xb8\x01\x1e\x01\x07\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x2e\x00\x19\x00\x9c\x00\x31\x00\xc6\x01\x1a\x00\x31\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\xa6\x01\xb9\x01\x21\x01\x23\x00\x9d\x00\xa3\x01\x24\x00\x9e\x00\xb9\x01\x25\x00\xfe\x00\xf8\x01\x26\x00\xa1\x00\xa2\x00\xa3\x00\x3d\x01\x27\x00\xba\x01\xd3\x00\x73\x00\x74\x00\x75\x00\xa4\x01\x76\x00\xa4\x00\x22\x01\xa5\x00\x28\x00\x29\x00\x10\x02\x5c\x00\xff\x00\x2a\x00\x2b\x00\x16\x00\x23\x01\x17\x00\x58\x00\x2c\x00\x0d\x01\x95\x01\x2d\x00\xb0\x01\x96\x01\x07\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x19\x01\x19\x00\x01\x01\x02\x01\x0d\x01\x1a\x00\x16\x01\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x79\x00\x31\x00\x17\x01\x7a\x00\x23\x00\x0e\x01\x02\x02\x24\x00\x18\x01\xc1\x00\x32\x00\x14\x02\x39\x01\xbc\x01\x7f\xff\xb9\x00\x7b\x00\x7f\xff\x1a\x01\x0e\x01\x7c\x00\x3a\x01\x96\x01\x5c\x00\xf3\x00\x1b\x01\x17\x02\x0f\x01\x7d\x00\x28\x00\x29\x00\x7e\x00\x18\x02\x3a\x00\x2a\x00\x2b\x00\x34\x00\x73\x00\x74\x00\x75\x00\x2c\x00\x76\x00\x06\x02\x2d\x00\xcf\x01\x7a\x01\x07\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\xc2\x01\xfe\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\xd3\x00\x50\x00\xf3\x01\x79\x00\x51\x00\x2e\x01\x7a\x00\x3a\x00\x3b\x00\x7f\x00\xf5\xff\xd2\x00\x07\x00\x2e\x00\x2f\x00\x39\x01\x31\x00\x5c\x00\xf9\x01\x7b\x00\xc3\x01\xc4\x01\xfb\x01\x7c\x00\x3a\x01\x06\x01\x73\x00\x74\x00\x75\x00\x00\x02\x76\x00\x7d\x00\xb5\x01\x6f\x01\x7e\x00\xf3\x00\x08\x01\x09\x01\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x6b\x01\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x6b\x01\x13\x00\xe3\x01\x5e\x01\x79\x01\x7a\x01\x14\x00\x50\x00\x13\x00\x98\x01\x51\x00\x5c\x01\xd3\x00\x14\x00\xe0\x01\x6c\x01\xd8\x01\x73\x00\x74\x00\x75\x00\x98\x01\xa0\x00\x6c\x01\x6d\x01\x7f\x00\x98\x01\x23\x02\x07\x00\x2e\x00\x2f\x00\x79\x00\x31\x00\xeb\x01\x7a\x00\xb9\x00\xf4\x01\x79\x00\xab\x01\xcb\x01\x7a\x00\xa7\x00\x37\x01\xe6\x01\x98\x01\x50\x00\x91\x01\x7b\x00\x51\x00\x52\x00\xe7\x01\x7c\x00\xf3\x00\x7b\x00\x5c\x00\x34\x00\x35\x00\x7c\x00\xf6\x01\x7d\x00\x79\x00\x99\x01\x7e\x00\x7a\x00\x3a\x00\x7d\x00\x79\x00\x34\x00\x7e\x00\x7a\x00\xa7\x00\xf7\x01\x9d\x01\x7a\x01\x4f\x00\x7f\x01\x7b\x00\xa1\x00\xa2\x00\xc5\x00\x7c\x00\xee\x01\x7b\x00\xac\x01\x14\xff\xc0\x01\x7c\x00\xcf\x00\x7d\x00\x14\xff\xd0\x00\x7e\x00\xc6\x00\x67\x01\x7d\x00\x50\x00\x8b\x00\x7e\x00\x51\x00\xbe\x00\x73\x00\x74\x00\x75\x00\x7f\x00\x76\x00\x63\x01\x07\x00\x2e\x00\x2f\x00\x7f\x00\x31\x00\x70\x01\x07\x00\x2e\x00\x2f\x00\x50\x00\x31\x00\x5c\x00\x51\x00\x52\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x7b\x01\x57\x00\xca\x01\x81\x01\x73\x00\x74\x00\x75\x00\x7f\x00\x76\x00\x83\x01\x07\x00\x2e\x00\x2f\x00\x7f\x00\x31\x00\x19\x00\x07\x00\x2e\x00\x2f\x00\x1a\x00\x31\x00\x93\x01\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x9b\x01\xdd\x01\x17\x00\x58\x00\x9c\x01\x50\x00\xb9\x00\x24\x00\x51\x00\x5d\x00\x9e\x01\x0e\xff\xa1\x01\x43\x01\xfe\x00\x98\x01\x19\x00\x0c\x00\x0d\x00\x95\x00\x1a\x00\x05\x01\x10\x01\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x2b\x01\xff\x01\x13\x00\xab\x01\x83\x00\x4f\x01\xb9\x00\x24\x00\x57\x00\xca\x01\x84\x00\x85\x00\x86\x00\x37\x01\x8d\x00\x50\x01\x06\x01\x07\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x19\x00\x8d\x01\x98\x01\x5d\x01\x1a\x00\x08\x01\x09\x01\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x9f\x00\xa8\x00\x57\x00\x58\x00\xaa\x01\x09\x02\xab\x01\x24\x00\x2d\x00\x0a\x02\x19\x02\x07\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x19\x00\x09\x02\xbd\x00\xc8\x00\x1a\x00\x0a\x02\x0b\x02\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\xd3\x00\xea\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x24\x00\x17\x00\x58\x00\x98\x01\x73\x00\x74\x00\x75\x00\x8d\x00\x76\x00\xeb\x00\x07\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x19\x00\xec\x00\x98\x01\xcc\x01\x1a\x00\xab\x01\xed\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\xee\x00\xef\x00\x57\x00\x58\x00\xce\x01\x3d\x00\xab\x01\x24\x00\x8d\x00\x3e\x00\x4d\x00\x07\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x19\x00\x0c\x00\x0d\x00\x96\x00\x1a\x00\x4e\x00\x6a\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x72\x00\x25\x02\x13\x00\x26\x02\x20\x02\x1f\x02\x53\x01\x24\x00\x17\x00\x58\x00\x31\x00\x73\x00\x74\x00\x75\x00\x2d\x00\x76\x00\x0e\x02\x07\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x19\x00\xfe\x00\x17\x02\x0d\x02\x1a\x00\x0f\x02\x81\x01\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x12\x02\x13\x02\x57\x00\x58\x00\x14\x02\x81\x01\x05\x02\x24\x00\x8d\x00\x02\x02\xff\x00\x07\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x19\x00\x07\x00\x06\x02\x08\x02\x1a\x00\x00\x01\x31\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x09\x02\x01\x01\x02\x01\x31\x00\xf0\x01\xf1\x01\x77\x00\x24\x00\x57\x00\x58\x00\x40\x00\x81\x01\xfe\x01\x41\x00\x2d\x00\x31\x00\xff\x01\x07\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x19\x00\x42\x00\x43\x00\x81\x01\x1a\x00\xda\x01\xdc\x01\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\xdb\x01\x86\x01\x17\x00\x58\x00\x44\x00\xe0\x01\xe2\x01\x24\x00\x8d\x00\x45\x00\x31\x00\x07\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x19\x00\xdf\x01\xfe\x00\xe3\x01\x1a\x00\xfe\x00\xe5\x01\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x73\x00\x74\x00\x75\x00\xe9\x01\xa0\x00\xea\x01\x31\x00\x24\x00\x73\x00\x74\x00\x75\x00\xff\x00\xc4\x00\xee\x01\x59\x00\xeb\x01\x31\x00\x07\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\x04\x01\x06\x01\xa6\x01\x73\x00\x74\x00\x75\x00\x31\x00\xa0\x00\x8e\x01\x01\x01\x02\x01\xa8\x01\x08\x01\x09\x01\xb0\x01\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\xa9\x01\x2d\x00\x31\x00\xb2\x01\x07\x00\x2e\x00\x2f\x00\x30\x00\x31\x00\xb5\x01\x31\x00\x50\x00\xbe\x01\x7d\x01\x51\x00\x52\x00\x31\x00\xa1\x00\xa2\x00\xc5\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\xa1\x00\xa2\x00\xc5\x00\xd3\x01\xd4\x01\xd5\x01\x65\x01\xc6\x00\x74\x01\x73\x00\x74\x00\x75\x00\x31\x00\xa0\x00\x66\x01\xc6\x00\xc7\x00\xa1\x00\xa2\x00\xc5\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x4b\x01\x07\x00\x08\x00\x09\x00\x0a\x00\x6e\x00\xc6\x00\x30\x01\x13\x00\x6b\x01\xd7\x01\x60\x01\x31\x00\x14\x00\x6c\x00\x77\x01\x4c\x01\x76\x01\x78\x01\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x6b\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x6e\x00\x79\x01\x7f\x01\x13\x00\x31\x00\x81\x01\x83\x01\x31\x00\x14\x00\x6c\x00\x85\x01\x6d\x00\xa1\x00\xa2\x00\x60\x01\x87\x01\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x6f\x00\x73\x00\x74\x00\x75\x00\x88\x01\xa0\x00\x89\x01\x8b\x01\x13\x00\x8a\x01\x8c\x01\x63\x00\xdd\x01\x14\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x6f\x00\x8d\x01\x07\x00\x08\x00\x09\x00\x0a\x00\x54\x00\x90\x01\x13\x00\x91\x01\x92\x01\x63\x00\x70\x00\x14\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\xc2\x00\x6e\x01\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x93\x01\x13\x00\x31\x00\x73\x00\x74\x00\x75\x00\x14\x00\xa0\x00\xa1\x00\xa2\x00\xa7\x00\x98\x01\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\xc2\x00\x31\x01\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\xb2\x00\x13\x00\x31\x00\x73\x00\x74\x00\x75\x00\x14\x00\xa0\x00\x49\x01\xa1\x01\x81\x01\xa5\x01\xf3\x00\xfb\x00\x13\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\xc2\x00\xc3\x00\xfc\x00\xfd\x00\x31\x00\xab\x00\x30\x01\x33\x01\x13\x00\x34\x01\x3b\x01\xa1\x00\x71\x01\x14\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\xc2\x00\xcb\x00\x3c\x01\x3d\x01\x40\x01\x31\x00\x41\x01\x42\x01\x13\x00\x43\x01\x45\x01\xa1\x00\x73\x01\x14\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x03\x02\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x48\x01\x49\x01\x13\x00\x4f\x01\x31\x00\x52\x01\x55\x01\x14\x00\x57\x01\x56\x01\x58\x01\x59\x01\x5b\x01\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\xf7\x01\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x5a\x01\x31\x00\x13\x00\x07\x00\x31\x00\x8a\x00\x91\x00\x14\x00\x31\x00\x2e\x00\x31\x00\xaa\x00\xae\x00\xaf\x00\xb0\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\xd7\x01\xb1\x00\xb2\x00\xb9\x00\xb5\x00\xb7\x00\xb8\x00\x31\x00\x13\x00\xc1\x00\xc0\x00\x8a\x00\x31\x00\x14\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\xe5\x01\x07\x00\x08\x00\x09\x00\x0a\x00\x54\x00\xcd\x00\xce\x00\x13\x00\xe9\x00\xd3\x00\x46\x00\x31\x00\x14\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\xb2\x01\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\xf1\x00\xf2\x00\x13\x00\xff\xff\x31\x00\xff\xff\x54\x00\x14\x00\xff\xff\x31\x00\x5a\x00\x5b\x00\x31\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\xb3\x01\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x88\x00\x13\x00\x61\x00\x80\x00\x81\x00\xff\xff\x14\x00\x82\x00\x8b\x00\x8a\x00\x07\x00\x34\x00\x37\x00\x13\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\xb7\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x13\x00\x00\x00\x00\x00\x00\x00\x00\x00\x14\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\xbf\x01\x07\x00\x08\x00\x09\x00\x0a\x00\xac\x00\x00\x00\x00\x00\x13\x00\x00\x00\x00\x00\x00\x00\x00\x00\x14\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\xd0\x01\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x00\x00\x00\x00\x13\x00\x00\x00\x00\x00\x00\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\xd5\x01\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x5f\x00\x13\x00\x00\x00\x00\x00\x00\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x13\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x66\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x13\x00\x00\x00\x00\x00\x00\x00\x00\x00\x14\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x68\x01\x07\x00\x08\x00\x09\x00\x0a\x00\x54\x00\x00\x00\x00\x00\x13\x00\x00\x00\x00\x00\x00\x00\x00\x00\x14\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x72\x01\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x00\x00\x00\x00\x13\x00\x00\x00\x00\x00\x00\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x2c\x01\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\xb2\x00\x00\x00\x13\x00\x00\x00\x00\x00\x00\x00\x00\x00\x14\x00\xb3\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x13\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x2d\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x13\x00\x00\x00\x00\x00\x00\x00\x00\x00\x14\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x3e\x01\x07\x00\x08\x00\x09\x00\x0a\x00\x54\x00\x00\x00\x00\x00\x13\x00\x00\x00\x00\x00\x00\x00\x00\x00\x14\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x46\x01\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x00\x00\x00\x00\x13\x00\x00\x00\x00\x00\x00\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x4a\x01\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x5b\x00\x13\x00\x00\x00\x00\x00\x00\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x13\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x4d\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x13\x00\x00\x00\x00\x00\x00\x00\x00\x00\x14\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x91\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x54\x00\x00\x00\x00\x00\x13\x00\x00\x00\x00\x00\x00\x00\x00\x00\x14\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x99\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x00\x00\x00\x00\x13\x00\x00\x00\x00\x00\x00\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x9a\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x5f\x00\x13\x00\x00\x00\x00\x00\x00\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x13\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\xc1\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x13\x00\x00\x00\x00\x00\x00\x00\x00\x00\x14\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x6f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x13\x00\x00\x00\x00\x00\x00\x00\x00\x00\x14\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x61\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x00\x00\x00\x00\x13\x00\x00\x00\x00\x00\x00\x00\x00\x00\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x11\x00\x12\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x00\x00\x00\x00\x13\x00\x00\x00\x00\x00\x00\x00\x00\x00\x14\x00\x00\x00\xfe\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x54\x00\x0c\x00\x0d\x00\x92\x00\x93\x00\x10\x00\x98\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x54\x00\xff\x00\x00\x00\x00\x00\x13\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x54\x00\xfe\x00\x00\x00\x0c\x01\x00\x00\x00\x00\x0c\x00\x0d\x00\x92\x00\x93\x00\x94\x00\x00\x00\x01\x01\x02\x01\xfe\x00\x00\x00\xfe\x00\x00\x00\x00\x00\xfe\x00\x13\x00\x0c\x00\x0d\x00\x97\x00\x00\x00\x00\x00\x0c\x00\x88\x00\x00\x00\x00\x00\x00\x00\x00\x00\x06\x01\xfe\x00\x00\x00\x13\x00\xff\x00\x8b\x00\xff\x00\x07\x01\x13\x00\xff\x00\x00\x00\x08\x01\x09\x01\xfe\x00\x55\x00\x11\x01\xfe\x00\x12\x01\x00\x00\x13\x00\x13\x01\x00\x00\x00\x00\x00\x00\x01\x01\x02\x01\x01\x01\x02\x01\x13\x00\x01\x01\x02\x01\xcc\xff\x06\x01\x00\x00\x00\x00\xff\x00\x1d\x01\x00\x00\xff\x00\x14\x01\xf9\x00\x00\x00\x00\x00\x08\x01\x09\x01\xfa\x00\x15\x01\x00\x00\x00\x00\x1c\x01\xcc\xff\x00\x00\x00\x00\x00\x00\x00\x00\x01\x01\x02\x01\x31\x00\x01\x01\x02\x01\x00\x00\x16\x01\x1e\x01\x00\x00\xd5\x00\x00\x00\xd6\x00\xd7\x00\xd8\x00\x00\x00\xd9\x00\x1f\x01\x20\x01\x00\x00\x00\x00\x00\x00\x00\x00\x18\x01\xda\x00\xdb\x00\xdc\x00\xdd\x00\x00\x00\x00\x00\xde\x00\x00\x00\xdf\x00\xe0\x00\xe1\x00\x00\x00\xe2\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe3\x00\xe4\x00\xd5\x00\xe5\x00\xd6\x00\xd7\x00\xd8\x00\x00\x00\xd9\x00\x1d\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xda\x00\xdb\x00\xdc\x00\xdd\x00\x00\x00\x00\x00\xde\x00\x00\x00\xdf\x00\xe0\x00\xe1\x00\x00\x00\xe2\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe3\x00\xe4\x00\xd5\x00\xe5\x00\xd6\x00\xd7\x00\xd8\x00\x00\x00\xd9\x00\x16\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xda\x00\xdb\x00\xdc\x00\xdd\x00\x00\x00\x00\x00\xde\x00\x00\x00\xdf\x00\xe0\x00\xe1\x00\x00\x00\xe2\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe3\x00\xe4\x00\xd5\x00\xe5\x00\xd6\x00\xd7\x00\xd8\x00\x00\x00\xd9\x00\xf2\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xda\x00\xdb\x00\xdc\x00\xdd\x00\x00\x00\x00\x00\xde\x00\x00\x00\xdf\x00\xe0\x00\xe1\x00\x00\x00\xe2\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe3\x00\xe4\x00\xd5\x00\xe5\x00\xd6\x00\xd7\x00\xd8\x00\x00\x00\xd9\x00\xfb\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xda\x00\xdb\x00\xdc\x00\xdd\x00\x00\x00\x00\x00\xde\x00\xf3\x00\xdf\x00\xe0\x00\xe1\x00\x00\x00\xe2\x00\x00\x00\x00\x00\xf3\x00\x00\x00\xe3\x00\xe4\x00\xf4\x00\xe5\x00\xf5\x00\x00\x00\x00\x00\x00\x00\x25\x01\x00\x00\xf6\x00\xf7\x00\x26\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x27\x01\x28\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

happyReduceArr = array (5, 275) [
	(5 , happyReduce_5),
	(6 , happyReduce_6),
	(7 , happyReduce_7),
	(8 , happyReduce_8),
	(9 , happyReduce_9),
	(10 , happyReduce_10),
	(11 , happyReduce_11),
	(12 , happyReduce_12),
	(13 , happyReduce_13),
	(14 , happyReduce_14),
	(15 , happyReduce_15),
	(16 , happyReduce_16),
	(17 , happyReduce_17),
	(18 , happyReduce_18),
	(19 , happyReduce_19),
	(20 , happyReduce_20),
	(21 , happyReduce_21),
	(22 , happyReduce_22),
	(23 , happyReduce_23),
	(24 , happyReduce_24),
	(25 , happyReduce_25),
	(26 , happyReduce_26),
	(27 , happyReduce_27),
	(28 , happyReduce_28),
	(29 , happyReduce_29),
	(30 , happyReduce_30),
	(31 , happyReduce_31),
	(32 , happyReduce_32),
	(33 , happyReduce_33),
	(34 , happyReduce_34),
	(35 , happyReduce_35),
	(36 , happyReduce_36),
	(37 , happyReduce_37),
	(38 , happyReduce_38),
	(39 , happyReduce_39),
	(40 , happyReduce_40),
	(41 , happyReduce_41),
	(42 , happyReduce_42),
	(43 , happyReduce_43),
	(44 , happyReduce_44),
	(45 , happyReduce_45),
	(46 , happyReduce_46),
	(47 , happyReduce_47),
	(48 , happyReduce_48),
	(49 , happyReduce_49),
	(50 , happyReduce_50),
	(51 , happyReduce_51),
	(52 , happyReduce_52),
	(53 , happyReduce_53),
	(54 , happyReduce_54),
	(55 , happyReduce_55),
	(56 , happyReduce_56),
	(57 , happyReduce_57),
	(58 , happyReduce_58),
	(59 , happyReduce_59),
	(60 , happyReduce_60),
	(61 , happyReduce_61),
	(62 , happyReduce_62),
	(63 , happyReduce_63),
	(64 , happyReduce_64),
	(65 , happyReduce_65),
	(66 , happyReduce_66),
	(67 , happyReduce_67),
	(68 , happyReduce_68),
	(69 , happyReduce_69),
	(70 , happyReduce_70),
	(71 , happyReduce_71),
	(72 , happyReduce_72),
	(73 , happyReduce_73),
	(74 , happyReduce_74),
	(75 , happyReduce_75),
	(76 , happyReduce_76),
	(77 , happyReduce_77),
	(78 , happyReduce_78),
	(79 , happyReduce_79),
	(80 , happyReduce_80),
	(81 , happyReduce_81),
	(82 , happyReduce_82),
	(83 , happyReduce_83),
	(84 , happyReduce_84),
	(85 , happyReduce_85),
	(86 , happyReduce_86),
	(87 , happyReduce_87),
	(88 , happyReduce_88),
	(89 , happyReduce_89),
	(90 , happyReduce_90),
	(91 , happyReduce_91),
	(92 , happyReduce_92),
	(93 , happyReduce_93),
	(94 , happyReduce_94),
	(95 , happyReduce_95),
	(96 , happyReduce_96),
	(97 , happyReduce_97),
	(98 , happyReduce_98),
	(99 , happyReduce_99),
	(100 , happyReduce_100),
	(101 , happyReduce_101),
	(102 , happyReduce_102),
	(103 , happyReduce_103),
	(104 , happyReduce_104),
	(105 , happyReduce_105),
	(106 , happyReduce_106),
	(107 , happyReduce_107),
	(108 , happyReduce_108),
	(109 , happyReduce_109),
	(110 , happyReduce_110),
	(111 , happyReduce_111),
	(112 , happyReduce_112),
	(113 , happyReduce_113),
	(114 , happyReduce_114),
	(115 , happyReduce_115),
	(116 , happyReduce_116),
	(117 , happyReduce_117),
	(118 , happyReduce_118),
	(119 , happyReduce_119),
	(120 , happyReduce_120),
	(121 , happyReduce_121),
	(122 , happyReduce_122),
	(123 , happyReduce_123),
	(124 , happyReduce_124),
	(125 , happyReduce_125),
	(126 , happyReduce_126),
	(127 , happyReduce_127),
	(128 , happyReduce_128),
	(129 , happyReduce_129),
	(130 , happyReduce_130),
	(131 , happyReduce_131),
	(132 , happyReduce_132),
	(133 , happyReduce_133),
	(134 , happyReduce_134),
	(135 , happyReduce_135),
	(136 , happyReduce_136),
	(137 , happyReduce_137),
	(138 , happyReduce_138),
	(139 , happyReduce_139),
	(140 , happyReduce_140),
	(141 , happyReduce_141),
	(142 , happyReduce_142),
	(143 , happyReduce_143),
	(144 , happyReduce_144),
	(145 , happyReduce_145),
	(146 , happyReduce_146),
	(147 , happyReduce_147),
	(148 , happyReduce_148),
	(149 , happyReduce_149),
	(150 , happyReduce_150),
	(151 , happyReduce_151),
	(152 , happyReduce_152),
	(153 , happyReduce_153),
	(154 , happyReduce_154),
	(155 , happyReduce_155),
	(156 , happyReduce_156),
	(157 , happyReduce_157),
	(158 , happyReduce_158),
	(159 , happyReduce_159),
	(160 , happyReduce_160),
	(161 , happyReduce_161),
	(162 , happyReduce_162),
	(163 , happyReduce_163),
	(164 , happyReduce_164),
	(165 , happyReduce_165),
	(166 , happyReduce_166),
	(167 , happyReduce_167),
	(168 , happyReduce_168),
	(169 , happyReduce_169),
	(170 , happyReduce_170),
	(171 , happyReduce_171),
	(172 , happyReduce_172),
	(173 , happyReduce_173),
	(174 , happyReduce_174),
	(175 , happyReduce_175),
	(176 , happyReduce_176),
	(177 , happyReduce_177),
	(178 , happyReduce_178),
	(179 , happyReduce_179),
	(180 , happyReduce_180),
	(181 , happyReduce_181),
	(182 , happyReduce_182),
	(183 , happyReduce_183),
	(184 , happyReduce_184),
	(185 , happyReduce_185),
	(186 , happyReduce_186),
	(187 , happyReduce_187),
	(188 , happyReduce_188),
	(189 , happyReduce_189),
	(190 , happyReduce_190),
	(191 , happyReduce_191),
	(192 , happyReduce_192),
	(193 , happyReduce_193),
	(194 , happyReduce_194),
	(195 , happyReduce_195),
	(196 , happyReduce_196),
	(197 , happyReduce_197),
	(198 , happyReduce_198),
	(199 , happyReduce_199),
	(200 , happyReduce_200),
	(201 , happyReduce_201),
	(202 , happyReduce_202),
	(203 , happyReduce_203),
	(204 , happyReduce_204),
	(205 , happyReduce_205),
	(206 , happyReduce_206),
	(207 , happyReduce_207),
	(208 , happyReduce_208),
	(209 , happyReduce_209),
	(210 , happyReduce_210),
	(211 , happyReduce_211),
	(212 , happyReduce_212),
	(213 , happyReduce_213),
	(214 , happyReduce_214),
	(215 , happyReduce_215),
	(216 , happyReduce_216),
	(217 , happyReduce_217),
	(218 , happyReduce_218),
	(219 , happyReduce_219),
	(220 , happyReduce_220),
	(221 , happyReduce_221),
	(222 , happyReduce_222),
	(223 , happyReduce_223),
	(224 , happyReduce_224),
	(225 , happyReduce_225),
	(226 , happyReduce_226),
	(227 , happyReduce_227),
	(228 , happyReduce_228),
	(229 , happyReduce_229),
	(230 , happyReduce_230),
	(231 , happyReduce_231),
	(232 , happyReduce_232),
	(233 , happyReduce_233),
	(234 , happyReduce_234),
	(235 , happyReduce_235),
	(236 , happyReduce_236),
	(237 , happyReduce_237),
	(238 , happyReduce_238),
	(239 , happyReduce_239),
	(240 , happyReduce_240),
	(241 , happyReduce_241),
	(242 , happyReduce_242),
	(243 , happyReduce_243),
	(244 , happyReduce_244),
	(245 , happyReduce_245),
	(246 , happyReduce_246),
	(247 , happyReduce_247),
	(248 , happyReduce_248),
	(249 , happyReduce_249),
	(250 , happyReduce_250),
	(251 , happyReduce_251),
	(252 , happyReduce_252),
	(253 , happyReduce_253),
	(254 , happyReduce_254),
	(255 , happyReduce_255),
	(256 , happyReduce_256),
	(257 , happyReduce_257),
	(258 , happyReduce_258),
	(259 , happyReduce_259),
	(260 , happyReduce_260),
	(261 , happyReduce_261),
	(262 , happyReduce_262),
	(263 , happyReduce_263),
	(264 , happyReduce_264),
	(265 , happyReduce_265),
	(266 , happyReduce_266),
	(267 , happyReduce_267),
	(268 , happyReduce_268),
	(269 , happyReduce_269),
	(270 , happyReduce_270),
	(271 , happyReduce_271),
	(272 , happyReduce_272),
	(273 , happyReduce_273),
	(274 , happyReduce_274),
	(275 , happyReduce_275)
	]

happy_n_terms = 84 :: Int
happy_n_nonterms = 86 :: Int

happyReduce_5 = happySpecReduce_1  0# happyReduction_5
happyReduction_5 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TI happy_var_1)) -> 
	happyIn8
		 ((read (BS.unpack happy_var_1)) :: Integer
	)}

happyReduce_6 = happySpecReduce_1  1# happyReduction_6
happyReduction_6 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TL happy_var_1)) -> 
	happyIn9
		 (BS.unpack happy_var_1
	)}

happyReduce_7 = happySpecReduce_1  2# happyReduction_7
happyReduction_7 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TD happy_var_1)) -> 
	happyIn10
		 ((read (BS.unpack happy_var_1)) :: Double
	)}

happyReduce_8 = happySpecReduce_1  3# happyReduction_8
happyReduction_8 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (T_LString happy_var_1)) -> 
	happyIn11
		 (LString (happy_var_1)
	)}

happyReduce_9 = happySpecReduce_1  4# happyReduction_9
happyReduction_9 happy_x_1
	 =  case happyOutTok happy_x_1 of { happy_var_1 -> 
	happyIn12
		 (PIdent (mkPosToken happy_var_1)
	)}

happyReduce_10 = happySpecReduce_1  5# happyReduction_10
happyReduction_10 happy_x_1
	 =  case happyOut14 happy_x_1 of { happy_var_1 -> 
	happyIn13
		 (Gr (reverse happy_var_1)
	)}

happyReduce_11 = happySpecReduce_0  6# happyReduction_11
happyReduction_11  =  happyIn14
		 ([]
	)

happyReduce_12 = happySpecReduce_2  6# happyReduction_12
happyReduction_12 happy_x_2
	happy_x_1
	 =  case happyOut14 happy_x_1 of { happy_var_1 -> 
	case happyOut15 happy_x_2 of { happy_var_2 -> 
	happyIn14
		 (flip (:) happy_var_1 happy_var_2
	)}}

happyReduce_13 = happySpecReduce_2  7# happyReduction_13
happyReduction_13 happy_x_2
	happy_x_1
	 =  case happyOut15 happy_x_1 of { happy_var_1 -> 
	happyIn15
		 (happy_var_1
	)}

happyReduce_14 = happyReduce 10# 7# happyReduction_14
happyReduction_14 (happy_x_10 `HappyStk`
	happy_x_9 `HappyStk`
	happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut12 happy_x_2 of { happy_var_2 -> 
	case happyOut12 happy_x_7 of { happy_var_7 -> 
	case happyOut17 happy_x_9 of { happy_var_9 -> 
	happyIn15
		 (MMain happy_var_2 happy_var_7 happy_var_9
	) `HappyStk` happyRest}}}

happyReduce_15 = happyReduce 4# 7# happyReduction_15
happyReduction_15 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut30 happy_x_1 of { happy_var_1 -> 
	case happyOut23 happy_x_2 of { happy_var_2 -> 
	case happyOut24 happy_x_4 of { happy_var_4 -> 
	happyIn15
		 (MModule happy_var_1 happy_var_2 happy_var_4
	) `HappyStk` happyRest}}}

happyReduce_16 = happySpecReduce_3  8# happyReduction_16
happyReduction_16 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	case happyOut18 happy_x_3 of { happy_var_3 -> 
	happyIn16
		 (ConcSpec happy_var_1 happy_var_3
	)}}

happyReduce_17 = happySpecReduce_0  9# happyReduction_17
happyReduction_17  =  happyIn17
		 ([]
	)

happyReduce_18 = happySpecReduce_1  9# happyReduction_18
happyReduction_18 happy_x_1
	 =  case happyOut16 happy_x_1 of { happy_var_1 -> 
	happyIn17
		 ((:[]) happy_var_1
	)}

happyReduce_19 = happySpecReduce_3  9# happyReduction_19
happyReduction_19 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut16 happy_x_1 of { happy_var_1 -> 
	case happyOut17 happy_x_3 of { happy_var_3 -> 
	happyIn17
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_20 = happySpecReduce_2  10# happyReduction_20
happyReduction_20 happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	case happyOut19 happy_x_2 of { happy_var_2 -> 
	happyIn18
		 (ConcExp happy_var_1 (reverse happy_var_2)
	)}}

happyReduce_21 = happySpecReduce_0  11# happyReduction_21
happyReduction_21  =  happyIn19
		 ([]
	)

happyReduce_22 = happySpecReduce_2  11# happyReduction_22
happyReduction_22 happy_x_2
	happy_x_1
	 =  case happyOut19 happy_x_1 of { happy_var_1 -> 
	case happyOut20 happy_x_2 of { happy_var_2 -> 
	happyIn19
		 (flip (:) happy_var_1 happy_var_2
	)}}

happyReduce_23 = happyReduce 5# 12# happyReduction_23
happyReduction_23 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut29 happy_x_4 of { happy_var_4 -> 
	happyIn20
		 (TransferIn happy_var_4
	) `HappyStk` happyRest}

happyReduce_24 = happyReduce 5# 12# happyReduction_24
happyReduction_24 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut29 happy_x_4 of { happy_var_4 -> 
	happyIn20
		 (TransferOut happy_var_4
	) `HappyStk` happyRest}

happyReduce_25 = happyReduce 4# 13# happyReduction_25
happyReduction_25 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut30 happy_x_1 of { happy_var_1 -> 
	case happyOut23 happy_x_2 of { happy_var_2 -> 
	case happyOut22 happy_x_4 of { happy_var_4 -> 
	happyIn21
		 (MModule2 happy_var_1 happy_var_2 happy_var_4
	) `HappyStk` happyRest}}}

happyReduce_26 = happySpecReduce_2  14# happyReduction_26
happyReduction_26 happy_x_2
	happy_x_1
	 =  case happyOut26 happy_x_1 of { happy_var_1 -> 
	case happyOut28 happy_x_2 of { happy_var_2 -> 
	happyIn22
		 (MBody2 happy_var_1 happy_var_2
	)}}

happyReduce_27 = happySpecReduce_1  14# happyReduction_27
happyReduction_27 happy_x_1
	 =  case happyOut32 happy_x_1 of { happy_var_1 -> 
	happyIn22
		 (MNoBody2 happy_var_1
	)}

happyReduce_28 = happySpecReduce_3  14# happyReduction_28
happyReduction_28 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut33 happy_x_1 of { happy_var_1 -> 
	case happyOut27 happy_x_3 of { happy_var_3 -> 
	happyIn22
		 (MWith2 happy_var_1 happy_var_3
	)}}

happyReduce_29 = happyReduce 5# 14# happyReduction_29
happyReduction_29 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut33 happy_x_1 of { happy_var_1 -> 
	case happyOut27 happy_x_3 of { happy_var_3 -> 
	case happyOut28 happy_x_5 of { happy_var_5 -> 
	happyIn22
		 (MWithBody2 happy_var_1 happy_var_3 happy_var_5
	) `HappyStk` happyRest}}}

happyReduce_30 = happyReduce 5# 14# happyReduction_30
happyReduction_30 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut32 happy_x_1 of { happy_var_1 -> 
	case happyOut33 happy_x_3 of { happy_var_3 -> 
	case happyOut27 happy_x_5 of { happy_var_5 -> 
	happyIn22
		 (MWithE2 happy_var_1 happy_var_3 happy_var_5
	) `HappyStk` happyRest}}}

happyReduce_31 = happyReduce 7# 14# happyReduction_31
happyReduction_31 (happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut32 happy_x_1 of { happy_var_1 -> 
	case happyOut33 happy_x_3 of { happy_var_3 -> 
	case happyOut27 happy_x_5 of { happy_var_5 -> 
	case happyOut28 happy_x_7 of { happy_var_7 -> 
	happyIn22
		 (MWithEBody2 happy_var_1 happy_var_3 happy_var_5 happy_var_7
	) `HappyStk` happyRest}}}}

happyReduce_32 = happySpecReduce_2  14# happyReduction_32
happyReduction_32 happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_2 of { happy_var_2 -> 
	happyIn22
		 (MReuse2 happy_var_2
	)}

happyReduce_33 = happySpecReduce_2  14# happyReduction_33
happyReduction_33 happy_x_2
	happy_x_1
	 =  case happyOut32 happy_x_2 of { happy_var_2 -> 
	happyIn22
		 (MUnion2 happy_var_2
	)}

happyReduce_34 = happySpecReduce_2  15# happyReduction_34
happyReduction_34 happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_2 of { happy_var_2 -> 
	happyIn23
		 (MTAbstract happy_var_2
	)}

happyReduce_35 = happySpecReduce_2  15# happyReduction_35
happyReduction_35 happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_2 of { happy_var_2 -> 
	happyIn23
		 (MTResource happy_var_2
	)}

happyReduce_36 = happySpecReduce_2  15# happyReduction_36
happyReduction_36 happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_2 of { happy_var_2 -> 
	happyIn23
		 (MTInterface happy_var_2
	)}

happyReduce_37 = happyReduce 4# 15# happyReduction_37
happyReduction_37 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut12 happy_x_2 of { happy_var_2 -> 
	case happyOut12 happy_x_4 of { happy_var_4 -> 
	happyIn23
		 (MTConcrete happy_var_2 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_38 = happyReduce 4# 15# happyReduction_38
happyReduction_38 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut12 happy_x_2 of { happy_var_2 -> 
	case happyOut12 happy_x_4 of { happy_var_4 -> 
	happyIn23
		 (MTInstance happy_var_2 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_39 = happyReduce 6# 15# happyReduction_39
happyReduction_39 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut12 happy_x_2 of { happy_var_2 -> 
	case happyOut29 happy_x_4 of { happy_var_4 -> 
	case happyOut29 happy_x_6 of { happy_var_6 -> 
	happyIn23
		 (MTTransfer happy_var_2 happy_var_4 happy_var_6
	) `HappyStk` happyRest}}}

happyReduce_40 = happyReduce 5# 16# happyReduction_40
happyReduction_40 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut26 happy_x_1 of { happy_var_1 -> 
	case happyOut28 happy_x_2 of { happy_var_2 -> 
	case happyOut25 happy_x_4 of { happy_var_4 -> 
	happyIn24
		 (MBody happy_var_1 happy_var_2 (reverse happy_var_4)
	) `HappyStk` happyRest}}}

happyReduce_41 = happySpecReduce_1  16# happyReduction_41
happyReduction_41 happy_x_1
	 =  case happyOut32 happy_x_1 of { happy_var_1 -> 
	happyIn24
		 (MNoBody happy_var_1
	)}

happyReduce_42 = happySpecReduce_3  16# happyReduction_42
happyReduction_42 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut33 happy_x_1 of { happy_var_1 -> 
	case happyOut27 happy_x_3 of { happy_var_3 -> 
	happyIn24
		 (MWith happy_var_1 happy_var_3
	)}}

happyReduce_43 = happyReduce 8# 16# happyReduction_43
happyReduction_43 (happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut33 happy_x_1 of { happy_var_1 -> 
	case happyOut27 happy_x_3 of { happy_var_3 -> 
	case happyOut28 happy_x_5 of { happy_var_5 -> 
	case happyOut25 happy_x_7 of { happy_var_7 -> 
	happyIn24
		 (MWithBody happy_var_1 happy_var_3 happy_var_5 (reverse happy_var_7)
	) `HappyStk` happyRest}}}}

happyReduce_44 = happyReduce 5# 16# happyReduction_44
happyReduction_44 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut32 happy_x_1 of { happy_var_1 -> 
	case happyOut33 happy_x_3 of { happy_var_3 -> 
	case happyOut27 happy_x_5 of { happy_var_5 -> 
	happyIn24
		 (MWithE happy_var_1 happy_var_3 happy_var_5
	) `HappyStk` happyRest}}}

happyReduce_45 = happyReduce 10# 16# happyReduction_45
happyReduction_45 (happy_x_10 `HappyStk`
	happy_x_9 `HappyStk`
	happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut32 happy_x_1 of { happy_var_1 -> 
	case happyOut33 happy_x_3 of { happy_var_3 -> 
	case happyOut27 happy_x_5 of { happy_var_5 -> 
	case happyOut28 happy_x_7 of { happy_var_7 -> 
	case happyOut25 happy_x_9 of { happy_var_9 -> 
	happyIn24
		 (MWithEBody happy_var_1 happy_var_3 happy_var_5 happy_var_7 (reverse happy_var_9)
	) `HappyStk` happyRest}}}}}

happyReduce_46 = happySpecReduce_2  16# happyReduction_46
happyReduction_46 happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_2 of { happy_var_2 -> 
	happyIn24
		 (MReuse happy_var_2
	)}

happyReduce_47 = happySpecReduce_2  16# happyReduction_47
happyReduction_47 happy_x_2
	happy_x_1
	 =  case happyOut32 happy_x_2 of { happy_var_2 -> 
	happyIn24
		 (MUnion happy_var_2
	)}

happyReduce_48 = happySpecReduce_0  17# happyReduction_48
happyReduction_48  =  happyIn25
		 ([]
	)

happyReduce_49 = happySpecReduce_2  17# happyReduction_49
happyReduction_49 happy_x_2
	happy_x_1
	 =  case happyOut25 happy_x_1 of { happy_var_1 -> 
	case happyOut35 happy_x_2 of { happy_var_2 -> 
	happyIn25
		 (flip (:) happy_var_1 happy_var_2
	)}}

happyReduce_50 = happySpecReduce_2  18# happyReduction_50
happyReduction_50 happy_x_2
	happy_x_1
	 =  case happyOut32 happy_x_1 of { happy_var_1 -> 
	happyIn26
		 (Ext happy_var_1
	)}

happyReduce_51 = happySpecReduce_0  18# happyReduction_51
happyReduction_51  =  happyIn26
		 (NoExt
	)

happyReduce_52 = happySpecReduce_0  19# happyReduction_52
happyReduction_52  =  happyIn27
		 ([]
	)

happyReduce_53 = happySpecReduce_1  19# happyReduction_53
happyReduction_53 happy_x_1
	 =  case happyOut29 happy_x_1 of { happy_var_1 -> 
	happyIn27
		 ((:[]) happy_var_1
	)}

happyReduce_54 = happySpecReduce_3  19# happyReduction_54
happyReduction_54 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut29 happy_x_1 of { happy_var_1 -> 
	case happyOut27 happy_x_3 of { happy_var_3 -> 
	happyIn27
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_55 = happySpecReduce_0  20# happyReduction_55
happyReduction_55  =  happyIn28
		 (NoOpens
	)

happyReduce_56 = happySpecReduce_3  20# happyReduction_56
happyReduction_56 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut27 happy_x_2 of { happy_var_2 -> 
	happyIn28
		 (OpenIn happy_var_2
	)}

happyReduce_57 = happySpecReduce_1  21# happyReduction_57
happyReduction_57 happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	happyIn29
		 (OName happy_var_1
	)}

happyReduce_58 = happyReduce 4# 21# happyReduction_58
happyReduction_58 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut31 happy_x_2 of { happy_var_2 -> 
	case happyOut12 happy_x_3 of { happy_var_3 -> 
	happyIn29
		 (OQualQO happy_var_2 happy_var_3
	) `HappyStk` happyRest}}

happyReduce_59 = happyReduce 6# 21# happyReduction_59
happyReduction_59 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut31 happy_x_2 of { happy_var_2 -> 
	case happyOut12 happy_x_3 of { happy_var_3 -> 
	case happyOut12 happy_x_5 of { happy_var_5 -> 
	happyIn29
		 (OQual happy_var_2 happy_var_3 happy_var_5
	) `HappyStk` happyRest}}}

happyReduce_60 = happySpecReduce_0  22# happyReduction_60
happyReduction_60  =  happyIn30
		 (CMCompl
	)

happyReduce_61 = happySpecReduce_1  22# happyReduction_61
happyReduction_61 happy_x_1
	 =  happyIn30
		 (CMIncompl
	)

happyReduce_62 = happySpecReduce_0  23# happyReduction_62
happyReduction_62  =  happyIn31
		 (QOCompl
	)

happyReduce_63 = happySpecReduce_1  23# happyReduction_63
happyReduction_63 happy_x_1
	 =  happyIn31
		 (QOIncompl
	)

happyReduce_64 = happySpecReduce_1  23# happyReduction_64
happyReduction_64 happy_x_1
	 =  happyIn31
		 (QOInterface
	)

happyReduce_65 = happySpecReduce_0  24# happyReduction_65
happyReduction_65  =  happyIn32
		 ([]
	)

happyReduce_66 = happySpecReduce_1  24# happyReduction_66
happyReduction_66 happy_x_1
	 =  case happyOut33 happy_x_1 of { happy_var_1 -> 
	happyIn32
		 ((:[]) happy_var_1
	)}

happyReduce_67 = happySpecReduce_3  24# happyReduction_67
happyReduction_67 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut33 happy_x_1 of { happy_var_1 -> 
	case happyOut32 happy_x_3 of { happy_var_3 -> 
	happyIn32
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_68 = happySpecReduce_1  25# happyReduction_68
happyReduction_68 happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	happyIn33
		 (IAll happy_var_1
	)}

happyReduce_69 = happyReduce 4# 25# happyReduction_69
happyReduction_69 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut12 happy_x_1 of { happy_var_1 -> 
	case happyOut53 happy_x_3 of { happy_var_3 -> 
	happyIn33
		 (ISome happy_var_1 happy_var_3
	) `HappyStk` happyRest}}

happyReduce_70 = happyReduce 5# 25# happyReduction_70
happyReduction_70 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut12 happy_x_1 of { happy_var_1 -> 
	case happyOut53 happy_x_4 of { happy_var_4 -> 
	happyIn33
		 (IMinus happy_var_1 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_71 = happySpecReduce_3  26# happyReduction_71
happyReduction_71 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut55 happy_x_1 of { happy_var_1 -> 
	case happyOut64 happy_x_3 of { happy_var_3 -> 
	happyIn34
		 (DDecl happy_var_1 happy_var_3
	)}}

happyReduce_72 = happySpecReduce_3  26# happyReduction_72
happyReduction_72 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut55 happy_x_1 of { happy_var_1 -> 
	case happyOut64 happy_x_3 of { happy_var_3 -> 
	happyIn34
		 (DDef happy_var_1 happy_var_3
	)}}

happyReduce_73 = happyReduce 4# 26# happyReduction_73
happyReduction_73 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut54 happy_x_1 of { happy_var_1 -> 
	case happyOut74 happy_x_2 of { happy_var_2 -> 
	case happyOut64 happy_x_4 of { happy_var_4 -> 
	happyIn34
		 (DPatt happy_var_1 happy_var_2 happy_var_4
	) `HappyStk` happyRest}}}

happyReduce_74 = happyReduce 5# 26# happyReduction_74
happyReduction_74 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut55 happy_x_1 of { happy_var_1 -> 
	case happyOut64 happy_x_3 of { happy_var_3 -> 
	case happyOut64 happy_x_5 of { happy_var_5 -> 
	happyIn34
		 (DFull happy_var_1 happy_var_3 happy_var_5
	) `HappyStk` happyRest}}}

happyReduce_75 = happySpecReduce_2  27# happyReduction_75
happyReduction_75 happy_x_2
	happy_x_1
	 =  case happyOut46 happy_x_2 of { happy_var_2 -> 
	happyIn35
		 (DefCat happy_var_2
	)}

happyReduce_76 = happySpecReduce_2  27# happyReduction_76
happyReduction_76 happy_x_2
	happy_x_1
	 =  case happyOut47 happy_x_2 of { happy_var_2 -> 
	happyIn35
		 (DefFun happy_var_2
	)}

happyReduce_77 = happySpecReduce_2  27# happyReduction_77
happyReduction_77 happy_x_2
	happy_x_1
	 =  case happyOut47 happy_x_2 of { happy_var_2 -> 
	happyIn35
		 (DefFunData happy_var_2
	)}

happyReduce_78 = happySpecReduce_2  27# happyReduction_78
happyReduction_78 happy_x_2
	happy_x_1
	 =  case happyOut45 happy_x_2 of { happy_var_2 -> 
	happyIn35
		 (DefDef happy_var_2
	)}

happyReduce_79 = happySpecReduce_2  27# happyReduction_79
happyReduction_79 happy_x_2
	happy_x_1
	 =  case happyOut48 happy_x_2 of { happy_var_2 -> 
	happyIn35
		 (DefData happy_var_2
	)}

happyReduce_80 = happySpecReduce_2  27# happyReduction_80
happyReduction_80 happy_x_2
	happy_x_1
	 =  case happyOut45 happy_x_2 of { happy_var_2 -> 
	happyIn35
		 (DefTrans happy_var_2
	)}

happyReduce_81 = happySpecReduce_2  27# happyReduction_81
happyReduction_81 happy_x_2
	happy_x_1
	 =  case happyOut49 happy_x_2 of { happy_var_2 -> 
	happyIn35
		 (DefPar happy_var_2
	)}

happyReduce_82 = happySpecReduce_2  27# happyReduction_82
happyReduction_82 happy_x_2
	happy_x_1
	 =  case happyOut45 happy_x_2 of { happy_var_2 -> 
	happyIn35
		 (DefOper happy_var_2
	)}

happyReduce_83 = happySpecReduce_2  27# happyReduction_83
happyReduction_83 happy_x_2
	happy_x_1
	 =  case happyOut50 happy_x_2 of { happy_var_2 -> 
	happyIn35
		 (DefLincat happy_var_2
	)}

happyReduce_84 = happySpecReduce_2  27# happyReduction_84
happyReduction_84 happy_x_2
	happy_x_1
	 =  case happyOut45 happy_x_2 of { happy_var_2 -> 
	happyIn35
		 (DefLindef happy_var_2
	)}

happyReduce_85 = happySpecReduce_2  27# happyReduction_85
happyReduction_85 happy_x_2
	happy_x_1
	 =  case happyOut45 happy_x_2 of { happy_var_2 -> 
	happyIn35
		 (DefLin happy_var_2
	)}

happyReduce_86 = happySpecReduce_3  27# happyReduction_86
happyReduction_86 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut50 happy_x_3 of { happy_var_3 -> 
	happyIn35
		 (DefPrintCat happy_var_3
	)}

happyReduce_87 = happySpecReduce_3  27# happyReduction_87
happyReduction_87 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut50 happy_x_3 of { happy_var_3 -> 
	happyIn35
		 (DefPrintFun happy_var_3
	)}

happyReduce_88 = happySpecReduce_2  27# happyReduction_88
happyReduction_88 happy_x_2
	happy_x_1
	 =  case happyOut51 happy_x_2 of { happy_var_2 -> 
	happyIn35
		 (DefFlag happy_var_2
	)}

happyReduce_89 = happySpecReduce_2  27# happyReduction_89
happyReduction_89 happy_x_2
	happy_x_1
	 =  case happyOut50 happy_x_2 of { happy_var_2 -> 
	happyIn35
		 (DefPrintOld happy_var_2
	)}

happyReduce_90 = happySpecReduce_2  27# happyReduction_90
happyReduction_90 happy_x_2
	happy_x_1
	 =  case happyOut45 happy_x_2 of { happy_var_2 -> 
	happyIn35
		 (DefLintype happy_var_2
	)}

happyReduce_91 = happySpecReduce_2  27# happyReduction_91
happyReduction_91 happy_x_2
	happy_x_1
	 =  case happyOut45 happy_x_2 of { happy_var_2 -> 
	happyIn35
		 (DefPattern happy_var_2
	)}

happyReduce_92 = happyReduce 7# 27# happyReduction_92
happyReduction_92 (happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut12 happy_x_2 of { happy_var_2 -> 
	case happyOut25 happy_x_5 of { happy_var_5 -> 
	happyIn35
		 (DefPackage happy_var_2 (reverse happy_var_5)
	) `HappyStk` happyRest}}

happyReduce_93 = happySpecReduce_2  27# happyReduction_93
happyReduction_93 happy_x_2
	happy_x_1
	 =  case happyOut45 happy_x_2 of { happy_var_2 -> 
	happyIn35
		 (DefVars happy_var_2
	)}

happyReduce_94 = happySpecReduce_3  27# happyReduction_94
happyReduction_94 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_2 of { happy_var_2 -> 
	happyIn35
		 (DefTokenizer happy_var_2
	)}

happyReduce_95 = happySpecReduce_2  28# happyReduction_95
happyReduction_95 happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	case happyOut89 happy_x_2 of { happy_var_2 -> 
	happyIn36
		 (SimpleCatDef happy_var_1 (reverse happy_var_2)
	)}}

happyReduce_96 = happyReduce 4# 28# happyReduction_96
happyReduction_96 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut12 happy_x_2 of { happy_var_2 -> 
	case happyOut89 happy_x_3 of { happy_var_3 -> 
	happyIn36
		 (ListCatDef happy_var_2 (reverse happy_var_3)
	) `HappyStk` happyRest}}

happyReduce_97 = happyReduce 7# 28# happyReduction_97
happyReduction_97 (happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut12 happy_x_2 of { happy_var_2 -> 
	case happyOut89 happy_x_3 of { happy_var_3 -> 
	case happyOut8 happy_x_6 of { happy_var_6 -> 
	happyIn36
		 (ListSizeCatDef happy_var_2 (reverse happy_var_3) happy_var_6
	) `HappyStk` happyRest}}}

happyReduce_98 = happySpecReduce_3  29# happyReduction_98
happyReduction_98 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut53 happy_x_1 of { happy_var_1 -> 
	case happyOut64 happy_x_3 of { happy_var_3 -> 
	happyIn37
		 (FunDef happy_var_1 happy_var_3
	)}}

happyReduce_99 = happySpecReduce_3  30# happyReduction_99
happyReduction_99 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	case happyOut40 happy_x_3 of { happy_var_3 -> 
	happyIn38
		 (DataDef happy_var_1 happy_var_3
	)}}

happyReduce_100 = happySpecReduce_1  31# happyReduction_100
happyReduction_100 happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	happyIn39
		 (DataId happy_var_1
	)}

happyReduce_101 = happySpecReduce_3  31# happyReduction_101
happyReduction_101 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	case happyOut12 happy_x_3 of { happy_var_3 -> 
	happyIn39
		 (DataQId happy_var_1 happy_var_3
	)}}

happyReduce_102 = happySpecReduce_0  32# happyReduction_102
happyReduction_102  =  happyIn40
		 ([]
	)

happyReduce_103 = happySpecReduce_1  32# happyReduction_103
happyReduction_103 happy_x_1
	 =  case happyOut39 happy_x_1 of { happy_var_1 -> 
	happyIn40
		 ((:[]) happy_var_1
	)}

happyReduce_104 = happySpecReduce_3  32# happyReduction_104
happyReduction_104 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut39 happy_x_1 of { happy_var_1 -> 
	case happyOut40 happy_x_3 of { happy_var_3 -> 
	happyIn40
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_105 = happySpecReduce_3  33# happyReduction_105
happyReduction_105 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	case happyOut52 happy_x_3 of { happy_var_3 -> 
	happyIn41
		 (ParDefDir happy_var_1 happy_var_3
	)}}

happyReduce_106 = happyReduce 6# 33# happyReduction_106
happyReduction_106 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut12 happy_x_1 of { happy_var_1 -> 
	case happyOut12 happy_x_5 of { happy_var_5 -> 
	happyIn41
		 (ParDefIndir happy_var_1 happy_var_5
	) `HappyStk` happyRest}}

happyReduce_107 = happySpecReduce_1  33# happyReduction_107
happyReduction_107 happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	happyIn41
		 (ParDefAbs happy_var_1
	)}

happyReduce_108 = happySpecReduce_2  34# happyReduction_108
happyReduction_108 happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	case happyOut89 happy_x_2 of { happy_var_2 -> 
	happyIn42
		 (ParConstr happy_var_1 (reverse happy_var_2)
	)}}

happyReduce_109 = happySpecReduce_3  35# happyReduction_109
happyReduction_109 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut55 happy_x_1 of { happy_var_1 -> 
	case happyOut64 happy_x_3 of { happy_var_3 -> 
	happyIn43
		 (PrintDef happy_var_1 happy_var_3
	)}}

happyReduce_110 = happySpecReduce_3  36# happyReduction_110
happyReduction_110 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	case happyOut12 happy_x_3 of { happy_var_3 -> 
	happyIn44
		 (FlagDef happy_var_1 happy_var_3
	)}}

happyReduce_111 = happySpecReduce_2  37# happyReduction_111
happyReduction_111 happy_x_2
	happy_x_1
	 =  case happyOut34 happy_x_1 of { happy_var_1 -> 
	happyIn45
		 ((:[]) happy_var_1
	)}

happyReduce_112 = happySpecReduce_3  37# happyReduction_112
happyReduction_112 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut34 happy_x_1 of { happy_var_1 -> 
	case happyOut45 happy_x_3 of { happy_var_3 -> 
	happyIn45
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_113 = happySpecReduce_2  38# happyReduction_113
happyReduction_113 happy_x_2
	happy_x_1
	 =  case happyOut36 happy_x_1 of { happy_var_1 -> 
	happyIn46
		 ((:[]) happy_var_1
	)}

happyReduce_114 = happySpecReduce_3  38# happyReduction_114
happyReduction_114 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut36 happy_x_1 of { happy_var_1 -> 
	case happyOut46 happy_x_3 of { happy_var_3 -> 
	happyIn46
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_115 = happySpecReduce_2  39# happyReduction_115
happyReduction_115 happy_x_2
	happy_x_1
	 =  case happyOut37 happy_x_1 of { happy_var_1 -> 
	happyIn47
		 ((:[]) happy_var_1
	)}

happyReduce_116 = happySpecReduce_3  39# happyReduction_116
happyReduction_116 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut37 happy_x_1 of { happy_var_1 -> 
	case happyOut47 happy_x_3 of { happy_var_3 -> 
	happyIn47
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_117 = happySpecReduce_2  40# happyReduction_117
happyReduction_117 happy_x_2
	happy_x_1
	 =  case happyOut38 happy_x_1 of { happy_var_1 -> 
	happyIn48
		 ((:[]) happy_var_1
	)}

happyReduce_118 = happySpecReduce_3  40# happyReduction_118
happyReduction_118 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut38 happy_x_1 of { happy_var_1 -> 
	case happyOut48 happy_x_3 of { happy_var_3 -> 
	happyIn48
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_119 = happySpecReduce_2  41# happyReduction_119
happyReduction_119 happy_x_2
	happy_x_1
	 =  case happyOut41 happy_x_1 of { happy_var_1 -> 
	happyIn49
		 ((:[]) happy_var_1
	)}

happyReduce_120 = happySpecReduce_3  41# happyReduction_120
happyReduction_120 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut41 happy_x_1 of { happy_var_1 -> 
	case happyOut49 happy_x_3 of { happy_var_3 -> 
	happyIn49
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_121 = happySpecReduce_2  42# happyReduction_121
happyReduction_121 happy_x_2
	happy_x_1
	 =  case happyOut43 happy_x_1 of { happy_var_1 -> 
	happyIn50
		 ((:[]) happy_var_1
	)}

happyReduce_122 = happySpecReduce_3  42# happyReduction_122
happyReduction_122 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut43 happy_x_1 of { happy_var_1 -> 
	case happyOut50 happy_x_3 of { happy_var_3 -> 
	happyIn50
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_123 = happySpecReduce_2  43# happyReduction_123
happyReduction_123 happy_x_2
	happy_x_1
	 =  case happyOut44 happy_x_1 of { happy_var_1 -> 
	happyIn51
		 ((:[]) happy_var_1
	)}

happyReduce_124 = happySpecReduce_3  43# happyReduction_124
happyReduction_124 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut44 happy_x_1 of { happy_var_1 -> 
	case happyOut51 happy_x_3 of { happy_var_3 -> 
	happyIn51
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_125 = happySpecReduce_0  44# happyReduction_125
happyReduction_125  =  happyIn52
		 ([]
	)

happyReduce_126 = happySpecReduce_1  44# happyReduction_126
happyReduction_126 happy_x_1
	 =  case happyOut42 happy_x_1 of { happy_var_1 -> 
	happyIn52
		 ((:[]) happy_var_1
	)}

happyReduce_127 = happySpecReduce_3  44# happyReduction_127
happyReduction_127 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut42 happy_x_1 of { happy_var_1 -> 
	case happyOut52 happy_x_3 of { happy_var_3 -> 
	happyIn52
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_128 = happySpecReduce_1  45# happyReduction_128
happyReduction_128 happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	happyIn53
		 ((:[]) happy_var_1
	)}

happyReduce_129 = happySpecReduce_3  45# happyReduction_129
happyReduction_129 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	case happyOut53 happy_x_3 of { happy_var_3 -> 
	happyIn53
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_130 = happySpecReduce_1  46# happyReduction_130
happyReduction_130 happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	happyIn54
		 (IdentName happy_var_1
	)}

happyReduce_131 = happySpecReduce_3  46# happyReduction_131
happyReduction_131 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_2 of { happy_var_2 -> 
	happyIn54
		 (ListName happy_var_2
	)}

happyReduce_132 = happySpecReduce_1  47# happyReduction_132
happyReduction_132 happy_x_1
	 =  case happyOut54 happy_x_1 of { happy_var_1 -> 
	happyIn55
		 ((:[]) happy_var_1
	)}

happyReduce_133 = happySpecReduce_3  47# happyReduction_133
happyReduction_133 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut54 happy_x_1 of { happy_var_1 -> 
	case happyOut55 happy_x_3 of { happy_var_3 -> 
	happyIn55
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_134 = happySpecReduce_3  48# happyReduction_134
happyReduction_134 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut53 happy_x_1 of { happy_var_1 -> 
	case happyOut64 happy_x_3 of { happy_var_3 -> 
	happyIn56
		 (LDDecl happy_var_1 happy_var_3
	)}}

happyReduce_135 = happySpecReduce_3  48# happyReduction_135
happyReduction_135 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut53 happy_x_1 of { happy_var_1 -> 
	case happyOut64 happy_x_3 of { happy_var_3 -> 
	happyIn56
		 (LDDef happy_var_1 happy_var_3
	)}}

happyReduce_136 = happyReduce 5# 48# happyReduction_136
happyReduction_136 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut53 happy_x_1 of { happy_var_1 -> 
	case happyOut64 happy_x_3 of { happy_var_3 -> 
	case happyOut64 happy_x_5 of { happy_var_5 -> 
	happyIn56
		 (LDFull happy_var_1 happy_var_3 happy_var_5
	) `HappyStk` happyRest}}}

happyReduce_137 = happySpecReduce_0  49# happyReduction_137
happyReduction_137  =  happyIn57
		 ([]
	)

happyReduce_138 = happySpecReduce_1  49# happyReduction_138
happyReduction_138 happy_x_1
	 =  case happyOut56 happy_x_1 of { happy_var_1 -> 
	happyIn57
		 ((:[]) happy_var_1
	)}

happyReduce_139 = happySpecReduce_3  49# happyReduction_139
happyReduction_139 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut56 happy_x_1 of { happy_var_1 -> 
	case happyOut57 happy_x_3 of { happy_var_3 -> 
	happyIn57
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_140 = happySpecReduce_1  50# happyReduction_140
happyReduction_140 happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	happyIn58
		 (EIdent happy_var_1
	)}

happyReduce_141 = happySpecReduce_3  50# happyReduction_141
happyReduction_141 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_2 of { happy_var_2 -> 
	happyIn58
		 (EConstr happy_var_2
	)}

happyReduce_142 = happySpecReduce_3  50# happyReduction_142
happyReduction_142 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_2 of { happy_var_2 -> 
	happyIn58
		 (ECons happy_var_2
	)}

happyReduce_143 = happySpecReduce_1  50# happyReduction_143
happyReduction_143 happy_x_1
	 =  case happyOut72 happy_x_1 of { happy_var_1 -> 
	happyIn58
		 (ESort happy_var_1
	)}

happyReduce_144 = happySpecReduce_1  50# happyReduction_144
happyReduction_144 happy_x_1
	 =  case happyOut9 happy_x_1 of { happy_var_1 -> 
	happyIn58
		 (EString happy_var_1
	)}

happyReduce_145 = happySpecReduce_1  50# happyReduction_145
happyReduction_145 happy_x_1
	 =  case happyOut8 happy_x_1 of { happy_var_1 -> 
	happyIn58
		 (EInt happy_var_1
	)}

happyReduce_146 = happySpecReduce_1  50# happyReduction_146
happyReduction_146 happy_x_1
	 =  case happyOut10 happy_x_1 of { happy_var_1 -> 
	happyIn58
		 (EFloat happy_var_1
	)}

happyReduce_147 = happySpecReduce_1  50# happyReduction_147
happyReduction_147 happy_x_1
	 =  happyIn58
		 (EMeta
	)

happyReduce_148 = happySpecReduce_2  50# happyReduction_148
happyReduction_148 happy_x_2
	happy_x_1
	 =  happyIn58
		 (EEmpty
	)

happyReduce_149 = happySpecReduce_1  50# happyReduction_149
happyReduction_149 happy_x_1
	 =  happyIn58
		 (EData
	)

happyReduce_150 = happyReduce 4# 50# happyReduction_150
happyReduction_150 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut12 happy_x_2 of { happy_var_2 -> 
	case happyOut66 happy_x_3 of { happy_var_3 -> 
	happyIn58
		 (EList happy_var_2 happy_var_3
	) `HappyStk` happyRest}}

happyReduce_151 = happySpecReduce_3  50# happyReduction_151
happyReduction_151 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut9 happy_x_2 of { happy_var_2 -> 
	happyIn58
		 (EStrings happy_var_2
	)}

happyReduce_152 = happySpecReduce_3  50# happyReduction_152
happyReduction_152 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut57 happy_x_2 of { happy_var_2 -> 
	happyIn58
		 (ERecord happy_var_2
	)}

happyReduce_153 = happySpecReduce_3  50# happyReduction_153
happyReduction_153 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut80 happy_x_2 of { happy_var_2 -> 
	happyIn58
		 (ETuple happy_var_2
	)}

happyReduce_154 = happyReduce 4# 50# happyReduction_154
happyReduction_154 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut12 happy_x_3 of { happy_var_3 -> 
	happyIn58
		 (EIndir happy_var_3
	) `HappyStk` happyRest}

happyReduce_155 = happyReduce 5# 50# happyReduction_155
happyReduction_155 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut64 happy_x_2 of { happy_var_2 -> 
	case happyOut64 happy_x_4 of { happy_var_4 -> 
	happyIn58
		 (ETyped happy_var_2 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_156 = happySpecReduce_3  50# happyReduction_156
happyReduction_156 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut64 happy_x_2 of { happy_var_2 -> 
	happyIn58
		 (happy_var_2
	)}

happyReduce_157 = happySpecReduce_1  50# happyReduction_157
happyReduction_157 happy_x_1
	 =  case happyOut11 happy_x_1 of { happy_var_1 -> 
	happyIn58
		 (ELString happy_var_1
	)}

happyReduce_158 = happySpecReduce_3  51# happyReduction_158
happyReduction_158 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut59 happy_x_1 of { happy_var_1 -> 
	case happyOut71 happy_x_3 of { happy_var_3 -> 
	happyIn59
		 (EProj happy_var_1 happy_var_3
	)}}

happyReduce_159 = happyReduce 5# 51# happyReduction_159
happyReduction_159 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut12 happy_x_2 of { happy_var_2 -> 
	case happyOut12 happy_x_4 of { happy_var_4 -> 
	happyIn59
		 (EQConstr happy_var_2 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_160 = happyReduce 4# 51# happyReduction_160
happyReduction_160 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut12 happy_x_2 of { happy_var_2 -> 
	case happyOut12 happy_x_4 of { happy_var_4 -> 
	happyIn59
		 (EQCons happy_var_2 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_161 = happySpecReduce_1  51# happyReduction_161
happyReduction_161 happy_x_1
	 =  case happyOut58 happy_x_1 of { happy_var_1 -> 
	happyIn59
		 (happy_var_1
	)}

happyReduce_162 = happySpecReduce_2  52# happyReduction_162
happyReduction_162 happy_x_2
	happy_x_1
	 =  case happyOut60 happy_x_1 of { happy_var_1 -> 
	case happyOut59 happy_x_2 of { happy_var_2 -> 
	happyIn60
		 (EApp happy_var_1 happy_var_2
	)}}

happyReduce_163 = happyReduce 4# 52# happyReduction_163
happyReduction_163 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut83 happy_x_3 of { happy_var_3 -> 
	happyIn60
		 (ETable happy_var_3
	) `HappyStk` happyRest}

happyReduce_164 = happyReduce 5# 52# happyReduction_164
happyReduction_164 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut58 happy_x_2 of { happy_var_2 -> 
	case happyOut83 happy_x_4 of { happy_var_4 -> 
	happyIn60
		 (ETTable happy_var_2 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_165 = happyReduce 5# 52# happyReduction_165
happyReduction_165 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut58 happy_x_2 of { happy_var_2 -> 
	case happyOut65 happy_x_4 of { happy_var_4 -> 
	happyIn60
		 (EVTable happy_var_2 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_166 = happyReduce 6# 52# happyReduction_166
happyReduction_166 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut64 happy_x_2 of { happy_var_2 -> 
	case happyOut83 happy_x_5 of { happy_var_5 -> 
	happyIn60
		 (ECase happy_var_2 happy_var_5
	) `HappyStk` happyRest}}

happyReduce_167 = happyReduce 4# 52# happyReduction_167
happyReduction_167 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut65 happy_x_3 of { happy_var_3 -> 
	happyIn60
		 (EVariants happy_var_3
	) `HappyStk` happyRest}

happyReduce_168 = happyReduce 6# 52# happyReduction_168
happyReduction_168 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut64 happy_x_3 of { happy_var_3 -> 
	case happyOut87 happy_x_5 of { happy_var_5 -> 
	happyIn60
		 (EPre happy_var_3 happy_var_5
	) `HappyStk` happyRest}}

happyReduce_169 = happyReduce 4# 52# happyReduction_169
happyReduction_169 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut65 happy_x_3 of { happy_var_3 -> 
	happyIn60
		 (EStrs happy_var_3
	) `HappyStk` happyRest}

happyReduce_170 = happySpecReduce_3  52# happyReduction_170
happyReduction_170 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	case happyOut58 happy_x_3 of { happy_var_3 -> 
	happyIn60
		 (EConAt happy_var_1 happy_var_3
	)}}

happyReduce_171 = happySpecReduce_2  52# happyReduction_171
happyReduction_171 happy_x_2
	happy_x_1
	 =  case happyOut67 happy_x_2 of { happy_var_2 -> 
	happyIn60
		 (EPatt happy_var_2
	)}

happyReduce_172 = happySpecReduce_2  52# happyReduction_172
happyReduction_172 happy_x_2
	happy_x_1
	 =  case happyOut59 happy_x_2 of { happy_var_2 -> 
	happyIn60
		 (EPattType happy_var_2
	)}

happyReduce_173 = happySpecReduce_1  52# happyReduction_173
happyReduction_173 happy_x_1
	 =  case happyOut59 happy_x_1 of { happy_var_1 -> 
	happyIn60
		 (happy_var_1
	)}

happyReduce_174 = happySpecReduce_2  52# happyReduction_174
happyReduction_174 happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_2 of { happy_var_2 -> 
	happyIn60
		 (ELin happy_var_2
	)}

happyReduce_175 = happySpecReduce_3  53# happyReduction_175
happyReduction_175 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut61 happy_x_1 of { happy_var_1 -> 
	case happyOut60 happy_x_3 of { happy_var_3 -> 
	happyIn61
		 (ESelect happy_var_1 happy_var_3
	)}}

happyReduce_176 = happySpecReduce_3  53# happyReduction_176
happyReduction_176 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut61 happy_x_1 of { happy_var_1 -> 
	case happyOut60 happy_x_3 of { happy_var_3 -> 
	happyIn61
		 (ETupTyp happy_var_1 happy_var_3
	)}}

happyReduce_177 = happySpecReduce_3  53# happyReduction_177
happyReduction_177 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut61 happy_x_1 of { happy_var_1 -> 
	case happyOut60 happy_x_3 of { happy_var_3 -> 
	happyIn61
		 (EExtend happy_var_1 happy_var_3
	)}}

happyReduce_178 = happySpecReduce_1  53# happyReduction_178
happyReduction_178 happy_x_1
	 =  case happyOut60 happy_x_1 of { happy_var_1 -> 
	happyIn61
		 (happy_var_1
	)}

happyReduce_179 = happySpecReduce_3  54# happyReduction_179
happyReduction_179 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut61 happy_x_1 of { happy_var_1 -> 
	case happyOut62 happy_x_3 of { happy_var_3 -> 
	happyIn62
		 (EGlue happy_var_1 happy_var_3
	)}}

happyReduce_180 = happySpecReduce_1  54# happyReduction_180
happyReduction_180 happy_x_1
	 =  case happyOut61 happy_x_1 of { happy_var_1 -> 
	happyIn62
		 (happy_var_1
	)}

happyReduce_181 = happySpecReduce_3  55# happyReduction_181
happyReduction_181 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut62 happy_x_1 of { happy_var_1 -> 
	case happyOut63 happy_x_3 of { happy_var_3 -> 
	happyIn63
		 (EConcat happy_var_1 happy_var_3
	)}}

happyReduce_182 = happySpecReduce_1  55# happyReduction_182
happyReduction_182 happy_x_1
	 =  case happyOut62 happy_x_1 of { happy_var_1 -> 
	happyIn63
		 (happy_var_1
	)}

happyReduce_183 = happySpecReduce_3  56# happyReduction_183
happyReduction_183 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut63 happy_x_1 of { happy_var_1 -> 
	case happyOut64 happy_x_3 of { happy_var_3 -> 
	happyIn64
		 (EVariant happy_var_1 happy_var_3
	)}}

happyReduce_184 = happyReduce 4# 56# happyReduction_184
happyReduction_184 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut76 happy_x_2 of { happy_var_2 -> 
	case happyOut64 happy_x_4 of { happy_var_4 -> 
	happyIn64
		 (EAbstr happy_var_2 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_185 = happyReduce 5# 56# happyReduction_185
happyReduction_185 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut76 happy_x_3 of { happy_var_3 -> 
	case happyOut64 happy_x_5 of { happy_var_5 -> 
	happyIn64
		 (ECTable happy_var_3 happy_var_5
	) `HappyStk` happyRest}}

happyReduce_186 = happySpecReduce_3  56# happyReduction_186
happyReduction_186 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut77 happy_x_1 of { happy_var_1 -> 
	case happyOut64 happy_x_3 of { happy_var_3 -> 
	happyIn64
		 (EProd happy_var_1 happy_var_3
	)}}

happyReduce_187 = happySpecReduce_3  56# happyReduction_187
happyReduction_187 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut61 happy_x_1 of { happy_var_1 -> 
	case happyOut64 happy_x_3 of { happy_var_3 -> 
	happyIn64
		 (ETType happy_var_1 happy_var_3
	)}}

happyReduce_188 = happyReduce 6# 56# happyReduction_188
happyReduction_188 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut57 happy_x_3 of { happy_var_3 -> 
	case happyOut64 happy_x_6 of { happy_var_6 -> 
	happyIn64
		 (ELet happy_var_3 happy_var_6
	) `HappyStk` happyRest}}

happyReduce_189 = happyReduce 4# 56# happyReduction_189
happyReduction_189 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut57 happy_x_2 of { happy_var_2 -> 
	case happyOut64 happy_x_4 of { happy_var_4 -> 
	happyIn64
		 (ELetb happy_var_2 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_190 = happyReduce 5# 56# happyReduction_190
happyReduction_190 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut61 happy_x_1 of { happy_var_1 -> 
	case happyOut57 happy_x_4 of { happy_var_4 -> 
	happyIn64
		 (EWhere happy_var_1 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_191 = happyReduce 4# 56# happyReduction_191
happyReduction_191 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut85 happy_x_3 of { happy_var_3 -> 
	happyIn64
		 (EEqs happy_var_3
	) `HappyStk` happyRest}

happyReduce_192 = happySpecReduce_3  56# happyReduction_192
happyReduction_192 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut59 happy_x_2 of { happy_var_2 -> 
	case happyOut9 happy_x_3 of { happy_var_3 -> 
	happyIn64
		 (EExample happy_var_2 happy_var_3
	)}}

happyReduce_193 = happySpecReduce_1  56# happyReduction_193
happyReduction_193 happy_x_1
	 =  case happyOut63 happy_x_1 of { happy_var_1 -> 
	happyIn64
		 (happy_var_1
	)}

happyReduce_194 = happySpecReduce_0  57# happyReduction_194
happyReduction_194  =  happyIn65
		 ([]
	)

happyReduce_195 = happySpecReduce_1  57# happyReduction_195
happyReduction_195 happy_x_1
	 =  case happyOut64 happy_x_1 of { happy_var_1 -> 
	happyIn65
		 ((:[]) happy_var_1
	)}

happyReduce_196 = happySpecReduce_3  57# happyReduction_196
happyReduction_196 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut64 happy_x_1 of { happy_var_1 -> 
	case happyOut65 happy_x_3 of { happy_var_3 -> 
	happyIn65
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_197 = happySpecReduce_0  58# happyReduction_197
happyReduction_197  =  happyIn66
		 (NilExp
	)

happyReduce_198 = happySpecReduce_2  58# happyReduction_198
happyReduction_198 happy_x_2
	happy_x_1
	 =  case happyOut58 happy_x_1 of { happy_var_1 -> 
	case happyOut66 happy_x_2 of { happy_var_2 -> 
	happyIn66
		 (ConsExp happy_var_1 happy_var_2
	)}}

happyReduce_199 = happySpecReduce_1  59# happyReduction_199
happyReduction_199 happy_x_1
	 =  happyIn67
		 (PChar
	)

happyReduce_200 = happySpecReduce_3  59# happyReduction_200
happyReduction_200 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut9 happy_x_2 of { happy_var_2 -> 
	happyIn67
		 (PChars happy_var_2
	)}

happyReduce_201 = happySpecReduce_2  59# happyReduction_201
happyReduction_201 happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_2 of { happy_var_2 -> 
	happyIn67
		 (PMacro happy_var_2
	)}

happyReduce_202 = happyReduce 4# 59# happyReduction_202
happyReduction_202 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut12 happy_x_2 of { happy_var_2 -> 
	case happyOut12 happy_x_4 of { happy_var_4 -> 
	happyIn67
		 (PM happy_var_2 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_203 = happySpecReduce_1  59# happyReduction_203
happyReduction_203 happy_x_1
	 =  happyIn67
		 (PW
	)

happyReduce_204 = happySpecReduce_1  59# happyReduction_204
happyReduction_204 happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	happyIn67
		 (PV happy_var_1
	)}

happyReduce_205 = happySpecReduce_3  59# happyReduction_205
happyReduction_205 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_2 of { happy_var_2 -> 
	happyIn67
		 (PCon happy_var_2
	)}

happyReduce_206 = happySpecReduce_3  59# happyReduction_206
happyReduction_206 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	case happyOut12 happy_x_3 of { happy_var_3 -> 
	happyIn67
		 (PQ happy_var_1 happy_var_3
	)}}

happyReduce_207 = happySpecReduce_1  59# happyReduction_207
happyReduction_207 happy_x_1
	 =  case happyOut8 happy_x_1 of { happy_var_1 -> 
	happyIn67
		 (PInt happy_var_1
	)}

happyReduce_208 = happySpecReduce_1  59# happyReduction_208
happyReduction_208 happy_x_1
	 =  case happyOut10 happy_x_1 of { happy_var_1 -> 
	happyIn67
		 (PFloat happy_var_1
	)}

happyReduce_209 = happySpecReduce_1  59# happyReduction_209
happyReduction_209 happy_x_1
	 =  case happyOut9 happy_x_1 of { happy_var_1 -> 
	happyIn67
		 (PStr happy_var_1
	)}

happyReduce_210 = happySpecReduce_3  59# happyReduction_210
happyReduction_210 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut73 happy_x_2 of { happy_var_2 -> 
	happyIn67
		 (PR happy_var_2
	)}

happyReduce_211 = happySpecReduce_3  59# happyReduction_211
happyReduction_211 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut81 happy_x_2 of { happy_var_2 -> 
	happyIn67
		 (PTup happy_var_2
	)}

happyReduce_212 = happySpecReduce_3  59# happyReduction_212
happyReduction_212 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut69 happy_x_2 of { happy_var_2 -> 
	happyIn67
		 (happy_var_2
	)}

happyReduce_213 = happySpecReduce_2  60# happyReduction_213
happyReduction_213 happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	case happyOut74 happy_x_2 of { happy_var_2 -> 
	happyIn68
		 (PC happy_var_1 happy_var_2
	)}}

happyReduce_214 = happyReduce 4# 60# happyReduction_214
happyReduction_214 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut12 happy_x_1 of { happy_var_1 -> 
	case happyOut12 happy_x_3 of { happy_var_3 -> 
	case happyOut74 happy_x_4 of { happy_var_4 -> 
	happyIn68
		 (PQC happy_var_1 happy_var_3 happy_var_4
	) `HappyStk` happyRest}}}

happyReduce_215 = happySpecReduce_2  60# happyReduction_215
happyReduction_215 happy_x_2
	happy_x_1
	 =  case happyOut67 happy_x_1 of { happy_var_1 -> 
	happyIn68
		 (PRep happy_var_1
	)}

happyReduce_216 = happySpecReduce_3  60# happyReduction_216
happyReduction_216 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	case happyOut67 happy_x_3 of { happy_var_3 -> 
	happyIn68
		 (PAs happy_var_1 happy_var_3
	)}}

happyReduce_217 = happySpecReduce_2  60# happyReduction_217
happyReduction_217 happy_x_2
	happy_x_1
	 =  case happyOut67 happy_x_2 of { happy_var_2 -> 
	happyIn68
		 (PNeg happy_var_2
	)}

happyReduce_218 = happySpecReduce_1  60# happyReduction_218
happyReduction_218 happy_x_1
	 =  case happyOut67 happy_x_1 of { happy_var_1 -> 
	happyIn68
		 (happy_var_1
	)}

happyReduce_219 = happySpecReduce_3  61# happyReduction_219
happyReduction_219 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut69 happy_x_1 of { happy_var_1 -> 
	case happyOut68 happy_x_3 of { happy_var_3 -> 
	happyIn69
		 (PDisj happy_var_1 happy_var_3
	)}}

happyReduce_220 = happySpecReduce_3  61# happyReduction_220
happyReduction_220 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut69 happy_x_1 of { happy_var_1 -> 
	case happyOut68 happy_x_3 of { happy_var_3 -> 
	happyIn69
		 (PSeq happy_var_1 happy_var_3
	)}}

happyReduce_221 = happySpecReduce_1  61# happyReduction_221
happyReduction_221 happy_x_1
	 =  case happyOut68 happy_x_1 of { happy_var_1 -> 
	happyIn69
		 (happy_var_1
	)}

happyReduce_222 = happySpecReduce_3  62# happyReduction_222
happyReduction_222 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut53 happy_x_1 of { happy_var_1 -> 
	case happyOut69 happy_x_3 of { happy_var_3 -> 
	happyIn70
		 (PA happy_var_1 happy_var_3
	)}}

happyReduce_223 = happySpecReduce_1  63# happyReduction_223
happyReduction_223 happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	happyIn71
		 (LIdent happy_var_1
	)}

happyReduce_224 = happySpecReduce_2  63# happyReduction_224
happyReduction_224 happy_x_2
	happy_x_1
	 =  case happyOut8 happy_x_2 of { happy_var_2 -> 
	happyIn71
		 (LVar happy_var_2
	)}

happyReduce_225 = happySpecReduce_1  64# happyReduction_225
happyReduction_225 happy_x_1
	 =  happyIn72
		 (Sort_Type
	)

happyReduce_226 = happySpecReduce_1  64# happyReduction_226
happyReduction_226 happy_x_1
	 =  happyIn72
		 (Sort_PType
	)

happyReduce_227 = happySpecReduce_1  64# happyReduction_227
happyReduction_227 happy_x_1
	 =  happyIn72
		 (Sort_Tok
	)

happyReduce_228 = happySpecReduce_1  64# happyReduction_228
happyReduction_228 happy_x_1
	 =  happyIn72
		 (Sort_Str
	)

happyReduce_229 = happySpecReduce_1  64# happyReduction_229
happyReduction_229 happy_x_1
	 =  happyIn72
		 (Sort_Strs
	)

happyReduce_230 = happySpecReduce_0  65# happyReduction_230
happyReduction_230  =  happyIn73
		 ([]
	)

happyReduce_231 = happySpecReduce_1  65# happyReduction_231
happyReduction_231 happy_x_1
	 =  case happyOut70 happy_x_1 of { happy_var_1 -> 
	happyIn73
		 ((:[]) happy_var_1
	)}

happyReduce_232 = happySpecReduce_3  65# happyReduction_232
happyReduction_232 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut70 happy_x_1 of { happy_var_1 -> 
	case happyOut73 happy_x_3 of { happy_var_3 -> 
	happyIn73
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_233 = happySpecReduce_1  66# happyReduction_233
happyReduction_233 happy_x_1
	 =  case happyOut67 happy_x_1 of { happy_var_1 -> 
	happyIn74
		 ((:[]) happy_var_1
	)}

happyReduce_234 = happySpecReduce_2  66# happyReduction_234
happyReduction_234 happy_x_2
	happy_x_1
	 =  case happyOut67 happy_x_1 of { happy_var_1 -> 
	case happyOut74 happy_x_2 of { happy_var_2 -> 
	happyIn74
		 ((:) happy_var_1 happy_var_2
	)}}

happyReduce_235 = happySpecReduce_1  67# happyReduction_235
happyReduction_235 happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	happyIn75
		 (BIdent happy_var_1
	)}

happyReduce_236 = happySpecReduce_1  67# happyReduction_236
happyReduction_236 happy_x_1
	 =  happyIn75
		 (BWild
	)

happyReduce_237 = happySpecReduce_0  68# happyReduction_237
happyReduction_237  =  happyIn76
		 ([]
	)

happyReduce_238 = happySpecReduce_1  68# happyReduction_238
happyReduction_238 happy_x_1
	 =  case happyOut75 happy_x_1 of { happy_var_1 -> 
	happyIn76
		 ((:[]) happy_var_1
	)}

happyReduce_239 = happySpecReduce_3  68# happyReduction_239
happyReduction_239 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut75 happy_x_1 of { happy_var_1 -> 
	case happyOut76 happy_x_3 of { happy_var_3 -> 
	happyIn76
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_240 = happyReduce 5# 69# happyReduction_240
happyReduction_240 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut76 happy_x_2 of { happy_var_2 -> 
	case happyOut64 happy_x_4 of { happy_var_4 -> 
	happyIn77
		 (DDec happy_var_2 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_241 = happySpecReduce_1  69# happyReduction_241
happyReduction_241 happy_x_1
	 =  case happyOut60 happy_x_1 of { happy_var_1 -> 
	happyIn77
		 (DExp happy_var_1
	)}

happyReduce_242 = happySpecReduce_1  70# happyReduction_242
happyReduction_242 happy_x_1
	 =  case happyOut64 happy_x_1 of { happy_var_1 -> 
	happyIn78
		 (TComp happy_var_1
	)}

happyReduce_243 = happySpecReduce_1  71# happyReduction_243
happyReduction_243 happy_x_1
	 =  case happyOut69 happy_x_1 of { happy_var_1 -> 
	happyIn79
		 (PTComp happy_var_1
	)}

happyReduce_244 = happySpecReduce_0  72# happyReduction_244
happyReduction_244  =  happyIn80
		 ([]
	)

happyReduce_245 = happySpecReduce_1  72# happyReduction_245
happyReduction_245 happy_x_1
	 =  case happyOut78 happy_x_1 of { happy_var_1 -> 
	happyIn80
		 ((:[]) happy_var_1
	)}

happyReduce_246 = happySpecReduce_3  72# happyReduction_246
happyReduction_246 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut78 happy_x_1 of { happy_var_1 -> 
	case happyOut80 happy_x_3 of { happy_var_3 -> 
	happyIn80
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_247 = happySpecReduce_0  73# happyReduction_247
happyReduction_247  =  happyIn81
		 ([]
	)

happyReduce_248 = happySpecReduce_1  73# happyReduction_248
happyReduction_248 happy_x_1
	 =  case happyOut79 happy_x_1 of { happy_var_1 -> 
	happyIn81
		 ((:[]) happy_var_1
	)}

happyReduce_249 = happySpecReduce_3  73# happyReduction_249
happyReduction_249 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut79 happy_x_1 of { happy_var_1 -> 
	case happyOut81 happy_x_3 of { happy_var_3 -> 
	happyIn81
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_250 = happySpecReduce_3  74# happyReduction_250
happyReduction_250 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut69 happy_x_1 of { happy_var_1 -> 
	case happyOut64 happy_x_3 of { happy_var_3 -> 
	happyIn82
		 (Case happy_var_1 happy_var_3
	)}}

happyReduce_251 = happySpecReduce_1  75# happyReduction_251
happyReduction_251 happy_x_1
	 =  case happyOut82 happy_x_1 of { happy_var_1 -> 
	happyIn83
		 ((:[]) happy_var_1
	)}

happyReduce_252 = happySpecReduce_3  75# happyReduction_252
happyReduction_252 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut82 happy_x_1 of { happy_var_1 -> 
	case happyOut83 happy_x_3 of { happy_var_3 -> 
	happyIn83
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_253 = happySpecReduce_3  76# happyReduction_253
happyReduction_253 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut74 happy_x_1 of { happy_var_1 -> 
	case happyOut64 happy_x_3 of { happy_var_3 -> 
	happyIn84
		 (Equ happy_var_1 happy_var_3
	)}}

happyReduce_254 = happySpecReduce_0  77# happyReduction_254
happyReduction_254  =  happyIn85
		 ([]
	)

happyReduce_255 = happySpecReduce_1  77# happyReduction_255
happyReduction_255 happy_x_1
	 =  case happyOut84 happy_x_1 of { happy_var_1 -> 
	happyIn85
		 ((:[]) happy_var_1
	)}

happyReduce_256 = happySpecReduce_3  77# happyReduction_256
happyReduction_256 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut84 happy_x_1 of { happy_var_1 -> 
	case happyOut85 happy_x_3 of { happy_var_3 -> 
	happyIn85
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_257 = happySpecReduce_3  78# happyReduction_257
happyReduction_257 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut64 happy_x_1 of { happy_var_1 -> 
	case happyOut64 happy_x_3 of { happy_var_3 -> 
	happyIn86
		 (Alt happy_var_1 happy_var_3
	)}}

happyReduce_258 = happySpecReduce_0  79# happyReduction_258
happyReduction_258  =  happyIn87
		 ([]
	)

happyReduce_259 = happySpecReduce_1  79# happyReduction_259
happyReduction_259 happy_x_1
	 =  case happyOut86 happy_x_1 of { happy_var_1 -> 
	happyIn87
		 ((:[]) happy_var_1
	)}

happyReduce_260 = happySpecReduce_3  79# happyReduction_260
happyReduction_260 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut86 happy_x_1 of { happy_var_1 -> 
	case happyOut87 happy_x_3 of { happy_var_3 -> 
	happyIn87
		 ((:) happy_var_1 happy_var_3
	)}}

happyReduce_261 = happyReduce 5# 80# happyReduction_261
happyReduction_261 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut76 happy_x_2 of { happy_var_2 -> 
	case happyOut64 happy_x_4 of { happy_var_4 -> 
	happyIn88
		 (DDDec happy_var_2 happy_var_4
	) `HappyStk` happyRest}}

happyReduce_262 = happySpecReduce_1  80# happyReduction_262
happyReduction_262 happy_x_1
	 =  case happyOut58 happy_x_1 of { happy_var_1 -> 
	happyIn88
		 (DDExp happy_var_1
	)}

happyReduce_263 = happySpecReduce_0  81# happyReduction_263
happyReduction_263  =  happyIn89
		 ([]
	)

happyReduce_264 = happySpecReduce_2  81# happyReduction_264
happyReduction_264 happy_x_2
	happy_x_1
	 =  case happyOut89 happy_x_1 of { happy_var_1 -> 
	case happyOut88 happy_x_2 of { happy_var_2 -> 
	happyIn89
		 (flip (:) happy_var_1 happy_var_2
	)}}

happyReduce_265 = happySpecReduce_2  82# happyReduction_265
happyReduction_265 happy_x_2
	happy_x_1
	 =  case happyOut91 happy_x_1 of { happy_var_1 -> 
	case happyOut25 happy_x_2 of { happy_var_2 -> 
	happyIn90
		 (OldGr happy_var_1 (reverse happy_var_2)
	)}}

happyReduce_266 = happySpecReduce_0  83# happyReduction_266
happyReduction_266  =  happyIn91
		 (NoIncl
	)

happyReduce_267 = happySpecReduce_2  83# happyReduction_267
happyReduction_267 happy_x_2
	happy_x_1
	 =  case happyOut93 happy_x_2 of { happy_var_2 -> 
	happyIn91
		 (Incl happy_var_2
	)}

happyReduce_268 = happySpecReduce_1  84# happyReduction_268
happyReduction_268 happy_x_1
	 =  case happyOut9 happy_x_1 of { happy_var_1 -> 
	happyIn92
		 (FString happy_var_1
	)}

happyReduce_269 = happySpecReduce_1  84# happyReduction_269
happyReduction_269 happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	happyIn92
		 (FIdent happy_var_1
	)}

happyReduce_270 = happySpecReduce_2  84# happyReduction_270
happyReduction_270 happy_x_2
	happy_x_1
	 =  case happyOut92 happy_x_2 of { happy_var_2 -> 
	happyIn92
		 (FSlash happy_var_2
	)}

happyReduce_271 = happySpecReduce_2  84# happyReduction_271
happyReduction_271 happy_x_2
	happy_x_1
	 =  case happyOut92 happy_x_2 of { happy_var_2 -> 
	happyIn92
		 (FDot happy_var_2
	)}

happyReduce_272 = happySpecReduce_2  84# happyReduction_272
happyReduction_272 happy_x_2
	happy_x_1
	 =  case happyOut92 happy_x_2 of { happy_var_2 -> 
	happyIn92
		 (FMinus happy_var_2
	)}

happyReduce_273 = happySpecReduce_2  84# happyReduction_273
happyReduction_273 happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_1 of { happy_var_1 -> 
	case happyOut92 happy_x_2 of { happy_var_2 -> 
	happyIn92
		 (FAddId happy_var_1 happy_var_2
	)}}

happyReduce_274 = happySpecReduce_2  85# happyReduction_274
happyReduction_274 happy_x_2
	happy_x_1
	 =  case happyOut92 happy_x_1 of { happy_var_1 -> 
	happyIn93
		 ((:[]) happy_var_1
	)}

happyReduce_275 = happySpecReduce_3  85# happyReduction_275
happyReduction_275 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut92 happy_x_1 of { happy_var_1 -> 
	case happyOut93 happy_x_3 of { happy_var_3 -> 
	happyIn93
		 ((:) happy_var_1 happy_var_3
	)}}

happyNewToken action sts stk [] =
	happyDoAction 83# notHappyAtAll action sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = happyDoAction i tk action sts stk tks in
	case tk of {
	PT _ (TS _ 1) -> cont 1#;
	PT _ (TS _ 2) -> cont 2#;
	PT _ (TS _ 3) -> cont 3#;
	PT _ (TS _ 4) -> cont 4#;
	PT _ (TS _ 5) -> cont 5#;
	PT _ (TS _ 6) -> cont 6#;
	PT _ (TS _ 7) -> cont 7#;
	PT _ (TS _ 8) -> cont 8#;
	PT _ (TS _ 9) -> cont 9#;
	PT _ (TS _ 10) -> cont 10#;
	PT _ (TS _ 11) -> cont 11#;
	PT _ (TS _ 12) -> cont 12#;
	PT _ (TS _ 13) -> cont 13#;
	PT _ (TS _ 14) -> cont 14#;
	PT _ (TS _ 15) -> cont 15#;
	PT _ (TS _ 16) -> cont 16#;
	PT _ (TS _ 17) -> cont 17#;
	PT _ (TS _ 18) -> cont 18#;
	PT _ (TS _ 19) -> cont 19#;
	PT _ (TS _ 20) -> cont 20#;
	PT _ (TS _ 21) -> cont 21#;
	PT _ (TS _ 22) -> cont 22#;
	PT _ (TS _ 23) -> cont 23#;
	PT _ (TS _ 24) -> cont 24#;
	PT _ (TS _ 25) -> cont 25#;
	PT _ (TS _ 26) -> cont 26#;
	PT _ (TS _ 27) -> cont 27#;
	PT _ (TS _ 28) -> cont 28#;
	PT _ (TS _ 29) -> cont 29#;
	PT _ (TS _ 30) -> cont 30#;
	PT _ (TS _ 31) -> cont 31#;
	PT _ (TS _ 32) -> cont 32#;
	PT _ (TS _ 33) -> cont 33#;
	PT _ (TS _ 34) -> cont 34#;
	PT _ (TS _ 35) -> cont 35#;
	PT _ (TS _ 36) -> cont 36#;
	PT _ (TS _ 37) -> cont 37#;
	PT _ (TS _ 38) -> cont 38#;
	PT _ (TS _ 39) -> cont 39#;
	PT _ (TS _ 40) -> cont 40#;
	PT _ (TS _ 41) -> cont 41#;
	PT _ (TS _ 42) -> cont 42#;
	PT _ (TS _ 43) -> cont 43#;
	PT _ (TS _ 44) -> cont 44#;
	PT _ (TS _ 45) -> cont 45#;
	PT _ (TS _ 46) -> cont 46#;
	PT _ (TS _ 47) -> cont 47#;
	PT _ (TS _ 48) -> cont 48#;
	PT _ (TS _ 49) -> cont 49#;
	PT _ (TS _ 50) -> cont 50#;
	PT _ (TS _ 51) -> cont 51#;
	PT _ (TS _ 52) -> cont 52#;
	PT _ (TS _ 53) -> cont 53#;
	PT _ (TS _ 54) -> cont 54#;
	PT _ (TS _ 55) -> cont 55#;
	PT _ (TS _ 56) -> cont 56#;
	PT _ (TS _ 57) -> cont 57#;
	PT _ (TS _ 58) -> cont 58#;
	PT _ (TS _ 59) -> cont 59#;
	PT _ (TS _ 60) -> cont 60#;
	PT _ (TS _ 61) -> cont 61#;
	PT _ (TS _ 62) -> cont 62#;
	PT _ (TS _ 63) -> cont 63#;
	PT _ (TS _ 64) -> cont 64#;
	PT _ (TS _ 65) -> cont 65#;
	PT _ (TS _ 66) -> cont 66#;
	PT _ (TS _ 67) -> cont 67#;
	PT _ (TS _ 68) -> cont 68#;
	PT _ (TS _ 69) -> cont 69#;
	PT _ (TS _ 70) -> cont 70#;
	PT _ (TS _ 71) -> cont 71#;
	PT _ (TS _ 72) -> cont 72#;
	PT _ (TS _ 73) -> cont 73#;
	PT _ (TS _ 74) -> cont 74#;
	PT _ (TS _ 75) -> cont 75#;
	PT _ (TS _ 76) -> cont 76#;
	PT _ (TI happy_dollar_dollar) -> cont 77#;
	PT _ (TL happy_dollar_dollar) -> cont 78#;
	PT _ (TD happy_dollar_dollar) -> cont 79#;
	PT _ (T_LString happy_dollar_dollar) -> cont 80#;
	PT _ (T_PIdent _) -> cont 81#;
	_ -> cont 82#;
	_ -> happyError' (tk:tks)
	}

happyError_ tk tks = happyError' (tk:tks)

happyThen :: () => Err a -> (a -> Err b) -> Err b
happyThen = (thenM)
happyReturn :: () => a -> Err a
happyReturn = (returnM)
happyThen1 m k tks = (thenM) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> Err a
happyReturn1 = \a tks -> (returnM) a
happyError' :: () => [Token] -> Err a
happyError' = happyError

pGrammar tks = happySomeParser where
  happySomeParser = happyThen (happyParse 0# tks) (\x -> happyReturn (happyOut13 x))

pModDef tks = happySomeParser where
  happySomeParser = happyThen (happyParse 1# tks) (\x -> happyReturn (happyOut15 x))

pOldGrammar tks = happySomeParser where
  happySomeParser = happyThen (happyParse 2# tks) (\x -> happyReturn (happyOut90 x))

pModHeader tks = happySomeParser where
  happySomeParser = happyThen (happyParse 3# tks) (\x -> happyReturn (happyOut21 x))

pExp tks = happySomeParser where
  happySomeParser = happyThen (happyParse 4# tks) (\x -> happyReturn (happyOut64 x))

happySeq = happyDontSeq


returnM :: a -> Err a
returnM = return

thenM :: Err a -> (a -> Err b) -> Err b
thenM = (>>=)

happyError :: [Token] -> Err a
happyError ts =
  Bad $ "syntax error at " ++ tokenPos ts ++ 
  case ts of
    [] -> []
    [Err _] -> " due to lexer error"
    _ -> " before " ++ unwords (map (BS.unpack . prToken) (take 4 ts))

myLexer = tokens
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "<built-in>" #-}
{-# LINE 1 "<command line>" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp 

{-# LINE 28 "templates/GenericTemplate.hs" #-}


data Happy_IntList = HappyCons Int# Happy_IntList





{-# LINE 49 "templates/GenericTemplate.hs" #-}

{-# LINE 59 "templates/GenericTemplate.hs" #-}

{-# LINE 68 "templates/GenericTemplate.hs" #-}

infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is 0#, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept 0# tk st sts (_ `HappyStk` ans `HappyStk` _) =
	happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
	(happyTcHack j (happyTcHack st)) (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action



happyDoAction i tk st
	= {- nothing -}


	  case action of
		0#		  -> {- nothing -}
				     happyFail i tk st
		-1# 	  -> {- nothing -}
				     happyAccept i tk st
		n | (n <# (0# :: Int#)) -> {- nothing -}

				     (happyReduceArr ! rule) i tk st
				     where rule = (I# ((negateInt# ((n +# (1# :: Int#))))))
		n		  -> {- nothing -}


				     happyShift new_state i tk st
				     where new_state = (n -# (1# :: Int#))
   where off    = indexShortOffAddr happyActOffsets st
	 off_i  = (off +# i)
	 check  = if (off_i >=# (0# :: Int#))
			then (indexShortOffAddr happyCheck off_i ==#  i)
			else False
 	 action | check     = indexShortOffAddr happyTable off_i
		| otherwise = indexShortOffAddr happyDefActions st

{-# LINE 127 "templates/GenericTemplate.hs" #-}


indexShortOffAddr (HappyA# arr) off =
#if __GLASGOW_HASKELL__ > 500
	narrow16Int# i
#elif __GLASGOW_HASKELL__ == 500
	intToInt16# i
#else
	(i `iShiftL#` 16#) `iShiftRA#` 16#
#endif
  where
#if __GLASGOW_HASKELL__ >= 503
	i = word2Int# ((high `uncheckedShiftL#` 8#) `or#` low)
#else
	i = word2Int# ((high `shiftL#` 8#) `or#` low)
#endif
	high = int2Word# (ord# (indexCharOffAddr# arr (off' +# 1#)))
	low  = int2Word# (ord# (indexCharOffAddr# arr off'))
	off' = off *# 2#





data HappyAddr = HappyA# Addr#




-----------------------------------------------------------------------------
-- HappyState data type (not arrays)

{-# LINE 170 "templates/GenericTemplate.hs" #-}

-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state 0# tk st sts stk@(x `HappyStk` _) =
     let i = (case unsafeCoerce# x of { (I# (i)) -> i }) in
--     trace "shifting the error token" $
     happyDoAction i tk new_state (HappyCons (st) (sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state (HappyCons (st) (sts)) ((happyInTok (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_0 nt fn j tk st@((action)) sts stk
     = happyGoto nt j tk st (HappyCons (st) (sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@((HappyCons (st@(action)) (_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_2 nt fn j tk _ (HappyCons (_) (sts@((HappyCons (st@(action)) (_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_3 nt fn j tk _ (HappyCons (_) ((HappyCons (_) (sts@((HappyCons (st@(action)) (_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k -# (1# :: Int#)) sts of
	 sts1@((HappyCons (st1@(action)) (_))) ->
        	let r = fn stk in  -- it doesn't hurt to always seq here...
       		happyDoSeq r (happyGoto nt j tk st1 sts1 r)

happyMonadReduce k nt fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
        happyThen1 (fn stk tk) (\r -> happyGoto nt j tk st1 sts1 (r `HappyStk` drop_stk))
       where sts1@((HappyCons (st1@(action)) (_))) = happyDrop k (HappyCons (st) (sts))
             drop_stk = happyDropStk k stk

happyMonad2Reduce k nt fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
       happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))
       where sts1@((HappyCons (st1@(action)) (_))) = happyDrop k (HappyCons (st) (sts))
             drop_stk = happyDropStk k stk

             off    = indexShortOffAddr happyGotoOffsets st1
             off_i  = (off +# nt)
             new_state = indexShortOffAddr happyTable off_i




happyDrop 0# l = l
happyDrop n (HappyCons (_) (t)) = happyDrop (n -# (1# :: Int#)) t

happyDropStk 0# l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n -# (1#::Int#)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction


happyGoto nt j tk st = 
   {- nothing -}
   happyDoAction j tk new_state
   where off    = indexShortOffAddr happyGotoOffsets st
	 off_i  = (off +# nt)
 	 new_state = indexShortOffAddr happyTable off_i




-----------------------------------------------------------------------------
-- Error recovery (0# is the error token)

-- parse error if we are in recovery and we fail again
happyFail  0# tk old_st _ stk =
--	trace "failing" $ 
    	happyError_ tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  0# tk old_st (HappyCons ((action)) (sts)) 
						(saved_tok `HappyStk` _ `HappyStk` stk) =
--	trace ("discarding state, depth " ++ show (length stk))  $
	happyDoAction 0# tk action sts ((saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail  i tk (action) sts stk =
--      trace "entering error recovery" $
	happyDoAction 0# tk action sts ( (unsafeCoerce# (I# (i))) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll = error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions


happyTcHack :: Int# -> a -> a
happyTcHack x y = y
{-# INLINE happyTcHack #-}


-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--	happySeq = happyDoSeq
-- otherwise it emits
-- 	happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.


{-# NOINLINE happyDoAction #-}
{-# NOINLINE happyTable #-}
{-# NOINLINE happyCheck #-}
{-# NOINLINE happyActOffsets #-}
{-# NOINLINE happyGotoOffsets #-}
{-# NOINLINE happyDefActions #-}

{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
