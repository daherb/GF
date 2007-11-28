module GF.Devel.Lookup where

import GF.Devel.Modules
import GF.Devel.Judgements
import GF.Devel.Terms
import GF.Infra.Ident

import GF.Data.Operations

import Data.Map

-- look up fields for a constant in a grammar

lookupJField :: (Judgement -> a) -> GF -> Ident -> Ident -> Err a
lookupJField field gf m c = do
  j <- lookupJudgement gf m c
  return $ field j

lookupJForm :: GF -> Ident -> Ident -> Err JudgementForm
lookupJForm = lookupJField jform

-- the following don't (need to) check that the jment form is adequate
 
lookupCatContext :: GF -> Ident -> Ident -> Err Context
lookupCatContext gf m c = do
  ty <- lookupJField jtype gf m c
  return [] ---- context of ty

lookupFunType :: GF -> Ident -> Ident -> Err Term
lookupFunType = lookupJField jtype 

lookupLin :: GF -> Ident -> Ident -> Err Term
lookupLin = lookupJField jlin

lookupLincat :: GF -> Ident -> Ident -> Err Term
lookupLincat = lookupJField jlin

lookupParamValues :: GF -> Ident -> Ident -> Err [Term]
lookupParamValues gf m c = do
  j <- lookupJudgement gf m c
  case jdef j of
    V _ ts -> return ts
    _ -> raise "no parameter values"

-- infrastructure for lookup
    
lookupIdent :: GF -> Ident -> Ident -> Err (Either Judgement Ident)
lookupIdent gf m c = do
  mo <- maybe (raise "module not found") return $ mlookup m (gfmodules gf)
  maybe (Bad "constant not found") return $ mlookup c (mjments mo)

lookupJudgement :: GF -> Ident -> Ident -> Err Judgement
lookupJudgement gf m c = do
  eji <- lookupIdent gf m c
  either return (\n -> lookupJudgement gf n c) eji 

mlookup = Data.Map.lookup

