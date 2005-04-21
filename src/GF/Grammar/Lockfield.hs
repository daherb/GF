----------------------------------------------------------------------
-- |
-- Module      : Lockfield
-- Maintainer  : AR
-- Stability   : (stable)
-- Portability : (portable)
--
-- > CVS $Date: 2005/04/21 16:22:21 $ 
-- > CVS $Author: bringert $
-- > CVS $Revision: 1.6 $
--
-- Creating and using lock fields in reused resource grammars.
--
-- AR 8\/2\/2005 detached from 'compile/MkResource'
-----------------------------------------------------------------------------

module GF.Grammar.Lockfield (lockRecType, unlockRecord, lockLabel, isLockLabel) where

import GF.Grammar.Grammar
import GF.Infra.Ident
import GF.Grammar.Macros
import GF.Grammar.PrGrammar

import GF.Data.Operations

lockRecType :: Ident -> Type -> Err Type
lockRecType c t@(RecType rs) = 
  let lab = lockLabel c in
  return $ if elem lab (map fst rs) 
    then t --- don't add an extra copy of the lock field
    else RecType (rs ++ [(lockLabel c,  RecType [])])
lockRecType c t = plusRecType t $ RecType [(lockLabel c,  RecType [])]

unlockRecord :: Ident -> Term -> Err Term
unlockRecord c ft = do
  let (xs,t) = termFormCnc ft
  t' <- plusRecord t $ R [(lockLabel c,  (Just (RecType []),R []))]
  return $ mkAbs xs t'

lockLabel :: Ident -> Label
lockLabel c = LIdent $ "lock_" ++ prt c ----

isLockLabel :: Label -> Bool
isLockLabel l = case l of
  LIdent c -> take 5 c == "lock_"
  _ -> False
