----------------------------------------------------------------------
-- |
-- Module      : (Module)
-- Maintainer  : (Maintainer)
-- Stability   : (stable)
-- Portability : (portable)
--
-- > CVS $Date $ 
-- > CVS $Author $
-- > CVS $Revision $
--
-- (Description of the module)
-----------------------------------------------------------------------------

module GetGFC (getCanonModule, getCanonGrammar) where

import Operations
import ParGFC
import GFC
import MkGFC
import Modules
import GetGrammar (err2err) ---
import UseIO

getCanonModule :: FilePath -> IOE CanonModule
getCanonModule file = do
  gr <- getCanonGrammar file
  case modules gr of
    [m] -> return m
    _ -> ioeErr $ Bad "expected exactly one module in a file"

getCanonGrammar :: FilePath -> IOE CanonGrammar
getCanonGrammar file = do
  s <- ioeIO $ readFileIf file
  -- c <- ioeErr $ err2err $ pCanon $ myLexer s
  c <- ioeErr $ pCanon $ myLexer s
  return $ canon2grammar c
