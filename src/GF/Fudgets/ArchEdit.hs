----------------------------------------------------------------------
-- |
-- Module      : (Module)
-- Maintainer  : (Maintainer)
-- Stability   : (stable)
-- Portability : (portable)
--
-- > CVS $Date: 2005/02/18 19:21:10 $ 
-- > CVS $Author: peb $
-- > CVS $Revision: 1.3 $
--
-- (Description of the module)
-----------------------------------------------------------------------------

module ArchEdit (
  fudlogueEdit, fudlogueWrite, fudlogueWriteUni
 ) where

import CommandF
import UnicodeF

-- architecture/compiler dependent definitions for unix/ghc, if Fudgets works.
-- If not, use the modules in for-ghci

fudlogueEdit font = fudlogueEditF ----
fudlogueWrite = fudlogueWriteU
fudlogueWriteUni _ _ = do
  putStrLn "sorry no unicode available in ghc"


