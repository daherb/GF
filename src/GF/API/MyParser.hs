----------------------------------------------------------------------
-- |
-- Module      : MyParser
-- Maintainer  : Peter Ljungl�f
-- Stability   : (stable)
-- Portability : (portable)
--
-- > CVS $Date $ 
-- > CVS $Author $
-- > CVS $Revision $
--
-- template to define your own parser (obsolete?)
-----------------------------------------------------------------------------

module MyParser (myParser) where

import ShellState
import CFIdent
import CF
import Operations

-- type CFParser = [CFTok] -> ([(CFTree,[CFTok])],String)

myParser :: StateGrammar -> CFCat -> CFParser
myParser gr cat toks = ([],"Would you like to add your own parser?")
