----------------------------------------------------------------------
-- |
-- Module      : Comments
-- Maintainer  : (Maintainer)
-- Stability   : (stable)
-- Portability : (portable)
--
-- > CVS $Date: 2005/04/21 16:22:34 $ 
-- > CVS $Author: bringert $
-- > CVS $Revision: 1.5 $
--
-- comment removal
-----------------------------------------------------------------------------

module GF.Infra.Comments ( remComments
		) where

-- | comment removal : line tails prefixed by -- as well as chunks in @{- ... -}@
remComments :: String -> String
remComments s = 
  case s of
    '"':s2 -> '"':pass remComments s2 -- comment marks in quotes not removed!
    '{':'-':cs -> readNested cs
    '-':'-':cs -> readTail cs
    c:cs -> c : remComments cs
    [] -> []
   where
     readNested t = 
       case t of
         '"':s2 -> '"':pass readNested s2
         '-':'}':cs -> remComments cs
         _:cs -> readNested cs
         [] -> []
     readTail t = 
       case t of
         '\n':cs -> '\n':remComments cs
         _:cs -> readTail cs
         [] -> []
     pass f t = 
       case t of
         '"':s2 -> '"': f s2
         c:s2 -> c:pass f s2
         _ -> t
