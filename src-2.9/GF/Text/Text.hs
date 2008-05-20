----------------------------------------------------------------------
-- |
-- Module      : Text
-- Maintainer  : AR
-- Stability   : (stable)
-- Portability : (portable)
--
-- > CVS $Date: 2005/06/23 14:32:44 $ 
-- > CVS $Author: aarne $
-- > CVS $Revision: 1.10 $
--
-- elementary text postprocessing. AR 21\/11\/2001.
--
-- This is very primitive indeed. The functions should work on
-- token lists and not on strings. AR 5\/12\/2002
--
-- XML hack 14\/8\/2004; not in use yet
-----------------------------------------------------------------------------

module GF.Text.Text (untokWithXML,
	     exceptXML,
	     formatAsTextLit,
	     formatAsCodeLit,
	     formatAsText,
	     formatAsHTML,
	     formatAsLatex,
	     formatAsCode,
	     performBinds,
	     performBindsFinnish,
	     unStringLit,
	     concatRemSpace
	    ) where

import GF.Data.Operations
import Data.Char

-- | does not apply untokenizer within XML tags --- heuristic "< "
-- this function is applied from top level...
untokWithXML :: (String -> String) -> String -> String
untokWithXML unt s = case s of
  '<':cs@(c:_) | isAlpha c -> '<':beg ++ ">" ++ unto (drop 1 rest) where 
                  (beg,rest) = span (/='>') cs
  '<':cs -> '<':unto cs ---
  [] -> []
  _ -> unt beg ++ unto rest where
               (beg,rest) = span (/='<') s
 where
   unto = untokWithXML unt

-- | ... whereas this one is embedded on a branch
exceptXML :: (String -> String) -> String -> String
exceptXML unt s = '<':beg ++ ">" ++ unt (drop 1 rest) where 
  (beg,rest) = span (/='>') s

formatAsTextLit :: String -> String
formatAsTextLit = formatAsText . unwords . map unStringLit . words 
--- hope that there will be deforestation...

formatAsCodeLit :: String -> String
formatAsCodeLit = formatAsCode . unwords . map unStringLit . words 

formatAsText,formatAsHTML,formatAsLatex :: String -> String
formatAsText  = formatAsTextGen (const False) (=="&-") 
formatAsHTML  = formatAsTextGen (\s -> take 1 s == "<" || last s == '>') (const False) 
formatAsLatex = formatAsTextGen ((=="\\") . take 1)  (const False) 

formatAsTextGen :: (String -> Bool) -> (String -> Bool) -> String -> String
formatAsTextGen tag para = unwords . format . cap . words where
  format ws = case ws of
    w :     ww | capit w -> format $ (cap ww)
    w : c : ww | major c -> format $ (w ++ c) :(cap ww)
    w : c : ww | minor c -> format $ (w ++ c) :    ww
    p : c : ww | openp p -> format $ (p ++ c) :ww
    p : c : ww | spanish p -> format $ (p ++ concat (cap [c])) :ww
    c     : ww | para  c -> "\n\n"        : format ww
    w     : ww           -> w             : format ww
    [] -> []
  cap (p:ww) | tag p = p : cap ww
  cap ((c:cs):ww) = (toUpper c : cs) : ww
  cap [] = []
  capit = (=="&|")
  major = flip elem (map singleton ".!?") 
  minor = flip elem (map singleton ",:;)")
  openp = all (flip elem "(")
  spanish = all (flip elem "\161\191")

formatAsCode :: String -> String
formatAsCode = rend 0 . words where
  -- render from BNF Converter
  rend i ss = case ss of
    "["      :ts -> cons "["  $ rend i ts
    "("      :ts -> cons "("  $ rend i ts
    "{"      :ts -> cons "{"  $ new (i+1) $ rend (i+1) ts
    "}" : ";":ts -> new (i-1) $ space "}" $ cons ";" $ new (i-1) $ rend (i-1) ts
    "}"      :ts -> new (i-1) $ cons "}" $ new (i-1) $ rend (i-1) ts
    ";"      :ts -> cons ";"  $ new i $ rend i ts
    t  : "," :ts -> cons t    $ space "," $ rend i ts
    t  : ")" :ts -> cons t    $ cons ")"  $ rend i ts
    t  : "]" :ts -> cons t    $ cons "]"  $ rend i ts
    t        :ts -> space t   $ rend i ts
    _            -> ""
  cons s t  = s ++ t
  new i s   = '\n' : replicate (2*i) ' ' ++ dropWhile isSpace s
  space t s = if null s then t else t ++ " " ++ s

performBinds :: String -> String
performBinds = performBindsOpt (\x y -> y) 


-- The function defines an effect of the former on the latter part,
-- such as in vowel harmony. It is triggered by the binder token "&*"

performBindsOpt :: (String -> String -> String) -> String -> String
performBindsOpt harm = unwords . format . words where
  format ws = case ws of
    w : "&+" : u : ws -> format ((w ++        u) : ws)
    w : "&*" : u : ws -> format ((w ++ harm w u) : ws)
    w : ws            -> w : format ws
    []                -> []

-- unlexer for Finnish particles
-- Notice: left associativity crucial for "tie &* ko &* han" --> "tiek�h�n"

performBindsFinnish :: String -> String
performBindsFinnish = performBindsOpt vowelHarmony where
  vowelHarmony w p = if any (flip elem "aouAOU") w then p else map toFront p
  toFront c = case c of
    'A' -> '\196'
    'O' -> '\214'
    'a' -> '\228'
    'o' -> '\246'
    _ -> c

unStringLit :: String -> String
unStringLit s = case s of
  c : cs | strlim c && strlim (last cs) -> init cs
  _ -> s
 where
   strlim = (=='\'')

concatRemSpace :: String -> String
concatRemSpace = concat . words
{-
concatRemSpace s = case s of
  '<':cs -> exceptXML concatRemSpace cs
  c : cs | isSpace c -> concatRemSpace cs
  c :cs -> c : concatRemSpace cs
  _ -> s
-}
