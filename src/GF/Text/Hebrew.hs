module Hebrew where

mkHebrew :: String -> String
mkHebrew = mkHebrewWord
--- reverse : assumes everything's on same line

type HebrewChar = Char

-- HH 031103 added code for spooling the markup
-- removed reverse, words, unwords (seemed obsolete and come out wrong on the screen)

mkHebrewWord :: String -> [HebrewChar]
-- mkHebrewWord = map mkHebrewChar

mkHebrewWord s = case s of 
  [] -> [] 
  '<' : cs -> '<' : spoolMarkup cs
  ' ' : cs -> ' ' : mkHebrewWord cs
  c1 : cs -> mkHebrewChar c1 : mkHebrewWord cs

spoolMarkup :: String -> String
spoolMarkup s = case s of
  [] -> [] -- Shouldn't happen
  '>' : cs -> '>' : mkHebrewWord cs  
  c1 : cs -> c1 : spoolMarkup cs

mkHebrewChar c = case lookup c cc of Just c' -> c' ; _ -> c 
 where 
   cc = zip allHebrewCodes allHebrew

allHebrewCodes = "-abgdhwzHTyKklMmNnSoPpCcqrst"

allHebrew :: String
allHebrew = (map toEnum (0x05be : [0x05d0 .. 0x05ea]))


