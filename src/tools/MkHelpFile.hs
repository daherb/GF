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
-- Compile HelpFile.hs from HelpFile.
-----------------------------------------------------------------------------

module Main where

main = do
  s <- readFile "HelpFile"
  let s' = mkHsFile (lines s)
  writeFile "HelpFile.hs" s'

mkHsFile ss =
  helpHeader ++
  "module HelpFile where\n\n" ++
  "import Operations\n\n" ++
  "txtHelpFileSummary =\n" ++
  "  unlines $ map (concat . take 1 . lines) $ paragraphs txtHelpFile\n\n" ++
  "txtHelpCommand c =\n" ++ 
  "  case lookup c [(takeWhile (/=',') p,p) | p <- paragraphs txtHelpFile] of\n" ++
  "    Just s -> s\n" ++
  "    _ -> \"Command not found.\"\n\n" ++
  "txtHelpFile =\n" ++
  unlines (map mkOne ss) ++
  "  []"

mkOne s = "  \"" ++ pref s ++ (escs s) ++ "\" ++"
 where 
   pref (' ':_) = "\\n"
   pref _ = "\\n" ---
   escs [] = []
   escs (c:cs) | elem c "\"\\" = '\\':c:escs cs
   escs (c:cs) = c:escs cs

helpHeader = unlines [
  "----------------------------------------------------------------------",
  "-- |",
  "-- Module      : HelpFile",
  "-- Maintainer  : Aarne Ranta",
  "-- Stability   : (stable)",
  "-- Portability : (portable)",
  "--",
  "-- > CVS $Date $", 
  "-- > CVS $Author $",
  "-- > CVS $Revision $",
  "--",
  "-- Help on shell commands. Generated from HelpFile by 'make help'.",
  "-----------------------------------------------------------------------------",
  "",
  ""
  ]