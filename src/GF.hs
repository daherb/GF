module Main where

import GFModes
import Operations
import UseIO
import Option
import IOGrammar
import ShellState
import Shell
import SubShell
import ShellCommands
import PShell
import JGF
import UTF8

import Today (today)
import Arch
import System (getArgs)
import Monad (foldM)

-- AR 19/4/2000 -- 11/11/2001

main :: IO ()
main = do
  xs <- getArgs
  let (os,fs) = getOptions "-" xs
      opt j   = oElem j os
      st0     = optInitShellState os
      ifNotSil c = if oElem beSilent os then return () else c 
  case 0 of

    _ | opt getHelp -> do
      putStrLnFlush $ encodeUTF8 helpMsg

    _ | opt forJava -> do
      putStrLnFlush $ encodeUTF8 welcomeMsg 
      st <- useIOE st0 $ 
              foldM (shellStateFromFiles os) st0 fs
      sessionLineJ True st
      return ()

    _ | opt doMake -> do
      case fs of
        [f] -> batchCompile os f
        _ -> putStrLnFlush "expecting exactly one gf file to compile"

    _ | opt doBatch -> do
      if opt beSilent then return () else putStrLnFlush "<gfbatch>"
      st <- useIOE st0 $ 
              foldM (shellStateFromFiles os) st0 fs
      gfBatch (initHState st) 
      if opt beSilent then return () else putStrLnFlush "</gfbatch>"
      return ()
    _ -> do

      ifNotSil $ putStrLnFlush $ welcomeMsg
      st <- useIOE st0 $ 
              foldM (shellStateFromFiles os) st0 fs
      if null fs then return () else (ifNotSil putCPU) 
      gfInteract (initHState st) 
      return ()

helpMsg = unlines [
  "Usage: gf <option>* <file>*",
  "Options:",
  "  -make    batch-compile files",
  "   -noemit do not emit code when compiling",
  "   -v      be verbose when compiling",
  "  -batch   structure session by XML tags (use > to send into a file)",
  "  -help    show this message",
  "To use the GUI: jgf <option>* <file>*"
  ]

welcomeMsg = 
  "Welcome to " ++ authorMsg ++++ welcomeArch ++ "\n\nType 'h' for help."

authorMsg = unlines [
 "Grammatical Framework, Version 2.1",
 "Compiled " ++ today,
 "Copyright (c)", 
 "Bj�rn Bringert, Markus Forsberg, Thomas Hallgren, Harald Hammarstr�m,",
 "Kristofer Johannisson, Janna Khegai, Peter Ljungl�f, Petri M�enp��,", 
 "and Aarne Ranta, 1998-2004, under GNU General Public License (GPL)",
 "Bug reports to aarne@cs.chalmers.se"
 ]
