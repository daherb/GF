module Main where

import Operations
import UseIO
import Option
import IOGrammar
import ShellState
import Shell
import SubShell
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
      java    = oElem forJava os
      isNew   = oElem newParser os ---- temporary hack to have two parallel GUIs
  putStrLn $ if java then encodeUTF8 welcomeMsg else welcomeMsg
  st <- case fs of 
    _ -> useIOE emptyShellState $ foldM (shellStateFromFiles os) emptyShellState fs
  ---  _ -> return emptyShellState
  if null fs then return () else putCPU 
  if java then sessionLineJ isNew st else do
  gfInteract (initHState st) 
  return ()

gfInteract :: HState -> IO HState
gfInteract st@(env,_) = do
  -- putStrFlush "> " M.F 25/01-02 prompt moved to Arch.
  (s,cs) <- getCommandLines
  case ifImpure cs of

    -- these are the three impure commands
    Just (ICQuit,_) -> do
      putStrLn "See you."
      return st
    Just (ICExecuteHistory file,_) -> do
      ss  <- readFileIf file
      let co = pCommandLines ss
      st' <- execLinesH s co st      
      gfInteract st'      
    Just (ICEarlierCommand i,_) -> do
      let line = earlierCommandH st i
          co   = pCommandLine $ words line
      st' <- execLinesH line [co] st       -- s would not work in execLinesH
      gfInteract st'
    Just (ICEditSession,os) -> 
      editSession (addOptions os opts) env >> gfInteract st
    Just (ICTranslateSession,os) -> 
      translateSession (addOptions os opts) env >> gfInteract st
    -- this is a normal command sequence
    _ -> do
      st' <- execLinesH s cs st
      gfInteract st'
   where
     opts = globalOptions env

welcomeMsg = 
  "Welcome to " ++ authorMsg ++++ welcomeArch ++ "\n\nType 'h' for help."

authorMsg = unlines [
 "Grammatical Framework, Version 2-beta (incomplete functionality)",
 "November 25, 2003", 
--- "Compiled March 26, 2003",
 "Compiled " ++ today,
 "Copyright (c) Markus Forsberg, Thomas Hallgren, Harald Hammarstr�m,",
 "Kristofer Johannisson, Janna Khegai, Peter Ljungl�f, Petri M�enp��,", 
 "and Aarne Ranta, 1998-2003, under GNU General Public License (GPL)",
 "Bug reports to aarne@cs.chalmers.se"
 ]
