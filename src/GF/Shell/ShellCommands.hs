module ShellCommands where

import qualified Ident as I
import ShellState
import Custom
import PrGrammar

import Option
import Operations

import Char (isDigit)

-- shell commands and their options
-- moved to separate module and added option check: AR 27/5/2004
--- TODO: single source for 
---   (1) command interpreter (2) option check (3) help file

data Command =
   CImport FilePath
 | CRemoveLanguage Language
 | CEmptyState
 | CStripState
 | CTransformGrammar FilePath
 | CConvertLatex FilePath

 | CLinearize [()] ---- parameters
 | CParse
 | CTranslate Language Language
 | CGenerateRandom
 | CGenerateTrees
 | CPutTerm
 | CWrapTerm I.Ident
 | CMorphoAnalyse
 | CTestTokenizer
 | CComputeConcrete String
 | CShowOpers String

 | CTranslationQuiz Language Language
 | CTranslationList Language Language Int
 | CMorphoQuiz
 | CMorphoList Int

 | CReadFile   FilePath
 | CWriteFile  FilePath
 | CAppendFile FilePath
 | CSpeakAloud
 | CPutString
 | CShowTerm
 | CSystemCommand String

 | CSetFlag
 | CSetLocalFlag Language

 | CPrintGrammar
 | CPrintGlobalOptions
 | CPrintLanguages
 | CPrintInformation I.Ident
 | CPrintMultiGrammar
 | CPrintGramlet 
 | CPrintCanonXML
 | CPrintCanonXMLStruct 
 | CPrintHistory
 | CHelp (Maybe String)

 | CImpure ImpureCommand

 | CVoid

-- to isolate the commands that are executed on top level
data ImpureCommand = 
    ICQuit | ICExecuteHistory FilePath | ICEarlierCommand Int
  | ICEditSession | ICTranslateSession

type CommandOpt = (Command, Options)

-- the top-level option warning action

checkOptions :: ShellState -> (Command,Options) -> IO ()
checkOptions sh (co, Opts opts) = do
  let (_,s) = errVal ([],"option check failed") $ mapErr check opts
  if (null s) then return () 
    else putStr "WARNING: " >> putStrLn s
 where 
   check = isValidOption sh co

isValidOption :: ShellState -> Command -> Option -> Err ()
isValidOption st co op = case op of
     Opt (o,[])  -> 
       testErr (elem o $ optsOf co) ("invalid option:" +++ prOpt op)
     Opt (o,[x]) -> do
       testErr (elem o (flagsOf co)) ("invalid flag:" +++ o) 
       testValidFlag st o x
     _ -> Bad $ "impossible option" +++ prOpt op
  where
   optsOf  co = ("tr" :) $ fst $ optionsOfCommand co
   flagsOf co = snd $ optionsOfCommand co

testValidFlag :: ShellState -> OptFunId -> String -> Err ()
testValidFlag st f x = case f of
  "cat"     -> testIn (map prQIdent_ (allCategories st))
  "lang"    -> testIn (map prt (allLanguages st))
  "res"     -> testIn (map prt (allResources (srcModules st)))
  "number"  -> testN
  "printer" -> testInc customGrammarPrinter
  "lexer"   -> testInc customTokenizer
  "unlexer" -> testInc customUntokenizer
  "depth"   -> testN
  "rawtrees"-> testN
  "parser"  -> testInc customParser
  "alts"    -> testN
  "transform" -> testInc customTermCommand
  "filter"  -> testInc customStringCommand
  "length"  -> testN
  _ -> return ()
 where
   testInc ci = 
     let vs = snd (customInfo ci) in testIn vs 
   testIn vs =
     if elem x vs
        then return ()
        else Bad ("flag:" +++ f +++ "invalid value:" +++ x ++++
                  "possible values:" +++ unwords vs)
   testN = 
     if all isDigit x
        then return ()
        else Bad ("flag:" +++ f +++ "invalid value:" +++ x ++++
                  "expected integer")


optionsOfCommand :: Command -> ([String],[String])
optionsOfCommand co = case co of
  CImport _ -> both "old v s opt src retain nocf nocheckcirc cflexer"
                    "abs cnc res path"
  CRemoveLanguage _ -> none
  CEmptyState -> none
  CStripState -> none
  CTransformGrammar _ -> flags "printer"
  CConvertLatex _ -> none
  CLinearize _ -> both "utf8 table struct record all" "lang number unlexer"
  CParse -> both "new n ign raw v" "cat lang lexer parser number rawtrees"
  CTranslate _ _ -> opts "cat lexer parser"
  CGenerateRandom -> flags "cat lang number depth"
  CGenerateTrees -> both "metas" "depth alts cat lang number"
  CPutTerm -> flags "transform number"
  CWrapTerm _ -> none
  CMorphoAnalyse -> both "short" "lang"
  CTestTokenizer -> flags "lexer"
  CComputeConcrete _ -> flags "res"
  CShowOpers _ -> flags "res"

  CTranslationQuiz _ _ -> flags "cat"
  CTranslationList _ _ _ ->  flags "cat"
  CMorphoQuiz -> flags "cat lang"
  CMorphoList _ -> flags "cat lang"

  CReadFile _  -> none
  CWriteFile  _ -> none
  CAppendFile _ -> none
  CSpeakAloud -> flags "language"
  CPutString -> flags "filter length"
  CShowTerm -> flags "printer"
  CSystemCommand _ -> none

  CPrintGrammar -> both "utf8" "printer"
  CPrintMultiGrammar -> opts "utf8"

  CHelp _ -> opts "all"

  CImpure ICEditSession -> opts "f"
  CImpure ICTranslateSession -> both "f langs" "cat"

  _ -> none

{-
  CSetFlag
  CSetLocalFlag Language
  CPrintGlobalOptions
  CPrintLanguages
  CPrintInformation I.Ident
  CPrintMultiGrammar
  CPrintGramlet 
  CPrintCanonXML
  CPrintCanonXMLStruct 
  CPrintHistory
  CVoid
-}
 where
   flags fs = ([],words fs)
   opts fs = (words fs,[])
   both os fs = (words os,words fs)
   none = ([],[])
