----------------------------------------------------------------------
-- |
-- Module      : (Module)
-- Maintainer  : (Maintainer)
-- Stability   : (stable)
-- Portability : (portable)
--
-- > CVS $Date: 2005/02/18 19:21:20 $ 
-- > CVS $Author: peb $
-- > CVS $Revision: 1.32 $
--
-- GF shell command interpreter.
-----------------------------------------------------------------------------

module Shell where

--- abstract away from these?
import Str
import qualified Grammar as G
import qualified Ident as I
import qualified Compute as Co
import qualified CheckGrammar as Ch
import qualified Lookup as L
import qualified GFC
import qualified Look
import qualified CMacros
import qualified GrammarToCanon
import Values
import GetTree

import ShellCommands

import VisualizeGrammar (visualizeCanonGrammar, visualizeSourceGrammar)
import API
import IOGrammar
import Compile
---- import GFTex
import TeachYourself -- also a subshell

import Randomized ---
import Editing (goFirstMeta) ---

import ShellState
import Option
import Information
import HelpFile
import PrOld
import PrGrammar

import Monad (foldM,liftM)
import System (system)
import Random (newStdGen) ----
import Zipper ----

import Operations
import UseIO
import UTF8 (encodeUTF8)

import VisualizeGrammar (visualizeSourceGrammar)

---- import qualified GrammarToGramlet as Gr
---- import qualified GrammarToCanonXML2 as Canon

-- AR 18/4/2000 - 7/11/2001

-- data Command moved to ShellCommands. AR 27/5/2004

type CommandLine = (CommandOpt, CommandArg,  [CommandOpt])

type SrcTerm = G.Term -- term as returned by the command parser

type HState  = (ShellState,([String],Integer)) -- history & CPU

type ShellIO = (HState, CommandArg) -> IO (HState, CommandArg)

initHState :: ShellState -> HState
initHState st = (st,([],0))

cpuHState (_,(_,i)) = i
optsHState (st,_) = globalOptions st
putHStateCPU cpu (st,(h,_)) = (st,(h,cpu))
updateHistory s (st,(h,cpu)) = (st,(s:h,cpu))
earlierCommandH (_,(h,_)) = ((h ++ repeat "") !!) -- empty command if index over

execLinesH :: String -> [CommandLine] -> HState -> IO HState
execLinesH s cs hst@(st, (h, _)) = do
  (_,st') <- execLines True cs hst
  cpu     <- prOptCPU (optsHState st') (cpuHState hst)
  return $ putHStateCPU cpu $ updateHistory s st'

ifImpure :: [CommandLine] -> Maybe (ImpureCommand,Options)
ifImpure cls = foldr (const . Just) Nothing [(c,os) | ((CImpure c,os),_,_) <- cls]

-- the main function: execution of commands. put :: Bool forces immediate output

-- command line with consecutive (;) commands: no value transmitted
execLines :: Bool -> [CommandLine] -> HState -> IO ([String],HState)
execLines put cs st = foldM (flip (execLine put)) ([],st) cs

-- command line with piped (|) commands: no value returned
execLine :: Bool -> CommandLine -> ([String],HState) -> IO ([String],HState)
execLine put (c@(co, os), arg, cs) (outps,st) = do
  (st',val) <- execC c (st, arg)
  let tr = oElem doTrace os || null cs    -- option -tr leaves trace in pipe
      utf = if (oElem useUTF8 os) then encodeUTF8 else id 
      outp = if tr then [utf (prCommandArg val)] else []
  if put then mapM_ putStrLnFlush outp else return ()
  execs cs val (if put then [] else outps ++ outp, st')
 where
    execs []     arg st = return st
    execs (c:cs) arg st = execLine put (c, arg, cs) st

-- individual commands possibly piped: value returned; this is not a state monad
execC :: CommandOpt -> ShellIO
execC co@(comm, opts0) sa@((st,(h,_)),a) = checkOptions st co >> case comm of

  CImport file -> useIOE sa $ do
    st1 <- shellStateFromFiles opts st file
    ioeIO $ changeState (const st1) sa --- \ ((_,h),a) -> ((st,h), a))
  CEmptyState    -> changeState reinitShellState sa
  CChangeMain ma -> changeStateErr (changeMain ma) sa
  CStripState    -> changeState purgeShellState sa

{-
  CRemoveLanguage lan -> changeState (removeLanguage lan) sa
  CTransformGrammar file -> do
    s <- transformGrammarFile opts file
    returnArg (AString s) sa
  CConvertLatex file -> do
    s <- readFileIf file
    returnArg (AString (convertGFTex s)) sa 
-}
  CPrintHistory -> (returnArg $ AString $ unlines $ reverse h) sa
  -- good to have here for piping; eh and ec must be done on outer level

  CLinearize [] ->  
    changeArg (opTS2CommandArg (optLinearizeTreeVal opts gro) . s2t) sa
----  CLinearize m -> changeArg (opTS2CommandArg (optLinearizeArgForm opts gro m)) sa

  CParse     -> do
    warnDiscont opts 
    case optParseArgErrMsg opts gro (prCommandArg a) of
      Ok (ts,msg) -> putStrLnFlush msg >> changeArg (const $ ATrms ts) sa
      Bad msg -> changeArg (const $ AError msg) sa

  CTranslate il ol -> do
    let a' = opST2CommandArg (optParseArgErr opts (sgr il)) a
    returnArg (opTS2CommandArg (optLinearizeTreeVal opts (sgr ol)) a') sa
  CGenerateRandom -> do
    let 
      a' = case a of
        ASTrm _ -> s2t a
        AString _ -> s2t a
        _ -> a
    case a' of
      ATrms (trm:_) -> case tree2exp trm of
        G.EInt _ -> do
          putStrLn "Warning: Number argument deprecated, use gr -number=n instead"
          ts <- randomTreesIO opts gro (optIntOrN opts flagNumber 1)
          returnArg (ATrms ts) sa
        _ -> do
            g    <- newStdGen
            case (goFirstMeta (tree2loc trm) >>= refineRandom g 41 cgr) of
              Ok trm' -> returnArg (ATrms [loc2tree trm']) sa
              Bad s   -> returnArg (AError s) sa
      _ -> do
        ts <- randomTreesIO opts gro (optIntOrN opts flagNumber 1)
        returnArg (ATrms ts) sa
  CGenerateTrees -> do
    let 
      a' = case a of
        ASTrm _ -> s2t a
        AString _ -> s2t a
        _ -> a
      mt = case a' of
        ATrms (tr:_) -> Just tr
        _ -> Nothing
    returnArg (ATrms $ generateTrees opts gro mt) sa


  CPutTerm -> changeArg (opTT2CommandArg (optTermCommand opts gro)  . s2t) sa

----  CWrapTerm f -> changeArg (opTT2CommandArg (return . wrapByFun opts gro f)) sa
  CMorphoAnalyse -> changeArg (AString . morphoAnalyse opts gro . prCommandArg) sa
  CTestTokenizer -> changeArg (AString . optTokenizer opts gro . prCommandArg) sa

  CComputeConcrete t -> do
    m <- return $
         maybe (I.identC "?") id $  -- meaningful if no opers in t 
           maybe (resourceOfShellState st) (return . I.identC) $ -- topmost res
             getOptVal opts useResource             -- flag -res=m
    justOutput opts (putStrLn (err id (prt . stripTerm) (
                string2srcTerm src m t >>= 
                Ch.justCheckLTerm src  >>=
                Co.computeConcrete src))) sa
  CShowOpers t -> do
    m <- return $
         maybe (I.identC "?") id $  -- meaningful if no opers in t 
           maybe (resourceOfShellState st) (return . I.identC) $ -- topmost res
             getOptVal opts useResource             -- flag -res=m
    justOutput opts (putStrLn (err id (unlines . map prOperSignature) (
                string2srcTerm src m t >>= 
                Co.computeConcrete src >>= 
                return . L.opersForType src))) sa


  CTranslationQuiz il ol -> do
    warnDiscont opts 
    justOutput opts (teachTranslation opts (sgr il) (sgr ol)) sa
  CTranslationList il ol n -> do
    warnDiscont opts 
    qs <- transTrainList opts (sgr il) (sgr ol) (toInteger n)
    returnArg (AString $ foldr (+++++) [] [unlines (s:ss) | (s,ss) <- qs]) sa

  CMorphoQuiz -> do
    warnDiscont opts 
    justOutput opts (teachMorpho opts gro) sa
  CMorphoList n -> do 
    warnDiscont opts 
    qs <- useIOE [] $ morphoTrainList opts gro (toInteger n)
    returnArg (AString $ foldr (+++++) [] [unlines (s:ss) | (s,ss) <- qs]) sa

  CReadFile file   -> returnArgIO   (readFileIf file >>= return . AString) sa
  CWriteFile file  -> justOutputArg opts (writeFile file) sa
  CAppendFile file -> justOutputArg opts (appendFile file) sa
  CSpeakAloud      -> justOutputArg opts (speechGenerate opts) sa
  CSystemCommand s -> justOutput    opts (system s >> return ()) sa
  CPutString       -> changeArg    (opSS2CommandArg (optStringCommand opts gro)) sa
-----  CShowTerm        -> changeArg  (opTS2CommandArg (optPrintTerm opts gro) . s2t) sa

  CSetFlag           -> changeState (addGlobalOptions opts0) sa
---- deprec!  CSetLocalFlag lang -> changeState (addLocalOptions lang opts0) sa

  CHelp (Just c) -> returnArg   (AString (txtHelpCommand c)) sa
  CHelp _ -> case opts0 of
    Opts [o] | o == showAll -> returnArg   (AString txtHelpFile) sa
    Opts [o]        -> returnArg   (AString (txtHelpCommand ('-':prOpt o))) sa
    _               -> returnArg   (AString txtHelpFileSummary) sa

  CPrintGrammar       -> returnArg (AString (optPrintGrammar opts gro)) sa
  CPrintGlobalOptions -> justOutput opts (putStrLn  $ prShellStateInfo st) sa
  CPrintInformation c -> justOutput opts (useIOE () $ showInformation opts st c) sa
  CPrintLanguages     -> justOutput opts 
                         (putStrLn $ unwords $ map prLanguage $ allLanguages st) sa
  CPrintMultiGrammar  -> do
    sa' <- changeState purgeShellState sa
    returnArg (AString (optPrintMultiGrammar opts cgr)) sa'
  CShowGrammarGraph  -> do
    ---- sa' <- changeState purgeShellState sa
    let g0 = writeFile "grphtmp.dot" $ visualizeCanonGrammar cgr
        g1 = system "dot -Tps grphtmp.dot >grphtmp.ps" 
        g2 = system "gv grphtmp.ps &" 
        g3 = return () ---- system "rm -f grphtmp.*"
    justOutput opts (g0 >> g1 >> g2 >> g3 >> return ()) sa
  CPrintSourceGrammar -> 
      returnArg (AString (visualizeSourceGrammar src)) sa

----  CPrintGramlet       -> returnArg (AString (Gr.prGramlet st)) sa
----  CPrintCanonXML      -> returnArg (AString (Canon.prCanonXML st False)) sa
----  CPrintCanonXMLStruct -> returnArg (AString (Canon.prCanonXML st True)) sa
  _ -> justOutput opts (putStrLn "command not understood") sa

 where
   sgr = stateGrammarOfLang st
   gro = grammarOfOptState opts st
   opts = addOptions opts0 (globalOptions st)
   src = srcModules st
   cgr = canModules st

   s2t a = case a of
     ASTrm s  -> err AError (ATrms . return) $ string2treeErr gro s
     AString s  -> err AError (ATrms . return) $ string2treeErr gro s
     _ -> a

   warnDiscont os = err putStrLn id $ do
     let c0 = firstAbsCat os gro
     c <- GrammarToCanon.redQIdent c0
     lang <- maybeErr "no concrete" $ languageOfOptState os st
     t <- return $ errVal CMacros.defLinType $ Look.lookupLincat cgr $ CMacros.redirectIdent lang c
     return $ if CMacros.isDiscontinuousCType t 
       then (putStrLn ("Warning: discontinuous category" +++ prt_ c))
       else (return ())

-- commands either change the state or process the argument, but not both
-- some commands just do output

changeState :: ShellStateOper -> ShellIO
changeState f ((st,h),a) = return ((f st,h), a)

changeStateErr :: ShellStateOperErr -> ShellIO
changeStateErr f ((st,h),a) = case f st of
  Ok st' -> return ((st',h), a)
  Bad s  -> return ((st, h),AError s)

changeArg :: (CommandArg -> CommandArg) -> ShellIO
changeArg f (st,a) = return (st, f a)

changeArgMsg :: (CommandArg -> (CommandArg,String)) -> ShellIO
changeArgMsg f (st,a) = do
  let (b,msg) = f a
  putStrLnFlush msg
  return (st, b)

returnArg :: CommandArg -> ShellIO
returnArg = changeArg . const

returnArgIO :: IO CommandArg -> ShellIO
returnArgIO io (st,_) = io >>= (\a -> return (st,a))

justOutputArg :: Options -> (String -> IO ()) -> ShellIO
justOutputArg opts f sa@(st,a) = f (utf (prCommandArg a)) >> return (st, AUnit) 
 where
   utf = if (oElem useUTF8 opts) then encodeUTF8 else id

justOutput :: Options -> IO () -> ShellIO
justOutput opts = justOutputArg opts . const

-- type system for command arguments; instead of plain strings...

data CommandArg = 
   AError  String 
 | ATrms   [Tree] 
 | ASTrm   String   -- to receive from parser 
 | AStrs   [Str] 
 | AString String 
 | AUnit 
  deriving (Eq, Show)

prCommandArg :: CommandArg -> String
prCommandArg arg = case arg of
  AError s   -> s
  AStrs ss   -> sstrV ss
  AString s  -> s
  ATrms []   -> "no tree found"
  ATrms tt   -> unlines $ map prt_Tree tt
  ASTrm s    -> s
  AUnit      -> ""

opSS2CommandArg :: (String -> String) -> CommandArg -> CommandArg
opSS2CommandArg f = AString . f . prCommandArg

opST2CommandArg :: (String -> Err [Tree]) -> CommandArg -> CommandArg
opST2CommandArg f = err AError ATrms . f . prCommandArg

opTS2CommandArg :: (Tree -> String) -> CommandArg -> CommandArg
opTS2CommandArg f (ATrms ts) = AString $ unlines $ map f ts
opTS2CommandArg _ (AError s) = AError ("expected term, but got error:" ++++ s)
opTS2CommandArg _ a = AError ("expected term, but got:" ++++ prCommandArg a)

opTT2CommandArg :: (Tree -> [Tree]) -> CommandArg -> CommandArg
opTT2CommandArg f (ATrms ts) = ATrms $ concat $ map f ts
opTT2CommandArg _ (AError s) = AError ("expected term, but got error:" ++++ s)
opTT2CommandArg _ a = AError ("expected term, but got:" ++++ prCommandArg a)
