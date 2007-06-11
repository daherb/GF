----------------------------------------------------------------------
-- |
-- Module      : Parsing
-- Maintainer  : AR
-- Stability   : (stable)
-- Portability : (portable)
--
-- > CVS $Date: 2005/06/02 10:23:52 $ 
-- > CVS $Author: aarne $
-- > CVS $Revision: 1.25 $
--
-- (Description of the module)
-----------------------------------------------------------------------------

module GF.UseGrammar.Parsing where

import GF.Infra.CheckM
import qualified GF.Canon.AbsGFC as C
import GF.Canon.GFC
import GF.Canon.MkGFC (trExp) ----
import GF.Canon.CMacros
import GF.Grammar.MMacros (refreshMetas)
import GF.UseGrammar.Linear
import GF.Data.Str
import GF.CF.CF
import GF.CF.CFIdent
import GF.Infra.Ident
import GF.Grammar.TypeCheck
import GF.Grammar.Values
--import CFMethod
import GF.UseGrammar.Tokenize
import GF.UseGrammar.Morphology (isKnownWord)
import GF.CF.Profile
import GF.Infra.Option
import GF.UseGrammar.Custom
import GF.Compile.ShellState

import GF.CF.PPrCF (prCFTree)
-- import qualified GF.OldParsing.ParseGFC as NewOld -- OBSOLETE
import qualified GF.Parsing.GFC as New

import GF.Data.Operations

import Data.List (nub,sortBy)
import Data.Char (toLower)
import Control.Monad (liftM)

-- AR 26/1/2000 -- 8/4 -- 28/1/2001 -- 9/12/2002

parseString :: Options -> StateGrammar -> CFCat -> String -> Err [Tree]
parseString os sg cat = liftM fst . parseStringMsg os sg cat

parseStringMsg :: Options -> StateGrammar -> CFCat -> String -> Err ([Tree],String)
parseStringMsg os sg cat s = do
  (ts,(_,ss)) <- checkStart $ parseStringC os sg cat s
  return (ts, unlines $ reverse ss)

parseStringC :: Options -> StateGrammar -> CFCat -> String -> Check [Tree]
parseStringC opts0 sg cat s 
 | oElem (iOpt "old") opts0 ||
   (not (oElem (iOpt "fcfg") opts0) && stateHasHOAS sg) = do
  let opts = unionOptions opts0 $ stateOptions sg
      cf  = stateCF sg
      gr  = stateGrammarST sg
      cn  = cncId sg
      toks = customOrDefault opts useTokenizer customTokenizer sg s
      parser = customOrDefault opts useParser customParser sg cat
  if oElem (iOpt "cut") opts 
    then doUntil (not . null) $ map (tokens2trms opts sg cn parser) toks
    else mapM (tokens2trms opts sg cn parser) toks >>= return . concat

---- | or [oElem p opts0 | 
----        p <- [newCParser,newMParser,newFParser,newParser,newerParser] = do  

 | otherwise = do
  let opts      = unionOptions opts0 $ stateOptions sg
      algorithm | oElem newCParser opts0 = "c"
		| oElem newMParser opts0 = "m"
		| oElem newFParser opts0 = "f"
		| otherwise              = "f" -- default algorithm: FCFG
      strategy  = maybe "bottomup" id $ getOptVal opts useParser 
                      -- -parser=bottomup/topdown
      tokenizer = customOrDefault opts useTokenizer customTokenizer sg
      toks = case tokenizer s of
               t:_ -> t
               _ -> [] ---- no support for undet. tok.
      unknowns = 
        [w | TC w <- toks, unk w && unk (uncap w)] ++ [w | TS w <- toks, unk w]
       where
        unk w = not $ isKnownWord (morpho sg) w
        uncap (c:cs) = toLower c : cs
        uncap s = s

  case unknowns of
    _:_ -> fail $ "Unknown words:" +++ unwords unknowns
    _ -> do  
  
     ts <- checkErr $ New.parse algorithm strategy (pInfo sg) (absId sg) cat toks
     ts' <- checkErr $ 
             allChecks $ map (annotate (stateGrammarST sg) . refreshMetas []) ts
     return $ optIntOrAll opts flagNumber ts'


tokens2trms :: Options ->StateGrammar ->Ident -> CFParser -> [CFTok] -> Check [Tree]
tokens2trms opts sg cn parser toks = trees2trms opts sg cn toks trees info
    where result = parser toks
	  info   = snd result
	  trees  = {- nub $ -} cfParseResults result -- peb 25/5-04: removed nub (O(n^2))

trees2trms :: 
  Options -> StateGrammar -> Ident -> [CFTok] -> [CFTree] -> String -> Check [Tree]
trees2trms opts sg cn as ts0 info = do
  let s = unwords $ map prCFTok as
  ts  <- case () of
    _ | null ts0 -> checkWarn ("No success in cf parsing" +++ s) >> return []
    _ | raw      -> do
      ts1 <- return (map cf2trm0 ts0) ----- should not need annot
      checks [
         mapM (checkErr . (annotate gr) . trExp) ts1 ---- complicated, often fails
        ,checkWarn (unlines ("Raw CF trees:":(map prCFTree ts0))) >> return []
        ]
    _ -> do
      let num = optIntOrN opts flagRawtrees 999999
      let (ts01,rest) = splitAt num ts0
      if null rest then return () 
         else raise ("Warning: only" +++ show num +++ "raw parses out of" +++ 
                          show (length ts0) +++ 
                          "considered; use -rawtrees=<Int> to see more"
                     )
      (ts1,ss) <- checkErr $ mapErrN 1 postParse ts01
      if null ts1 then raise ss else return ()
      ts2 <- checkErr $ 
               allChecks $ map (annotate gr . refreshMetas [] . trExp) ts1 ---- 
      if forgive then return ts2 else do
        let tsss = [(t, allLinsOfTree gr cn t) | t <- ts2]
            ps = [t | (t,ss) <- tsss, 
                      any (compatToks as) (map str2cftoks ss)]
        if null ps 
           then raise $ "Failure in morphology." ++
                  if verb 
                     then "\nPossible corrections: " +++++
                          unlines (nub (map sstr (concatMap snd tsss)))
                     else ""
           else return ps
  if verb 
     then checkWarn $ " the token list" +++ show as ++++ unknownWords sg as +++++ info
     else return ()

  return $ optIntOrAll opts flagNumber $ nub ts
 where
   gr  = stateGrammarST sg

   raw     = oElem rawParse opts
   verb    = oElem beVerbose opts
   forgive = oElem forgiveParse opts

---- Operatins.allChecks :: ErrorMonad m => [m a] -> m [a]

unknownWords sg ts = case filter noMatch [t | t@(TS _) <- ts] of
     [] -> "where all words are known"
     us -> "with the unknown tokens" +++ show us --- needs to be fixed for literals
  where
   terminals = map TS $ stateGrammarWords sg
   noMatch t = all (not . compatTok t) terminals 
     

--- too much type checking in building term info? return FullTerm to save work?

-- | raw parsing: so simple it is for a context-free CF grammar
cf2trm0 :: CFTree -> C.Exp
cf2trm0 (CFTree (fun, (_, trees))) = mkAppAtom (cffun2trm fun) (map cf2trm0 trees)
 where
   cffun2trm (CFFun (fun,_)) = fun
   mkApp = foldl C.EApp
   mkAppAtom a = mkApp (C.EAtom a)
