----------------------------------------------------------------------
-- |
-- Module      : GFCCAPI
-- Maintainer  : Aarne Ranta
-- Stability   : (stable)
-- Portability : (portable)
--
-- > CVS $Date: 
-- > CVS $Author: 
-- > CVS $Revision: 
--
-- Reduced Application Programmer's Interface to GF, meant for
-- embedded GF systems. AR 19/9/2007
-----------------------------------------------------------------------------

module  GF.GFCC.API where

import GF.GFCC.Linearize
import GF.GFCC.Generate
import GF.GFCC.Macros
import GF.GFCC.DataGFCC
import GF.GFCC.CId
import GF.GFCC.Raw.ConvertGFCC
import GF.GFCC.Raw.ParGFCCRaw
import GF.Command.PPrTree

import GF.Data.ErrM

import GF.Parsing.FCFG

--import GF.Data.Operations
--import GF.Infra.UseIO
import qualified Data.Map as Map
import System.Random (newStdGen)
import System.Directory (doesFileExist)


-- This API is meant to be used when embedding GF grammars in Haskell 
-- programs. The embedded system is supposed to use the
-- .gfcc grammar format, which is first produced by the gf program.

---------------------------------------------------
-- Interface
---------------------------------------------------

data MultiGrammar = MultiGrammar {gfcc :: GFCC}
type Language     = String
type Category     = String
type Tree         = Exp

file2grammar :: FilePath -> IO MultiGrammar

linearize    :: MultiGrammar -> Language -> Tree -> String
parse        :: MultiGrammar -> Language -> Category -> String -> [Tree]

linearizeAll     :: MultiGrammar -> Tree -> [String]
linearizeAllLang :: MultiGrammar -> Tree -> [(Language,String)]

parseAll     :: MultiGrammar -> Category -> String -> [[Tree]]
parseAllLang :: MultiGrammar -> Category -> String -> [(Language,[Tree])]

generateAll      :: MultiGrammar -> Category -> [Tree]
generateRandom   :: MultiGrammar -> Category -> IO [Tree]
generateAllDepth :: MultiGrammar -> Category -> Maybe Int -> [Tree]

readTree   :: MultiGrammar -> String -> Tree
showTree   ::                 Tree -> String

languages  :: MultiGrammar -> [Language]
categories :: MultiGrammar -> [Category]

startCat   :: MultiGrammar -> Category

---------------------------------------------------
-- Implementation
---------------------------------------------------

file2grammar f = do
  gfcc <- file2gfcc f
  return (MultiGrammar gfcc)

file2gfcc f = do
  s <- readFileIf f
  g <- parseGrammar s
  return $ toGFCC g

linearize mgr lang = GF.GFCC.Linearize.linearize (gfcc mgr) (mkCId lang)

parse mgr lang cat s = 
  case lookParser (gfcc mgr) (mkCId lang) of
    Nothing    -> error "no parser"
    Just pinfo -> case parseFCF "bottomup" pinfo (mkCId cat) (words s) of
                    Ok x -> x
                    Bad s -> error s

linearizeAll mgr = map snd . linearizeAllLang mgr
linearizeAllLang mgr t = 
  [(lang,linearThis mgr lang t) | lang <- languages mgr]

parseAll mgr cat = map snd . parseAllLang mgr cat

parseAllLang mgr cat s = 
  [(lang,ts) | lang <- languages mgr, let ts = parse mgr lang cat s, not (null ts)]

generateRandom mgr cat = do
  gen <- newStdGen
  return $ genRandom gen (gfcc mgr) (mkCId cat)

generateAll mgr cat = generate (gfcc mgr) (mkCId cat) Nothing
generateAllDepth mgr cat = generate (gfcc mgr) (mkCId cat)

readTree _ = pTree

showTree = prExp

abstractName mgr = prCId (absname (gfcc mgr))

languages mgr = [prCId l | l <- cncnames (gfcc mgr)]

categories mgr = [prCId c | c <- Map.keys (cats (abstract (gfcc mgr)))]

startCat mgr = lookStartCat (gfcc mgr)

emptyMultiGrammar = MultiGrammar emptyGFCC

------------ for internal use only

linearThis = GF.GFCC.API.linearize

err f g ex = case ex of
  Ok x -> g x
  Bad s -> f s

readFileIf f = do
  b <- doesFileExist f
  if b then readFile f 
       else putStrLn ("file " ++ f ++ " not found") >> return ""
