-- Handles printing a CFGrammar in CFGM format.
module PrintCFGrammar (prCanonAsCFGM) where

import AbsGFC
import Ident
import GFC
import Modules
import qualified ConvertGrammar as Cnv
import qualified PrintParser as Prt
import ErrM

import List (intersperse)
import Maybe (listToMaybe, maybe)

-- FIXME: fix warning about bad -printer= value

prCanonAsCFGM :: CanonGrammar -> String
prCanonAsCFGM gr = unlines $ map (uncurry (prLangAsCFGM gr)) xs 
    where 
    cncs = maybe [] (allConcretes gr) (greatestAbstract gr)
    cncms = map (\i -> (i,fromOk (lookupModule gr i))) cncs
    fromOk (Ok x) = x
    fromOk (Bad y) = error y
    xs = [(i,getFlag fs "startcat") | (i,ModMod (Module{flags=fs})) <- cncms]

-- FIXME: need to look in abstract module too
getFlag :: [Flag] -> String -> Maybe String
getFlag fs x = listToMaybe [v | Flg (IC k) (IC v) <- fs, k == x]

prLangAsCFGM :: CanonGrammar -> Ident -> Maybe String -> String
prLangAsCFGM gr i@(IC lang) start = (header . startcat . rules . footer) ""
    where
    header = showString "grammar " . showString lang . showString "\n"
    startcat = maybe id (\s -> showString "startcat " . showString (s++"{}.s") . showString ";\n") start
    rules0 = map Prt.prt $ Cnv.cfg $ Cnv.pInfo gr i
    rules = showString $ concat $ map (\l -> init l++";\n") rules0 
    footer = showString "end grammar\n"

