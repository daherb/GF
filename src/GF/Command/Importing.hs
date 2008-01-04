module GF.Command.Importing (importGrammar) where

import GF.Compile.API
import GF.GFCC.DataGFCC
import GF.GFCC.API

import GF.Devel.UseIO
import GF.Infra.Option

import Data.List (nubBy)

-- import a grammar in an environment where it extends an existing grammar
importGrammar :: MultiGrammar -> Options -> [FilePath] -> IO MultiGrammar
importGrammar mgr0 opts files = do
  gfcc2 <- case fileSuffix (last files) of
    s | elem s ["gf","gfo"] -> compileToGFCC opts files
    "gfcc" -> 
      mapM file2gfcc files >>= return . foldl1 unionGFCC
  let gfcc3 = unionGFCC (gfcc mgr0) gfcc2
  return $ MultiGrammar gfcc3