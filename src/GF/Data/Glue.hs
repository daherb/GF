module Glue where

import Trie2
import Operations
import List

-------- AR 8/11/2003, using Markus Forsberg's implementation of Huet's unglue

decomposeSimple :: Trie Char a -> [Char] -> Err [[Char]]
decomposeSimple t s = do
  let ss = map (decompose t) $ words s
  if any null ss
    then Bad "unknown word in input"
    else return $ concat [intersperse "&+" ws | ws <- ss]

exTrie = tcompile (zip ws ws) where 
  ws = words "ett tv� tre tjugo trettio hundra tusen"

