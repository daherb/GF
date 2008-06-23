module Main where

import System

-- Make commands for compiling and testing resource grammars.
-- usage: runghc Make present? (lang | api | math | pgf | test | demo | clean)?
-- With no argument, lang and api are done, in this order.
-- See 'make' below for what is done by which command.

langs = [
  ("arabic",   "Ara"),
  ("bulgarian","Bul"),
  ("catalan",  "Cat"),
  ("danish",   "Dan"),
  ("english",  "Eng"),
  ("finnish",  "Fin"),
  ("french",   "Fre"),
  ("hindi",    "Hin"),
  ("german",   "Ger"),
  ("interlingua","Ina"),
  ("italian",  "Ita"),
  ("norwegian","Nor"),
  ("russian",  "Rus"),
  ("spanish",  "Spa"),
  ("swedish",  "Swe"),
  ("thai",     "Tha")
  ]

-- languagues for which to compile Lang
langsLang = langs `except` ["Ara"]

-- languages for which to compile Try 
langsAPI  = langsLang `except` ["Bul","Cat","Hin","Ina","Rus","Tha"]

-- languages for which to compile Mathematical 
langsMath = langsAPI

-- languages for which to run treebank test
langsTest = langsLang `except` ["Bul","Cat","Hin","Rus","Spa","Tha"]

-- languages for which to run demo test
langsDemo = langsLang `except` ["Bul","Hin","Ina","Rus","Tha"] ---- fix utf8 for Bul,Rus

-- languages for which langs.pgf is built
langsPGF = langsTest `only` ["Eng","Fre","Swe"]

treebankExx = "exx-resource.gft"
treebankResults = "exx-resource.gftb"

main = do
  xx <- getArgs
  make xx

make xx = do
  let ifx  opt act = if null xx || elem opt xx then act >> return () else return () 
  let ifxx opt act = if            elem opt xx then act >> return () else return () 
  let pres = elem "present" xx
  let dir = if pres then "../present" else "../alltenses"
  ifx "lang" $ do
    mapM_ (gfc pres [] . lang) langsLang
    system $ "cp */*.gfo " ++ dir
  ifx "api" $ do
    mapM_ (gfc pres presApiPath . try) langsAPI
    system $ "cp */*.gfo " ++ dir
  ifx "math" $ do
    mapM_ (gfc False [] . math) langsMath
    system $ "cp mathematical/*.gfo ../mathematical"
    mapM_ (gfc False [] . symbolic) langsMath
    system $ "cp mathematical/Symbolic*.gfo ../mathematical"
  ifxx "pgf" $ do
    system $ "gfc -s --make --name=langs --parser=off --output-dir=" ++ dir ++ " " ++
              unwords [dir ++ "/Lang" ++ la ++ ".gfo" | (_,la) <- langsPGF] ++
              " +RTS -K100M"
  ifxx "test" $ do
    gf treeb $ unwords [dir ++ "/Lang" ++ la ++ ".gfo" | (_,la) <- langsTest]
  ifxx "demo" $ do
    gf demos $ unwords ["demo/Demo" ++ la ++ ".gf" | (_,la) <- langsDemo]
  ifxx "clean" $ do
    system "rm */*.gfo ../alltenses/*.gfo ../present/*.gfo"
  return ()

gfc pres ppath file = do
  let preproc = if pres then " -preproc=./mkPresent " else ""
  let path    = if pres then ppath else ""
  putStrLn $ "compiling " ++ file
  system $ "gfc -s -src " ++ preproc ++ path ++ file

gf comm file = do
  putStrLn $ "reading " ++ file
  system $ "echo \"" ++ comm ++ "\" | gf3 -s " ++ file

treeb = "rf -lines -tree -file=" ++ treebankExx ++ 
        " | l -treebank | wf -file=" ++ treebankResults

demos = "gr -number=100 | l -treebank | ps -to_utf8 -to_html | wf -file=resdemo.html"

lang (lla,la) = lla ++ "/Lang" ++ la ++ ".gf"
try  (lla,la) = "api/Try"  ++ la ++ ".gf"
math (lla,la) = "mathematical/Mathematical"  ++ la ++ ".gf"
symbolic (lla,la) = "mathematical/Symbolic"  ++ la ++ ".gf"

except ls es = filter (flip notElem es . snd) ls
only   ls es = filter (flip elem es . snd) ls

presApiPath = " -path=api:present "

