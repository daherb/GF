import System
import Char
import List

main = do
  xx <- getArgs
  let isLatex = case xx of
        "-tex":_ -> True
        _ -> False 
  writeFile synopsis "GF Resource Grammar Library: Synopsis"
  append "Aarne Ranta"
  space
  include "synopsis-intro.txt"
  title "Categories"
  space
  link "Source 1:" commonAPI
  space
  link "Source 2:" catAPI
  space
  append "==A hierarchic view==\n"
  include "categories-intro.txt"
  append "==Explanations==\n"
  cs1 <- getCats commonAPI
  cs2 <- getCats catAPI
  let cs = sortCats (cs1 ++ cs2)
  delimit $ mkCatTable isLatex cs
  space
  title "Syntax Rules"
  space
  link "Source:" syntaxAPI
  space
  rs <- getRules syntaxAPI
  delimit $ mkSplitTables True isLatex rs
  space
  title "Structural Words"
  space
  link "Source:" structuralAPI
  space
  rs <- rulesTable False isLatex structuralAPI
  delimit rs
  space
  mapM_ (putParadigms isLatex) paradigmFiles
  space
  include "synopsis-browse.txt"
  space
  title "An Example of Usage"
  space
  include "synopsis-example.txt"
  space
  let format = if isLatex then "tex" else "html"
  system $ "txt2tags -t" ++ format ++ " --toc " ++ synopsis
  if isLatex then (system $ "pdflatex synopsis.tex") >> return () else return ()


getCats :: FilePath -> IO [(String, String, String)]
getCats file = do
  ss <- readFile file >>= return . lines
  return $ getrs [] ss
 where
   getrs rs ss = case ss of
     ('-':'-':'.':_):_ -> reverse rs
     [] -> reverse rs
     ('-':'-':_):ss2 -> getrs rs ss2
     s:ss2 -> case words s of
       cat:";":"--":exp -> getrs ((cat,unwords expl, unwords (tail ex)):rs) ss2 where
         (expl,ex) = span (/="e.g.") exp
       _ -> getrs rs ss2

rulesTable :: Bool -> Bool -> FilePath -> IO [String]
rulesTable hasEx isLatex file = do
  rs <- getRules file
  return $ mkTable hasEx isLatex rs


getRules :: FilePath -> IO [(String,String,String)]
getRules file = do
  ss <- readFile file >>= return . lines
  return $ getrs [] ss
 where
   getrs rs ss = case ss of
     ('-':'-':'.':_):_ -> reverse rs
     [] -> reverse rs
     ('-':'-':_):ss2 -> getrs rs ss2
     s:ss2 -> case words s of
       _:_:"overload":_ -> getrs rs ss2
       _:":":_ -> getrs (rule s:rs) ss2
       _ -> getrs rs ss2
   rule s = (name, typ, ex)
       where 
         ws = words s
         name = head ws
         (t,e) = span (/="--") (tail ws)
         typ = unwords $ filtype (drop 1 t)
         filtype = filter (/=";")
         ex = if null e then "" else unwords $ unnumber $ drop 1 e
         unnumber e = case e of
           n:ws | last n == '.' && not (null (init n)) && all isDigit (init n) -> ws
           _ -> e

putParadigms isLatex (lang,file) = do
  title ("Paradigms for " ++ lang)
  space
  link "source" file
  space
  rs <- rulesTable False isLatex file
  space
  delimit rs
  space

inChunks :: Int -> ([a] -> [String]) -> [a] -> [String]
inChunks i f = concat . intersperse ["\n\n"] . map f . chunks i where
  chunks _ [] = []
  chunks i xs = x : chunks i y where (x,y) = splitAt i xs

-- Makes one table per result category.
-- Adds a subsection header for each table.
mkSplitTables :: Bool -> Bool -> [(String,String,String)] -> [String]
mkSplitTables hasEx isLatex rs = concatMap t (sortRules rs)
  where t xs = subtitle (resultCat (head xs)) : mkTable hasEx isLatex xs

mkTable :: Bool -> Bool -> [(String,String,String)] -> [String]
mkTable hasEx isLatex = inChunks chsize (\rs -> header : map (unwords . row) rs)
 where
  chsize = if isLatex then 40 else 1000
  header = if hasEx then "|| Function  | Type  | Example  ||" 
                    else "|| Function  | Type  ||"
  row (name,typ,ex) 
         = if hasEx then ["|", name', "|", typ', "|", ex', "|"]
                    else ["|", name', "|", typ', "|"]
   where 
     name' = ttf name
     typ' = showTyp typ
     ex' = if null ex then "-" else itf ex

mkCatTable :: Bool -> [(String, String, String)] -> [String]
mkCatTable isLatex = inChunks chsize (\rs -> header ++ map mk1 rs)
 where
  header = ["|| Category  | Explanation  | Example  ||"]
  chsize = if isLatex then 40 else 1000
  mk1 (name,expl,ex) = unwords ["|", showCat name, "|", expl, "|", typo ex, "|"]
  typo ex = if take 1 ex == "\"" then itf (init (tail ex)) else ex

synopsis = "synopsis.txt"
commonAPI = "../abstract/Common.gf"
catAPI    = "../abstract/Cat.gf"
syntaxAPI = "../api/Constructors.gf"
structuralAPI = "../abstract/Structural.gf"
paradigmFiles = [
  ("Danish", "../danish/ParadigmsDan.gf"),
  ("English", "../english/ParadigmsEng.gf"),
  ("Finnish", "../finnish/ParadigmsFin.gf"),
  ("French",  "../french/ParadigmsFre.gf"),
  ("German",  "../german/ParadigmsGer.gf"),
  ("Italian",  "../italian/ParadigmsIta.gf"),
  ("Norwegian", "../norwegian/ParadigmsNor.gf"),
  ("Russian", "../russian/ParadigmsRus.gf"),
  ("Spanish",  "../spanish/ParadigmsSpa.gf"),
  ("Swedish",  "../swedish/ParadigmsSwe.gf")
  ]

append s = appendFile synopsis ('\n':s)
title s = append $ "=" ++ s ++ "="
include s = append $ "%!include: " ++ s
space = append "\n"
delimit ss = mapM_ append ss
link s f = append $ s ++ " [``" ++ fa ++ "`` " ++ f ++ "]" where
  fa = "http://www.cs.chalmers.se/~aarne/GF/lib/resource" ++ dropWhile (=='.') f

ttf s = "``" ++ s ++ "``"
itf s = "//" ++ s ++ "//"

-----------------

-- sort category synopsis by category, retain one table
sortCats :: [(String,String,String)] -> [(String,String,String)]
sortCats = sortBy compareCat
  where compareCat (n1,_,_) (n2,_,_) = compare n1 n2

-- sort function synopsis by category, into separate tables
sortRules :: [(String,String,String)] -> [[(String,String,String)]]
sortRules = groupBy sameCat . sortBy compareRules
  where sameCat r1 r2 = resultCat r1 == resultCat r2
        compareRules r1@(n1,_,_) r2@(n2,_,_) 
            = compare (resultCat r1,n1) (resultCat r2,n2)

resultCat :: (String,String,String) -> String
resultCat (_,t,_) = last (words t)


subtitle cat = "==" ++ cat ++ "==" ++ "[" ++ cat ++ "]"

showCat cat = "[" ++ cat ++ " #" ++ cat ++ "]"

showTyp = unwords . map f . words
  where f s | head s == '(' && last s == ')' && isCat c
                = "(" ++ showCat c ++ ")"
            | isCat s = showCat s
            | otherwise = ttf s
         where c = init (tail s)
        isCat cat = cat `notElem` ["Str","Int"]
                    && all (\c -> isAlphaNum c || c == '\'') cat
                    && isUpper (head cat)