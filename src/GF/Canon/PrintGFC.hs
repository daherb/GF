
module PrintGFC where

-- pretty-printer generated by the BNF converter, except handhacked spacing --H

import Ident --H
import AbsGFC
import Char

-- the top-level printing method
printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 (map ($ "") $ d []) "" where
  rend i ss = case ss of
    "NEW"    :ts -> realnew . rend i ts --H
    "<"      :ts -> showString "<" . rend i ts --H
    "$"      :ts -> showString "$" . rend i ts --H
    "?"      :ts -> showString "?" . rend i ts --H
    "["      :ts -> showChar '[' . rend i ts
    "("      :ts -> showChar '(' . rend i ts
    "{"      :ts -> showChar '{' . new (i+1) . rend (i+1) ts
    "}" : ";":ts -> new (i-1) . space "}" . showChar ';' . new (i-1) . rend (i-1) ts
    "}"      :ts -> new (i-1) . showChar '}' . new (i-1) . rend (i-1) ts
    ";"      :ts -> showChar ';' . new i . rend i ts
    t  : "," :ts -> showString t . space "," . rend i ts
    t  : ")" :ts -> showString t . showChar ')' . rend i ts
    t  : "]" :ts -> showString t . showChar ']' . rend i ts
    t  : ">" :ts -> showString t . showString ">" . rend i ts --H
    t  : "." :ts -> showString t . showString "." . rend i ts --H
    t        :ts -> realspace t . rend i ts --H
    _            -> id
  space t = showString t . showChar ' ' -- H 
  realspace t = showString t . (\s -> if null s then "" else (' ':s)) -- H
  new i s   = s  -- H
  realnew = showChar '\n' --H


parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- the printer class does the job
class Print a where
  prt :: Int -> a -> Doc
  prtList :: [a] -> Doc
  prtList = concatD . map (prt 0)

instance Print a => Print [a] where
  prt _ = prtList

instance Print Integer where
  prt _ x = doc (shows x)

instance Print Double where
  prt _ x = doc (shows x)

instance Print Char where
  prt _ s = doc (showChar '\'' . mkEsc '\'' s . showChar '\'')
  prtList s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q s = case s of
  _ | s == q -> showChar '\\' . showChar s
  '\\'-> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  _ -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j<i then parenth else id


instance Print Ident where
  prt _ i = doc (showString $ prIdent i)
  prtList es = case es of
   [] -> (concatD [])
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ",") , prt 0 xs])



instance Print Canon where
  prt i e = case e of
   MGr ids id modules -> prPrec i 0 (concatD [doc (showString "grammar") , prt 0 ids , doc (showString "of") , prt 0 id , doc (showString ";") , prt 0 modules])
   Gr modules -> prPrec i 0 (concatD [prt 0 modules])


instance Print Module where
  prt i e = case e of
   Mod modtype extend open flags defs -> prPrec i 0 (concatD [prt 0 modtype , doc (showString "=") , prt 0 extend , prt 0 open , doc (showString "{") , prt 0 flags , prt 0 defs , doc (showString "}")])

  prtList es = case es of
   [] -> (concatD [])
   x:xs -> (concatD [prt 0 x , prt 0 xs])

instance Print ModType where
  prt i e = case e of
   MTAbs id -> prPrec i 0 (concatD [doc (showString "abstract") , prt 0 id])
   MTCnc id0 id -> prPrec i 0 (concatD [doc (showString "concrete") , prt 0 id0 , doc (showString "of") , prt 0 id])
   MTRes id -> prPrec i 0 (concatD [doc (showString "resource") , prt 0 id])
   MTTrans id0 id1 id -> prPrec i 0 (concatD [doc (showString "transfer") , prt 0 id0 , doc (showString ":") , prt 0 id1 , doc (showString "->") , prt 0 id])


instance Print Extend where
  prt i e = case e of
   Ext ids -> prPrec i 0 (concatD [prt 0 ids , doc (showString "**")])
   NoExt  -> prPrec i 0 (concatD [])


instance Print Open where
  prt i e = case e of
   Opens ids -> prPrec i 0 (concatD [doc (showString "open") , prt 0 ids , doc (showString "in")])
   NoOpens  -> prPrec i 0 (concatD [])


instance Print Flag where
  prt i e = case e of
   Flg id0 id -> prPrec i 0 (concatD [doc (showString "flags") , prt 0 id0 , doc (showString "=") , prt 0 id])

  prtList es = case es of
   [] -> (concatD [])
   x:xs -> (concatD [prt 0 x , doc (showString ";") , prt 0 xs])

instance Print Def where
  prt i e = case e of
   AbsDCat id decls cidents -> prPrec i 0 (concatD [doc (showString "cat") , prt 0 id , doc (showString "[") , prt 0 decls , doc (showString "]") , doc (showString "=") , prt 0 cidents])
   AbsDFun id exp0 exp -> prPrec i 0 (concatD [doc (showString "fun") , prt 0 id , doc (showString ":") , prt 0 exp0 , doc (showString "=") , prt 0 exp])
   AbsDTrans id exp -> prPrec i 0 (concatD [doc (showString "transfer") , prt 0 id , doc (showString "=") , prt 0 exp])
   ResDPar id pardefs -> prPrec i 0 (concatD [doc (showString "param") , prt 0 id , doc (showString "=") , prt 0 pardefs])
   ResDOper id ctype term -> prPrec i 0 (concatD [doc (showString "oper") , prt 0 id , doc (showString ":") , prt 0 ctype , doc (showString "=") , prt 0 term])
   CncDCat id ctype term0 term -> prPrec i 0 (concatD [doc (showString "lincat") , prt 0 id , doc (showString "=") , prt 0 ctype , doc (showString "=") , prt 0 term0 , doc (showString ";") , prt 0 term])
   CncDFun id cident argvars term0 term -> prPrec i 0 (concatD [doc (showString "lin") , prt 0 id , doc (showString ":") , prt 0 cident , doc (showString "=") , doc (showString "\\") , prt 0 argvars , doc (showString "->") , prt 0 term0 , doc (showString ";") , prt 0 term])
   AnyDInd id0 status id -> prPrec i 0 (concatD [prt 0 id0 , prt 0 status , doc (showString "in") , prt 0 id])

  prtList es = case es of
   [] -> (concatD [])
   x:xs -> (concatD [prt 0 x , doc (showString ";"), doc (showString "NEW") , prt 0 xs]) -- H

instance Print ParDef where
  prt i e = case e of
   ParD id ctypes -> prPrec i 0 (concatD [prt 0 id , prt 0 ctypes])

  prtList es = case es of
   [] -> (concatD [])
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString "|") , prt 0 xs])

instance Print Status where
  prt i e = case e of
   Canon  -> prPrec i 0 (concatD [doc (showString "data")])
   NonCan  -> prPrec i 0 (concatD [])


instance Print CIdent where
  prt i e = case e of
   CIQ id0 id -> prPrec i 0 (concatD [prt 0 id0 , doc (showString ".") , prt 0 id])

  prtList es = case es of
   [] -> (concatD [])
   x:xs -> (concatD [prt 0 x , prt 0 xs])

instance Print Exp where
  prt i e = case e of
   EApp exp0 exp -> prPrec i 1 (concatD [prt 1 exp0 , prt 2 exp])
   EProd id exp0 exp -> prPrec i 0 (concatD [doc (showString "(") , prt 0 id , doc (showString ":") , prt 0 exp0 , doc (showString ")") , doc (showString "->") , prt 0 exp])
   EAbs id exp -> prPrec i 0 (concatD [doc (showString "\\") , prt 0 id , doc (showString "->") , prt 0 exp])
   EAtom atom -> prPrec i 2 (concatD [prt 0 atom])
   EData  -> prPrec i 2 (concatD [doc (showString "data")])
   EEq equations -> prPrec i 0 (concatD [doc (showString "{") , prt 0 equations , doc (showString "}")])


instance Print Sort where
  prt i e = case e of
   SType  -> prPrec i 0 (concatD [doc (showString "Type")])


instance Print Equation where
  prt i e = case e of
   Equ apatts exp -> prPrec i 0 (concatD [prt 0 apatts , doc (showString "->") , prt 0 exp])

  prtList es = case es of
   [] -> (concatD [])
   x:xs -> (concatD [prt 0 x , doc (showString ";") , prt 0 xs])

instance Print APatt where
  prt i e = case e of
   APC cident apatts -> prPrec i 0 (concatD [doc (showString "(") , prt 0 cident , prt 0 apatts , doc (showString ")")])
   APV id -> prPrec i 0 (concatD [prt 0 id])
   APS str -> prPrec i 0 (concatD [prt 0 str])
   API n -> prPrec i 0 (concatD [prt 0 n])
   APW  -> prPrec i 0 (concatD [doc (showString "_")])

  prtList es = case es of
   [] -> (concatD [])
   x:xs -> (concatD [prt 0 x , prt 0 xs])

instance Print Atom where
  prt i e = case e of
   AC cident -> prPrec i 0 (concatD [prt 0 cident])
   AD cident -> prPrec i 0 (concatD [doc (showString "<") , prt 0 cident , doc (showString ">")])
   AV id -> prPrec i 0 (concatD [doc (showString "$") , prt 0 id])
   AM n -> prPrec i 0 (concatD [doc (showString "?") , prt 0 n])
   AS str -> prPrec i 0 (concatD [prt 0 str])
   AI n -> prPrec i 0 (concatD [prt 0 n])
   AT sort -> prPrec i 0 (concatD [prt 0 sort])


instance Print Decl where
  prt i e = case e of
   Decl id exp -> prPrec i 0 (concatD [prt 0 id , doc (showString ":") , prt 0 exp])

  prtList es = case es of
   [] -> (concatD [])
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ";") , prt 0 xs])

instance Print CType where
  prt i e = case e of
   RecType labellings -> prPrec i 0 (concatD [doc (showString "{") , prt 0 labellings , doc (showString "}")])
   Table ctype0 ctype -> prPrec i 0 (concatD [doc (showString "(") , prt 0 ctype0 , doc (showString "=>") , prt 0 ctype , doc (showString ")")])
   Cn cident -> prPrec i 0 (concatD [prt 0 cident])
   TStr  -> prPrec i 0 (concatD [doc (showString "Str")])
   TInts n -> prPrec i 0 (concatD [doc (showString "Ints") , prt 0 n])

  prtList es = case es of
   [] -> (concatD [])
   x:xs -> (concatD [prt 0 x , prt 0 xs])

instance Print Labelling where
  prt i e = case e of
   Lbg label ctype -> prPrec i 0 (concatD [prt 0 label , doc (showString ":") , prt 0 ctype])

  prtList es = case es of
   [] -> (concatD [])
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ";") , prt 0 xs])

instance Print Term where
  prt i e = case e of
   Arg argvar -> prPrec i 2 (concatD [prt 0 argvar])
   I cident -> prPrec i 2 (concatD [prt 0 cident])
   Con cident terms -> prPrec i 2 (concatD [doc (showString "<") , prt 0 cident , prt 2 terms , doc (showString ">")])
   LI id -> prPrec i 2 (concatD [doc (showString "$") , prt 0 id])
   R assigns -> prPrec i 2 (concatD [doc (showString "{") , prt 0 assigns , doc (showString "}")])
   P term label -> prPrec i 1 (concatD [prt 2 term , doc (showString ".") , prt 0 label])
   T ctype cases -> prPrec i 1 (concatD [doc (showString "table") , prt 0 ctype , doc (showString "{") , prt 0 cases , doc (showString "}")])
   V ctype terms -> prPrec i 1 (concatD [doc (showString "table") , prt 0 ctype , doc (showString "[") , prt 2 terms , doc (showString "]")])
   S term0 term -> prPrec i 1 (concatD [prt 1 term0 , doc (showString "!") , prt 2 term])
   C term0 term -> prPrec i 0 (concatD [prt 0 term0 , doc (showString "++") , prt 1 term])
   FV terms -> prPrec i 1 (concatD [doc (showString "variants") , doc (showString "{") , prt 2 terms , doc (showString "}")])
   EInt n -> prPrec i 2 (concatD [prt 0 n])
   K tokn -> prPrec i 2 (concatD [prt 0 tokn])
   E  -> prPrec i 2 (concatD [doc (showString "[") , doc (showString "]")])

  prtList es = case es of
   [] -> (concatD [])
   x:xs -> (concatD [prt 2 x , prt 2 xs])

instance Print Tokn where
  prt i e = case e of
   KS str -> prPrec i 0 (concatD [prt 0 str])
   KM str -> prPrec i 0 (concatD [prt 0 str])
   KP strs variants -> prPrec i 0 (concatD [doc (showString "[") , doc (showString "pre") , prt 0 strs , doc (showString "{") , prt 0 variants , doc (showString "}") , doc (showString "]")])


instance Print Assign where
  prt i e = case e of
   Ass label term -> prPrec i 0 (concatD [prt 0 label , doc (showString "=") , prt 0 term])

  prtList es = case es of
   [] -> (concatD [])
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ";") , prt 0 xs])

instance Print Case where
  prt i e = case e of
   Cas patts term -> prPrec i 0 (concatD [prt 0 patts , doc (showString "=>") , prt 0 term])

  prtList es = case es of
   [] -> (concatD [])
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ";") , prt 0 xs])

instance Print Variant where
  prt i e = case e of
   Var strs0 strs -> prPrec i 0 (concatD [prt 0 strs0 , doc (showString "/") , prt 0 strs])

  prtList es = case es of
   [] -> (concatD [])
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ";") , prt 0 xs])

instance Print Label where
  prt i e = case e of
   L id -> prPrec i 0 (concatD [prt 0 id])
   LV n -> prPrec i 0 (concatD [doc (showString "$") , prt 0 n])


instance Print ArgVar where
  prt i e = case e of
   A id n -> prPrec i 0 (concatD [prt 0 id , doc (showString "@") , prt 0 n])
   AB id n0 n -> prPrec i 0 (concatD [prt 0 id , doc (showString "+") , prt 0 n0 , doc (showString "@") , prt 0 n])

  prtList es = case es of
   [] -> (concatD [])
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ",") , prt 0 xs])

instance Print Patt where
  prt i e = case e of
   PC cident patts -> prPrec i 0 (concatD [doc (showString "(") , prt 0 cident , prt 0 patts , doc (showString ")")])
   PV id -> prPrec i 0 (concatD [prt 0 id])
   PW  -> prPrec i 0 (concatD [doc (showString "_")])
   PR pattassigns -> prPrec i 0 (concatD [doc (showString "{") , prt 0 pattassigns , doc (showString "}")])
   PI n -> prPrec i 0 (concatD [prt 0 n])

  prtList es = case es of
   [] -> (concatD [])
   x:xs -> (concatD [prt 0 x , prt 0 xs])

instance Print PattAssign where
  prt i e = case e of
   PAss label patt -> prPrec i 0 (concatD [prt 0 label , doc (showString "=") , prt 0 patt])

  prtList es = case es of
   [] -> (concatD [])
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ";") , prt 0 xs])


