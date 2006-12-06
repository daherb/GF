module GF.Canon.CanonToJS (prCanon2js) where

import GF.Canon.GFC
import GF.Canon.CanonToGFCC
import qualified GF.Canon.GFCC.AbsGFCC as C
import qualified GF.JavaScript.AbsJS as JS
import qualified GF.JavaScript.PrintJS as JS


prCanon2js :: CanonGrammar -> String
prCanon2js gr = gfcc2js $ mkCanon2gfcc gr

gfcc2js :: C.Grammar -> String
gfcc2js (C.Grm _ _ cs) = JS.printTree (concrete2js (head cs)) -- FIXME

concrete2js :: C.Concrete -> JS.Program
concrete2js (C.Cnc (C.CId c) ds) = 
    JS.Program ([JS.ElStmt $ JS.SDeclOrExpr $ JS.Decl [JS.DInit l (new "Linearizer" [])]] 
                ++ concatMap (cncdef2js l) ds)
  where l = JS.Ident c

cncdef2js :: JS.Ident -> C.CncDef -> [JS.Element]
cncdef2js l (C.Lin (C.CId f) t) = 
    [JS.ElStmt $ JS.SDeclOrExpr $ JS.DExpr $ JS.ECall (JS.EMember (JS.EVar l) (JS.Ident "addRule")) [JS.EStr f, JS.EFun [children] [JS.SReturn (term2js l t)]]]

term2js :: JS.Ident -> C.Term -> JS.Expr
term2js l t = f t
  where 
  f t = 
    case t of
      C.R xs           -> new "Arr" (map f xs)
      C.P x y          -> JS.ECall (JS.EMember (f x) (JS.Ident "sel")) [f y]
      C.S xs           -> new "Seq" (map f xs)
      C.K t            -> tokn2js t
      C.V i            -> JS.EIndex (JS.EVar children) (JS.EInt i)
      C.C i            -> new "Int" [JS.EInt i]
      C.F (C.CId f)    -> JS.ECall (JS.EMember (JS.EVar l) (JS.Ident "rule")) [JS.EStr f, JS.EVar children]
      C.FV xs          -> new "Variants" (map f xs)
      C.W str x        -> new "Suffix" [JS.EStr str, f x]
      C.RP x y         -> new "Rp" [f x, f y]
      C.TM             -> new "Meta" []

argIdent :: Integer -> JS.Ident
argIdent n = JS.Ident ("x" ++ show n)

tokn2js :: C.Tokn -> JS.Expr
tokn2js (C.KS s) = new "Str" [JS.EStr s]
tokn2js (C.KP ss vs) = new "Seq" (map JS.EStr ss) -- FIXME

children :: JS.Ident
children = JS.Ident "cs"

new :: String -> [JS.Expr] -> JS.Expr
new f xs = JS.ENew (JS.Ident f) xs
