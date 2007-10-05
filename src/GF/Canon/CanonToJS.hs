module GF.Canon.CanonToJS (prCanon2js) where

import GF.Canon.GFC
import GF.Canon.CanonToGFCC
import GF.Canon.Look
import GF.Data.ErrM
import GF.Infra.Option
import qualified GF.GFCC.Macros as M
import qualified GF.GFCC.DataGFCC as D
import qualified GF.GFCC.AbsGFCC as C
import qualified GF.JavaScript.AbsJS as JS
import qualified GF.JavaScript.PrintJS as JS


import Control.Monad (mplus)
import Data.Maybe (fromMaybe)
import qualified Data.Map as Map

prCanon2js :: Options -> CanonGrammar -> String
prCanon2js opts gr = gfcc2js start $ mkCanon2gfcc gr
  where 
    start = fromMaybe "S" (getOptVal opts gStartCat 
                           `mplus` getOptVal grOpts gStartCat)
    grOpts = errVal noOptions $ lookupOptionsCan gr

gfcc2js :: String -> D.GFCC -> String
gfcc2js start gfcc =
  JS.printTree $ JS.Program $ abstract2js start n as ++ 
  concatMap (concrete2js n) cs
 where
   n  = D.absname gfcc
   as = D.abstract gfcc
   cs = Map.assocs (D.concretes gfcc)

abstract2js :: String -> C.CId -> D.Abstr -> [JS.Element]
abstract2js start (C.CId n) ds = 
    [JS.ElStmt $ JS.SDeclOrExpr $ JS.Decl [JS.DInit a (new "Abstract" [JS.EStr start])]] 
    ++ concatMap (absdef2js a) (Map.assocs (D.funs ds))
  where a = JS.Ident n

absdef2js :: JS.Ident -> (C.CId,(C.Type,C.Exp)) -> [JS.Element]
absdef2js a (C.CId f,(typ,_)) =
  let (args,C.CId cat) = M.catSkeleton typ in 
    [JS.ElStmt $ JS.SDeclOrExpr $ JS.DExpr $ JS.ECall (JS.EMember (JS.EVar a) (JS.Ident "addType")) 
           [JS.EStr f, JS.EArray [JS.EStr x | C.CId x <- args], JS.EStr cat]]

concrete2js :: C.CId -> (C.CId,D.Concr) -> [JS.Element]
concrete2js (C.CId a) (C.CId c, cnc) =
    [JS.ElStmt $ JS.SDeclOrExpr $ JS.Decl [JS.DInit l (new "Concrete" [JS.EVar (JS.Ident a)])]] 
    ++ concatMap (cncdef2js l) ds
  where 
   l  = JS.Ident c
   ds = Map.assocs $ D.lins cnc

cncdef2js :: JS.Ident -> (C.CId,C.Term) -> [JS.Element]
cncdef2js l (C.CId f, t) = 
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

tokn2js :: C.Tokn -> JS.Expr
tokn2js (C.KS s) = new "Str" [JS.EStr s]
tokn2js (C.KP ss vs) = new "Seq" (map JS.EStr ss) -- FIXME

argIdent :: Integer -> JS.Ident
argIdent n = JS.Ident ("x" ++ show n)

children :: JS.Ident
children = JS.Ident "cs"

new :: String -> [JS.Expr] -> JS.Expr
new f xs = JS.ENew (JS.Ident f) xs
