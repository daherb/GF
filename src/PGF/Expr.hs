module PGF.Expr(Tree(..), Literal(..),                
                readTree, showTree, pTree, ppTree,

                Expr(..), Equation(..),
                readExpr, showExpr, pExpr, ppExpr,

                tree2expr, expr2tree,

                -- needed in the typechecker
                Value(..), Env, eval, apply,

                -- helpers
                pStr,pFactor,

                -- refresh metavariables
                newMetas
               ) where

import PGF.CId

import Data.Char
import Data.Maybe
import Control.Monad
import qualified Text.PrettyPrint as PP
import qualified Text.ParserCombinators.ReadP as RP
import qualified Data.Map as Map

data Literal = 
   LStr String                      -- ^ string constant
 | LInt Integer                     -- ^ integer constant
 | LFlt Double                      -- ^ floating point constant
 deriving (Eq,Ord,Show)

-- | The tree is an evaluated expression in the abstract syntax
-- of the grammar. The type is especially restricted to not
-- allow unapplied lambda abstractions. The tree is used directly 
-- from the linearizer and is produced directly from the parser.
data Tree = 
   Abs [CId] Tree                   -- ^ lambda abstraction. The list of variables is non-empty
 | Var CId                          -- ^ variable
 | Fun CId [Tree]                   -- ^ function application
 | Lit Literal                      -- ^ literal
 | Meta Int                         -- ^ meta variable
  deriving (Eq, Ord)

-- | An expression represents a potentially unevaluated expression
-- in the abstract syntax of the grammar. It can be evaluated with
-- the 'expr2tree' function and then linearized or it can be used
-- directly in the dependent types.
data Expr =
   EAbs CId Expr                    -- ^ lambda abstraction
 | EApp Expr Expr                   -- ^ application
 | ELit Literal                     -- ^ literal
 | EMeta  Int                       -- ^ meta variable
 | EVar   CId                       -- ^ variable or function reference
 | EEq [Equation]                   -- ^ lambda function defined as a set of equations with pattern matching
 | EPi CId Expr Expr                -- ^ dependent function type
  deriving (Eq,Ord)

-- | The equation is used to define lambda function as a sequence
-- of equations with pattern matching. The list of 'Expr' represents
-- the patterns and the second 'Expr' is the function body for this
-- equation.
data Equation =
   Equ [Expr] Expr
  deriving (Eq,Ord,Show)

-- | parses 'String' as an expression
readTree :: String -> Maybe Tree
readTree s = case [x | (x,cs) <- RP.readP_to_S (pTree False) s, all isSpace cs] of
               [x] -> Just x
               _   -> Nothing

-- | renders expression as 'String'
showTree :: Tree -> String
showTree = PP.render . ppTree 0

instance Show Tree where
    showsPrec i x = showString (PP.render (ppTree i x))

instance Read Tree where
    readsPrec _ = RP.readP_to_S (pTree False)

-- | parses 'String' as an expression
readExpr :: String -> Maybe Expr
readExpr s = case [x | (x,cs) <- RP.readP_to_S pExpr s, all isSpace cs] of
               [x] -> Just x
               _   -> Nothing

-- | renders expression as 'String'
showExpr :: Expr -> String
showExpr = PP.render . ppExpr 0

instance Show Expr where
    showsPrec i x = showString (PP.render (ppExpr i x))

instance Read Expr where
    readsPrec _ = RP.readP_to_S pExpr


-----------------------------------------------------
-- Parsing
-----------------------------------------------------

pTrees :: RP.ReadP [Tree]
pTrees = liftM2 (:) (pTree True) pTrees RP.<++ (RP.skipSpaces >> return [])

pTree :: Bool -> RP.ReadP Tree
pTree isNested = RP.skipSpaces >> (pParen RP.<++ pAbs RP.<++ pApp RP.<++ fmap Lit pLit RP.<++ pMeta)
  where 
        pParen = RP.between (RP.char '(') (RP.char ')') (pTree False)
        pAbs = do xs <- RP.between (RP.char '\\') (RP.skipSpaces >> RP.string "->") (RP.sepBy1 (RP.skipSpaces >> pCId) (RP.skipSpaces >> RP.char ','))
                  t  <- pTree False
                  return (Abs xs t)
        pApp = do f  <- pCId
                  ts <- (if isNested then return [] else pTrees)
                  return (Fun f ts)
        pMeta = do RP.char '?'
                   n <- fmap read (RP.munch1 isDigit)
                   return (Meta n)

pExpr :: RP.ReadP Expr
pExpr = RP.skipSpaces >> (pAbs RP.<++ pTerm RP.<++ pEqs)
  where
    pTerm   =       fmap (foldl1 EApp) (RP.sepBy1 pFactor RP.skipSpaces)

    pAbs = do xs <- RP.between (RP.char '\\') (RP.skipSpaces >> RP.string "->") (RP.sepBy1 (RP.skipSpaces >> pCId) (RP.skipSpaces >> RP.char ','))
              e  <- pExpr
              return (foldr EAbs e xs)
               
    pEqs = fmap EEq $
           RP.between (RP.skipSpaces >> RP.char '{')
                      (RP.skipSpaces >> RP.char '}')
                      (RP.sepBy1 (RP.skipSpaces >> pEq) 
                                 (RP.skipSpaces >> RP.string ";"))

    pEq = do pats <- (RP.sepBy1 pExpr RP.skipSpaces)
             RP.skipSpaces >> RP.string "=>"
             e <- pExpr
             return (Equ pats e)

pFactor =       fmap EVar pCId
        RP.<++  fmap ELit pLit
        RP.<++  pMeta
        RP.<++  RP.between (RP.char '(') (RP.char ')') pExpr
  where
    pMeta = do RP.char '?'
               n <- fmap read (RP.munch1 isDigit)
               return (EMeta n)

pLit :: RP.ReadP Literal
pLit = pNum RP.<++ liftM LStr pStr

pNum = do x <- RP.munch1 isDigit
          ((RP.char '.' >> RP.munch1 isDigit >>= \y -> return (LFlt (read (x++"."++y))))
           RP.<++
           (return (LInt (read x))))

pStr = RP.char '"' >> (RP.manyTill (pEsc RP.<++ RP.get) (RP.char '"'))
       where
         pEsc = RP.char '\\' >> RP.get    


-----------------------------------------------------
-- Printing
-----------------------------------------------------

ppTree d (Abs xs t) = ppParens (d > 0) (PP.char '\\' PP.<>
                                        PP.hsep (PP.punctuate PP.comma (map (PP.text . prCId) xs)) PP.<+>
                                        PP.text "->" PP.<+>
                                        ppTree 0 t)
ppTree d (Fun f []) = PP.text (prCId f)
ppTree d (Fun f ts) = ppParens (d > 0) (PP.text (prCId f) PP.<+> PP.hsep (map (ppTree 1) ts))
ppTree d (Lit l)    = ppLit l
ppTree d (Meta n)   = PP.char '?' PP.<> PP.int n
ppTree d (Var id)   = PP.text (prCId id)


ppExpr d (EAbs x e)   = let (xs,e1) = getVars (EAbs x e)
                        in ppParens (d > 0) (PP.char '\\' PP.<>
                                             PP.hsep (PP.punctuate PP.comma (map (PP.text . prCId) xs)) PP.<+>
                                             PP.text "->" PP.<+>
                                             ppExpr 0 e1)
                        where
                          getVars (EAbs x e) = let (xs,e1) = getVars e in (x:xs,e1)
                          getVars e          = ([],e)
ppExpr d (EApp e1 e2) = ppParens (d > 1) ((ppExpr 1 e1) PP.<+> (ppExpr 2 e2))
ppExpr d (ELit l)     = ppLit l
ppExpr d (EMeta n)    = PP.char '?' PP.<+> PP.int n
ppExpr d (EVar f)     = PP.text (prCId f)
ppExpr d (EEq eqs)    = PP.braces (PP.sep (PP.punctuate PP.semi (map ppEquation eqs)))

ppEquation (Equ pats e) = PP.hsep (map (ppExpr 2) pats) PP.<+> PP.text "=>" PP.<+> ppExpr 0 e

ppLit (LStr s) = PP.text (show s)
ppLit (LInt n) = PP.integer n
ppLit (LFlt d) = PP.double d

ppParens True  = PP.parens
ppParens False = id


-----------------------------------------------------
-- Evaluation
-----------------------------------------------------

-- | Converts a tree to expression.
tree2expr :: Tree -> Expr
tree2expr (Fun x ts) = foldl EApp (EVar x) (map tree2expr ts) 
tree2expr (Lit l)    = ELit l
tree2expr (Meta n)   = EMeta n
tree2expr (Abs xs t) = foldr EAbs (tree2expr t) xs
tree2expr (Var x)    = EVar x

-- | Converts an expression to tree. If the expression
-- contains unevaluated applications they will be applied.
expr2tree :: Expr -> Tree
expr2tree e = value2tree (eval Map.empty e) [] []
  where
    value2tree (VApp v1 v2)              xs ts = value2tree v1 xs (value2tree v2 [] []:ts)
    value2tree (VVar x)                  xs ts = ret xs (fun xs x ts)
    value2tree (VMeta n)                 xs [] = ret xs (Meta n)
    value2tree (VLit l)                  xs [] = ret xs (Lit l)
    value2tree (VClosure env (EAbs x e)) xs [] = value2tree (eval (Map.insert x (VVar x) env) e) (x:xs) []
    
    fun xs x ts
      | x `elem` xs = Var x
      | otherwise   = Fun x ts

    ret [] t = t
    ret xs t = Abs (reverse xs) t

data Value
  = VGen Int
  | VApp Value Value
  | VVar CId
  | VMeta Int 
  | VLit Literal
  | VClosure Env Expr
 deriving (Show,Eq,Ord)

type Env = Map.Map CId Value

eval :: Env -> Expr -> Value
eval env (EVar x)     = fromMaybe (VVar x) (Map.lookup x env)
eval env (EApp e1 e2) = apply (eval env e1) (eval env e2)
eval env (EAbs x e)   = VClosure env (EAbs x e)
eval env (EMeta k)    = VMeta k
eval env (ELit l)     = VLit l
eval env e            = VClosure env e

apply :: Value -> Value -> Value
apply (VClosure env (EAbs x e)) v = eval (Map.insert x v env) e
apply v0                        v = VApp v0 v

--- use composOp and state monad...
newMetas :: Expr -> Expr
newMetas = fst . metas 0 where
  metas i exp = case exp of
    EAbs x e -> let (f,j) = metas i e in (EAbs x f, j)
    EApp f a -> let (g,j) = metas i f ; (b,k) = metas j a in (EApp g b,k)
    EMeta _  -> (EMeta i, i+1)
    _        -> (exp,i)
