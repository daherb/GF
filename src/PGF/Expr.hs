module PGF.Expr(Tree(..), Literal(..),                
                readTree, showTree, pTree, ppTree,

                Expr(..), Patt(..), Equation(..),
                readExpr, showExpr, pExpr, ppExpr, ppPatt,

                tree2expr, expr2tree,

                -- needed in the typechecker
                Value(..), Env, eval, apply, eqValue,

                -- helpers
                pStr,pFactor,
               ) where

import PGF.CId
import PGF.Type

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
 deriving (Eq,Ord)

-- | The tree is an evaluated expression in the abstract syntax
-- of the grammar. The type is especially restricted to not
-- allow unapplied lambda abstractions. The tree is used directly 
-- from the linearizer and is produced directly from the parser.
data Tree = 
   Abs [CId] Tree                   -- ^ lambda abstraction. The list of variables is non-empty
 | Var CId                          -- ^ variable
 | Fun CId [Tree]                   -- ^ function application
 | Lit Literal                      -- ^ literal
 | Meta {-# UNPACK #-} !Int         -- ^ meta variable
  deriving (Eq, Ord)

-- | An expression represents a potentially unevaluated expression
-- in the abstract syntax of the grammar. It can be evaluated with
-- the 'expr2tree' function and then linearized or it can be used
-- directly in the dependent types.
data Expr =
   EAbs CId Expr                    -- ^ lambda abstraction
 | EApp Expr Expr                   -- ^ application
 | ELit Literal                     -- ^ literal
 | EMeta  {-# UNPACK #-} !Int       -- ^ meta variable
 | EVar   CId                       -- ^ variable or function reference
 | EPi CId Expr Expr                -- ^ dependent function type
  deriving (Eq,Ord)

-- | The pattern is used to define equations in the abstract syntax of the grammar.
data Patt =
   PApp CId [Patt]                  -- ^ application. The identifier should be constructor i.e. defined with 'data'
 | PLit Literal                     -- ^ literal
 | PVar CId                         -- ^ variable
 | PWild                            -- ^ wildcard
  deriving (Eq,Ord)

-- | The equation is used to define lambda function as a sequence
-- of equations with pattern matching. The list of 'Expr' represents
-- the patterns and the second 'Expr' is the function body for this
-- equation.
data Equation =
   Equ [Patt] Expr
  deriving (Eq,Ord)

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
pExpr = RP.skipSpaces >> (pAbs RP.<++ pTerm)
  where
    pTerm   =       fmap (foldl1 EApp) (RP.sepBy1 pFactor RP.skipSpaces)

    pAbs = do xs <- RP.between (RP.char '\\') (RP.skipSpaces >> RP.string "->") (RP.sepBy1 (RP.skipSpaces >> pCId) (RP.skipSpaces >> RP.char ','))
              e  <- pExpr
              return (foldr EAbs e xs)

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


ppExpr :: Int -> Expr -> PP.Doc
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

ppPatt d (PApp f ps) = ppParens (d > 1) (PP.text (prCId f) PP.<+> PP.hsep (map (ppPatt 2) ps))
ppPatt d (PLit l)    = ppLit l
ppPatt d (PVar f)    = PP.text (prCId f)
ppPatt d PWild       = PP.char '_'

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

-- | Converts an expression to tree. The expression
-- is first reduced to beta-eta-alfa normal form and
-- after that converted to tree.
expr2tree :: Funs -> Expr -> Tree
expr2tree funs e = value2tree [] (eval funs Map.empty e)
  where
    value2tree xs (VApp f vs)               = case Map.lookup f funs of
                                                Just (DTyp hyps _ _,_,_) -> -- eta conversion
                                                                          let a1  = length hyps    
                                                                              a2  = length vs
                                                                              a   = a1 - a2
                                                                              i   = length xs
                                                                              xs' = [var i | i <- [i..i+a-1]]
                                                                          in ret (reverse xs'++xs)
                                                                                 (Fun f (map (value2tree []) vs++map Var xs'))
                                                Nothing                -> error ("unknown variable "++prCId f)
    value2tree xs (VGen i vs)   | null vs   = ret xs (Var (var i))
                                | otherwise = error "variable of function type"
    value2tree xs (VMeta n vs)  | null vs   = ret xs (Meta n)
                                | otherwise = error "meta variable of function type"
    value2tree xs (VLit l)                  = ret xs (Lit l)
    value2tree xs (VClosure env (EAbs x e)) = let i = length xs
                                              in value2tree (var i:xs) (eval funs (Map.insert x (VGen i []) env) e)

    var i = mkCId ('v':show i)

    ret [] t = t
    ret xs t = Abs (reverse xs) t

data Value
  = VApp CId [Value]
  | VLit Literal
  | VMeta {-# UNPACK #-} !Int [Value]
  | VGen  {-# UNPACK #-} !Int [Value]
  | VClosure Env Expr
 deriving (Eq,Ord)

type Funs = Map.Map CId (Type,Int,[Equation]) -- type and def of a fun
type Env  = Map.Map CId Value

eval :: Funs -> Env -> Expr -> Value
eval funs env (EVar x)     = case Map.lookup x env of
                               Just v  -> v
                               Nothing -> case Map.lookup x funs of
                                            Just (_,a,eqs) -> if a == 0
                                                                then case eqs of
                                                                       Equ [] e : _ -> eval funs env e
                                                                       _            -> VApp x []
                                                                else VApp x []
                                            Nothing        -> error ("unknown variable "++prCId x)
eval funs env (EApp e1 e2) = apply funs env e1 [eval funs env e2]
eval funs env (EAbs x e)   = VClosure env (EAbs x e)
eval funs env (EMeta k)    = VMeta k []
eval funs env (ELit l)     = VLit l

apply :: Funs -> Env -> Expr -> [Value] -> Value
apply funs env e            []     = eval funs env e
apply funs env (EVar x)     vs     = case Map.lookup x env of
                                       Just v  -> case (v,vs) of
                                                    (VApp f  vs0            ,  vs) -> apply funs env (EVar f) (vs0++vs)
                                                    (VLit _                 ,  vs) -> error "literal of function type"
                                                    (VMeta i vs0            ,  vs) -> VMeta i (vs0++vs)
                                                    (VGen  i vs0            ,  vs) -> VGen  i (vs0++vs)
                                                    (VClosure env (EAbs x e),v:vs) -> apply funs (Map.insert x v env) e vs
                                       Nothing -> case Map.lookup x funs of
                                                    Just (_,a,eqs) -> if a <= length vs
                                                                        then let (as,vs') = splitAt a vs
                                                                             in case match eqs as of
                                                                                  Match e env -> apply funs env e vs'
                                                                                  Fail        -> VApp x vs
                                                                                  Susp        -> VApp x vs
                                                                        else VApp x vs
                                                    Nothing        -> error ("unknown variable "++prCId x)
apply funs env (EApp e1 e2) vs     = apply funs env e1 (eval funs env e2 : vs)
apply funs env (EAbs x e)   (v:vs) = apply funs (Map.insert x v env) e vs
apply funs env (EMeta k)    vs     = VMeta k vs
apply funs env (ELit l)     vs     = error "literal of function type"


-----------------------------------------------------
-- Pattern matching
-----------------------------------------------------

data MatchRes
  = Match Expr Env
  | Susp
  | Fail

match :: [Equation] -> [Value] -> MatchRes
match eqs as =
  case eqs of
    []               -> Fail
    (Equ ps res):eqs -> case tryMatches ps as res Map.empty of
                          Fail -> match eqs as
                          res  -> res
  where
    tryMatches []     []     res env = Match res env
    tryMatches (p:ps) (a:as) res env = tryMatch p a env
      where
        tryMatch (PApp f1 ps1) (VApp f2 vs2) env | f1 == f2 = tryMatches (ps1++ps) (vs2++as) res env
        tryMatch (PApp f1 ps1) (VMeta _ _  ) env            = Susp
        tryMatch (PApp f1 ps1) (VGen  _ _  ) env            = Susp
        tryMatch (PLit l1    ) (VLit l2    ) env | l1 == l2 = tryMatches       ps        as  res env
        tryMatch (PLit l1    ) (VMeta _ _  ) env            = Susp
        tryMatch (PLit l1    ) (VGen  _ _  ) env            = Susp
        tryMatch (PVar x     ) (v          ) env            = tryMatches       ps        as  res (Map.insert x v env)
        tryMatch (PWild      ) (_          ) env            = tryMatches       ps        as  res env
        tryMatch _             _             env            = Fail


-----------------------------------------------------
-- Equality checking
-----------------------------------------------------

eqValue :: Int -> Value -> Value -> [(Value,Value)]
eqValue k v1 v2 =
  case (v1,v2) of
    (VApp f1 vs1, VApp f2 vs2) | f1 == f2  -> concat (zipWith (eqValue k) vs1 vs2)
    (VLit l1,     VLit l2    ) | l1 == l2  -> []
    (VMeta i vs1, VMeta j vs2) | i  == j   -> concat (zipWith (eqValue k) vs1 vs2)
    (VGen  i vs1, VGen  j vs2) | i  == j   -> concat (zipWith (eqValue k) vs1 vs2)
    (VClosure env1 (EAbs x1 e1), VClosure env2 (EAbs x2 e2)) ->
      let v = VGen k []
      in eqValue (k+1) (VClosure (Map.insert x1 v env1) e1) (VClosure (Map.insert x2 v env2) e2)
    _                                      -> [(v1,v2)]
