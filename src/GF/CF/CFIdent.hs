----------------------------------------------------------------------
-- |
-- Module      : CFIdent
-- Maintainer  : AR
-- Stability   : (stable)
-- Portability : (portable)
--
-- > CVS $Date: 2005/11/14 16:03:40 $ 
-- > CVS $Author: aarne $
-- > CVS $Revision: 1.13 $
--
-- symbols (categories, functions) for context-free grammars.
-----------------------------------------------------------------------------

module GF.CF.CFIdent (-- * Tokens and categories
		CFTok(..), CFCat(..),
		tS, tC, tL, tI, tF, tV, tM, tInt,
		prCFTok,
		-- * Function names and profiles
		CFFun(..), Profile,
		wordsCFTok,
		-- * CF Functions
		mkCFFun, varCFFun, consCFFun, string2CFFun, stringCFFun, 
                intCFFun, floatCFFun, dummyCFFun,
		cfFun2String, cfFun2Ident, cfFun2Profile, metaCFFun,
		-- * CF Categories
		mkCIdent, ident2CFCat, labels2CFCat, string2CFCat, 
                catVarCF, cat2CFCat, cfCatString, cfCatInt,cfCatFloat,
		moduleOfCFCat, cfCat2Cat, cfCat2Ident, lexCFCat,
		-- * CF Tokens
		string2CFTok, str2cftoks,
		-- * Comparisons
		compatToks, compatTok, compatCFFun, compatCF,
                wordsLits
	       ) where

import GF.Data.Operations
import GF.Canon.GFC
import GF.Infra.Ident
import GF.Grammar.Values (cPredefAbs)
import GF.Canon.AbsGFC
import GF.Grammar.Macros (ident2label)
import GF.Grammar.PrGrammar
import GF.Data.Str
import Data.Char (toLower, toUpper, isSpace)
import Data.List (intersperse)

-- | this type should be abstract
data CFTok = 
   TS String     -- ^ normal strings
 | TC String     -- ^ strings that are ambiguous between upper or lower case
 | TL String     -- ^ string literals
 | TI Integer    -- ^ integer literals
 | TF Double     -- ^ float literals
 | TV Ident      -- ^ variables
 | TM Int String -- ^ metavariables; the integer identifies it
  deriving (Eq, Ord, Show)

-- | this type should be abstract
newtype CFCat = CFCat (CIdent,Label) deriving (Eq, Ord, Show)

tS :: String -> CFTok
tC :: String -> CFTok
tL :: String -> CFTok
tI :: String -> CFTok
tF :: String -> CFTok
tV :: String -> CFTok
tM :: String -> CFTok

tS  = TS
tC  = TC
tL  = TL
tI  = TI . read 
tF  = TF . read 
tV  = TV . identC
tM  = TM 0

tInt :: Integer -> CFTok
tInt = TI

prCFTok :: CFTok -> String
prCFTok t = case t of
  TS s -> s
  TC s -> s
  TL s -> s
  TI i -> show i
  TF i -> show i
  TV x -> prt x
  TM i m -> m --- "?" --- m

-- | to build trees: the Atom contains a GF function, @Cn | Meta | Vr | Literal@
newtype CFFun = CFFun (Atom, Profile) deriving (Eq,Ord,Show) 
-- - - - - - - - - - - - - - - - - - - - -         ^^^ added by peb, 21/5-04 

type Profile  = [([[Int]],[Int])]

wordsCFTok :: CFTok -> [String]
wordsCFTok t = case t of
  TC (c:cs) -> [c':cs | c' <- [toUpper c, toLower c]]
  _ -> [prCFTok t]

-- the following functions should be used instead of constructors

-- to construct CF functions

mkCFFun :: Atom -> CFFun
mkCFFun t = CFFun (t,[])

varCFFun :: Ident -> CFFun
varCFFun = mkCFFun . AV

consCFFun :: CIdent -> CFFun
consCFFun = mkCFFun . AC

-- | standard way of making cf fun
string2CFFun :: String -> String -> CFFun
string2CFFun m c = consCFFun $ mkCIdent m c

stringCFFun :: String -> CFFun 
stringCFFun = mkCFFun . AS

intCFFun :: Integer -> CFFun 
intCFFun = mkCFFun . AI

floatCFFun :: Double -> CFFun 
floatCFFun = mkCFFun . AF

-- | used in lexer-by-need rules
dummyCFFun :: CFFun
dummyCFFun = varCFFun $ identC "_"

cfFun2String :: CFFun -> String
cfFun2String (CFFun (f,_)) = prt f

cfFun2Ident :: CFFun -> Ident
cfFun2Ident (CFFun (f,_)) = identC $ prt_ f ---

cfFun2Profile :: CFFun -> Profile
cfFun2Profile (CFFun (_,p)) = p

{- ----
strPro2cfFun :: String -> Profile -> CFFun
strPro2cfFun str p = (CFFun (AC (Ident str), p))
-}

metaCFFun :: CFFun
metaCFFun = mkCFFun $ AM 0

-- to construct CF categories

-- | belongs elsewhere
mkCIdent :: String -> String -> CIdent
mkCIdent m c = CIQ (identC m) (identC c)

ident2CFCat :: CIdent -> Ident -> CFCat
ident2CFCat mc d = CFCat (mc, L d)

labels2CFCat :: CIdent -> [Label] -> CFCat
labels2CFCat mc d = CFCat (mc, L (identC (concat (intersperse "." (map prt d))))) ----

-- | standard way of making cf cat: label s
string2CFCat :: String -> String -> CFCat
string2CFCat m c = ident2CFCat (mkCIdent m c) (identC "s")

idents2CFCat :: Ident -> Ident -> CFCat
idents2CFCat m c = ident2CFCat (CIQ m c) (identC "s")

catVarCF :: CFCat
catVarCF = ident2CFCat (mkCIdent "_" "#Var") (identC "_") ----

cat2CFCat :: (Ident,Ident) -> CFCat
cat2CFCat = uncurry idents2CFCat

-- | literals
cfCatString :: CFCat
cfCatString = string2CFCat (prt cPredefAbs) "String"

cfCatInt, cfCatFloat :: CFCat
cfCatInt = string2CFCat (prt cPredefAbs) "Int"
cfCatFloat = string2CFCat (prt cPredefAbs) "Float"



{- ----
uCFCat :: CFCat
uCFCat = cat2CFCat uCat
-}

moduleOfCFCat :: CFCat -> Ident
moduleOfCFCat (CFCat (CIQ m _, _)) = m

-- | the opposite direction
cfCat2Cat :: CFCat -> (Ident,Ident)
cfCat2Cat (CFCat (CIQ m c,_)) = (m,c)

cfCat2Ident :: CFCat -> Ident
cfCat2Ident = snd . cfCat2Cat

lexCFCat :: CFCat -> CFCat
lexCFCat cat = ident2CFCat (uncurry CIQ (cfCat2Cat cat)) (identC "*")

-- to construct CF tokens

string2CFTok :: String -> CFTok
string2CFTok = tS

str2cftoks :: Str -> [CFTok]
str2cftoks = map tS . wordsLits . sstr

-- decide if two token lists look the same (in parser postprocessing)

compatToks :: [CFTok] -> [CFTok] -> Bool
compatToks ts us = and [compatTok t u | (t,u) <- zip ts us]

compatTok :: CFTok -> CFTok -> Bool
compatTok (TM _ _) _ = True --- hack because metas are renamed
compatTok _ (TM _ _) = True
compatTok t u = any (`elem` (alts t)) (alts u) where
  alts u = case u of
    TC (c:s) -> [toLower c : s, toUpper c : s]
    TL s -> [s, prQuotedString s]
    _ -> [prCFTok u]

-- | decide if two CFFuns have the same function head (profiles may differ)
compatCFFun :: CFFun -> CFFun -> Bool
compatCFFun (CFFun (f,_)) (CFFun (g,_)) = f == g

-- | decide whether two categories match
-- the modifiers can be from different modules, but on the same extension
-- path, so there is no clash, and they can be safely ignored ---
compatCF :: CFCat -> CFCat -> Bool
----compatCF = (==)
compatCF (CFCat (CIQ _ c, l)) (CFCat (CIQ _ c', l')) = c==c' && l==l'

-- | Like 'words', but does not split on whitespace inside
--   double quotes.wordsLits :: String -> [String]
-- Also treats escaped quotes in quotes (AR 21/12/2005) by breaks
-- instead of break
wordsLits [] = []
wordsLits (c:cs) | isSpace c = wordsLits (dropWhile isSpace cs)
		 | c == '\'' || c == '"' 
		     = let (l,rs) = breaks (==c) cs
			   rs' = drop 1 rs
			   in ([c]++l++[c]):wordsLits rs'
		 | otherwise = let (w,rs) = break isSpace cs
				   in (c:w):wordsLits rs
  where
    breaks c cs = case break c cs of
      (l@(_:_),d:rs) | last l == '\\' -> 
        let (r,ts) = breaks c rs in (l++[d]++r, ts)
      v -> v
