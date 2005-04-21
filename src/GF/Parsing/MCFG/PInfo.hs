---------------------------------------------------------------------
-- |
-- Maintainer  : PL
-- Stability   : (stable)
-- Portability : (portable)
--
-- > CVS $Date: 2005/04/21 16:23:14 $ 
-- > CVS $Author: bringert $
-- > CVS $Revision: 1.3 $
--
-- MCFG parsing, parser information
-----------------------------------------------------------------------------

module GF.Parsing.MCFG.PInfo where

import GF.System.Tracing
import GF.Infra.Print

import GF.Formalism.Utilities
import GF.Formalism.GCFG
import GF.Formalism.MCFG
import GF.Data.SortedList
import GF.Data.Assoc
import GF.Parsing.MCFG.Range

----------------------------------------------------------------------
-- type declarations

-- | the list of categories = possible starting categories
type MCFParser c n l t = MCFPInfo c n l t 
		       -> [c]
		       -> Input t
		       -> MCFChart c n l

type MCFChart  c n l   = [Abstract (c, RangeRec l) n]

type MCFPInfo  c n l t = MCFGrammar c n l t

buildMCFPInfo :: (Ord n, Ord c, Ord l, Ord t) => MCFGrammar c n l t -> MCFPInfo c n l t
buildMCFPInfo = id

makeFinalEdge :: c -> l -> (Int, Int) -> (c, RangeRec l)
makeFinalEdge cat lbl bnds = (cat, [(lbl, makeRange bnds)])

