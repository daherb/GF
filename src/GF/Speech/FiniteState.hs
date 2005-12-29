----------------------------------------------------------------------
-- |
-- Module      : FiniteState
-- Maintainer  : BB
-- Stability   : (stable)
-- Portability : (portable)
--
-- > CVS $Date: 2005/11/10 16:43:44 $ 
-- > CVS $Author: bringert $
-- > CVS $Revision: 1.16 $
--
-- A simple finite state network module.
-----------------------------------------------------------------------------
module GF.Speech.FiniteState (FA, State, NFA, DFA,
			      startState, finalStates,
			      states, transitions,
			      newFA, 
			      addFinalState,
			      newState, newStates,
                              newTransition,
			      mapStates, mapTransitions,
                              oneFinalState,
			      moveLabelsToNodes, minimize,
                              dfa2nfa,
			      prFAGraphviz) where

import Data.List
import Data.Maybe (catMaybes,fromJust)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import GF.Data.Utilities
import GF.Speech.Graph
import qualified GF.Visualization.Graphviz as Dot

type State = Int

data FA n a b = FA (Graph n a b) n [n]

type NFA a = FA State () (Maybe a)

type DFA a = FA State () a


startState :: FA n a b -> n
startState (FA _ s _) = s

finalStates :: FA n a b -> [n]
finalStates (FA _ _ ss) = ss

states :: FA n a b -> [(n,a)]
states (FA g _ _) = nodes g

transitions :: FA n a b -> [(n,n,b)]
transitions (FA g _ _) = edges g

newFA :: Enum n => a -- ^ Start node label
      -> FA n a b
newFA l = FA g s []
    where (g,s) = newNode l (newGraph [toEnum 0..])

addFinalState :: n -> FA n a b -> FA n a b
addFinalState f (FA g s ss) = FA g s (f:ss)

newState :: a -> FA n a b -> (FA n a b, n)
newState x (FA g s ss) = (FA g' s ss, n)
    where (g',n) = newNode x g

newStates :: [a] -> FA n a b -> (FA n a b, [(n,a)])
newStates xs (FA g s ss) = (FA g' s ss, ns)
    where (g',ns) = newNodes xs g

newTransition :: n -> n -> b -> FA n a b -> FA n a b
newTransition f t l = onGraph (newEdge (f,t,l))

mapStates :: (a -> c) -> FA n a b -> FA n c b
mapStates f = onGraph (nmap f)

mapTransitions :: (b -> c) -> FA n a b -> FA n a c
mapTransitions f = onGraph (emap f)

minimize :: Ord a => NFA a -> DFA a
minimize = determinize . reverseNFA . dfa2nfa . determinize . reverseNFA

onGraph :: (Graph n a b -> Graph n c d) -> FA n a b -> FA n c d
onGraph f (FA g s ss) = FA (f g) s ss

-- | Make the finite automaton have a single final state
--   by adding a new final state and adding an edge
--   from the old final states to the new state.
oneFinalState :: a        -- ^ Label to give the new node
              -> b        -- ^ Label to give the new edges
              -> FA n a b -- ^ The old network
              -> FA n a b -- ^ The new network
oneFinalState nl el fa =
    let (FA g s fs,nf) = newState nl fa
        es = [ (f,nf,el) | f <- fs ]
     in FA (newEdges es g) s [nf]

-- | Transform a standard finite automaton with labelled edges
--   to one where the labels are on the nodes instead. This can add
--   up to one extra node per edge.
moveLabelsToNodes :: (Ord n,Eq a) => FA n () (Maybe a) -> FA n (Maybe a) ()
moveLabelsToNodes = removeTrivialEmptyNodes . onGraph f
  where f gr@(Graph c _ _) = Graph c' ns (concat ess)
	    where is = incomingToList $ incoming gr
		  (c',is') = mapAccumL fixIncoming c is
		  (ns,ess) = unzip (concat is')

-- | Remove nodes which are not start or final, and have
--   exactly one incoming or exactly one outgoing edge.
removeTrivialEmptyNodes :: FA n (Maybe a) () -> FA n (Maybe a) ()
removeTrivialEmptyNodes = id -- FIXME: implement

fixIncoming :: (Ord n, Eq a) => [n] -> (Node n (),[Edge n (Maybe a)]) -> ([n],[(Node n (Maybe a),[Edge n ()])])
fixIncoming cs c@((n,()),es) = (cs'', ((n,Nothing),es'):newContexts)
  where ls = nub $ map getLabel es
	(cs',cs'') = splitAt (length ls) cs
	newNodes = zip cs' ls
	es' = [ (x,n,()) | x <- map fst newNodes ]
	-- separate cyclic and non-cyclic edges
	(cyc,ncyc) = partition (\ (f,_,_) -> f == n) es
	       -- keep all incoming non-cyclic edges with the right label
	to (x,l) = [ (f,x,()) | (f,_,l') <- ncyc, l == l']
	          -- for each cyclic edge with the right label, 
	          -- add an edge from each of the new nodes (including this one)
		    ++ [ (y,x,()) | (f,_,l') <- cyc, l == l', (y,_) <- newNodes]
	newContexts = [ (v, to v) | v <- newNodes ]

alphabet :: Eq b => Graph n a (Maybe b) -> [b]
alphabet = nub . catMaybes . map getLabel . edges

determinize :: Ord a => NFA a -> DFA a
determinize (FA g s f) = let (ns,es) = h [start] [] []
                             final = filter isDFAFinal ns
                             fa = FA (Graph undefined [(n,()) | n <- ns] es) start final
 		          in numberStates fa
  where out = outgoing g
	start = closure out $ Set.singleton s
        isDFAFinal n = not (Set.null (Set.fromList f `Set.intersection` n))
	h currentStates oldStates oldEdges 
	    | null currentStates = (oldStates,oldEdges)
	    | otherwise = h uniqueNewStates allOldStates (newEdges++oldEdges)
	    where 
	    allOldStates = currentStates ++ oldStates
            (newStates,newEdges) 
                = unzip [ (s, (n,s,c)) | n <- currentStates, (c,s) <- reachable out n]
	    uniqueNewStates = nub newStates \\ allOldStates

numberStates :: (Ord x,Enum y) => FA x a b -> FA y a b
numberStates (FA g s fs) = FA (renameNodes newName rest g) s' fs'
    where (ns,rest) = splitAt (length (nodes g)) $ [toEnum 0 .. ]
          newNodes = zip (map fst (nodes g)) ns
	  newName n = lookup' n newNodes
          s' = newName s
          fs' = map newName fs

-- | Get all the nodes reachable from a list of nodes by only empty edges.
closure :: Ord n => Outgoing n a (Maybe b) -> Set n -> Set n
closure out = fix closure_
    where closure_ r = inserts [y | x <- Set.toList r, (_,y,Nothing) <- getOutgoing out x] r
          inserts xs s = foldl (flip Set.insert) s xs

-- | Get a map of labels to sets of all nodes reachable 
--   from a the set of nodes by one edge with the given 
--   label and then any number of empty edges.
reachable :: (Ord n, Ord b) => Outgoing n a (Maybe b) -> Set n -> [(b,Set n)]
reachable out ns = Map.toList $ Map.map (closure out . Set.fromList) $ Map.fromListWith (++) [(c,[y]) | n <- Set.toList ns, (_,y,Just c) <- getOutgoing out n]

reverseNFA :: NFA a -> NFA a
reverseNFA (FA g s fs) = FA g''' s' [s]
    where g' = reverseGraph g
	  (g'',s') = newNode () g'
	  g''' = newEdges [(s',f,Nothing) | f <- fs] g''

dfa2nfa :: DFA a -> NFA a
dfa2nfa = mapTransitions Just

--
-- * Visualization
--

prFAGraphviz :: (Eq n,Show n) => FA n String String -> String
prFAGraphviz  = Dot.prGraphviz . toGraphviz

prFAGraphviz_ :: (Eq n,Show n,Show a, Show b) => FA n a b -> String
prFAGraphviz_  = Dot.prGraphviz . toGraphviz . mapStates show . mapTransitions show

toGraphviz :: (Eq n,Show n) => FA n String String -> Dot.Graph
toGraphviz (FA (Graph _ ns es) s f) = Dot.Graph Dot.Directed [] (map mkNode ns) (map mkEdge es)
   where mkNode (n,l) = Dot.Node (show n) attrs
	     where attrs = [("label",l)]
			   ++ if n == s then [("shape","box")] else []
			   ++ if n `elem` f then [("style","bold")] else []
	 mkEdge (x,y,l) = Dot.Edge (show x) (show y) [("label",l)]

