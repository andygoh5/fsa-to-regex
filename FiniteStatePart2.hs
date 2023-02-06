module FiniteStatePart2 where

----------------------------------------------------------------------------
-- Some helper functions

-- liftA :: (a -> b) -> [a] -> [b]
-- liftA2 :: (a -> b -> c) -> [a] -> [b] -> [c]
-- liftA3 :: (a -> b -> c -> d) -> [a] -> [b] -> [c] -> [d]
import Control.Applicative(liftA, liftA2, liftA3)

-- nub just removes duplicate elements from a list
-- nub :: (Eq a) => [a] -> [a]
import Data.List(nub)

-- filter (already defined) removes from a list of elements that don't satisfy the given predicate
-- e.g. filter (\x -> x > 3) [1,2,3,4,5]   ==>   [4,5]
-- filter :: (a -> Bool) -> [a] -> [a]

----------------------------------------------------------------------------
-- Simple definitions

data SegmentCV = C | V deriving (Show,Eq)

-- This now has two type parameters: one for states, and one for symbols
type Automaton st sy = ([st], [sy], [st], [st], [(st,sy,st)])

-- FSA requiring an odd number of Cs
fsa_oddCs :: Automaton Bool SegmentCV
fsa_oddCs = ([True,False], [C,V], [False], [True], 
             [(False, C, True), (False, V, False), (True, C, False), (True, V, True)])

-- FSA requiring an even number of Vs
fsa_evenVs :: Automaton Bool SegmentCV
fsa_evenVs = ([True,False], [C,V], [False], [False], 
              [(False, C, False), (False, V, True), (True, C, True), (True, V, False)])

----------------------------------------------------------------------------
-- Basic generation (essentially the same as last week)

backward :: (Eq st, Eq sy) => Automaton st sy -> [sy] -> st -> Bool
backward m w q =
    let (states, syms, i, f, delta) = m in
    case w of
    [] -> elem q f
    (x:rest) -> or (map (\q1 -> elem (q,x,q1) delta && backward m rest q1) states)

generates :: (Eq st, Eq sy) => Automaton st sy -> [sy] -> Bool
generates m w =
    let (states, syms, i, f, delta) = m in
    or (map (\q0 -> elem q0 i && backward m w q0) states)

----------------------------------------------------------------------------
-- Intersection of FSAs

-- See (19) on the handout
intersect :: (Eq st, Eq st', Eq sy) => Automaton st sy -> Automaton st' sy -> Automaton (st,st') sy
intersect (states, syms, i, f, delta) (states', syms', i', f', delta') =
    let newStates = liftA2 (\x -> \y -> (x,y)) states states' in
    let newI = liftA2 (\x -> \y -> (x,y)) i i' in
    let newF = liftA2 (\x -> \y -> (x,y)) f f' in
    let newSyms = nub (syms ++ syms') in    -- A bit ugly. Only common symbols will end up in newDelta.
    let candidateTransitions = liftA3 (\x -> \y -> \z -> (x,y,z)) newStates newSyms newStates in
    let isValidTransition ((q1,q1'),x,(q2,q2')) = elem (q1,x,q2) delta && elem (q1',x,q2') delta' in
    let newDelta = filter isValidTransition candidateTransitions in
    (newStates, newSyms, newI, newF, newDelta)

----------------------------------------------------------------------------
-- FSAs with epsilon transitions

-- Maybe types are pre-defined like this. You can think of them 
-- like a non-recursive list, with a maximum length of one.
-- data Maybe a = Nothing | Just a deriving (Eq,Show)

-- See (20) on the handout
type EpsAutomaton st sy = ([st], [sy], [st], [st], [(st, Maybe sy, st)])

-- See (23) on the handout. Feel free to ignore the implementation of this.
epsilonClosure :: (Eq st, Eq sy) => [(st, Maybe sy, st)] -> st -> [st]
epsilonClosure delta q =
    let outgoingEpsilons q' = filter (\(q1,x,q2) -> q1 == q' && x == Nothing) delta in
    let oneStepFrom q' = map (\(q1,x,q2) -> q2) (outgoingEpsilons q') in
    let update qs = nub (qs ++ (concat (map oneStepFrom qs))) in
    until (\qs -> update qs == qs) update [q]

-- See (24) on the handout.
removeEpsilons :: (Eq st, Eq sy) => EpsAutomaton st sy -> Automaton st sy
removeEpsilons (states, syms, i, f, delta) =
    let validTransition (q1,x,q2) = or (map (\q' -> elem q' (epsilonClosure delta q1) && elem (q', Just x, q2) delta) states) in
    let newDelta = filter validTransition (liftA3 (\x -> \y -> \z -> (x,y,z)) states syms states) in
    let canReachEnd q = or (map (\q' -> elem q' f) (epsilonClosure delta q)) in
    let newEnds = filter canReachEnd states in
    (states, syms, i, newEnds, newDelta)

----------------------------------------------------------------------------
data RegExp a = Lit a | Alt (RegExp a) (RegExp a) | Concat (RegExp a) (RegExp a) 
              | Star (RegExp a) | ZeroRE | OneRE
              deriving (Eq,Show)

