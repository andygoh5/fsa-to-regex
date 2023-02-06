module RegexToFSA where

import Prelude hiding (Either(..))

import Control.Applicative(liftA, liftA2, liftA3)
import Data.List(nub)

import FiniteStatePart2

data Either a b = First a | Second b deriving (Show,Eq)

----------- SECTION 2: Converting regex to epsilon-FSAs ------------
-- Problem 2A
unionFSAs :: (Eq sy) => EpsAutomaton st1 sy -> EpsAutomaton st2 sy -> EpsAutomaton (Either st1 st2) sy
unionFSAs (states, syms, i, f, delta) (states', syms', i', f', delta') = 
    let newStates = liftA(\x -> First x) states ++ liftA(\x -> Second x) states' in
    let newI = liftA(\x -> First x) i ++ liftA(\x -> Second x) i' in
    let newF = liftA(\x -> First x) f ++ liftA(\x -> Second x) f' in
    let newSyms = nub (syms ++ syms') in
    let newDelta = liftA(\(a,b,c) -> (First a,b,First c)) delta ++ liftA(\(a,b,c) -> (Second a,b,Second c)) delta' in 
    (newStates, newSyms, newI, newF, newDelta)

-- Problem 2B
concatFSAs :: (Eq sy) => EpsAutomaton st1 sy -> EpsAutomaton st2 sy -> EpsAutomaton (Either st1 st2) sy
concatFSAs (states, syms, i, f, delta) (states', syms', i', f', delta') = 
    let newStates = liftA(\x -> First x) states ++ liftA(\x -> Second x) states' in
    let newI = liftA(\x -> First x) i in
    let newF = liftA(\x -> Second x) f' in
    let newSyms = nub (syms ++ syms') in
    let newTransitions = liftA(\(a,b,c) -> (First a,b,First c)) delta ++ liftA(\(a,b,c) -> (Second a,b,Second c)) delta' in 
    let epsilons = liftA2(\a -> \b -> (First a,Nothing,Second b)) f i' in
    let newDelta = newTransitions ++ epsilons in 
    (newStates, newSyms, newI, newF, newDelta)

-- Problem 2C
starFSA :: EpsAutomaton st sy -> EpsAutomaton (Either Int st) sy
starFSA (states, syms, i, f, delta) = 
    let newStates = liftA(\x -> Second x) states ++ [First (-1)] in
    let newI = [First (-1)] in
    let newF = liftA(\x -> Second x) f  ++ newI in
    let newSyms = syms in
    let newTransitions = liftA(\(a,b,c) -> (Second a,b,Second c)) delta in
    let epsilons = liftA2(\a -> \b -> (Second a,Nothing,Second b)) f i ++ liftA(\a -> (First (-1),Nothing,Second a)) i in
    let newDelta = newTransitions ++ epsilons in 
    (newStates, newSyms, newI, newF, newDelta)


-- Problem 2D
flatten :: Either Int Int -> Int
flatten x = case x of
                First a -> 2*a
                Second a -> 2*a + 1

-- Problem 2E
mapStates :: (a -> b) -> EpsAutomaton a sy -> EpsAutomaton b sy
mapStates fx (states,syms,i,f,delta) =
    let newStates = liftA(\x -> fx x) states in
    let newI = liftA(\x -> fx x) i in
    let newF = liftA(\x -> fx x) f in
    let newDelta = liftA(\(a,b,c) -> (fx a,b,fx c)) delta in
    (newStates, syms, newI, newF, newDelta)

-- Problem 2F
reToFSA :: (Eq sy) => RegExp sy -> EpsAutomaton Int sy
reToFSA r = case r of
            OneRE -> ([0],[],[0],[0],[])
            ZeroRE -> ([0],[],[0],[],[])
            Lit x -> ([0,1],[x],[0],[1],[(0,Just x,1)])
            Alt r1 r2 -> mapStates flatten (unionFSAs (reToFSA r1) (reToFSA r2))
            Concat r1 r2 -> mapStates flatten (concatFSAs (reToFSA r1) (reToFSA r2))
            Star r1 -> mapStates flatten (starFSA (reToFSA (r1)))
