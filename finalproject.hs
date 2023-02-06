module FinalProject where

import RegexToFSA
import FiniteStatePart2
import Control.Applicative(liftA, liftA2, liftA3)
import Data.List(nub)

-- this datatype is used to represent the states in a GNFA
data State st = Start | Accept | Reg st deriving (Show, Eq)

type GeneralizedAutomaton st sy = ([st], [sy], [st], [st], [(st, RegExp sy, st)])

multLabels :: (Eq st) => st -> st -> [(st,sy,st)] -> [(st,sy,st)]
multLabels x y l = filter (\(a,b,c) -> a == x && c == y) l


-- given a list of transitions, return the union of all the symbols
buildUnion :: [(st,sy,st)] -> RegExp sy
buildUnion l = case l of 
                [] -> OneRE
                (a,b,c):[] -> Lit b
                (a,b,c):y:rest -> Alt (Lit b) (buildUnion ([y] ++ rest))
                
-- takes in an FSA and generates an equivalent GNFA as output
-- from the algorithm described in Sipser page 71.
-- * adding ZeroRE transitions has been skipped here. It is easier to deal with it
--   in the convert function later
fsa_to_gnfa :: (Eq st, Eq sy) => Automaton st sy -> GeneralizedAutomaton (State st) sy
fsa_to_gnfa fsa = let (states,syms,i,f,delta) = fsa in
    let newStates = liftA(\x -> Reg x) states ++ [Start] ++ [Accept] in
    let newSyms = syms in
    let newI = [Start] in
    let newF = [Accept] in
    let newEpsilons = liftA(\x -> (Start, OneRE, Reg x)) i ++ liftA(\x -> (Reg x, OneRE, Accept)) f in
    let newTransitions = nub (liftA(\l -> let (a,b,c) = head l in (Reg a, buildUnion l, Reg c)) (liftA(\(a,b,c) -> multLabels a c delta) delta)) in
    let newDelta = newEpsilons ++ newTransitions in
    (newStates, newSyms, newI, newF, newDelta)
     

-- FSA from Figure 1.67 of Sipser, page 75
fsa_ex1 :: Automaton Int Char
fsa_ex1 = ([1,2],['a','b'],[1],[2], [(1,'a',1),
                                    (1,'b',2),
                                    (2,'a',2),
                                    (2,'b',2)])

-- FSA from Figure 1.68 of Sipser, page 76
fsa_ex2 :: Automaton Int Char
fsa_ex2 = ([1,2,3],['a','b'],[1],[2,3], [(1,'a',2),
                                         (1,'b',3),
                                         (2,'a',1),
                                         (2,'b',2),
                                         (3,'a',2),
                                         (3,'b',1)])

-- allows for delta(q0,q1) = sym 
-- Having True -> ZeroRE simulates adding the ZeroRE transitions that I skipped in the fsa_to_gnfa function
getTransition :: (Eq st) => (State st, State st) -> [(State st, RegExp sy, State st)] -> RegExp sy
getTransition (q0,q1) d = let l = (filter (\(a,b,c) -> a == q0 && c == q1) d) in 
                            case (length l == 0) of
                                True -> ZeroRE
                                False -> let (x,y,z) = head l in y

-- the DFA to RegEx algorithm creates redudancy. This helps make the final output more readable.
simplifyRegex :: (Eq sy) => RegExp sy -> RegExp sy
simplifyRegex r = case r of 
                    ZeroRE -> ZeroRE
                    OneRE -> OneRE
                    Lit x -> Lit x
                    Alt r1 r2 -> case (r1 == ZeroRE) of
                                    True -> simplifyRegex r2
                                    False -> case (r2 == ZeroRE) of
                                                True -> simplifyRegex r1
                                                False -> case (r1 == r2) of
                                                            True -> simplifyRegex r1
                                                            False -> Alt (simplifyRegex r1) (simplifyRegex r2)
                    Concat r1 r2 -> case (r1 == OneRE) of
                                        True -> simplifyRegex r2
                                        False -> case (r2 == OneRE) of
                                                    True -> simplifyRegex r1
                                                    False -> case (r1 == ZeroRE || r2 == ZeroRE) of
                                                                True -> ZeroRE
                                                                False -> Concat (simplifyRegex r1) (simplifyRegex r2)
                    Star r1 -> case (r1 == ZeroRE) of
                                True -> OneRE
                                False -> Star (simplifyRegex r1)


-- converting GNFA to a smaller size GNFA, eventually outputting the equivalent regular expression
-- based on the algorithm from Sipser page 73
convert :: (Eq st, Eq sy) => GeneralizedAutomaton (State st) sy -> RegExp sy
convert g = let (states,syms,i,f,delta) = g in
    case ((length states) == 2) of
        True -> let (a,b,c) = head delta in b
        False -> let newStates = let x:rest = states in rest in 
                 let newDelta = let x = head states in liftA2(\a -> \b -> (a, simplifyRegex (Alt (simplifyRegex (Concat (simplifyRegex (getTransition (a,x) delta))(simplifyRegex (Concat (Star (simplifyRegex (getTransition (x,x) delta)))(simplifyRegex (getTransition (x,b) delta))))))(simplifyRegex (getTransition (a,b) delta))), b)) (filter (\x -> x /= Accept) newStates) (filter (\x -> x /= Start) newStates) in
                 convert (newStates, syms, i, f, newDelta)

-- given an FSA f and a given input w, this function checks if the FSA and the RegEx have the same behavior
-- the RegEx is checked by creating an equivalent FSA. The process is as follows
--          FSA   --> GNFA (fsa_to_gnfa)
--          GNFA  --> RegEx (convert)
--          RegEx --> NFA (reToFSA) from Assignment 4
--          NFA   --> FSA (removeEpsilons) from FiniteStartPart2
--          use generates (from FiniteStartPart2) to check if the string is accepted.
test :: (Eq st, Eq sy) => Automaton st sy -> [sy] -> [Char]
test f w = let g = fsa_to_gnfa f in
         let newF = removeEpsilons (reToFSA (convert g)) in
         let y = (generates newF w) in
         case (y == (generates f w)) of
             True -> case (y == True) of
                        True -> "FSA and RegEx have the same behavior. Both accept it."
                        False -> "FSA and RegEx have the same behavior. Both reject it."
             False -> case (y == True) of
                        True -> "FSA and RegEx have different behavior. FSA rejects, but RegEx accepts it."
                        False -> "FSA and RegEx have different behavior. FSA accepts, but RegEx rejects it."

reToString :: RegExp Char -> [Char]
reToString = \r -> case r of
                OneRE -> "1"
                ZeroRE -> "0"
                Lit x -> [x]
                Alt r1 r2 -> "(" ++ reToString r1 ++ "|" ++ reToString r2 ++ ")"
                Concat r1 r2 -> reToString r1 ++ reToString r2
                Star r1 -> reToString r1 ++ "*"