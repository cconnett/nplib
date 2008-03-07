module Solvers where
      
import ILPSAT
import ILPSATReduction

class Solver s where
    -- Solve a problem and return its satisfiablility, plus a list of
    -- the variables assigned a truth value of true.
    solveA :: (Show a, Ord a) => s -> Problem a -> (Bool, [Proposition a])
    solveA s problem = (startPartial s problem [])

    -- Solve a problem and return its satisfiablility.
    solve :: (Show a, Ord a) => s -> Problem a -> Bool
    solve s problem = fst (solveA s problem)

    -- Compute support data structures for a large initial problem and
    -- return a closure that will take additional constraints and
    -- solve the combined problem.
    startPartial :: (Show a, Ord a) => s -> Problem a -> Problem a -> (Bool, [Proposition a])

