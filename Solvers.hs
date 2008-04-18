module Solvers where
      
import ILPSAT
import ILPSATReduction
import VarMapping
import qualified Data.Map as M

class Solver s where
    -- Solve a problem and return its satisfiablility, plus a list of
    -- the variables assigned a truth value of true.
    solveA :: (Show a, Ord a) => s -> Problem a -> (Maybe Bool, [Proposition a])
    solveA s problem = (startPartial s undefined {-([], M.empty)-} problem)

    -- Solve a problem and return its satisfiablility.
    solve :: (Show a, Ord a) => s -> Problem a -> Maybe Bool
    solve s problem = fst (solveA s problem)

    -- Compute support data structures for a large initial problem and
    -- return a closure that will take additional constraints and
    -- solve the combined problem.
    startPartial :: (Show a, Ord a, Read b, Integral b) =>
                    s -> ([[b]], VarMap a b) -> Problem a -> (Maybe Bool, [Proposition a])
