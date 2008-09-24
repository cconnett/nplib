{-# OPTIONS -fno-monomorphism-restriction #-}
module Solving where

import SAT
import SatSolvers
import NProgram
import NVar
import Control.Monad.State
import qualified Data.IntMap as IM

solveAllNProgram :: (Interpret a b) => SatSolver -> State NProgram a -> Maybe [b]
solveAllNProgram ss nprogramComputation =
    let (theNVars, NProgram formula unusedVars) = runState nprogramComputation emptyNProgram
        numVars = head unusedVars - 1
        solutions = solveAll ss (numVars, formula)
    in case solutions of
         Just [] -> Just [] -- error "Unsatisfiable formula"
         Just truthMaps -> Just $ map (interpret theNVars) truthMaps
         Nothing -> Nothing -- error "Solve time limit exceeded"

solve1NProgram :: (Interpret a b) => SatSolver -> State NProgram a -> (Maybe Bool, b)
solve1NProgram ss nprogramComputation =
  case solveAllNProgram ss nprogramComputation of
    Just [] -> (Just False, error "Unsatisfiable formula")
    Nothing -> (Nothing, error "Solve time limit exceeded")
    Just (solution:solutions) -> (Just True, solution)
runNProgram = solve1NProgram