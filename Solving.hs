{-# OPTIONS -fno-monomorphism-restriction #-}
module Solving where

import SAT
import SatSolvers
import NProgram
import NVar
import Control.Monad.State
import qualified Data.IntMap as IM

solveNProgram :: (a -> IM.IntMap Bool -> b) -> SatSolver -> State NProgram a -> Maybe [b]
solveNProgram interpreter ss nprogramComputation =
    let (theNVars, NProgram formula unusedVars) = runState nprogramComputation emptyNProgram
        numVars = head unusedVars - 1
        solutions = solveAll ss (numVars, formula)
    in case solutions of
         Just [] -> Just [] -- error "Unsatisfiable formula"
         Just truthMaps -> Just $ map (interpreter theNVars) truthMaps
         Nothing -> Nothing -- error "Solve time limit exceeded"

reduceSolutions :: Maybe [b] -> (Maybe Bool, b)
reduceSolutions Nothing = (Nothing, error "Solve time limit exceeded")
reduceSolutions (Just []) = (Just False, error "Unsatisfiable formula")
reduceSolutions (Just (solution:solutions)) = (Just True, solution)

evalAllNProgram :: (Interpret a b) => SatSolver -> State NProgram a -> Maybe [b]
evalAllNProgram = solveNProgram interpret

evalNProgram :: (Interpret a b) => SatSolver -> State NProgram a -> (Maybe Bool, b)
evalNProgram ss nprogramComputation =
    reduceSolutions $ evalAllNProgram ss nprogramComputation

execNProgram :: SatSolver -> State NProgram a -> Maybe Bool
execNProgram ss nprogramComputation =
    fst $ reduceSolutions $ solveNProgram (const (const ())) ss nprogramComputation
