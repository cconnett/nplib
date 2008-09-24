module Solving where

import SAT
import SatSolvers
import NProgram
import NVar
import Control.Monad.State
import qualified Data.IntMap as IM

runNProgram :: (Interpret a b) => SatSolver -> State NProgram a -> (Maybe Bool, b)
runNProgram ss nprogramComputation =
    let (theNVars, NProgram formula unusedVars) = runState nprogramComputation emptyNProgram
        numVars = head unusedVars - 1
        (satisfiable, truthMap) = solveA ss (numVars, formula)
        --retriever = case satisfiable of
        --              Just True -> \v -> interpret v truthMap
        --              _ -> error "UNSAT"
    in (satisfiable, interpret theNVars truthMap)
