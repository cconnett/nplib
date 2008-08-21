{-# OPTIONS -fglasgow-exts #-}
module NProgram where

import Control.Monad.State
import SAT
import SatSolvers
import qualified Data.IntMap as IM

data NProgram = NProgram Formula [Var]

type Stateful a = State NProgram a

class NVar v where
    toVars :: v -> [Var]
    fromVars :: [Var] -> v

class NVar v => Interpret v d where
    interpret :: v -> [Bool] -> d

-- Empty program has first and second variables as a reference false
-- and true respectively.
emptyNProgram :: NProgram
emptyNProgram = NProgram (Formula [Clause [Not 1], Clause [Merely 2]]) [3..]

falseVar = 1 :: Var
trueVar = 2 :: Var

runNProgram :: Interpret v d => SatSolver -> State NProgram a -> (Maybe Bool, (v -> d, a))
runNProgram ss nprogramComputation =
    let (theNVars, NProgram formula unusedVars) = runState nprogramComputation emptyNProgram
        numVars = head unusedVars - 1
        (satisfiable, truthMap) = solveA ss (numVars, formula)
        retriever = case satisfiable of
                      Just True -> \v -> interpret v (extractTruths truthMap v)
                      _ -> error "UNSAT"
    in (satisfiable, (retriever, theNVars))

extractTruths :: NVar v => IM.IntMap Bool -> v -> [Bool]
extractTruths truthMap a = map (truthMap IM.!) (toVars a)

takeSatVar :: State NProgram Var
takeSatVar = do
  NProgram formula unusedVars <- get
  put $ NProgram formula (tail unusedVars)
  return $ head unusedVars

takeSatVars n = replicateM n takeSatVar

assert :: Formula -> State NProgram ()
assert formula = do
  NProgram f unusedVars <- get
  put $ NProgram (conjoin [f, formula]) unusedVars
