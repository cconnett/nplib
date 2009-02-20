{-# OPTIONS -fglasgow-exts #-}
module NPLib
    (NProgramComputation
    ,takeSatVar
    ,takeSatVars
    ,assert
    ,assertAll
    ,ntrace

    ,NVar
    ,toVars
    ,fromVars
    ,true
    ,false
    ,new

    ,Interpret
    ,interpret
    ,lookupVarAnswers

    ,execNProgram
    ,evalNProgram
    ,evalAllNProgram

    ,prop_assertConjoinShow
    )
    where

import Control.Arrow
import Control.Monad.State
import Data.Array.IArray
import Debug.Trace
import Tracing
import SAT
import SatSolvers
import qualified Data.IntMap as IM

data NTrace = forall v d. (Interpret v d) => NTrace String v (d -> String)

data NProgram = NProgram Formula [Var] [NTrace]
instance Show NProgram where
    show (NProgram formula _ _) = show formula

type NProgramComputation a = State NProgram a
type Model = IM.IntMap Bool

-- Empty program has first and second variables as a reference false
-- and true respectively.
emptyNProgram :: NProgram
emptyNProgram = NProgram (fromListForm [[Not 1], [Merely 2]]) [3..] []

false = 1 :: Var
true = 2 :: Var

takeSatVar :: NProgramComputation Var
takeSatVar = do
  NProgram formula unusedVars traces <- get
  put $ NProgram formula (tail unusedVars) traces
  return $ head unusedVars

takeSatVars n = replicateM n takeSatVar

assert :: Formula -> NProgramComputation ()
assert formula = do
  NProgram f unusedVars traces <- get
  put $ NProgram (conjoin f formula) unusedVars traces
assertAll :: [Formula] -> NProgramComputation ()
assertAll = assert . conjoinAll

ntrace tag v show =  do
  NProgram f unusedVars traces <- get
  put $ NProgram f unusedVars ((NTrace tag v show):traces)

-- The NVar class are types that represent complex non-deterministic
-- structures.
class NVar v where
    -- Convert to and from a list of Vars.
    toVars :: v -> [Var]
    fromVars :: [Var] -> v

    -- Statefully allocate new variables
    new :: NProgramComputation v

-- The Interpret class allows the interpretation of a (usually) NVar
-- type into a related deterministic type, given an IntMap Bool of the
-- assignments to the Vars in the formula it was used in.
class Interpret v d where
    interpret :: v -> IM.IntMap Bool -> d

-- NVar and Interpret instances for Var
instance NVar Var where
    toVars var = [var]
    fromVars vars = last vars

    new = takeSatVar
instance Interpret Var Bool where
    interpret v answers = answers IM.! v
instance Interpret Formula Bool where
    interpret formula answers = formulaSatisfied formula answers

lookupVarAnswers v answers = map (answers IM.!) (toVars v)

-- Interpret instances for tuples up to 15.
instance (Interpret v1 d1, Interpret v2 d2) => Interpret (v1, v2) (d1, d2) where
    interpret (v1, v2) answers = (interpret v1 answers, interpret v2 answers)
instance (Interpret v1 d1, Interpret v2 d2, Interpret v3 d3) => Interpret (v1, v2, v3) (d1, d2, d3) where
    interpret (v1, v2, v3) answers = (interpret v1 answers, interpret v2 answers, interpret v3 answers)
instance (Interpret v1 d1, Interpret v2 d2, Interpret v3 d3, Interpret v4 d4) => Interpret (v1, v2, v3, v4) (d1, d2, d3, d4) where
    interpret (v1, v2, v3, v4) answers = (interpret v1 answers, interpret v2 answers, interpret v3 answers, interpret v4 answers)
instance (Interpret v1 d1, Interpret v2 d2, Interpret v3 d3, Interpret v4 d4, Interpret v5 d5) => Interpret (v1, v2, v3, v4, v5) (d1, d2, d3, d4, d5) where
    interpret (v1, v2, v3, v4, v5) answers = (interpret v1 answers, interpret v2 answers, interpret v3 answers, interpret v4 answers, interpret v5 answers)
instance (Interpret v1 d1, Interpret v2 d2, Interpret v3 d3, Interpret v4 d4, Interpret v5 d5, Interpret v6 d6) => Interpret (v1, v2, v3, v4, v5, v6) (d1, d2, d3, d4, d5, d6) where
    interpret (v1, v2, v3, v4, v5, v6) answers = (interpret v1 answers, interpret v2 answers, interpret v3 answers, interpret v4 answers, interpret v5 answers, interpret v6 answers)
instance (Interpret v1 d1, Interpret v2 d2, Interpret v3 d3, Interpret v4 d4, Interpret v5 d5, Interpret v6 d6, Interpret v7 d7) => Interpret (v1, v2, v3, v4, v5, v6, v7) (d1, d2, d3, d4, d5, d6, d7) where
    interpret (v1, v2, v3, v4, v5, v6, v7) answers = (interpret v1 answers, interpret v2 answers, interpret v3 answers, interpret v4 answers, interpret v5 answers, interpret v6 answers, interpret v7 answers)
instance (Interpret v1 d1, Interpret v2 d2, Interpret v3 d3, Interpret v4 d4, Interpret v5 d5, Interpret v6 d6, Interpret v7 d7, Interpret v8 d8) => Interpret (v1, v2, v3, v4, v5, v6, v7, v8) (d1, d2, d3, d4, d5, d6, d7, d8) where
    interpret (v1, v2, v3, v4, v5, v6, v7, v8) answers = (interpret v1 answers, interpret v2 answers, interpret v3 answers, interpret v4 answers, interpret v5 answers, interpret v6 answers, interpret v7 answers, interpret v8 answers)
instance (Interpret v1 d1, Interpret v2 d2, Interpret v3 d3, Interpret v4 d4, Interpret v5 d5, Interpret v6 d6, Interpret v7 d7, Interpret v8 d8, Interpret v9 d9) => Interpret (v1, v2, v3, v4, v5, v6, v7, v8, v9) (d1, d2, d3, d4, d5, d6, d7, d8, d9) where
    interpret (v1, v2, v3, v4, v5, v6, v7, v8, v9) answers = (interpret v1 answers, interpret v2 answers, interpret v3 answers, interpret v4 answers, interpret v5 answers, interpret v6 answers, interpret v7 answers, interpret v8 answers, interpret v9 answers)
instance (Interpret v1 d1, Interpret v2 d2, Interpret v3 d3, Interpret v4 d4, Interpret v5 d5, Interpret v6 d6, Interpret v7 d7, Interpret v8 d8, Interpret v9 d9, Interpret v10 d10) => Interpret (v1, v2, v3, v4, v5, v6, v7, v8, v9, v10) (d1, d2, d3, d4, d5, d6, d7, d8, d9, d10) where
    interpret (v1, v2, v3, v4, v5, v6, v7, v8, v9, v10) answers = (interpret v1 answers, interpret v2 answers, interpret v3 answers, interpret v4 answers, interpret v5 answers, interpret v6 answers, interpret v7 answers, interpret v8 answers, interpret v9 answers, interpret v10 answers)
instance (Interpret v1 d1, Interpret v2 d2, Interpret v3 d3, Interpret v4 d4, Interpret v5 d5, Interpret v6 d6, Interpret v7 d7, Interpret v8 d8, Interpret v9 d9, Interpret v10 d10, Interpret v11 d11) => Interpret (v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11) (d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11) where
    interpret (v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11) answers = (interpret v1 answers, interpret v2 answers, interpret v3 answers, interpret v4 answers, interpret v5 answers, interpret v6 answers, interpret v7 answers, interpret v8 answers, interpret v9 answers, interpret v10 answers, interpret v11 answers)
instance (Interpret v1 d1, Interpret v2 d2, Interpret v3 d3, Interpret v4 d4, Interpret v5 d5, Interpret v6 d6, Interpret v7 d7, Interpret v8 d8, Interpret v9 d9, Interpret v10 d10, Interpret v11 d11, Interpret v12 d12) => Interpret (v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12) (d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12) where
    interpret (v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12) answers = (interpret v1 answers, interpret v2 answers, interpret v3 answers, interpret v4 answers, interpret v5 answers, interpret v6 answers, interpret v7 answers, interpret v8 answers, interpret v9 answers, interpret v10 answers, interpret v11 answers, interpret v12 answers)
instance (Interpret v1 d1, Interpret v2 d2, Interpret v3 d3, Interpret v4 d4, Interpret v5 d5, Interpret v6 d6, Interpret v7 d7, Interpret v8 d8, Interpret v9 d9, Interpret v10 d10, Interpret v11 d11, Interpret v12 d12, Interpret v13 d13) => Interpret (v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13) (d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13) where
    interpret (v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13) answers = (interpret v1 answers, interpret v2 answers, interpret v3 answers, interpret v4 answers, interpret v5 answers, interpret v6 answers, interpret v7 answers, interpret v8 answers, interpret v9 answers, interpret v10 answers, interpret v11 answers, interpret v12 answers, interpret v13 answers)
instance (Interpret v1 d1, Interpret v2 d2, Interpret v3 d3, Interpret v4 d4, Interpret v5 d5, Interpret v6 d6, Interpret v7 d7, Interpret v8 d8, Interpret v9 d9, Interpret v10 d10, Interpret v11 d11, Interpret v12 d12, Interpret v13 d13, Interpret v14 d14) => Interpret (v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14) (d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14) where
    interpret (v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14) answers = (interpret v1 answers, interpret v2 answers, interpret v3 answers, interpret v4 answers, interpret v5 answers, interpret v6 answers, interpret v7 answers, interpret v8 answers, interpret v9 answers, interpret v10 answers, interpret v11 answers, interpret v12 answers, interpret v13 answers, interpret v14 answers)
instance (Interpret v1 d1, Interpret v2 d2, Interpret v3 d3, Interpret v4 d4, Interpret v5 d5, Interpret v6 d6, Interpret v7 d7, Interpret v8 d8, Interpret v9 d9, Interpret v10 d10, Interpret v11 d11, Interpret v12 d12, Interpret v13 d13, Interpret v14 d14, Interpret v15 d15) => Interpret (v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15) (d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15) where
    interpret (v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15) answers = (interpret v1 answers, interpret v2 answers, interpret v3 answers, interpret v4 answers, interpret v5 answers, interpret v6 answers, interpret v7 answers, interpret v8 answers, interpret v9 answers, interpret v10 answers, interpret v11 answers, interpret v12 answers, interpret v13 answers, interpret v14 answers, interpret v15 answers)

-- Interpret instance for list of interpretables.
instance (Functor f, Interpret a v) => Interpret (f a) (f v) where
    interpret vs answers = fmap ((flip interpret) answers) vs

instance (Interpret v ()) where
    interpret v answers = ()

-- Solving NPrograms with a SAT Solver
solveNProgram :: (a -> Model -> b) -> SatSolver -> NProgramComputation a -> (Maybe Bool, [b])
solveNProgram interpret ss nprogramComputation =
    let (theNVars, NProgram formula unusedVars traces) = runState nprogramComputation emptyNProgram
        numVars = head unusedVars - 1
        results = solveAll ss (numVars, formula)
    in case results of
         Just []     -> (Just False, error "Unsatisfiable formula") -- Just [] -- error "Unsatisfiable formula"
         Just models -> let tracedModels = map (traceTraces traces) models in
                        ((if null traces then id else seq (head tracedModels)) (Just True),
                         map (interpret theNVars) tracedModels)
         Nothing     -> (Nothing, error "Solve time limit exceeded")

traceTraces :: [NTrace] -> (IM.IntMap Bool) -> (IM.IntMap Bool)
traceTraces traces model =
    if null traces then model else
    myTrace 1 (concatMap (\(NTrace tag v show) ->
                          seq model $
                          "NTrace: " ++ tag ++ " = " ++ show (interpret v model) ++ "\n") (reverse traces))
    model

evalAllNProgram :: (Interpret a b) => SatSolver -> NProgramComputation a -> (Maybe Bool, [b])
evalAllNProgram = solveNProgram interpret

evalNProgram :: (Interpret a b) => SatSolver -> NProgramComputation a -> (Maybe Bool, b)
evalNProgram ss nprogramComputation =
    (second head) $ evalAllNProgram ss nprogramComputation

execNProgram :: SatSolver -> NProgramComputation a -> Maybe Bool
execNProgram ss nprogramComputation =
    fst $ solveNProgram (const (const ())) ss nprogramComputation

{- QuickCheck Properties -}

prop_assertConjoinShow formula =
    let (NProgram baseFormula _ _) = emptyNProgram in
    (show $ execState (assert formula) emptyNProgram) == (show $ conjoin baseFormula formula)
