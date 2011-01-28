{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module NPLib
    (NProgramComputation
    ,takeSatVar
    ,takeSatVars
    ,assert
    ,assertAll
    ,ntrace

    ,Nondeterministic
    ,toVars
    ,fromVars
    ,true
    ,false
    ,new

    ,Interpret
    ,interpret
    ,varsUnderModel

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

data NTrace = forall n d. (Interpret n d) => NTrace String n (d -> String)

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

ntrace tag v = do
  NProgram f unusedVars traces <- get
  put $ NProgram f unusedVars ((NTrace tag v show):traces)

-- The class of Nondeterministic types represent non-deterministic
-- structures.
class Nondeterministic n where
    -- Convert to and from a list of Vars.
    toVars :: n -> [Var]
    fromVars :: [Var] -> n

    -- Statefully allocate new variables
    new :: NProgramComputation n

-- The Interpret class allows the interpretation of a Nondeterministic
-- type into a related deterministic type, given a model of the
-- formula it was used in.
class Interpret n d | n -> d, d -> n where
    interpret :: Model -> n -> d

-- Nondeterministic and Interpret instances for Var
instance Nondeterministic Var where
    toVars var = [var]
    fromVars vars = last vars

    new = takeSatVar
instance Interpret Var Bool where
    interpret model n = model IM.! n

varsUnderModel :: (Nondeterministic n) => Model -> n -> [Bool]
varsUnderModel model n = map (model IM.!) (toVars n)

-- Interpret instances for tuples up to 15.
instance (Interpret n1 d1, Interpret n2 d2) => Interpret (n1, n2) (d1, d2) where
    interpret model (n1, n2) = (interpret model n1, interpret model n2)
instance (Interpret n1 d1, Interpret n2 d2, Interpret n3 d3) => Interpret (n1, n2, n3) (d1, d2, d3) where
    interpret model (n1, n2, n3) = (interpret model n1, interpret model n2,  interpret model n3)
instance (Interpret n1 d1, Interpret n2 d2, Interpret n3 d3, Interpret n4 d4) => Interpret (n1, n2, n3, n4) (d1, d2, d3, d4) where
    interpret model (n1, n2, n3, n4) = (interpret model n1,  interpret model n2,  interpret model n3,  interpret model n4)
instance (Interpret n1 d1, Interpret n2 d2, Interpret n3 d3, Interpret n4 d4, Interpret n5 d5) => Interpret (n1, n2, n3, n4, n5) (d1, d2, d3, d4, d5) where
    interpret model (n1, n2, n3, n4, n5) = (interpret model n1,  interpret model n2,  interpret model n3,  interpret model n4,  interpret model n5)
instance (Interpret n1 d1, Interpret n2 d2, Interpret n3 d3, Interpret n4 d4, Interpret n5 d5, Interpret n6 d6) => Interpret (n1, n2, n3, n4, n5, n6) (d1, d2, d3, d4, d5, d6) where
    interpret model (n1, n2, n3, n4, n5, n6) = (interpret model n1,  interpret model n2,  interpret model n3,  interpret model n4,  interpret model n5,  interpret model n6)
instance (Interpret n1 d1, Interpret n2 d2, Interpret n3 d3, Interpret n4 d4, Interpret n5 d5, Interpret n6 d6, Interpret n7 d7) => Interpret (n1, n2, n3, n4, n5, n6, n7) (d1, d2, d3, d4, d5, d6, d7) where
    interpret model (n1, n2, n3, n4, n5, n6, n7) = (interpret model n1,  interpret model n2,  interpret model n3,  interpret model n4,  interpret model n5,  interpret model n6,  interpret model n7)
instance (Interpret n1 d1, Interpret n2 d2, Interpret n3 d3, Interpret n4 d4, Interpret n5 d5, Interpret n6 d6, Interpret n7 d7, Interpret n8 d8) => Interpret (n1, n2, n3, n4, n5, n6, n7, n8) (d1, d2, d3, d4, d5, d6, d7, d8) where
    interpret model (n1, n2, n3, n4, n5, n6, n7, n8) = (interpret model n1,  interpret model n2,  interpret model n3,  interpret model n4,  interpret model n5,  interpret model n6,  interpret model n7,  interpret model n8)
instance (Interpret n1 d1, Interpret n2 d2, Interpret n3 d3, Interpret n4 d4, Interpret n5 d5, Interpret n6 d6, Interpret n7 d7, Interpret n8 d8, Interpret n9 d9) => Interpret (n1, n2, n3, n4, n5, n6, n7, n8, n9) (d1, d2, d3, d4, d5, d6, d7, d8, d9) where
    interpret model (n1, n2, n3, n4, n5, n6, n7, n8, n9) = (interpret model n1,  interpret model n2,  interpret model n3,  interpret model n4,  interpret model n5,  interpret model n6,  interpret model n7,  interpret model n8,  interpret model n9)
instance (Interpret n1 d1, Interpret n2 d2, Interpret n3 d3, Interpret n4 d4, Interpret n5 d5, Interpret n6 d6, Interpret n7 d7, Interpret n8 d8, Interpret n9 d9, Interpret n10 d10) => Interpret (n1, n2, n3, n4, n5, n6, n7, n8, n9, n10) (d1, d2, d3, d4, d5, d6, d7, d8, d9, d10) where
    interpret model (n1, n2, n3, n4, n5, n6, n7, n8, n9, n10) = (interpret model n1,  interpret model n2,  interpret model n3,  interpret model n4,  interpret model n5,  interpret model n6,  interpret model n7,  interpret model n8,  interpret model n9,  interpret model n10)
instance (Interpret n1 d1, Interpret n2 d2, Interpret n3 d3, Interpret n4 d4, Interpret n5 d5, Interpret n6 d6, Interpret n7 d7, Interpret n8 d8, Interpret n9 d9, Interpret n10 d10, Interpret n11 d11) => Interpret (n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11) (d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11) where
    interpret model (n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11) = (interpret model n1,  interpret model n2,  interpret model n3,  interpret model n4,  interpret model n5,  interpret model n6,  interpret model n7,  interpret model n8,  interpret model n9,  interpret model n10,  interpret model n11)
instance (Interpret n1 d1, Interpret n2 d2, Interpret n3 d3, Interpret n4 d4, Interpret n5 d5, Interpret n6 d6, Interpret n7 d7, Interpret n8 d8, Interpret n9 d9, Interpret n10 d10, Interpret n11 d11, Interpret n12 d12) => Interpret (n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12) (d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12) where
    interpret model (n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12) = (interpret model n1,  interpret model n2,  interpret model n3,  interpret model n4,  interpret model n5,  interpret model n6,  interpret model n7,  interpret model n8,  interpret model n9,  interpret model n10,  interpret model n11,  interpret model n12)
instance (Interpret n1 d1, Interpret n2 d2, Interpret n3 d3, Interpret n4 d4, Interpret n5 d5, Interpret n6 d6, Interpret n7 d7, Interpret n8 d8, Interpret n9 d9, Interpret n10 d10, Interpret n11 d11, Interpret n12 d12, Interpret n13 d13) => Interpret (n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13) (d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13) where
    interpret model (n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13) = (interpret model n1,  interpret model n2,  interpret model n3,  interpret model n4,  interpret model n5,  interpret model n6,  interpret model n7,  interpret model n8,  interpret model n9,  interpret model n10,  interpret model n11,  interpret model n12,  interpret model n13)
instance (Interpret n1 d1, Interpret n2 d2, Interpret n3 d3, Interpret n4 d4, Interpret n5 d5, Interpret n6 d6, Interpret n7 d7, Interpret n8 d8, Interpret n9 d9, Interpret n10 d10, Interpret n11 d11, Interpret n12 d12, Interpret n13 d13, Interpret n14 d14) => Interpret (n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14) (d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14) where
    interpret model (n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14) = (interpret model n1,  interpret model n2,  interpret model n3,  interpret model n4,  interpret model n5,  interpret model n6,  interpret model n7,  interpret model n8,  interpret model n9,  interpret model n10,  interpret model n11,  interpret model n12,  interpret model n13,  interpret model n14)
instance (Interpret n1 d1, Interpret n2 d2, Interpret n3 d3, Interpret n4 d4, Interpret n5 d5, Interpret n6 d6, Interpret n7 d7, Interpret n8 d8, Interpret n9 d9, Interpret n10 d10, Interpret n11 d11, Interpret n12 d12, Interpret n13 d13, Interpret n14 d14, Interpret n15 d15) => Interpret (n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15) (d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15) where
    interpret model (n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15) = (interpret model n1,  interpret model n2,  interpret model n3,  interpret model n4,  interpret model n5,  interpret model n6,  interpret model n7,  interpret model n8,  interpret model n9,  interpret model n10,  interpret model n11,  interpret model n12,  interpret model n13,  interpret model n14,  interpret model n15)

-- Interpret instance for lists and arrays of interpretables.
-- Interpret instances for functors/traversables is incompatible,
-- because tuples are fmappable/traversable with the wrong meaning.
instance (Interpret n d) => Interpret [n] [d] where
    interpret = map . interpret
instance (Ix i, Interpret n d) => Interpret (Array i n) (Array i d) where
    interpret = fmap . interpret

-- Solving NPrograms with a SAT Solver
solveNProgram :: (Model -> n -> d) -> SatSolver -> NProgramComputation n -> (Maybe Bool, [d])
solveNProgram interpret ss nprogramComputation =
    let (theNVars, NProgram formula unusedVars traces) = runState nprogramComputation emptyNProgram
        numVars = head unusedVars - 1
        results = solveAll ss (numVars, formula)
    in case results of
         Just []     -> (Just False, error "Unsatisfiable formula") -- Just [] -- error "Unsatisfiable formula"
         Just models -> let tracedModels = map (traceTraces traces) models in
                        ((if null traces then id else seq (head tracedModels)) (Just True),
                         map ((flip interpret) theNVars) tracedModels)
         Nothing     -> (Nothing, error "Solve time limit exceeded")

traceTraces :: [NTrace] -> Model -> Model
traceTraces traces model =
    if null traces then model else
    myTrace 1 (concatMap (\(NTrace tag n show) ->
                          seq model $
                          "NTrace: " ++ tag ++ " = " ++ show (interpret model n) ++ "\n") (reverse traces))
    model

evalAllNProgram :: (Interpret n d) => SatSolver -> NProgramComputation n -> (Maybe Bool, [d])
evalAllNProgram = solveNProgram interpret

evalNProgram :: (Interpret n d) => SatSolver -> NProgramComputation n -> (Maybe Bool, d)
evalNProgram ss nprogramComputation =
    (second head) $ evalAllNProgram ss nprogramComputation

execNProgram :: SatSolver -> NProgramComputation n -> Maybe Bool
execNProgram ss nprogramComputation =
    fst $ solveNProgram (const (const ())) ss nprogramComputation

{- QuickCheck Properties -}

prop_assertConjoinShow formula =
    let (NProgram baseFormula _ _) = emptyNProgram in
    (show $ execState (assert formula) emptyNProgram) == (show $ conjoin baseFormula formula)
