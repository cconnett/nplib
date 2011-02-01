{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module NPLib
    (InstanceBuilder
    ,buildInstance

    ,Instance
    ,satisfiability
    ,satisfiable
    ,solutions
    ,formula
    ,models
    ,solverUsed
    ,comments

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
import qualified Data.Map as M

data NTrace = forall n d. (Interpret n d) => NTrace String n (d -> String)

data Instance n = Instance {
      satisfiability :: Maybe Bool,
      formula :: Formula,
      models :: [Model],
      solverUsed :: SatSolver,
      comments :: [SolverComments],
      _NVars :: n
    }
satisfiable inst = case satisfiability inst of
                     Just True -> True
                     Just False -> False
                     Nothing -> False
solutions :: forall n d. (Interpret n d) => Instance n -> [d]
solutions inst = map ((flip interpret) (_NVars inst)) (models inst)

data IncompleteInstance = IncompleteInstance {
      formula' :: Formula,
      nextUnusedVar :: Var,
      traces :: [NTrace]
    }
instance Show IncompleteInstance where
    show iinst = show (formula' iinst, nextUnusedVar iinst)
type InstanceBuilder n = State IncompleteInstance n

-- Empty program has first and second variables as a reference false
-- and true respectively.
emptyInstance :: IncompleteInstance
emptyInstance = IncompleteInstance { formula' = fromListForm [[Not false], [Merely true]],
                                  nextUnusedVar = true + 1,
                                  traces = []}
false = 1 :: Var
true = 2 :: Var

takeSatVar :: InstanceBuilder Var
takeSatVar = do
  inst <- get
  put $ inst { nextUnusedVar = nextUnusedVar inst + 1 }
  return $ nextUnusedVar inst

takeSatVars n = replicateM n takeSatVar

assert :: Formula -> InstanceBuilder ()
assert newFormula = do
  inst <- get
  put $ inst { formula' = conjoin (formula' inst) newFormula }
assertAll :: [Formula] -> InstanceBuilder ()
assertAll = assert . conjoinAll

ntrace tag n = do
  inst <- get
  put $ inst { traces = (NTrace tag n show) : traces inst }

-- The class of Nondeterministic types represent non-deterministic
-- structures.
class Nondeterministic n where
    -- Convert to and from a list of Vars.
    toVars :: n -> [Var]
    fromVars :: [Var] -> n

    -- Statefully allocate new variables
    new :: InstanceBuilder n

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
instance Interpret () () where
    interpret model () = ()

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

-- Solving Instances with a SAT Solver
buildInstance :: (Interpret n d) => SatSolver -> InstanceBuilder n -> Instance n
buildInstance ss instanceBuilder =
    let (theNVars, IncompleteInstance formula' nextUnusedVar traces) = runState instanceBuilder emptyInstance
        numVars = nextUnusedVar - 1
        (satisiablility', models, comments) = solveAll ss (numVars, formula')
        tracedModels = map (traceTraces traces) models
    in Instance { satisfiability = satisiablility',
                  formula = formula',
                  models = tracedModels,
                  solverUsed = ss,
                  comments = comments,
                  _NVars = theNVars
                }

traceTraces :: [NTrace] -> Model -> Model
traceTraces traces model =
    if null traces then model else
    myTrace 1 (concatMap (\(NTrace tag n show) ->
                          seq model $
                          "NTrace: " ++ tag ++ " = " ++ show (interpret model n) ++ "\n") (reverse traces))
    model

{- QuickCheck Properties -}

prop_assertConjoinShow formula =
    let (IncompleteInstance baseFormula _ _) = emptyInstance in
    (show $ execState (assert formula) emptyInstance) == (show $ conjoin baseFormula formula)
