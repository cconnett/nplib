module TestNPLib where

import Control.Monad.State
import Data.Maybe
import Elections
import Embeddings
import NInteger
import NProgram
import NVar
import SAT
import SatSolvers
import Solving
import Utilities
import Voting hiding (beats)

import Test.QuickCheck

prop_doubleNegation prop = prop == (neg $ neg $ prop)

prop_if' ss a b =
    (a==b) == (snd $
               evalNProgram ss (do
                                 cond::Var <- new
                                 let a'::NInteger = NInteger.fromInteger a
                                 let b'::NInteger = NInteger.fromInteger b
                                 eq <- a'`equal`b'
                                 if' cond
                                     (eq)
                                     (emptyFormula)
                                 if' eq
                                     (emptyFormula)
                                     (makeFalse cond)
                                 return cond)
              )
prop_interpretInteger ss a =
    a == (snd $
          evalNProgram ss (do
                            let a'::NInteger = NInteger.fromInteger a
                            b'::NInteger <- fixedWidthNew (width a')
                            a'`equal`b' >>= assert
                            return b')
         )
prop_deny ss a b =
    (a/=b) == (fromJust $
               execNProgram ss (do
                                 let a'::NInteger = NInteger.fromInteger a
                                 let b'::NInteger = NInteger.fromInteger b
                                 eq <- a'`equal`b'
                                 deny eq)
              )
prop_assertConjoinShow formula =
    let (NProgram baseFormula _) = emptyNProgram in
    (show $ execState (assert formula) emptyNProgram) == (show $ conjoin [baseFormula,formula])

-- cleanFormula removes null clauses from a formula.  Minisat takes
-- null clauses to be unsatisfiable, and ZChaff and RSat ignore them.
-- So clean any formulas used in properties checking for agreement
-- between the sat solvers.
cleanFormula (Formula formula) = Formula $ filter (not . null . fromClause) formula
