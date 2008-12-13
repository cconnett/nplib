module TestNPLib where

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

mode = RSat

prop_doubleNegation prop = prop == (neg $ neg $ prop)

prop_if' a b =
    (a==b) == (snd $
               evalNProgram Minisat (do
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
prop_deny a b =
    (a/=b) == (fromJust $
               execNProgram Minisat (do
                                      let a'::NInteger = NInteger.fromInteger a
                                      let b'::NInteger = NInteger.fromInteger b
                                      eq <- a'`equal`b'
                                      deny eq)
              )
