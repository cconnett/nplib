module TestNPLib where

import Elections
import Embeddings
import SatSolvers
import SAT
import Utilities
import NProgram
import NVar
import Voting hiding (beats)

import Test.QuickCheck

mode = RSat

prop_doubleNegation prop = prop == (neg $ neg $ prop)
