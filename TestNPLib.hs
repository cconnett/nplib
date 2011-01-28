{-# LANGUAGE ScopedTypeVariables #-}

module TestNPLib where

import Data.Maybe
import Elections
import Embeddings
import NPLib
import NInteger
import SAT
import SatSolvers
import Utilities
import Voting hiding (beats)

import Test.QuickCheck

prop_doubleNegation prop = prop == (neg $ neg $ prop)

prop_if' ss a b =
    (a==b) == (snd $
               evalInstance ss (do
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
          evalInstance ss (do
                            let a'::NInteger = NInteger.fromInteger a
                            b'::NInteger <- newNInteger (width a')
                            a'`equal`b' >>= assert
                            return b')
         )
prop_deny ss a b =
    (a/=b) == (fromJust $
               execInstance ss (do
                                 let a'::NInteger = NInteger.fromInteger a
                                 let b'::NInteger = NInteger.fromInteger b
                                 eq <- a'`equal`b'
                                 deny eq)
              )
