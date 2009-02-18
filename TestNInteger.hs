{-# OPTIONS -fglasgow-exts #-}
module TestNInteger where

import SatSolvers
import SAT
import NPLib
import NInteger
import Test.QuickCheck
import Data.Maybe
import Data.Bits
import Data.Word
import Debug.Trace

prop_equal ss aa bb =
    (aa == bb) == (fromJust $
                   execNProgram ss (do
                                     let a::NInt8 = NInteger.fromInteger aa
                                     let b::NInt8 = NInteger.fromInteger bb
                                     a `equal` b >>= assert
                                          )
                  )
prop_notEqual ss aa bb =
    (aa /= bb) == (fromJust $
                   execNProgram ss (do
                                     let a::NInt8 = NInteger.fromInteger aa
                                     let b::NInt8 = NInteger.fromInteger bb
                                     a `notEqual` b >>= assert
                                          )
                  )
prop_leq ss aa bb =
    classify (aa < bb) "a < b" $
    classify (aa == bb) "a = b" $
    classify (aa > bb) "a > b" $
    (aa <= bb) == (fromJust $
                   execNProgram ss (do
                                     let a::NInt8 = NInteger.fromInteger aa
                                     let b::NInt8 = NInteger.fromInteger bb
                                     a `leq` b >>= assert
                                          )
                  )
prop_lt ss aa bb =
    classify (aa < bb) "a < b" $
    classify (aa == bb) "a = b" $
    classify (aa > bb) "a > b" $
    (aa < bb) == (fromJust $
                  execNProgram ss (do
                                    let a::NInt8 = NInteger.fromInteger aa
                                    let b::NInt8 = NInteger.fromInteger bb
                                    a `lt` b >>= assert
                                  )
                 )

prop_addition ss aa bb =
    (aa + bb) == (snd $
                  evalNProgram ss (do
                                    let a::NInt8 = NInteger.fromInteger aa
                                    let b::NInt8 = NInteger.fromInteger bb
                                    c <- add a b
                                    return c)
                 )
prop_subtraction ss aa bb =
    (aa - bb) == (snd $
                  evalNProgram ss (do
                                    let a::NInt8 = NInteger.fromInteger aa
                                    let b::NInt8 = NInteger.fromInteger bb
                                    c <- sub a b
                                    return c)
                 )
prop_add_1bit ss listOfBool =
    (length $ filter id listOfBool) == (snd $ evalNProgram ss (add_1bit_prog listOfBool))
add_1bit_prog :: [Bool] -> NProgramComputation NInteger
add_1bit_prog listOfBool = do
  let x = [if bool then true else false
               | bool <- listOfBool]
  t <- nsum x
  return t
prop_negation ss aa =
    aa == (snd $
           evalNProgram ss (do
                             let negativeA::NInt8 = NInteger.fromInteger (-aa)
                             b::NInt8 <- new
                             negativeB <- NInteger.negate b
                             negativeA`equal`negativeB >>= assert
                             return b)
          )
prop_multiplication ss aa bb =
    (aa * bb) == (snd $
                  evalNProgram ss (do
                                    let a::NInt16 = NInteger.fromInteger aa
                                    let b::NInt16 = NInteger.fromInteger bb
                                    c <- mul a b
                                    return c)
                 )
prop_factor ss cc =
    let factors = (take 2 $ snd $
                   evalAllNProgram ss (do
                                        a::NInt8 <- new
                                        b::NInt8 <- new
                                        let c::NInt8 = NInteger.fromInteger cc
                                        c' <- mul a b
                                        equal c c' >>= assert
                                        return (a,b)) :: [(Integer,Integer)]
                  )
    in all (\(aa, bb) -> (aa * bb) `mod` 256 == cc `mod` 256) factors
