{-# OPTIONS -fglasgow-exts #-}
module TestNInteger where

import SatSolvers
import NInteger
import Test.QuickCheck
import NProgram
import Solving
import Data.Maybe
import Data.Bits
import Data.Word
import NVar
import Debug.Trace

prop_equal aa bb =
    (aa == bb) == (fromJust $
                   execNProgram Minisat (do
                                          let a::NInt8 = NInteger.fromInteger aa
                                          let b::NInt8 = NInteger.fromInteger bb
                                          a `equal` b >>= assert
                                          )
                  )
prop_notEqual aa bb =
    (aa /= bb) == (fromJust $
                   execNProgram Minisat (do
                                          let a::NInt8 = NInteger.fromInteger aa
                                          let b::NInt8 = NInteger.fromInteger bb
                                          a `notEqual` b >>= assert
                                          )
                  )
prop_leq aa bb =
    classify (aa < bb) "a < b" $
    classify (aa == bb) "a = b" $
    classify (aa > bb) "a > b" $
    (aa <= bb) == (fromJust $
                   execNProgram Minisat (do
                                          let a::NInt8 = NInteger.fromInteger aa
                                          let b::NInt8 = NInteger.fromInteger bb
                                          a `leq` b >>= assert
                                          )
                  )
prop_lt aa bb =
    classify (aa < bb) "a < b" $
    classify (aa == bb) "a = b" $
    classify (aa > bb) "a > b" $
    (aa < bb) == (fromJust $
                  execNProgram Minisat (do
                                         let a::NInt8 = NInteger.fromInteger aa
                                         let b::NInt8 = NInteger.fromInteger bb
                                         a `lt` b >>= assert
                                         )
                 )

prop_asSignedInteger a =
    a == asSignedInteger (map (testBit a) [31,30..0])
prop_asUnsignedInteger (a::Integer) = a > 0 ==>
    a == fromIntegral (asUnsignedInteger (map (testBit a) [31,30..0]))

prop_addition aa bb =
    (aa + bb) == (snd $
                  evalNProgram Minisat (do
                                         let a::NInt8 = NInteger.fromInteger aa
                                         let b::NInt8 = NInteger.fromInteger bb
                                         c <- add a b
                                         return c)
                 )
prop_subtraction aa bb =
    (aa - bb) == (snd $
                  evalNProgram Minisat (do
                                         let a::NInt8 = NInteger.fromInteger aa
                                         let b::NInt8 = NInteger.fromInteger bb
                                         c <- sub a b
                                         return c)
                 )
prop_multiplication aa bb =
    (aa * bb) == (snd $
                  evalNProgram Minisat (do
                                         let a::NInt16 = NInteger.fromInteger aa
                                         let b::NInt16 = NInteger.fromInteger bb
                                         c <- mul a b
                                         return c)
                 )
prop_factor cc =
    let factors = (take 5 $ fromJust $
                   evalAllNProgram Minisat (do
                                             a::NInt8 <- new
                                             b::NInt8 <- new
                                             let c::NInt8 = NInteger.fromInteger cc
                                             c' <- mul a b
                                             equal c c' >>= assert
                                             return (a,b)) :: [(Integer,Integer)]
                  )
    in all (\(aa, bb) -> (aa * bb) `mod` 256 == cc `mod` 256) factors
