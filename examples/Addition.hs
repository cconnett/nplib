module Main where

import SatSolvers
import NPLib
import NInteger

--addition :: NIntegral k => NProgramComputation (k, k, k)
addition :: NProgramComputation (NWord8, NWord8, NWord8)
addition = do
  let a = NInteger.fromInteger 47
  --let b = NInteger.fromInteger 81
  --a <- new
  b <- new
  --c <- new
  c <- add a b
  equal (NInteger.fromInteger 128) c >>= assert
  return (a, b, c)

main = do
  let (worked, (a,b,c)) = evalNProgram RSat addition
  putStrLn $ "a: " ++ show (a::Int)
  putStrLn $ "b: " ++ show (b::Int)
  putStrLn $ "c: " ++ show (c::Int)
