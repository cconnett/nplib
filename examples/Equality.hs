module Main where

import SatSolvers
import NPLib
import NInteger

equality :: NProgramComputation (NInt16, NInt16)
equality = do
  let a = NInteger.fromInteger 1238
  b <- new
  equal a b >>= assert
  return (a, b)

main = do
  let (worked, (a,b)) = evalNProgram Minisat equality
  putStrLn $ "a: " ++ show (a::Int)
  putStrLn $ "b: " ++ show (b::Int)
