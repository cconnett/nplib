module Main where

import SatSolvers
import NPLib
import NInteger

nsumDemo :: NProgramComputation (NInteger, NInteger)
nsumDemo = do
  x <- new
  sum <- nsum [NInteger.fromInteger 21,
              NInteger.fromInteger 15,
              NInteger.fromInteger 97,
              x]
  equal sum (NInteger.fromInteger 200 `asTypeOf` sum) >>= assert
  return (x, sum)

main = do
  let (worked, (x, sum)) = evalNProgram Minisat nsumDemo
  putStrLn $ "x: " ++ show x
  putStrLn $ "sum: " ++ show sum
