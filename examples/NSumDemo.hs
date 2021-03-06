module Main where

import SatSolvers
import NPLib
import NInteger

nsumDemo :: InstanceBuilder (NInteger, NInteger)
nsumDemo = do
  x <- new
  sum <- nsum [NInteger.fromInteger 21,
              NInteger.fromInteger 15,
              NInteger.fromInteger 97,
              x]
  equal sum (NInteger.fromInteger 200 `asTypeOf` sum) >>= assert
  return (x, sum)

main = do
  let (x, sum) = head . solutions $ buildInstance Minisat nsumDemo
  putStrLn $ "x: " ++ show x
  putStrLn $ "sum: " ++ show sum
