module Main where

import NProgram
import NVar
import NInteger
import Control.Monad.State
import SatSolvers
import Solving

nsumDemo :: State NProgram (NWord8, NWord8)
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
  putStrLn $ "x: " ++ show (x::Int)
  putStrLn $ "sum: " ++ show (sum::Int)
