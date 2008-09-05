module Main where

import NProgram
import NInteger
import Control.Monad.State
import SatSolvers

nsumDemo :: State NProgram (NInt, NInt, NInt)
nsumDemo = do
  x <- new 16
  y <- new 16
  sum <- nsum [NInteger.fromInteger 21,
              NInteger.fromInteger 15,
              NInteger.fromInteger 97,
              x, y]
  return (x, y, sum)

main = do
  let (worked, (get, (x, y, sum))) = runNProgram Minisat nsumDemo
  putStrLn $ "x: " ++ show (get x::Int)
  putStrLn $ "y: " ++ show (get y::Int)
  putStrLn $ "sum: " ++ show (get sum::Int)
