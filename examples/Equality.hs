module Main where

import NProgram
import NInteger
import Control.Monad.State
import SatSolvers
import NVar
import Solving

equality :: State NProgram (NInt16, NInt16)
equality = do
  let a = NInteger.fromInteger 1238
  b <- new
  equal a b >>= assert
  return (a, b)

main = do
  let (worked, (a,b)) = evalNProgram Minisat equality
  putStrLn $ "a: " ++ show (a::Int)
  putStrLn $ "b: " ++ show (b::Int)
