module Main where

import NProgram
import NInteger
import Control.Monad.State
import SatSolvers

equality :: State NProgram (NInt, NInt)
equality = do
  a <- NInteger.fromInteger 1238
  b <- new 16
  equal a b >>= assert
  return (a, b)

main = do
  let (worked, (get, (a,b))) = runNProgram Minisat equality
  print (toVars a)
  print (toVars b)
  putStrLn $ "a: " ++ show (get a::Int)
  putStrLn $ "b: " ++ show (get b::Int)
