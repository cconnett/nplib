module Main where

import NProgram
import NVar
import NInteger
import Control.Monad.State
import SatSolvers
import Solving

--addition :: NIntegral k => State NProgram (k, k, k)
addition :: State NProgram (NWord8, NWord8, NWord8)
addition = do
  let a = NInteger.fromInteger 47
  --let b = NInteger.fromInteger 81
  let c = NInteger.fromInteger 128
  --a <- new
  b <- new
  --c <- new
  add c a b >>= assert
  return (a, b, c)

main = do
  let (worked, (a,b,c)) = evalNProgram RSat addition
  putStrLn $ "a: " ++ show (a::Int)
  putStrLn $ "b: " ++ show (b::Int)
  putStrLn $ "c: " ++ show (c::Int)
