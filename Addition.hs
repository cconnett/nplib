module Main where

import NProgram
import NInteger
import Control.Monad.State
import SatSolvers

--addition :: NIntegral k => State NProgram (k, k, k)
addition :: State NProgram (NInt, NInt, NInt)
addition = do
  let a = NInteger.fromInteger 47
  --let b = NInteger.fromInteger 81
  let c = NInteger.fromInteger 128
  --a <- new 16
  b <- new 16
  --c <- new 16
  add c a b >>= assert
  return (a, b, c)

main = do
  let (worked, (get, (a,b,c))) = runNProgram RSat addition
  print (toVars a)
  print (toVars b)
  print (toVars c)
  putStrLn $ "a: " ++ show (get a::Int)
  putStrLn $ "b: " ++ show (get b::Int)
  putStrLn $ "c: " ++ show (get c::Int)
