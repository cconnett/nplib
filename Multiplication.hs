module Main where

import NProgram
import NInteger
import Control.Monad.State
import SatSolvers

import Debug.Trace
    
--multiplication :: NIntegral k => State NProgram (k, k, k)
multiplication :: State NProgram (NInt, NInt, NInt)
multiplication = do
  --let a = NInteger.fromInteger 3
  --let b = NInteger.fromInteger 7
  let c = NInteger.fromInteger 21
  a <- new 16
  b <- new 16
  --c <- new 16
  mul c a b >>= assert
  return (a, b, c)

main = do
  let (worked, (get, (a,b,c))) = runNProgram Minisat multiplication
  print (toVars a)
  print (toVars b)
  print (toVars c)
  putStrLn $ "a: " ++ show (get a::Int)
  putStrLn $ "b: " ++ show (get b::Int)
  putStrLn $ "c: " ++ show (get c::Int)
