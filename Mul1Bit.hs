module Main where

import NProgram
import NInteger
import Control.Monad.State
import SatSolvers

--multiplication :: NIntegral k => State NProgram (k, k, k)
mul1 :: State NProgram (NInt, NInt)
mul1 = do
  let a = NInteger.fromInteger 21
  a' <- mul1bit a true
  z' <- mul1bit a false
  return (a', z')

main = do
  let (worked, (get, (a',z'))) = runNProgram Minisat mul1
  putStrLn $ "a': " ++ show (get a'::Int)
  putStrLn $ "z': " ++ show (get z'::Int)
