module Main where

import SatSolvers
import NPLib
import NInteger

--multiplication :: NIntegral k => NProgramComputation (k, k, k)
mul1 :: NProgramComputation (NInt8, NInt8)
mul1 = do
  let a = NInteger.fromInteger 21
  a' <- mul1bit a true
  z' <- mul1bit a false
  return (a', z')

main = do
  let (worked, (a',z')) = evalNProgram Minisat mul1
  putStrLn $ "a': " ++ show (a'::Int)
  putStrLn $ "z': " ++ show (z'::Int)
