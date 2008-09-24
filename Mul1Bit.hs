module Main where

import NProgram
import NInteger
import Control.Monad.State
import SatSolvers
import Solving

--multiplication :: NIntegral k => State NProgram (k, k, k)
mul1 :: State NProgram (NInt8, NInt8)
mul1 = do
  let a = NInteger.fromInteger 21
  a' <- mul1bit a true
  z' <- mul1bit a false
  return (a', z')

main = do
  let (worked, (a',z')) = runNProgram Minisat mul1
  putStrLn $ "a': " ++ show (a'::Int)
  putStrLn $ "z': " ++ show (z'::Int)
