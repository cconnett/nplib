module Main where

import SatSolvers
import NPLib
import NInteger
import Data.Int

--multiplication :: NIntegral k => InstanceBuilder (k, k, k)
mul1 :: InstanceBuilder (NInt8, NInt8)
mul1 = do
  let a = NInteger.fromInteger 21
  a' <- mul1bit a true
  z' <- mul1bit a false
  return (a', z')

main = do
  let (worked, (a',z')) = evalInstance Minisat mul1
  putStrLn $ "a': " ++ show (a'::Int8)
  putStrLn $ "z': " ++ show (z'::Int8)
