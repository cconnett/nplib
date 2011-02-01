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
  let (a',z') = head . solutions $ buildInstance Minisat mul1
  putStrLn $ "a': " ++ show a'
  putStrLn $ "z': " ++ show z'
