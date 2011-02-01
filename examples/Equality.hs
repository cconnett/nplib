module Main where

import SatSolvers
import NPLib
import NInteger
import Data.Int

equality :: InstanceBuilder (NInt16, NInt16)
equality = do
  let a = NInteger.fromInteger 1238
  b <- new
  equal a b >>= assert
  return (a, b)

main = do
  let (a,b) = head . solutions $ buildInstance Clasp equality
  putStrLn $ "a: " ++ show (a::Int16)
  putStrLn $ "b: " ++ show (b::Int16)
