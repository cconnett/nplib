module Main where

import SatSolvers
import NPLib
import NInteger
import Control.Monad

multiplication :: InstanceBuilder (NWord8, NWord8, NWord8)
multiplication = do
  --let a = NInteger.fromInteger 3
  --let b = NInteger.fromInteger 7
  a <- new
  b <- new
  --c <- new 16
  c <- mul a b
  equal c (NInteger.fromInteger 50) >>= assert
  notEqual b (NInteger.fromInteger 1 `asTypeOf` b) >>= assert
  notEqual a (NInteger.fromInteger 1 `asTypeOf` a) >>= assert
  return (a, b, c)

main = do
  let (_, solutions) = evalAllInstance Minisat multiplication
  forM_ solutions $ \(a,b,c) -> do
         putStrLn $ "a: " ++ show a
         putStrLn $ "b: " ++ show b
         putStrLn $ "c: " ++ show c
         putStrLn ""
