module Main where

import NProgram
import NVar
import NInteger
import Control.Monad.State
import SatSolvers
import Solving
    
multiplication :: State NProgram (NWord8, NWord8, NWord8, NInteger)
multiplication = do
  --let a = NInteger.fromInteger 3
  --let b = NInteger.fromInteger 7
  let c = NInteger.fromInteger 50
  a <- new
  b <- new
  --c <- new 16
  c' <- mul a b
  equal c c' >>= assert
  notEqual b (NInteger.fromInteger 1 `asTypeOf` b) >>= assert
  notEqual a (NInteger.fromInteger 1 `asTypeOf` a) >>= assert
  return (a, b, c, c')

main = do
  let Just solutions = solveAllNProgram Minisat multiplication
  forM_ solutions $ \(a,b,c,c') -> do
         putStrLn $ "a: " ++ show (a::Int)
         putStrLn $ "b: " ++ show (b::Int)
         putStrLn $ "c: " ++ show (c::Int)
         putStrLn $ "c': " ++ show (c'::Integer)
         putStrLn ""
