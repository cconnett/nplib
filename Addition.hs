module Main where

import NProgram
import NInteger
import Control.Monad.State
import SatSolvers

--addition :: NIntegral k => State NProgram (k, k, k)
addition :: State NProgram [NInt]
addition = do
  a <- NInteger.fromInteger 47
  --b <- NInteger.fromInteger 81
  c <- NInteger.fromInteger 128
  --a <- new 16
  b <- new 16
  --c <- new 16
  add c a b >>= assert
  return [a, b, c]

main = do
  let (worked, [a,b,c]) = solve1NProgram Minisat addition
  putStrLn $ "a: " ++ show (a :: Int)
  putStrLn $ "b: " ++ show (b :: Int)
  putStrLn $ "c: " ++ show (c :: Int)
