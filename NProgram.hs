{-# OPTIONS -fglasgow-exts #-}
module NProgram where

import Control.Monad.State
import SAT

data NProgram = NProgram Formula [Var]
instance Show NProgram where
    show (NProgram formula _) = show formula

type Stateful a = State NProgram a

-- Empty program has first and second variables as a reference false
-- and true respectively.
emptyNProgram :: NProgram
emptyNProgram = NProgram (Formula [Clause [Not 1], Clause [Merely 2]]) [3..]

false = 1 :: Var
true = 2 :: Var

takeSatVar :: State NProgram Var
takeSatVar = do
  NProgram formula unusedVars <- get
  put $ NProgram formula (tail unusedVars)
  return $ head unusedVars

takeSatVars n = replicateM n takeSatVar

assert :: Formula -> State NProgram ()
assert formula = do
  NProgram f unusedVars <- get
  put $ NProgram (conjoin [f, formula]) unusedVars
