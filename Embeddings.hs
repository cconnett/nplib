{-# OPTIONS -fglasgow-exts #-}
module Embeddings where

import Data.List
import SAT
import NProgram
import Control.Monad.State

class Cond c where
    condify :: c -> Stateful Var
instance Cond Var where
    condify = return
instance Cond Formula where
    condify = embedFormula

if' :: Cond c => c -> Formula -> Formula -> Stateful ()
if' cond then' else' = do
  condVar <- condify cond
  thenVar <- embedFormula then'
  elseVar <- embedFormula else'
  assert $ makeEquivalent condVar thenVar
  assert $ makeOpposed condVar elseVar

embedFormula :: Formula -> Stateful Var
embedFormula (Formula []) = return true
embedFormula (Formula [Clause [Merely v]]) = return v
embedFormula (Formula [Clause [Not v]]) = do
  s <- takeSatVar
  assert $ makeOpposed v s
  return s
embedFormula (Formula clauses) = do
  s <- takeSatVar
  assert $ Formula [(Clause $ Not s:(fromClause clause)) | clause <- clauses]
  ss <- mapM embedFormula (map negateClause clauses)
  assert $ Formula [Clause (map Merely (s:ss))]
  return s

negateClause (Clause c) = Formula [Clause [neg p] | p <- c]

negateFormula formula = do
  surrogate <- embedFormula formula
  return $ Formula [Clause [Not surrogate]]

deny :: Formula -> State NProgram ()
deny = (>>= assert) . negateFormula

embedFormulas = mapM embedFormula
