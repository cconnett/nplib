{-# OPTIONS -fglasgow-exts #-}
module Embeddings
    (embedFormula
    ,embedFormulas

    ,Cond
    ,if'

    ,negateClause
    ,negateFormula
    ,deny
    )
    where

import Data.List
import SAT
import NPLib
import Control.Monad.State

class Cond c where
    condify :: c -> Stateful Var
instance Cond Var where
    condify = return
instance Cond Formula where
    condify = embedFormula

if' :: (Cond c1, Cond c2, Cond c3) => c1 -> c2 -> c3 -> Stateful ()
if' cond then' else' = do
  condVar <- condify cond
  thenVar <- condify then'
  elseVar <- condify else'
  assert $ makeEquivalent condVar thenVar
  assert $ makeOpposed condVar elseVar

embedFormula :: Formula -> Stateful Var
embedFormula (Formula []) = takeSatVar
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

embedFormulas = mapM embedFormula

negateClause (Clause c) = Formula [Clause [neg p] | p <- c]

negateFormula formula = do
  surrogate <- embedFormula formula
  return $ Formula [Clause [Not surrogate]]

deny :: Formula -> Stateful ()
deny = (>>= assert) . negateFormula

