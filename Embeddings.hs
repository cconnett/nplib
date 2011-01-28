{-# LANGUAGE TypeSynonymInstances #-}

module Embeddings
    (embedFormula
    ,embedFormulas

    ,Cond
    ,condify
    ,if'

    ,negateClause
    ,negateFormula
    ,deny
    )
    where

import Data.List
import SAT
import NPLib

class Cond c where
    condify :: c -> NProgramComputation Var
instance Cond Var where
    condify = return
instance Cond Formula where
    condify = embedFormula

if' :: (Cond c1, Cond c2, Cond c3) => c1 -> c2 -> c3 -> NProgramComputation ()
if' cond then' else' = do
  condVar <- condify cond
  thenVar <- condify then'
  elseVar <- condify else'
  assert $ makeEquivalent condVar thenVar
  assert $ makeOpposed condVar elseVar

embedFormula :: Formula -> NProgramComputation Var
embedFormula = embedFormula' . toListForm
embedFormula' []= takeSatVar
embedFormula' [[Merely v]] = return v
embedFormula' [[Not v]] = do
  s <- takeSatVar
  assert $ makeOpposed v s
  return s
embedFormula' clauses = do
  s <- takeSatVar
  assert $ fromListForm [Not s:clause | clause <- clauses]
  ss <- mapM embedFormula (map negateClause clauses)
  assert $ fromListForm [map Merely (s:ss)]
  return s

embedFormulas = mapM embedFormula

negateClause props = fromListForm [[neg prop] | prop <- props]

negateFormula formula = do
  surrogate <- embedFormula formula
  return $ makeFalse surrogate

deny :: Formula -> NProgramComputation ()
deny = (>>= assert) . negateFormula

