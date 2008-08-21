module Embeddings where

import Data.List

--nif :: NBool -> State NProgram a -> State NProgram a -> State NProgram a
--nif cond then' else' = do

embedFormula :: (Show a) => Formula -> Stateful Var
embedFormula (Formula [Clause [Merely v]]) surrogateExpr = return v
embedFormula (Formula [Clause [Not v]]) surrogateExpr = do
  s <- takeSatVar
  makeOpposed v s >>= assert
  return s
embedFormula (Formula clauses) = do
  s <- takeSatVar
  assert $ Formula [(Clause $ neg s:(fromClause clause)) | clause <- clauses]
  let ss = mapM embedFormula (map negateClause clauses)
  assert $ Formula [Clause (s:ss)]
  return s

negateClause (Clause c) = Formula [Clause [neg p] | p <- c]
                          
embedFormulas = mapM embedFormula
