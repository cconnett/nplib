module Embeddings where

import ILPSAT
--import ILPSATReduction
import Hash
import qualified Data.HashTable as HT
import Data.List

type Embedding a = (Proposition a -> Problem a) -> Problem a

-- Takes a surrogate expression and a formula to embed.  The surrogate
-- expression is a function that takes a single proposition and gives
-- a constraint expressed using that proposition.  The embedConstraint
-- function will ensure that the truth value of the proposition given
-- to the surrogate expression will be equal to the truth value of the
-- formula being embedded.  The resulting constraint will be a formula
-- respecting all of the above.
embedFormula :: (Show a) => String -> Constraint a -> Embedding a
embedFormula tag (Formula [Clause [p]]) surrogateExpr = map cleanFormula (surrogateExpr p)
embedFormula tag formula@(Formula f) surrogateExpr =
    let (s, equivalenceConstraints) = embedFormula' tag (cleanFormula formula)
    in
      (map cleanFormula $ surrogateExpr s) ++ equivalenceConstraints

embedFormula' :: forall a. (Show a) => String -> Constraint a -> (Proposition a, Problem a)
embedFormula' tag (Formula formula) =
    let s = Surrogate tag (Formula formula) :: Proposition a
        equivalenceConstraints = TopFormula [(Clause $ neg s:(fromClause clause)) | clause <- formula] :
                                 (embedConstraints (map (const "") formula) (map negateClause formula) $ \ss ->
                                  [TopFormula [Clause $ ss ++ [s]]])
    in (s, equivalenceConstraints)

embedTopFormula tag tf surrogateExpr = [tf]
-- For embedInequality, would need a ineqNumber for trans and a tag to
-- embed.  Instead, just make the caller call trans with the
-- ineqNumber and call embedProblem with a tag.
embedInequality tag ineq surrogateExpr = undefined
--embedInequality tag ineq = embedFormula tag $ trans (hash tag) ineq


embedConstraint :: Show a => String -> Constraint a -> (Proposition a -> Problem a) -> Problem a
embedConstraint tag c surrogateExpr =
    case c of
      (Formula f) -> embedFormula tag (Formula f) surrogateExpr
      (TopFormula tf) -> embedTopFormula tag (TopFormula tf) surrogateExpr
      (Inequality ineq) -> embedInequality tag (Inequality ineq) surrogateExpr

embedConstraints :: Show a => [String] -> [Constraint a] -> ([Proposition a] -> Problem a) -> Problem a
embedConstraints tags constraints multiSurrogateExpr =
    embedConstraints' tags [] constraints multiSurrogateExpr
--embedConstraints' :: (Show a) =>
--                     [String] -> [Proposition a] -> [Constraint a] -> ([Proposition a] -> Problem a) ->
--                     Problem a
embedConstraints' tags acc [] multiSurrogateExpr = multiSurrogateExpr (reverse acc)
embedConstraints' tags acc constraints multiSurrogateExpr =
    embedConstraint (head tags) (head constraints) $ \surrogate ->
    embedConstraints' (tail tags) (surrogate : acc) (tail constraints) multiSurrogateExpr

embedProblem :: (Show a) => String -> Problem a -> Embedding a
embedProblem tag problem surrogateExpr =
    let (s, equivalenceConstraints) = embedProblem' tag problem
    in
      surrogateExpr s ++ equivalenceConstraints
embedProblem' tag problem =
    let (tfs, others) = partition isTopFormula problem
        (s, equivalenceConstraints) = embedFormula' tag (conjoin others)
    in
      (s, TopFormula (concatMap fromFormula tfs) : equivalenceConstraints)

negateClause (Clause c) = Formula [Clause [neg p] | p <- c]
                          
pluralizeEmbedding embeddings multiSurrogateExpr = pluralizeEmbedding' (reverse embeddings) [] multiSurrogateExpr
pluralizeEmbedding' [] acc multiSurrogateExpr = multiSurrogateExpr acc
pluralizeEmbedding' (embedding:embeddings) acc multiSurrogateExpr =
    embedding $ \a-> pluralizeEmbedding' embeddings (a:acc) multiSurrogateExpr

-- Convenience functions operating on embeddings
tautology embedding = embedding (\surrogate -> [Formula [Clause [surrogate]]])
unsat embedding = embedding (\surrogate -> [Formula [Clause [neg surrogate]]])
