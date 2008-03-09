module Embeddings where

import ILPSAT
import ILPSATReduction
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
embedFormula tag f surrogateExpr = embedFormula' tag surrogateExpr (cleanFormula f)

embedFormula' :: forall a. (Show a) => String -> (Proposition a -> Problem a) -> Constraint a -> Problem a
embedFormula' tag surrogateExpr formula@(Formula [Clause [p]]) = map cleanFormula (surrogateExpr p)
embedFormula' tag surrogateExpr (Formula formula) =
    let t = Surrogate (Formula formula) tag :: Proposition a
        equivalenceConstraint = conjoin ([Formula [(Clause $ neg t:(fromClause clause)) | clause <- formula],
                                         Formula $ foldl ((\((Clause ts):rest) ->
                                                               (++rest) . fromFormula . conjoin .
                                                               (embedFormula' "non-uniq"
                                                                                 (\tx -> [Formula [Clause (tx:ts)]])) .
                                                               negateClause) :: [Clause a] -> Clause a -> [Clause a])
                                                     [Clause [t]] formula] :: [Constraint a])
    in equivalenceConstraint : (map cleanFormula $ surrogateExpr t)

embedTopFormula tag tf surrogateExpr = [tf]
-- For embedInequality, would need a ineqNumber for trans and a tag to
-- embed.  Instead, just make the caller call trans with the
-- ineqNumber and call embedProblem with a tag.
embedInequality tag ineq surrogateExpr = undefined

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

embedProblem :: (Show a) => String -> Problem a -> (Proposition a -> Problem a) -> Problem a
embedProblem tag problem surrogateExpr =
    let (tfs, others) = partition isTopFormula problem in
    embedFormula tag (conjoin others) $ \othersProposition ->
           [TopFormula (concatMap fromFormula tfs)] ++
           surrogateExpr othersProposition
           

negateClause (Clause c) = Formula [Clause [neg p] | p <- c]

cleanFormula (Formula formula) = Formula $ filter (not . null . fromClause) formula
cleanFormula (TopFormula formula) = TopFormula $ filter (not . null . fromClause) formula
                          
pluralizeEmbedding fns multiSurrogateExpr = pluralizeEmbedding' fns [] multiSurrogateExpr
pluralizeEmbedding' [] acc multiSurrogateExpr = multiSurrogateExpr acc
pluralizeEmbedding' (fn:fns) acc multiSurrogateExpr = fn $ \a-> pluralizeEmbedding' fns (a:acc) multiSurrogateExpr

-- Convenience functions operating on embeddings
tautology embedding = embedding (\surrogate -> Formula [Clause [surrogate]])
unsat embedding = embedding (\surrogate -> Formula [Clause [Not surrogate]])
