module Embeddings where

import ILPSAT
import ILPSATReduction
import qualified Data.HashTable as HT
    
-- Takes a surrogate expression and a formula to embed.  The surrogate
-- expression is a function that takes a single proposition and gives
-- a constraint expressed using that proposition.  The embedConstraint
-- function will ensure that the truth value of the proposition given
-- to the surrogate expression will be equal to the truth value of the
-- formula being embedded.  The resulting constraint will be a formula
-- respecting all of the above.

type Embedding a = (Proposition a -> Problem a) -> Problem a

embedConstraint :: (Show a) => String -> Constraint a -> Embedding a
embedConstraint _ (Inequality ineq) _ = undefined
embedConstraint tag c surrogateExpr = embedConstraint' tag surrogateExpr (cleanConstraint c)

cleanConstraint (Formula formula) = Formula $ filter (not . null . fromClause) formula
cleanConstraint (TopFormula formula) = TopFormula $ filter (not . null . fromClause) formula
cleanConstraint (Inequality ineq) = Inequality ineq
                                      
embedConstraint' :: forall a. (Show a) => String -> (Proposition a -> Problem a) -> Constraint a -> Problem a
embedConstraint' tag surrogateExpr formula@(Formula [Clause [p]]) = map cleanConstraint (surrogateExpr p)
embedConstraint' tag surrogateExpr (TopFormula formula) = [TopFormula formula]
embedConstraint' tag surrogateExpr (Formula formula) =
    let t = Surrogate (Formula formula) tag :: Proposition a
        equivalenceConstraint = conjoin ([Formula [(Clause $ neg t:(fromClause clause)) | clause <- formula],
                                          Formula $ foldl ((\((Clause ts):rest) ->
                                                               (++rest) . fromFormula . head .
                                                               (embedConstraint' "non-uniq"
                                                                                 (\tx -> [Formula [Clause (tx:ts)]])) .
                                                               negateClause) :: [Clause a] -> Clause a -> [Clause a])
                                                     [Clause [t]] formula] :: [Constraint a])
    in         map cleanConstraint (surrogateExpr t) ++ [equivalenceConstraint]

pluralizeEmbedding fns multiSurrogateExpr = pluralizeEmbedding' fns [] multiSurrogateExpr
pluralizeEmbedding' [] acc multiSurrogateExpr = multiSurrogateExpr acc
pluralizeEmbedding' (fn:fns) acc multiSurrogateExpr = fn $ \a-> pluralizeEmbedding' fns (a:acc) multiSurrogateExpr

--class Pluralize where
--    pluralize :: (a1 -> t) -> [a1] -> [t']
--    pluralize embedding firstArgList = map embedding firstArgList
--autoPluralize embedding firstArgList = concatMap autoPluralize $ map embedding firstArgList

--embedTautology = (flip (embedConstraint "taut")) (\p -> Formula [Clause [p]])
tautology embedding = embedding (\surrogate -> Formula [Clause [surrogate]])
unsat embedding = embedding (\surrogate -> Formula [Clause [Not surrogate]])

embedConstraints tags constraints multiSurrogateExpr =
    embedConstraints' tags [] constraints multiSurrogateExpr
embedConstraints' tags acc [] multiSurrogateExpr = multiSurrogateExpr acc
embedConstraints' tags acc constraints multiSurrogateExpr =
    embedConstraint (head tags) (head constraints) $ \surrogate ->
    embedConstraints' (tail tags) (surrogate : acc) (tail constraints) multiSurrogateExpr
                 
negateClause (Clause c) = Formula [Clause [neg p] | p <- c]
--negateClause (TopClause c) = Formula [TopClause [neg p] | p <- c]
equivalent p1 p2 = Formula [Clause [Not p1, p2], Clause [p1, Not p2]]
