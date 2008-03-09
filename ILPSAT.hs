{-# OPTIONS -fglasgow-exts -fno-monomorphism-restriction #-}

module ILPSAT
    where

import Voting
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.HashTable as HT
import Data.Maybe
import Data.List
import Data.Ord
import Data.Char (ord)
import Test.QuickCheck
import Control.Monad
import Control.Arrow
import RunGenIO
import Random
import Foreign (unsafePerformIO)
    
import Debug.Trace
--import Text.Regex
texify vars = unlines $ map (\(str, i) -> "$" ++ show i ++ "=" ++ filter (/='"') str ++ "$\\\\") vars

-- Data type definitions for ILP and SAT problem forumations.

-- Formulas are conjunctions of Clauses, Clauses are disjuntions of Propositions.
-- Inequalities are (LHS = [(coefficient, variable)], RHS), with an implied less-than-or-equal-to: LHS <= RHS.
-- Constrants are polymorphic with respect to variables to be solved for.
data Constraint a = Formula ![Clause a]
                  | Inequality !([(Int, Proposition a)], Int)
                  | TopFormula ![Clause a]
--                     deriving (Show, Read, Eq, Ord)
                     deriving (Read, Eq, Ord)
data Clause a = Clause ![Proposition a]
--                     deriving (Show, Read, Eq, Ord)
                     deriving (Read, Eq, Ord)
data Proposition a = Merely !a
                   | Not !(Proposition a)
                   | Surrogate {sConstraint :: !(Constraint a), sTag :: !String}
                   | Auxiliary {auxIneqNumber :: !Int, auxTag :: !String, auxBitNo :: !Int, auxVarSet :: ![Proposition a]}
--                     deriving (Show, Read, Eq, Ord)
                     deriving (Read, Eq, Ord)

pushTL = TopFormula . fromFormula

-- A problem in this module is a set of constraints, which can be
-- mixed between SAT formula and ILP inequalities.
type Problem a = [Constraint a]

fromProposition :: Proposition a -> a
fromProposition (Merely var) = var
fromProposition (Not p) = fromProposition p

normalizeProposition (Not p) = normalizeProposition p
normalizeProposition prop = prop

neg :: Proposition a -> Proposition a
neg (Not p) = p
neg p = Not p

isNeg (Not p) = not (isNeg p)
isNeg _ = False
isPos = not . isNeg

isAux (Auxiliary _ _ _ _) = True
isAux _ = False
isSurrogate (Surrogate _ _) = True
isSurrogate _ = False

fromClause (Clause c) = c
fromFormula (Formula f) = f
fromFormula (TopFormula f) = f
fromInequality (Inequality ineq) = ineq

isFormula (Formula f) = True
isFormula _ = False
isTopFormula (TopFormula tf) = True
isTopFormula _ = False
isInequality (Inequality i) = True
isInequality _ = False

equivalent p1 p2 = Formula [Clause [Not p1, p2], Clause [p1, Not p2]]
                 
{-
-- Show instances for Constraint and helper types
  -}
-- {-
instance (Show a) => Show (Constraint a) where
    show (Formula f) = "Formula{" ++ (concat $ intersperse " ^ " $ map show f) ++ "}"
    show (Inequality (coeffsAndVars, b)) = "Ineq{" ++ (lhs ++ " <= " ++ rhs) ++ "}"
        where lhs = concat $ intersperse " + " $
                    (map (\(c, v) -> (show c ++ "*" ++ show v)) coeffsAndVars)
              rhs = show b

instance (Show a) => Show (Clause a) where
    show (Clause c) = "(" ++ (concat $ intersperse " v " $ map show c) ++ ")"

instance (Show a) => Show (Proposition a) where
    show = show2
-- -}
show2 (Merely a) = show a
show2 (Not p) = '-':(show p)
show2 (Surrogate f tag) = "<" ++ tag ++ ">"
show2 (Auxiliary ineqNo label bitNo varSet) =
    "Aux (" ++ show ineqNo ++ ", " ++ label ++ ", " ++ show bitNo ++ ", " ++ show varSet ++ ")"

-- Functor instances for Constraint
instance Functor Constraint where
    fmap f (Formula formula) = Formula (map (\(Clause c) -> Clause (map (propApply f) c) ) formula)
    fmap f (Inequality (addends, rhs)) = Inequality (map (second (propApply f)) addends, rhs)
propApply f (Not p) = Not (propApply f p)
propApply f (Merely v) = Merely (f v)

-- Var is a nice restricted version of Char that is convenient to use
-- in Arbitrary Constraints.
newtype Var = Var Char
    deriving (Eq, Ord)
instance Show Var where showsPrec _ (Var c) s = c:s
instance Read Var where readsPrec _ s = let [(c,s')] = (lex s) in [(Var (head c), s')]
instance Arbitrary Var where
    arbitrary = sized $ (\n -> elements (map Var (take (min (n`div`3 + 2) 9) ['A'..])))
    coarbitrary (Var v) = variant (ord v)

instance (Ord a, Arbitrary a) => Arbitrary (Constraint a) where
    arbitrary = oneof [arbitraryFormula, arbitraryInequality]
    coarbitrary (Formula f) = variant 0
    coarbitrary (Inequality i) = variant 1

arbitraryFormula :: (Arbitrary a) => Gen (Constraint a)
arbitraryFormula = sized (\n -> (liftM Formula) (resize (round $ sqrt $ fromIntegral n) arbitrary))

arbitraryInequality :: (Ord a, Arbitrary a) => Gen (Constraint a)
arbitraryInequality = sized $ (\n -> do
                                 coeffs <- vector (n+1)
                                 as <- vector (n+1)
                                 b <- arbitrary
                                 return $ Inequality (reduce coeffs (map normalizeProposition as), b))
    where reduce coeffs as = map (\(a,b)->(b,a)) $ M.toList $ M.fromListWith (+) (zip as coeffs)
instance (Arbitrary a) => Arbitrary (Clause a) where
    arbitrary = sized (\n -> (liftM Clause) (resize (round $ sqrt $ fromIntegral n) arbitrary))
    coarbitrary (Clause c) = coarbitrary c

instance (Arbitrary a) => Arbitrary (Proposition a) where
    arbitrary = oneof (map (\ctor -> (liftM ctor) arbitrary) [Merely, Not . Merely])
    coarbitrary (Merely p) = coarbitrary p
    coarbitrary (Not p) = coarbitrary p

multiConstraintProblem :: Gen (Problem Var)
multiConstraintProblem = sized $ \n -> resize (round ((**0.6) $ fromIntegral n)) arbitrary

conjoin formulas = Formula $ concatMap fromFormula formulas

detrivialize = catMaybes.(map detrivialize')
detrivialize' i@(Inequality (lhs, rhs))
    | null (fst it) && rhs >= 0 = Nothing
    | otherwise = Just (Inequality it)
    where it = (filter ((/=0).fst) lhs, rhs)
detrivialize' f@(Formula clauses) = if null it then Nothing else Just (Formula it)
    where it = filter (not.null.fromClause) clauses
