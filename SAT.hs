module SAT
    (Formula
    ,Clause
    ,Proposition(Merely,Not)
    ,Var

    ,propositionVar
    ,neg
    ,isNeg
    ,isPos

    ,conjoin
    ,conjoinAll

    ,numClauses
    ,formulaFromClauses
    ,formulaFromClause
    ,clauseFromPropositions
    ,toListForm
    ,fromListForm

    ,toDIMACS

    ,makeTrue
    ,makeFalse
    ,makeEquivalent
    ,makeOpposed
    ,implies
    ,impliesSome

    ,emptyFormula
    ,formulaSatisfied
    )
    where

import qualified Data.IntMap as IM
import qualified Data.Map as M
import qualified Data.Sequence as Seq
import qualified Data.Foldable as Fold
import qualified Data.HashTable as HT
import Data.Maybe
import Data.List
import Data.Ord
import Data.Char (ord)
import Test.QuickCheck
import Control.Monad
import Control.Arrow
import Random
import Foreign (unsafePerformIO)

import Debug.Trace

-- Formulas are conjunctions of Clauses, Clauses are disjuntions of Propositions.
newtype Formula = Formula (Seq.Seq Clause)
    deriving (Eq, Ord)

newtype Clause = Clause [Proposition]
    deriving (Eq, Ord)

data Proposition = Merely Var
                 | Not Var
                   deriving (Eq, Ord)

type Var = Int

propositionVar (Merely v) = v
propositionVar (Not v) = v

neg :: Proposition -> Proposition
neg (Not v) = Merely v
neg (Merely v) = Not v

isNeg (Not v) = True
isNeg _ = False
isPos = not . isNeg

conjoin (Formula clauses1) (Formula clauses2) = Formula $ clauses1 Seq.>< clauses2
conjoinAll formulas = Formula $ Fold.foldMap (\(Formula f) -> f) formulas

numClauses :: Formula -> Int
numClauses (Formula f) = Seq.length f

formulaFromClause :: Clause -> Formula
formulaFromClause = Formula . Seq.singleton
formulaFromClauses :: [Clause] -> Formula
formulaFromClauses = Formula . Seq.fromList
clauseFromPropositions :: [Proposition] -> Clause
clauseFromPropositions ps = Clause ps

toListForm (Formula f) = map (\(Clause c) -> c) $ Fold.toList f
fromListForm = formulaFromClauses . (map clauseFromPropositions)

makeTrue v = Formula $ Seq.fromList [Clause [Merely v]]
makeFalse v = Formula $ Seq.fromList [Clause [Not v]]
makeEquivalent v1 v2 = Formula $ Seq.fromList [Clause [Not v1, Merely v2], Clause [Merely v1, Not v2]]
makeOpposed v1 v2 = Formula $ Seq.fromList [Clause [Merely v1, Merely v2], Clause [Not v1, Not v2]]
v1 `implies` v2 = Formula $ Seq.fromList [Clause [Not v1, Merely v2]]
v `impliesSome` vs = Formula $ Seq.fromList [Clause (Not v : map Merely vs)]
--v `impliedBySome` vs = Formula [Clause (Merely v : map Not vs)]

emptyFormula = Formula Seq.empty

formulaSatisfied (Formula f) model = Fold.all (\(Clause c) -> any propositionTrue c) f
    where propositionTrue (Merely v) = model IM.! v
          propositionTrue (Not v) = not $ model IM.! v

-- Conversion of Formulas to DIMACS (CNF-SAT) formats.
toDIMACS :: (Int, Formula) -> String
toDIMACS (numVars, formula) =
    let cnf = toCNF formula
        numClauses = SAT.numClauses formula
    in ("p cnf " ++
        (show numVars) ++ " " ++
        (show numClauses) ++ "\n") ++
       (unlines $ map (unwords . (map show) . (++[0])) cnf)

toCNF :: Formula -> [[Int]]
toCNF (Formula clauses) = Fold.toList $ fmap (\(Clause props) -> map transformProposition props) clauses
    where transformProposition p =
              (if isNeg p then negate else id) $ propositionVar p

-- Show instances for Formula, Clause, and Proposition
instance Show Formula where
    show (Formula f) = "\nFormula{\n" ++ (concat $ intersperse " ^ \n" $ map show $ Fold.toList f) ++ "}"

instance Show Clause where
    show (Clause c) = "(" ++ (concat $ intersperse " v " $ map show c) ++ ")"

instance Show Proposition where
    show = show2
show2 (Merely v) = show v
show2 (Not v) = '-':(show v)

instance Arbitrary Formula where
    arbitrary = sized (\n -> (liftM (Formula . Seq.fromList)) (resize (round $ sqrt $ fromIntegral n) arbitrary))
    coarbitrary (Formula f) = coarbitrary $ Fold.toList f
instance Arbitrary Clause where
    arbitrary = sized (\n -> (liftM Clause) (resize (round $ sqrt $ fromIntegral n) arbitrary))
    coarbitrary (Clause c) = coarbitrary c

instance Arbitrary Proposition where
    arbitrary = do
      ctor <- elements [Merely, Not]
      var <- arbitrary
      return $ ctor var
    coarbitrary (Merely p) = variant 1 . coarbitrary p
    coarbitrary (Not p) = variant 2 . coarbitrary p
