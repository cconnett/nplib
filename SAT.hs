{-# OPTIONS -fglasgow-exts -fno-monomorphism-restriction #-}
module SAT where

import qualified Data.IntMap as IM
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
import Random
import Foreign (unsafePerformIO)
    
import Debug.Trace

-- Formulas are conjunctions of Clauses, Clauses are disjuntions of Propositions.
data Formula = Formula [Clause]
               deriving (Eq, Ord)
                     
data Clause = Clause [Proposition]
              deriving (Eq, Ord)
data Proposition = Merely !Var
                 | Not !Var
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

fromClause (Clause c) = c
fromFormula (Formula f) = f

conjoin formulas = Formula $ concatMap fromFormula formulas

makeTrue v = Formula [Clause [Merely v]]
makeFalse v = Formula [Clause [Not v]]
makeEquivalent v1 v2 = Formula [Clause [Not v1, Merely v2], Clause [Merely v1, Not v2]]
makeOpposed v1 v2 = Formula [Clause [Merely v1, Merely v2], Clause [Not v1, Not v2]]
v1 `implies` v2 = Formula [Clause [Not v1, Merely v2]]
v `impliesSome` vs = Formula [Clause (Not v : map Merely vs)]
--v `impliedBySome` vs = Formula [Clause (Merely v : map Not vs)]

emptyFormula = Formula []

formulaSatisfied (Formula f) answers = all (\(Clause c) -> any propositionTrue c) f
    where propositionTrue (Merely v) = answers IM.! v
          propositionTrue (Not v) = not $ answers IM.! v

-- Show instances for Constraint and helper types
instance Show Formula where
    show (Formula f) = "\nFormula{\n" ++ (concat $ intersperse " ^ \n" $ map show f) ++ "}"

instance Show Clause where
    show (Clause c) = "(" ++ (concat $ intersperse " v " $ map show c) ++ ")"

instance Show Proposition where
    show = show2
show2 (Merely v) = show v
show2 (Not v) = '-':(show v)

instance Arbitrary Formula where
    arbitrary = sized (\n -> (liftM Formula) (resize (round $ sqrt $ fromIntegral n) arbitrary))
    coarbitrary (Formula f) = coarbitrary f
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
