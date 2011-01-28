{-# OPTIONS -fglasgow-exts #-}

-- The primary convenience type for non-deterministic programming
-- provided by nplib is a representation of a non-deterministic
-- integer.  A non-deterministic integer is represented in a sat
-- formula by a list of variables in a formula.  Each variable
-- represents one bit of the integer.  When the formula is solved by a
-- sat solver and the variables assigned truth values, the truth
-- values of each variable determine the value of the
-- non-deterministic integer.  For example, if an integer has the list
-- of variables [1,2,3,4,5,6,7,8], and the satisfying assignment
-- generated by the sat solver assigns them the truth values [False,
-- False, True, True, False, True, True, True] respectively (leftmost
-- variables are most significant), then the integer can be
-- interpreted to have value 00110111 in base 2, and the value 55 in
-- base 10.
--
-- Currently there is no explicit differentiation between signed and
-- unsigned numbers.  Reductions constructed by this library
-- performing arithmetic on non-deterministic integers will respect
-- using two's complement representation for negative values.  That
-- is, if known negative values are represented in two's complement,
-- the assignments to the unknowns will be correct if interpreted as
-- two's complement.

module NInteger
    (NInt8
    ,NInt16
    ,NInt32
    ,NInt64

    ,NWord8
    ,NWord16
    ,NWord32
    ,NWord64

    ,NInteger
    ,newNInteger

    ,NVar
    ,toVars
    ,fromVars
    ,new

    ,NIntegral
    ,NInteger.fromInteger
    ,extendTo
    ,fromNIntegral
    ,width

    ,equal
    ,notEqual
    ,leq
    ,lt
    ,geq
    ,gt

    ,add
    ,sub
    ,negate
    ,shiftL
    ,shiftR
    ,ashiftR
    ,nsum
    ,mul1bit
    ,mul

    ,prop_asSignedInteger
    ,prop_asUnsignedInteger
    )
    where

import NPLib
import SAT
import Embeddings

import Prelude hiding (negate)
import Control.Monad
import Control.Arrow
import Data.Bits ((.|.))
import qualified Data.Bits as Bits
import Data.Word
import Data.Int
import Test.QuickCheck

import Tracing

newtype NInt8  = NInt8  [Var] deriving (Show, Read)
newtype NInt16 = NInt16 [Var] deriving (Show, Read)
newtype NInt32 = NInt32 [Var] deriving (Show, Read)
newtype NInt64 = NInt64 [Var] deriving (Show, Read)
newtype NInteger = NInteger [Var] deriving (Show, Read)

newtype NWord8  = NWord8  [Var] deriving (Show, Read)
newtype NWord16 = NWord16 [Var] deriving (Show, Read)
newtype NWord32 = NWord32 [Var] deriving (Show, Read)
newtype NWord64 = NWord64 [Var] deriving (Show, Read)

-- NVar and Interpret instances for signed types
instance NVar NInt8 where
    toVars (NInt8 vars) = vars
    fromVars = NInt8 . (makeCorrectLength arithmeticStyle 8)
    new = fixedWidthNew 8
instance (Integral i) => Interpret NInt8 i where
    interpret v = fromIntegral . asSignedInteger . lookupVarAnswers v

instance NVar NInt16 where
    toVars (NInt16 vars) = vars
    fromVars = NInt16 . (makeCorrectLength arithmeticStyle 16)
    new = fixedWidthNew 16
instance (Integral i) => Interpret NInt16 i where
    interpret v = fromIntegral . asSignedInteger . lookupVarAnswers v

instance NVar NInt32 where
    toVars (NInt32 vars) = vars
    fromVars = NInt32 . (makeCorrectLength arithmeticStyle 32)
    new = fixedWidthNew 32
instance (Integral i) => Interpret NInt32 i where
    interpret v = fromIntegral . asSignedInteger . lookupVarAnswers v

instance NVar NInt64 where
    toVars (NInt64 vars) = vars
    fromVars = NInt64 . (makeCorrectLength arithmeticStyle 64)
    new = fixedWidthNew 64
instance (Integral i) => Interpret NInt64 i where
    interpret v = fromIntegral . asSignedInteger . lookupVarAnswers v

instance NVar NInteger where
    toVars (NInteger vars) = vars
    fromVars = NInteger
    new = error "Use newNInteger to create an NInteger with a specific width"
instance (Integral i) => Interpret NInteger i where
    interpret v = fromIntegral . asSignedInteger . lookupVarAnswers v

fixedWidthNew width = do
  vars <- takeSatVars width
  return $ fromVars vars
newNInteger :: Int -> NProgramComputation NInteger
newNInteger  = fixedWidthNew

asSignedInteger :: [Bool] -> Integer
asSignedInteger bools =
    let signBit = head (myTrace 3 (concatMap (\b -> if b then "1" else "0") bools) bools)
        magnitude = asUnsignedInteger (tail bools)
    in magnitude - (if signBit then Bits.bit (length bools - 1) else 0)

asUnsignedInteger :: [Bool] -> Integer
asUnsignedInteger bools = foldl (.|.) 0 (map Bits.bit $ trueIndices (myTrace 4 (concatMap (\b -> if b then "1" else "0") bools) bools))
trueIndices bools = map fst $ filter snd $ zip [0..] (reverse bools)

prop_asSignedInteger a =
    a == asSignedInteger (map (Bits.testBit a) [31,30..0])
prop_asUnsignedInteger (a::Integer) = a > 0 ==>
    a == fromIntegral (asUnsignedInteger (map (Bits.testBit a) [31,30..0]))

-- NVar and Interpret instances for unsigned types
instance NVar NWord8 where
    toVars (NWord8 vars) = (makeCorrectLength logicalStyle 9 vars)
    fromVars = NWord8 . (makeCorrectLength logicalStyle 8)
    new = fixedWidthNew 8
instance (Integral i) => Interpret NWord8 i where
    interpret v = fromIntegral . asUnsignedInteger . lookupVarAnswers v

instance NVar NWord16 where
    toVars (NWord16 vars) = (makeCorrectLength logicalStyle 17 vars)
    fromVars = NWord16 . (makeCorrectLength logicalStyle 16)
    new = fixedWidthNew 16
instance (Integral i) => Interpret NWord16 i where
    interpret v = fromIntegral . asUnsignedInteger . lookupVarAnswers v

instance NVar NWord32 where
    toVars (NWord32 vars) = (makeCorrectLength logicalStyle 33 vars)
    fromVars = NWord32 . (makeCorrectLength logicalStyle 32)
    new = fixedWidthNew 32
instance (Integral i) => Interpret NWord32 i where
    interpret v = fromIntegral . asUnsignedInteger . lookupVarAnswers v

instance NVar NWord64 where
    toVars (NWord64 vars) = (makeCorrectLength logicalStyle 65 vars)
    fromVars = NWord64 . (makeCorrectLength logicalStyle 64)
    new = fixedWidthNew 64
instance (Integral i) => Interpret NWord64 i where
    interpret v = fromIntegral . asUnsignedInteger . lookupVarAnswers v

-- The NIntegral class represents non-deterministic Integral types
class (NVar k) => NIntegral k where
    fromInteger :: Integer -> k
    extendTo :: Int -> k -> [Var]
    fromNIntegral :: (NIntegral j) => k -> j
    fromNIntegral = fromVars . toVars


m, mPos, mNeg :: (Integral a) => a -> Int
m a
    | a == 0 = 1
    | a > 0 = mPos a
    | a < 0 = mNeg (abs a)
mPos = (+1) . floor . (logBase 2) . fromIntegral
mNeg = (+0) . ceiling . (logBase 2) . fromIntegral

width :: (NVar v) => v -> Int
width = length . toVars

-- Produces an NIntegral representing the value in the Integer a,
-- using the fewest bits possible for a signed represenation.  A
-- positive value will have a 0 in the top-most (sign) bit.
minWidthFromInteger a =
    let width = m a + 1 in
    fixedWidthFromInteger width a

fixedWidthFromInteger :: forall k. (NIntegral k) => Int -> Integer -> k
fixedWidthFromInteger width a = fromVars $
    map (\i -> if Bits.testBit a i then true else false)
            [width - 1, width - 2 .. 0]


extendToStyle style numBits vars =
    replicate (numBits - length vars) (style (head vars)) ++ vars
logicalStyle = const false
arithmeticStyle = id

trimTo numBits vars = drop (length vars - numBits) vars

makeCorrectLength style numBits vars =
    trimTo numBits $ extendToStyle style numBits vars

instance NIntegral NInt8 where
    fromInteger = fixedWidthFromInteger 8
    extendTo numBits = (extendToStyle arithmeticStyle numBits) . toVars
instance NIntegral NInt16 where
    fromInteger = fixedWidthFromInteger 16
    extendTo numBits = (extendToStyle arithmeticStyle numBits) . toVars
instance NIntegral NInt32 where
    fromInteger = fixedWidthFromInteger 32
    extendTo numBits = (extendToStyle arithmeticStyle numBits) . toVars
instance NIntegral NInt64 where
    fromInteger = fixedWidthFromInteger 64
    extendTo numBits = (extendToStyle arithmeticStyle numBits) . toVars
instance NIntegral NInteger where
    fromInteger = minWidthFromInteger
    extendTo numBits = (extendToStyle arithmeticStyle numBits) . toVars

instance NIntegral Var where
    fromInteger = fixedWidthFromInteger 1
    extendTo numBits = (extendToStyle logicalStyle numBits) . toVars
    -- fromNIntegral could produce a signed type, so we need to add a
    -- leading false bit so that a True Var becomes +1, not -1.
    fromNIntegral var = fromVars [false, var]
instance NIntegral NWord8 where
    fromInteger = fixedWidthFromInteger 8
    extendTo numBits = (extendToStyle logicalStyle numBits) . toVars
instance NIntegral NWord16 where
    fromInteger = fixedWidthFromInteger 16
    extendTo numBits = (extendToStyle logicalStyle numBits) . toVars
instance NIntegral NWord32 where
    fromInteger = fixedWidthFromInteger 32
    extendTo numBits = (extendToStyle logicalStyle numBits) . toVars
instance NIntegral NWord64 where
    fromInteger = fixedWidthFromInteger 64
    extendTo numBits = (extendToStyle logicalStyle numBits) . toVars

{-
testBit :: k -> Int -> Var
k `testBit` i = reverse (toVars k) !! i
-}

extendToCommonWidth :: (NIntegral k) => [k] -> [[Var]]
extendToCommonWidth as =
    let commonWidth = maximum $ map width as
    in map (extendTo commonWidth) as

equal, notEqual, leq, lt, geq, gt :: (NIntegral k) => k -> k -> NProgramComputation Formula
a `equal` b =
    let [a', b'] = extendToCommonWidth [a, b] in
    return $ conjoinAll $ map (uncurry makeEquivalent) (zip a' b')

a `leq` b = do
  let [a', b'] = extendToCommonWidth [a, b]
  let aBits = tail a'
  let bBits = tail b'
  let aSign = head a'
  let bSign = head b'
  correctingTerms <- embedFormulas [fromListForm [[Not aj], [Merely bj]]
                                        | (aj, bj) <- zip aBits bBits]
  return $ --trace (show (aSign, aBits, bSign, bBits)) $
            fromListForm $ concat $
             [[Merely aSign, Not bSign]] :
            [[[Merely aSign, Merely bSign, Not ak, Merely bk] ++ map Merely (take k' correctingTerms),
              [Not aSign, Not bSign, Not ak, Merely bk] ++ map Merely (take k' correctingTerms)]
             | (k', ak, bk) <- zip3 [0..] aBits bBits]

a `notEqual` b = equal a b >>= negateFormula
a `lt` b = do
  leq' <- a `leq` b
  neq' <- a `notEqual` b
  return $ conjoin leq' neq'
a `geq` b = b `leq` a
a `gt` b = b `lt` a

add :: NIntegral k => k -> k -> NProgramComputation k
add a b = do
  let [a', b'] = extendToCommonWidth [a, b]
  let theWidth = length a' -- == width b' == width c'
  c <- fixedWidthNew theWidth
  let c' = toVars $ c `asTypeOf` a
  let numCarryBits = theWidth
  carryBits <- takeSatVars numCarryBits
  let aBit k = Merely $ a' !! (theWidth - k - 1)
  let bBit k = Merely $ b' !! (theWidth - k - 1)
  let cBit k = Merely $ c' !! (theWidth - k - 1)
  let carryBit k = Merely $ carryBits !! (numCarryBits - k)
  let set0thResult = fromListForm
       [[      cBit 0,       aBit 0, neg $ bBit 0],
        [      cBit 0, neg $ aBit 0,       bBit 0],
        [neg $ cBit 0, neg $ aBit 0, neg $ bBit 0],
        [neg $ cBit 0,       aBit 0,       bBit 0]]
  let set1stCarry = fromListForm
       [[      carryBit 1, neg $ aBit 0, neg $ bBit 0],
        [neg $ carryBit 1,       aBit 0              ],
        [neg $ carryBit 1,                     bBit 0]]
  let setKthResult k = fromListForm
       [[      cBit k, neg $ aBit k,       bBit k,       carryBit k],
        [      cBit k, neg $ aBit k, neg $ bBit k, neg $ carryBit k],
        [      cBit k,       aBit k, neg $ bBit k,       carryBit k],
        [      cBit k,       aBit k,       bBit k, neg $ carryBit k],
        [neg $ cBit k,       aBit k,       bBit k,       carryBit k],
        [neg $ cBit k,       aBit k, neg $ bBit k, neg $ carryBit k],
        [neg $ cBit k, neg $ aBit k, neg $ bBit k,       carryBit k],
        [neg $ cBit k, neg $ aBit k,       bBit k, neg $ carryBit k]]
  let setKthCarry k = fromListForm
       [[      carryBit k, neg $ aBit (k-1), neg $ bBit (k-1)                      ],
        [      carryBit k, neg $ aBit (k-1),                   neg $ carryBit (k-1)],
        [      carryBit k,                   neg $ bBit (k-1), neg $ carryBit (k-1)],
        [neg $ carryBit k,       aBit (k-1),       bBit (k-1)                      ],
        [neg $ carryBit k,       aBit (k-1),                         carryBit (k-1)],
        [neg $ carryBit k,                         bBit (k-1),       carryBit (k-1)]]
  assertAll (set0thResult : set1stCarry :
             map setKthResult [1 .. theWidth - 1] ++
             map setKthCarry [2 .. theWidth])
  return (fromVars $ head carryBits : c')

-- c == a - b <=> a == b + c
sub a b = do
  c <- new
  a' <- add b c
  equal a a' >>= assert
  return c
-- Take the two's complement of x
negate :: forall k. (NIntegral k) => k -> NProgramComputation k
negate x = do
  (onesComplementX::k) <- new
  forM_ (zip (toVars x) (toVars onesComplementX)) $ \(v, ocv) ->
      assert $ makeOpposed v ocv
  add onesComplementX (NInteger.fromInteger 1)

-- Logical shift left and right
shiftL, shiftR, ashiftR :: NIntegral k => k -> Int -> k
x `shiftL` i = fromVars . (++ replicate i false) . toVars $ x
x `shiftR` i = fromVars . (replicate i false ++) . toVars $ x
-- Arithmetic shift right (sign bit extension)
x `ashiftR` i =
  let vars = toVars x
  in fromVars . (replicate i (head vars) ++) . toVars $ x

nsum :: (NIntegral k) => [k] -> NProgramComputation NInteger
nsum summands = nsum' (map fromNIntegral summands :: [NInteger])
nsum' [] = return $ NInteger.fromInteger 0
nsum' [a] = return $ fromNIntegral a
nsum' summands = do
  frontSum <- nsum frontHalf
  backSum <- nsum backHalf
  sum <- add frontSum backSum
  return $ {-myTrace 3 (show $ (length $ toVars sum, map (length . toVars) frontHalf, map (length . toVars) backHalf))-} sum
  where frontHalf = take half summands
        backHalf = drop half summands
        half = (length summands) `div` 2

mul1bit :: NIntegral k => k -> Var -> NProgramComputation k
mul1bit a bit = do
  outVars <- takeSatVars (width a)
  forM_ (zip (toVars a) outVars) $ \(ai, oi) ->
      assert $ fromListForm [[Not ai, Not bit, Merely oi],
                             [Not oi, Merely ai],
                             [Not oi, Merely bit]]
  return (fromVars outVars)

mul :: (NIntegral k) => k -> k -> NProgramComputation k
mul a b = do
  partialProducts :: [NInteger] <- liftM (map fromNIntegral) $ mapM (mul1bit a) (reverse $ toVars b)
  result <- nsum $ map (uncurry shiftL) $ zip partialProducts [0..]
  return $ fromNIntegral result
