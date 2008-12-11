-- http://en.wikipedia.org/w/index.php?title=Booth's_multiplication_algorithm&oldid=231255993b
boothMul :: forall k. (Show k, NIntegral k) => k -> k -> k -> Stateful Formula
boothMul z x y
    | width x < width y = boothMul z y x
    | otherwise = do
        nx <- negate x
        let a = x `shiftL` ((width y) + 1)
            s = nx `shiftL` ((width y) + 1)
            p = y `shiftL` 1
            step = boothMulStep (a::k) (s::k)
        lastp' <- iterateM (width y) step p
        equal z lastp'

iterateM :: (Show a, Monad m) => Int -> (a -> m a) -> a -> m a
iterateM 0 f x = return x
iterateM n f x = f x >>= iterateM (n-1) f

boothMulStep :: (Show k, NIntegral k) => k -> k -> k -> Stateful k
boothMulStep a s p = do
  zero <- NInteger.fromInteger 0
  intermediate <- new (width p)
  final <- new (width p)
  intermediateIsA <- equal a intermediate
  intermediateIsS <- equal s intermediate
  useIntermediate <- equal final intermediate
  useZero <- equal final zero
  if' (testBit p 0)
      intermediateIsA
      intermediateIsS
  if' (makeEquivalent (testBit p 0) (testBit p 1))
      useIntermediate
      useZero
  p' <- new (width p)
  add p' p final >>= assert
  return (p' `ashiftR` 1)
