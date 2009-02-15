module Tracing
    (myTrace
    ,traceIt
    )
    where

import Debug.Trace

debugLevel = 0 :: Int
myTrace :: Int -> String -> a -> a
myTrace level = if level <= debugLevel then trace else flip const
traceIt s = myTrace 1 ("TRACEIT:" ++ show s) s
