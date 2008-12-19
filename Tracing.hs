module Tracing where

import Debug.Trace

debug = True
myTrace = if debug then trace else flip const
traceIt s = myTrace ("TRACEIT:" ++ show s) s
