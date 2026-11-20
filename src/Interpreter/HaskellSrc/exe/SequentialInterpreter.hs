module SequentialInterpreter where

-- Evaluates the sequential semantics only, by iterating the extracted
-- `sequentialStepFunc`. For a program `prog` and a step limit `n`, use
-- `run n [] (RExp (EExp prog))`.

import RocqExtraction (Redex(..), Exception, ValSeq, FrameStack, sequentialStepFunc)

data Outcome
  = Value ValSeq              -- final configuration ([], RValSeq vs)
  | Exc Exception             -- uncaught exception ([], RExc e)
  | Stuck FrameStack Redex    -- no step is possible in a non-final configuration
  | OutOfFuel FrameStack Redex -- the step limit was reached
  deriving Show

run :: Integer -> FrameStack -> Redex -> Outcome
run _ [] (RValSeq vs) = Value vs
run _ [] (RExc e)     = Exc e
run n fs r
  | n <= 0    = OutOfFuel fs r
  | otherwise =
      case sequentialStepFunc fs r of
        Nothing        -> Stuck fs r
        Just (fs', r') -> run (n - 1) fs' r'
