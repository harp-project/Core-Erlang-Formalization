Require Coq.extraction.Extraction.
Extraction Language Haskell.

From CoreErlang.Interpreter Require Import StepFunctions.


Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellString.

Extraction "extr_test.hs" step_func processLocalStepFunc interProcessStepFunc.
