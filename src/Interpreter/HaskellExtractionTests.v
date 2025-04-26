Require Coq.extraction.Extraction.
Extraction Language Haskell.

From CoreErlang.Interpreter Require Import StepFunctions.
From CoreErlang.Interpreter Require Import Tests.

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellString.

Extraction "HaskellTesting/ExtractionTests.hs" step_func processLocalStepFunc positive_tests negative_tests.
