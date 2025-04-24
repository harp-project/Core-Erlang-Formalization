Require Coq.extraction.Extraction.
Extraction Language Haskell.

From CoreErlang.Interpreter Require Import StepFunctions.

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellString.

Definition ex_set_1 : gset nat := {[1]}.
Definition ex_set_2 : gset nat := {[2]}.
Definition ex_set_3 : gset nat := {[1;2]}.

Extraction "extr_test.hs" step_func processLocalStepFunc ex_set_1 ex_set_2 ex_set_3.

Compute union ex_set_1 ex_set_2.
Compute ex_set_1 ∪ ex_set_2.
Compute ex_set_3.
