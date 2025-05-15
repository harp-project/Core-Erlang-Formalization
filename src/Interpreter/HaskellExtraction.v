Require Coq.extraction.Extraction.
Extraction Language Haskell.

From CoreErlang.Interpreter Require Import StepFunctions.
From CoreErlang.Interpreter Require Import Scheduler.
From CoreErlang.Interpreter.ExampleASTs.coqAST Require Import decode fib huff length length_c length_u life mean_nnc nrev qsort ring smith stable tak zip_nnc.

Definition examplePrograms : list Redex :=
[RExp testdecode; RExp testfib; RExp testhuff; RExp testlength;
 RExp testlength_c; RExp testlength_u; RExp testlife; RExp testmean_nnc;
 RExp testnrev; RExp testqsort; RExp testring; RExp testsmith; RExp testtak; RExp testzip_nnc].

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellString.

Extraction "HaskellCode/CoqExtraction.hs"
  nodeSimpleStep makeInitialNodeConf ex_Process 
  isDead isTotallyDead etherNonEmpty
  currPID nextConf newConfByAction delCurrFromConf
  examplePrograms.
