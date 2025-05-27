Require Coq.extraction.Extraction.
Extraction Language Haskell.

From CoreErlang.Interpreter Require Import StepFunctions.
From CoreErlang.Interpreter Require Import Scheduler.
From CoreErlang.Interpreter.ExampleASTs.coqAST Require Import decode fib huff length length2 length_c length_u life life2 life3 mean_nnc nrev qsort ring smith stable stable2 tak zip_nnc.

Definition examplePrograms : list Redex :=
[RExp testdecode; RExp testfib; RExp testhuff; RExp testlength; RExp testlength2;
 RExp testlength_c; RExp testlength_u; RExp testlife; RExp testlife2; RExp testlife3;
 RExp testmean_nnc; RExp testnrev; RExp testqsort; RExp testring; RExp testsmith; 
 RExp teststable; RExp teststable2; RExp testtak; RExp testzip_nnc].

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellString.

Extract Inlined Constant Pos.succ => "(Prelude.+ 1)".
Extract Inlined Constant Pos.succ_of_nat => "(Prelude.+ 1)". (** doesn't work?? *)
Extract Inlined Constant fst => "Prelude.fst".
Extract Inlined Constant snd => "Prelude.snd".
Extract Inlined Constant uncurry => "Prelude.uncurry".
Extract Inlined Constant prod_rect => "Prelude.uncurry".
Extract Inlined Constant unit_rec => "Prelude.const".
Locate add.
Extract Inlined Constant Pos.add => "(Prelude.+)".

Extraction "HaskellCode/CoqExtraction.hs"
  nodeSimpleStep makeInitialNodeConf ex_Process 
  isDead isTotallyDead etherNonEmpty
  currPID nextConf newConfByAction delCurrFromConf
  examplePrograms.