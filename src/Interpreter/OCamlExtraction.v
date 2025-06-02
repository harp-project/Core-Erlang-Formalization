Require Coq.extraction.Extraction.
Extraction Language OCaml.

From CoreErlang.Interpreter Require Import StepFunctions.
From CoreErlang.Interpreter Require Import Scheduler.
From CoreErlang.Interpreter.ExampleASTs.coqAST Require Import decode fib huff length length2 length_c length_u life life2 life3 mean_nnc nrev qsort ring smith stable stable2 tak zip_nnc life4.

Definition examplePrograms : list Redex :=
[RExp testdecode; RExp testfib; RExp testhuff; RExp testlength; RExp testlength2;
 RExp testlength_c; RExp testlength_u; RExp testlife; RExp testlife2; RExp testlife3;
 RExp testmean_nnc; RExp testnrev; RExp testqsort; RExp testring; RExp testsmith; 
 RExp teststable; RExp teststable2; RExp testtak; RExp testzip_nnc; RExp testlife4].

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlZInt.
Require Import ExtrOcamlString.

Extract Inlined Constant pool_singleton => "(PIDMap.singleton)".
Extract Inlined Constant pool_lookup => "(PIDMap.find_opt)".
Extract Inlined Constant pool_insert => "(PIDMap.add)".
Extract Inlined Constant pool_toList => "(PIDMap.bindings)".

Extract Inlined Constant ether_empty => "(PIDPIDMap.empty)".
Extract Inlined Constant ether_lookup => "(PIDPIDMap.find_opt)".
Extract Inlined Constant ether_insert => "(PIDPIDMap.add)".
Extract Inlined Constant ether_toList => "(PIDPIDMap.bindings)".
Extract Inlined Constant ether_domain_toList => "(fun eth -> List.map fst (PIDPIDMap.bindings eth))".

Extract Inlined Constant Val_eqb_strict => "(=)".
Extract Inlined Constant Exp_eqb_strict => "(=)".
Extract Inlined Constant Pos.succ => "(Stdlib.Int.succ)".

Extraction "OCamlSrc/CoqExtraction.ml"
  nodeSimpleStep interProcessStepFuncFast makeInitialNodeConf ex_Process 
  isDead isTotallyDead etherNonEmpty
  currPID nextConf newConfByAction delCurrFromConf
  examplePrograms.