Require Coq.extraction.Extraction.
Extraction Language Haskell.

From CoreErlang.Interpreter Require Import StepFunctions.
From CoreErlang.Interpreter Require Import Scheduler.
From CoreErlang.Interpreter.ExampleASTs.coqAST Require Import decode fib huff length length2 length_c length_u life life2 life3 mean_nnc nrev qsort ring smith stable stable2 tak zip_nnc life4.

Definition examplePrograms : list Redex :=
[RExp testdecode; RExp testfib; RExp testhuff; RExp testlength; RExp testlength2;
 RExp testlength_c; RExp testlength_u; RExp testlife; RExp testlife2; RExp testlife3;
 RExp testmean_nnc; RExp testnrev; RExp testqsort; RExp testring; RExp testsmith; 
 RExp teststable; RExp teststable2; RExp testtak; RExp testzip_nnc; RExp testlife4].

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

(* Operations for extracting gsets and gmaps into HashSets and HashMaps *)
Extract Inlined Constant fold_right => "Prelude.foldr".
Extract Inlined Constant dead_lookup => "Data.HashMap.Strict.lookup".
Extract Inlined Constant dead_delete => "Data.HashMap.Strict.delete".
Extract Inlined Constant dead_domain => "Data.HashMap.Strict.keysSet".
Extract Inlined Constant dead_size => "(\dead -> Prelude.toInteger (Data.HashMap.Strict.size dead))".
Extract Inlined Constant pids_set_to_map => 
  "(\v s -> Data.HashMap.Strict.fromList [(k, v) | k <- Data.HashSet.toList s])".
Extract Inlined Constant pids_insert => "Data.HashSet.insert".
Extract Inlined Constant pids_delete => "Data.HashSet.delete".
Extract Inlined Constant pids_empty => "Data.HashSet.empty".
Extract Inlined Constant pids_member => "Data.HashSet.member".
Extract Inlined Constant pids_union => "Data.HashSet.union".
Extract Inlined Constant pids_singleton => "Data.HashSet.singleton".
Extract Inlined Constant pids_toList => "Data.HashSet.toList".
Extract Inlined Constant pids_fresh =>
  "(\pids -> if Data.HashSet.null pids then 0 else (Prelude.maximum (Data.HashSet.toList pids) Prelude.+ 1))".
Extract Inlined Constant pids_foldWithKey => "Data.HashMap.Strict.foldrWithKey'". (* note the apostrophy *)
Extract Inlined Constant pool_singleton => "Data.HashMap.Strict.singleton".
Extract Inlined Constant pool_lookup => "Data.HashMap.Strict.lookup".
Extract Inlined Constant pool_insert => "Data.HashMap.Strict.insert".
Extract Inlined Constant pool_toList => "Data.HashMap.Strict.toList".
Extract Inlined Constant pool_domain => "Data.HashMap.Strict.keysSet".
Extract Inlined Constant ether_empty => "Data.HashMap.Strict.empty".
Extract Inlined Constant ether_lookup => "Data.HashMap.Strict.lookup".
Extract Inlined Constant ether_insert => "Data.HashMap.Strict.insert".
Extract Inlined Constant ether_toList => "Data.HashMap.Strict.toList".
Extract Inlined Constant ether_domain_toList => "(\eth -> Data.HashSet.toList (Data.HashMap.Strict.keysSet eth))".

Extract Inlined Constant Val_eqb_strict => "(Prelude.==)".
Extract Inlined Constant Exp_eqb_strict => "(Prelude.==)".

Extract Inlined Constant map => "(Prelude.map)".

Extraction "HaskellSrc/exe/CoqExtraction.hs"
  nodeTauFirstStep makeInitialNode currentProcessList
  nodeSimpleStep interProcessStepFuncFast makeInitialNodeConf ex_Process 
  isDead isTotallyDead etherNonEmpty
  currPID nextConf newConfByAction delCurrFromConf
  examplePrograms.