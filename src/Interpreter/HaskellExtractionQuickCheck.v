Require Stdlib.extraction.Extraction.
Extraction Language Haskell.

From CoreErlang.Interpreter Require Import StepFunctions.
From CoreErlang.Interpreter Require Import Scheduler.
From CoreErlang.Interpreter.ExampleASTs.rocqAST Require Import decode fib huff length length2 length_c length_u life life2 life3 mean_nnc nrev qsort ring smith stable stable2 tak zip_nnc life4 pmap length3.

Definition examplePrograms : list Redex :=
[RExp testdecode; RExp testfib; RExp testhuff; RExp testlength; RExp testlength2;
 RExp testlength_c; RExp testlength_u; RExp testlife; RExp testlife2; RExp testlife3;
 RExp testmean_nnc; RExp testnrev; RExp testqsort; RExp testring; RExp testsmith; 
 RExp teststable; RExp teststable2; RExp testtak; RExp testzip_nnc; RExp testlife4; RExp testpmap; RExp testlength3].

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellString.

Extract Inlined Constant app => "(Prelude.++)".
Extract Inlined Constant length => "(Data.List.genericLength)".

Extract Inlined Constant Pos.succ => "(Prelude.+ 1)".
Extract Inlined Constant Pos.succ_of_nat => "(Prelude.+ 1)". (** doesn't work?? *)
Extract Inlined Constant fst => "Prelude.fst".
Extract Inlined Constant snd => "Prelude.snd".
Extract Inlined Constant uncurry => "Prelude.uncurry".
Extract Inlined Constant prod_rect => "Prelude.uncurry".
Extract Inlined Constant unit_rec => "Prelude.const".
Extract Inlined Constant Pos.add => "(Prelude.+)".

(* Operations for extracting gsets and gmaps into HashSets and HashMaps *)
Extract Inlined Constant fold_right => "Prelude.foldr".
(*
Extract  Constant dead_lookup => "Data.HashMap.Strict.lookup".
Extract  Constant dead_delete => "Data.HashMap.Strict.delete".
Extract  Constant dead_domain => "Data.HashMap.Strict.keysSet".
Extract  Constant dead_size => "(\dead -> Prelude.toInteger (Data.HashMap.Strict.size dead))".
Extract  Constant pids_set_to_map => 
  "(\v s -> Data.HashMap.Strict.fromList [(k, v) | k <- Data.HashSet.toList s])".
Extract  Constant pids_insert => "Data.HashSet.insert".
Extract  Constant pids_delete => "Data.HashSet.delete".
Extract  Constant pids_empty => "Data.HashSet.empty".
Extract  Constant pids_member => "Data.HashSet.member".
Extract  Constant pids_union => "Data.HashSet.union".
Extract  Constant pids_singleton => "Data.HashSet.singleton".
Extract  Constant pids_toList => "Data.HashSet.toList".
Extract  Constant pids_fresh =>
  "(\pids -> if Data.HashSet.null pids then 0 else (Prelude.maximum (Data.HashSet.toList pids) Prelude.+ 1))".
Extract  Constant pids_foldWithKey => "Data.HashMap.Strict.foldrWithKey'". (* note the apostrophy *)
Extract  Constant pids_map_set_union => "(\f m -> Data.HashSet.unions [f k v | (k, v) <- Data.HashMap.Strict.toList m])".
Extract  Constant pool_singleton => "Data.HashMap.Strict.singleton".
Extract  Constant pool_lookup => "Data.HashMap.Strict.lookup".
Extract  Constant pool_insert => "Data.HashMap.Strict.insert".
Extract  Constant pool_toList => "Data.HashMap.Strict.toList".
Extract  Constant pool_domain => "Data.HashMap.Strict.keysSet".
Extract  Constant ether_empty => "Data.HashMap.Strict.empty".
Extract  Constant ether_lookup => "Data.HashMap.Strict.lookup".
Extract  Constant ether_insert => "Data.HashMap.Strict.insert".
Extract  Constant ether_toList => "Data.HashMap.Strict.toList".
Extract  Constant ether_domain_toList => "(\eth -> Data.HashSet.toList (Data.HashMap.Strict.keysSet eth))".
*)

Extract Inlined Constant Val_eqb_strict => "(Prelude.==)".
Extract Inlined Constant Exp_eqb_strict => "(Prelude.==)".
Extract Inlined Constant Signal_eqb_strict => "(Prelude.==)".

Extract Inlined Constant map => "(Prelude.map)".

Extract Constant subst => 
"
  (\_UU03be_ base ->
    case base of {
     VVal v -> 
        let v' = (substVal _UU03be_ v)
        in v' `deepseq` VVal v';
     EExp e -> 
        let e' = (substNonVal _UU03be_ e)
        in e' `deepseq` EExp e'})
".

Extraction "HaskellSrc/QuickCheck/RocqExtractionRaw.hs"
  substVal substNonVal
  nodeTauFirstStep makeInitialNode makeInitialConfig currentProcessList
  nodeSimpleStep interProcessStepFuncFast ex_Process 
  isDead isTotallyDead etherNonEmpty.