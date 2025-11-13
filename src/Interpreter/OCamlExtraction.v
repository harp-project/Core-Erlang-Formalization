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

(**
   This is a VERY dirty trick, and it's only left here because the OCaml Interpreter is essentially 
   deprecated. The reason for this is as follows: in the usedPIDsProc function (ProcessSemantics.v),
   two methods are given for the PIDs of dead processes. A new version of this function was created 
   in InterpreterAux, for the wrapper functions of map and set operation.
   
   In the Haskell version, all maps and sets were swapped to Haskell's HashMaps and HashSets (see
   HaskellExtraction.v). However, in the OCaml version, only the Ether and the ProcessPool was swapped.
   The reason for this is that there is no general way to swap every "intermediate" form, such as a
   set of PIDs. This is because of the type annotations that the extraction adds. The syntax just makes
   it (probably?) impossible.
   
   When the new usedPIDsProc function was initially defined in InterpreterAux.v, the old version method 
   of dead process PIDs was used:

      "map_fold (fun k x acc => {[k]} ∪ usedPIDsVal x ∪ acc) ∅ links"

   This works during the extraction to OCaml. However, it could not be proven that this behaves
   equivalently to the new method, defined just below it:

      "@union_set _ _ _ gsetPID_elem_of _ (map_to_set (fun k x => {[k]} ∪ usedPIDsVal x) links)"

   Therefore, this new version was used in the wrapper function for usedPIDsProc. This is no problem when
   we're extracting into Haskell, however it is a problem for OCaml. A wrapper function inside this
   (pids_map_set_union) is extracted into OCaml and it does NOT get replaced. This pids_map_set_union
   function calls "gsetPID_elem_of", and ocamlc seems to not understand the type declaration of that.
   This is either a bug with the extraction to OCaml, or a bug inside ocamlc itself.
   
   The fix is very dirty. We replace pids_map_set_union with the old version of the function. However,
   the interfaces are not compatible (see the type declarations for pids_map_set_union and pids_foldWithKey),
   so we need a lambda that throws away the old function, but keeps the links. So we are essentially
   using the old version of the function. Node that during the extraction, we need to manually add
   pids_foldWithKey, as it does not get extracted on it's own when it's in a manual replacement.
*)
Extract Inlined Constant pids_map_set_union =>
  "(fun _ l -> pids_foldWithKey (fun k x acc -> 
    pids_union (pids_insert k (usedPIDsValNew x)) acc) pids_empty l)".

Extraction "OCamlSrc/CoqExtraction.ml"
  pids_foldWithKey  (* To see why this is here, read the comment for "pids_map_set_union" above. *)
  nodeSimpleStep interProcessStepFuncFast makeInitialNodeConf ex_Process 
  isDead isTotallyDead etherNonEmpty
  currPID nextConf newConfByAction delCurrFromConf
  examplePrograms.