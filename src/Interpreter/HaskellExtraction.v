Require Stdlib.extraction.Extraction.
Extraction Language Haskell.

From CoreErlang.Interpreter Require Import StepFunctions.
From CoreErlang.Interpreter Require Import Scheduler.

(* Basics of extraction into Haskell *)
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellString.
Extract Inductive comparison => "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].

Extract Inlined Constant app => "(Prelude.++)".
Extract Inlined Constant length => "(Data.List.genericLength)".

Extract Inlined Constant Pos.succ => "(Prelude.+ 1)".
Extract Inlined Constant Pos.of_succ_nat => "(Prelude.+ 1)".
Extract Inlined Constant Pos.mul => "(Prelude.*)".
Extract Inlined Constant Z.of_nat => "(Prelude.id)".
Extract Inlined Constant Z.abs => "(Prelude.abs)".
Extract Inlined Constant Z.leb => "(Prelude.<=)".
Extract Inlined Constant Z.ltb => "(Prelude.<)".

Extract Inlined Constant fst => "Prelude.fst".
Extract Inlined Constant snd => "Prelude.snd".
Extract Inlined Constant uncurry => "Prelude.uncurry".
Extract Inlined Constant prod_rect => "Prelude.uncurry".
Extract Inlined Constant unit_rec => "Prelude.const".
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
Extract Inlined Constant pids_map_set_union => "(\f m -> Data.HashSet.unions [f k v | (k, v) <- Data.HashMap.Strict.toList m])".
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

(* All these operations are equivalent to Haskell's in-built equality function,
   derived using the Eq typeclass in the preprocessing stage. *)
Extract Inlined Constant Z.eqb => "(Prelude.==)".
Extract Inlined Constant Pos.eqb => "(Prelude.==)".
Extract Inlined Constant Lit_beq => "(Prelude.==)".
Extract Inlined Constant Val_eqb_strict => "(Prelude.==)".
Extract Inlined Constant Exp_eqb_strict => "(Prelude.==)".
Extract Inlined Constant Signal_eqb_strict => "(Prelude.==)".

(** NOTE: `Z.quot` and `Z.rem` are not exactly the same as their Haskell counterparts,
          because in Haskell division by 0 gives an error, but in Coq
          it gives a constant zero. There are already extraction patterns
          like these for Z.div and Z.modulo in ExtrHaskellZNum (imported by
          ExtrHaskellZInteger). *)
Extract Constant Z.quot => "(\n m -> if m Prelude.== 0 then 0 else Prelude.quot n m)".
Extract Constant Z.rem => "(\n m -> if m Prelude.== 0 then 0 else Prelude.rem n m)".

Extract Inlined Constant map => "(Prelude.map)".
Extract Inlined Constant List.filter => "(Prelude.filter)".

(** NOTE: The following is a dirty trick. Coq's extraction mechanism is
          very conservative. Even when some functions get replaced by
          constants, some other functions that would have been needed had
          the original function been extracted without constant replacement
          get extracted as well. Ergo, some functions get extracted and never
          get used anywhere.
          
          The trick is to inline these functions, because since they don't
          get used anywhere, they will disappear. However, function can't be
          inlined without constant replacement, so an invalid name is given.
          This way, if an invalid name gets found in the extracted file,
          a function was removed when it wasn't supposed to. *)
Extract Inlined Constant Z.quotrem => "removed_Z_quotrem".
Extract Inlined Constant Z.div_eucl => "removed_Z_div_eucl".
Extract Inlined Constant Z.pos_div_eucl => "removed_Z_pos_div_eucl".
Extract Inlined Constant N.pos_div_eucl => "removed_N_pos_div_eucl".
Extract Inlined Constant N.eq_dec => "removed_N_eq_dec".
Extract Inlined Constant BinNat.N.eq_dec => "removed_BinNat_N_eq_dec".
Extract Inlined Constant Z.eq_dec => "removed_Z_eq_dec".
Extract Inlined Constant Nat.eq_dec => "removed_Nat_eq_dec".
Extract Inlined Constant Pos.eq_dec => "removed_Pos_eq_dec".
Extract Inlined Constant BinPos.Pos.eq_dec => "removed_BinPos_Pos_eq_dec".
Extract Inlined Constant Pos.dup => "removed_Pos_dup".
Extract Inlined Constant Pos.reverse => "removed_Pos_reverse".
Extract Inlined Constant Pos.reverse_go => "removed_Pos_reverse_go".
Extract Inlined Constant Pos.app => "removed_Pos_app".
Extract Inlined Constant Z.compare => "removed_Z_compare".
Extract Inlined Constant Z.pos_sub => "removed_Z_pos_sub".
Extract Inlined Constant Z.pred_double => "removed_Z_pred_double".
Extract Inlined Constant Z.succ_double => "removed_Z_succ_double".
Extract Inlined Constant Z.double => "removed_Z_double".
Extract Inlined Constant N.leb => "removed_N_leb".
Extract Inlined Constant N.sub => "removed_N_sub".
Extract Inlined Constant N.double => "removed_N_double".
Extract Inlined Constant N.succ_double => "removed_N_succ_double".
Extract Inlined Constant Pos.sub_mask => "removed_Pos_sub_mask".
Extract Inlined Constant Pos.sub_mask_carry => "removed_Pos_sub_mask_carry".
Extract Inlined Constant Pos.double_pred_mask => "removed_Pos_double_pred_mask".
Extract Inlined Constant Pos.double_mask => "removed_Pos_double_mask".
Extract Inlined Constant Pos.succ_double_mask => "removed_Pos_succ_double_mask".
Extract Inlined Constant Pos.pred => "removed_Pos_pred".
Extract Inlined Constant Pos.pred_double => "removed_Pos_pred_double".
Extract Inlined Constant Pos.add_carry => "removed_Pos_add_carry".

(** NOTE: Since maps and sets get replaced during the extraction process,
          these type definitions will be unused. This is also a dirty trick
          to remove them from the file. *)
Extract Inductive Pos.mask => "" ["" "" ""].
Extract Inductive gmap_dep => "" ["" ""].
Extract Inductive gmap_dep_ne => "" ["" "" "" "" "" "" ""].

(** NOTE: Because of Haskell's lazyness, substitutions need to be made
          strict to prevent space leaks. For this purpose, the deepseq was
          used. This constant replacement is here so that `deepseq` does not
          need to be inserted manually. Also note that deepseq requires a few
          typeclass definitions, which are inserted by the preprocessing script. *)
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

Extraction "HaskellSrc/exe/RocqExtraction.hs"
  substVal substNonVal
  nodeTauFirstStep makeInitialNode makeInitialConfig currentProcessList
  nodeSimpleStep interProcessStepFuncFast ex_Process 
  isDead isTotallyDead etherNonEmpty.