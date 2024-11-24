From CoreErlang.Eq.BsFs Require Export B20EraseNamesLemmas.

Import BigStep.

(* STRUCTURE:
* Create
  - create_result_values
  - create_result_vtuple
  - create_result_vmap
*)












Section Create.



  Lemma create_result_values :
    forall v vl,
      create_result IValues ([] ++ v :: vl) []
    = Some (RValSeq (v :: vl), []).
  Proof.
   trv.
  Qed.



  Lemma create_result_vtuple :
    forall v vl,
      create_result ITuple ([] ++ v :: vl) []
    = Some (RValSeq [Syntax.VTuple (v :: vl)], []).
  Proof.
   trv.
  Qed.



  Lemma create_result_vmap :
    forall v1 v2 vll,
      create_result IMap ([v1] ++ v2 :: (flatten_list vll)) []
    = Some (RValSeq [Syntax.VMap (make_val_map ((v1, v2) :: vll))], []).
  Proof.
    (* #1 Simply: intro/simpl/f_equal *)
    itr.
    smp.
    f_equal.
    (* Rewrite Lemma: rewrite *)
    bwr - flatten_deflatten.
  Qed.



End Create.