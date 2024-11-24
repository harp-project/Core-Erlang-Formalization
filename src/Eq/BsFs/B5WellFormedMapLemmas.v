From CoreErlang.Eq.BsFs Require Export B4WellFormedMapDefinitions.

Import SubstSemantics.

(* STRUCTURE:
* Induction
  - fs_wfm_vcons
  - fs_wfm_vtuple
  - fs_wfm_vmap
* Transform
  - fs_wfm_val_to_result
  - fs_wfm_valseq_to_result
  - fs_wfm_exception_to_result
  - fs_wfm_val_to_forall
*)












Section Induction.



  Theorem fs_wfm_vcons :
    forall v1 v2,
        Forall fs_wfm_val [VCons v1 v2]
    ->  Forall fs_wfm_val [v1]
    /\  Forall fs_wfm_val [v2].
  Proof.
    (* #1 Destruct Foralls: intro/inversion *)
    itr - v1 v2 HForall.
    ivc - HForall as Hv1v2: H1 / H2.
    (* #2 Destruct & Split: destruct/split/auto *)
    des - Hv1v2 as [Hv1 Hv2].
    spl; ato.
  Qed.



  Theorem fs_wfm_vtuple :
    forall v vl,
        Forall fs_wfm_val [VTuple (v :: vl)]
    ->  Forall fs_wfm_val [v]
    /\  Forall fs_wfm_val [VTuple vl].
  Proof.
    (* #1 Destruct Foralls: intro/inversion *)
    itr - v vl HForall.
    ivc - HForall as Hvvl: H1 / H2.
    (* #2 Destruct & Split: destruct/split/auto *)
    des - Hvvl as [Hv Hvl].
    spl; ato.
  Qed.



  Theorem fs_wfm_vmap :
    forall v1 v2 vl,
        Forall fs_wfm_val [VMap ((v1, v2) :: vl)]
    ->  Forall fs_wfm_val [v1]
    /\  Forall fs_wfm_val [v2]
    /\  Forall fs_wfm_val [VMap vl].
  Proof.
    (* #1 Destruct Foralls: intro/inversion *)
    itr - v1 v2 vl HForall.
    ivc - HForall as Hv1v2vl: H1 / H2.
    (* #2 Destruct & Split: destruct/split/constructor/auto *)
    des - Hv1v2vl as [Hmake [[Hv1 Hv2] Hvl]].
    do 4 (spl + cns; ato).
    (* #3 Prove Eqvivalence by Lemma: clear/pose *)
    clr - Hv1 Hv2 Hvl.
    bse - make_val_map_cons: v1 v2 vl Hmake.
  Qed.



End Induction.









Section Transform.



  Lemma fs_wfm_val_to_result :
    forall v,
        fs_wfm_val v
    ->  fs_wfm_result (RValSeq [v]).
  Proof.
    (* #1 Auto: intro/cbn/auto *)
    itr; abn.
  Qed.



  Lemma fs_wfm_valseq_to_result :
    forall vs,
        fs_wfm_valseq vs
    ->  fs_wfm_result (RValSeq vs).
  Proof.
    (* #1 Auto: intro/cbn/auto *)
    itr; abn.
  Qed.



  Lemma fs_wfm_exception_to_result :
    forall exc,
        fs_wfm_exception exc
    ->  fs_wfm_result (RExc exc).
  Proof.
    (* #1 Auto: intro/cbn/auto *)
    itr; abn.
  Qed.



  Lemma fs_wfm_val_to_forall :
    forall v,
        fs_wfm_val v
    ->  Forall fs_wfm_val [v].
  Proof.
    (* #1 Auto: intro/cbn/auto *)
    itr; abn.
  Qed.



End Transform.