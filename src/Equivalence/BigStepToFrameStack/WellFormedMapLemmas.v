From CoreErlang.Equivalence.BigStepToFrameStack Require Export WellFormedMap.

From CoreErlang.FrameStack Require Import SubstSemantics.
Require Import stdpp.list.

Import SubstSemantics.

(**
* Help
  - make_val_map_length [Admitted]
  - make_val_map_cons
* Main
  - well_formed_map_fs_tuple
  - well_formed_map_fs_map
*)

(**
NOTES:  Later change lists to maps in Syntax
*)



Section Help.



  Theorem make_val_map_length :
    forall ms,
      length (make_val_map ms) <= length ms.
  Proof.
    induction ms as [| (k, v) ms' IHms'].
    - (* Base case: ms = [] *)
      simpl.
      apply le_n.
    - (* Inductive case: ms = (k, v) :: ms' *)
      simpl.
      destruct
        (make_val_map ms')
        as [| (k', v') ms'']
        eqn:Hmap.
      + (* Case: make_val_map ms' = [] *)
        simpl in IHms'.
        by apply le_n_S.
      + (* Case: make_val_map ms' = (k', v') :: ms'' *)
        simpl.
        destruct (k <ᵥ k') eqn:Hlt.
        * (* Case: k <ᵥ k' *)
          clear Hmap Hlt.
          simpl.
          apply le_n_S.
          apply IHms'.
        * destruct (k =ᵥ k') eqn:Heq.
          -- (* Case: k =ᵥ k' *)
             clear Hmap Hlt Heq.
             simpl.
             apply le_S.
             apply IHms'.
          -- (* Case: k >ᵥ k' *)
             simpl.
             admit.
  Admitted.



  Theorem make_val_map_cons :
    forall v1 v2 vl,
      (v1, v2) :: vl = make_val_map ((v1, v2) :: vl)
      -> vl = make_val_map vl.
  Proof.
    intros v1 v2 vl H.
    inv H.
    rename H1 into H.
    unfold Maps.map_insert in H.
    destruct
      (make_val_map vl)
      as [| (k', v') vl']
      eqn:Hmap.
    - (* Case: make_val_map vl = [] *)
      clear Hmap.
      by inv H.
    - (* Case: make_val_map vl = (k', v') :: ms *)
      destruct (v1 <ᵥ k') eqn:Hlt.
      + (* Case: v1 <ᵥ k' *)
        clear Hlt.
        by inv H.
      + destruct (v1 =ᵥ k') eqn:Heq.
        * (* Case: v1 =ᵥ k' *)
          clear Hlt Heq.
          inv H.
          pose proof make_val_map_length vl' as Hlength.
          rewrite Hmap in Hlength.
          simpl in Hlength.
          lia.
        * (* Case: v1 >ᵥ k' *)
          clear Hmap Hlt.
          inv H.
          rewrite Val_eqb_refl in Heq.
          congruence.
  Qed.



End Help.






Section Main.



  Theorem well_formed_map_fs_tuple :
    forall v vl,
        Forall well_formed_map_fs [VTuple (v :: vl)]
    ->  Forall well_formed_map_fs [v]
    /\  Forall well_formed_map_fs [VTuple vl].
  Proof.
    intros v vl Hvvl.
    inv Hvvl.
    clear H2.
    destruct H1.
    rename H into Hv.
    rename H0 into Hvl.
    split.
    - apply Forall_cons.
      + exact Hv.
      + apply Forall_nil.
    - apply Forall_cons.
      + unfold well_formed_map_fs.
        exact Hvl.
      + apply Forall_nil.
  Qed.



  Theorem well_formed_map_fs_map :
    forall v1 v2 vl,
        Forall well_formed_map_fs [VMap ((v1, v2) :: vl)]
    ->  Forall well_formed_map_fs [v1]
    /\  Forall well_formed_map_fs [v2]
    /\  Forall well_formed_map_fs [VMap vl].
  Proof.
    intros v1 v2 vl Hv1v2vl.
    inv Hv1v2vl.
    clear H2.
    destruct H1.
    inv H0.
    inv H1.
    rename H0 into Hv1.
    rename H3 into Hv2.
    rename H2 into Hvl.
    rename H into Hmap.
    cbn in Hv1.
    cbn in Hv2.
    split.
    - apply Forall_cons.
      + exact Hv1.
      + apply Forall_nil.
    - clear Hv1.
      split.
      + apply Forall_cons. 
        * exact Hv2.
        * apply Forall_nil.
      + clear Hv2.
        apply Forall_cons.
        * unfold well_formed_map_fs.
          split. 2:
          {
            exact Hvl.
          }
          clear Hvl.
          by pose proof make_val_map_cons v1 v2 vl Hmap.
       * apply Forall_nil.
  Qed.



End Main.