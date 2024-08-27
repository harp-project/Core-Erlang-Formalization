From CoreErlang.Equivalence.BigStepToFrameStack Require Export WellFormedMap.

Import SubstSemantics.

(**
* Help
  - map_insert_length1 [NotUsing]
  - map_insert_length2
  - make_val_map_length
  - make_val_map_cons
* Main
  - well_formed_map_fs_tuple
  - well_formed_map_fs_map
*)

(**
NOTES:  Later change lists to maps in Syntax
*)



Section Help.



  Theorem map_insert_length1 :
    forall k v ms,
      length ms <= length (map_insert k v ms).
  Proof.
    intros.
    induction ms as [| (key, var) ms IHms].
    * (* Case: ms is empty *)
      slia.
    * (* Inductive case: ms is (key, var) :: ms *)
      fold map_insert in *.
      simpl.
      destruct (k <ᵥ key).
      - (* Case: k <ᵥ key *)
        clear IHms. 
        slia.
      - destruct (k =ᵥ key).
        + (* Case: k =ᵥ key *)
          clear IHms.
          slia.
        + (* Case: k >ᵥ key *)
          by apply le_n_S.
  Qed.



  Theorem map_insert_length2 :
    forall k k' v v' ms,
      length (map_insert k v ms) <= length ((k', v') :: ms).
  Proof.
    intros.
    induction ms as [| (key, var) ms IHms].
    * (* Case: ms is empty *)
      slia.
    * (* Inductive case: ms is (key, var) :: ms *)
      fold map_insert in *.
      simpl.
      destruct (k <ᵥ key).
      - (* Case: k <ᵥ key *)
        clear IHms. 
        slia.
      - destruct (k =ᵥ key).
        + (* Case: k =ᵥ key *)
          clear IHms.
          slia.
        + (* Case: k >ᵥ key *)
          by apply le_n_S.
  Qed.



  Theorem make_val_map_length :
    forall ms,
      length (make_val_map ms) <= length ms.
  Proof.
    induction ms as [| (k, v) ms IHms].
    * (* Base case: ms is empty *)
      slia.
    * (* Inductive case: ms = (k, v) :: ms'*)
      simpl.
      destruct (make_val_map ms) as [| (k', v') ms'].
      - (* Case: make_val_map ms = [] *)
        by apply le_n_S.
      - (* Case: make_val_map ms = (k', v') :: ms' *)
        simpl.
        destruct (k <ᵥ k').
        + (* Case: k <ᵥ k' *)
          simpl in *.
          apply le_n_S.
          apply IHms.
        + destruct (k =ᵥ k').
          ** (* Case: k =ᵥ k' *)
             simpl in *.
             apply le_S.
             apply IHms.
          ** (* Case: k >ᵥ k' *)
             simpl.
             apply le_n_S.
             pose proof map_insert_length2 k k' v v' ms' as Hinsert.
             eapply Nat.le_trans.
             -- apply Hinsert.
             -- apply IHms.
  Qed.



  Theorem make_val_map_cons :
    forall v1 v2 vl,
        (v1, v2) :: vl = make_val_map ((v1, v2) :: vl)
    ->  vl = make_val_map vl.
  Proof.
    intros v1 v2 vl H.
    inv H.
    rename H1 into H.
    unfold Maps.map_insert in H.
    destruct (make_val_map vl) as [| (v1', v2') vl'] eqn:Hmake.
    - (* Case: make_val_map vl = [] *)
      clear Hmake.
      by inv H.
    - (* Case: make_val_map vl = (v1', v2') :: vl' *)
      destruct (v1 <ᵥ v1') eqn:Hlt.
      + (* Case: v1 <ᵥ v1' *)
        clear Hmake Hlt.
        by inv H.
      + destruct (v1 =ᵥ v1') eqn:Heq.
        * (* Case: v1 =ᵥ k' *)
          clear Hlt Heq.
          inv H.
          pose proof make_val_map_length vl' as Hlength.
          rewrite Hmake in Hlength.
          simpl in Hlength.
          lia.
        * (* Case: v1 >ᵥ v1' *)
          clear Hmake Hlt.
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
    * apply Forall_cons.
      - exact Hv.
      - apply Forall_nil.
    * apply Forall_cons.
      - unfold well_formed_map_fs.
        exact Hvl.
      - apply Forall_nil.
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
    rename H into Hmake.
    cbn in Hv1.
    cbn in Hv2.
    split.
    - clear Hmake Hvl Hv2.
      apply Forall_cons.
      + exact Hv1.
      + apply Forall_nil.
    - clear Hv1.
      split.
      + clear Hmake Hvl.
        apply Forall_cons. 
        * exact Hv2.
        * apply Forall_nil.
      + clear Hv2.
        apply Forall_cons.
        * unfold well_formed_map_fs.
          split. 2: { exact Hvl. }
          clear Hvl.
          by pose proof make_val_map_cons v1 v2 vl Hmake.
       * apply Forall_nil.
  Qed.



End Main.