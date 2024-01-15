From CoreErlang.Concurrent Require Import BarbedBisim.

Import ListNotations.

Definition appearsEther (ι : PID) (eth : Ether) : Prop :=
  isUsedEther ι eth \/
  (exists (ι' : PID), eth !! (ι, ι') ≠ None) \/
  (exists (ιs ιd : PID) (t : list Signal),
     eth !! (ιs, ιd) = Some t /\ ι ∈ (flat_union usedPIDsSignal t)).

Proposition isUsedEther_appearsEther :
  forall ι eth, isUsedEther ι eth -> appearsEther ι eth.
Proof.
  intros. by left.
Qed.

Proposition appearsEther_isUsedEther :
  forall ι eth, ¬appearsEther ι eth -> ¬isUsedEther ι eth.
Proof.
  intros. intro. apply H. by apply isUsedEther_appearsEther.
Qed.

Proposition not_appearsEther_alt :
  forall ι eth, ¬appearsEther ι eth <->
    (
      ¬isUsedEther ι eth /\
      (forall ι', eth !! (ι, ι') = None) /\
      (forall ιs ιd t, eth !! (ιs, ιd) = Some t -> ι ∉ (flat_union usedPIDsSignal t))
    ).
Proof.
  intros. split; intros.
  * intuition.
    - apply H. by left.
    - apply eq_None_ne_Some_2. intros. intro.
      apply H. right. left. exists ι'. by rewrite H0.
    - apply H. right. right.
      apply elem_of_flat_union in H1. destruct_hyps.
      exists ιs, ιd, t. split; auto.
      apply elem_of_flat_union. set_solver.
  * intro. destruct_hyps. destruct H0. congruence.
    destruct_or!.
    - set_solver.
    - set_solver.
Qed.

Corollary does_not_appear_renamePID_ether :
  forall eth p p', ¬ appearsEther p eth -> ¬ appearsEther p' eth ->
    renamePIDEther p p' eth = eth.
Proof.
  intros. unfold renamePIDEther.
  apply map_eq. intros. destruct i as [ιs ιd].
  destruct (eth !! (ιs, ιd)) eqn:P; setoid_rewrite P.
  {
    apply lookup_kmap_Some; auto.
    assert (ιs ≠ p /\ ιs ≠ p' /\ ιd ≠ p /\ ιd ≠ p'). {
      split_and!; intro; subst.
      * apply H. right. left. exists ιd. intro. congruence.
      * apply H0. right. left. exists ιd. intro. congruence.
      * apply H. left. by exists ιs, l.
      * apply H0. left. by exists ιs, l.
    }
    exists (ιs, ιd). destruct_hyps. simpl.
    unfold renamePIDPID_sym; repeat case_match; eqb_to_eq; subst; try congruence.
    split. reflexivity.
    rewrite lookup_fmap. setoid_rewrite P. simpl.
    f_equal.
    rewrite <- (map_id l) at 2.
    apply map_ext_Forall. apply Forall_forall. intros.
    apply isNotUsed_renamePID_signal.
    intro. apply H. right. right. do 3 eexists. split. exact P.
    apply elem_of_flat_union. eexists. split; eassumption.
  }
  {
    apply lookup_kmap_None; auto.
    intros. destruct i. cbn in H1. setoid_rewrite lookup_fmap.
    unfold renamePIDPID_sym in H1.
    repeat case_match; eqb_to_eq; subst; simpl in *; inv H1.
    9: try by setoid_rewrite P.
    all: try by (apply not_appearsEther_alt in H; destruct_hyps;
      rewrite H1).
    all: try by (apply not_appearsEther_alt in H0; destruct_hyps;
      rewrite H1).
    * apply not_appearsEther_alt in H; destruct_hyps.
      unfold isUsedEther in H.
      assert (forall ι' l, eth !! (ι', p) ≠ Some l) by set_solver.
      eapply eq_None_ne_Some_2 in H5. by setoid_rewrite H5.
    * apply not_appearsEther_alt in H0; destruct_hyps.
      unfold isUsedEther in H0.
      assert (forall ι' l, eth !! (ι', p') ≠ Some l) by set_solver.
      eapply eq_None_ne_Some_2 in H6. by setoid_rewrite H6.
  }
Qed.

Corollary isNotUsed_renamePID_pool :
  forall Π p p', ¬ isUsedPool p Π -> ¬ isUsedPool p' Π ->
    renamePIDPool p p' Π = Π.
Proof.
  intros. unfold renamePIDPool.
  apply map_eq. intros.
  destruct (Π !! i) eqn:P; setoid_rewrite P.
  {
    apply lookup_kmap_Some; auto.
    assert (i ≠ p /\ i ≠ p'). {
      split_and!; intro; subst.
      * apply H. left. intro. congruence.
      * apply H0. left. intro. congruence.
    }
    exists i. destruct_hyps. simpl.
    unfold renamePIDPID_sym; repeat case_match; eqb_to_eq; subst; try congruence.
    split. reflexivity.
    rewrite lookup_fmap. setoid_rewrite P. simpl.
    f_equal.
    apply isNotUsed_renamePID_proc.
    intro. apply H. right. do 2 eexists. split. exact P. assumption.
  }
  {
    apply lookup_kmap_None; auto.
    intros.
    unfold renamePIDPID_sym in H1.
    repeat case_match; eqb_to_eq; subst; simpl in *.
    all: setoid_rewrite lookup_fmap.
    3: try by setoid_rewrite P.
    * destruct (Π !! p) eqn:Q; setoid_rewrite Q; auto.
      exfalso. apply H. left. intro. congruence.
    * destruct (Π !! p') eqn:Q; setoid_rewrite Q; auto.
      exfalso. apply H0. left. intro. congruence.
  }
Qed.

(* InductiveNodeSemantics.v *)
(* Lemma ether_is_not_affected :
  forall n n' l, n -[l]ₙ->* n' ->
    (forall ι, In ι (PIDsOf sendPIDOf l) -> n'.2 !! ι <> None) ->
    forall source dest,
      n'.2 !! dest = None ->
      n.1 !! (source, dest) = [] ->
      n'.1 !! (source, dest) = []. *)
Lemma ether_is_not_affected :
  forall O n n' l, n -[l]ₙ->* n' with O ->
    (forall ι, ι ∈ (PIDsOf sendPIDOf l) -> n'.2 !! ι <> None) ->
    forall source dest,
      n'.2 !! dest = None ->
      n.1 !! (source, dest) = n'.1 !! (source, dest).
Proof.
  intros O n n' l H. induction H; intros; try reflexivity.
  setoid_rewrite <- IHclosureNodeSem.
  2: { intros. apply H1. unfold PIDsOf. simpl. apply elem_of_app. now right. }
  2: { assumption. }
  inversion H; subst; simpl in *; try reflexivity.
  * unfold etherAdd. destruct (decide ((ι, ι') = (source, dest))).
    - inv e. exfalso. eapply H1. left. assumption.
    - break_match_goal; setoid_rewrite lookup_insert_ne; try assumption; auto.
  * unfold etherPop in H3. destruct (decide ((ι1, ι) = (source, dest))).
    - inv e. exfalso. eapply processes_dont_die_Some in H0.
      2: { setoid_rewrite lookup_insert. reflexivity. }
      inv H0. congruence.
    - break_match_hyp; try congruence. destruct l0; try congruence. inv H3.
      setoid_rewrite lookup_insert_ne; auto.
Qed.

(* BarbedBisim.v *)
Lemma isUntaken_comp :
  forall eth Π Π' ι, isUntaken ι (eth, Π ∪ Π') <->
    isUntaken ι (eth, Π) /\ isUntaken ι (eth, Π').
Proof.
  split.
  {
    intros. destruct H. unfold isUntaken. simpl in *.
    apply lookup_union_None in H. intuition.
  }
  {
    intros. destruct H, H, H0. simpl in *.
    split; auto.
    simpl. now apply lookup_union_None.
  }
Qed.

Lemma insert_of_union :
  forall ι p Π Π2 prs,
  ι ↦ p ∥ prs = Π ∪ Π2 ->
  Π = ι ↦ p ∥ Π \/ (ι ∉ dom Π /\ Π2 = ι ↦ p ∥ Π2).
Proof.
  intros.
  put (lookup ι : ProcessPool -> _) on H as H'. simpl in H'.
  setoid_rewrite lookup_insert in H'.
  symmetry in H'. apply lookup_union_Some_raw in H'. destruct H' as [H' | [H_1 H_2]].
  * left. apply map_eq. intros.
    destruct (decide (i = ι)); subst.
    - now setoid_rewrite lookup_insert.
    - now setoid_rewrite lookup_insert_ne.
  * right. split. now apply not_elem_of_dom.
    apply map_eq. intros.
    destruct (decide (i = ι)); subst.
    - now setoid_rewrite lookup_insert.
    - now setoid_rewrite lookup_insert_ne.
Qed.

(* InductiveNodeSemantics.v *)
Lemma step_in_comp :
  forall O eth eth' Π Π2 Π' a ι,
    (eth, Π ∪ Π2) -[ a | ι ]ₙ-> (eth', Π') with O ->
    (exists n'', (eth, Π) -[ a | ι ]ₙ-> (eth', n'') with O /\ (Π' = n'' ∪ Π2)) \/
    (exists n'', (eth, Π2) -[ a | ι ]ₙ-> (eth', n'') with O /\ (Π' = Π ∪ n'')).
Proof.
  intros. inv H.
  * apply insert_of_union in H2 as H2'. destruct_or!.
    - setoid_rewrite H2'. left. exists (ι ↦ p' ∥ Π).
      split. now apply n_send.
      apply map_eq. intros. put (lookup i : ProcessPool -> _) on H2 as H2''.
      simpl in *. rewrite par_comp_assoc_pool.
      repeat processpool_destruct; try congruence.
    - inv H2'. setoid_rewrite H0. right. exists (ι ↦ p' ∥ Π2).
      split. 1: now apply n_send.
      apply map_eq. intros. put (lookup i : ProcessPool -> _) on H2 as H2''.
      simpl in *. setoid_rewrite <- insert_union_r. 2: now apply not_elem_of_dom.
      repeat processpool_destruct; try congruence.
  * apply insert_of_union in H1 as H1'. destruct_or!.
    - setoid_rewrite H1'. left. exists (ι ↦ p' ∥ Π).
      split. apply n_arrive; auto.
      apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as H1''.
      simpl in *. rewrite par_comp_assoc_pool.
      repeat processpool_destruct; try congruence.
    - inv H1'. setoid_rewrite H0. right. exists (ι ↦ p' ∥ Π2).
      split. 1: now apply n_arrive.
      apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as H1''.
      simpl in *. setoid_rewrite <- insert_union_r. 2: now apply not_elem_of_dom.
      repeat processpool_destruct; try congruence.
  * apply insert_of_union in H1 as H1'. destruct H1'.
    - setoid_rewrite H. left. exists (ι ↦ p' ∥ Π).
      split. apply n_other; auto.
      apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as H1''.
      simpl in *. rewrite par_comp_assoc_pool.
      repeat processpool_destruct; try congruence.
    - inv H. setoid_rewrite H2. right. exists (ι ↦ p' ∥ Π2).
      split. 1: now apply n_other.
      apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as H1''.
      simpl in *. setoid_rewrite <- insert_union_r. 2: now apply not_elem_of_dom.
      repeat processpool_destruct; try congruence.
  * apply insert_of_union in H1 as H1'. destruct_or!.
    - setoid_rewrite H1'. left.
      exists (ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π).
      split. eapply n_spawn; eauto.
      1: put (dom : ProcessPool -> _) on H1 as P; simpl in *; clear -P H5 H6 H7; set_solver.
      apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as H1''.
      simpl in *. do 2 rewrite par_comp_assoc_pool.
      repeat processpool_destruct; try congruence.
    - inv H1'. setoid_rewrite H0. right. exists (ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π2).
      split. 1: eapply n_spawn; eauto.
      1: put (dom : ProcessPool -> _) on H1 as P; simpl in *; clear -P H5 H6 H7; set_solver.
      apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as H1''.
      simpl in *. repeat setoid_rewrite <- insert_union_r.
      2: now apply not_elem_of_dom.
      2: put (dom : ProcessPool -> _) on H1 as P; simpl in *; apply not_elem_of_dom; set_solver.
      repeat processpool_destruct; try congruence.
Qed.

(* InductiveNodeSemantics.v *)
(* Corollary isNotUsed_renamePID_ether :
  forall eth from to, ¬isUsedEther from eth ->
                      ¬isUsedEther to eth -> renamePIDEther from to eth = eth.
Proof.
  intros. unfold renamePIDEther. apply map_eq_iff. intros.
  destruct (eth !! i) eqn:P; setoid_rewrite P.
  * apply lookup_kmap_Some; auto. admit.
  * apply lookup_kmap_None; auto. intros. destruct i, i0. simpl in H1.
    inv H1. rewrite lookup_fmap. unfold renamePIDPID_sym in P.
    unfold isUsedEther in *. repeat case_match; eqb_to_eq; subst.
    - assert (forall ι' x l, eth !! (ι', from) <> Some (x :: l)) by firstorder.
Admitted. *)

(* InductiveNodeSemantics.v *)
(* Corollary double_renamePID_ether :
  forall eth from to, ¬isUsedEther to eth  -> renamePIDEther to from (renamePIDEther from to eth) = eth.
Proof.
  intros. unfold renamePIDEther.
  intros. unfold renamePIDEther. apply map_eq_iff. intros.
  unfold isUsedEther in H.
  assert (forall ι', eth !! (ι', to) = None). {
    intros. apply eq_None_ne_Some. intros ? ?.
    apply H. do 2 eexists. eassumption.
  }
  destruct i as [ιs ιd]. destruct (decide (to = ιd)); subst.
  * rewrite H0. apply lookup_kmap_None; auto. intros.
    destruct i; inv H1. unfold renamePIDPID_sym in H4.
    rewrite lookup_fmap. apply fmap_None.
    apply lookup_kmap_None; auto. intros.
    destruct i; inv H1. unfold renamePIDPID_sym in H5.
    rewrite lookup_fmap. apply fmap_None.
    repeat case_match; eqb_to_eq; subst; try apply H0; congruence.
  * admit.
Admitted. *)


(* Corollary isNotUsed_renamePID_pool :
  forall Π from to, ¬isUsedPool from Π -> renamePIDPool from to Π = Π.
Proof.
  intros.
Admitted. *)

(* Corollary double_renamePID_pool :
  forall Π from to, ¬isUsedPool to Π  -> renamePIDPool to from (renamePIDPool from to Π) = Π.
Proof.

Admitted. *)


Lemma SIGCLOSED_rename :
  forall s p p', SIGCLOSED s <-> SIGCLOSED (renamePIDSignal p p' s).
Proof.
  intros. destruct s; simpl; auto.
  all: split; intro; try by apply renamePID_preserves_scope.
  1-2: by apply renamePID_implies_scope in H.
Qed.

Lemma Signal_eq_renamePID :
  forall s from to,
    s =ₛ renamePIDSignal from to s.
Proof.
  destruct s; intros; try reflexivity.
  all: unfold Signal_eq; simpl; rewrite renamePID_Val_eqb.
  2: rewrite eqb_reflx.
  all: reflexivity.
Qed.

Lemma ether_wf_rename :
  forall eth p p',
    ether_wf eth <-> ether_wf (renamePIDEther p p' eth).
Proof.
  split; intro; unfold ether_wf, renamePIDEther in *; intros.
  * apply lookup_kmap_Some in H0. 2: auto. destruct H0 as [[s d] [Eq H0]].
    simpl in Eq. inv Eq. rewrite lookup_fmap in H0.
    destruct (eth !! (s, d)) eqn:P; setoid_rewrite P in H0. 2: inv H0.
    apply H in P. inv H0.
    apply Forall_forall. intros. rewrite Forall_forall in P.
    apply elem_of_map_iff in H0 as [? [? ?]]. apply P in H1.
    subst x. now apply SIGCLOSED_rename.
  * (* case separation needed for ι = p/p' *)
    assert ((map (renamePIDSignal p p') <$> eth) !! (ι, ι') = map (renamePIDSignal p p') <$> Some l). {
      rewrite lookup_fmap. by setoid_rewrite H0.
    }
    simpl in H1.
    pose proof (lookup_kmap (prod_map (renamePIDPID_sym p p') (renamePIDPID_sym p p')) (map (renamePIDSignal p p') <$> eth) (ι, ι')).
    setoid_rewrite <- H2 in H1. apply H in H1.
    clear -H1. apply Basics.map_Forall in H1; auto.
    intros. by apply SIGCLOSED_rename in H.
Qed.

Lemma spawnPIDs_subset_all :
  forall l, list_to_set (PIDsOf spawnPIDOf l) ⊆ flat_union (fun '(a, ι) => {[ι]} ∪ usedPIDsAct a) l.
Proof.
  induction l; simpl; auto.
  destruct a; simpl in *. case_match; simpl.
  destruct a; inv H.
  cbn. set_solver.
  set_solver.
Qed.

Lemma sendPIDs_subset_all :
  forall l, list_to_set (PIDsOf sendPIDOf l) ⊆ flat_union (fun '(a, ι) => {[ι]} ∪ usedPIDsAct a) l.
Proof.
  induction l; simpl; auto.
  destruct a; simpl in *. case_match; simpl.
  destruct a; inv H.
  cbn. set_solver.
  set_solver.
Qed.

(* Lemma rename_preCompatible :
  forall O eth Π p p',
  ¬isUsedPool p' Π ->
  (* p' ∉ dom Π -> *)
  p' ∉ O ->
  p ∉ O ->
  ¬isUsedEther p' eth ->
  (* ¬isUntaken p (eth, Π) ->  *)(* <- 
    renaming is only compatible when it is done for either a non-existing PID, or
    an existing process. It does not make sense for a PID that is reserved for the
    "outside" world.
   *)
  preCompatibleNodes O (eth, Π)
    (renamePIDEther p p' eth, renamePIDPool p p' Π).
Proof.
  split; simpl.
  * apply lookup_kmap_None; auto. intros.
    destruct H4. unfold renamePIDPID_sym in H5. repeat case_match; eqb_to_eq; subst.
    - simpl in *. congruence.
    - rewrite lookup_fmap.
      assert (Π !! p' = None). {
        apply eq_None_ne_Some_2. intros. intro. apply H. left.
        intro. congruence.
      }
      now setoid_rewrite H5.
    - rewrite lookup_fmap. simpl in *. now setoid_rewrite H4.
  * destruct H4. simpl in *.
    assert (ι ≠ p'). {
      intro. subst. congruence.
    }
    assert (ι ≠ p). {
      intro. subst.
      congruence.
    }
    now apply isUsedEther_rename_same_neq.
Qed. *)


Lemma rename_preCompatible:
  forall O eth Π p p',
  ¬isUsedPool p' Π ->
  (* p' ∉ dom Π -> *)
  p' ∉ O ->
  p ∉ O ->
  (* ¬appearsEther p' eth -> *)
  preCompatibleNodes O (eth, Π)
    (renamePIDEther p p' eth, renamePIDPool p p' Π).
Proof.
  split; simpl.
  * apply lookup_kmap_None; auto. intros.
    destruct H3. unfold renamePIDPID_sym in H4. repeat case_match; eqb_to_eq; subst.
    - simpl in *. congruence.
    - rewrite lookup_fmap.
      assert (Π !! p' = None). {
        apply eq_None_ne_Some_2. intros. intro. apply H. left.
        intro. congruence.
      }
      now setoid_rewrite H4.
    - rewrite lookup_fmap. simpl in *. now setoid_rewrite H3.
  * destruct H3. simpl in *.
    assert (ι ≠ p'). {
      intro. subst. congruence.
    }
    assert (ι ≠ p). {
      intro. subst.
      congruence.
    }
    now apply isUsedEther_rename_same_neq.
Qed.

Corollary rename_preCompatible_sym :
  forall O eth Π p p',
  ¬isUsedPool p' Π ->
  (* p' ∉ dom Π -> *)
  (* ¬isUsedEther p' eth -> *)
  p' ∉ O ->
  p ∉ O ->
  (* ¬isUntaken p (eth, Π) -> *)
  symClos (preCompatibleNodes O) (eth, Π)
    (renamePIDEther p p' eth, renamePIDPool p p' Π).
Proof.
  intros. split.
  * apply rename_preCompatible; auto.
  * split; simpl.
    - destruct H3. simpl in *. setoid_rewrite lookup_kmap_None in H3; auto.
      specialize (H3 ι). unfold renamePIDPID_sym in H3.
      repeat break_match_hyp; eqb_to_eq; subst.
      + simpl in *. congruence.
      + congruence.
      + rewrite lookup_fmap in H3. simpl in *.
        specialize (H3 eq_refl).
        destruct (Π !! ι) eqn:P; setoid_rewrite P in H3. simpl in H3. congruence.
        reflexivity.
    - destruct H3. simpl in *.
      assert (ι ≠ p'). {
        intro. subst. congruence.
      }
      assert (ι ≠ p). {
        intro. subst.
        congruence.
      }
      by apply isUsedEther_rename_same_neq in H4.
Qed.

(* Lemma impossible_send :
  forall n n' l, n -[l]ₙ->* n' ->
    forall ι, In ι (flat_map (fun '(a, ι) => ι::usedPIDsAct a) l) ->
      (isUsedEther ι n.1 \/ isUsedPool ι n.2 \/ exists ιd, (n.1 !! (ι, ιd)) ≠ None).
Proof.
  intros. induction H. inv H0.
  unfold PIDsOf in H0. simpl in H0.
  destruct H0. 2: apply in_app_or in H0 as [|].
  {
    subst. inv H; simpl; right; left; left; by setoid_rewrite lookup_insert.
  }
  {
    inv H; simpl in H0.
    * destruct_or!; subst; simpl.
      - right; left; left; by setoid_rewrite lookup_insert.
      - right. left. right. exists ι0, p.
        split. by setoid_rewrite lookup_insert. inv H2; simpl; try by auto.
        all: apply in_or_app; right; by left.
      - right. left. right. exists ι0, p.
        split. by setoid_rewrite lookup_insert. inv H2; simpl; try by auto.
        + cbn in H0. right. In_app_solver.
        + cbn in H0. right. In_app_solver.
        + cbn in H0. right. In_app_solver.
    * destruct_or!; subst; simpl.
      - right. right. unfold etherPop in H2. case_match. 2: congruence.
        eexists. intro. rewrite H in H0. congruence.
      - right; left; left; by setoid_rewrite lookup_insert.
      - right. left.
    * destruct_or!; subst; try by inv H0.
      inv H0. 2: { inv H. }
      right; left; by setoid_rewrite lookup_insert.
    * 
  }
  {
  
  } *)

(* This will not hold. For example, spawn + send to self won't be in the ether
   or in the pool. *)
Lemma impossible_send :
  forall O n n' l, n -[l]ₙ->* n' with O ->
    forall ι, ι ∈ (PIDsOf sendPIDOf l) ->
      (isUsedEther ι n.1 \/ isUsedPool ι n.2).
Proof.
  (* intros. induction H. inv H0.
  unfold PIDsOf in H0. simpl in H0.
  apply in_app_or in H0. destruct H0.
  * destruct a; simpl in H0; inv H0. 2: contradiction.
    inv H. 2: { clear -H2. intuition; congruence. }
    simpl. right. right. exists ι0, p. split.
    by setoid_rewrite lookup_insert. inv H7; simpl; auto.
    - apply in_or_app. right. by left.
    - apply in_or_app. right. by left.
  * pose proof H0 as H0D. apply IHclosureNodeSem in H0. clear IHclosureNodeSem H1.
    inv H;simpl in *.
    - destruct H0.
      + destruct (isUsedEther_dec ι ether). 1: by auto.
        right. destruct (decide (ι = ι0)).
        ** subst. left. by setoid_rewrite lookup_insert.
        ** right. exists ι0, p.
           split. by setoid_rewrite lookup_insert.
           assert (ι = ι'). {
             destruct H as [x0 [l0 H]]. unfold etherAdd in H.
             unfold isUsedEther in H0.
             assert (forall ιs l, ether !! (ιs, ι) <> Some l) by (clear -H0; firstorder).
             case_match.
             * destruct (decide ((ι0, ι') = (x0, ι))).
               - inv e. by apply H2 in H3.
               - setoid_rewrite lookup_insert_ne in H; auto.
                 by apply H2 in H.
             * destruct (decide ((ι0, ι') = (x0, ι))).
               - inv e. reflexivity.
               - setoid_rewrite lookup_insert_ne in H; auto.
                 by apply H2 in H.
           }
           subst. inv H1; simpl; try by auto.
           -- apply in_or_app. right. by left.
           -- apply in_or_app. right. by left.
      + apply isUsedPool_insert_1 in H. destruct_or!.
        ** right. apply isUsedPool_insert_2. by left.
        ** subst. right. left. by setoid_rewrite lookup_insert.
        ** right.
           clear H0D.
           apply isUsedPool_insert_2. right. right.
           inv H1; simpl in *. all: try right.
           1-2,5: repeat (apply in_app_or in H as [|]); In_app_solver.
           1-2: apply in_app_or in H as [|]; [In_app_solver |].
           1: destruct H; subst; apply in_or_app; right; try by left.
           1: right; repeat (apply in_app_or in H as [|]); In_app_solver.
           repeat (apply in_app_or in H as [|]).
           2-3: apply in_or_app; right; right; In_app_solver.
           apply in_or_app; right. right. apply in_or_app.
           left. apply in_remove in H; by apply H.
    - destruct H0.
      + left. eapply isUsedEther_etherPop_rev; eassumption.
      + apply isUsedPool_insert_1 in H. destruct_or!.
        ** right. apply isUsedPool_insert_2. by left.
        ** subst. right. left. by setoid_rewrite lookup_insert.
        ** inv H2; simpl in *.
           all: repeat apply in_app_or in H as [|].
           all: try by (right; apply isUsedPool_insert_2; right; right; In_app_solver).
           -- rewrite flat_map_app in H. apply in_app_or in H as [|].
              by (right; apply isUsedPool_insert_2; right; right; In_app_solver).
              simpl in H. rewrite app_nil_r in H. *)
Abort.

(* Lemma rename_reduction_compatible_1 :
  forall eth Π p p' l eth' Π',
  (eth,Π) -[l]ₙ->* (eth',Π') ->
  ¬ isUsedPool p' Π ->
  ¬ isUsedEther p' eth ->
  (* ¬isUntaken p (eth, Π) -> *)
  (p ∈ dom Π \/ (¬isUsedEther p eth /\ ¬isUsedPool p Π)) ->
  ¬In p' (flat_map (fun '(a, ι) => ι::usedPIDsAct a) l) ->
  reductionPreCompatibility (eth, Π) (eth .[ p ⇔ p' ]ₑ, Π .[ p ⇔ p' ]ₚₚ)
                   l (map (prod_map (renamePIDAct p p') (renamePIDPID_sym p p')) l).
Proof.
  intros ??????? D. intros. split.
  * apply Forall_forall. intros. intro.
    destruct H4; simpl in *. unfold renamePIDPool in H4.
    assert (x <> p'). {
      pose proof (spawnPIDs_subset_all l).
      clear -H3 H2 H6.
      pose proof (proj1 (elem_of_subseteq _ _) H6).
      apply elem_of_list_In in H3. apply H in H3.
      intro. subst. apply elem_of_list_In in H3. congruence.
    }
    assert (x <> p). {
      intro. subst.
      by apply isUsedEther_rename_same_old in H5.
    }
    apply isUsedEther_rename_same_neq in H5. 2-3: assumption.
    eapply isUsedEther_no_spawn in H3. 2-3: eassumption. congruence.
  * simpl. intros.
    assert (ι <> p'). {
      pose proof (sendPIDs_subset_all l).
      clear -H6 H2 H4.
      pose proof (proj1 (elem_of_subseteq _ _) H6).
      apply elem_of_list_In in H4. apply H in H4.
      intro. subst. apply elem_of_list_In in H4. congruence.
    }
    assert (ι <> p). {
      intro. subst.
      destruct H1. 1: congruence.
      destruct H1.
      
    }
    destruct (decide (ι = p)).
    {
      subst. split. 2: split.
      - unfold renamePIDPool. setoid_rewrite kmap_fmap; auto.
        setoid_rewrite dom_fmap. setoid_rewrite dom_kmap_L; auto.
        intro. apply elem_of_map in H7 as [x [Eq1 Eq2]].
        unfold renamePIDPID_sym in Eq1.
        repeat case_match; eqb_to_eq; subst; try congruence.
        apply H. left. intro. by apply not_elem_of_dom in H8.
      - admit.
      - admit.
    }
    {
      split. 2: split.
      - admit.
      - admit.
      - admit.
    }

Admitted.

Lemma rename_reduction_compatible_2 :
  forall eth Π p p' l,
  reductionPreCompatibility (eth .[ p ⇔ p' ]ₑ, Π .[ p ⇔ p' ]ₚₚ) (eth, Π)
                   (map (prod_map (renamePIDAct p p') (renamePIDPID_sym p p')) l) l.
Proof.
  
Admitted. *)

Lemma fresh_pid_is_not_in_step :
  forall O n n' a ι,
  n -[ a | ι ]ₙ-> n' with O ->
  (forall p',
    ¬ isUsedPool p' n.2 ->
    ¬ appearsEther p' n.1 ->
    p' ∉ O ->
   p' ∉ (usedPIDsAct a) \/ (exists v1 v2, a = ASpawn p' v1 v2 /\ p' ∉ usedPIDsVal v1 ∪ usedPIDsVal v2)).
Proof.
  intros. inv H; simpl in *. 1-3: left; intro.
  * assert (p' = ι \/ (p' = ι' \/ p' ∈ usedPIDsSignal t)) by set_solver.
    destruct H4.
    - subst. apply H0. left. by setoid_rewrite lookup_insert.
    - apply H0. clear -H3 H4.
      right. exists ι, p. split. by setoid_rewrite lookup_insert.
      inv H3; simpl in *; set_solver.
  * destruct (decide (ι = p')).
    - subst. apply H0. left. by setoid_rewrite lookup_insert.
    - apply not_appearsEther_alt in H1. destruct_hyps.
      unfold etherPop in H3. case_match. 2: congruence.
      destruct l. 1: congruence.
      inv H3. destruct (decide (p' = ι1)).
      + subst. specialize (H5 ι). congruence.
      + apply H6 in H7. simpl in H7. set_solver.
  * destruct_or!; subst; simpl in *; try set_solver.
    apply H0. left. assert (p' = ι) by set_solver. subst.
    by setoid_rewrite lookup_insert.
  * destruct (decide (ι' = p')).
    - subst. right. do 2 eexists. split. reflexivity.
      intro. apply H0. right. exists ι, p. split. by setoid_rewrite lookup_insert.
      inv H9. set_solver.
    - left. intro.
      apply H0. right. exists ι, p. split. by setoid_rewrite lookup_insert.
      inv H9; simpl in *.
      clear-H n. set_solver.
Qed.

Theorem appearsEther_step :
  forall O n n' a ι,
  n -[ a | ι ]ₙ-> n' with O ->
  forall ι',
    ι' ∉ usedPIDsAct a ->
    ¬appearsEther ι' n.1 ->
    ¬appearsEther ι' n'.1.
Proof.
  intros. inv H; simpl in *; auto.
  * intro. apply H1.
    destruct H. 2: destruct H.
    - left. apply isUsedEther_etherAdd_rev in H; auto. intro. subst.
      set_solver.
    - destruct_hyps. unfold etherAdd in H. case_match.
      + destruct (decide ((ι, ι'0) = (ι', x))).
        ** inv e. setoid_rewrite lookup_insert in H.
           right. left. exists x. by rewrite H3.
        ** setoid_rewrite lookup_insert_ne in H; auto.
           right. left. by exists x.
      + destruct (decide ((ι, ι'0) = (ι', x))).
        ** inv e. set_solver.
        ** setoid_rewrite lookup_insert_ne in H; auto.
           right. left. by exists x.
    - destruct_hyps. unfold etherAdd. unfold etherAdd in H.
      case_match.
      + destruct (decide ((ι, ι'0) = (x, x0))).
        ** inv e. setoid_rewrite lookup_insert in H. inv H.
           right. right. exists x, x0, l.
           split. assumption.
           rewrite flat_union_app in H3. set_solver.
        ** setoid_rewrite lookup_insert_ne in H; auto.
           right. right. exists x, x0, x1.
           split; assumption.
      + destruct (decide ((ι, ι'0) = (x, x0))).
        ** inv e. setoid_rewrite lookup_insert in H. inv H. set_solver.
        ** setoid_rewrite lookup_insert_ne in H; auto.
           right. right. exists x, x0, x1.
           split; assumption.
  * unfold etherPop in H2. case_match. 2: congruence.
    case_match. 1: congruence.
    inv H2. intro. apply H1. destruct H2. 2: destruct H2.
    - left. destruct H2. destruct_hyps.
      setoid_rewrite lookup_insert_ne in H2. 2: set_solver.
      by exists x, x0.
    - destruct_hyps. setoid_rewrite lookup_insert_ne in H2. 2: set_solver.
      right. left. by exists x.
    - destruct_hyps. destruct (decide ((ι1, ι) = (x, x0))).
      + inv e. setoid_rewrite lookup_insert in H2. inv H2.
        right. right. do 3 eexists. split. exact H.
        simpl. set_solver.
      + setoid_rewrite lookup_insert_ne in H2. 2: auto.
        right. right. do 3 eexists. split; eassumption.
Qed.

(* Axiom ff : False.

Theorem rename_bisim :
  forall O eth Π p p',
    ether_wf eth ->
    ¬ appearsEther p' eth ->
    (* p' ∉ dom Π -> *)
    (* (p ∈ dom Π \/ (¬isUsedEther p eth /\ ¬isUsedPool p Π)) -> *)
    (* (p ∈ dom Π \/ (¬isUsedEther p eth /\ ¬isUsedPool p Π)) -> *)
    (* ~isUntaken p (eth, Π) -> *)
    ¬isUsedPool p' Π ->
    p ∉ O ->
    p' ∉ O ->
    (eth, Π) ~ (renamePIDEther p p' eth, renamePIDPool p p' Π) observing O.
Proof.
  cofix IH.
  intros. constructor; auto.
  * apply appearsEther_isUsedEther in H0. apply rename_preCompatible_sym; assumption.
  * simpl. by apply ether_wf_rename.
  * intros. destruct A' as [eth' Π'].
    apply fresh_pid_is_not_in_step with (p' := p') in H4 as D; auto.
    destruct D.
    {
      exists (renamePIDEther p p' eth', renamePIDPool p p' Π'),
             [(renamePIDAct p p' a, renamePIDPID_sym p p' ι)].
      split.
      - econstructor. apply renamePID_is_preserved_node_semantics. exact H4.
        1,3-4: assumption.
        by apply appearsEther_isUsedEther.
        constructor.
      - apply IH; try assumption.
        + eapply n_trans with (l := []) in H4. 2: constructor.
          by apply ether_wf_preserved in H4.
        + eapply appearsEther_step in H4. exact H4. all: assumption.
        + eapply not_isUsedPool_step in H4; try eassumption.
    }
    { (* p' should be renamed to a fresh variable <- not guarded anymore *)
      destruct_hyps. subst.
      assert (exists new, ¬ appearsEther new eth /\ ¬isUsedPool new Π /\ new ∉ O /\
               new ∉ usedPIDsVal x ∪ usedPIDsVal x0). {
        exfalso. apply ff.
      }
      destruct H5 as [new H5]. destruct_hyps.
      exists (renamePIDEther p p' (renamePIDEther p' new eth'), renamePIDPool p p' (renamePIDPool p' new Π')),
             [(renamePIDAct p p' (renamePIDAct p' new  (ASpawn p' x x0)), renamePIDPID_sym p p' (renamePIDPID_sym p' new  ι))].
      rewrite <- (does_not_appear_renamePID_ether eth p' new); auto.
      rewrite <- (isNotUsed_renamePID_pool Π p' new); auto.
      split.
      eapply n_trans.
        eapply renamePID_is_preserved_node_semantics.
        eapply renamePID_is_preserved_node_semantics.
        exact H4.
        9: apply n_refl.
        all: auto. 1-5: exfalso; apply ff.
      eapply barbedBisim_trans. 2: apply IH. apply IH.
      all: clear IH; try assumption.
      all: exfalso; apply ff.
    }
  * simpl. intros.
    exists (renamePIDPID_sym p p' source), []. eexists.
    split.
    {
      apply n_refl.
    }
    {
      replace (renamePIDPID_sym p p' source, dest) with
           ((prod_map (renamePIDPID_sym p p') (renamePIDPID_sym p p')) (source, dest)).
      2: {
        cbn. f_equal. unfold renamePIDPID_sym.
        repeat case_match; try reflexivity; eqb_to_eq; subst; congruence.
      }
      setoid_rewrite lookup_kmap; auto.
      setoid_rewrite lookup_fmap.
      simpl. destruct (eth !! _) eqn:P.
      {
        setoid_rewrite P. simpl.
        eapply forall_biforall with (d1 := SUnlink) (d2 := SUnlink).
        1: by rewrite map_length.
        intros. rewrite map_nth with (d:= SUnlink).
        by apply Signal_eq_renamePID.
      }
      {
        setoid_rewrite P. simpl. trivial.
      }
    }
  * exfalso. apply ff.
  * exfalso. apply ff.
Qed. *)

Definition PIDRenamingList := list (PID * PID).
Definition renamePIDs {A} (f : PID -> PID -> A -> A) (l : PIDRenamingList) (x : A) : A :=
  fold_left (fun acc '(from, to) => f from to acc) l x.


Lemma usedPIDsProc_rename_elem_of :
  forall pr p p',
  p ∈ (usedPIDsProc pr) ->
  (usedPIDsProc (renamePIDProc p p' pr)) = {[p']} ∪ (usedPIDsProc pr) ∖ {[p]}.
Proof.
  intros. destruct pr; simpl.
  * destruct l, p0, p0, p0. simpl in *. admit.
  * admit.
Admitted.

Lemma usedPIDsProc_not_elem_of :
  forall pr p p',
  p ∉ (usedPIDsProc pr) ->
  (usedPIDsProc (renamePIDProc p p' pr)) = (usedPIDsProc pr) ∖ {[p]}.
Proof.
  admit.
Admitted.

Lemma isUsedPool_rename_same_neq :
  ∀ (ι p p' : PID) (Π : ProcessPool),
    ι ≠ p → ι ≠ p' → isUsedPool ι Π ↔ isUsedPool ι Π .[ p ⇔ p' ]ₚₚ.
Proof.
  intros. split; intro.
  {
    destruct H1.
    * left. intro. setoid_rewrite lookup_kmap_None in H2; auto.
      specialize (H2 ι). unfold renamePIDPID_sym in H2. repeat case_match; eqb_to_eq; try congruence.
      specialize (H2 eq_refl).
      setoid_rewrite lookup_fmap in H2. destruct (Π !! ι) eqn:P; setoid_rewrite P in H2.
      simpl in H2. congruence.
      congruence.
    * right.
      destruct_hyps.
      exists (renamePIDPID_sym p p' x), (renamePIDProc p p' x0). split.
      - setoid_rewrite lookup_kmap; auto.
        setoid_rewrite lookup_fmap. by setoid_rewrite H1.
      - destruct (gset_elem_of_dec p (usedPIDsProc x0)).
        + rewrite usedPIDsProc_rename_elem_of. 2: assumption. set_solver.
        + rewrite usedPIDsProc_not_elem_of. 2: assumption. set_solver.
  }
  {
    destruct H1.
    * left. intro. setoid_rewrite lookup_kmap_None in H1; auto.
      apply H1. intros. unfold renamePIDPID_sym in H3. repeat case_match; eqb_to_eq; try congruence.
      subst.
      setoid_rewrite lookup_fmap. by setoid_rewrite H2.
    * right.
      destruct_hyps.
      setoid_rewrite lookup_kmap_Some in H1; auto. destruct_hyps.
      setoid_rewrite lookup_fmap in H3.
      destruct (Π !! x1) eqn:P; setoid_rewrite P in H3; inv H3.
      exists x1, p0. split.
      - assumption.
      - destruct (gset_elem_of_dec p (usedPIDsProc p0)).
        + rewrite usedPIDsProc_rename_elem_of in H2. 2: assumption. set_solver.
        + rewrite usedPIDsProc_not_elem_of in H2. 2: assumption. set_solver.
  }
Qed.

Lemma isUsedPool_rename_same_old :
  ∀ (p p' : PID) (Π : ProcessPool),
    isUsedPool p Π .[ p ⇔ p' ]ₚₚ -> isUsedPool p' Π .
Proof.
  intros.
  destruct (decide (p = p')).
  {
    subst. by rewrite renamePID_id_pool in H.
  }
  destruct H.
  * left. intro. setoid_rewrite lookup_kmap_None in H; auto.
    apply H. intros. unfold renamePIDPID_sym in H1.
    repeat case_match; eqb_to_eq; subst; try congruence.
    rewrite lookup_fmap. by setoid_rewrite H0.
  * destruct_hyps.
    apply lookup_kmap_Some in H; auto. destruct_hyps. subst.
    setoid_rewrite lookup_fmap in H1.
    destruct (Π !! x1) eqn:P; setoid_rewrite P in H1; inv H1.
    destruct (decide (p ∈ usedPIDsProc p0)).
    - eapply usedPIDsProc_rename_elem_of in e.
      rewrite e in H0. set_solver.
    - eapply usedPIDsProc_not_elem_of in n0.
      rewrite n0 in H0. set_solver.
Qed.

Lemma isUsedPool_rename_same_new_1 :
  ∀ (p p' : PID) (Π : ProcessPool),
    isUsedPool p Π -> isUsedPool p' Π .[ p ⇔ p' ]ₚₚ.
Proof.
  intros.
  destruct H.
  * left. intro. setoid_rewrite lookup_kmap_None in H0; auto.
    specialize (H0 p). unfold renamePIDPID_sym in H0.
    rewrite Nat.eqb_refl in H0.
    repeat case_match; eqb_to_eq; try congruence; subst;
    specialize (H0 eq_refl);
    setoid_rewrite lookup_fmap in H0.
    - destruct (Π !! _) eqn:P; setoid_rewrite P in H0.
      simpl in H0. congruence.
      congruence.
  * right.
    destruct_hyps.
    exists (renamePIDPID_sym p p' x), (renamePIDProc p p' x0). split.
    - setoid_rewrite lookup_kmap; auto.
      setoid_rewrite lookup_fmap. by setoid_rewrite H.
    - rewrite usedPIDsProc_rename_elem_of. 2: assumption. set_solver.
Qed.

Lemma isUsedPool_rename_same_new_2 :
  ∀ (p p' : PID) (Π : ProcessPool),
    ¬isUsedPool p' Π ->
    isUsedPool p' Π .[ p ⇔ p' ]ₚₚ -> isUsedPool p Π.
Proof.
  intros.
  destruct H0.
  * left. intro. apply H0. apply lookup_kmap_None; auto.
    intros. setoid_rewrite lookup_fmap.
    unfold renamePIDPID_sym in H2. repeat case_match; eqb_to_eq; subst; try congruence.
    by setoid_rewrite H1.
  * right.
    destruct_hyps.
    setoid_rewrite lookup_kmap_Some in H0; auto. destruct_hyps.
    setoid_rewrite lookup_fmap in H2.
    destruct (Π !! x1) eqn:P; setoid_rewrite P in H2; inv H2.
    exists x1, p0. split.
    - assumption.
    - destruct (gset_elem_of_dec p (usedPIDsProc p0)). assumption.
      assert (p' ∉ usedPIDsProc p0). {
        intro. apply H. right. do 2 eexists. split; eassumption.
      }
      rewrite isNotUsed_renamePID_proc in H1; auto.
      congruence.
Qed.

(*
  If something is renamed, then it should not be renamed again
  if the ith element of the list is (from, to) then from should not appear 

*)

Inductive well_formed (O : gset PID) : Node -> list (PID * PID) -> Prop :=
| wf_nil Π : well_formed O Π nil
| wf_cons eth Π l from to:
  well_formed O (renamePIDEther from to eth, renamePIDPool from to Π) l ->
  from ∉ O ->
  to ∉ O ->
  ¬isUsedPool to Π ->
  ¬appearsEther to eth
->
  well_formed O (eth, Π) ((from, to) :: l).

Corollary renameList_preCompatible_sym :
  forall O l eth Π,
  (* ¬isUsedPool p' Π ->
  (* p' ∉ dom Π -> *)
  ¬isUsedEther p' eth ->
  p' ∉ O ->
  p ∉ O -> *)
  (* Forall (fun '(from, to) => (* ¬ appearsEther to eth /\ *) ¬isUsedPool to Π
     /\ to ∉ O /\ from ∉ O) l ->
  NoDup (map fst l) -> *)
  well_formed O (eth, Π) l ->
  (* ¬isUntaken p (eth, Π) -> *)
  symClos (preCompatibleNodes O) (eth, Π)
    (renamePIDs renamePIDEther l eth, renamePIDs renamePIDPool l Π).
Proof.
  induction l; intros.
  cbn. split; apply preCompatibleNodes_refl.
  inv H. simpl.
  split.
  {
    eapply preCompatibleNodes_trans.
    eapply rename_preCompatible with (p := from) (p' := to). 1-3: assumption.
    apply IHl; try assumption.
(*     {
      rewrite Forall_forall in H5. apply Forall_forall. intros.
      apply H5 in H2. destruct x; simpl in *. destruct_and!.
      split_and!; try assumption.
      intro. apply isUsedPool_rename_same_neq in H7. congruence.
      intro. subst. apply isUsedPool_rename_same_old in H7. congruence.
      intro. subst. apply isUsedPool_rename_same_new_2 in H7; try assumption.
      congruence.
    }
 *)
  }
  {
    (* destruct_hyps. inv H0. *)
    eapply preCompatibleNodes_trans.
    apply IHl; try assumption.
(*     1: {
      admit.
      (* clear -H H1 H4 H7 H8.
      induction H4; constructor; auto.
      * destruct x.
        clear IHForall. simpl in *.
        destruct_and!. split_and!.
        - intro. apply isUsedEther_rename_same_neq in H5. congruence. 2: set_solver.
          intro. subst. apply isUsedEther_rename_same_old in H5. congruence.
        - intro. apply isUsedPool_rename_same_neq in H5. congruence. 2: set_solver.
          intro. subst. apply isUsedPool_rename_same_old in H5. congruence.
        - set_solver.
        - set_solver.
      * apply IHForall; auto. set_solver. now inv H8. *)
    } *)
    eapply rename_preCompatible_sym with (p := from) (p' := to). 1-3: assumption.
  }
Qed.

Corollary renameList_preCompatible_sym_old :
  forall O l eth Π,
  (* ¬isUsedPool p' Π ->
  (* p' ∉ dom Π -> *)
  ¬isUsedEther p' eth ->
  p' ∉ O ->
  p ∉ O -> *)
  Forall (fun '(from, to) => ¬ isUsedEther to eth /\ ¬isUsedPool to Π /\ to ∉ O /\ from ∉ O) l ->
  NoDup (map snd l) ->
  (* ¬isUntaken p (eth, Π) -> *)
  symClos (preCompatibleNodes O) (eth, Π)
    (renamePIDs renamePIDEther l eth, renamePIDs renamePIDPool l Π).
Proof.
  induction l; intros.
  cbn. split; apply preCompatibleNodes_refl.
  inv H. destruct a. simpl.
  split.
  {
    destruct_hyps. inv H0.
    eapply preCompatibleNodes_trans.
    eapply rename_preCompatible with (p := p) (p' := p0). 1-3: assumption.
    apply IHl; try assumption.
    {
      clear -H H1 H4 H7 H8.
      induction H4. constructor.
      destruct x. inv H8. simpl in H7. destruct_hyps. constructor.
      * split_and!; try assumption.
        intro. apply isUsedEther_rename_same_neq in H9. congruence. 2: set_solver.
        intro. subst. apply isUsedEther_rename_same_old in H9. congruence.
        intro. apply isUsedPool_rename_same_neq in H9. congruence. 2: set_solver.
        intro. subst. apply isUsedPool_rename_same_old in H9. congruence.
      * apply IHForall; auto. set_solver.
    }
  }
  {
    destruct_hyps. inv H0.
    eapply preCompatibleNodes_trans.
    apply IHl; try assumption.
    1: {
      clear -H H1 H4 H7 H8.
      induction H4; constructor; auto.
      * destruct x.
        clear IHForall. simpl in *.
        destruct_and!. split_and!.
        - intro. apply isUsedEther_rename_same_neq in H5. congruence. 2: set_solver.
          intro. subst. apply isUsedEther_rename_same_old in H5. congruence.
        - intro. apply isUsedPool_rename_same_neq in H5. congruence. 2: set_solver.
          intro. subst. apply isUsedPool_rename_same_old in H5. congruence.
        - set_solver.
        - set_solver.
      * apply IHForall; auto. set_solver. now inv H8.
    }
    eapply rename_preCompatible_sym with (p := p) (p' := p0). 1-3: assumption.
  }
Qed.


Lemma ether_wf_renameList :
  forall l eth,
    ether_wf eth <-> ether_wf (renamePIDs renamePIDEther l eth).
Proof.
  induction l; intros.
  * split; by simpl.
  * split; simpl in *.
    {
      intro. destruct a.
      apply -> IHl. by apply ether_wf_rename.
    }
    {
      intro. destruct a.
      apply IHl in H. by apply ether_wf_rename in H.
    }
Qed.

(* Lemma fresh_pid_list_is_not_in_step :
  forall l O n n' a ι,
  n -[ a | ι ]ₙ-> n' with O ->
  (
    well_formed O n l ->
   Forall (fun p' => p' ∉ (usedPIDsAct a)) (map snd l) \/
   (exists v1 v2 p', a = ASpawn p' v1 v2 /\ p' ∈ (map snd l) /\ p' ∉ usedPIDsVal v1 ∪ usedPIDsVal v2)).
Proof.
  induction l; intros; inv H0.
  * left. constructor.
  * eapply fresh_pid_is_not_in_step in H as P; eauto.
    destruct P.
    - destruct n' as [eth' Π']. eapply IHl with (a := renamePIDAct from to a0) in H3.
      2: { apply renamePID_is_preserved_node_semantics; eauto.
           by apply appearsEther_isUsedEther.
         }
      destruct H3.
      + left. simpl. constructor. by simpl.
        {
          apply Forall_forall. rewrite Forall_forall in H1. intros.
          apply H1 in H2.
        }
      + destruct_hyps. subst. simpl in *.
        right. do 3 eexists. split. reflexivity.
        split. 1: set_solver.
        assumption.
      + 
    - right. destruct_hyps. do 3 eexists. split. eassumption.
      split. 1: set_solver. assumption.
Qed. *)

(* TODO: generalize this *)
Fixpoint collapse_list (l : list (PID * PID)) (a : Action) :=
match l with
| (from, to)::l => to ∉ usedPIDsAct a /\ collapse_list l (renamePIDAct from to a)
| [] => True
end.

Theorem renamePIDlist_is_preserved_node_semantics :
  forall l O eth eth' Π Π' a ι,
    (eth, Π) -[a | ι]ₙ-> (eth', Π') with O ->
      (* Forall (fun '(from, to) => to ∉(usedPIDsAct a)(*  /\
                                 ¬ isUsedEther to eth *) (* /\ *)
                                 (* ¬ isUsedPool to Π /\ *)
                                 (* to ∉ O *)) l -> *)
      collapse_list l a ->
      (* NoDup (map snd l) -> *)
      well_formed O (eth, Π) l ->
      (renamePIDs renamePIDEther l eth, renamePIDs renamePIDPool l Π)
    -[renamePIDs renamePIDAct l a | renamePIDs renamePIDPID_sym l ι]ₙ->
      (renamePIDs renamePIDEther l eth', renamePIDs renamePIDPool l Π') with O.
Proof.
  induction l; intros. by assumption.
  destruct a. simpl. inv H1.
  inv H0. destruct_hyps.
  eapply IHl; auto.
  {
    apply renamePID_is_preserved_node_semantics; try assumption.
    by apply appearsEther_isUsedEther.
  }
  (* rewrite Forall_forall in H4. apply Forall_forall. intros.
  destruct x. apply H4 in H0 as P. simpl in *. (*  (* clear H4. *) destruct_hyps. split_and!. *)
  * destruct (decide (p2 = p)).
    - subst. admit. (* P -> usedPIDsAct a0.[[p->p0]] = usedPIDsAct a0 *)
    - admit. (* This case is doable *)
(*   * intro. apply isUsedEther_rename_same_neq in H6. congruence.
    - intro. subst. apply isUsedEther_rename_same_old in H6.
      congruence.
    - intro. subst. admit.
  * intro. apply isUsedPool_rename_same_neq in H11. congruence.
    - intro. subst. apply isUsedPool_rename_same_old in H11.
      congruence.
    - intro. subst. apply H4. apply elem_of_map_iff. exists (p1, p0). split; auto.
  * set_solver.
 *) *)
Qed.

(*
Theorem renamePIDlist_is_preserved_node_semantics_weakened :
  forall l O eth eth' Π Π' a ι,
    (eth, Π) -[a | ι]ₙ-> (eth', Π') with O ->
      Forall (fun '(from, to) => (to ∈ (usedPIDsAct a) -> exists new, new ≠ to /\ (to, new) ∈ l /\ new ∉ (usedPIDsAct a)) /\
                                 ¬ isUsedEther to eth /\
                                 ¬ isUsedPool to Π /\
                                 to ∉ O) l ->
      NoDup (map snd l) ->
      (renamePIDs renamePIDEther l eth, renamePIDs renamePIDPool l Π)
    -[renamePIDs renamePIDAct l a | renamePIDs renamePIDPID_sym l ι]ₙ->
      (renamePIDs renamePIDEther l eth', renamePIDs renamePIDPool l Π') with O.
Proof.
  induction l; intros. by assumption.
  destruct a. simpl. inv H1.
  inv H0. destruct_hyps.
  destruct (gset_elem_of_dec p0 (usedPIDsAct a0)).
  {
    apply H0 in e. destruct e as [new [Heq [Hin Hfst]]].
    apply elem_of_cons in Hin as [|].
    * inv H7. congruence.
    * simpl in Hfst.
      (* p0 <-> new, i.e., p <-> p0 could be replaced by p <-> new *)
      admit.
  }
  eapply IHl; auto.
  {
    apply renamePID_is_preserved_node_semantics; try assumption.
  }
  rewrite Forall_forall in H6. apply Forall_forall. intros.
  destruct x. apply H6 in H7 as H7'. simpl in *. clear H6. destruct_hyps. split_and!.
  * destruct (decide (p2 = p)).
    - subst. admit. (* H6 -> usedPIDsAct a0.[[p->p0]] = usedPIDsAct a0 *)
    - admit. (* This case is doable *)
  * intro. apply isUsedEther_rename_same_neq in H11. congruence.
    - intro. subst. apply isUsedEther_rename_same_old in H11.
      congruence.
    - intro. subst. apply H4. apply elem_of_map_iff. exists (p1, p0). split; auto.
  * intro. apply isUsedPool_rename_same_neq in H11. congruence.
    - intro. subst. apply isUsedPool_rename_same_old in H11.
      congruence.
    - intro. subst. apply H4. apply elem_of_map_iff. exists (p1, p0). split; auto.
  * set_solver.
Admitted.*)

Lemma well_formed_preserved :
  forall l O n n' a ι,
    well_formed O n l ->
    collapse_list l a ->
    n -[a | ι]ₙ-> n' with O ->
    well_formed O n' l.
Proof.
  induction l; intros. constructor. destruct n'.
  inv H. inv H0. eapply IHl in H4; eauto.
  2: { eapply renamePID_is_preserved_node_semantics. exact H1.
       all: try assumption.
       by apply appearsEther_isUsedEther.
     }
  constructor; auto.
  * eapply not_isUsedPool_step; eauto.
  * eapply appearsEther_step in H1; eauto.
Qed.

Lemma renamePIDPID_1 :
  forall a b, renamePIDPID a b a = b.
Proof.
  unfold renamePIDPID. intros. by rewrite Nat.eqb_refl.
Qed.

Lemma renamePIDPID_sym_1 :
  forall a b, renamePIDPID_sym a b a = b.
Proof.
  unfold renamePIDPID_sym. intros. by rewrite Nat.eqb_refl.
Qed.

Lemma well_formed_collapse :
  forall l O n,
    well_formed O n l ->
    forall a, collapse_list l a.
Proof.
  induction l; intros; simpl.
  trivial.
  destruct a. inv H. eapply IHl in H3. split. 2: eassumption.
  
Qed.

Lemma fresh_pid_list_is_not_in_step :
  forall l O n n' a ι,
  n -[ a | ι ]ₙ-> n' with O ->
   well_formed O n l ->
   collapse_list l a \/
   (exists v1 v2 p', a = ASpawn p' v1 v2 /\ exists new, collapse_list ((p', new) :: l) a /\ well_formed O n ((p', new) :: l)).
   (* p' ∈ (map snd l) /\ p' ∉ usedPIDsVal v1 ∪ usedPIDsVal v2) *)
Proof.
  induction l; intros; inv H0.
  * left. constructor.
  * eapply fresh_pid_is_not_in_step in H as P; eauto.
    destruct P.
    - destruct n' as [eth' Π']. eapply IHl with (a := renamePIDAct from to a0) in H3.
      2: { apply renamePID_is_preserved_node_semantics; eauto.
           by apply appearsEther_isUsedEther.
         }
      destruct H3.
      + left. simpl. constructor. by simpl.
        {
          assumption.
        }
      + destruct_hyps. simpl in *.
        destruct_hyps.
        left. split. assumption.
        destruct a0; inv H1.
        simpl in *. admit.
    - right. destruct_hyps. subst. do 3 eexists. split. reflexivity.
      eexists. split.
      + constructor.
        ** simpl. admit. (* freshness *)
        ** constructor; simpl.
           -- rewrite renamePIDPID_1.
              rewrite isNotUsed_renamePID_val. 2: set_solver.
              rewrite isNotUsed_renamePID_val. 2: set_solver.
              admit. (* freshness *)
           -- repeat rewrite renamePIDPID_1.
              repeat rewrite double_PIDrenaming_val.
           
      +
Qed.


Theorem rename_bisim :
  forall O eth Π (l : list (PID * PID)),
    ether_wf eth ->
    (* Forall (fun p' => ¬ appearsEther p' eth) (map snd l) ->
    (* p' ∉ dom Π -> *)
    (* (p ∈ dom Π \/ (¬isUsedEther p eth /\ ¬isUsedPool p Π)) -> *)
    (* (p ∈ dom Π \/ (¬isUsedEther p eth /\ ¬isUsedPool p Π)) -> *)
    (* ~isUntaken p (eth, Π) -> *)
    Forall (fun p' => ¬isUsedPool p' Π) (map snd l) ->
    Forall (fun p => p ∉ O) (map fst l) ->
    Forall (fun p => p ∉ O) (map snd l) -> *)
    (* Forall (fun '(from, to) => ¬ appearsEther to eth /\ ¬isUsedPool to Π /\ to ∉ O /\ from ∉ O) l ->
    NoDup (map snd l) -> *)
    well_formed O (eth, Π) l ->
    (eth, Π) ~ (renamePIDs renamePIDEther l eth, renamePIDs renamePIDPool l Π) observing O.
Proof.
  cofix IH.
  intros. constructor; auto.
  * apply renameList_preCompatible_sym. assumption.
  * simpl. by apply ether_wf_renameList.
  * intros. destruct A' as [eth' Π'].
    (* eapply fresh_pid_list_is_not_in_step with (l := map snd l) in H1 as HD.
    2: {
      simpl. apply Forall_map. clear -H0.
      eapply Forall_impl. eassumption. intros. destruct x; simpl in *.
      set_solver.
    }
    destruct HD. *)
    (* epose proof (List.Forall_Exists_dec (λ '(_, to), to ∉ usedPIDsAct a) _ l). *)
    
    Unshelve. 2: {
      destruct x. simpl.
      destruct (gset_elem_of_dec p0 (usedPIDsAct a)).
      * right. set_solver.
      * left. assumption.
    }
    destruct H2.
    {
      apply renamePIDlist_is_preserved_node_semantics with (l := l) in H1 as D.
      3: clear IH; assumption.
      2: {
        (* clear IH; assumption. *) (* 
        rewrite Forall_forall in f. rewrite Forall_forall in H3.
        apply Forall_forall. intros. destruct x.
        apply H0 in H4 as P1. destruct_hyps.
        assert (p0 ∈ map snd l) by set_solver.
        apply H3 in H9. split_and!; try assumption.
        by apply appearsEther_isUsedEther.
      } *)
      }
      do 2 eexists. split.
      eapply n_trans. exact D. apply n_refl.
      apply IH; clear IH.
      * eapply n_trans in H1. 2:apply n_refl.
        by apply ether_wf_preserved in H1.
      * by eapply well_formed_preserved. (* 
      * rewrite Forall_forall in H0. rewrite Forall_forall in H3.
        apply Forall_forall. intros. destruct x.
        apply H0 in H4 as P1. destruct_hyps.
        assert (p0 ∈ map snd l) by set_solver.
        apply H3 in H9. split_and!; try assumption.
        eapply appearsEther_step in H2. exact H2. all: try assumption.
        eapply not_isUsedPool_step in H2. exact H2. all: assumption.
      * assumption. *)
    }
    { (* renaming is needed here *)
      (* destruct H3 as [v1 [v2 [taken ?]]]. destruct_hyps.
      subst. *)
      rewrite Exists_exists in e. destruct e. destruct_hyps. destruct x.
      assert (exists new, (* new ∉ map snd l /\
                          new ∉ O /\
                          ¬appearsEther new eth /\
                          ¬isUsedPool new Π /\
                          new ≠ taken /\
                          new ∉ usedPIDsVal v1 ∪ usedPIDsVal v2 *)
                          well_formed O (eth, Π) ((p0, new)::l)). {
        clear IH. eexists. constructor; auto; admit.
      }
      destruct H4 as [new ?].
      (* assert (Forall (fun p => p ∉ usedPIDsVal v1 ∪ usedPIDsVal v2) (map snd l)) as HP. {
        (* the PIDs are not used in the spawn values which we use to rename with. *)
        clear -H0 H2.
        rewrite Forall_forall in H0. apply Forall_forall. intros.
        rewrite elem_of_map_iff in H. destruct_hyps. destruct x0. simpl in *.
        apply H0 in H1. subst. destruct_hyps.
        apply fresh_pid_is_not_in_step with (p' := x) in H2; auto.
        destruct H2. set_solver.
        destruct_hyps. by inv H2.
      } *)
      apply renamePIDlist_is_preserved_node_semantics with (l := (p0, new) :: l) in H1 as D.
      3: {
        clear IH. assumption.
      }
      2: {
      2: {
        clear IH.
        rewrite Forall_forall in H0.
        apply Forall_forall. intros. destruct x.
        apply elem_of_cons in H11 as [|].
        * simpl. inv H11. split_and!; try assumption.
          set_solver.
          by apply appearsEther_isUsedEther.
        * apply H0 in H11 as P1. destruct_hyps.
          assert (p0 ∈ map snd l) by set_solver.
          split_and!; try assumption.
          - simpl. intros.
            assert (p0 = taken \/ p0 ∈ usedPIDsVal v1 ∪ usedPIDsVal v2) as X by set_solver.
            destruct X.
            + subst. exists new. split_and!; auto.
              apply elem_of_cons; by left. set_solver.
            + exfalso. rewrite Forall_forall in HP. apply HP in H16. congruence.
          - by apply appearsEther_isUsedEther.
      }
      replace (renamePIDs renamePIDEther l eth) with
         (renamePIDs renamePIDEther ((taken, new)::l) eth). 2: {
         simpl. rewrite does_not_appear_renamePID_ether; auto.
         rewrite Forall_forall in H0. clear-H0 H4.
         rewrite elem_of_map_iff in H4; destruct_hyps. destruct x.
         simpl in *. apply H0 in H1. subst. apply H1.
      }
      replace (renamePIDs renamePIDPool l Π) with
         (renamePIDs renamePIDPool ((taken, new)::l) Π). 2: {
         simpl. rewrite isNotUsed_renamePID_pool; auto.
         rewrite Forall_forall in H0. clear-H0 H4.
         rewrite elem_of_map_iff in H4; destruct_hyps. destruct x.
         simpl in *. apply H0 in H1. subst. apply H1.
      }
      do 2 eexists. split. eapply n_trans. exact D. apply n_refl.
(*       replace (renamePIDs renamePIDEther ((taken, new) :: l) eth') with
        (renamePIDs renamePIDEther ((taken, new) :: map (prod_map id (renamePIDPID_sym taken new) ) l) eth').
            replace (renamePIDs renamePIDPool ((taken, new) :: l) Π') with
        (renamePIDs renamePIDPool ((taken, new) :: map (prod_map id (renamePIDPID_sym taken new) ) l) Π'). *)
      apply IH; clear IH.
      * eapply n_trans in H2. 2:apply n_refl.
        by apply ether_wf_preserved in H2.
      * clear D.
        rewrite Forall_forall in H0.
        apply Forall_forall. intros. destruct x.
        apply elem_of_cons in H11 as [|].
        - simpl. inv H11. split_and!; try assumption.
          eapply appearsEther_step in H2. exact H2. all: simpl.
          set_solver.
          assumption.
          eapply not_isUsedPool_step in H2. eassumption. assumption.
          simpl. set_solver.
          rewrite elem_of_map_iff in H4. destruct_hyps. destruct x; subst.
          simpl in *. apply H0 in H11. apply H11.
        - apply elem_of_map_iff in H11. destruct_hyps. destruct x. inv H11.
          apply H0 in H12 as D. destruct_hyps.
          split_and!.
          + destruct (decide (n = taken)).
            ** subst. unfold renamePIDPID_sym. rewrite Nat.eqb_refl.
               eapply appearsEther_step in H2. exact H2. set_solver. assumption.
            ** assert (n ≠ new). {
                 intro. subst. apply H3. apply elem_of_map_iff.
                 eexists. split. 2: exact H12. reflexivity.
               }
               unfold renamePIDPID_sym. repeat case_match; eqb_to_eq; try congruence.
               eapply appearsEther_step in H2. exact H2.
               simpl. rewrite Forall_forall in HP.
               assert (n ∈ map snd l). {
                 apply elem_of_map_iff. eexists. split. 2: exact H12. reflexivity.
               }
               apply HP in H19. set_solver.
               assumption.
          + destruct (decide (n = taken)).
            ** subst. unfold renamePIDPID_sym. rewrite Nat.eqb_refl.
               eapply not_isUsedPool_step in H2. exact H2. assumption. set_solver.
            ** assert (n ≠ new). {
                 intro. subst. apply H3. apply elem_of_map_iff.
                 eexists. split. 2: exact H12. reflexivity.
               }
               unfold renamePIDPID_sym. repeat case_match; eqb_to_eq; try congruence.
               eapply not_isUsedPool_step in H2. exact H2. assumption.
               simpl. rewrite Forall_forall in HP.
               assert (n ∈ map snd l). {
                 apply elem_of_map_iff. eexists. split. 2: exact H12. reflexivity.
               }
               apply HP in H19. set_solver.
          + destruct (decide (n = taken)).
            ** subst. unfold renamePIDPID_sym. rewrite Nat.eqb_refl. assumption.
            ** assert (n ≠ new). {
                 intro. subst. apply H3. apply elem_of_map_iff.
                 eexists. split. 2: exact H12. reflexivity.
               }
               unfold renamePIDPID_sym. repeat case_match; eqb_to_eq; try congruence.
          + assumption.
      * simpl. constructor.
        - rewrite map_map. intro. apply elem_of_map_iff in H11. destruct_hyps.
          destruct x. simpl in *. unfold renamePIDPID_sym in H11.
          repeat case_match; eqb_to_eq; subst; try congruence.
          
        -
    }
  * simpl. intros.
    exists (renamePIDs renamePIDPID_sym l source), []. eexists.
    split.
    {
      apply n_refl.
    }
    {
      simpl.
      assert ((renamePIDs renamePIDPID_sym l source, dest) =
           ((prod_map (renamePIDs renamePIDPID_sym l) (renamePIDs renamePIDPID_sym l)) (source, dest))). {
        cbn. f_equal. clear -H0 H1 H2.
        generalize dependent dest.
        induction l. reflexivity.
        inv H1. inv H0. destruct a. simpl.
        intros. rewrite <- IHl; auto.
        * unfold renamePIDPID_sym.
          destruct_hyps. repeat case_match;eqb_to_eq; subst; try congruence.
        * unfold renamePIDPID_sym.
          destruct_hyps. repeat case_match;eqb_to_eq; subst; try congruence.
      }
      setoid_rewrite H3.
      {
        clear. revert eth source dest.
        induction l; intros; simpl.
        * apply option_biforall_refl. intros. apply Signal_eq_refl.
        * destruct a. eapply option_biforall_trans. 3: apply IHl.
          - apply Signal_eq_trans.
          - unfold renamePIDEther. replace (if source =? _ then _ else _, _) with
              (prod_map (renamePIDPID_sym p p0) (renamePIDPID_sym p p0) (source, dest)) by reflexivity.
            setoid_rewrite lookup_kmap; auto.
            setoid_rewrite lookup_fmap.
            simpl. destruct (eth !! _) eqn:P.
            {
              setoid_rewrite P. simpl.
              eapply forall_biforall with (d1 := SUnlink) (d2 := SUnlink).
              1: by rewrite map_length.
              intros. rewrite map_nth with (d:= SUnlink).
              by apply Signal_eq_renamePID.
            }
            {
              setoid_rewrite P. simpl. trivial.
            }
      }
    }
  * admit.
  * admit.
Qed.



















Theorem rename_bisim_old :
  forall O eth Π (l : list (PID * PID)),
    ether_wf eth ->
    (* Forall (fun p' => ¬ appearsEther p' eth) (map snd l) ->
    (* p' ∉ dom Π -> *)
    (* (p ∈ dom Π \/ (¬isUsedEther p eth /\ ¬isUsedPool p Π)) -> *)
    (* (p ∈ dom Π \/ (¬isUsedEther p eth /\ ¬isUsedPool p Π)) -> *)
    (* ~isUntaken p (eth, Π) -> *)
    Forall (fun p' => ¬isUsedPool p' Π) (map snd l) ->
    Forall (fun p => p ∉ O) (map fst l) ->
    Forall (fun p => p ∉ O) (map snd l) -> *)
    Forall (fun '(from, to) => ¬ appearsEther to eth /\ ¬isUsedPool to Π /\ to ∉ O /\ from ∉ O) l ->
    NoDup (map snd l) ->
    (eth, Π) ~ (renamePIDs renamePIDEther l eth, renamePIDs renamePIDPool l Π) observing O.
Proof.
  cofix IH.
  intros. constructor; auto.
  * apply renameList_preCompatible_sym. 2: assumption.
    eapply Forall_impl. 1: eassumption.
    intros. destruct x. clear-H2. intuition.
    by apply isUsedEther_appearsEther in H2.
  * simpl. by apply ether_wf_renameList.
  * intros. destruct A' as [eth' Π'].
    eapply fresh_pid_list_is_not_in_step with (l := map snd l) in H2 as HD.
    2: {
      simpl. apply Forall_map. clear -H0.
      eapply Forall_impl. eassumption. intros. destruct x; simpl in *.
      set_solver.
    }
    destruct HD.
    {
      apply renamePIDlist_is_preserved_node_semantics with (l := l) in H2 as D.
      3: clear IH; assumption.
      2: {
        clear IH.
        rewrite Forall_forall in H0. rewrite Forall_forall in H3.
        apply Forall_forall. intros. destruct x.
        apply H0 in H4 as P1. destruct_hyps.
        assert (p0 ∈ map snd l) by set_solver.
        apply H3 in H9. split_and!; try assumption.
        by apply appearsEther_isUsedEther.
      }
      do 2 eexists. split.
      eapply n_trans. exact D. apply n_refl.
      apply IH; clear IH.
      * eapply n_trans in H2. 2:apply n_refl.
        by apply ether_wf_preserved in H2.
      * rewrite Forall_forall in H0. rewrite Forall_forall in H3.
        apply Forall_forall. intros. destruct x.
        apply H0 in H4 as P1. destruct_hyps.
        assert (p0 ∈ map snd l) by set_solver.
        apply H3 in H9. split_and!; try assumption.
        eapply appearsEther_step in H2. exact H2. all: try assumption.
        eapply not_isUsedPool_step in H2. exact H2. all: assumption.
      * assumption.
    }
    { (* renaming is needed here *)
      destruct H3 as [v1 [v2 [taken ?]]]. destruct_hyps.
      subst.
      assert (exists new, new ∉ map snd l /\
                          new ∉ O /\
                          ¬appearsEther new eth /\
                          ¬isUsedPool new Π /\
                          new ≠ taken /\
                          new ∉ usedPIDsVal v1 ∪ usedPIDsVal v2). {
        clear IH. admit.
      }
      destruct H3 as [new ?]. destruct_hyps.
      assert (Forall (fun p => p ∉ usedPIDsVal v1 ∪ usedPIDsVal v2) (map snd l)) as HP. {
        (* the PIDs are not used in the spawn values which we use to rename with. *)
        clear -H0 H2.
        rewrite Forall_forall in H0. apply Forall_forall. intros.
        rewrite elem_of_map_iff in H. destruct_hyps. destruct x0. simpl in *.
        apply H0 in H1. subst. destruct_hyps.
        apply fresh_pid_is_not_in_step with (p' := x) in H2; auto.
        destruct H2. set_solver.
        destruct_hyps. by inv H2.
      }
      apply renamePIDlist_is_preserved_node_semantics_weakened with (l := (taken, new) :: l) in H2 as D.
      3: {
        clear IH. constructor; assumption.
      }
      2: {
        clear IH.
        rewrite Forall_forall in H0.
        apply Forall_forall. intros. destruct x.
        apply elem_of_cons in H11 as [|].
        * simpl. inv H11. split_and!; try assumption.
          set_solver.
          by apply appearsEther_isUsedEther.
        * apply H0 in H11 as P1. destruct_hyps.
          assert (p0 ∈ map snd l) by set_solver.
          split_and!; try assumption.
          - simpl. intros.
            assert (p0 = taken \/ p0 ∈ usedPIDsVal v1 ∪ usedPIDsVal v2) as X by set_solver.
            destruct X.
            + subst. exists new. split_and!; auto.
              apply elem_of_cons; by left. set_solver.
            + exfalso. rewrite Forall_forall in HP. apply HP in H16. congruence.
          - by apply appearsEther_isUsedEther.
      }
      replace (renamePIDs renamePIDEther l eth) with
         (renamePIDs renamePIDEther ((taken, new)::l) eth). 2: {
         simpl. rewrite does_not_appear_renamePID_ether; auto.
         rewrite Forall_forall in H0. clear-H0 H4.
         rewrite elem_of_map_iff in H4; destruct_hyps. destruct x.
         simpl in *. apply H0 in H1. subst. apply H1.
      }
      replace (renamePIDs renamePIDPool l Π) with
         (renamePIDs renamePIDPool ((taken, new)::l) Π). 2: {
         simpl. rewrite isNotUsed_renamePID_pool; auto.
         rewrite Forall_forall in H0. clear-H0 H4.
         rewrite elem_of_map_iff in H4; destruct_hyps. destruct x.
         simpl in *. apply H0 in H1. subst. apply H1.
      }
      do 2 eexists. split. eapply n_trans. exact D. apply n_refl.
      replace (renamePIDs renamePIDEther ((taken, new) :: l) eth') with
        (renamePIDs renamePIDEther ((taken, new) :: map (prod_map id (renamePIDPID_sym taken new) ) l) eth').
            replace (renamePIDs renamePIDPool ((taken, new) :: l) Π') with
        (renamePIDs renamePIDPool ((taken, new) :: map (prod_map id (renamePIDPID_sym taken new) ) l) Π').
      apply IH; clear IH.
      * eapply n_trans in H2. 2:apply n_refl.
        by apply ether_wf_preserved in H2.
      * clear D.
        rewrite Forall_forall in H0.
        apply Forall_forall. intros. destruct x.
        apply elem_of_cons in H11 as [|].
        - simpl. inv H11. split_and!; try assumption.
          eapply appearsEther_step in H2. exact H2. all: simpl.
          set_solver.
          assumption.
          eapply not_isUsedPool_step in H2. eassumption. assumption.
          simpl. set_solver.
          rewrite elem_of_map_iff in H4. destruct_hyps. destruct x; subst.
          simpl in *. apply H0 in H11. apply H11.
        - apply elem_of_map_iff in H11. destruct_hyps. destruct x. inv H11.
          apply H0 in H12 as D. destruct_hyps.
          split_and!.
          + destruct (decide (n = taken)).
            ** subst. unfold renamePIDPID_sym. rewrite Nat.eqb_refl.
               eapply appearsEther_step in H2. exact H2. set_solver. assumption.
            ** assert (n ≠ new). {
                 intro. subst. apply H3. apply elem_of_map_iff.
                 eexists. split. 2: exact H12. reflexivity.
               }
               unfold renamePIDPID_sym. repeat case_match; eqb_to_eq; try congruence.
               eapply appearsEther_step in H2. exact H2.
               simpl. rewrite Forall_forall in HP.
               assert (n ∈ map snd l). {
                 apply elem_of_map_iff. eexists. split. 2: exact H12. reflexivity.
               }
               apply HP in H19. set_solver.
               assumption.
          + destruct (decide (n = taken)).
            ** subst. unfold renamePIDPID_sym. rewrite Nat.eqb_refl.
               eapply not_isUsedPool_step in H2. exact H2. assumption. set_solver.
            ** assert (n ≠ new). {
                 intro. subst. apply H3. apply elem_of_map_iff.
                 eexists. split. 2: exact H12. reflexivity.
               }
               unfold renamePIDPID_sym. repeat case_match; eqb_to_eq; try congruence.
               eapply not_isUsedPool_step in H2. exact H2. assumption.
               simpl. rewrite Forall_forall in HP.
               assert (n ∈ map snd l). {
                 apply elem_of_map_iff. eexists. split. 2: exact H12. reflexivity.
               }
               apply HP in H19. set_solver.
          + destruct (decide (n = taken)).
            ** subst. unfold renamePIDPID_sym. rewrite Nat.eqb_refl. assumption.
            ** assert (n ≠ new). {
                 intro. subst. apply H3. apply elem_of_map_iff.
                 eexists. split. 2: exact H12. reflexivity.
               }
               unfold renamePIDPID_sym. repeat case_match; eqb_to_eq; try congruence.
          + assumption.
      * simpl. constructor.
        - rewrite map_map. intro. apply elem_of_map_iff in H11. destruct_hyps.
          destruct x. simpl in *. unfold renamePIDPID_sym in H11.
          repeat case_match; eqb_to_eq; subst; try congruence.
          
        -
    }
  * simpl. intros.
    exists (renamePIDs renamePIDPID_sym l source), []. eexists.
    split.
    {
      apply n_refl.
    }
    {
      simpl.
      assert ((renamePIDs renamePIDPID_sym l source, dest) =
           ((prod_map (renamePIDs renamePIDPID_sym l) (renamePIDs renamePIDPID_sym l)) (source, dest))). {
        cbn. f_equal. clear -H0 H1 H2.
        generalize dependent dest.
        induction l. reflexivity.
        inv H1. inv H0. destruct a. simpl.
        intros. rewrite <- IHl; auto.
        * unfold renamePIDPID_sym.
          destruct_hyps. repeat case_match;eqb_to_eq; subst; try congruence.
        * unfold renamePIDPID_sym.
          destruct_hyps. repeat case_match;eqb_to_eq; subst; try congruence.
      }
      setoid_rewrite H3.
      {
        clear. revert eth source dest.
        induction l; intros; simpl.
        * apply option_biforall_refl. intros. apply Signal_eq_refl.
        * destruct a. eapply option_biforall_trans. 3: apply IHl.
          - apply Signal_eq_trans.
          - unfold renamePIDEther. replace (if source =? _ then _ else _, _) with
              (prod_map (renamePIDPID_sym p p0) (renamePIDPID_sym p p0) (source, dest)) by reflexivity.
            setoid_rewrite lookup_kmap; auto.
            setoid_rewrite lookup_fmap.
            simpl. destruct (eth !! _) eqn:P.
            {
              setoid_rewrite P. simpl.
              eapply forall_biforall with (d1 := SUnlink) (d2 := SUnlink).
              1: by rewrite map_length.
              intros. rewrite map_nth with (d:= SUnlink).
              by apply Signal_eq_renamePID.
            }
            {
              setoid_rewrite P. simpl. trivial.
            }
      }
    }
  * admit.
  * admit.
Qed.


Lemma bisim_congr :
  forall U Π Π' eth eth', (eth, Π) ~ (eth', Π') using U ->
    forall Π2, (eth, Π ∪ Π2) ~ (eth', Π' ∪ Π2) using U.
Proof.
  cofix IH. intros. inv H. constructor; auto; simpl in *.
  * clear -H0. destruct H0. split; unfold preCompatibleNodes in *; intros.
    - apply isUntaken_comp in H1 as [H1_1 H1_2].
      apply H in H1_1.
      assert (isUntaken ι (eth', Π2)). {
        destruct H1_1, H1_2. split; auto.
      }
      now apply isUntaken_comp.
    - apply isUntaken_comp in H1 as [H1_1 H1_2].
      apply H0 in H1_1.
      assert (isUntaken ι (eth, Π2)). {
        destruct H1_1, H1_2. split; auto.
      }
      now apply isUntaken_comp.
  * clear H4 H5 H6. intros. destruct A'.
    apply step_in_comp in H as H'. destruct H' as [[Π1' [? ?]] | [Π2' [? ?]]].
    - subst. apply H3 in H4 as H4'. destruct_hyps. destruct x as [e' Π1''].
      (* (* At this point, we need renamings :( - or to know what PIDs are
         spawned by Π *)
      Print reductionPreCompatibility.
      (* spawns in x0 should be distinct from:
         - syntactically used PIDs in Π2 - for goal 3
         - ι0 -> if a = send(ι, ι0 <- destination, msg)
         - We also need a proof that (eth, Π) ~ (eth[x|->y], Π[x|->y])
      *)
      exists (e', Π1'' ∪ Π2), x0. split. 2: split. 3: split.
      4: { apply IH. assumption. }
      3: apply reductions_are_preserved_by_comp; auto.
      3: {
        intros. destruct H6 as [H6 _]. rewrite Forall_forall in H6.
        apply H6 in H9. unfold isUntaken in H9. simpl in *.
      } *)
      admit.
    - subst. exists (e, Π' ∪ Π2'), [(a, ι)]. split_and!.
      + split.
        ** destruct a; auto. simpl. constructor; auto. intro.
           eapply (no_spawn_unTaken (eth, Π ∪ Π2)). eapply n_trans. eassumption.
           apply n_refl. 2: cbn; left; reflexivity.
           apply isUntaken_comp in H5 as [? ?]. apply H0 in H5.
           apply isUntaken_comp; split; auto.
           (* ι0 should be Untaken wrt. eth *)
           destruct H5, H6. split; simpl in *; auto.
        ** intros; simpl in *; destruct a; auto; simpl in *.
           destruct_or!; auto. split. 2: split; auto.
           subst.
           (* ISSUE: we do not know, whether Π' uses ι0 *)
           (* is it okay to assume, that Π2 does not communicate to 
              PIDs in the domain of Π/Π' -> NO!

              is it okay to assume, that Π2 does not communicate to
              PIDs in ((dom Π ∪ dom Π') \ (dom Π ∩ dom Π')). Probably not.
            *)
           admit.
      + split.
        ** destruct a; auto. simpl. constructor; auto. intro.
           eapply (no_spawn_unTaken (eth, Π ∪ Π2)). eapply n_trans. eassumption.
           apply n_refl. 2: cbn; left; reflexivity.
           apply isUntaken_comp in H5 as [? ?].
           apply isUntaken_comp; split; auto.
        ** intros; simpl in *; destruct a; auto; simpl in *.
           destruct_or!; auto. split. 2: split; auto.
           subst.
           (* ISSUE: we do not know, whether Π uses ι0
              BOTTOMLINE: we should specify where can Π2 send messages?
            *)
           admit.
      + econstructor.
        apply reduction_is_preserved_by_comp_r. (* eassumption. *) admit. admit. admit. admit.
      + admit.
(*     - subst. exists (e, Π ∪ Π2'), [(a, ι)]. split_and!.
      split.
      + destruct a; auto. simpl. constructor; auto. intro.
        eapply (no_spawn_unTaken (eth, Π ∪ Π2)). eapply n_trans. eassumption.
        apply n_refl. 2: cbn; left; reflexivity.
        apply isUntaken_comp in H5 as [? ?]. apply H0 in H5.
        apply isUntaken_comp; split; auto.
        (* ι0 should be Untaken wrt. eth *)
        destruct H5, H6. split; simpl in *; auto.
      + intros; simpl in *; destruct a; auto; simpl in *.
        destruct_or!; auto. split. 2: split; auto.
        subst.
        (* ISSUE: we do not know, whether Π' uses ι0 *)
        admit.
      4: { apply IH. apply barbedBisim_refl. } *)
Abort.
















Theorem action_chainable:
  forall l n n', n -[l]ₙ->* n' ->
    (* (forall ι : PID, In ι (PIDsOf sendPIDOf l) -> n'.2 ι <> None) -> *)
    (* (forall ι ι' : PID, n.2 ι' = None -> n.1 ι ι' = []) -> *)
    forall a ι n'', n -[a | ι]ₙ-> n'' ->
      In (a, ι) l \/ 
      exists n''' a' ι', n' -[a' | ι']ₙ-> n''' /\
               reductionPreCompatibility n n' [(a, ι)] [(a', ι')] /\
               reductionPreCompatibility n' n [(a', ι')] [(a, ι)].
Proof.
  induction l using list_length_ind; intros.
  
  (* induction l using list_length_ind; intros.
  destruct (length l) eqn:Hl.
  * apply length_zero_iff_nil in Hl. subst.
    inv H0. right. exists n'', a, ι.
    split; auto.
    split; eapply reductionPreCompatibility_refl; eassumption.
  * simpl in Hl. apply eq_sym, last_element_exists in Hl as Hl'.
    destruct Hl' as [l' [[a' ι'] EQ]]. subst.
    apply split_reduction in H0 as [n'0 [D1 D2]].
    rewrite app_length in Hl. simpl in Hl.
    specialize (H l' ltac:(lia) _ _ D1 _ _ _ H1). destruct H.
    - left. apply elem_of_app. now left.
    - rename n'0 into A. rename n' into B.
      destruct_hyps. inv D2. inv H9. *)
Abort.

(* Theorem normalisation :
  forall n n' l,
    ether_wf n.1 ->
    (forall ι, In ι (PIDsOf sendPIDOf l) ->
      n'.2 ι <> None) -> (* Signals shouldn't be sent to the "world" *)
    (* (forall ι source dest s, In (AArrive source dest s, ι) l ->
                             n'.2 ι <> None) -> (* Signals should not
                                                   arrive to the "world" *) *)
    (forall ι ι', n.2 ι' = None -> n.1 ι ι' = []) ->
    n -[l]ₙ->* n' ->
    n ~ n' using (PIDsOf spawnPIDOf l).
Proof.
  intros. apply barbedExpansion_implies_bisim.
  generalize dependent n. generalize dependent n'. revert l. cofix IH. intros.
  constructor; auto.
  1: split; [ now eapply reduction_produces_preCompatibleNodes; eassumption
            | now eapply reduction_produces_preCompatibleNodes_sym; eassumption].
  1: now apply ether_wf_preserved in H2.
  * intros. Print reductionPreCompatibility. Print Action. *)
    
  
  (* exists n', [].
    split. 2: split. 3: split. 4: split. all: simpl.
    - split.
      + cbn. destruct a; simpl; try now constructor.
        constructor. 2: constructor.
        admit.
      + intros. admit.
    - admit.
    - lia.
    - admit.
    - admit. *)
(*   * intros. exists B', (l ++ [(a, ι)]).
    split. 2: split. 3: split. 4: split. all: simpl.
    - split.
      + cbn. destruct a; simpl; constructor; auto.
        intro. destruct H4.
        eapply isUsed_no_spawn. 2: exact H5.
        eapply closureNodeSem_trans. exact H2. econstructor 2. exact H3. constructor.
        unfold PIDsOf. rewrite flat_map_app, elem_of_app. right. cbn. now left.
      + intros.
        eapply no_spawn_included_2 in H2 as H2'. 2: exact H4.
        pose proof (no_spawn_included l n n' H2 _ H2').
        split.
        ** now apply H7.
        ** split; unfold PIDsOf; rewrite flat_map_app, elem_of_app.
           -- now right.
           -- intro. firstorder.
    - split.
      + unfold PIDsOf. rewrite flat_map_app. cbn. fold (PIDsOf spawnPIDOf l).
        rewrite app_nil_r. apply Forall_app. split.
        ** rewrite Forall_forall. intros. intro. destruct H5.
           eapply no_spawn_included_2 in H2. 2: eassumption. congruence.
        ** destruct a; simpl; constructor; auto.
           intro. destruct H4.
           inv H3. 1: clear-H7; intuition; congruence.
           simpl in *. congruence.
      + intros.
        unfold PIDsOf in H5, H6. rewrite flat_map_app in H5, H6. cbn in H5, H6.
        fold (PIDsOf spawnPIDOf l) in H6. fold (PIDsOf sendPIDOf l) in H5.
        rewrite app_nil_r in *. apply not_in_app in H6 as [H6_1 H6_2].
        eapply no_spawn_included in H2 as H2'. 2: eassumption.
        split.
        ** now apply H2'.
        ** split. 2: cbn; now rewrite app_nil_r.
           clear H6_1 H6_2.
           apply elem_of_app in H5 as [? | ?]. 2: cbn; now rewrite app_nil_r in *.
           exfalso. apply H0 in H5.
           now apply H2' in H4.
    - rewrite app_length. slia.
    - eapply closureNodeSem_trans. eassumption. econstructor. eassumption. constructor.
    - apply barbedExpansion_refl.
      eapply ether_wf_preserved. 2: eassumption.
      eapply closureNodeSem_trans. eassumption. econstructor. eassumption. constructor.
  * intros. exists source.
    eapply no_spawn_included in H3. 2: eassumption. apply H3 in H4 as H4'.
    split. assumption.
    apply (H1 source) in H4.
    eapply ether_is_not_affected in H2. 2-4: eassumption.
    rewrite H2. assumption.
  * intros. exists source, l, n'. split; auto.
Abort.
 *)

