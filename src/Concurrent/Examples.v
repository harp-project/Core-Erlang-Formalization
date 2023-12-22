From CoreErlang.Concurrent Require Import BarbedBisim.

Import ListNotations.

(* BarbedBisim.v *)
Lemma preCompatibleNodes_refl :
  forall n, preCompatibleNodes n n.
Proof.
  intros. split; now destruct H.
Qed.

(* BarbedBisim.v *)
Lemma reduction_produces_preCompatibleNodes :
  forall n1 n2 l, n1 -[l]ₙ->* n2 ->
    preCompatibleNodes n1 n2.
Proof.
  intros. induction H.
  * apply preCompatibleNodes_refl.
  * eapply preCompatibleNodes_trans. 2: eassumption.
    clear -H. inv H; split; simpl; destruct H; simpl in *; try assumption.
    all: try now unfold update in *; break_match_goal; congruence.
    - repeat processpool_destruct; try congruence.
    - now apply isUsedEther_etherAdd.
    - repeat processpool_destruct; try congruence.
    - eapply isUsedEther_etherPop in H0; eauto. destruct H0.
      + assumption.
      + subst. now setoid_rewrite lookup_insert in H.
    - repeat processpool_destruct; try congruence.
    - clear H4 H0. repeat processpool_destruct; try congruence.
Qed.

(* BarbedBisim.v *)
Lemma reduction_produces_preCompatibleNodes_sym :
  forall n1 n2 l, n1 -[l]ₙ->* n2 ->
    (forall ι, In ι (PIDsOf sendPIDOf l) ->
      n2.2 !! ι <> None) ->
    preCompatibleNodes n2 n1.
Proof.
  intros. induction H.
  * apply preCompatibleNodes_refl.
  * eapply preCompatibleNodes_trans.
    1: {
      apply IHclosureNodeSem.
      intros. apply H0. unfold PIDsOf. simpl.
      apply in_app_iff. now right.
    }
    clear -H H0 H1. inv H; split; simpl; destruct H; simpl in *; try assumption.
    all: try now unfold update in *; break_match_goal; congruence.
    - repeat processpool_destruct; try congruence.
    - eapply isUsedEther_etherAdd_rev in H3.
      processpool_destruct. congruence.
      destruct (Nat.eq_dec ι' ι0). 2: assumption. subst.
      specialize (H0 ι0 ltac:(now left)).
      apply isUsedEther_no_spawn with (ι := ι0) in H1 as H1'. 2: assumption.
      eapply no_spawn_included in H1'. 2: eassumption.
      simpl in H1'. destruct H1' as [H1' _].
      repeat processpool_destruct; try congruence.
      setoid_rewrite lookup_insert_ne in H1'. 2: assumption.
      apply H1' in H. congruence.
    - repeat processpool_destruct; try congruence.
    - eapply isUsedEther_etherPop_rev in H2; eauto.
    - repeat processpool_destruct; try congruence.
    - repeat processpool_destruct; try congruence.
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
  forall n n' l, n -[l]ₙ->* n' ->
    (forall ι, In ι (PIDsOf sendPIDOf l) -> n'.2 !! ι <> None) ->
    forall source dest,
      n'.2 !! dest = None ->
      n.1 !! (source, dest) = n'.1 !! (source, dest).
Proof.
  intros n n' l H. induction H; intros; try reflexivity.
  setoid_rewrite <- IHclosureNodeSem.
  2: { intros. apply H1. unfold PIDsOf. simpl. apply in_app_iff. now right. }
  2: { assumption. }
  inversion H; subst; simpl in *; try reflexivity.
  * unfold etherAdd. destruct (decide ((ι, ι') = (source, dest))).
    - inv e. exfalso. eapply H1. left. reflexivity. assumption.
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
  forall eth eth' Π Π2 Π' a ι,
    (eth, Π ∪ Π2) -[ a | ι ]ₙ-> (eth', Π') ->
    (exists n'', (eth, Π) -[ a | ι ]ₙ-> (eth', n'') /\ (Π' = n'' ∪ Π2)) \/
    (exists n'', (eth, Π2) -[ a | ι ]ₙ-> (eth', n'') /\ (Π' = Π ∪ n'')).
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
      1: put (dom : ProcessPool -> _) on H1 as P; simpl in *; clear -P H5 H6; set_solver.
      apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as H1''.
      simpl in *. do 2 rewrite par_comp_assoc_pool.
      repeat processpool_destruct; try congruence.
    - inv H1'. setoid_rewrite H0. right. exists (ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π2).
      split. 1: eapply n_spawn; eauto.
      1: put (dom : ProcessPool -> _) on H1 as P; simpl in *; clear -P H5 H6; set_solver.
      apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as H1''.
      simpl in *. repeat setoid_rewrite <- insert_union_r.
      2: now apply not_elem_of_dom.
      2: put (dom : ProcessPool -> _) on H1 as P; simpl in *; apply not_elem_of_dom; set_solver.
      repeat processpool_destruct; try congruence.
Qed.

Definition renamePIDPID_sym (p p' : PID) := fun s => if s =? p
                                                     then p'
                                                     else if s =? p'
                                                      (* This part is needed
                                                         for Inj eq eq *)
                                                          then p
                                                          else s.

Instance renamePIDPID_sym_Inj p p' : Inj eq eq (renamePIDPID_sym p p').
Proof.
  unfold Inj. intros. unfold renamePIDPID_sym in H.
  repeat case_match; eqb_to_eq; subst; auto; try congruence.
Defined.

Hint Resolve renamePIDPID_sym_Inj : core.
Hint Resolve prod_map_inj : core.
Hint Resolve id_inj : core.

Definition renamePIDEther (p p' : PID) (eth : Ether) : Ether :=
  kmap (prod_map (renamePIDPID_sym p p') (renamePIDPID_sym p p'))
    ((map (renamePIDSignal p p')) <$> eth).

Notation "e .[ x ↦ y ]ₑ" := (renamePIDEther x y e) (at level 2).

Instance Signal_equiv : Equiv Signal := eq.
Instance Signal_leibniz : LeibnizEquiv Signal.
Proof.
  intros x y H. exact H.
Defined.

Corollary isNotUsed_renamePID_ether :
  forall eth from to, ¬isUsedEther from eth -> renamePIDEther from to eth = eth.
Proof.
  intros. unfold renamePIDEther.
  apply map_leibniz, map_equiv_iff. intros. destruct i as [s d].
  (* replace (s, d) with (prod_map (renamePIDPID from to) (renamePIDPID from to) (s, d)) at 1.
  2: {
    cbn.
  } *)
  destruct (_ !! _) eqn:P; destruct (eth !! (s, d)) eqn:P1; setoid_rewrite P1.
  1,4: constructor.
  2: {
    apply lookup_kmap_Some in P as [[s' d'] [Eq P]]. 2: auto. inv Eq.
    unfold isUsedEther in H. exfalso.
  }
  
  
  
  
(*   rewrite lookup_kmap. 2: auto.
  
  
  destruct (eth !! (s, d)) eqn:P; setoid_rewrite P.
  Search kmap lookup. *)
  
Admitted.

Corollary double_renamePID_ether :
  forall eth from to, ¬isUsedEther to eth  -> renamePIDEther to from (renamePIDEther from to eth) = eth.
Proof.

Admitted.


Check ( <[(1,1) := [SMessage (VPid 0)]]>empty) : Ether.
Compute (( <[(1,1) := [SMessage (VPid 0)]]>empty) : Ether) !! (1,1).
Compute (( <[(2,1) := [SMessage (VPid 1)]]>(<[(1,1) := [SMessage (VPid 2)]]>empty)) : Ether) !! (1,1).
Compute ( renamePIDEther 1 3 (( <[(2,1) := [SMessage (VPid 1)]]>(<[(1,1) := [SMessage (VPid 2)]]>empty)) : Ether))!! (3,3).

Definition renamePIDPool (p p' : PID) (Π : ProcessPool) : ProcessPool :=
  kmap (renamePIDPID p p') (renamePIDProc p p' <$> Π).

Notation "e .[ x ⇔ y ]ₚₚ" := (renamePIDPool x y e) (at level 2).

Corollary isNotUsed_renamePID_pool :
  forall Π from to, ¬isUsedPool from Π -> renamePIDPool from to Π = Π.
Proof.
  intros.
Admitted.

Corollary double_renamePID_pool :
  forall Π from to, ¬isUsedPool to Π  -> renamePIDPool to from (renamePIDPool from to Π) = Π.
Proof.

Admitted.

Lemma isUsedEther_rename_same_new :
  forall p p' eth, isUsedEther p eth <-> isUsedEther p' (renamePIDEther p p' eth).
Proof.
  split; intro.
  * unfold renamePIDEther, isUsedEther in *.
    destruct H as [ιs [x [l H]]].
    exists (renamePIDPID p p' ιs), (renamePIDSignal p p' x), (map (renamePIDSignal p p') l).
    apply lookup_kmap_Some. auto.
    exists (ιs, p). split. cbn. unfold renamePIDPID. rewrite Nat.eqb_refl. reflexivity.
    rewrite lookup_fmap. setoid_rewrite H. reflexivity.
  * unfold renamePIDEther, isUsedEther in *.
    destruct H as [ιs [x [l H]]].
    apply lookup_kmap_Some in H as [[ιs0 p0] [Eq H]]. inv Eq. 2: auto.
    rewrite lookup_fmap in H.
    destruct (eth !! (ιs0, p0)) eqn:P; setoid_rewrite P in H.
    2: simpl in H;congruence.
    destruct l0. inv H.
    destruct (decide (p0 = p)).
    - subst. do 3 eexists. eassumption.
    - unfold renamePIDPID in H2. apply Nat.eqb_neq in n. rewrite n in H2.
      break_match_hyp; eqb_to_eq; subst.
      + congruence.
      + congruence.
Qed.

Lemma isUsedEther_rename_same_old :
  forall p p' eth, isUsedEther p' eth <-> isUsedEther p (renamePIDEther p p' eth).
Proof.
  split; intro.
  * unfold renamePIDEther, isUsedEther in *.
    destruct H as [ιs [x [l H]]].
    exists (renamePIDPID p p' ιs), (renamePIDSignal p p' x), (map (renamePIDSignal p p') l).
    apply lookup_kmap_Some. auto.
    exists (ιs, p'). split. cbn. unfold renamePIDPID. rewrite Nat.eqb_refl.
    destruct (p' =? p) eqn:P. 2: reflexivity. eqb_to_eq. now subst.
    rewrite lookup_fmap. setoid_rewrite H. reflexivity.
  * unfold renamePIDEther, isUsedEther in *.
    destruct H as [ιs [x [l H]]].
    apply lookup_kmap_Some in H as [[ιs0 p0] [Eq H]]. inv Eq. 2: auto.
    rewrite lookup_fmap in H.
    destruct (eth !! (ιs0, p0)) eqn:P; setoid_rewrite P in H.
    2: simpl in H;congruence.
    destruct l0. inv H.
    destruct (decide (p0 = p')).
    - subst. do 3 eexists. eassumption.
    - unfold renamePIDPID in H2. apply Nat.eqb_neq in n. rewrite n in H2.
      break_match_hyp; eqb_to_eq; subst.
      + congruence.
      + congruence.
Qed.

Lemma isUsedEther_rename_same_neq :
  forall ι p p' eth,
    ι <> p -> ι <> p' ->
    isUsedEther ι eth <-> isUsedEther ι (renamePIDEther p p' eth).
Proof.
  split; intro.
  * unfold renamePIDEther, isUsedEther in *.
    destruct H1 as [ιs [x [l H1]]].
    exists (renamePIDPID p p' ιs), (renamePIDSignal p p' x), (map (renamePIDSignal p p') l).
    apply lookup_kmap_Some. auto.
    exists (ιs, ι). split. cbn. unfold renamePIDPID. apply Nat.eqb_neq in H, H0.
    now rewrite H, H0.
    rewrite lookup_fmap. setoid_rewrite H1. reflexivity.
  * unfold renamePIDEther, isUsedEther in *.
    destruct H1 as [ιs [x [l H1]]].
    apply lookup_kmap_Some in H1 as [[ιs0 p0] [Eq H1]]. inv Eq. 2: auto.
    rewrite lookup_fmap in H1.
    destruct (eth !! (ιs0, p0)) eqn:P; setoid_rewrite P in H1.
    2: simpl in H1;congruence.
    destruct l0. inv H1.
    unfold renamePIDPID in *. repeat case_match; eqb_to_eq; subst; try congruence.
    do 3 eexists. eassumption.
Qed.

Lemma rename_preCompatible :
  forall eth Π p p',
  ¬isUsedPool p' Π ->
  p' ∉ dom Π ->
  ¬isUsedEther p' eth ->
  p ∈ dom Π -> (* <- renaming only makes sense for existing process
    NOTE, that this could be weakened to `¬isUntaken p (eth, Π)`. This theorem
    would not make sense for such a `p`, that is reserved for the outside
   *)
  preCompatibleNodes (eth, Π)
    (renamePIDEther p p' eth, renamePIDPool p p' Π).
Proof.
  split; simpl.
  * apply lookup_kmap_None; auto. intros.
    destruct H3. unfold renamePIDPID in H4. repeat case_match; eqb_to_eq; subst.
    - Search kmap. simpl in *. congruence.
    - rewrite lookup_fmap. apply not_elem_of_dom in H0. now setoid_rewrite H0.
    - rewrite lookup_fmap. simpl in *. now setoid_rewrite H3.
  * destruct H3. simpl in *.
    assert (ι ≠ p'). {
      intro. subst. congruence.
    }
    assert (ι ≠ p). {
      intro. subst. now apply not_elem_of_dom in H3.
    }
    now apply isUsedEther_rename_same_neq.
Qed.


Corollary rename_preCompatible_sym :
  forall eth Π p p',
  ¬isUsedPool p' Π ->
  p' ∉ dom Π ->
  ¬isUsedEther p' eth ->
  p ∈ dom Π ->
  symClos preCompatibleNodes (eth, Π)
    (renamePIDEther p p' eth, renamePIDPool p p' Π).
Proof.
  intros. split.
  * apply rename_preCompatible; auto.
  * rewrite <- (double_renamePID_ether eth p p') at 2; auto.
    rewrite <- (double_renamePID_pool Π p p') at 2; auto.
    apply rename_preCompatible; auto.
    - admit.
    - admit.
    - intro. now apply isUsedEther_rename_same_old in H3.
    - admit.
Admitted.

Lemma SIGCLOSED_rename :
  forall s p p', SIGCLOSED s <-> SIGCLOSED (renamePIDSignal p p' s).
Proof.

Admitted.

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
    apply in_map_iff in H0 as [? [? ?]]. apply P in H1.
    subst x. now apply SIGCLOSED_rename.
  * (* case separation needed for ι = p/p' *)
Abort.

Lemma ether_wf_rename :
  forall eth p p',
    ether_wf eth -> ether_wf (renamePIDEther p p' eth).
Proof.
  intro; unfold ether_wf, renamePIDEther in *; intros.
  apply lookup_kmap_Some in H0. 2: auto. destruct H0 as [[s d] [Eq H0]].
  simpl in Eq. inv Eq. rewrite lookup_fmap in H0.
  destruct (eth !! (s, d)) eqn:P; setoid_rewrite P in H0. 2: inv H0.
  apply H in P. inv H0.
  apply Forall_forall. intros. rewrite Forall_forall in P.
  apply in_map_iff in H0 as [? [? ?]]. apply P in H1.
  subst x. now apply SIGCLOSED_rename.
Qed.

Lemma ether_wf_rename_rev :
  forall eth p p',
    ¬isUsedEther p' eth -> (* This is weaker than the aborted lemma! *)
    ether_wf (renamePIDEther p p' eth) -> ether_wf eth.
Proof.
  intros.
  rewrite <- (double_renamePID_ether eth p p'); auto.
  by apply ether_wf_rename.
Qed.

Theorem rename_bisim :
  forall eth Π p p',
    ether_wf eth ->
    ¬isUsedEther p' eth ->
    p' ∉ dom Π ->
    p ∈ dom Π ->
    ¬isUsedPool p' Π ->
    (eth, Π) ~ (renamePIDEther p p' eth, renamePIDPool p p' Π) using [].
Proof.
  cofix IH.
  intros. constructor; auto.
  * apply rename_preCompatible_sym; assumption.
  * simpl. by apply ether_wf_rename.
  * intros. admit. (* TODO steps are preserved by renaming *)
  * simpl. intros.
    exists (renamePIDPID p p' source), []. eexists. split. 2: split.
    {
      apply n_refl.
    }
    {
      simpl. admit. (* TODO This property is too strong, definition should be weakened
        Destinations should only be checked, if they are mapped to Some (x::l)! *)
    }
    {
      simpl. admit. (* TODO: renamePID should produce values that are equal with =ᵥ*)
    }
  * admit.
  *
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
    - left. apply in_app_iff. now left.
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
        unfold PIDsOf. rewrite flat_map_app, in_app_iff. right. cbn. now left.
      + intros.
        eapply no_spawn_included_2 in H2 as H2'. 2: exact H4.
        pose proof (no_spawn_included l n n' H2 _ H2').
        split.
        ** now apply H7.
        ** split; unfold PIDsOf; rewrite flat_map_app, in_app_iff.
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
           apply in_app_iff in H5 as [? | ?]. 2: cbn; now rewrite app_nil_r in *.
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

