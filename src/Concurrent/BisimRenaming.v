(**
  This file proves a number of properties about bisimulations. The most
  important of these is that PID renaming is a bisimulation.
*)

From CoreErlang.Concurrent Require Export BarbedBisim.

Import ListNotations.

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
    assert ((map (renamePIDSignal p p') <$> eth) !! (ι, ι') = map (renamePIDSignal p p') <$> Some l). {
      rewrite lookup_fmap. by setoid_rewrite H0.
    }
    simpl in H1.
    pose proof (lookup_kmap (prod_map (renamePIDPID_sym p p') (renamePIDPID_sym p p')) (map (renamePIDSignal p p') <$> eth) (ι, ι')).
    setoid_rewrite <- H2 in H1. apply H in H1.
    clear -H1. apply Basics.map_Forall in H1; auto.
    intros. by apply SIGCLOSED_rename in H.
Qed.

Lemma rename_preCompatible:
  forall O eth Π p p',
  ¬isUsedPool p' Π ->
  p' ∉ O ->
  p ∉ O ->
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
    now apply isTargetedEther_rename_neq.
Qed.

Corollary rename_preCompatible_sym :
  forall O eth Π p p',
  ¬isUsedPool p' Π ->
  p' ∉ O ->
  p ∉ O ->
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
      by apply isTargetedEther_rename_neq in H4.
Qed.

(* This will not hold. For example, spawn + send to self won't be in the ether
   or in the pool. *)
Lemma impossible_send :
  forall O n n' l, n -[l]ₙ->* n' with O ->
    forall ι, ι ∈ (PIDsOf sendPIDOf l) ->
      (isTargetedEther ι n.1 \/ isUsedPool ι n.2).
Proof.
Abort.

Definition PIDRenamingList := list (PID * PID).
Definition renamePIDs {A} (f : PID -> PID -> A -> A) (l : PIDRenamingList) (x : A) : A :=
  fold_left (fun acc '(from, to) => f from to acc) l x.

(*
  If something is renamed, then it should not be renamed again to the same/a used PID.
*)
(* P holds for l !! 0, o, then P holds for l !! 1, f (l !! 0) o, etc. *)
Fixpoint collapse_list {A B : Set} (P : A -> B -> Prop) (f : A -> B -> B) (o : B) (l : list A) : Prop :=
match l with
| [] => True
| x::xs => P x o /\ collapse_list P f (f x o) xs
end.

Definition PIDsRespectNode (O : gset PID) (n : Node) : list (PID * PID) -> Prop :=
  collapse_list (fun '(from, to) n =>
                   from ∉ O /\ to ∉ O /\ ¬isUsedPool to n.2 /\ ¬appearsEther to n.1)
                (fun '(from, to) => prod_map (renamePIDEther from to) (renamePIDPool from to)) n.

Definition PIDsRespectAction (a : Action) : list (PID * PID) -> Prop :=
  collapse_list (fun '(from, to) a => to ∉ usedPIDsAct a) (fun '(from, to) => renamePIDAct from to) a.

Corollary renameList_preCompatible_sym :
  forall O l eth Π,
  PIDsRespectNode O (eth, Π) l ->
  symClos (preCompatibleNodes O) (eth, Π)
    (renamePIDs renamePIDEther l eth, renamePIDs renamePIDPool l Π).
Proof.
  induction l; intros.
  cbn. split; apply preCompatibleNodes_refl.
  inv H. destruct a. destruct_hyps. simpl in *.
  split.
  {
    eapply preCompatibleNodes_trans.
    eapply rename_preCompatible with (p := p) (p' := p0). 1-3: assumption.
    apply IHl; try assumption.
  }
  {
    eapply preCompatibleNodes_trans.
    apply IHl; try assumption.
    eapply rename_preCompatible_sym with (p := p) (p' := p0). 1-3: assumption.
  }
Qed.

Corollary renameList_preCompatible_sym_old :
  forall O l eth Π,
  Forall (fun '(from, to) => ¬ isTargetedEther to eth /\ ¬isUsedPool to Π /\ to ∉ O /\ from ∉ O) l ->
  NoDup (map snd l) ->
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
        intro. apply isTargetedEther_rename_neq in H9. congruence. 2: set_solver.
        intro. subst. apply isTargetedEther_rename_old in H9. congruence.
        intro. apply isUsedPool_rename_neq in H9. congruence. 2: set_solver.
        intro. subst. apply isUsedPool_rename_old in H9. congruence.
      * apply IHForall; auto. (* set_solver. *)
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
        - intro. apply isTargetedEther_rename_neq in H5. congruence. 2: set_solver.
          intro. subst. apply isTargetedEther_rename_old in H5. congruence.
        - intro. apply isUsedPool_rename_neq in H5. congruence. 2: set_solver.
          intro. subst. apply isUsedPool_rename_old in H5. congruence.
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

Theorem renamePIDlist_is_preserved_node_semantics_1 :
  forall l O eth eth' Π Π' a ι,
    (eth, Π) -[a | ι]ₙ-> (eth', Π') with O ->
      PIDsRespectAction a l ->
      PIDsRespectNode O (eth, Π) l ->
      (renamePIDs renamePIDEther l eth, renamePIDs renamePIDPool l Π)
    -[renamePIDs renamePIDAct l a | renamePIDs renamePIDPID_sym l ι]ₙ->
      (renamePIDs renamePIDEther l eth', renamePIDs renamePIDPool l Π') with O.
Proof.
  induction l; intros. by assumption.
  destruct a. simpl in *. inv H0. inv H1. destruct_hyps. simpl in *.
  eapply IHl; auto.
  {
    apply renamePID_is_preserved; try assumption.
  }
Qed.

Lemma PIDsRespectNode_preserved :
  forall l O n n' a ι,
    PIDsRespectNode O n l ->
    PIDsRespectAction a l ->
    n -[a | ι]ₙ-> n' with O ->
    PIDsRespectNode O n' l.
Proof.
  induction l; intros. constructor. destruct n', n.
  inv H. inv H0. destruct a. simpl in *. destruct_hyps. eapply IHl in H3; eauto.
  2: { eapply renamePID_is_preserved. exact H1.
       all: try assumption.
     }
  split.
  * split_and!; auto. eapply not_isUsedPool_step; eauto.
    eapply appearsEther_step in H1; eauto.
  * exact H3.
Qed.

Lemma PIDsRespectAction_take_drop :
  forall l a,
    (forall n, PIDsRespectAction (renamePIDs renamePIDAct (take n l) a) (drop n l)) ->
    PIDsRespectAction a l.
Proof.
  induction l; intros. constructor.
  split. destruct a.
  * apply (H 0).
  * destruct a. simpl. apply IHl. intros. apply (H (S n)).
Qed.

Fixpoint does_not_respect (l : list (PID * PID)) (a : Action) : gset PID :=
match l with
| [] => ∅
| (from, to)::xs =>
  if decide (to ∈ usedPIDsAct a)
  then {[to]} ∪ (does_not_respect xs (renamePIDAct from to a) (* ∖ {[from]} *))
  else does_not_respect xs (renamePIDAct from to a)  (* ∖ {[from]} *)
end.

Lemma PIDsRespectNode_respect_action_1 :
  forall l a,
    does_not_respect l a = ∅ ->
    PIDsRespectAction a l.
Proof.
  induction l; intros. by constructor.
    simpl in *. destruct a. inv H. destruct_hyps.
    case_match.
    - exfalso. set_solver.
    - split. assumption.
      by eapply IHl.
Qed.

Lemma does_not_respect_elem_of :
  forall l from a, from ∈ does_not_respect l a ->
    from ∈ map snd l.
Proof.
  induction l; intros. inv H.
  simpl in *. destruct a. case_match.
  * apply elem_of_union in H as [|].
    - set_solver.
    - simpl. apply IHl in H. set_solver.
  * apply IHl in H. set_solver.
Qed.

Lemma PIDsRespectNode_elem_of_O :
  forall l O n from,
    PIDsRespectNode O n l ->
    from ∈ map snd l ->
    from ∉ O.
Proof.
  induction l; intros.
  * set_solver.
  * simpl in *. destruct a. inv H; simpl in *; destruct_hyps.
    apply elem_of_cons in H0 as [|].
    - subst. assumption.
    - eapply IHl in H2; eassumption.
Qed.

Lemma fresh_PID_increases_respect :
  forall l a from to ι,
    to ∉ map snd l ->
    to ∉ usedPIDsAct a ->
    from ∉ map fst l ->
    from ∉ map snd l ->
    to ∉ map fst l ->
    from ≠ to ->
    ι ∈ does_not_respect l (renamePIDAct from to a) ->
    ι ∈ does_not_respect l a ∖ {[from]}.
Proof.
  induction l; intros; simpl in *. set_solver.
  destruct a.
  rewrite usedPIDsAct_rename in H5; simpl in *.
  repeat destruct decide.
  * assert (p0 ≠ from) by set_solver.
    destruct (decide (ι = p0)).
    - set_solver.
    - apply elem_of_union in H5 as [|]. 1: set_solver.
      rewrite difference_union_distr_l_L. apply elem_of_union_r.
      apply IHl with (to := to); auto. 1, 3-5: set_solver.
      + rewrite usedPIDsAct_rename. destruct decide; set_solver.
      + rewrite renamePID_swap_act. assumption.
        ** intro. subst. set_solver.
        ** lia.
        ** set_solver.
  * destruct (decide (ι = p0)).
    - set_solver.
    - apply elem_of_union in H5 as [|]. 1: set_solver.
      apply IHl with (to := to); auto. 1, 3-5: set_solver.
      + rewrite usedPIDsAct_rename. destruct decide; set_solver.
      + rewrite renamePID_swap_act. assumption.
        ** intro. subst. set_solver.
        ** intro. set_solver.
        ** set_solver.
  * assert (p0 ≠ from) by set_solver.
    destruct (decide (ι = p0)).
    - set_solver.
    - apply elem_of_union in H5 as [|]. 1: set_solver.
      rewrite difference_union_distr_l_L. apply elem_of_union_r.
      apply IHl with (to := to); auto. 1, 3-5: set_solver.
      + rewrite usedPIDsAct_rename. destruct decide; set_solver.
      + rewrite renamePID_swap_act. assumption.
        ** intro. subst. set_solver.
        ** lia.
        ** set_solver.
  * destruct (decide (ι = p0)).
    - set_solver.
    - apply elem_of_union in H5 as [|]. 1: set_solver.
      apply IHl with (to := to); auto. 1, 3-5: set_solver.
      + rewrite usedPIDsAct_rename. destruct decide; set_solver.
      + rewrite renamePID_swap_act. assumption.
        ** intro. subst. set_solver.
        ** intro. set_solver.
        ** set_solver.
  * assert (to = p0) by set_solver. subst. set_solver.
  * assert (to ≠ p0) by set_solver.
    apply IHl with (to := to); auto. 1, 3-5: set_solver.
    + rewrite usedPIDsAct_rename. destruct decide; set_solver.
    + rewrite renamePID_swap_act. assumption.
      ** intro. subst. set_solver.
      ** intro. set_solver.
      ** set_solver.
  * assert (to = p0) by set_solver. subst. set_solver.
  * assert (to ≠ p0) by set_solver.
    apply IHl with (to := to); auto. 1, 3-5: set_solver.
    + rewrite usedPIDsAct_rename. destruct decide; set_solver.
    + rewrite renamePID_swap_act. assumption.
      ** intro. subst. set_solver.
      ** intro. set_solver.
      ** set_solver.
Qed.

Lemma step_not_spawn_respects :
  forall l a eth Π eth' Π' O ι,
  (eth, Π) -[ a | ι ]ₙ-> (eth', Π') with O ->
  PIDsRespectNode O (eth, Π) l ->
  spawnPIDOf a = None -> does_not_respect l a = ∅.
Proof.
  induction l; intros.
  * constructor.
  * simpl in *. destruct a. inv H0. destruct_hyps.
    case_match.
    - simpl in *.
      exfalso. inv H; simpl in *; try congruence.
      + clear H6. destruct (decide (p0 = ι)).
        ** apply H4. left. subst. setoid_rewrite lookup_insert. congruence.
        ** apply H4. right.
           exists ι, p1. split. by setoid_rewrite lookup_insert.
           clear -e n H11. inv H11; simpl in *. 1-4: set_solver.
           apply elem_of_union_list. simpl in *.
           exists ({[ι']} ∪ usedPIDsVal reason). split. 2: set_solver.
           apply elem_of_elements, elem_of_map_to_set. exists ι', reason. by split.
      + destruct (decide (p0 = ι)).
        ** apply H4. left. subst. setoid_rewrite lookup_insert. congruence.
        ** apply H5. unfold etherPop in H12.
           do 2 (case_match; try congruence). inv H12.
           right.
           destruct (decide (p0 = ι1)).
           -- subst. left. eexists. rewrite H. congruence.
           -- right. do 3 eexists. split. exact H. simpl.
              apply elem_of_union_l. clear -e n n0. set_solver.
      + destruct_or!; subst; simpl in *.
        ** set_solver.
        ** apply H4. assert (p0 = ι) by (clear-e;set_solver).
           subst. left. by setoid_rewrite lookup_insert.
        ** clear-e. set_solver.
    - eapply IHl. 2: exact H3.
      simpl. apply renamePID_is_preserved. exact H.
      all: try assumption.
      + clear -H1. destruct a0; auto. simpl in H1. congruence.
Qed.


(** New idea: restrict semantics so that spawn cannot happen to appearing PIDs,
   this way, the renaming does not do anything in this theorem! *)
Lemma step_spawn_respects_3 :
  forall l a eth Π eth' Π' O ι,
  (eth, Π) -[ a | ι ]ₙ-> (eth', Π') with O ->
  PIDsRespectNode O (eth, Π) l ->
  forall p, spawnPIDOf a = Some p ->
    exists new, new ∉ usedPIDsAct a /\ new ∉ O /\ ¬isUsedPool new Π /\ ¬appearsEther new eth /\ new ∉ map snd l /\
    PIDsRespectNode O (eth, Π) ((p, new)::l) /\
    PIDsRespectAction a ((p, new) :: l).
Proof.
  intros.
  assert (exists new, new ∉ usedPIDsAct a /\ new ∉ O /\ ¬isUsedPool new Π /\ ¬appearsEther new eth /\ new ∉ map snd l /\ new ∉ map fst l). {
    (* freshness *)
    pose proof (infinite_is_fresh (elements (usedPIDsAct a) ++ elements O ++ elements (allPIDsPool Π) ++ elements (allPIDsEther eth) ++ map snd l ++ map fst l)).
    remember (fresh _) as y in H2. clear-H2. exists y.
    repeat apply not_elem_of_app in H2 as [? H2].
    split_and!; try assumption.
    1-2: set_solver.
    * apply allPIDsPool_isNotUsed_1. set_solver.
    * apply allPIDsEther_does_not_appear_1. set_solver.
  }
  destruct H2 as [new H2].
  destruct_hyps. exists new. split_and!; try assumption.
  * cbn. split_and!; try assumption.
    1: {
      destruct a; inv H1. inv H. destruct_or!; congruence.
      assumption.
    }
    destruct a; inv H1. inv H. destruct_or!; congruence.
    rewrite does_not_appear_renamePID_ether. 2-3: assumption.
    rewrite isNotUsed_renamePID_pool. 2-3: assumption.
    assumption.
  * cbn. split; auto.
    destruct a; inv H1. inv H. destruct_or!; congruence.
    simpl.
    assert (Ht1 : p ∉ usedPIDsVal t1). 2: assert (Ht2 : p ∉ usedPIDsVal t2).
    1-2: intro; apply H18; right; exists ι, p0; setoid_rewrite lookup_insert; split; [reflexivity|].
    1-2: inv H21; simpl; set_solver.
    rewrite isNotUsed_renamePID_val. rewrite isNotUsed_renamePID_val.
    2-3: assumption.
    clear H20 H16.
    renamePIDPID_case_match.
    (* TODO: separate *)
    {
      clear -H6 H7 H0 H21.
      assert (usedPIDsVal t1 ∪ usedPIDsVal t2 ⊆ usedPIDsProc p0). {
        inv H21; set_solver.
      }
      clear H21.
      generalize dependent l. intro l.
      revert t1 t2 eth' ι p0 Π0 H. induction l; intros; cbn. trivial.
      destruct a. simpl in *. inv H0. destruct_hyps.
      split.
      * intro. apply H3. right. exists ι, p0.
        setoid_rewrite lookup_insert. split. reflexivity.
        set_solver.
      * renamePIDPID_case_match. 1: set_solver.
        apply IHl with (p0 := renamePIDProc p1 p2 p0)
                       (eth' := renamePIDEther p1 p2 eth')
                       (Π0 := renamePIDPool p1 p2 Π0)
                       (ι := renamePIDPID_sym p1 p2 ι).
        + do 2 rewrite usedPIDsVal_rename.
          destruct p0.
          ** rewrite usedPIDsLiveProc_rename.
             repeat destruct decide; set_solver.
          ** clear H2.
             epose proof (usedPIDsDeadProc_rename d p1 p2 _).
             repeat destruct decide; set_solver.
             Unshelve.
               intro.
               apply H3. right. exists ι, (inr d). split.
               by setoid_rewrite lookup_insert. assumption.
        + unfold PIDsRespectNode. cbn in H2.
          setoid_rewrite <- kmap_insert; auto.
          setoid_rewrite <- fmap_insert. exact H2.
        + set_solver.
        + set_solver.
    }
Qed.

Definition swap {A B : Set} (a : A * B) : B * A := (a.2, a.1).

Theorem cancel_renamePIDs_pool :
  forall l O eth Π,
  PIDsRespectNode O (eth, Π) l ->
  renamePIDs renamePIDPool (map swap (reverse l)) (renamePIDs renamePIDPool l Π) = Π.
Proof.
  induction l; intros; simpl. reflexivity.
  inv H. destruct a as [from to]. destruct_hyps. apply IHl in H1.
  simpl in *.
  rewrite reverse_cons, map_app. simpl.
  unfold renamePIDs in *. rewrite fold_left_app. simpl.
  rewrite H1.
  by rewrite double_renamePID_pool.
Qed.

Theorem cancel_renamePIDs_ether :
  forall l O eth Π,
  PIDsRespectNode O (eth, Π) l ->
  renamePIDs renamePIDEther (map swap (reverse l)) (renamePIDs renamePIDEther l eth) = eth.
Proof.
  induction l; intros; simpl. reflexivity.
  inv H. destruct a as [from to]. destruct_hyps. apply IHl in H1.
  simpl in *.
  rewrite reverse_cons, map_app. simpl.
  unfold renamePIDs in *. rewrite fold_left_app. simpl.
  rewrite H1.
  by rewrite double_renamePID_ether.
Qed.

Lemma PIDsRespectNode_app :
  forall l₁ l₂ O n,
    PIDsRespectNode O n (l₁ ++ l₂) <->
    PIDsRespectNode O n l₁ /\
    PIDsRespectNode O (prod_map (renamePIDs renamePIDEther l₁)
                                  (renamePIDs renamePIDPool  l₁) n) l₂.
Proof.
  induction l₁; intros; cbn.
  1: split; intros; destruct_hyps; try split; trivial; try assumption.
  1-2: by destruct n.
  destruct a. split; intros.
  {
    destruct_hyps. apply IHl₁ in H0 as [? ?]. split_and!; try assumption.
  }
  {
    destruct_hyps. split_and!; try assumption.
    apply IHl₁. split; assumption.
  }
Qed.

Lemma cancel_PIDsRespectNode :
  forall l O eth Π,
  PIDsRespectNode O (eth, Π) l ->
  PIDsRespectNode O (renamePIDs renamePIDEther l eth, renamePIDs renamePIDPool l Π)
                      (map swap (reverse l)).
Proof.
  induction l; intros; simpl. constructor.
  inv H. destruct a. simpl in *. apply IHl in H1 as H'. destruct_hyps.
  rewrite reverse_cons, map_app. unfold swap at 2. cbn.
  apply PIDsRespectNode_app. split. assumption.
  cbn. split_and!; try assumption. 3: trivial.
  * erewrite cancel_renamePIDs_pool. 2: exact H1.
    intro. by apply isUsedPool_rename_old in H4.
  * erewrite cancel_renamePIDs_ether. 2: exact H1.
    intro. by apply appearsEther_rename_old in H4.
Qed.

(* NOTE:
    We can try to avoid guardedness checking with an alternative definition?
    However, this is not this simple:

Theorem rename_bisim_alt :
  forall O,
    is_barbed_bisim_alt (
      fun '(eth, Π) '(eth', Π') =>
         forall l,
          PIDsRespectNode O (eth, Π) l /\
          renamePIDs renamePIDEther l eth = eth' /\
          renamePIDs renamePIDPool l Π = Π'
    ) O.
Proof.

Qed.  *)

Unset Guard Checking.
Theorem rename_bisim :
  forall O eth Π (l : list (PID * PID)),
    PIDsRespectNode O (eth, Π) l ->
    (eth, Π) ~ (renamePIDs renamePIDEther l eth, renamePIDs renamePIDPool l Π) observing O.
Proof.
  cofix IH.
  intros. constructor; auto.
  * intros. destruct A' as [eth' Π'].
    destruct (spawnPIDOf a) eqn:P.
    { (* renaming needed *)
      pose proof step_spawn_respects_3 l a _ _ _ _ _ _ H0 H _ P.
      destruct H1 as [new H1]. destruct_hyps.
      apply renamePIDlist_is_preserved_node_semantics_1 with (l := (p, new)::l) in H0 as D.
      3: clear IH; assumption.
      2: {
        assumption.
      }

      replace (renamePIDs renamePIDEther l eth) with
         (renamePIDs renamePIDEther ((p, new) :: l) eth). 2: {
         simpl.
         rewrite does_not_appear_renamePID_ether; auto.
         destruct a; inv P. inv H0. 1: destruct_or!; congruence.
         by simpl.
      }
      replace (renamePIDs renamePIDPool l Π) with
         (renamePIDs renamePIDPool ((p, new) :: l) Π). 2: {
         simpl.
         rewrite isNotUsed_renamePID_pool; auto.
         destruct a; inv P. inv H0. 1: destruct_or!; congruence.
         by simpl.
      }
      do 2 eexists. split. eapply n_trans. exact D. apply n_refl.
      apply IH; clear IH.
      eapply PIDsRespectNode_preserved in H0; eassumption.
    }
    { (* renaming is not needed *)
      eapply step_not_spawn_respects in H0 as R. 2: exact H. 2: assumption.
      apply PIDsRespectNode_respect_action_1 in R as R'.
      apply renamePIDlist_is_preserved_node_semantics_1 with (l := l) in H0 as D.
      3: clear IH; assumption.
      2: {
        assumption.
      }
      do 2 eexists. split. eapply n_trans. exact D. apply n_refl.
      apply IH; clear IH.
      eapply PIDsRespectNode_preserved in H0; eassumption.
    }
  * clear IH.
    simpl. intros.
    exists (renamePIDs renamePIDPID_sym l source), []. eexists.
    split.
    {
      apply n_refl.
    }
    {
      simpl.
      assert ((renamePIDs renamePIDPID_sym l source, dest) =
           ((prod_map (renamePIDs renamePIDPID_sym l) (renamePIDs renamePIDPID_sym l)) (source, dest))). {
        cbn. f_equal. clear -H H0.
        generalize dependent dest. revert eth Π H.
        induction l; intros. reflexivity.
        inv H. destruct a. simpl.
        intros. erewrite <- IHl; auto.
        * unfold renamePIDPID_sym.
          destruct_hyps. repeat case_match;eqb_to_eq; subst; try congruence.
        * eassumption.
        * unfold renamePIDPID_sym.
          destruct_hyps. repeat case_match;eqb_to_eq; subst; try congruence.
      }
      setoid_rewrite H1.
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
  (* The other two cases need additional consideration. Now, it is allowed for l
     to contain duplicates in its second elements.

     Duplicates should be allowed in (map fst l), because we can't guarantee
     that in the previous proof, the spawned PID "p" is not initially in
     the (map fst l)
     - Is this true? We could restrict l to contain only elements from the ether/pool
     - But in the previous case, p cannot be added to l!

     We can't do the proof by using double renaming, because it won't be guarded.
     See the proof below, notice the use of "barbedBisim_sym"! : *)
  * intros.
    rewrite <- (cancel_renamePIDs_pool l O eth Π). 2: assumption.
    rewrite <- (cancel_renamePIDs_ether l O eth Π). 2: assumption.

    remember (map swap (reverse l)) as l'.
    apply cancel_PIDsRespectNode in H as Hcancel.
    rewrite <- Heql' in Hcancel.
    destruct B' as [eth' Π'].
    destruct (spawnPIDOf a) eqn:P.
    { (* renaming needed *)
      pose proof step_spawn_respects_3 l' a _ _ _ _ _ _ H0 Hcancel _ P.
      destruct H1 as [new H1]. destruct_hyps.
      apply renamePIDlist_is_preserved_node_semantics_1 with (l := (p, new)::l') in H0 as D.
      3: clear IH; assumption.
      2: {
        assumption.
      }

      replace (renamePIDs renamePIDEther l' (renamePIDs renamePIDEther l eth)) with
         (renamePIDs renamePIDEther ((p, new)::l') (renamePIDs renamePIDEther l eth)). 2: {
         simpl.
         rewrite does_not_appear_renamePID_ether; auto.
         destruct a; inv P. inv H0. 1: destruct_or!; congruence.
         by simpl.
      }
      replace (renamePIDs renamePIDPool l' (renamePIDs renamePIDPool l Π)) with
         (renamePIDs renamePIDPool ((p, new) :: l') (renamePIDs renamePIDPool l Π)). 2: {
         simpl.
         rewrite isNotUsed_renamePID_pool; auto.
         destruct a; inv P. inv H0. 1: destruct_or!; congruence.
         by simpl.
      }
      do 2 eexists. split. eapply n_trans. exact D. apply n_refl.
      (** NOTE: this use of symmetry makes the next use of IH unguarded *)
      apply barbedBisim_sym.
      apply IH; clear IH.
      (** END NOTE *)
      eapply PIDsRespectNode_preserved in H0; eassumption.
    }
    { (* renaming is not needed *)
      eapply step_not_spawn_respects in H0 as R. 3: exact P. 2: exact Hcancel.
      apply PIDsRespectNode_respect_action_1 in R as R'.
      apply renamePIDlist_is_preserved_node_semantics_1 with (l := l') in H0 as D.
      3: clear IH; assumption.
      2: {
        assumption.
      }
      do 2 eexists. split. eapply n_trans. exact D. apply n_refl.
      (** NOTE: this use of symmetry makes the next use of IH unguarded *)
      apply barbedBisim_sym.
      apply IH; clear IH.
      (** END NOTE *)
      - eapply PIDsRespectNode_preserved in H0; eassumption.
    }
  * clear IH. intros. simpl.
    assert (exists source', option_list_biforall Signal_eq
      (renamePIDs renamePIDEther l eth !! (source, dest))
      (eth !! (source', dest))). {
      revert l eth Π source H0 H. induction l; intros.
      * inv H0. simpl. exists source.
        apply option_biforall_refl. intros.
        apply Signal_eq_refl.
      * simpl. destruct a. inv H. cbn in H1. apply IHl with (source := source) in H2.
        2: assumption.
        destruct_hyps.
        simpl in *.
        destruct (decide (x = p)). 2: destruct (decide (x = p0)).
        (* TODO: shorten, these 3 cases are almost the same. The difference
           is the variables need to be used: x vs p vs p0. *)
        {
          subst. replace (p, dest) with (prod_map (renamePIDPID_sym p p0) (renamePIDPID_sym p p0) (p0, dest)) in H.
          2: {
            cbn. renamePIDPID_sym_case_match; try reflexivity;congruence.
          }
          setoid_rewrite lookup_kmap in H; auto.
          setoid_rewrite lookup_fmap in H.
          exists p0.
          eapply option_biforall_trans. 1: apply Signal_eq_trans.
          exact H.
          simpl. destruct (eth !! _) eqn:P.
          {
            setoid_rewrite P. simpl.
            eapply forall_biforall with (d1 := SUnlink) (d2 := SUnlink).
            1: by rewrite map_length.
            intros. rewrite map_nth with (d:= SUnlink).
            pose proof (Signal_eq_renamePID (nth i l0 SUnlink) p p0).
            unfold Signal_eq in *.
            rewrite <- H6.
            by rewrite Signal_eq_sym, Signal_eq_renamePID.
          }
          {
            setoid_rewrite P. simpl. trivial.
          }
        }
        {
          subst. replace (p0, dest) with (prod_map (renamePIDPID_sym p p0) (renamePIDPID_sym p p0) (p, dest)) in H.
          2: {
            cbn. renamePIDPID_sym_case_match; try reflexivity;congruence.
          }
          setoid_rewrite lookup_kmap in H; auto.
          setoid_rewrite lookup_fmap in H.
          exists p.
          eapply option_biforall_trans. 1: apply Signal_eq_trans.
          exact H.
          simpl. destruct (eth !! _) eqn:P.
          {
            setoid_rewrite P. simpl.
            eapply forall_biforall with (d1 := SUnlink) (d2 := SUnlink).
            1: by rewrite map_length.
            intros. rewrite map_nth with (d:= SUnlink).
            pose proof (Signal_eq_renamePID (nth i l0 SUnlink) p p0).
            unfold Signal_eq in *.
            rewrite <- H6.
            by rewrite Signal_eq_sym, Signal_eq_renamePID.
          }
          {
            setoid_rewrite P. simpl. trivial.
          }
        }
        {
          subst. replace (x, dest) with (prod_map (renamePIDPID_sym p p0) (renamePIDPID_sym p p0) (x, dest)) in H.
          2: {
            cbn. renamePIDPID_sym_case_match; try reflexivity;congruence.
          }
          setoid_rewrite lookup_kmap in H; auto.
          setoid_rewrite lookup_fmap in H.
          exists x.
          eapply option_biforall_trans. 1: apply Signal_eq_trans.
          exact H.
          simpl. destruct (eth !! _) eqn:P.
          {
            setoid_rewrite P. simpl.
            eapply forall_biforall with (d1 := SUnlink) (d2 := SUnlink).
            1: by rewrite map_length.
            intros. rewrite map_nth with (d:= SUnlink).
            pose proof (Signal_eq_renamePID (nth i l0 SUnlink) p p0).
            unfold Signal_eq in *.
            rewrite <- H6.
            by rewrite Signal_eq_sym, Signal_eq_renamePID.
          }
          {
            setoid_rewrite P. simpl. trivial.
          }
        }
    }
    destruct H1. exists x, []. eexists.
    split. apply n_refl.
    assumption.
Defined.
Set Guard Checking.
