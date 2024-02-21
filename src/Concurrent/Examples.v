From CoreErlang.Concurrent Require Import BarbedBisim.

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
      inv H8. set_solver.
    - left. intro.
      apply H0. right. exists ι, p. split. by setoid_rewrite lookup_insert.
      inv H8; simpl in *.
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
    - left. apply isTargetedEther_etherAdd_rev in H; auto. intro. subst.
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

Definition PIDRenamingList := list (PID * PID).
Definition renamePIDs {A} (f : PID -> PID -> A -> A) (l : PIDRenamingList) (x : A) : A :=
  fold_left (fun acc '(from, to) => f from to acc) l x.

(*
  If something is renamed, then it should not be renamed again
  if the ith element of the list is (from, to) then from should not appear 

*)
(* P holds for l !! 0, o, then P holds for l !! 1, f (l !! 0) o, etc. *)
Fixpoint collapse_list {A B : Set} (P : A -> B -> Prop) (f : A -> B -> B) (o : B) (l : list A) : Prop :=
match l with
| [] => True
| x::xs => P x o /\ collapse_list P f (f x o) xs
end.

Definition PIDs_respect_node (O : gset PID) (n : Node) : list (PID * PID) -> Prop :=
  collapse_list (fun '(from, to) n =>
                   from ∉ O /\ to ∉ O /\ ¬isUsedPool to n.2 /\ ¬appearsEther to n.1)
                (fun '(from, to) => prod_map (renamePIDEther from to) (renamePIDPool from to)) n.

(* (* TODO: generalize this *)
Fixpoint collapse_list (l : list (PID * PID)) (a : Action) :=
match l with
| (from, to)::l => to ∉ usedPIDsAct a /\ collapse_list l (renamePIDAct from to a)
| [] => True
end. *)

Definition PIDs_respect_action (a : Action) : list (PID * PID) -> Prop :=
  collapse_list (fun '(from, to) a => to ∉ usedPIDsAct a) (fun '(from, to) => renamePIDAct from to) a.

Corollary renameList_preCompatible_sym :
  forall O l eth Π,
  PIDs_respect_node O (eth, Π) l ->
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
      PIDs_respect_action a l ->
      (* NoDup (map snd l) -> *)
      PIDs_respect_node O (eth, Π) l ->
      (renamePIDs renamePIDEther l eth, renamePIDs renamePIDPool l Π)
    -[renamePIDs renamePIDAct l a | renamePIDs renamePIDPID_sym l ι]ₙ->
      (renamePIDs renamePIDEther l eth', renamePIDs renamePIDPool l Π') with O.
Proof.
  induction l; intros. by assumption.
  destruct a. simpl in *. inv H0. inv H1. destruct_hyps. simpl in *.
  eapply IHl; auto.
  {
    apply renamePID_is_preserved_node_semantics; try assumption.
  }
Qed.

Lemma PIDs_respect_node_preserved :
  forall l O n n' a ι,
    PIDs_respect_node O n l ->
    PIDs_respect_action a l ->
    n -[a | ι]ₙ-> n' with O ->
    PIDs_respect_node O n' l.
Proof.
  induction l; intros. constructor. destruct n', n.
  inv H. inv H0. destruct a. simpl in *. destruct_hyps. eapply IHl in H3; eauto.
  2: { eapply renamePID_is_preserved_node_semantics. exact H1.
       all: try assumption.
     }
  split.
  * split_and!; auto. eapply not_isUsedPool_step; eauto.
    eapply appearsEther_step in H1; eauto.
  * exact H3.
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

Lemma PIDs_respect_action_take_drop :
  forall l a,
    (forall n, PIDs_respect_action (renamePIDs renamePIDAct (take n l) a) (drop n l)) ->
    PIDs_respect_action a l.
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

Lemma PIDs_respect_node_respect_action_1 :
  forall l a,
    does_not_respect l a = ∅ ->
    PIDs_respect_action a l.
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

Lemma PIDs_respect_node_elem_of_O :
  forall l O n from,
    PIDs_respect_node O n l ->
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
  PIDs_respect_node O (eth, Π) l ->
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
           clear -e n H11. inv H11; simpl in *; set_solver.
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
        ** clear-e. set_solver.
    - eapply IHl. 2: exact H3.
      simpl. apply renamePID_is_preserved_node_semantics. exact H.
      all: try assumption.
      + clear -H1. destruct a0; auto. simpl in H1. congruence.
Qed.

Lemma fst_combine :
  forall {A B} (l : list A) (l' : list B),
    length l <= length l' ->
    map fst (combine l l') = l.
Proof.
  induction l; destruct l'; simpl; intros.
  1-2: reflexivity.
  1: lia.
  f_equal. apply IHl. lia.
Qed.

Lemma snd_combine :
  forall {A B} (l : list A) (l' : list B),
    length l' <= length l ->
    map snd (combine l l') = l'.
Proof.
  induction l; destruct l'; simpl; intros.
  1,3: reflexivity.
  1: lia.
  f_equal. apply IHl. lia.
Qed.

Definition allPIDsEther (eth : Ether) : gset PID :=
  flat_union (fun '((ιs, ιd), sigs) => {[ιs; ιd]} ∪ flat_union usedPIDsSignal sigs) (map_to_list eth).
Definition allPIDsPool (Π : ProcessPool) : gset PID :=
  flat_union (fun '(ι, proc) => {[ι]} ∪ usedPIDsProc proc) (map_to_list Π).

Lemma allPIDsPool_isNotUsed_1 :
  forall ι Π,
    ι ∉ allPIDsPool Π -> ¬isUsedPool ι Π.
Proof.
  intros. intro. destruct H0.
  * apply H. apply elem_of_flat_union.
    apply not_eq_None_Some in H0. destruct H0 as [proc H0].
    exists (ι, proc). split. 2: set_solver.
    by apply elem_of_map_to_list.
  * apply H. apply elem_of_flat_union.
    destruct H0 as [ι' [proc [P_1 P_2]]].
    exists (ι', proc). split.
    by apply elem_of_map_to_list.
    set_solver.
Qed.

Lemma allPIDsPool_isNotUsed_2 :
  forall ι Π,
    ¬isUsedPool ι Π ->
    ι ∉ allPIDsPool Π.
Proof.
  intros. intro. apply H.
  unfold allPIDsPool in H0. apply elem_of_flat_union in H0.
  destruct_hyps. destruct x as [ι' proc].
  apply elem_of_map_to_list in H0 as P.
  apply elem_of_union in H1 as [|].
  * assert (ι = ι') by set_solver.
    subst. left. by setoid_rewrite P.
  * right. exists ι', proc. split; assumption.
Qed.

Lemma allPIDsEther_does_not_appear_1 :
  forall ι eth,
    ι ∉ allPIDsEther eth -> ¬appearsEther ι eth.
Proof.
  intros. intro. apply H.
  apply elem_of_flat_union.
  destruct H0. 2: destruct H0.
  * destruct H0 as [ιs [l H0]].
    exists (ιs, ι, l). split.
    by apply elem_of_map_to_list.
    set_solver.
  * destruct H0 as [ιd H0].
    apply not_eq_None_Some in H0. destruct H0 as [l H0].
    exists (ι, ιd, l). split.
    by apply elem_of_map_to_list.
    set_solver.
  * destruct H0 as [ιs [ιd [l [P1 P2]]]].
    exists (ιs, ιd, l). split.
    by apply elem_of_map_to_list.
    set_solver.
Qed.

Lemma allPIDsEther_does_not_appear_2 :
  forall ι eth,
    ¬appearsEther ι eth ->
    ι ∉ allPIDsEther eth.
Proof.
  intros. intro. apply H.
  unfold allPIDsEther in H0. apply elem_of_flat_union in H0.
  destruct_hyps. destruct x as [[ιs ιd] l].
  apply elem_of_map_to_list in H0 as P.
  apply elem_of_union in H1 as [|].
  destruct (decide (ι = ιd)).
  * subst. left. by exists ιs, l.
  * assert (ι = ιs) by set_solver. subst. right. left.
    exists ιd. by setoid_rewrite P.
  * right. right. exists ιs, ιd, l. split; assumption.
Qed.

(** New idea: restrict semantics so that spawn cannot happen to appearing PIDs,
   this way, the renaming does not do anything in this theorem! *)
Lemma step_spawn_respects_3 :
  forall l a eth Π eth' Π' O ι,
  (eth, Π) -[ a | ι ]ₙ-> (eth', Π') with O ->
  PIDs_respect_node O (eth, Π) l ->
  forall p, spawnPIDOf a = Some p ->
    exists new, new ∉ usedPIDsAct a /\ new ∉ O /\ ¬isUsedPool new Π /\ ¬appearsEther new eth /\ new ∉ map snd l /\
    PIDs_respect_node O (eth, Π) ((p, new)::l) /\
    PIDs_respect_action a ((p, new) :: l).
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
    1-2: intro; apply H17; right; exists ι, p0; setoid_rewrite lookup_insert; split; [reflexivity|].
    1-2: inv H20; simpl; set_solver.
    rewrite isNotUsed_renamePID_val. rewrite isNotUsed_renamePID_val.
    2-3: assumption.
    clear H19 H14.
    renamePIDPID_case_match.
    (* TODO: separate *)
    {
      clear -H6 H7 H0 H20.
      assert (usedPIDsVal t1 ∪ usedPIDsVal t2 ⊆ usedPIDsProc p0). {
        inv H20. set_solver.
      }
      clear H20.
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
          rewrite usedPIDsProc_rename.
          repeat destruct decide; set_solver.
        + unfold PIDs_respect_node. cbn in H2.
          setoid_rewrite <- kmap_insert; auto.
          setoid_rewrite <- fmap_insert. exact H2.
        + set_solver.
        + set_solver.
    }
Qed.

Definition swap {A B : Set} (a : A * B) : B * A := (a.2, a.1).

Theorem cancel_renamePIDs_pool :
  forall l O eth Π,
  PIDs_respect_node O (eth, Π) l ->
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
  PIDs_respect_node O (eth, Π) l ->
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

Lemma PIDs_respect_node_app :
  forall l₁ l₂ O n,
    PIDs_respect_node O n (l₁ ++ l₂) <->
    PIDs_respect_node O n l₁ /\
    PIDs_respect_node O (prod_map (renamePIDs renamePIDEther l₁)
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

Lemma cancel_PIDs_respect_node :
  forall l O eth Π,
  PIDs_respect_node O (eth, Π) l ->
  PIDs_respect_node O (renamePIDs renamePIDEther l eth, renamePIDs renamePIDPool l Π)
                      (map swap (reverse l)).
Proof.
  induction l; intros; simpl. constructor.
  inv H. destruct a. simpl in *. apply IHl in H1 as H'. destruct_hyps.
  rewrite reverse_cons, map_app. unfold swap at 2. cbn.
  apply PIDs_respect_node_app. split. assumption.
  cbn. split_and!; try assumption. 3: trivial.
  * erewrite cancel_renamePIDs_pool. 2: exact H1.
    intro. by apply isUsedPool_rename_old in H4.
  * erewrite cancel_renamePIDs_ether. 2: exact H1.
    intro. by apply appearsEther_rename_old in H4.
Qed.

(* TODO: this is not this simple:

Theorem rename_bisim_alt :
  forall O,
    is_barbed_bisim_alt (
      fun '(eth, Π) '(eth', Π') =>
         forall l,
          PIDs_respect_node O (eth, Π) l /\
          renamePIDs renamePIDEther l eth = eth' /\
          renamePIDs renamePIDPool l Π = Π'
    ) O.
Proof.
  intros.
  intros A B. destruct A as [eth Π]. destruct B.
  intros. split_and!.
  * intros. destruct A' as [eth' Π']. subst.
    destruct (spawnPIDOf a) eqn:P.
    { (* renaming needed *)
      pose proof step_spawn_respects_3 l a _ _ _ _ _ _ H0 H _ P.
      destruct H1 as [new H1]. destruct_hyps.
      apply renamePIDlist_is_preserved_node_semantics_1 with (l := (p, new)::l) in H0 as D.
      3: assumption.
      2: assumption.

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
      simpl. split_and!.
      eapply PIDs_respect_node_preserved in H6; eassumption.
    }
    { (* renaming is not needed *)
      eapply step_not_spawn_respects in H0 as R. 2: exact H. 2: assumption.
      apply PIDs_respect_node_respect_action_1 in R as R'.
      apply renamePIDlist_is_preserved_node_semantics_1 with (l := l) in H0 as D.
      3: clear IH; assumption.
      2: {
        assumption.
      }
      do 2 eexists. split. eapply n_trans. exact D. apply n_refl.
      apply IH; clear IH.
      (* - eapply n_trans in H1. 2:apply n_refl.
        by apply ether_wf_preserved in H1. *)
      eapply PIDs_respect_node_preserved in H0; eassumption.
    }
  *
  *
  *
Qed.  *)

Unset Guard Checking.
Theorem rename_bisim :
  forall O eth Π (l : list (PID * PID)),
    (* ether_wf eth -> *)
    PIDs_respect_node O (eth, Π) l ->
    (eth, Π) ~ (renamePIDs renamePIDEther l eth, renamePIDs renamePIDPool l Π) observing O.
Proof.
  cofix IH.
  intros. constructor; auto.
  (* * apply renameList_preCompatible_sym. assumption.
  * simpl. by apply ether_wf_renameList. *)
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
(*       - eapply n_trans in H0. 2:apply n_refl.
        by apply ether_wf_preserved in H0. *)
      eapply PIDs_respect_node_preserved in H0; eassumption.
    }
    { (* renaming is not needed *)
      eapply step_not_spawn_respects in H0 as R. 2: exact H. 2: assumption.
      apply PIDs_respect_node_respect_action_1 in R as R'.
      apply renamePIDlist_is_preserved_node_semantics_1 with (l := l) in H0 as D.
      3: clear IH; assumption.
      2: {
        assumption.
      }
      do 2 eexists. split. eapply n_trans. exact D. apply n_refl.
      apply IH; clear IH.
      (* - eapply n_trans in H1. 2:apply n_refl.
        by apply ether_wf_preserved in H1. *)
      eapply PIDs_respect_node_preserved in H0; eassumption.
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
    apply cancel_PIDs_respect_node in H as Hcancel.
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
      (* - eapply n_trans in H1. 2: apply n_refl.
        apply ether_wf_preserved in H1. exact H1.
        simpl. by apply ether_wf_renameList. *)
      eapply PIDs_respect_node_preserved in H0; eassumption.
    }
    { (* renaming is not needed *)
      eapply step_not_spawn_respects in H0 as R. 3: exact P. 2: exact Hcancel.
      apply PIDs_respect_node_respect_action_1 in R as R'.
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
(*       - eapply n_trans in H0. 2: apply n_refl.
        apply ether_wf_preserved in H0. exact H.
        simpl. by apply ether_wf_renameList. *)
      - eapply PIDs_respect_node_preserved in H0; eassumption.
    }
  (* * intros. destruct B' as [eth' Π'].
    destruct (spawnPIDOf a) eqn:P.
    { (* renaming needed *)
      (* pose proof step_spawn_respects_3 l a _ _ _ _ _ _ H1 H0 _ P.
      destruct H2 as [new H2]. destruct_hyps.
      apply renamePIDlist_is_preserved_node_semantics with (l := (p, new)::l) in H1 as D.
      3: clear IH; assumption.
      2: {
        assumption.
      }

      replace (renamePIDs renamePIDEther l eth) with
         (renamePIDs renamePIDEther ((p, new) :: l) eth). 2: {
         simpl.
         rewrite does_not_appear_renamePID_ether; auto.
         destruct a; inv P. inv H1. 1: destruct_or!; congruence.
         by simpl.
      }
      replace (renamePIDs renamePIDPool l Π) with
         (renamePIDs renamePIDPool ((p, new) :: l) Π). 2: {
         simpl.
         rewrite isNotUsed_renamePID_pool; auto.
         destruct a; inv P. inv H1. 1: destruct_or!; congruence.
         by simpl.
      }
      do 2 eexists. split. eapply n_trans. exact D. apply n_refl.
      apply IH; clear IH.
      - eapply n_trans in H1. 2:apply n_refl.
        by apply ether_wf_preserved in H1.
      - eapply PIDs_respect_node_preserved in H1; eassumption. *)
      admit.
    }
    { (* renaming is not needed *)
      eapply step_not_spawn_respects in H1 as R. 3: exact P. 2: assumption.
      apply PIDs_respect_node_respect_action_1 in R as R'.
      apply renamePIDlist_is_preserved_node_semantics with (l := l) in H1 as D.
      3: clear IH; assumption.
      2: {
        assumption.
      }
      do 2 eexists. split. eapply n_trans. exact D. apply n_refl.
      apply IH; clear IH.
      - eapply n_trans in H1. 2:apply n_refl.
        by apply ether_wf_preserved in H1.
      - eapply PIDs_respect_node_preserved in H1; eassumption.
    } *)
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

Lemma reductions_preserve_O_dom :
  forall l O n n', n -[l]ₙ->* n' with O ->
    O ## dom n.2 ->
    O ## dom n'.2.
Proof.
  induction l; intros; inv H. assumption.
  apply IHl in H6. assumption.
  clear IHl H6. inv H4; simpl in *; setoid_rewrite dom_insert; setoid_rewrite dom_insert in H0; try assumption.
  clear H5. setoid_rewrite dom_insert. set_solver.
Qed.

Lemma reductions_preserve_singals_targeting_O :
  forall O (n n' : Node) l, n -[l]ₙ->* n' with O ->
    O ## dom n.2 ->
    (forall ι, ι ∈ (PIDsOf sendPIDOf l) -> ι ∉ O) ->
    forall source : PID,
      (* n'.2 !! dest = None -> *)
      forall dest, dest ∈ O ->
      option_list_biforall Signal_eq (n.1 !! (source, dest)) (n'.1 !! (source, dest)).
Proof.
  intros O n n' l H. induction H; intros Hdom H1 ? ? Hin.
  1: apply option_biforall_refl; intros; apply Signal_eq_refl.
  eapply option_biforall_trans.
    1: by apply Signal_eq_trans.
    2: apply IHclosureNodeSem. 3-4: set_solver.
    2: eapply reductions_preserve_O_dom; [|eassumption].
    2: eapply n_trans; [ exact H | apply n_refl ].
  inversion H; subst; simpl in *.
  3-4: apply option_biforall_refl; intros; apply Signal_eq_refl.
  * unfold etherAdd. destruct (decide ((ι, ι') = (source, dest))).
    - inv e. case_match; exfalso; apply H1 in Hin; try assumption; set_solver.
    - break_match_goal; setoid_rewrite lookup_insert_ne; try assumption; auto.
      all: apply option_biforall_refl; intros; apply Signal_eq_refl.
  * unfold etherPop in H2. destruct (decide ((ι1, ι) = (source, dest))).
    - inv e.
      case_match. 2: congruence. destruct l0; try congruence. inv H2.
      exfalso. clear -Hin Hdom. set_solver.
    - case_match; try congruence. destruct l0; try congruence. inv H2.
      setoid_rewrite lookup_insert_ne; auto.
      apply option_biforall_refl; intros; apply Signal_eq_refl.
Qed.

Theorem action_options :
  forall O n n' n'' a ι a' ι',
    n -[a | ι]ₙ-> n' with O ->
    n -[a' | ι']ₙ-> n'' with O ->
    ι = ι' ->
    a = a' \/
    (exists v1 v2 ι1 ι2, a = ASpawn ι1 v1 v2 /\ a' = ASpawn ι2 v1 v2) \/
    (exists s ιs, a = AArrive ιs ι s)
    \/ (exists s ιs, a' = AArrive ιs ι' s).
Proof.
  intros. subst. inv H; inv H0.
  (* NOTATION: single reduction + reduction from l *)
  (* send + send *)
  * subst. put (lookup ι' : ProcessPool -> option Process) on H3 as P.
    setoid_rewrite lookup_insert in P. inv P.
    inv H1; inv H6; try by left.
  (* arrive + send *)
  * right. right. right. by do 2 eexists.
  (* local + send - PIDs should be different *)
  * subst. put (lookup ι' : ProcessPool -> option Process) on H2 as P.
    setoid_rewrite lookup_insert in P. inv P.
    destruct_or!; subst; inv H1; inv H3; try by left.
    all: try (inv H8; by cbn in H6).
    all: try (inv H7; by cbn in H6).
  (* spawn + send - PIDs should be different *)
  * subst. put (lookup ι' : ProcessPool -> option Process) on H2 as P.
    setoid_rewrite lookup_insert in P. inv P.
    inv H1; inv H11; try by left.
  (* send + arrive *)
  * right. right. left. by do 2 eexists.
  (* arrive + arrive *)
  * right. right. left. by do 2 eexists.
  (* local + arrive *)
  * right. right. left. by do 2 eexists.
  (* spawn + arrive *)
  * right. right. left. by do 2 eexists.
  (* send + local - PIDs should be different *)
  * subst. put (lookup ι' : ProcessPool -> option Process) on H4 as P.
    setoid_rewrite lookup_insert in P. inv P.
    destruct_or!; subst; inv H1; inv H7; try by left.
    all: try (inv H; by cbn in H4).
  (* arrive + local *)
  * right. right. right. by do 2 eexists.
  (* local + local - PIDs should be different *)
  * subst. put (lookup ι' : ProcessPool -> option Process) on H3 as P.
    setoid_rewrite lookup_insert in P. inv P.
    destruct_or!; subst; inv H1; inv H4; try by left.
    all: try (inv H7; by cbn in *).
    all: try (inv H8; by cbn in *).
    all: try (inv H; by cbn in *).
  (* spawn + local - PIDs should be different *)
  * subst. put (lookup ι' : ProcessPool -> option Process) on H3 as P.
    setoid_rewrite lookup_insert in P. inv P.
    destruct_or!; subst; inv H1; inv H12; try by left.
    all: try (inv H; by cbn in *).
  (* send + spawn - PIDs should be different *)
  * subst. put (lookup ι' : ProcessPool -> option Process) on H8 as P.
    setoid_rewrite lookup_insert in P. inv P.
    inv H6; inv H11; try by left.
  (* arrive + spawn *)
  * right. right. right. by do 2 eexists.
  (* local + spawn - PIDs should be different *)
  * subst. put (lookup ι' : ProcessPool -> option Process) on H7 as P.
    setoid_rewrite lookup_insert in P. inv P.
    destruct_or!; inv H6; inv H8; try by left.
    inv H12. by cbn in *.
  (* spawn + spawn - PIDs should be different *)
  * subst. put (lookup ι' : ProcessPool -> option Process) on H7 as P.
    setoid_rewrite lookup_insert in P. inv P.
    inv H16. inv H6. subst.
    right. left. do 4 eexists. split; by reflexivity.
Qed.


Theorem normalisation :
  forall O (n n' : Node) l,
   (*  ether_wf n.1 -> *)
    (forall ι, ι ∈ (PIDsOf sendPIDOf l) -> ι ∉ O) -> (* Signals shouldn't be sent to the "world" *)
    (* (forall ι source dest s, In (AArrive source dest s, ι) l ->
                             n'.2 ι <> None) -> (* Signals should not
                                                   arrive to the "world" *) *)
    (* (forall ι ι', n.2 ι' = None -> n.1 ι ι' = []) -> *)
    O ## dom n.2 ->
    n -[l]ₙ->* n' with O ->
    n ~ n' observing O.
Proof.
  intros. apply barbedExpansion_implies_bisim.
  generalize dependent n. generalize dependent n'. revert l H. cofix IH. intros.
  constructor; auto.
  (* 1: split; [ by eapply reduction_produces_preCompatibleNodes; eassumption
            | by eapply reduction_produces_preCompatibleNodes_sym; try eassumption].
  1: now apply ether_wf_preserved in H2. *)
  * intros.
    rename n into A, A' into B, n' into C.
    admit.
  * intros. exists source. eapply reductions_preserve_singals_targeting_O in H2.
    - exact H2.
    - eassumption.
    - assumption.
    - assumption.
  * intros. exists B', (l ++ [(a, ι)]).
    split. 2: split. all: simpl.
    - rewrite app_length. slia.
    - eapply closureNodeSem_trans. eassumption. econstructor. eassumption. constructor.
    - apply barbedExpansion_refl.
(*       eapply ether_wf_preserved. 2: eassumption.
      eapply closureNodeSem_trans. eassumption. econstructor. eassumption. constructor.
 *)
  * intros. exists source, l, n'. split; auto.
    apply option_biforall_refl. intros. by apply Signal_eq_refl.
Abort.

(* It seems that this approach is not going to work, because the two
   cases should be handled separately, since  *)
Theorem compatiblePIDOf_options :
  forall a a',
    compatiblePIDOf a a' \/
    (exists from, (Some from = spawnPIDOf a \/ Some from = spawnPIDOf a') /\
      forall to1 to2, to1 ≠ to2 ->
      to1 ∉ usedPIDsAct a -> to1 ∉ usedPIDsAct a' ->
      to2 ∉ usedPIDsAct a -> to2 ∉ usedPIDsAct a' ->
      compatiblePIDOf (renamePIDAct from to1 a) (renamePIDAct from to2 a')).
Proof.
  intros. destruct a, a'; simpl; try by left; intros.
  * right. exists ι. split. by right. intros. renamePIDPID_case_match. set_solver.
  * right. exists ι. split. by left.  intros. renamePIDPID_case_match. set_solver.
  * right. exists ι. split. by left.  intros. renamePIDPID_case_match. set_solver.
Qed.

Theorem compatiblePIDOf_options_alt :
  forall a a',
    compatiblePIDOf a a' \/
    forall to, to ∉ usedPIDsAct a -> to ∉ usedPIDsAct a' ->
      (exists from, Some from = spawnPIDOf a /\
        compatiblePIDOf (renamePIDAct from to a) a') \/
      (exists from, Some from = spawnPIDOf a' /\
        compatiblePIDOf a (renamePIDAct from to a')).
Proof.
  intros. destruct a, a'; simpl; try by left; intros.
  * right; intros. right. exists ι. split. reflexivity. renamePIDPID_case_match. set_solver.
  * right; intros. left. exists ι. split. reflexivity. renamePIDPID_case_match. set_solver.
  * right; intros. left. exists ι. split. reflexivity. renamePIDPID_case_match. set_solver.
Qed.

(* Theorem compatiblePIDOf_options_alt :
  forall a a' n n' n'' ι ι' O,
    n -[a |ι]ₙ-> n' with O ->
    n -[a' |ι']ₙ-> n'' with O ->
    compatiblePIDOf a a' \/
    forall to, to ∉ usedPIDsAct a -> to ∉ usedPIDsAct a' ->
      (exists from, Some from = spawnPIDOf a /\ from ∉ usedPIDsAct a' /\
        compatiblePIDOf (renamePIDAct from to a) a') \/
      (exists from, Some from = spawnPIDOf a' /\ from ∉ usedPIDsAct a /\
        compatiblePIDOf a (renamePIDAct from to a')) \/
      (exists from, Some from = spawnPIDOf a /\ Some from = spawnPIDOf a' /\
        compatiblePIDOf a (renamePIDAct from to a')).
Proof.
  intros. destruct a, a'; simpl; try by left; intros.
  * right; intros. right. left. exists ι. split. reflexivity. renamePIDPID_case_match. set_solver.
  * right; intros. left. exists ι. split. reflexivity. renamePIDPID_case_match. set_solver.
  * right; intros. left. exists ι. split. reflexivity. renamePIDPID_case_match. set_solver.
Qed.
 *)
(* Theorem compatiblePIDOf_options_alt :
  forall a a' n n' O,
    n -[a |ι]ₙ-> n' with O ->
    compatiblePIDOf a a' \/
    forall to, to ∉ usedPIDsAct a -> to ∉ usedPIDsAct a' ->
      (exists from, Some from = spawnPIDOf a /\ from ∉ usedPIDsAct a' /\
        compatiblePIDOf (renamePIDAct from to a) a') \/
      (exists from, Some from = spawnPIDOf a' /\ from ∉ usedPIDsAct a /\
        compatiblePIDOf a (renamePIDAct from to a')) \/
      (exists from, Some from = spawnPIDOf a /\ Some from = spawnPIDOf a' /\
        ).
Proof.
  intros. destruct a, a'; simpl; try by left; intros.
  * right; intros. right. exists ι. split. reflexivity. renamePIDPID_case_match. set_solver.
  * right; intros. left. exists ι. split. reflexivity. renamePIDPID_case_match. set_solver.
  * right; intros. left. exists ι. split. reflexivity. renamePIDPID_case_match. set_solver.
Qed.
 *)

(*  *)
Theorem local_chainable :
  forall (A B C : Process) (a a' : Action),
     A -⌈a⌉-> B ->
     A -⌈a'⌉-> C ->
     (exists D, B -⌈a⌉-> D /\ C -⌈a'⌉-> D) \/
     (B = C) \/ (* if the actions were the same *)
     B -⌈a'⌉-> C \/ (* if a' is an exit *)
     C -⌈a⌉-> B (* if a is an exit *).
Proof.
  
Abort.

Instance Action_dec : EqDecision Action.
Proof.
  unfold EqDecision. intros. unfold Decision.
  decide equality; subst; auto.
  all: try apply Nat.eq_dec.
  all: try apply Signal_eq_dec.
  all: apply Val_eq_dec.
Defined.

Definition isChainable (a : Action) : Prop :=
match a with
 | AArrive _ _ _ | ASetFlag => False
 | _ => True
end.

Theorem remove_subset :
  forall {A} eq_dec (l : list A) a,
    remove eq_dec a l ⊆ l.
Proof.
  intros.
  apply elem_of_subseteq. intros.
  apply elem_of_list_In in H.
  apply in_remove in H as [H _].
  by apply elem_of_list_In.
Qed.

Definition optional_update (Π : ProcessPool) (a : Action) : ProcessPool :=
match a with
| ASpawn ι v1 v2 =>
  match mk_list v2 with
  | Some l =>
    (* NOTE: keep this consistent with the definition in NodeSemantics.v *)
    match create_result (IApp v1) l [] with
    | Some (r, eff) => ι ↦ inl ([], r, ([], []), [], false) ∥ Π
    | _ => Π
    end
  | _ => Π
  end
| _ => Π
end.

(* This theorem won't hold
   In Lanese et al., Lemma 9 does not hold for this semantics,
   because arrival can change the semantics of receive primops!!!
   E.g., recv_peek_message returns None for empty mailbox, while the
   first message if it is nonempty (and arrival can put a message into the
   empty mailbox).

   In l,
*)
Theorem chain_arrive_later :
  forall O A B C a ι ιs s,
  a <> AArrive ιs ι s ->
  A -[ a | ι ]ₙ-> B with O ->
  isChainable a ->
  A -[ AArrive ιs ι s | ι]ₙ-> C with O ->
  exists D, B -[ AArrive ιs ι s | ι]ₙ-> D with O /\
    ((exists neweth, etherPop ιs ι B.1 = Some (s, neweth) /\
     (neweth, optional_update C.2 a) = D) \/ (* pontentially, sent messages are put into the ether before termination *)
     C -[ a | ι ]ₙ-> D with O).
Proof.
  intros * Hneq HD1 ? HD2.
  inv HD2. 2: { destruct_or!; congruence. }
  inv H7.
  (* message arrival *)
  * inv HD1.
    - put (lookup ι : ProcessPool -> option _) on H2 as P.
      setoid_rewrite lookup_insert in P. inv P.
      inv H7.
     (* message send *)
     (* TODO: proofs for these cases are almost identical *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor.
           }
        right.
        assert (ι
    ↦ inl
    (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
    :: fs0, RValSeq [v0], mailboxPush mb v, links, flag) ∥ prs = ι
    ↦ inl
    (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
    :: fs0, RValSeq [v0], mailboxPush mb v, links, flag) ∥ prs0). {
               apply map_eq. intros.
               clear -H2.
               put (lookup i : ProcessPool -> _) on H2 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_send. by constructor.
      (* exit send *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [
        VPid ι'] [] :: fs0, RValSeq [v0], mailboxPush mb v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [
        VPid ι'] [] :: fs0, RValSeq [v0], mailboxPush mb v, links, flag) ∥ prs0). {
               apply map_eq. intros.
               clear -H2.
               put (lookup i : ProcessPool -> _) on H2 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_send. by constructor.
      (* link send *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] []
      :: fs0, RValSeq [VPid ι'], mailboxPush mb v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] []
      :: fs0, RValSeq [VPid ι'], mailboxPush mb v, links, flag) ∥ prs0). {
               apply map_eq. intros.
               clear -H2.
               put (lookup i : ProcessPool -> _) on H2 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_send. by constructor.
      (* unlink send *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "unlink"%string)) [] []
      :: fs0, RValSeq [VPid ι'], mailboxPush mb v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "unlink"%string)) [] []
      :: fs0, RValSeq [VPid ι'], mailboxPush mb v, links, flag) ∥ prs0). {
               apply map_eq. intros.
               clear -H2.
               put (lookup i : ProcessPool -> _) on H2 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_send. by constructor.
    (* arrivals - cannot happen *)
    - inv H.
    (* local actions *)
    - put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. inv P.
(* case separation is needed at this point, because
 exists can't be instantiated first, also ε actions
 could terminate a process -> no chaining

TODO: this cases a lot of boiler plate
*)
      destruct_or! H8; subst; inv H2.
      (* silent steps *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι ↦ inl (fs, e, mailboxPush mb v, links, flag) ∥ prs = ι ↦ inl (fs, e, mailboxPush mb v, links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. by constructor. by left.
      (* recv_wait_timeout 0 *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      VLit 0%Z], mailboxPush mb v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      VLit 0%Z], mailboxPush mb v, links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. by constructor. by left.
      (* recv_wait_timeout error *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      v0], mailboxPush mb v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      v0], mailboxPush mb v, links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. by constructor. by left.
      (* self *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "self"%string)) [] []
      :: fs0, RBox, mailboxPush mb v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "self"%string)) [] []
      :: fs0, RBox, mailboxPush mb v, links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. by constructor. by right; left.
      (* recv_peek_message - success *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox,
      mailboxPush mb v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox,
      mailboxPush mb v, links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. econstructor.
             { destruct mb; clear-H10. simpl.
               destruct l0; inv H10. reflexivity. }
             by right; right; left.
      (* recv_peek_message - fail - This cannot be proved
         after pushing a message, peekMessage won't fail anymore *)
      + admit.
      (* recv_next *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_next") [] [] :: fs0, RBox, 
      mailboxPush mb v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_next") [] [] :: fs0, RBox, 
      mailboxPush mb v, links, flag) ∥ Π). {
           apply map_eq. intros.
           clear -H1.
           put (lookup i : ProcessPool -> _) on H1 as HH.
           destruct (decide (i = ι)).
           * subst. by setoid_rewrite lookup_insert.
           * setoid_rewrite lookup_insert_ne; auto.
             setoid_rewrite lookup_insert_ne in HH; auto.
         }
         setoid_rewrite H0.
         destruct mb as [old new]. destruct new.
         1: admit. (* This won't work if the mailbox is empty *)
         assert (mailboxPush (recvNext (old, v0 :: new)) v = recvNext (mailboxPush (old, v0 :: new) v)) by reflexivity.
         rewrite H2.
         eapply n_other. econstructor.
         by right; right; left.
      (* removeMessage *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "remove_message") [] [] :: fs0, RBox,
      mailboxPush mb v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "remove_message") [] [] :: fs0, RBox,
      mailboxPush mb v, links, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other.
        econstructor.
        {
          clear -H10. destruct mb. simpl in *.
          destruct l0; invSome. simpl.
          by rewrite app_assoc.
        }
        by right; right; left.
      (* recv_wait_timeout infinity *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0,
      RValSeq [VLit "infinity"%string], mailboxPush (oldmb, msg :: newmb) v, links,
      flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0,
      RValSeq [VLit "infinity"%string], mailboxPush (oldmb, msg :: newmb) v, links,
      flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
        setoid_rewrite H0.
        eapply n_other.
        econstructor.
        by right; right; left.
      (* normal termination *)
      + admit. (* arrive can't be chained on a dead process *)
      (* exceptional termination *)
      + admit. (* arrive can't be chained on a dead process *)
      (* setflag *)
      + inv H.
    (* spawn *)
    - inv H12.
      eexists. split.
      1: {
        setoid_rewrite insert_commute. 2: {
          intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
        }
        constructor. eassumption.
        constructor. }
      right.
      assert (ι ↦ inl (fs, e, mailboxPush mb v, links, flag) ∥ prs = ι ↦ inl (fs, e, mailboxPush mb v, links, flag) ∥  Π). {
        apply map_eq. intros.
        clear -H1.
        put (lookup i : ProcessPool -> _) on H1 as HH.
        destruct (decide (i = ι)).
        * subst. by setoid_rewrite lookup_insert.
        * setoid_rewrite lookup_insert_ne; auto.
          setoid_rewrite lookup_insert_ne in HH; auto.
      }
      setoid_rewrite H0.
      setoid_rewrite insert_commute. 2: {
        intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
      }
      eapply n_spawn; try eassumption.
      1: {
        rewrite <- H0. rewrite H1 in H5.
        clear -H5 H7 H6.
        intro. apply isUsedPool_insert_1 in H as [H | [H | H]].
        * apply H5. apply isUsedPool_insert_2. by left.
        * subst. apply H5. left. by setoid_rewrite lookup_insert.
        * simpl in H. rewrite flat_union_app in H. simpl in H.
          assert (ι' ∉ usedPIDsVal v). {
            intro. apply H7.
            unfold etherPop in H6. repeat case_match; try congruence.
            subst. inv H6.
            right. right. do 3 eexists. split. exact H1.
            set_solver.
          }
          apply H5. right. exists ι. eexists.
          split. by setoid_rewrite lookup_insert.
          simpl. set_solver.
      }
      1: {
        clear -H6 H7.
        intro. eapply appearsEther_etherPop_rev in H; eauto.
      }
      put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. inv P.
      constructor; assumption.
  (* exit dropped - it is potentially influenced by links, process flag *)
  * inv HD1.
    - put (lookup ι : ProcessPool -> option _) on H2 as P.
      setoid_rewrite lookup_insert in P. inv P.
      inv H7.
     (* message send *)
     (* TODO: proofs for these cases are almost identical *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor. set_solver.
           }
        right.
        eapply n_send. by constructor.
      (* exit send *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor. set_solver.
           }
        right.
        eapply n_send. by constructor.
      (* link send *)
      + admit. (* can't be done *)
      (* unlink send *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor.
             pose proof (remove_subset Nat.eq_dec links ι').
             clear -H8 H0. set_solver.
           }
        right.
        eapply n_send. by constructor.
    (* arrivals - cannot happen *)
    - inv H.
    (* local actions *)
    - put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. inv P.
(* case separation is needed at this point, because
 exists can't be instantiated first, also ε actions
 could terminate a process -> no chaining

TODO: this cases a lot of boiler plate
*)
      destruct_or! H9; subst; inv H2.
      (* silent steps *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by left.
      (* recv_wait_timeout 0 *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by left.
      (* recv_wait_timeout error *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by left.
      (* self *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by right;left.
      (* recv_peek_message - success *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by right;right;left.
      (* recv_peek_message - fail *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by intuition.
      (* recv_next *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by intuition.
      (* removeMessage *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by intuition.
      (* recv_wait_timeout infinity *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by intuition.
      (* normal termination *)
      + admit. (* arrive can't be chained on a dead process *)
      (* exceptional termination *)
      + admit. (* arrive can't be chained on a dead process *)
      (* setflag *)
      + inv H.
    (* spawn *)
    - inv H13.
      put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. inv P.
      eexists. split.
      1: {
        setoid_rewrite insert_commute. 2: {
          intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
        }
        constructor. eassumption.
        constructor. assumption.
      }
      right.
      setoid_rewrite insert_commute. 2: {
        intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
      }
      eapply n_spawn; try eassumption.
      1: {
        clear -H6 H7.
        intro. eapply appearsEther_etherPop_rev in H; eauto.
      }
      constructor; assumption.
  (* exit terminates - it is potentially influenced by links, process flag *)
  * inv HD1.
    - put (lookup ι : ProcessPool -> option _) on H2 as P.
      setoid_rewrite lookup_insert in P. inv P.
      inv H7.
     (* message send *)
     (* TODO: proofs for these cases are almost identical *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: by apply etherPop_greater.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H2 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* exit send *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: by apply etherPop_greater.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H2 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* link send - can't be done, since links are potentially modified *)
      + admit.
      (* unlink send - can't be done, since links are potentially modified *)
      + admit.
    (* arrivals - cannot happen *)
    - inv H.
    (* local actions *)
    - put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. inv P.
(* case separation is needed at this point, because
 exists can't be instantiated first, also ε actions
 could terminate a process -> no chaining

TODO: this cases a lot of boiler plate
*)
      destruct_or! H9; subst; inv H2.
      (* silent steps *)
      + eexists. split.
        1: { constructor. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: eassumption.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H1 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* recv_wait_timeout 0 *)
      + eexists. split.
        1: { constructor. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: eassumption.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H1 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* recv_wait_timeout error *)
      + eexists. split.
        1: { constructor. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: eassumption.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H1 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* self *)
      + eexists. split.
        1: { constructor. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: eassumption.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H1 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* recv_peek_message - success *)
      + eexists. split.
        1: { constructor. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: eassumption.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H1 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* recv_peek_message - fail *)
      + eexists. split.
        1: { constructor. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: eassumption.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H1 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* recv_next *)
      + eexists. split.
        1: { constructor. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: eassumption.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H1 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* removeMessage *)
      + eexists. split.
        1: { constructor. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: eassumption.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H1 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* recv_wait_timeout infinity *)
      + eexists. split.
        1: { constructor. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: eassumption.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H1 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* normal termination *)
      + admit. (* arrive can't be chained on a dead process *)
      (* exceptional termination *)
      + admit. (* arrive can't be chained on a dead process *)
      (* setflag *)
      + inv H.
    (* spawn -
       if the exit is delivered first, a process cannot be
       spawned *)
    - inv H13.
      put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. inv P.
      eexists. split.
      1: {
        setoid_rewrite insert_commute. 2: {
          intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
        }
        constructor. eassumption.
        apply p_exit_terminate. eassumption.
      }
      left.
      assert (ι' <> ι). {
        intro. subst. apply H5. left. by setoid_rewrite lookup_insert.
      }
      eexists; split. simpl. eassumption.
      simpl. rewrite H2. simpl in H9. rewrite H9.
      f_equal.
      setoid_rewrite insert_commute at 1; auto.
      apply map_eq. intros.
      destruct (decide (i = ι)). 2: destruct (decide (i = ι')).
      all: subst.
      1: by setoid_rewrite lookup_insert.
      1: setoid_rewrite lookup_insert_ne; try lia.
      1: by setoid_rewrite lookup_insert.
      do 2 (setoid_rewrite lookup_insert_ne; try lia).
      put (lookup i : ProcessPool -> _) on H1 as H'.
      simpl in H'.
      by (setoid_rewrite lookup_insert_ne in H'; try lia).
  (* exit converted - it is potentially influenced by links, process flag, mailbox *)
  * inv HD1.
    - put (lookup ι : ProcessPool -> option _) on H2 as P.
      setoid_rewrite lookup_insert in P. inv P.
      inv H7.
     (* message send *)
     (* TODO: proofs for these cases are almost identical *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             apply p_exit_convert. assumption.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
      :: fs0, RValSeq [v],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
      :: fs0, RValSeq [v],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs0). {
               apply map_eq. intros.
               clear -H2.
               put (lookup i : ProcessPool -> _) on H2 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_send. by constructor.
      (* exit send *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             apply p_exit_convert. assumption.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [
        VPid ι'] [] :: fs0, RValSeq [v],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [
        VPid ι'] [] :: fs0, RValSeq [v],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs0). {
               apply map_eq. intros.
               clear -H2.
               put (lookup i : ProcessPool -> _) on H2 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_send. by constructor.
      (* link send - maybe this should not be proved? *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             apply p_exit_convert.
             pose proof (remove_subset Nat.eq_dec links ι').
             clear -H8 H0. set_solver.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] []
      :: fs0, RValSeq [VPid ι'],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] []
      :: fs0, RValSeq [VPid ι'],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs0). {
               apply map_eq. intros.
               clear -H2.
               put (lookup i : ProcessPool -> _) on H2 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_send. by constructor.
      (* unlink send - can't be proved, list of links influence the behaviour of exits *)
      + admit.
    (* arrivals - cannot happen *)
    - inv H.
    (* local actions *)
    - put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. inv P.
(* case separation is needed at this point, because
 exists can't be instantiated first, also ε actions
 could terminate a process -> no chaining

TODO: this cases a lot of boiler plate
*)
      destruct_or! H9; subst; inv H2.
      (* silent steps *)
      + eexists. split.
        1: { constructor. eassumption. apply p_exit_convert. assumption. }
        right.
        assert (ι
 ↦ inl
     (fs, e, mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]),
      links, true) ∥ prs = ι
 ↦ inl
     (fs, e, mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]),
      links, true) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. by constructor. by left.
      (* recv_wait_timeout 0 *)
      + eexists. split.
        1: { constructor. eassumption. by apply p_exit_convert. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      VLit 0%Z],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      VLit 0%Z],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. by constructor. by left.
      (* recv_wait_timeout error *)
      + eexists. split.
        1: { constructor. eassumption. by apply p_exit_convert. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [v],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [v],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. by constructor. by left.
      (* self *)
      + eexists. split.
        1: { constructor. eassumption. by apply p_exit_convert. }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "self"%string)) [] []
      :: fs0, RBox,
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "self"%string)) [] []
      :: fs0, RBox,
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. by constructor. by right; left.
      (* recv_peek_message - success *)
      + eexists. split.
        1: { constructor. eassumption. by apply p_exit_convert. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox,
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox,
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. econstructor.
             { destruct mb; clear-H11. simpl.
               destruct l0; inv H11. reflexivity. }
             by right; right; left.
      (* recv_peek_message - fail - This cannot be proved
         after pushing a message, peekMessage won't fail anymore *)
      + admit.
      (* recv_next *)
      + eexists. split.
        1: { constructor. eassumption. by apply p_exit_convert. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_next") [] [] :: fs0, RBox,
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_next") [] [] :: fs0, RBox,
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ Π). {
           apply map_eq. intros.
           clear -H1.
           put (lookup i : ProcessPool -> _) on H1 as HH.
           destruct (decide (i = ι)).
           * subst. by setoid_rewrite lookup_insert.
           * setoid_rewrite lookup_insert_ne; auto.
             setoid_rewrite lookup_insert_ne in HH; auto.
         }
         setoid_rewrite H0.
         destruct mb as [old new]. destruct new.
         1: admit. (* This won't work if the mailbox is empty *)
         assert (mailboxPush (recvNext (old, v :: new)) (VTuple [VLit "EXIT"%string; VPid ιs; reason]) = recvNext (mailboxPush (old, v :: new) (VTuple [VLit "EXIT"%string; VPid ιs; reason]))) by reflexivity.
         rewrite H2.
         eapply n_other. econstructor.
         by right; right; left.
      (* removeMessage *)
      + eexists. split.
        1: { constructor. eassumption. by apply p_exit_convert. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "remove_message") [] [] :: fs0, RBox,
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "remove_message") [] [] :: fs0, RBox,
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ Π). {
         apply map_eq. intros.
         clear -H1.
         put (lookup i : ProcessPool -> _) on H1 as HH.
         destruct (decide (i = ι)).
         * subst. by setoid_rewrite lookup_insert.
         * setoid_rewrite lookup_insert_ne; auto.
           setoid_rewrite lookup_insert_ne in HH; auto.
       }
       setoid_rewrite H0.
       eapply n_other.
       econstructor.
       {
         clear -H11. destruct mb. simpl in *.
         destruct l0; invSome. simpl.
         by rewrite app_assoc.
       }
       by right; right; left.
      (* recv_wait_timeout infinity *)
      + eexists. split.
        1: { constructor. eassumption. by apply p_exit_convert. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0,
      RValSeq [VLit "infinity"%string],
      mailboxPush (oldmb, msg :: newmb)
        (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links, true) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0,
      RValSeq [VLit "infinity"%string],
      mailboxPush (oldmb, msg :: newmb)
        (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links, true) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other.
        econstructor.
        by right; right; left.
      (* normal termination *)
      + admit. (* arrive can't be chained on a dead process *)
      (* exceptional termination *)
      + admit. (* arrive can't be chained on a dead process *)
      (* setflag *)
      + inv H.
    (* spawn *)
    - inv H13.
      put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. inv P.
      eexists. split.
      1: {
        setoid_rewrite insert_commute. 2: {
          intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
        }
        constructor. eassumption.
        by apply p_exit_convert.
      }
      right.
      assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "spawn"%string))
        [VClos ext id vars e0] [] :: fs0, RValSeq [v2],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "spawn"%string))
        [VClos ext id vars e0] [] :: fs0, RValSeq [v2],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ Π). {
        apply map_eq. intros.
        clear -H1.
        put (lookup i : ProcessPool -> _) on H1 as HH.
        destruct (decide (i = ι)).
        * subst. by setoid_rewrite lookup_insert.
        * setoid_rewrite lookup_insert_ne; auto.
          setoid_rewrite lookup_insert_ne in HH; auto.
      }
      setoid_rewrite H0.
      setoid_rewrite insert_commute. 2: {
        intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
      }
      eapply n_spawn; try eassumption.
      1: {
        rewrite <- H0. rewrite H1 in H5.
        clear -H5 H7 H6.
        intro. apply isUsedPool_insert_1 in H as [H | [H | H]].
        * apply H5. apply isUsedPool_insert_2. by left.
        * subst. apply H5. left. by setoid_rewrite lookup_insert.
        * simpl in H. rewrite flat_union_app in H. simpl in H.
          assert (ι' ∉ usedPIDsVal reason /\ ι' <> ιs). {
            unfold etherPop in H6. repeat case_match; try congruence.
            split.
            * intro. apply H7.
              subst. inv H6.
              right. right. do 3 eexists. split. exact H0.
              set_solver.
            * intro. subst. apply H7. right. left.
              eexists. by rewrite H0.
          }
          apply H5. right. exists ι. eexists.
          split. by setoid_rewrite lookup_insert.
          simpl. set_solver.
      }
      1: {
        clear -H6 H7.
        intro. eapply appearsEther_etherPop_rev in H; eauto.
      }
      constructor; assumption.
  (* link arrives *)
  * inv HD1.
    - put (lookup ι : ProcessPool -> option _) on H2 as P.
      setoid_rewrite lookup_insert in P. inv P.
      inv H7.
     (* message send *)
     (* TODO: proofs for these cases are almost identical *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
      :: fs0, RValSeq [v], mb, ιs :: links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
      :: fs0, RValSeq [v], mb, ιs :: links, flag) ∥ prs0). {
               apply map_eq. intros.
               clear -H2.
               put (lookup i : ProcessPool -> _) on H2 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_send. by constructor.
      (* exit send *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [
        VPid ι'] [] :: fs0, RValSeq [v], mb, ιs :: links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [
        VPid ι'] [] :: fs0, RValSeq [v], mb, ιs :: links, flag) ∥ prs0). {
               apply map_eq. intros.
               clear -H2.
               put (lookup i : ProcessPool -> _) on H2 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_send. by constructor.
      (* link send - maybe this should not be proved? *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] []
      :: fs0, RValSeq [VPid ι'], mb, ιs :: links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] []
      :: fs0, RValSeq [VPid ι'], mb, ιs :: links, flag) ∥ prs0). {
               apply map_eq. intros.
               clear -H2.
               put (lookup i : ProcessPool -> _) on H2 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_send. admit. (* TODO: links should be formalised as sets *)
      (* unlink send - can't be proved if the same link is established and deleted in the two reductions *)
      + admit.
    (* arrivals - cannot happen *)
    - inv H.
    (* local actions *)
    - put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. inv P.
(* case separation is needed at this point, because
 exists can't be instantiated first, also ε actions
 could terminate a process -> no chaining

TODO: this cases a lot of boiler plate
*)
      destruct_or! H8; subst; inv H2.
      (* silent steps *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι ↦ inl (fs, e, mb, ιs :: links, flag) ∥ prs = ι ↦ inl (fs, e, mb, ιs :: links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. by constructor. by left.
      (* recv_wait_timeout 0 *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      VLit 0%Z], mb, ιs :: links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      VLit 0%Z], mb, ιs :: links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. by constructor. by left.
      (* recv_wait_timeout error *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [v], mb,
      ιs :: links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [v], mb,
      ιs :: links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. by constructor. by left.
      (* self *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "self"%string)) [] []
      :: fs0, RBox, mb, ιs :: links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "self"%string)) [] []
      :: fs0, RBox, mb, ιs :: links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. by constructor. by right; left.
      (* recv_peek_message - success *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      ιs :: links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      ιs :: links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. econstructor.
             assumption.
             by right; right; left.
      (* recv_peek_message - fail *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      ιs :: links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      ιs :: links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. econstructor.
             assumption.
             by right; right; left.
      (* recv_next *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_next") [] [] :: fs0, RBox, mb, 
      ιs :: links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_next") [] [] :: fs0, RBox, mb, 
      ιs :: links, flag) ∥ Π). {
           apply map_eq. intros.
           clear -H1.
           put (lookup i : ProcessPool -> _) on H1 as HH.
           destruct (decide (i = ι)).
           * subst. by setoid_rewrite lookup_insert.
           * setoid_rewrite lookup_insert_ne; auto.
             setoid_rewrite lookup_insert_ne in HH; auto.
         }
         setoid_rewrite H0.
         eapply n_other. econstructor.
         by right; right; left.
      (* removeMessage *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "remove_message") [] [] :: fs0, RBox, mb,
      ιs :: links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "remove_message") [] [] :: fs0, RBox, mb,
      ιs :: links, flag) ∥ Π). {
         apply map_eq. intros.
         clear -H1.
         put (lookup i : ProcessPool -> _) on H1 as HH.
         destruct (decide (i = ι)).
         * subst. by setoid_rewrite lookup_insert.
         * setoid_rewrite lookup_insert_ne; auto.
           setoid_rewrite lookup_insert_ne in HH; auto.
       }
       setoid_rewrite H0.
       eapply n_other.
       econstructor.
       assumption.
       by right; right; left.
      (* recv_wait_timeout infinity *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0,
      RValSeq [VLit "infinity"%string], (oldmb, msg :: newmb), 
      ιs :: links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0,
      RValSeq [VLit "infinity"%string], (oldmb, msg :: newmb), 
      ιs :: links, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other.
        econstructor.
        by right; right; left.
      (* normal termination *)
      + admit. (* arrive can't be chained on a dead process *)
      (* exceptional termination *)
      + admit. (* arrive can't be chained on a dead process *)
      (* setflag *)
      + inv H.
    (* spawn *)
    - inv H12.
      put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. inv P.
      eexists. split.
      1: {
        setoid_rewrite insert_commute. 2: {
          intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
        }
        constructor. eassumption. constructor.
      }
      right.
      assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "spawn"%string))
        [VClos ext id vars e0] [] :: fs0, RValSeq [v2], mb, 
      ιs :: links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "spawn"%string))
        [VClos ext id vars e0] [] :: fs0, RValSeq [v2], mb, 
      ιs :: links, flag) ∥ Π). {
        apply map_eq. intros.
        clear -H1.
        put (lookup i : ProcessPool -> _) on H1 as HH.
        destruct (decide (i = ι)).
        * subst. by setoid_rewrite lookup_insert.
        * setoid_rewrite lookup_insert_ne; auto.
          setoid_rewrite lookup_insert_ne in HH; auto.
      }
      setoid_rewrite H0.
      setoid_rewrite insert_commute. 2: {
        intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
      }
      eapply n_spawn; try eassumption.
      1: {
        rewrite <- H0. rewrite H1 in H5.
        clear -H5 H7 H6.
        intro. apply isUsedPool_insert_1 in H as [H | [H | H]].
        * apply H5. apply isUsedPool_insert_2. by left.
        * subst. apply H5. left. by setoid_rewrite lookup_insert.
        * simpl in H.
          assert (ι' <> ιs). {
            unfold etherPop in H6. repeat case_match; try congruence.
            intro. subst. apply H7. right. left.
            eexists. by rewrite H0.
          }
          apply H5. right. exists ι. eexists.
          split. by setoid_rewrite lookup_insert.
          simpl. set_solver.
      }
      1: {
        clear -H6 H7.
        intro. eapply appearsEther_etherPop_rev in H; eauto.
      }
      constructor; assumption.
  (* unlink arrives *)
  * inv HD1.
    - put (lookup ι : ProcessPool -> option _) on H2 as P.
      setoid_rewrite lookup_insert in P. inv P.
      inv H7.
     (* message send *)
     (* TODO: proofs for these cases are almost identical *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
      :: fs0, RValSeq [v], mb, remove numbers.Nat.eq_dec ιs links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
      :: fs0, RValSeq [v], mb, remove numbers.Nat.eq_dec ιs links, flag) ∥ prs0). {
               apply map_eq. intros.
               clear -H2.
               put (lookup i : ProcessPool -> _) on H2 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_send. by constructor.
      (* exit send *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [
        VPid ι'] [] :: fs0, RValSeq [v], mb, remove numbers.Nat.eq_dec ιs links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [
        VPid ι'] [] :: fs0, RValSeq [v], mb, remove numbers.Nat.eq_dec ιs links, flag) ∥ prs0). {
               apply map_eq. intros.
               clear -H2.
               put (lookup i : ProcessPool -> _) on H2 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_send. by constructor.
      (* link send - maybe this should not be proved? *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] []
      :: fs0, RValSeq [VPid ι'], mb, remove numbers.Nat.eq_dec ιs links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] []
      :: fs0, RValSeq [VPid ι'], mb, remove numbers.Nat.eq_dec ιs links, flag) ∥ prs0). {
               apply map_eq. intros.
               clear -H2.
               put (lookup i : ProcessPool -> _) on H2 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_send. admit. (* TODO: links should be formalised as sets *)
      (* unlink send - can't be proved if the same link is established and deleted in the two reductions *)
      + admit.
    (* arrivals - cannot happen *)
    - inv H.
    (* local actions *)
    - put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. inv P.
(* case separation is needed at this point, because
 exists can't be instantiated first, also ε actions
 could terminate a process -> no chaining

TODO: this cases a lot of boiler plate
*)
      destruct_or! H8; subst; inv H2.
      (* silent steps *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι ↦ inl (fs, e, mb, remove numbers.Nat.eq_dec ιs links, flag) ∥ prs = ι ↦ inl (fs, e, mb, remove numbers.Nat.eq_dec ιs links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. by constructor. by left.
      (* recv_wait_timeout 0 *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      VLit 0%Z], mb, remove numbers.Nat.eq_dec ιs links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      VLit 0%Z], mb, remove numbers.Nat.eq_dec ιs links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. by constructor. by left.
      (* recv_wait_timeout error *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [v], mb,
      remove numbers.Nat.eq_dec ιs links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [v], mb,
      remove numbers.Nat.eq_dec ιs links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. by constructor. by left.
      (* self *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "self"%string)) [] []
      :: fs0, RBox, mb, remove numbers.Nat.eq_dec ιs links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "self"%string)) [] []
      :: fs0, RBox, mb, remove numbers.Nat.eq_dec ιs links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. by constructor. by right; left.
      (* recv_peek_message - success *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      remove numbers.Nat.eq_dec ιs links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      remove numbers.Nat.eq_dec ιs links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. econstructor.
             assumption.
             by right; right; left.
      (* recv_peek_message - fail *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      remove numbers.Nat.eq_dec ιs links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      remove numbers.Nat.eq_dec ιs links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. econstructor.
             assumption.
             by right; right; left.
      (* recv_next *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_next") [] [] :: fs0, RBox, mb, 
      remove numbers.Nat.eq_dec ιs links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_next") [] [] :: fs0, RBox, mb, 
      remove numbers.Nat.eq_dec ιs links, flag) ∥ Π). {
           apply map_eq. intros.
           clear -H1.
           put (lookup i : ProcessPool -> _) on H1 as HH.
           destruct (decide (i = ι)).
           * subst. by setoid_rewrite lookup_insert.
           * setoid_rewrite lookup_insert_ne; auto.
             setoid_rewrite lookup_insert_ne in HH; auto.
         }
         setoid_rewrite H0.
         eapply n_other. econstructor.
         by right; right; left.
      (* removeMessage *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "remove_message") [] [] :: fs0, RBox, mb,
      remove numbers.Nat.eq_dec ιs links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "remove_message") [] [] :: fs0, RBox, mb,
      remove numbers.Nat.eq_dec ιs links, flag) ∥ Π). {
         apply map_eq. intros.
         clear -H1.
         put (lookup i : ProcessPool -> _) on H1 as HH.
         destruct (decide (i = ι)).
         * subst. by setoid_rewrite lookup_insert.
         * setoid_rewrite lookup_insert_ne; auto.
           setoid_rewrite lookup_insert_ne in HH; auto.
       }
       setoid_rewrite H0.
       eapply n_other.
       econstructor.
       assumption.
       by right; right; left.
      (* recv_wait_timeout infinity *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0,
      RValSeq [VLit "infinity"%string], (oldmb, msg :: newmb), 
      remove numbers.Nat.eq_dec ιs links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0,
      RValSeq [VLit "infinity"%string], (oldmb, msg :: newmb), 
      remove numbers.Nat.eq_dec ιs links, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other.
        econstructor.
        by right; right; left.
      (* normal termination *)
      + admit. (* arrive can't be chained on a dead process *)
      (* exceptional termination *)
      + admit. (* arrive can't be chained on a dead process *)
      (* setflag *)
      + inv H.
    (* spawn *)
    - inv H12.
      put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. inv P.
      eexists. split.
      1: {
        setoid_rewrite insert_commute. 2: {
          intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
        }
        constructor. eassumption. constructor.
      }
      right.
      assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "spawn"%string))
        [VClos ext id vars e0] [] :: fs0, RValSeq [v2], mb, 
      remove numbers.Nat.eq_dec ιs links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "spawn"%string))
        [VClos ext id vars e0] [] :: fs0, RValSeq [v2], mb, 
      remove numbers.Nat.eq_dec ιs links, flag) ∥ Π). {
        apply map_eq. intros.
        clear -H1.
        put (lookup i : ProcessPool -> _) on H1 as HH.
        destruct (decide (i = ι)).
        * subst. by setoid_rewrite lookup_insert.
        * setoid_rewrite lookup_insert_ne; auto.
          setoid_rewrite lookup_insert_ne in HH; auto.
      }
      setoid_rewrite H0.
      setoid_rewrite insert_commute. 2: {
        intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
      }
      eapply n_spawn; try eassumption.
      1: {
        rewrite <- H0. rewrite H1 in H5.
        clear -H5 H7 H6.
        intro. apply isUsedPool_insert_1 in H as [H | [H | H]].
        * apply H5. apply isUsedPool_insert_2. by left.
        * subst. apply H5. left. by setoid_rewrite lookup_insert.
        * apply H5. right. exists ι. eexists.
          split. by setoid_rewrite lookup_insert.
          simpl.
          clear -H. simpl in H.
          pose proof (remove_subset Nat.eq_dec links ιs).
          set_solver.
      }
      1: {
        clear -H6 H7.
        intro. eapply appearsEther_etherPop_rev in H; eauto.
      }
      constructor; assumption.
Admitted.

Theorem action_chainable :
  (* NOTE: only l (and n n') can be constrained for the proof of normalisation!
     NOTE: don't forget that 
           we would like to prove equivalences like map ≈ paralell map *)
  forall l O A C, A -[l]ₙ->* C with O ->
    forall B a ι, A -[a | ι]ₙ-> B with O ->
      Forall (compatiblePIDOf a ∘ fst) l -> (* If some PID is not compatible, 
                                               we rename l *)
      Forall (isChainable ∘ fst) l ->
      (* (a, ι) ∈ l \/ *)
      (exists D l'', ((exists l', C -[l']ₙ->* D with O /\ length l' ≤ 1)
       \/ (exists from fresh, D = prod_map (renamePIDEther from fresh) (renamePIDPool from fresh) C) (* this part is needed for spawns + potentially exits in the future *))
       /\ B -[l'']ₙ->* D with O)
      (* (exists n''', n'' -[a | ι]ₙ-> n''' with O) \/ (* normal arrivals, sends, other processes can take the step at the end *)
      (True) (* if some processes die due to l *) *).
Proof.
  induction l using list_length_ind. rename H into IH.
  destruct l; intros ? ? ? HD1 ? ? ? HD2 Hcompat Harrives.
  {
    inv HD1. exists B, []. split. left. exists [(a, ι)]. split_and!; simpl.
    * econstructor. eassumption. constructor.
    * lia.
    * constructor.
  }
  {
    inv HD1.
    destruct (decide (ι = ι0)).
    {
      destruct (decide (a0 = a)). {
        subst. eapply concurrent_determinism in H2.
        2: exact HD2. subst.
        subst. exists C, l. split. left. exists []. split.
        - constructor.
        - slia.
        - assumption.
      }
      rename n into HX.
      subst.
      epose proof (action_options _ _ _ _ _ _ _ _ H2 HD2 eq_refl).
      intuition; destruct_hyps.
      * subst.
        assert (exists to, to ∉ flat_union (usedPIDsAct ∘ fst) l /\ ¬appearsEther to B.1 /\ ¬appearsEther to n'.1 /\ ¬isUsedPool to B.2 /\ ¬isUsedPool to n'.2 /\ to ∉ O). {
          admit. (* freshness *)
        }
        destruct H as [to [I1 [I2 [I3 [I4 [I5 I6]]]]]].
        exists (prod_map (renamePIDEther x1 to) (renamePIDPool x1 to) C), (map (prod_map (renamePIDAct x1 to) (renamePIDPID_sym x1 to)) l).
        split. right.
        - do 2 eexists. reflexivity.
        - replace B with (prod_map (renamePIDEther x1 to) (renamePIDPool x1 to) n').
          2: {
            inv HD2. 1: destruct_or!; congruence.
            inv H2. 1: destruct_or!; congruence.
            put (lookup ι0 : ProcessPool -> option Process) on H0 as P.
            setoid_rewrite lookup_insert in P. inv P.
            simpl. rewrite does_not_appear_renamePID_ether; auto.
            unfold renamePIDPool. clear IH.
            do 2 setoid_rewrite fmap_insert.
            do 2 (setoid_rewrite kmap_insert; auto).
            simpl.
            setoid_rewrite isNotUsed_renamePID_pool; auto.
            all: admit. (* TODO: technical, x1 is not used anywhere except the new PID *)
          }
          apply renamePID_is_preserved_node_semantics_steps; auto.
          by rewrite <- surjective_pairing, <- surjective_pairing.
      * subst. inv Harrives. destruct H1. (* arrives can't be in l *)
      * subst. inv Harrives. inv Hcompat.
        eapply chain_arrive_later in HD2; eauto.
        destruct HD2 as [D HD2].
        eapply IH in H4. 2: slia. 2: exact HD2.
        2-3: assumption.
        destruct H4 as [Dnew [l'' H4]].
        destruct H4 as [H4_1 H4_2].
        do 2 eexists. split.
        2: {
          
        }
      
      
        (* every combination of arrives should be checked *)
        inv HD2. 2: { destruct_or!; congruence. }
        inv H8.
        (* message arrival *)
        - inv H2.
          + put (lookup ι0 : ProcessPool -> option _) on H1 as P.
            setoid_rewrite lookup_insert in P. inv P.
            inv H8.
            (* message send *)
            (* TODO: proofs for these cases are almost identical *)
            ** eapply IH in H4. 2: slia. 3-4: by destruct_foralls.
               2: {
                 constructor.
                 apply etherPop_greater. eassumption.
                 by constructor.
               }
               destruct H4 as [D [l'' H4]].
               destruct H4 as [H4_1 H4_2].
               do 2 eexists. split.
                2: { eapply n_trans. 2: exact H4_2.
                       assert (ι0
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
      :: fs0, RValSeq [v0], mailboxPush mb v, links, flag) ∥ prs = ι0
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
      :: fs0, RValSeq [v0], mailboxPush mb v, links, flag) ∥ prs0). {
                         apply map_eq. intros.
                         clear -H1.
                         put (lookup i : ProcessPool -> _) on H1 as HH.
                         destruct (decide (i = ι0)).
                         * subst. by setoid_rewrite lookup_insert.
                         * setoid_rewrite lookup_insert_ne; auto.
                           setoid_rewrite lookup_insert_ne in HH; auto.
                       }
                       setoid_rewrite H.
                       eapply n_send. by constructor.
                  }
               destruct H4_1.
               -- destruct_hyps. left. eexists; split; eassumption.
               -- destruct_hyps. right. do 2 eexists; eassumption.
            (* exit send *)
            ** eapply IH in H4. 2: slia. 3-4: by destruct_foralls.
               2: {
                 constructor.
                 apply etherPop_greater. eassumption.
                 by constructor.
               }
               destruct H4 as [D [l'' H4]].
               destruct H4 as [H4_1 H4_2].
               do 2 eexists. split.
                2: { eapply n_trans. 2: exact H4_2.
                       assert (ι0
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [VPid ι'] []
      :: fs0, RValSeq [v0], mailboxPush mb v, links, flag) ∥ prs = ι0
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [VPid ι'] []
      :: fs0, RValSeq [v0], mailboxPush mb v, links, flag) ∥ prs0). {
                         apply map_eq. intros.
                         clear -H1.
                         put (lookup i : ProcessPool -> _) on H1 as HH.
                         destruct (decide (i = ι0)).
                         * subst. by setoid_rewrite lookup_insert.
                         * setoid_rewrite lookup_insert_ne; auto.
                           setoid_rewrite lookup_insert_ne in HH; auto.
                       }
                       setoid_rewrite H.
                       eapply n_send. by constructor.
                  }
               destruct H4_1.
               -- destruct_hyps. left. eexists; split; eassumption.
               -- destruct_hyps. right. do 2 eexists; eassumption.
            (* link send *)
            ** eapply IH in H4. 2: slia. 3-4: by destruct_foralls.
               2: {
                 constructor.
                 apply etherPop_greater. eassumption.
                 by constructor.
               }
               destruct H4 as [D [l'' H4]].
               destruct H4 as [H4_1 H4_2].
               do 2 eexists. split.
                2: { eapply n_trans. 2: exact H4_2.
                       assert (ι0
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] [] :: fs0,
      RValSeq [VPid ι'], mailboxPush mb v, links, flag) ∥ prs = ι0
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] [] :: fs0,
      RValSeq [VPid ι'], mailboxPush mb v, links, flag) ∥ prs0). {
                         apply map_eq. intros.
                         clear -H1.
                         put (lookup i : ProcessPool -> _) on H1 as HH.
                         destruct (decide (i = ι0)).
                         * subst. by setoid_rewrite lookup_insert.
                         * setoid_rewrite lookup_insert_ne; auto.
                           setoid_rewrite lookup_insert_ne in HH; auto.
                       }
                       setoid_rewrite H.
                       eapply n_send. by constructor.
                  }
               destruct H4_1.
               -- destruct_hyps. left. eexists; split; eassumption.
               -- destruct_hyps. right. do 2 eexists; eassumption.
            (* unlink send *)
            **  eapply IH in H4. 2: slia. 3-4: by destruct_foralls.
               2: {
                 constructor.
                 apply etherPop_greater. eassumption.
                 by constructor.
               }
               destruct H4 as [D [l'' H4]].
               destruct H4 as [H4_1 H4_2].
               do 2 eexists. split.
                2: { eapply n_trans. 2: exact H4_2.
                       assert (ι0
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "unlink"%string)) [] [] :: fs0,
      RValSeq [VPid ι'], mailboxPush mb v, links, flag) ∥ prs = ι0
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "unlink"%string)) [] [] :: fs0,
      RValSeq [VPid ι'], mailboxPush mb v, links, flag) ∥ prs0). {
                         apply map_eq. intros.
                         clear -H1.
                         put (lookup i : ProcessPool -> _) on H1 as HH.
                         destruct (decide (i = ι0)).
                         * subst. by setoid_rewrite lookup_insert.
                         * setoid_rewrite lookup_insert_ne; auto.
                           setoid_rewrite lookup_insert_ne in HH; auto.
                       }
                       setoid_rewrite H.
                       eapply n_send. by constructor.
                  }
               destruct H4_1.
               -- destruct_hyps. left. eexists; split; eassumption.
               -- destruct_hyps. right. do 2 eexists; eassumption.
          (* arrive *)
          + inv Harrives. destruct H5.
          (* local *)
          + put (lookup ι0 : ProcessPool -> option _) on H0 as P.
            setoid_rewrite lookup_insert in P. inv P.
            inv Hcompat. inv Harrives.
            (* case separation is needed at this point, because
               exists can't be instantiated first, also ε actions
               could terminate a process -> no chaining

              TODO: this cases a lot of boiler plate
             *)
            destruct_or! H9; subst; inv H1.
            (* silent steps *)
            ** eapply IH in H4. 2: slia. 3-4: eassumption.
               2: {
                 constructor; auto.
                 exact H7.
                 apply p_arrive.
               }
               destruct H4 as [D [l'' H4]].
               destruct H4 as [H4_1 H4_2].
               do 2 eexists. split.
               2: {
                  eapply n_trans. 2: exact H4_2.
                  assert (ι0 ↦ inl (fs, e, mailboxPush mb v, links, flag) ∥ prs = ι0 ↦ inl (fs, e, mailboxPush mb v, links, flag) ∥ Π). {
                    apply map_eq. intros.
                    clear -H0.
                     put (lookup i : ProcessPool -> _) on H0 as HH.
                    destruct (decide (i = ι0)).
                    * subst. by setoid_rewrite lookup_insert.
                    * setoid_rewrite lookup_insert_ne; auto.
                      setoid_rewrite lookup_insert_ne in HH; auto.
                  }
                 rewrite H.
                 eapply n_other. by apply p_local.
                 by left.
               }
               destruct H4_1.
               -- destruct_hyps. left. eexists; split; eassumption.
               -- destruct_hyps. right. do 2 eexists; eassumption.
            (* recv_wait_timeout *)
            ** eapply IH in H4. 2: slia. 3-4: eassumption.
               2: {
                 constructor; auto.
                 exact H7.
                 apply p_arrive.
               }
               destruct H4 as [D [l'' H4]].
               destruct H4 as [H4_1 H4_2].
               do 2 eexists. split.
               2: {
                  eapply n_trans. 2: exact H4_2.
                  assert (ι0
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      VLit 0%Z], mailboxPush mb v, links, flag) ∥ prs = ι0
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      VLit 0%Z], mailboxPush mb v, links, flag) ∥ Π). {
                    apply map_eq. intros.
                    clear -H0.
                     put (lookup i : ProcessPool -> _) on H0 as HH.
                    destruct (decide (i = ι0)).
                    * subst. by setoid_rewrite lookup_insert.
                    * setoid_rewrite lookup_insert_ne; auto.
                      setoid_rewrite lookup_insert_ne in HH; auto.
                  }
                 setoid_rewrite H.
                 eapply n_other. apply p_recv_wait_timeout_0.
                 by left.
               }
               destruct H4_1.
               -- destruct_hyps. left. eexists; split; eassumption.
               -- destruct_hyps. right. do 2 eexists; eassumption.
            (* recv_wait_timeout invalid *)
            ** eapply IH in H4. 2: slia. 3-4: eassumption.
               2: {
                 constructor; auto.
                 exact H7.
                 apply p_arrive.
               }
               destruct H4 as [D [l'' H4]].
               destruct H4 as [H4_1 H4_2].
               do 2 eexists. split.
               2: {
                  eapply n_trans. 2: exact H4_2.
                  assert (ι0
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      v0], mailboxPush mb v, links, flag) ∥ prs = ι0
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      v0], mailboxPush mb v, links, flag) ∥ Π). {
                    apply map_eq. intros.
                    clear -H0.
                     put (lookup i : ProcessPool -> _) on H0 as HH.
                    destruct (decide (i = ι0)).
                    * subst. by setoid_rewrite lookup_insert.
                    * setoid_rewrite lookup_insert_ne; auto.
                      setoid_rewrite lookup_insert_ne in HH; auto.
                  }
                 setoid_rewrite H.
                 eapply n_other. apply p_recv_wait_timeout_invalid.
                 1-2: assumption.
                 by left.
               }
               destruct H4_1.
               -- destruct_hyps. left. eexists; split; eassumption.
               -- destruct_hyps. right. do 2 eexists; eassumption.
            (* self *)
            ** eapply IH in H4. 2: slia. 3-4: eassumption.
               2: {
                 constructor; auto.
                 exact H7.
                 apply p_arrive.
               }
               destruct H4 as [D [l'' H4]].
               destruct H4 as [H4_1 H4_2].
               do 2 eexists. split.
               2: {
                  eapply n_trans. 2: exact H4_2.
                  assert (ι0
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "self"%string)) [] [] :: fs0,
      RBox, mailboxPush mb v, links, flag) ∥ prs = ι0
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "self"%string)) [] [] :: fs0,
      RBox, mailboxPush mb v, links, flag) ∥ Π). {
                    apply map_eq. intros.
                    clear -H0.
                     put (lookup i : ProcessPool -> _) on H0 as HH.
                    destruct (decide (i = ι0)).
                    * subst. by setoid_rewrite lookup_insert.
                    * setoid_rewrite lookup_insert_ne; auto.
                      setoid_rewrite lookup_insert_ne in HH; auto.
                  }
                 setoid_rewrite H.
                 eapply n_other. apply p_self.
                 by right; left.
               }
               destruct H4_1.
               -- destruct_hyps. left. eexists; split; eassumption.
               -- destruct_hyps. right. do 2 eexists; eassumption.
            (* peek_message *)
            ** eapply IH in H4. 2: slia. 3-4: eassumption.
               2: {
                 constructor; auto.
                 exact H7.
                 apply p_arrive.
               }
               destruct H4 as [D [l'' H4]].
               destruct H4 as [H4_1 H4_2].
               do 2 eexists. split.
               2: {
                  eapply n_trans. 2: exact H4_2.
                  assert (ι0
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox,
      mailboxPush mb v, links, flag) ∥ prs = ι0
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox,
      mailboxPush mb v, links, flag) ∥ Π). {
                    apply map_eq. intros.
                    clear -H0.
                     put (lookup i : ProcessPool -> _) on H0 as HH.
                    destruct (decide (i = ι0)).
                    * subst. by setoid_rewrite lookup_insert.
                    * setoid_rewrite lookup_insert_ne; auto.
                      setoid_rewrite lookup_insert_ne in HH; auto.
                  }
                 setoid_rewrite H.
                 eapply n_other. apply p_recv_peek_message_ok.
                 destruct mb; simpl in *. destruct l1; inv H14.
                 by simpl.
                 by intuition.
               }
               destruct H4_1.
               -- destruct_hyps. left. eexists; split; eassumption.
               -- destruct_hyps. right. do 2 eexists; eassumption.
            (* peek_message_fail *)
            ** eapply IH in H4. 2: slia. 3-4: eassumption.
               2: {
                 constructor; auto.
                 exact H7.
                 apply p_arrive.
               }
               destruct H4 as [D [l'' H4]].
               destruct H4 as [H4_1 H4_2].
               do 2 eexists. split.
               2: {
                  eapply n_trans. 2: exact H4_2.
                  assert (ι0
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox,
      mailboxPush mb v, links, flag) ∥ prs = ι0
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox,
      mailboxPush mb v, links, flag) ∥ Π). {
                    apply map_eq. intros.
                    clear -H0.
                     put (lookup i : ProcessPool -> _) on H0 as HH.
                    destruct (decide (i = ι0)).
                    * subst. by setoid_rewrite lookup_insert.
                    * setoid_rewrite lookup_insert_ne; auto.
                      setoid_rewrite lookup_insert_ne in HH; auto.
                  }
                 setoid_rewrite H.
                 eapply n_other. apply p_recv_peek_message_no_message.
                 destruct mb; simpl in *. destruct l1; inv H14.
                 by simpl.
                 by intuition.
               }
               destruct H4_1.
               -- destruct_hyps. left. eexists; split; eassumption.
               -- destruct_hyps. right. do 2 eexists; eassumption.
            **
            **
            **
            **
            **
            **
          (* spawn *)
          + put (lookup ι0 : ProcessPool -> option _) on H0 as P.
            setoid_rewrite lookup_insert in P. inv P. admit.
        (* exit drop *)
        - exfalso. inv Harrives.
          specialize (H1 _ _ _ eq_refl) as [? ?]. congruence.
        (* exit terminates *)
        - exfalso. inv Harrives.
          specialize (H1 _ _ _ eq_refl) as [? ?]. congruence.
        (* exit converted *)
        - exfalso. inv Harrives.
          specialize (H1 _ _ _ eq_refl) as [? ?]. congruence.
        (* link *)
        - exfalso. inv Harrives.
          specialize (H1 _ _ _ eq_refl) as [? ?]. congruence.
        (* unlink *)
        - exfalso. inv Harrives.
          specialize (H1 _ _ _ eq_refl) as [? ?]. congruence.
    }
    {
      (* pose proof (compatiblePIDOf_options_alt a a0) as [Ha | Ha ]. *)
      (* pose proof (compatiblePIDOf_options a a0) as [Ha | Ha ].
      { *)
      inv Hcompat. simpl in H1.
      pose proof (confluence _ _ _ _ _ HD2 _ _ _ H1 H2 n).
      destruct_hyps.
      eapply IH in H4. 3: exact H0. 2: slia. 2: eassumption.
      destruct H4 as [D [l'' H4]].
      destruct H4 as [H4_1 H4_2]. destruct H4_1.
      * destruct_hyps. exists D, ((a0, ι0)::l''). split.
        - left. exists x0. split; assumption.
        - econstructor; eassumption.
      * exists D, ((a0, ι0)::l''). split.
        - right. destruct_hyps. do 2 eexists. eassumption.
        - econstructor; eassumption.
Qed.

Theorem action_chainable_old :
  (* NOTE: only l (and n n') can be constrained for the proof of normalisation!
     NOTE: don't forget that 
           we would like to prove equivalences like map ≈ paralell map *)
  forall l O A C, A -[l]ₙ->* C with O ->
    forall B a ι, A -[a | ι]ₙ-> B with O ->
      (* Forall (compatiblePIDOf a ∘ fst) l -> (* If some PID is not compatible, 
                                               we rename l *) *)
      (* (a, ι) ∈ l \/ *)
      (exists D l'', ((exists l', C -[l']ₙ->* D with O /\ length l' ≤ 1)
       \/ (exists from fresh, D = prod_map (renamePIDEther from fresh) (renamePIDPool from fresh) C))
       /\ B -[l'']ₙ->* D with O)
      (* (exists n''', n'' -[a | ι]ₙ-> n''' with O) \/ (* normal arrivals, sends, other processes can take the step at the end *)
      (True) (* if some processes die due to l *) *).
Proof.
  induction l using list_length_ind. rename H into IH.
  destruct l; intros ? ? ? HD1 ? ? ? HD2.
  {
    inv HD1. exists B, []. split. left. exists [(a, ι)]. split_and!; simpl.
    * econstructor. eassumption. constructor.
    * lia.
    * constructor.
  }
  {
    inv HD1.
    destruct (decide (ι = ι0)).
    {
      subst.
      epose proof (action_options _ _ _ _ _ _ _ _ H2 HD2 eq_refl).
      intuition; destruct_hyps.
      * subst. eapply concurrent_determinism in HD2. 2: exact H2.
        subst. exists C, l. split. left. exists []. split.
        - constructor.
        - slia.
        - assumption.
      * subst.
        assert (exists to, to ∉ flat_union (usedPIDsAct ∘ fst) l /\ ¬appearsEther to B.1 /\ ¬appearsEther to n'.1 /\ ¬isUsedPool to B.2 /\ ¬isUsedPool to n'.2 /\ to ∉ O). {
          admit. (* freshness *)
        }
        destruct (decide (x1 = x2)). { (* same spawn - the inequality in needed later *)
          subst. eapply concurrent_determinism in HD2. 2: exact H2.
          subst. exists C, l. split. left. exists []. split.
          - constructor.
          - slia.
          - assumption.
        }
        destruct H as [to [I1 [I2 [I3 [I4 [I5 I6]]]]]].
        exists (prod_map (renamePIDEther x1 to) (renamePIDPool x1 to) C), (map (prod_map (renamePIDAct x1 to) (renamePIDPID_sym x1 to)) l).
        split. right.
        - do 2 eexists. reflexivity.
        - replace B with (prod_map (renamePIDEther x1 to) (renamePIDPool x1 to) n').
          2: {
            inv HD2. 1: destruct_or!; congruence.
            inv H2. 1: destruct_or!; congruence.
            put (lookup ι0 : ProcessPool -> option Process) on H0 as P.
            setoid_rewrite lookup_insert in P. inv P.
            simpl. rewrite does_not_appear_renamePID_ether; auto.
            unfold renamePIDPool. clear IH.
            do 2 setoid_rewrite fmap_insert.
            do 2 (setoid_rewrite kmap_insert; auto).
            simpl.
            setoid_rewrite isNotUsed_renamePID_pool; auto.
            all: admit. (* TODO: technical, x1 is not used anywhere except the new PID *)
          }
          apply renamePID_is_preserved_node_semantics_steps; auto.
          by rewrite <- surjective_pairing, <- surjective_pairing.
      * subst.
        (* every combination of arrives should be checked *)
        admit.
      * admit.
    }
    {
      (* pose proof (compatiblePIDOf_options_alt a a0) as [Ha | Ha ]. *)
      pose proof (compatiblePIDOf_options a a0) as [Ha | Ha ].
      {
        pose proof (confluence _ _ _ _ _ HD2 _ _ _ Ha H2 n).
        destruct_hyps.
        eapply IH in H4. 3: exact H0. 2: slia. destruct H4 as [D [l'' H4]].
        destruct H4 as [H4_1 H4_2]. destruct H4_1.
        * destruct_hyps. exists D, ((a0, ι0)::l''). split.
          - left. exists x0. split; assumption.
          - econstructor; eassumption.
        * exists D, ((a0, ι0)::l''). split.
          - right. destruct_hyps. do 2 eexists. eassumption.
          - econstructor; eassumption.
      }
      {
        (* assert (exists to, to ∉ flat_union (usedPIDsAct ∘ fst) l /\ ¬appearsEther to A.1 /\ ¬appearsEther to n'.1 /\ ¬isUsedPool to A.2 /\ ¬isUsedPool to n'.2 /\ to ∉ O /\
        to ∉ usedPIDsAct a /\ to ∉ usedPIDsAct a0). {
          admit. (* freshness *)
        }
        destruct H as [to ?]. destruct_hyps.
        specialize (Ha to H7 H8) as [Ha | Ha].
        { (* a0 needs to be renamed *)
          destruct A as [Aeth AΠ].
          destruct B as [Beth BΠ].
          destruct Ha as [from [Ha1 Ha2]].
          eapply renamePID_is_preserved_node_semantics in HD2 as HD2'.
          2-5: eassumption.
          Unshelve. 2: exact from.
          assert (¬ appearsEther from Aeth /\ ¬isUsedPool from AΠ /\ from <> ι0) as [Hfrom1 [Hfrom2 Hfrom3]]. {
            destruct a; inv Ha1. inv HD2. destruct_or!; congruence.
            split_and!; try assumption.
            intro. subst. apply H19.
            left. inv H2; by setoid_rewrite lookup_insert.
          }
          rewrite does_not_appear_renamePID_ether in HD2'; auto.
          rewrite isNotUsed_renamePID_pool in HD2'; auto.
          assert (renamePIDPID_sym from to ι ≠ ι0) as X. {
            renamePIDPID_sym_case_match.
            intro. subst. apply H3. left. inv H2; by setoid_rewrite lookup_insert.
          }
          pose proof (confluence _ _ _ _ _ HD2' _ _ _ Ha2 H2 X).
          destruct_hyps.
          destruct n' as [n'eth n'Π].
          destruct C as [Ceth CΠ].
          apply renamePID_is_preserved_node_semantics_steps with (from := from) (to := to) in H4; auto.
          
          eapply IH in H4. 2: rewrite map_length; simpl; clear.
          2: { (* NOTE For some reason, lia does not work here *)
            apply NPeano.Nat.lt_succ_diag_r.
          }
          2: {
            rewrite does_not_appear_renamePID_ether; auto.
            rewrite isNotUsed_renamePID_pool; auto.
            exact H10.
            eapply not_isUsedPool_step; try eassumption.
          }
          destruct H4 as [D [l'' H4]].
          destruct H4 as [H4_1 H4_2]. destruct H4_1.
          * destruct_hyps. exists D, ((a1, ι0)::l''). split.
            - left. exists x0. split; assumption.
            - econstructor; eassumption.
          * exists D, ((a1, ι0)::l''). split.
            - right. destruct_hyps. do 2 eexists. eassumption.
            - econstructor; eassumption.
        }
        { (* a1 needs to be renamed *)
        
        } *)
        
        
        
        
        destruct Ha as [from Ha].
        assert (exists to1, to1 ∉ flat_union (usedPIDsAct ∘ fst) l /\ ¬appearsEther to1 A.1 /\ ¬appearsEther to1 n'.1 /\ ¬isUsedPool to1 A.2 /\ ¬isUsedPool to1 n'.2 /\ to1 ∉ O /\
        to1 ∉ usedPIDsAct a /\ to1 ∉ usedPIDsAct a0). {
          admit. (* freshness *)
        }
        destruct H as [to1 ?]. destruct_hyps.
        assert (exists to2, to2 ∉ flat_union (usedPIDsAct ∘ fst) l /\ ¬appearsEther to2 A.1 /\ ¬appearsEther to2 n'.1 /\ ¬isUsedPool to2 A.2 /\ ¬isUsedPool to2 n'.2 /\ to2 ∉ O /\
        to2 ∉ usedPIDsAct a /\ to2 ∉ usedPIDsAct a0 /\ to1 ≠ to2). {
          admit. (* freshness *)
        }
        destruct H11 as [to2 ?]. destruct_hyps.
        (* it matters which one of the actions is going to be renamed (which is the spawn) *)
        (* destruct H9.
        {
          specialize (H10 to H7 H8).
          destruct A as [Aeth AΠ]. destruct B as [Beth BΠ].
          destruct n' as [n'eth n'Π].
          eapply renamePID_is_preserved_node_semantics in H2.
          5: eassumption. 2-4: try assumption.
        }
        {
        
        } *)
        
        
        assert (¬ isUsedPool from A.2 /\ ¬appearsEther from A.1 /\ from <> ι /\ from <> ι0) as [HF1 [HF2 [HF3 HF4]]]. {
          destruct H9.
          * destruct a; inv H9. inv HD2. destruct_or!; congruence.
            repeat split; auto.
            all: intro; subst.
            apply H24. left. by setoid_rewrite lookup_insert.
            apply H24. inv H2; left; by setoid_rewrite lookup_insert.
          * destruct a0; inv H9. inv H2. destruct_or!; congruence.
            repeat split; auto.
            all: intro; subst.
            apply H24. inv HD2; left; by setoid_rewrite lookup_insert.
            apply H24. left. by setoid_rewrite lookup_insert.
        }
        specialize (H10 to1 to2 H19 H7 H8 H17 H18).
        destruct A as [Aeth AΠ]. destruct B as [Beth BΠ].
        destruct n' as [n'eth n'Π]. destruct C as [Ceth CΠ].
        simpl in *.
        apply renamePID_is_preserved_node_semantics with (from := from) (to := to2) in H2 as H2D.
        5: eassumption. 2-4: try assumption.
        apply renamePID_is_preserved_node_semantics with (from := from) (to := to1) in HD2 as HD2D.
        5: eassumption. 2-4: try assumption.
        simpl in *.
        rewrite does_not_appear_renamePID_ether in H2D, HD2D; auto.
        rewrite isNotUsed_renamePID_pool in H2D, HD2D; auto.
        replace (renamePIDPID_sym from to1 ι0) with ι0 in H2D.
        replace (renamePIDPID_sym from to2 ι) with ι in HD2D.
        2: {
          renamePIDPID_sym_case_match.
          admit. (* TODO technical from H7 + H8 and H9 *)
        }
        2: {
          renamePIDPID_sym_case_match.
          admit. (* TODO technical from H7 + H8 and H9 *)
        }
        epose proof (confluence _ _ _ _ _ HD2D _ _ _ H10 H2D _). Unshelve.
        2: {
          renamePIDPID_sym_case_match.
          admit. (* TODO technical from H7 + H8 and H9 *)
        }
        destruct_hyps.
        apply renamePID_is_preserved_node_semantics_steps with (from := from) (to := to1) in H4 as H4D.
        5: eassumption. 2-4: try assumption.
        
        
        
        eapply IH in H4D as H4DD. 2: admit. 2: exact H21. destruct H4DD as [D [l'' H4']].
        destruct H4' as [H4_1 H4_2]. destruct H4_1.
        * destruct_hyps.
          eapply n_trans in H4_2. 2: exact H20.
         exists D, ((a1, ι0)::l''). split.
          - left. exists x0. split; assumption.
          - econstructor; eassumption.
        * exists D, ((a1, ι0)::l''). split.
          - right. destruct_hyps. do 2 eexists. eassumption.
          - econstructor; eassumption.
      }
    }
Abort.

Theorem arrive_chain :
  forall O A B C a ι s ιs,
    A -[a|ι]ₙ-> B with O ->
    A -[AArrive ιs ι s|ι]ₙ-> C with O ->
    (a = AArrive ιs ι s) \/
    (exists D, B -[AArrive ιs ι s| ι]ₙ-> D with O) \/
    (B = (A.1, C.2)) (* One of the actions can't happen due to termination *).
Proof.
  intros. inv H; inv H0; subst.
  * 
  *
  *
  *
  *
  *
  *
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
    - left. apply elem_of_app. now left.
    - rename n'0 into A. rename n' into B.
      destruct_hyps. inv D2. inv H9. *)
Abort.

