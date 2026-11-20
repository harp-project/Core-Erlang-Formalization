(**
  This file shows that renaming the PIDs of a node with a list of PID
  renamings is a bisimulation (`rename_bisim`), if the targets of the
  renamings are fresh and no observed PID is renamed (`PIDsRespectNode`).

  The proof does not use `cofix`: it shows that the relation of nodes and
  their renamed versions is a bisimulation (`rename_bisim_alt`). Steps of the
  renamed node are handled by renaming it back with the reversed list of
  inverse renamings (`cancel_renamePIDs_ether`, `cancel_renamePIDs_pool`).
*)

From CoreErlang.Concurrent Require Export BarbedBisim.

Import ListNotations.

(** The PIDs sent to during a reduction sequence are not necessarily
    targeted in the ether or used in the pool of the initial node. This
    statement does not hold, e.g., a newly spawned process can send a message
    to itself, while its PID was unused initially. *)
Lemma impossible_send :
  forall O n n' l, n -[l]ₙ->* n' with O ->
    forall ι, ι ∈ (PIDsOf sendPIDOf l) ->
      (isTargetedEther ι n.1 \/ isUsedPool ι n.2).
Proof.
Abort.

(** * PID renaming lists *)

(** A list of PID renamings `(from, to)`, applied from left to right. *)
Definition PIDRenamingList := list (PID * PID).

(** `renamePIDs f l x` renames `x` with the elements of `l` (from left to
    right), using the PID renaming function `f`. *)
Definition renamePIDs {A} (f : PID -> PID -> A -> A) (l : PIDRenamingList) (x : A) : A :=
  fold_left (fun acc '(from, to) => f from to acc) l x.

(** `collapse_list P f o l`: `P` holds for the first element of `l` and `o`,
    then for the second element of `l` and `f (l !! 0) o`, and so on. *)
Fixpoint collapse_list {A B : Type} (P : A -> B -> Prop) (f : A -> B -> B) (o : B) (l : list A) : Prop :=
match l with
| [] => True
| x::xs => P x o /\ collapse_list P f (f x o) xs
end.

(** A PID renaming list respects a node, if every renaming `(from, to)` of it
    renames an unobserved PID to an unobserved PID, which is neither used in
    the pool nor appears in the ether of the node renamed with the previous
    elements of the list. Thus, a PID can only be renamed to a fresh one. *)
Definition PIDsRespectNode (O : gset PID) (n : Node) : list (PID * PID) -> Prop :=
  collapse_list (fun '(from, to) n =>
                   (from ∉ O) /\ (to ∉ O) /\ ¬isUsedPool to n.2 /\ ¬appearsEther to n.1)
                (fun '(from, to) => prod_map (renamePIDEther from to) (renamePIDPool from to)) n.

(** A PID renaming list respects an action, if the target of every renaming
    of it does not appear in the action renamed with the previous elements of
    the list. *)
Definition PIDsRespectAction (a : Action) : list (PID * PID) -> Prop :=
  collapse_list (fun '(from, to) a => to ∉ usedPIDsAct a) (fun '(from, to) => renamePIDAct from to) a.

(** Steps are preserved by renaming with a PID renaming list that respects
    both the node and the action of the step. *)
Theorem renamePIDs_is_preserved :
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

(** PID renaming lists respecting a node and the action of a step from the
    node also respect the result of the step. *)
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

(** `does_not_respect l a` collects the targets of the PID renaming list `l`
    which appear in the action `a` (renamed with the previous elements of
    `l`), i.e., which violate `PIDsRespectAction a l`. *)
Fixpoint does_not_respect (l : list (PID * PID)) (a : Action) : gset PID :=
match l with
| [] => ∅
| (from, to)::xs =>
  if decide (to ∈ usedPIDsAct a)
  then {[to]} ∪ does_not_respect xs (renamePIDAct from to a)
  else does_not_respect xs (renamePIDAct from to a)
end.

(** If no target of the PID renaming list violates `PIDsRespectAction`, the
    list respects the action. *)
Lemma does_not_respect_PIDsRespectAction :
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

(** If a step does not spawn a process, every PID renaming list respecting
    the node respects the action too (no target of the list violates
    `PIDsRespectAction`). *)
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
        ** apply H4. left. subst. setoid_rewrite lookup_insert. by destruct_decide_eq.
        ** apply H4. right.
           exists ι, p1. split. by setoid_rewrite lookup_insert; destruct_decide_eq.
           clear -e n H11. inv H11; simpl in *. 1-4: set_solver.
           apply elem_of_union_list. simpl in *.
           exists ({[ι']} ∪ usedPIDsVal reason). split. 2: set_solver.
           apply elem_of_elements, elem_of_map_to_set. exists ι', reason. by split.
      + destruct (decide (p0 = ι)).
        ** apply H4. left. subst. setoid_rewrite lookup_insert. by destruct_decide_eq.
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
           subst. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
        ** clear-e. set_solver.
    - eapply IHl. 2: exact H3.
      simpl. apply renamePID_is_preserved. exact H.
      all: try assumption.
      + clear -H1. destruct a0; auto. simpl in H1. congruence.
Qed.

(** If a step spawns a process with the PID `p`, a PID renaming list
    respecting the node can be extended with the renaming of `p` to a fresh
    PID `new` (which is also outside of a given set `K`), so that the
    extended list respects both the node and the action of the step. Since
    `p` has to be fresh in the node for spawning, the renaming of `p` does
    not modify the node. *)
Lemma step_spawn_respects_avoid :
  forall (K : gset PID) l a eth Π eth' Π' O ι,
  (eth, Π) -[ a | ι ]ₙ-> (eth', Π') with O ->
  PIDsRespectNode O (eth, Π) l ->
  forall p, spawnPIDOf a = Some p ->
    exists new, (new ∉ K) /\ (new ∉ map fst l) /\
    (new ∉ usedPIDsAct a) /\ (new ∉ O) /\ ¬isUsedPool new Π /\ ¬appearsEther new eth /\ (new ∉ map snd l) /\
    PIDsRespectNode O (eth, Π) ((p, new)::l) /\
    PIDsRespectAction a ((p, new) :: l).
Proof.
  intros.
  assert (exists new, (new ∉ K) /\ (new ∉ usedPIDsAct a) /\ (new ∉ O) /\ ¬isUsedPool new Π /\ ¬appearsEther new eth /\ (new ∉ map snd l) /\ (new ∉ map fst l)). {
    (* freshness *)
    pose proof (infinite_is_fresh (elements K ++ elements (usedPIDsAct a) ++ elements O ++ elements (allPIDsPool Π) ++ elements (allPIDsEther eth) ++ map snd l ++ map fst l)).
    remember (fresh _) as y in H2. clear-H2. exists y.
    repeat apply not_elem_of_app in H2 as [? H2].
    split_and!; try assumption.
    1-3: set_solver.
    * apply allPIDsPool_isNotUsed_1. set_solver.
    * apply allPIDsEther_does_not_appear_1. set_solver.
  }
  destruct H2 as [new [HK H2]].
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
    1-2: intro; apply H18; right; exists ι, p0; setoid_rewrite lookup_insert; destruct_decide_eq; split; [reflexivity|].
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
        setoid_rewrite lookup_insert. destruct_decide_eq. split. reflexivity.
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
               by setoid_rewrite lookup_insert; destruct_decide_eq. assumption.
        + unfold PIDsRespectNode. cbn in H2.
          setoid_rewrite <- kmap_insert; auto.
          setoid_rewrite <- fmap_insert. exact H2.
        + set_solver.
        + set_solver.
    }
Qed.

(** `step_spawn_respects_avoid` without the additional set to avoid. *)
Corollary step_spawn_respects :
  forall l a eth Π eth' Π' O ι,
  (eth, Π) -[ a | ι ]ₙ-> (eth', Π') with O ->
  PIDsRespectNode O (eth, Π) l ->
  forall p, spawnPIDOf a = Some p ->
    exists new, (new ∉ usedPIDsAct a) /\ (new ∉ O) /\ ¬isUsedPool new Π /\ ¬appearsEther new eth /\ (new ∉ map snd l) /\
    PIDsRespectNode O (eth, Π) ((p, new)::l) /\
    PIDsRespectAction a ((p, new) :: l).
Proof.
  intros.
  destruct (step_spawn_respects_avoid ∅ l a eth Π eth' Π' O ι H H0 p H1)
    as [new [_ [_ Hnew]]].
  by exists new.
Qed.

(** * Cancelling PID renaming lists *)

(** Renaming a pool with a respecting PID renaming list `l` is cancelled by
    renaming with the reversed list of inverse renamings. *)
Theorem cancel_renamePIDs_pool :
  forall l O eth Π,
  PIDsRespectNode O (eth, Π) l ->
  renamePIDs renamePIDPool (map prod_swap (reverse l)) (renamePIDs renamePIDPool l Π) = Π.
Proof.
  induction l; intros; simpl. reflexivity.
  inv H. destruct a as [from to]. destruct_hyps. apply IHl in H1.
  simpl in *.
  rewrite reverse_cons, map_app. simpl.
  unfold renamePIDs in *. rewrite fold_left_app. simpl.
  rewrite H1.
  by rewrite double_renamePID_pool.
Qed.

(** Renaming an ether with a respecting PID renaming list `l` is cancelled
    by renaming with the reversed list of inverse renamings. *)
Theorem cancel_renamePIDs_ether :
  forall l O eth Π,
  PIDsRespectNode O (eth, Π) l ->
  renamePIDs renamePIDEther (map prod_swap (reverse l)) (renamePIDs renamePIDEther l eth) = eth.
Proof.
  induction l; intros; simpl. reflexivity.
  inv H. destruct a as [from to]. destruct_hyps. apply IHl in H1.
  simpl in *.
  rewrite reverse_cons, map_app. simpl.
  unfold renamePIDs in *. rewrite fold_left_app. simpl.
  rewrite H1.
  by rewrite double_renamePID_ether.
Qed.

(** A concatenation of PID renaming lists respects a node, if the first list
    respects the node, and the second list respects the node renamed with
    the first list. *)
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

(** The reversed list of inverse renamings of a PID renaming list respecting
    a node respects the renamed node. *)
Lemma cancel_PIDsRespectNode :
  forall l O eth Π,
  PIDsRespectNode O (eth, Π) l ->
  PIDsRespectNode O (renamePIDs renamePIDEther l eth, renamePIDs renamePIDPool l Π)
                      (map prod_swap (reverse l)).
Proof.
  induction l; intros; simpl. constructor.
  inv H. destruct a. simpl in *. apply IHl in H1 as H'. destruct_hyps.
  rewrite reverse_cons, map_app. unfold prod_swap at 2. cbn.
  apply PIDsRespectNode_app. split. assumption.
  cbn. split_and!; try assumption. 3: trivial.
  * erewrite cancel_renamePIDs_pool. 2: exact H1.
    intro. by apply isUsedPool_rename_old in H4.
  * erewrite cancel_renamePIDs_ether. 2: exact H1.
    intro. by apply appearsEther_rename_old in H4.
Qed.

(** Renaming a node with a respecting list of PID renamings preserves the
    signals in transit to the observed PIDs, where the source of the signals
    is renamed too. *)
Lemma renamePIDs_barbs :
  forall l O eth Π, PIDsRespectNode O (eth, Π) l ->
    forall source dest, dest ∈ O ->
      option_list_biforall Signal_eq (eth !! (source, dest))
        (renamePIDs renamePIDEther l eth !! (renamePIDs renamePIDPID_sym l source, dest)).
Proof.
  intros l O eth Π Hresp source dest H.
  assert ((renamePIDs renamePIDPID_sym l source, dest) =
       ((prod_map (renamePIDs renamePIDPID_sym l) (renamePIDs renamePIDPID_sym l)) (source, dest))) as HX. {
    cbn. f_equal. clear -H Hresp.
    generalize dependent dest. revert eth Π Hresp.
    induction l; intros. reflexivity.
    inv H. destruct a. simpl. destruct Hresp as [Hresp1 Hresp].
    intros. erewrite <- IHl; auto.
    * unfold renamePIDPID_sym. cbn in Hresp.
      destruct_hyps. repeat case_match;eqb_to_eq; subst; try congruence.
    * exact Hresp.
    * unfold renamePIDPID_sym.
      destruct_hyps. repeat case_match;eqb_to_eq; subst; try congruence.
  }
  setoid_rewrite HX.
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
        1: by rewrite length_map.
        intros. rewrite map_nth with (d:= SUnlink).
        by apply Signal_eq_renamePID.
      }
      {
        setoid_rewrite P. simpl. trivial.
      }
Qed.

(** * PID renaming is a bisimulation *)

(** The relation of nodes and their versions renamed with a respecting PID
    renaming list is a bisimulation. A step of the renamed node is matched
    by renaming it back with the reversed list of inverse renamings, and the
    resulting nodes are related by the reversed list of inverse renamings of
    the list used for the step. *)
Theorem rename_bisim_alt :
  forall O,
    is_barbed_bisim_alt (
      fun '(eth, Π) '(eth', Π') =>
        exists l,
          PIDsRespectNode O (eth, Π) l /\
          renamePIDs renamePIDEther l eth = eth' /\
          renamePIDs renamePIDPool l Π = Π'
    ) O.
Proof.
  intros. repeat split; destruct A as [ethA ΠA], B as [ethB ΠB];
  destruct H as [l [Hresp [Heq1 Heq2]]]; subst.
  * intros [ethA' ΠA'] a ι D.
    destruct (spawnPIDOf a) eqn:P.
    { (* renaming needed *)
      epose proof step_spawn_respects l a _ _ _ _ _ _ D Hresp _ P as Hspawn.
      destruct Hspawn as [new H1]. destruct_hyps.
      apply renamePIDs_is_preserved with (l := (p, new)::l) in D as D'.
      2-3: assumption.

      replace (renamePIDs renamePIDEther l ethA) with
         (renamePIDs renamePIDEther ((p, new) :: l) ethA). 2: {
         simpl.
         rewrite does_not_appear_renamePID_ether; auto.
         destruct a; inv P. inv D. 1: destruct_or!; congruence.
         by simpl.
      }
      replace (renamePIDs renamePIDPool l ΠA) with
         (renamePIDs renamePIDPool ((p, new) :: l) ΠA). 2: {
         simpl.
         rewrite isNotUsed_renamePID_pool; auto.
         destruct a; inv P. inv D. 1: destruct_or!; congruence.
         by simpl.
      }
      do 2 eexists. split. eapply n_trans. exact D'. apply n_refl.
      simpl. eexists. split.
      * epose proof PIDsRespectNode_preserved _ _ _ _ _ _ H4 H5 D.
        exact H6.
      * by simpl.
    }
    { (* renaming is not needed *)
      eapply step_not_spawn_respects in D as R. 2: exact Hresp. 2: assumption.
      apply does_not_respect_PIDsRespectAction in R as R'.
      apply renamePIDs_is_preserved with (l := l) in D as D'.
      2-3: assumption.
      do 2 eexists. split. eapply n_trans. exact D'. apply n_refl.
      simpl. eexists. split.
      * epose proof PIDsRespectNode_preserved _ _ _ _ _ _ Hresp R' D.
        exact H.
      * by simpl.
    }
  * intros source dest Hdest.
    exists (renamePIDs renamePIDPID_sym l source), [].
    eexists. split. 1: apply n_refl.
    by eapply renamePIDs_barbs.
  (* The renamed node is the original node renamed back with l', thus the
     previous cases can be repeated with l'. *)
  * intros [ethB ΠB] a ι D.
    rewrite <- (cancel_renamePIDs_pool l O ethA ΠA). 2: assumption.
    rewrite <- (cancel_renamePIDs_ether l O ethA ΠA). 2: assumption.

    remember (map prod_swap (reverse l)) as l'.
    apply cancel_PIDsRespectNode in Hresp as Hcancel.
    rewrite <- Heql' in Hcancel.
    destruct (spawnPIDOf a) eqn:P.
    { (* renaming needed *)
      pose proof step_spawn_respects l' a _ _ _ _ _ _ D Hcancel _ P as X.
      destruct X as [new X]. destruct_hyps.
      apply renamePIDs_is_preserved with (l := (p, new)::l') in D as D'.
      2-3: assumption.

      replace (renamePIDs renamePIDEther l' (renamePIDs renamePIDEther l ethA)) with
         (renamePIDs renamePIDEther ((p, new)::l') (renamePIDs renamePIDEther l ethA)). 2: {
         simpl.
         rewrite does_not_appear_renamePID_ether; auto.
         destruct a; inv P. inv D. 1: destruct_or!; congruence.
         by simpl.
      }
      replace (renamePIDs renamePIDPool l' (renamePIDs renamePIDPool l ΠA)) with
         (renamePIDs renamePIDPool ((p, new) :: l') (renamePIDs renamePIDPool l ΠA)). 2: {
         simpl.
         rewrite isNotUsed_renamePID_pool; auto.
         destruct a; inv P. inv D. 1: destruct_or!; congruence.
         by simpl.
      }
      simpl.
      do 2 eexists. split. eapply n_trans. exact D'. apply n_refl.
      cbv beta iota.
      assert (PIDsRespectNode O (ethB, ΠB) ((p, new) :: l')) as HB.
      { eapply PIDsRespectNode_preserved; eassumption. }
      exists (map prod_swap (reverse ((p, new) :: l'))). split_and!.
      - by apply cancel_PIDsRespectNode.
      - by eapply cancel_renamePIDs_ether.
      - by eapply cancel_renamePIDs_pool.
    }
    { (* renaming is not needed *)
      eapply step_not_spawn_respects in D as R. 3: exact P. 2: exact Hcancel.
      apply does_not_respect_PIDsRespectAction in R as R'.
      apply renamePIDs_is_preserved with (l := l') in D as D'.
      2-3: assumption.
      do 2 eexists. split. eapply n_trans. exact D'. apply n_refl.
      cbv beta iota.
      assert (PIDsRespectNode O (ethB, ΠB) l') as HB.
      { eapply PIDsRespectNode_preserved; eassumption. }
      exists (map prod_swap (reverse l')). split_and!.
      - by apply cancel_PIDsRespectNode.
      - by eapply cancel_renamePIDs_ether.
      - by eapply cancel_renamePIDs_pool.
    }
  * intros source dest Hdest.
    apply cancel_PIDsRespectNode in Hresp as Hcancel.
    pose proof (renamePIDs_barbs _ _ _ _ Hcancel source dest Hdest) as Hb.
    erewrite cancel_renamePIDs_ether in Hb. 2: exact Hresp.
    eexists. exists [], (ethA, ΠA). split. 1: apply n_refl.
    exact Hb.
Qed.

(** Renaming a node with a respecting PID renaming list results in a
    bisimilar node. *)
Corollary rename_bisim :
  forall O eth Π (l : list (PID * PID)),
    PIDsRespectNode O (eth, Π) l ->
    (eth, Π) ~ᵇ (renamePIDs renamePIDEther l eth, renamePIDs renamePIDPool l Π) observing O.
Proof.
  intros.
  eapply barbed_alt_barbed_1. apply rename_bisim_alt.
  simpl. exists l. split. assumption.
  split; reflexivity.
Qed.
