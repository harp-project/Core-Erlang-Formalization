From CoreErlang.Concurrent Require Export NodeSemanticsLemmas.

Definition SIGCLOSED s :=
match s with
 | SMessage e => VALCLOSED e
 | SExit r b => VALCLOSED r
 | SLink => True
 | SUnlink => True
end.

Lemma SIGCLOSED_rename :
  forall s p p', SIGCLOSED s <-> SIGCLOSED (renamePIDSignal p p' s).
Proof.
  intros. destruct s; simpl; auto.
  all: split; intro; try by apply renamePID_preserves_scope.
  1-2: by apply renamePID_implies_scope in H.
Qed.

Definition ACTIONCLOSED (a : Action) :=
  match a with
  | ASend _ _ s => SIGCLOSED s
  | AArrive _ _ s => SIGCLOSED s
  | ASpawn _ vl1 vl2 _ => VALCLOSED vl1 /\ VALCLOSED vl2
  | _ => True
  end.

Definition MBCLOSED (mb : Mailbox) :=
  match mb with
  | (mb1, mb2) => Forall (fun v1 => VALCLOSED v1) mb1 /\ Forall (fun v2 => VALCLOSED v2) mb2
  end.

Definition PROCCLOSED (p : Process) :=
  match p with
  | inl (fs, r, mb, links, flag) => FSCLOSED fs /\ REDCLOSED r /\ MBCLOSED mb
  | inr (links) => Forall (fun '(_, v) => VALCLOSED v) (map_to_list links)
  end.

Definition POOLCLOSED (pp : ProcessPool) :=
  Forall (fun '(_, pr) => PROCCLOSED pr) (map_to_list pp).

Definition ETHERCLOSED (eth : Ether) :=
  Forall (fun '(_, sl) => Forall (fun s => SIGCLOSED s) sl) (map_to_list eth).

Definition NODECLOSED (n : Node) :=
  match n with
  | (eth, pp) => POOLCLOSED pp /\ ETHERCLOSED eth
  end.

Lemma fsclosed_weaken: forall f fs, FSCLOSED (f :: fs) -> FSCLOSED fs.
Proof.
  intros. inv H. inv H3.
  * constructor.
  * constructor; auto.
Qed.

Theorem processLocalStepClosedness: forall p p' a,
  p -⌈ a ⌉-> p' -> PROCCLOSED p -> ACTIONCLOSED a -> PROCCLOSED p'.
Proof.
  intros p p' a IH. induction IH; intros Hcl Hacl.
  all: unfold PROCCLOSED; unfold PROCCLOSED in Hcl;
  try destruct Hcl as [Hcl1 Hcl2]; try destruct Hcl2 as [Hcl2 Hcl3]; 
  try split; try split; auto.
  all: try (apply fsclosed_weaken in Hcl1); auto.
  * destruct (step_closedness fs e fs' e' H Hcl1 Hcl2) as [Hcl4 _]. auto.
  * destruct (step_closedness fs e fs' e' H Hcl1 Hcl2) as [_ Hcl4]. auto.
  * unfold mailboxPush. destruct mb. simpl in *.
    destruct Hcl3. split; auto.
    induction l0.
    + simpl. constructor; auto.
    + simpl. inv H0. constructor. auto. apply IHl0. auto.
  * destruct H.
    + destruct H. destruct H0. subst. clear.
      apply Forall_forall. intros. destruct x.
      apply elem_of_map_to_list in H.
      apply lookup_gset_to_gmap_Some in H. destruct H. subst. scope_solver.
    + destruct H.
      - destruct H, H0, H1, H2. subst.
        apply Forall_forall. intros. destruct x.
        apply elem_of_map_to_list in H. apply lookup_gset_to_gmap_Some in H. destruct H.
        subst. inv Hacl; scope_solver.
      - destruct H, H0, H1. subst. clear.
        apply Forall_forall. intros. destruct x.
        apply elem_of_map_to_list in H.
        apply lookup_gset_to_gmap_Some in H.
        destruct H. subst. scope_solver.
  * unfold mailboxPush. destruct mb. simpl in *. destruct Hcl3.
    split; auto. induction l0.
    + simpl. constructor;[|constructor]. scope_solver.
    + simpl. inv H1. constructor; auto.
  * apply Forall_forall. intros. destruct x.
    apply elem_of_map_to_list in H0.
    destruct (decide (ι = p)).
    + subst. setoid_rewrite lookup_delete in H0. discriminate.
    + setoid_rewrite (lookup_delete_ne _ _ _ n) in H0.
      apply elem_of_map_to_list in H0.
      apply Forall_forall with (x := (p, v)) in Hcl;auto.
  * scope_solver. destruct mb. unfold peekMessage in H. destruct l0; try discriminate.
    inv H. inv Hcl3. inv H0. auto.
  * scope_solver.
  * destruct mb. unfold recvNext in H. destruct l0; try discriminate. inv H.
    simpl. simpl in Hcl3. destruct Hcl3. split.
    + induction l.
      - simpl. inv H0. constructor; auto.
      - simpl. inv H. constructor; auto.
    + inv H0. auto.
  * destruct mb. unfold removeMessage in H. destruct l0; try discriminate. inv H.
    simpl. simpl in Hcl3. destruct Hcl3. split;[constructor|].
    inv H0. induction l.
    + simpl. auto.
    + simpl. inv H. constructor. auto. apply IHl. auto.
  * unfold timeout_value. scope_solver. inv Hcl2. inv H2. auto.
  * unfold lit_from_bool. destruct flag; scope_solver.
  * unfold badarg. scope_solver. inv Hcl2. inv H1. auto.
  * clear.
    apply Forall_forall. intros. destruct x.
    apply elem_of_map_to_list in H. apply lookup_gset_to_gmap_Some in H.
    destruct H. subst. scope_solver.
  * destruct exc. destruct p. simpl.
    apply Forall_forall. intros. destruct x.
    apply elem_of_map_to_list in H. apply lookup_gset_to_gmap_Some in H. destruct H. subst.
    inv Hcl2. auto.
Qed.

Lemma onlyClosedActionPossible: forall n n' pid a O,
  n -[ a | pid ]ₙ-> n' with O -> NODECLOSED n -> ACTIONCLOSED a.
Proof.
  intros n n' pid a O IH.
  induction IH; intros Hcl.
  all:unfold ACTIONCLOSED; unfold NODECLOSED in Hcl; destruct Hcl as [Hcl1 Hcl2].
  * opose proof* (proj1 (Forall_forall _ _) Hcl1 (ι, p)).
    apply elem_of_map_to_list. by setoid_rewrite lookup_insert.
    simpl in H0. clear -H H0.
    inv H; simpl; try constructor.
    - simpl in H0. destruct_and?. inv H0. by inv H3.
    - simpl in H0. destruct_and?. inv H0. by inv H3.
    - simpl in H0.
      opose proof* (proj1 (Forall_forall _ _) H0 (ι', reason)).
      apply elem_of_map_to_list. assumption.
      assumption.
  * clear -H Hcl2.
    unfold etherPop in H. unfold ETHERCLOSED in Hcl2.
    destruct (ether !! (ι0, ι)) eqn:Hineth; try discriminate.
    destruct l eqn:Hl; try discriminate. inv H.
    apply elem_of_map_to_list in Hineth.
    apply Forall_forall with (x := ((ι0, ι), t :: l0)) in Hcl2;auto.
    inv Hcl2. auto.
  * destruct H0.
    + subst a. auto.
    + destruct H0; subst a; auto.
  * unfold POOLCLOSED in Hcl1.
    apply Forall_forall with (x := (ι, p)) in Hcl1;[|apply elem_of_map_to_list; apply lookup_insert].
    inv H4.
    + unfold PROCCLOSED in Hcl1. destruct Hcl1, H5.
      inv H4. inv H9. inv H5. inv H7. inv H13. split; auto.
    + unfold PROCCLOSED in Hcl1. destruct Hcl1, H5.
      inv H4. inv H9. inv H5. inv H7. inv H13. split; auto.
Qed.

Theorem interProcessStepClosedness: forall n n' pid a O,
  n -[ a | pid ]ₙ-> n' with O -> NODECLOSED n -> NODECLOSED n'.
Proof.
  intros n n' pid a O IH Hcl.
  pose proof (onlyClosedActionPossible _ _ _ _ _ IH Hcl) as Hacl. revert Hacl Hcl.
  induction IH; intros Hacl Hcl.
  all:unfold NODECLOSED; unfold NODECLOSED in Hcl; destruct Hcl as [Hcl1 Hcl2]; split; auto.
  all:pose proof Hcl1 as Hcl1'; unfold POOLCLOSED in Hcl1'.
  all:apply Forall_forall with (x := (ι, p)) in Hcl1';[|apply elem_of_map_to_list; apply lookup_insert].
  * pose proof (processLocalStepClosedness _ _ _ H Hcl1' Hacl).
    unfold POOLCLOSED. apply Forall_forall. intros. destruct x.
    apply elem_of_map_to_list in H1.
    destruct (decide (ι = p0)).
    + subst. setoid_rewrite lookup_insert in H1. inv H1. assumption.
    + unfold POOLCLOSED in Hcl1.
      setoid_rewrite (lookup_insert_ne _ _ _ _ n) in H1.
      apply Forall_forall with (x := (p0, p1)) in Hcl1; auto.
      apply elem_of_map_to_list.
      setoid_rewrite (lookup_insert_ne _ _ _ _ n). assumption.
  * clear -Hcl2 Hacl.
    unfold etherAdd.
    destruct (ether !! (ι, ι')) eqn:Heth.
    + unfold ETHERCLOSED. unfold ETHERCLOSED in Hcl2.
      apply Forall_forall. intros. destruct x.
      apply elem_of_map_to_list in H.
      destruct (decide ((ι, ι') = p)).
      - subst p. setoid_rewrite lookup_insert in H. inv H.
        simpl in Hacl.
        apply Forall_forall with (x := (ι, ι', l)) in Hcl2.
        ** clear Heth. induction l; intros.
           ++ scope_solver. auto.
           ++ simpl. inv Hcl2. constructor; auto.
        ** apply elem_of_map_to_list. auto.
      - setoid_rewrite (lookup_insert_ne _ _ _ _ n) in H.
        apply Forall_forall with (x := (p, l0)) in Hcl2; auto.
        apply elem_of_map_to_list. auto.
    + unfold ETHERCLOSED. unfold ETHERCLOSED in Hcl2.
      apply Forall_forall. intros. destruct x.
      apply elem_of_map_to_list in H.
      destruct (decide ((ι, ι') = p)).
      - subst p. setoid_rewrite lookup_insert in H. inv H.
        simpl in Hacl.
        constructor; auto.
      - setoid_rewrite (lookup_insert_ne _ _ _ _ n) in H.
        apply Forall_forall with (x := (p, l)) in Hcl2; auto.
        apply elem_of_map_to_list. auto.
  * pose proof (processLocalStepClosedness _ _ _ H0 Hcl1' Hacl).
    unfold POOLCLOSED. apply Forall_forall. intros. destruct x.
    apply elem_of_map_to_list in H2.
    destruct (decide (ι = p0)).
    + subst. setoid_rewrite lookup_insert in H2. inv H2. assumption.
    + unfold POOLCLOSED in Hcl1.
      setoid_rewrite (lookup_insert_ne _ _ _ _ n) in H2.
      apply Forall_forall with (x := (p0, p1)) in Hcl1; auto.
      apply elem_of_map_to_list.
      setoid_rewrite (lookup_insert_ne _ _ _ _ n). assumption.
  * clear -Hcl2 H.
    unfold etherPop in H.
    destruct (ether !! (ι0, ι)) eqn:Heth; try discriminate.
    destruct l eqn:Hl; try discriminate.
    inv H. unfold ETHERCLOSED in *.
    apply Forall_forall. intros. destruct x.
    apply elem_of_map_to_list in H.
    destruct (decide ((ι0, ι) = p)).
    + subst p. setoid_rewrite lookup_insert in H. inv H.
      apply Forall_forall with (x := (ι0, ι, t :: l)) in Hcl2.
      - inv Hcl2. auto.
      - apply elem_of_map_to_list. auto.
    + setoid_rewrite (lookup_insert_ne _ _ _ _ n) in H.
      apply Forall_forall with (x := (p, l)) in Hcl2; auto.
      apply elem_of_map_to_list. auto.
  * pose proof (processLocalStepClosedness _ _ _ H Hcl1' Hacl).
    unfold POOLCLOSED. apply Forall_forall. intros. destruct x.
    apply elem_of_map_to_list in H2.
    destruct (decide (ι = p0)).
    + subst. setoid_rewrite lookup_insert in H2. inv H2. assumption.
    + unfold POOLCLOSED in Hcl1.
      setoid_rewrite (lookup_insert_ne _ _ _ _ n) in H2.
      apply Forall_forall with (x := (p0, p1)) in Hcl1; auto.
      apply elem_of_map_to_list.
      setoid_rewrite (lookup_insert_ne _ _ _ _ n). assumption.
  * pose proof (processLocalStepClosedness _ _ _ H4 Hcl1' Hacl).
    unfold POOLCLOSED. apply Forall_forall. intros. destruct x.
    apply elem_of_map_to_list in H6.
    destruct (decide (ι' = p0)).
    + subst ι'. setoid_rewrite lookup_insert in H6. inv H6.
      simpl. scope_solver.
      pose proof create_result_closed l (IApp v1) r eff.
      pose proof mk_list_closed v2 l 0.
      inv Hacl. specialize (H7 H9 H).
      assert (ICLOSED (IApp v1)). { scope_solver. }
      symmetry in H3.
      specialize (H6 H7 H10 H3). assumption.
    + setoid_rewrite (lookup_insert_ne _ _ _ _ n) in H6.
      destruct (decide (ι = p0)).
      - subst ι. setoid_rewrite lookup_insert in H6. inv H6. assumption.
      - setoid_rewrite (lookup_insert_ne _ _ _ _ n0) in H6.
        unfold POOLCLOSED in Hcl1.
        apply Forall_forall with (x := (p0, p1)) in Hcl1; auto.
        apply elem_of_map_to_list.
        setoid_rewrite (lookup_insert_ne _ _ _ _ n0). assumption.
Qed.
