From CoreErlang.Concurrent Require Export NodeSemanticsLemmas.

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

Theorem processLocalStepClosednedd: forall p p' a,
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
    apply elem_of_map_to_list in H1.
    destruct (decide (ι = p)).
    + subst. setoid_rewrite lookup_delete in H1. discriminate.
    + setoid_rewrite (lookup_delete_ne _ _ _ n) in H1.
      apply elem_of_map_to_list in H1.
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









