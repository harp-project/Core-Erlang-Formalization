(**
  This file proves numerous properties about the process-local and inter-process
  semantics:
  - lifting sequential and process-local steps to nodes;
  - properties of the reflexive, transitive closure of the node semantics;
  - determinism of internal steps and signal ordering;
  - spawned PIDs, process lifetime and untaken PIDs;
  - composition of process pools;
  - preservation of reduction steps under PID renaming, and the used PIDs of
    nodes during reduction;
  - confluence of steps of different processes;
  - freshness of PIDs, and decision procedures for the used PIDs;
  - steps of nodes with updated ethers and dead processes;
  - evaluating arrivals later (`chain_arrive_later`).

  Some proofs rely on classical logic (`Classical_Prop`,
  `Classical_Pred_Type`).
*)

From CoreErlang.FrameStack Require Export SubstSemanticsLemmas.
From CoreErlang.Concurrent Require Export NodeSemantics.

Import ListNotations.

Require Import Stdlib.Logic.Classical_Prop.
Require Import Stdlib.Logic.Classical_Pred_Type.


(** * Lifting steps to nodes *)

(** Sequential reductions can be lifted to the inter-process level as `τ`
    steps. *)
Theorem sequential_to_node :
  forall k fs e fs' e', ⟨fs, e⟩ -[k]-> ⟨fs', e'⟩ ->
    forall O ι eth Π mb links flag,
      (eth, ι ↦ inl (fs, e, mb, links, flag) ∥ Π) -[repeat (τ, ι) k]ₙ->*
      (eth, ι ↦ inl (fs', e', mb, links, flag) ∥ Π) with O.
Proof.
  intros *. intro H. induction H; intros.
  * constructor.
  * simpl. econstructor.
    constructor. constructor. eassumption.
    by left.
    apply IHstep_rt.
Qed.

(** Everything which falls under the `n_other` category can be lifted to
    inter-process level. *)
Theorem process_local_to_node :
  forall p p' l ι, p -⌈l⌉->* p' ->
    Forall (fun a => a = τ \/ a = ε \/ a = ASelf ι) l ->
    forall O eth Π,
      (eth, ι ↦ p ∥ Π) -[map (fun a => (a, ι)) l]ₙ->*
      (eth, ι ↦ p' ∥ Π) with O.
Proof.
  intros *. intro H. induction H; intros.
  * constructor.
  * simpl. inv H1. specialize (IHLabelStar H5 O eth Π). econstructor.
    2: exact IHLabelStar.
    clear H5 H0 IHLabelStar. destruct_or! H4; subst.
    - constructor; auto.
    - constructor; auto.
    - constructor; auto.
Qed.

(** * The reflexive, transitive closure of the node semantics *)

(** The closure is transitive (the action logs are concatenated). *)
Theorem closureNodeSem_trans :
  forall O n n' l, n -[l]ₙ->* n'  with O -> forall n'' l', n' -[l']ₙ->* n''  with O
->
  n -[l ++ l']ₙ->* n''  with O.
Proof.
  intros O n n' l D1; induction D1; intros; simpl.
  * exact H.
  * eapply n_trans. exact H.
    eapply (IHD1 _ _ H0).
Qed.

(** A step remains valid with fewer observed PIDs. *)
Theorem reduce_O_step :
  forall O O' n n' a ι,
    O' ⊆ O ->
    n -[a | ι]ₙ-> n' with O ->
    n -[a | ι]ₙ-> n' with O'.
Proof.
  intros. inv H0; econstructor; try eassumption.
  set_solver.
Qed.

(** A reduction sequence can be split at any point of its action log. *)
Theorem closureNodeSem_trans_rev :
  forall O l n n'' l', n -[l ++ l']ₙ->* n'' with O
->
  exists n', n -[l]ₙ->* n' with O /\ n' -[l']ₙ->* n'' with O.
Proof.
  induction l; simpl; intros.
  * exists n. split; auto. constructor.
  * inversion H; subst. apply IHl in H5 as [n'2 [H5_1 H5_2]].
    exists n'2. split; auto.
    econstructor; eassumption.
Qed.

(** `n -->* n' with O`: `n` reduces to `n'` with `τ` steps only. *)
Definition internals O (n n' : Node) : Prop :=
  exists l, Forall (fun e => e.1 = τ) l /\ n -[l]ₙ->* n' with O.

Notation "n -->* n' 'with' O" := (internals O n n') (at level 50).

(** `-->*` is reflexive. *)
Theorem internals_refl :
  forall O n, n -->* n with O.
Proof.
  intros. exists []. split; auto. constructor.
Qed.

(** `-->*` is transitive. *)
Theorem internals_trans :
  forall O n n' n'', n -->* n' with O -> n' -->* n'' with O
->
  n -->* n'' with O.
Proof.
  intros. destruct H as [l1 [All1 D1]]. destruct H0 as [l2 [All2 D2]].
  exists (l1 ++ l2). split.
  * now apply Forall_app.
  * eapply closureNodeSem_trans; eassumption.
Qed.

(** `n -[* a | ι *]-> n' with O`: `n` reduces to `n'` with a single `a`
    step of `ι`, surrounded by `τ` steps. *)
Definition onlyOne O (a : Action) (ι : PID) (n n''' : Node) :=
  exists n' n'', n -->* n' with O /\ n' -[a|ι]ₙ-> n'' with O /\ n'' -->* n''' with O.

Notation "n -[* a | ι *]-> n' 'with' O" := (onlyOne O a ι n n') (at level 60).

(** * Determinism and signal ordering *)

(** The node semantics is deterministic for a given action and process. *)
Lemma concurrent_determinism :
  forall O Π a ι Π', Π -[a | ι]ₙ-> Π' with O -> forall Π'', Π -[a | ι]ₙ-> Π'' with O -> Π' = Π''.
Proof.
  intros O Π a ι Π' IH. inversion IH; intros; subst.
  * inv H4.
    - apply insert_eq in H2 as H2'. subst.
      eapply process_local_determinism in H. 2:exact H8. subst. auto. f_equal.
      apply map_eq_iff. intros ι''.
      apply map_eq_iff with (i := ι'') in H2.
      destruct (decide (ι0 = ι'')).
      + subst. setoid_rewrite lookup_insert. by destruct_decide_eq.
      + setoid_rewrite lookup_insert_ne; auto.
        setoid_rewrite lookup_insert_ne in H2; auto.
    - intuition; try congruence.
  * inv H5.
    - apply insert_eq in H2 as H2'. subst.
      eapply process_local_determinism in H0. 2:exact H10. subst.
      f_equal.
      apply map_eq_iff. intros ι''.
      apply map_eq_iff with (i := ι'') in H2.
      destruct (decide (ι0 = ι'')).
      + subst. setoid_rewrite lookup_insert. by destruct_decide_eq.
      + setoid_rewrite lookup_insert_ne; auto.
        setoid_rewrite lookup_insert_ne in H2; auto.
    - intuition; try congruence.
  * inv H5.
    - intuition; try congruence.
    - intuition; try congruence.
    - apply insert_eq in H2 as H2'. subst.
      eapply process_local_determinism in H. 2: exact H3. subst. f_equal.
      apply map_eq_iff. intros ι''.
      apply map_eq_iff with (i := ι'') in H2.
      destruct (decide (ι = ι'')).
      + subst. setoid_rewrite lookup_insert. by destruct_decide_eq.
      + setoid_rewrite lookup_insert_ne; auto.
        setoid_rewrite lookup_insert_ne in H2; auto.
    - intuition; try congruence.
  * inv H9.
    - intuition; try congruence.
    - apply insert_eq in H6 as P. subst.
      eapply process_local_determinism in H4. 2: exact H19. subst.
      f_equal.
      apply map_eq_iff. intros ι''.
      apply map_eq_iff with (i := ι'') in H6.
      destruct (decide (ι' = ι'')).
      + subst. setoid_rewrite lookup_insert. by destruct_decide_eq.
      + setoid_rewrite lookup_insert_ne; auto.
        destruct (decide (ι = ι'')).
        ** subst. setoid_rewrite lookup_insert. by destruct_decide_eq.
        ** setoid_rewrite lookup_insert_ne; auto.
           setoid_rewrite lookup_insert_ne in H6; auto.
Qed.

(** If a live process can take a `τ` step and an `a` step, then either
    `a = τ` (and the results are equal), or `a` is a signal arrival, and the
    two steps can be joined (the process-level version of `internal_det`). *)
Lemma internal_equal :
  forall p p', inl p -⌈ τ ⌉-> p' -> forall p'' a, inl p -⌈ a ⌉-> p''
->
  (a = τ /\ p'' = p') \/
  (exists t ι ι', a = AArrive ι ι' t
   /\ exists p''', p' -⌈AArrive ι ι' t⌉-> p''' /\
   (p'' -⌈ τ ⌉-> p''' \/ p'' = p''')).
Proof.
  intros. destruct a.
  * exfalso. inv H0; inv H; try inv H6; try inv H7; cbn in *; try invSome.
  * right. do 3 eexists. split. reflexivity. inv H0.
    - inv H.
      + eexists. split. constructor. left. now constructor.
      + eexists. split. constructor. left. apply p_recv_peek_message_ok.
        destruct mb. destruct l0; simpl in *; by invSome.
      + eexists. split. constructor. left.
        unfold mailboxPush. apply p_recv_next.
        destruct mb; simpl in *. destruct l0; inv H6.
        by simpl.
      + eexists. split. constructor. left. apply p_remove_message.
        destruct mb. destruct l0; simpl in *; invSome.
        simpl. by rewrite app_assoc.
      + eexists. split. constructor. left. apply p_recv_wait_timeout_new_message.
      + eexists. split. constructor. left. apply p_recv_wait_timeout_0.
      + eexists. split. constructor. left. by apply p_recv_wait_timeout_invalid.
      + eexists. split. constructor. left. now constructor.
    - inv H.
      + eexists. split. constructor. assumption. left. now constructor.
      + eexists. split. constructor. assumption. left. now constructor.
      + eexists. split. constructor. assumption. left. now constructor.
      + eexists. split. constructor. assumption. left. now constructor.
      + eexists. split. constructor. assumption. left. now constructor.
      + eexists. split. constructor. assumption. left. now constructor.
      + eexists. split. constructor. assumption. left. now constructor.
      + eexists. split. constructor. assumption. left. now constructor.
    - inv H.
      + eexists. split. apply p_exit_terminate. eassumption. now right.
      + eexists. split. apply p_exit_terminate. eassumption. now right.
      + eexists. split. apply p_exit_terminate. eassumption. now right.
      + eexists. split. apply p_exit_terminate. eassumption. now right.
      + eexists. split. apply p_exit_terminate. eassumption. now right.
      + eexists. split. apply p_exit_terminate. eassumption. now right.
      + eexists. split. apply p_exit_terminate. eassumption. now right.
      + eexists. split. apply p_exit_terminate. eassumption. now right.
    - inv H.
      + eexists. split. apply p_exit_convert; auto. left. now constructor.
      + eexists. split. apply p_exit_convert; auto. left.
        apply p_recv_peek_message_ok.
        destruct mb, l0; simpl in *; by invSome.
      + eexists. split. apply p_exit_convert; auto. left.
        apply p_recv_next.
        destruct mb, l0; inv H7. by simpl.
      + eexists. split. apply p_exit_convert; auto. left.
        apply p_remove_message.
        destruct mb, l0; simpl in *; invSome. by rewrite app_assoc.
      + eexists. split. apply p_exit_convert; auto. left. now constructor.
      + eexists. split. apply p_exit_convert; auto. left. now constructor.
      + eexists. split. apply p_exit_convert; auto. left. now constructor.
      + eexists. split. apply p_exit_convert; auto. left. now constructor.
    - inv H.
      all: eexists; split; [constructor|];left; now constructor.
    - inv H.
      all: eexists; split; [constructor|];left; now constructor.
  * exfalso. inv H0; inv H. inv H6; cbn in *; invSome.
  * exfalso. inv H0; inv H. inv H6; cbn in *; invSome.
    inv H6; cbn in *; invSome.
  * left. eapply process_local_determinism in H; eauto.
  * exfalso. inv H0; inv H; try (now inv H7 + now inv H6).
    all: congruence.
Qed.

(**
  If a <> τ, then a = arrive ι' ι σ, and the derivations with double lines exist:

  n -- ι:τ ----> n'
  |              ∥
  | ι:a          ∥ ι:a
  |              ∥
  v              v
 n'' == ι:τ ===> n'''

    or n'' = n''' (in case an exit signal was delivered)


  If a = τ, then:

  n ---ι:τ-----> n'
  |              |
  | ι:τ         /
  |            /
  v      ==   /
 n''---------

*)
Lemma internal_det :
  forall O n n' n'' ι a, n -[τ | ι]ₙ-> n' with O -> n -[a | ι]ₙ-> n'' with O
->
  (a = τ /\ n''= n') \/ (exists t ι', a = AArrive ι' ι t /\
                                 exists n''', n' -[AArrive ι' ι t | ι]ₙ-> n''' with O /\
                                 (n'' -[τ | ι]ₙ-> n''' with O \/ n'' = n''')).
Proof.
  intros. inv H; inv H0.
  * exfalso. inv H7.
    - apply insert_eq in H4. subst. inv H1. inv H7.
    - apply insert_eq in H4. subst. inv H1. inv H7.
    - apply insert_eq in H4. subst. inv H1. inv H7.
    - apply insert_eq in H4. subst. inv H1. inv H7.
    - apply insert_eq in H4. subst. inv H1.
  * apply insert_eq in H3 as H3'. subst.
    apply internal_is_alive in H1 as H1'. destruct H1'. subst.
    eapply internal_equal in H8. 2: eassumption.
    intuition; subst; try congruence.
    right. repeat destruct_hyps. do 2 eexists. split. reflexivity.
    inv H0.
    eexists. split. constructor; try eassumption. destruct H5.
    - left. setoid_rewrite insert_eq_Π.
      apply n_other; eauto.
      exact H3. reflexivity. Unshelve. exact (inr ∅).
    - right. subst. setoid_rewrite insert_eq_Π. reflexivity. eassumption.
      reflexivity. Unshelve. exact (inr ∅).
  * apply insert_eq in H3 as H3'. subst.
    destruct H8 as [H8 | [ H8 | H8]].
    - subst. left. split; auto. eapply process_local_determinism in H4. 2: exact H1.
      subst. eapply insert_eq_Π in H3. now rewrite H3.
    - subst. exfalso. inv H4. inv H1. inv H8.
    - subst. exfalso. inv H4; inv H1; try inv H9; try inv H8; try by cbn in *.
      congruence.
  * apply insert_eq in H3 as H3'. subst.
    exfalso. inv H12; inv H1; inv H13; now cbn in *.
Qed.

(** Both actions are spawns. *)
Definition bothSpawn (a1 a2 : Action) : Prop:=
match a1, a2 with
| ASpawn _ _ _ _, ASpawn _ _ _ _ => True
| _, _ => False
end.

(** Two actions are compatible if a spawn does not use the PID which is
    the target of the other action (send or spawn). *)
Definition compatiblePIDOf (a1 a2 : Action) :=
match a1, a2 with
| ASend _ ι1 _, ASpawn ι2 _ _ _
| ASpawn ι1 _ _ _, ASend _ ι2 _
| ASpawn ι1 _ _ _, ASpawn ι2 _ _ _ => (ι1 <> ι2)%type
| _, _ => True
end.

(** Two actions are either compatible, or one of them spawns a PID `from`,
    such that renaming `from` to different fresh PIDs in the two actions
    makes them compatible. *)
Theorem compatiblePIDOf_options :
  forall a a',
    compatiblePIDOf a a' \/
    (exists from, (Some from = spawnPIDOf a \/ Some from = spawnPIDOf a') /\
      forall to1 to2, to1 ≠ to2 ->
      (to1 ∉ usedPIDsAct a) -> (to1 ∉ usedPIDsAct a') ->
      (to2 ∉ usedPIDsAct a) -> (to2 ∉ usedPIDsAct a') ->
      compatiblePIDOf (renamePIDAct from to1 a) (renamePIDAct from to2 a')).
Proof.
  intros. destruct a, a'; simpl; try by left; intros.
  * right. exists ι. split. by right. intros. renamePIDPID_case_match. set_solver.
  * right. exists ι. split. by left.  intros. renamePIDPID_case_match. set_solver.
  * right. exists ι. split. by left.  intros. renamePIDPID_case_match. set_solver.
Qed.

(** Two actions are either compatible, or for every PID `to` fresh in them,
    renaming the PID spawned by one of the actions to `to` makes them
    compatible. *)
Theorem compatiblePIDOf_options_alt :
  forall a a',
    compatiblePIDOf a a' \/
    forall to, (to ∉ usedPIDsAct a) -> (to ∉ usedPIDsAct a') ->
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

(** If the signal `s` from `ι` to `ι'` does not arrive during a reduction
    sequence, then it stays in the ether, and only signals from the front of
    it can be removed. *)
Lemma no_ether_pop : forall O l Π Π',
  Π -[ l ]ₙ->* Π' with O ->
  forall ι ι' sigs s sigs',
  (AArrive ι ι' s, ι') ∉ l ->
  fst Π !! (ι, ι') = Some (sigs ++ s :: sigs') ->
  exists sigs1 sigs2, fst Π' !! (ι, ι') = Some (sigs1 ++ s :: sigs' ++ sigs2) /\ 
                      exists sigs1_1, sigs = sigs1_1 ++ sigs1.
Proof.
  intros ? ? ? ? D. induction D; intros.
  * eexists. exists []. rewrite app_nil_r. split. exact H0.
    exists []. reflexivity.
  * apply not_elem_of_cons in H0 as [H0_1 H0_2].
    inversion H; subst.
    (* Send: potentially puts something at the end *)
    - unfold etherAdd in IHD. cbn in *.
      destruct (decide ((ι, ι'0) = (ι0, ι'))).
      + inv e.
        specialize (IHD ι0 ι' sigs s (sigs' ++ [t]) H0_2).
        cbn in *. rewrite H1 in IHD. rewrite <- app_assoc in IHD.
        assert (sigs ++ (s :: sigs') ++ [t] = sigs ++ s :: sigs' ++ [t]). {
          f_equal.
        }
        setoid_rewrite lookup_insert in IHD.
        rewrite H2 in IHD. destruct_decide_eq. specialize (IHD eq_refl).
        destruct IHD as [sigs1 [sigs2 [Hlookup [sigs1_1 Heq]]]].
        exists sigs1, ([t] ++ sigs2).
        split.
        rewrite Hlookup. f_equal. rewrite <- app_assoc. cbn. reflexivity.
        exists sigs1_1. exact Heq.
      + break_match_hyp; simpl in IHD; apply IHD; auto;
        setoid_rewrite lookup_insert_ne; auto.
    (* Arrive: potentially removes something *)
    - cbn in *.
      destruct (ι0 =? ι2) eqn:Eq1.
      + destruct (ι' =? ι) eqn:Eq2.
        ** apply Nat.eqb_eq in Eq1. apply Nat.eqb_eq in Eq2. subst.
           unfold etherPop in H0. rewrite H1 in H0.
           destruct sigs as [|s_popped sigs_tail].
           cbn in H0. inversion H0; subst. exfalso. apply H0_1. f_equal.
           cbn in H0. inversion H0; subst. specialize (IHD ι2 ι sigs_tail s sigs' H0_2).
           setoid_rewrite lookup_insert in IHD. destruct_decide_eq. specialize (IHD eq_refl).
           destruct IHD as [sigs1 [sigs2 [Hlookup [sigs1_1 Heq]]]]. exists sigs1, sigs2.
           split. 
           exact Hlookup. 
           exists (t :: sigs1_1). cbn. f_equal. exact Heq.
        **   unfold etherPop in H0. break_match_hyp. 2: congruence.
           destruct l0. congruence.
           inversion H0. subst. eapply IHD in H0_2. apply H0_2.
           eqb_to_eq. subst. setoid_rewrite lookup_insert_ne. 2: intro X; inv X; auto.
           assumption.
      + unfold etherPop in H0. break_match_hyp. 2: congruence.
        destruct l0. congruence.
        inversion H0. subst. eapply IHD in H0_2. apply H0_2.
        eqb_to_eq. setoid_rewrite lookup_insert_ne. 2: intro X; inv X; auto.
        assumption.
    (* Other actions do not modify the ether *)
    - eapply IHD. auto. cbn in *. rewrite H1. reflexivity.
    - eapply IHD. auto. cbn in *. rewrite H1. reflexivity.
Qed.

(** Signal ordering: if `ι` sends `s1` and then `s2` to `ι'`, then `s2` cannot
    arrive before `s1`. *)
Lemma signal_ordering :
  forall O l Π (ι ι' : PID) s1 s2 Π' Π'' Π''' (NEQ : s1 <> s2),
            Π -[ASend ι ι' s1 | ι]ₙ-> Π' with O ->
            Π' -[ASend ι ι' s2 | ι]ₙ-> Π'' with O ->
            (AArrive ι ι' s1, ι') ∉ l ->
            (forall l, fst Π !! (ι, ι') = Some l -> s1 ∉ l) ->
            (forall l, fst Π !! (ι, ι') = Some l -> s2 ∉ l) ->
            Π'' -[l]ₙ->* Π''' with O ->
            ~exists Σ, Π''' -[AArrive ι ι' s2 | ι']ₙ-> Σ with O.
Proof.
  intros. inv H. inv H0.
  2-3: intuition; try congruence.
  cbn in *.
  (* inversion H13; subst. clear H13. *)
  assert (exists sigs sigs', etherAdd ι ι' s2 (etherAdd ι ι' s1 ether) !! (ι, ι') = Some (sigs ++ s1 :: sigs')) as [sigs1 [sigs2 H]]. {
    unfold etherAdd. destruct (ether !! (ι, ι')); setoid_rewrite lookup_insert.
    + destruct_decide_eq. setoid_rewrite lookup_insert. destruct_decide_eq.
      exists l0, [s2]. now rewrite <- app_assoc.
    + destruct_decide_eq. setoid_rewrite lookup_insert. destruct_decide_eq.
      now exists [], [s2].
  }
  epose proof (no_ether_pop _ l _ _ H4 _ _ _ _ _ H1 H).
  intro. destruct H5 as [Π''''].
  destruct H0 as [sigs11 [sigs3]].
  clear H1 H4. inv H5.
  2: { intuition; try congruence. }
  destruct H0 as [H0 H0_1].
  cbn in *. unfold etherPop in H13. rewrite H0 in H13.
  destruct sigs11; cbn in *. by inv H13.
  cbn in *. inv H13.
  unfold etherAdd in H. destruct (ether !! (ι, ι0)); setoid_rewrite lookup_insert in H; destruct_decide_eq; setoid_rewrite lookup_insert in H; destruct_decide_eq; try rewrite <- app_assoc in H; inv H.
  * destruct H0_1. subst.
    specialize (H2 l0 eq_refl). specialize (H3 l0 eq_refl).
    rewrite <- app_assoc in H4.
    apply in_list_order in H4; auto; rewrite <- list_elem_of_In; set_solver.
  * destruct H0_1. subst.
    destruct x. by inv H4.
    apply (f_equal length) in H4.
    cbn in H4. repeat rewrite length_app in H4. cbn in H4. lia.
Qed.

(** * Spawned PIDs and process lifetime *)

(** The PIDs which are not spawned during a reduction sequence are
    associated with a process after the sequence iff they were associated
    before. *)
Lemma no_spawn_included :
  forall O l n n', n -[l]ₙ->* n' with O ->
    forall ι, ι ∉ (PIDsOf spawnPIDOf l) ->
      n.2 !! ι = None <-> n'.2 !! ι = None.
Proof.
  intros. induction H; auto;
  unfold PIDsOf in H0; simpl in H0; fold (PIDsOf spawnPIDOf l) in H0;
  apply not_elem_of_app in H0 as [H0_1 H0_2]; apply IHclosureNodeSem in H0_2;
  clear IHclosureNodeSem H1; split; intro I; [ apply H0_2 | apply H0_2 in I ];
  inv H; simpl in *.
  all: try (destruct (decide (ι0 = ι)); subst; [
       setoid_rewrite lookup_insert in I;
       setoid_rewrite lookup_insert;
       try congruence
     |
       setoid_rewrite lookup_insert_ne in I; auto;
       setoid_rewrite lookup_insert_ne; auto;
       intro Z; now apply I in Z
     ]).
  all: try by destruct_decide_eq.
  * assert (ι' <> ι) by (clear- H0_1; set_solver). clear H4.
    setoid_rewrite lookup_insert_ne; auto.
    try (destruct (decide (ι0 = ι)); subst; [
       setoid_rewrite lookup_insert in I;
       setoid_rewrite lookup_insert;
       try congruence
     |
       setoid_rewrite lookup_insert_ne in I; auto;
       setoid_rewrite lookup_insert_ne; auto;
       intro Z; now apply I in Z
     ]).
    by destruct_decide_eq.
  * assert (H_neq_prime: ι' <> ι) by (clear- H0_1; set_solver).
    destruct (decide (ι0 = ι)) as [-> | NEQ].
    { setoid_rewrite lookup_insert_ne in I; [|exact H_neq_prime].
      setoid_rewrite lookup_insert in I.
      by destruct_decide_eq.
    }
    { setoid_rewrite lookup_insert_ne in I; [|exact H_neq_prime].
      setoid_rewrite lookup_insert_ne in I; [|exact NEQ].
      setoid_rewrite lookup_insert_ne; [|exact NEQ].
      exact I.
    }
Qed.

(** If a PID is not associated with any process after a reduction sequence,
    then it was not spawned during the sequence. *)
Lemma no_spawn_included_2 :
  forall O l n n', n -[l]ₙ->* n' with O ->
    forall ι, n'.2 !! ι = None ->
    ι ∉ (PIDsOf spawnPIDOf l).
Proof.
  induction l using list_length_ind.
  intros. destruct (length l) eqn:Hlen.
  * apply length_zero_iff_nil in Hlen. subst. set_solver.
  * destruct (exists_last (l := l) ltac:(intros ->; discriminate Hlen)) as [l' [x ?]]; subst.
    rename n' into n''.
    apply closureNodeSem_trans_rev in H0 as [n' [D1 D2]].
    rewrite length_app in Hlen. simpl in Hlen. inv D2. inv H6. inv H4.
    - eapply H with (ι := ι) in D1. 2: lia.
      2: {
        simpl in *; destruct (decide (ι0 = ι)); subst; [
          setoid_rewrite lookup_insert in H1;
          try congruence
        |
          setoid_rewrite lookup_insert_ne in H1; auto;
          setoid_rewrite lookup_insert_ne; auto;
          intro Z; now apply I in Z
        ].
          by destruct_decide_eq.
         }
      unfold PIDsOf. rewrite flat_map_app. apply not_elem_of_app; split.
      1-2: fold (PIDsOf spawnPIDOf l'); simpl; auto.
      set_solver.
    - eapply H with (ι := ι) in D1. 2: lia.
      2: {
        simpl in *; destruct (decide (ι0 = ι)); subst; [
          setoid_rewrite lookup_insert in H1;
          try congruence
        |
          setoid_rewrite lookup_insert_ne in H1; auto;
          setoid_rewrite lookup_insert_ne; auto;
          intro Z; now apply I in Z
        ].
          by destruct_decide_eq.
         }
      unfold PIDsOf. rewrite flat_map_app. apply not_elem_of_app; split.
      1-2: fold (PIDsOf spawnPIDOf l'); simpl; auto.
      set_solver.
    - eapply H with (ι := ι) in D1. 2: lia.
      2: {
        simpl in *; destruct (decide (ι0 = ι)); subst; [
          setoid_rewrite lookup_insert in H1;
          try congruence
        |
          setoid_rewrite lookup_insert_ne in H1; auto;
          setoid_rewrite lookup_insert_ne; auto;
          intro Z; now apply I in Z
        ].
          by destruct_decide_eq.
         }
      unfold PIDsOf. rewrite flat_map_app. apply not_elem_of_app; split.
      1-2: fold (PIDsOf spawnPIDOf l'); simpl; auto.
      destruct a; simpl; auto.
      destruct H2 as [? | [? | ?]]; congruence. all: set_solver.
    - unfold PIDsOf. rewrite flat_map_app. apply not_elem_of_app; split.
      1-2: fold (PIDsOf spawnPIDOf l'); simpl.
      + eapply H. lia. eassumption.
        simpl in *. clear H5.
        destruct (decide (ι' = ι)); subst.
        1: setoid_rewrite lookup_insert in H1; destruct_decide_eq.
        setoid_rewrite lookup_insert_ne in H1; auto.
        destruct (decide (ι0 = ι)); subst.
        { 
          setoid_rewrite lookup_insert in H1. by destruct_decide_eq.
        }
        setoid_rewrite lookup_insert_ne in H1; auto.
        setoid_rewrite lookup_insert_ne; auto.
      + intro. assert (ι = ι') by set_solver. subst.
        simpl in H1. setoid_rewrite lookup_insert in H1. by destruct_decide_eq.
Qed.

(** Case-splits on whether the PID looked up in a process pool is the one
    inserted last (`ι0 ↦ _ ∥ _`), in the goal or in a hypothesis. The
    `_manual` variants take the PIDs (and the hypothesis) explicitly. *)
(* TODO: generalize *)
Ltac processpool_destruct :=
match goal with
| [H : (?ι0 ↦ _ ∥ _) !! ?ι = _ |- _] =>
  simpl in *; destruct (decide (ι0 = ι)); subst; [
    setoid_rewrite lookup_insert in H; try destruct_decide_eq
  |
    setoid_rewrite lookup_insert_ne in H; auto
  ]
| [|- (?ι0 ↦ _ ∥ _) !! ?ι = _] =>
  simpl in *; destruct (decide (ι0 = ι)); subst; [
    setoid_rewrite lookup_insert; try destruct_decide_eq
  |
    setoid_rewrite lookup_insert_ne; auto
  ]
| [H : (?ι0 ↦ _ ∥ _) !! ?ι ≠ _ |- _] =>
  simpl in *; destruct (decide (ι0 = ι)); subst; [
    setoid_rewrite lookup_insert in H; try destruct_decide_eq
  |
    setoid_rewrite lookup_insert_ne in H; auto
  ]
| [|- (?ι0 ↦ _ ∥ _) !! ?ι ≠ _] =>
  simpl in *; destruct (decide (ι0 = ι)); subst; [
    setoid_rewrite lookup_insert; try destruct_decide_eq
  |
    setoid_rewrite lookup_insert_ne; auto
  ]
end.

Ltac processpool_destruct_manual_hyp ι0 ι H :=
  simpl in *; destruct (decide (ι0 = ι)); subst; [
    setoid_rewrite lookup_insert in H; destruct_decide_eq
  |
    setoid_rewrite lookup_insert_ne in H; auto
  ].

Ltac processpool_destruct_manual ι0 ι :=
  simpl in *; destruct (decide (ι0 = ι)); subst; [
    setoid_rewrite lookup_insert; destruct_decide_eq
  |
    setoid_rewrite lookup_insert_ne; auto
  ].



(** If a PID is not associated with any process after a reduction sequence,
    then it was not associated with any process before the sequence
    either. *)
Lemma processes_dont_die_None :
  forall O l n n', n -[l]ₙ->* n' with O ->
    forall ι, n'.2 !! ι = None -> n.2 !! ι = None.
Proof.
  induction l using list_length_ind.
  destruct (length l) eqn:Hl; intros.
  * apply length_zero_iff_nil in Hl; subst. inv H0. auto.
  * pose proof Hl.
    destruct (exists_last (l := l) ltac:(intros ->; discriminate Hl)) as [l' [x Eq]].
    clear Hl. subst.
    apply closureNodeSem_trans_rev in H0 as [n0' [D1 D2]].
    rewrite length_app in H2. simpl in *.
    inv D2. inv H7.
    eapply H in D1; eauto. lia. 
    
    inv H5; simpl.
    1-3: simpl in *;
         destruct (decide (ι0 = ι)); subst; [
         setoid_rewrite lookup_insert in H1; try congruence
         | 
           setoid_rewrite lookup_insert_ne in H1; auto;
           setoid_rewrite lookup_insert_ne; auto
         ].
    all: simpl in *; destruct (decide (ι = ι)); try congruence.
    destruct (decide (ι = ι')); subst.
    { setoid_rewrite lookup_insert in H1. by destruct_decide_eq. }
    setoid_rewrite lookup_insert_ne in H1; auto.
    destruct (decide (ι = ι0)); subst.
    { setoid_rewrite lookup_insert in H1. by destruct_decide_eq. }
    setoid_rewrite lookup_insert_ne in H1; auto.
    setoid_rewrite lookup_insert_ne; auto.
Qed.


(** Processes are never removed from the pool (dead processes remain as
    `inr`). *)
Lemma processes_dont_die :
  forall O n n' l, n -[l]ₙ->* n' with O ->
    forall ι, n.2 !! ι <> None -> n'.2 !! ι <> None.
Proof.
  intros. induction H; auto.
  apply IHclosureNodeSem. clear IHclosureNodeSem H1. inv H.
  all: simpl in *.
  1-3: repeat processpool_destruct; auto.
  all: simpl in *; try by destruct_decide_eq.
  destruct (decide (ι = ι')); subst.
  { 
    setoid_rewrite lookup_insert. by destruct_decide_eq.
  }
  setoid_rewrite lookup_insert_ne; last auto.
  destruct (decide (ι = ι0)); subst.
  { 
    setoid_rewrite lookup_insert. by destruct_decide_eq.
  }
 setoid_rewrite lookup_insert_ne; last auto.
 revert H0. setoid_rewrite lookup_insert_ne. intros H0. exact H0. symmetry. exact n0.
Qed.


(** The previous property, phrased slightly differently: if a PID is
    associated with a process before a reduction sequence, then it is
    associated with some (possibly changed) process after it. *)
Corollary processes_dont_die_Some :
  forall O n n' l, n -[l]ₙ->* n' with O ->
    forall ι p, n.2 !! ι = Some p -> exists p', n'.2 !! ι = Some p'.
Proof.
  intros.
  epose proof (processes_dont_die _ _ _ _ H ι _).
  Unshelve. 2: { intro D. rewrite D in H0. congruence. }
  destruct (n'.2 !! ι). eexists. reflexivity.
  congruence.
Qed.

(** The PIDs of existing processes are not spawned. *)
Lemma no_spawn_on_Some :
  forall O n n' l, n -[l]ₙ->* n' with O ->
    forall ι, n.2 !! ι <> None ->
      ι ∉ (PIDsOf spawnPIDOf l).
Proof.
  intros O n n' l H. induction H; intros; simpl; auto.
  intro Ha. set_solver. inv H; simpl in *.
  * assert ((ι ↦ p' ∥ prs) !! ι0 <> None). {
      repeat processpool_destruct; auto.
    }

    now apply IHclosureNodeSem in H.
  * assert ((ι ↦ p' ∥ prs) !! ι0 <> None). {
      repeat processpool_destruct; auto.
    }
    now apply IHclosureNodeSem in H.
  * assert ((ι ↦ p' ∥ Π) !! ι0 <> None). {
      repeat processpool_destruct; auto.
    }
    apply IHclosureNodeSem in H. destruct a; auto.
    destruct H3 as [? | [? | ?]]; congruence.
  * clear H7. intro Ha. apply elem_of_cons in Ha as [|].
    - subst. setoid_rewrite lookup_insert_ne in H1;
      apply not_isUsedPool_insert_1 in H4 as [? ?]. 2: lia.
      apply not_elem_of_dom in H. congruence.
    - assert ((ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false) ∥ ι ↦ p' ∥ Π) !! ι0 <> None). {
      repeat processpool_destruct; auto.
    }
    apply IHclosureNodeSem in H; auto.
Qed.



(** The PIDs targeted in the ether are not spawned. *)
Lemma isTargetedEther_no_spawn :
  forall O n n' l, n -[l]ₙ->* n' with O ->
    forall ι, (exists ι' l, n.1 !! (ι', ι) = Some l) ->
      ι ∉ (PIDsOf spawnPIDOf l).
Proof.
  intros O n n' l H. induction H; intros; simpl. set_solver.
  intro Ha. inv H; simpl in *.
  * pose proof (isTargetedEther_etherAdd ether _ ι ι' t H1). apply IHclosureNodeSem in H.
    congruence.
  * apply (@isTargetedEther_etherPop _ ι0) in H2 as [H2 | H2]; try assumption.
    now apply IHclosureNodeSem in H2.
    subst. remember (ether', ι ↦ p' ∥ prs) as n.
    assert (n.2 !! ι <> None). {
      subst n. cbn. setoid_rewrite lookup_insert.
      by destruct_decide_eq.
    }
    eapply no_spawn_on_Some in H0. 2: eassumption. congruence.
  * destruct a; simpl in *; try now apply IHclosureNodeSem in Ha.
    destruct H3 as [? | [? | ?]]; congruence.
  * clear H7. apply elem_of_cons in Ha as [|].
    subst. destruct_hyps. apply H5. left. by exists x, x0.
    apply IHclosureNodeSem in H; auto.
Qed.

(** Observed PIDs are not spawned. *)
Lemma no_spawn_on_O :
  forall O n n' l, n -[l]ₙ->* n' with O ->
    forall ι, ι ∈ O ->
      ι ∉ (PIDsOf spawnPIDOf l).
Proof.
  intros O n n' l H. induction H; intros; simpl. set_solver.
  intro Ha. inv H; simpl in *.
  * apply IHclosureNodeSem in Ha. 2: assumption. congruence.
  * apply IHclosureNodeSem in Ha. 2: assumption. congruence.
  * destruct a; try (apply IHclosureNodeSem in Ha; [|assumption]; congruence).
    destruct H3 as [? | [? | ?]]; congruence.
  * clear H7. apply elem_of_cons in Ha as [|]. congruence.
    apply IHclosureNodeSem in H; auto.
Qed.

(** * Untaken PIDs *)

(** A PID is untaken if it is not associated with a process, but it is
    targeted in the ether. *)
Definition isUntaken (ι : PID) (n : Node) : Prop :=
  n.2 !! ι = None /\ isTargetedEther ι n.1.

(** Steps preserve untaken PIDs. *)
Theorem compatibility_of_reduction :
  forall O n n' a ι, n -[a | ι]ₙ-> n' with O ->
    forall ι, isUntaken ι n ->
      isUntaken ι n'.
Proof.
  intros. inv H.
  * (* left. *) destruct H0. split.
    - simpl in *. repeat processpool_destruct; congruence.
    - simpl in *. now apply isTargetedEther_etherAdd.
  * (* left. *) destruct H0. split.
    - simpl in *. repeat processpool_destruct; congruence.
    - simpl in *. eapply isTargetedEther_etherPop in H1 as [H1 | H1].
      + eassumption.
      + subst. by repeat processpool_destruct.
      + assumption.
  * (* left. *) destruct H0. split.
    - simpl in *. repeat processpool_destruct; congruence.
    - assumption.
  * destruct H0. simpl in *.
    repeat processpool_destruct; try congruence.
    destruct (Nat.eq_dec ι0 ι').
    - subst.
      epose proof (isTargetedEther_no_spawn O (ether, ι ↦ p ∥ Π) (ether, ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false) ∥ ι ↦ p' ∥ Π) [(ASpawn ι' v1 v2 link_flag, ι)] _ _ H0).
      simpl in H7. set_solver.
      Unshelve. econstructor. eapply n_spawn; try eassumption. constructor.
    -(*  left. *) split.
      + simpl. repeat processpool_destruct; congruence.
      + simpl. assumption.
Qed.


(** Reduction sequences preserve untaken PIDs. *)
Corollary compatibility_of_reductions :
   forall O n n' l, n -[l]ₙ->* n' with O ->
    forall ι, isUntaken ι n ->
      isUntaken ι n'.
Proof.
  intros O n n' l H. induction H; intros; auto.
  apply (compatibility_of_reduction _ _ _ _ _ H) in H1(*  as [H1 | [H1_1 H1_2]] *).
  * now apply IHclosureNodeSem in H1. 
Qed.



(** If a PID is untaken after a step, then either it was untaken before the
    step as well, or the step sent the first signal to it. *)
Theorem compatibility_of_reduction_rev :
  forall O n n' a ι, n -[a | ι]ₙ-> n' with O ->
    forall ι,
      isUntaken ι n' ->
      isUntaken ι n \/
      (sendPIDOf a = Some ι /\ ~isTargetedEther ι n.1 /\ n.2 !! ι = None).
Proof.
  intros. inv H.
  * destruct H0.
    destruct (Nat.eq_dec ι' ι0); simpl; subst.
    - simpl in *.
      destruct (isTargetedEther_dec ι0 ether).
      + left. split. simpl. repeat processpool_destruct; congruence.
        now simpl.
      + right. split; simpl; auto.
        split; auto. repeat processpool_destruct; congruence.
    - left. split.
      + simpl in *. repeat processpool_destruct; congruence.
      + simpl in *. eapply isTargetedEther_etherAdd_rev. eassumption. assumption.
  * destruct H0. left. split.
    - simpl in *. repeat processpool_destruct; congruence.
    - simpl in *. eapply isTargetedEther_etherPop_rev; eassumption.
  * destruct H0. left. split.
    - simpl in *. repeat processpool_destruct; congruence.
    - assumption.
  * clear H3 H4 H1. destruct H0. simpl in *.
    destruct (Nat.eq_dec ι0 ι').
    - subst. processpool_destruct.
      congruence.
    - left. split.
      + simpl. repeat processpool_destruct; congruence.
      + simpl. assumption.
Qed.

(** If a PID is untaken after a reduction sequence, then either it was
    untaken before the sequence as well, or a signal was sent to it during
    the sequence. *)
Corollary compatibility_of_reductions_rev :
   forall O l n n', n -[l]ₙ->* n' with O ->
    forall ι,
      isUntaken ι n' ->
      isUntaken ι n \/
      (ι ∈ (PIDsOf sendPIDOf l) /\ ~isTargetedEther ι n.1 /\ n.2 !! ι = None).
Proof.
  induction l using list_length_ind.
  destruct (length l) eqn:Hl; intros.
  * apply length_zero_iff_nil in Hl; subst. inv H0. auto.
  * pose proof Hl.
    destruct (exists_last (l := l) ltac:(intros ->; discriminate Hl)) as [l' [x Eq]].
    clear Hl. subst.
    apply closureNodeSem_trans_rev in H0 as [n0' [D1 D2]].
    rewrite length_app in H2. simpl in *.
    inv D2. inv H7. eapply compatibility_of_reduction_rev in H5.
    2: eassumption.
    destruct H5. 2: destruct H0.
    - eapply H in D1. 2: lia. 2: eassumption.
      destruct D1; auto. destruct_hyps.
      right; split. 2: split; auto.
      unfold PIDsOf. rewrite flat_map_app. simpl.
      fold (PIDsOf spawnPIDOf l'). apply elem_of_app. now left.
    - destruct_hyps. clear H H2 H1.
      unfold isUntaken.
      eapply processes_dont_die_None in D1 as P3. 2: eassumption.
      destruct (isTargetedEther_dec ι n0.1).
      + left. easy.
      + right. split. 2: easy.
        unfold PIDsOf. rewrite flat_map_app.
        apply elem_of_app. simpl. right. rewrite H0. now constructor.
Qed.

(** Spawned PIDs are associated with processes. *)
Lemma included_spawn :
  forall O (l : list (Action * PID)) (n n' : Node),
  n -[ l ]ₙ->* n' with O ->
    forall ι : PID, ι ∈ (PIDsOf spawnPIDOf l) ->
      n'.2 !! ι <> None.
Proof.
  intros O l n n' H. induction H; intros.
  * intro. inv H.
  * inv H; simpl in *; try assumption.
    1-3: apply IHclosureNodeSem; try assumption.
    - firstorder; now subst.
    - clear H5. apply elem_of_cons in H1 as [|].
      2: apply IHclosureNodeSem; try assumption.
      subst. apply processes_dont_die with (ι := ι') in H0; auto.
      cbn. by repeat processpool_destruct.
Qed.

(** A non-existing, non-spawned PID which was the target of a send is
    targeted in the ether. *)
Lemma isUsedEther_after_send :
  forall O n n' l, n -[l]ₙ->* n' with O ->
    forall ι,
      ι ∈ (PIDsOf sendPIDOf l) ->
      ι ∉ (PIDsOf spawnPIDOf l) ->
      n.2 !! ι = None ->
      isTargetedEther ι n'.1.
Proof.
  intros O n n' l H. induction H; intros; simpl; auto.
  * inv H.
  * unfold PIDsOf in H2. simpl in H2. apply not_elem_of_app in H2.
    fold (PIDsOf spawnPIDOf l) in *. destruct H2. inv H.
    - simpl in *. apply elem_of_cons in H1 as [|].
      + apply compatibility_of_reductions with (ι := ι0) in H0.
        2: {
          split; simpl. repeat processpool_destruct; congruence.
          subst. unfold isTargetedEther. exists ι. unfold etherAdd.
          break_match_goal; setoid_rewrite lookup_insert; auto.
          all: destruct_decide_eq; by eexists.
        }
        destruct H0.
        destruct H. congruence.
      + apply IHclosureNodeSem; auto.
        repeat processpool_destruct; congruence.
    - simpl in *. apply IHclosureNodeSem; auto.
      repeat processpool_destruct; congruence.
    - simpl in *. apply IHclosureNodeSem; auto.
      2: repeat processpool_destruct; congruence.
      destruct a; simpl in *; auto.
      destruct H6 as [? | [? | ?]]; congruence.
    - simpl in *. clear H8.
      apply IHclosureNodeSem; auto.
      repeat processpool_destruct; try congruence.
      set_solver.
 (* ι0 <> ι0 *)
Qed.

(* Definition comp_pool (Π₁ Π₂ : ProcessPool) : ProcessPool :=
  union Π₁ Π₂. *)

(* Definition comp_ether (e1 e2 : Ether) : Ether :=
  fun ι₁ ι₂ => e1 ι₁ ι₂ ++ e2 ι₁ ι₂.

Definition comp_node (n1 n2 : Node) : Node :=
  (comp_ether n1.1 n2.1, comp_pool n1.2 n2.2).

Notation "n1 ∥∥ n2" := (comp_pool n1 n2) (at level 32, right associativity).

Theorem etherAdd_comp : (* This does not hold *)
  forall eth1 eth2 (ι1 ι2 : PID) (s : Signal),
    comp_ether (etherAdd ι1 ι2 s eth1) eth2 =
    etherAdd ι1 ι2 s (comp_ether eth1 eth2).
Proof.
  intros. unfold etherAdd, comp_ether.
  extensionality source. extensionality dest. unfold update.
  repeat break_match_goal;simpl; eqb_to_eq; auto.
Abort. *)

(* Theorem etherPop_comp :
  forall eth1 eth2 ether' (ι1 ι2 : PID) (s : Signal),
    etherPop ι1 ι2 eth1 = Some (s, ether') ->
    etherPop ι1 ι2 (comp_ether eth1 eth2) = Some (s, comp_ether ether' eth2).
Proof.

Abort. *)

(** `preCompatibleNodes O n1 n2`: the observed PIDs untaken in `n1` are
    untaken in `n2` too. *)
Definition preCompatibleNodes (O : gset PID) (n1 n2 : Node) : Prop :=
  forall ι, ι ∈ O ->
    isUntaken ι n1 -> isUntaken ι n2.

(** `preCompatibleNodes` is transitive. *)
Lemma preCompatibleNodes_trans :
  forall O n1 n2 n3, preCompatibleNodes O n1 n2 -> preCompatibleNodes O n2 n3 ->
    preCompatibleNodes O n1 n3.
Proof.
  unfold preCompatibleNodes. intros.
  apply H in H2; auto.
Qed.

(** `preCompatibleNodes` is reflexive. *)
Lemma preCompatibleNodes_refl :
  forall O n, preCompatibleNodes O n n.
Proof.
  intros. intros ???. assumption.
Qed.

(** * Composition of process pools *)

(** Inserting a process commutes with the union of pools. *)
Corollary par_comp_assoc_pool (Π1 Π2 : ProcessPool) (ι : PID) (p : Process) :
  (ι ↦ p ∥ Π1) ∪ Π2 = ι ↦ p ∥ (Π1 ∪ Π2).
Proof.
  now setoid_rewrite insert_union_l.
Qed.

(** A step is preserved by extending the pool on the right, if the spawned
    PID is not used in the extension. *)
Theorem reduction_is_preserved_by_comp_l :
  forall O Π Π' ether ether' a ι,
    (ether, Π) -[a | ι]ₙ-> (ether', Π') with O ->
    forall (Π2 : ProcessPool),
      (forall ι, spawnPIDOf a = Some ι -> ¬ isUsedPool ι Π2) ->
      (ether, Π ∪ Π2) -[a | ι]ₙ-> (ether', Π' ∪ Π2) with O.
Proof.
  intros. inv H; cbn.
  * do 2 rewrite par_comp_assoc_pool. now apply n_send.
  * do 2 rewrite par_comp_assoc_pool. now apply n_arrive.
  * do 2 rewrite par_comp_assoc_pool. now apply n_other.
  * do 3 rewrite par_comp_assoc_pool. econstructor; eauto.
    specialize (H0 _ eq_refl).
    (* TODO: separate thm *)
    intro. destruct H.
    {
      assert (ι <> ι'). {
        intro. subst.
        apply H7. left. setoid_rewrite lookup_insert.
        by destruct_decide_eq.
      }
      setoid_rewrite lookup_insert_ne in H. 2: auto.
      setoid_rewrite lookup_union in H. apply H.
      apply union_None. split.
      * clear -H7 H1. unfold isUsedPool in H7.
        apply eq_None_ne_Some_2. intros. intro. apply H7. left. intro.
        setoid_rewrite lookup_insert_ne in H0. 2: auto.
        by setoid_rewrite H0 in H.
      * clear -H1 H0. unfold isUsedPool in H0.
        apply eq_None_ne_Some_2. intros. intro. apply H0. left. intro.
        by setoid_rewrite H2 in H.
    }
    {
      destruct_hyps.
      assert (x <> ι). {
        intro. subst.
        setoid_rewrite lookup_insert in H. inv H.
        apply H7. right. do 2 eexists. split.
        setoid_rewrite lookup_insert. rewrite decide_True.
        destruct_decide_eq. eassumption. reflexivity. assumption.
      }
      setoid_rewrite lookup_insert_ne in H. 2: lia.
      setoid_rewrite lookup_union in H. setoid_rewrite union_Some in H.
      destruct H.
      * apply H7. right. exists x, x0.
        setoid_rewrite lookup_insert_ne. 2: lia. split; assumption.
      * apply H0. right. exists x, x0. destruct_hyps. split; assumption.
    }
Qed.

(** A PID used in the union of two pools is used in one of them. *)
Theorem isUsedPool_union_1 :
  forall Π Π' ι, isUsedPool ι (Π ∪ Π') -> isUsedPool ι Π \/ isUsedPool ι Π'.
Proof.
  intros.
  destruct H.
  * setoid_rewrite lookup_union in H.
    apply not_eq_None_Some in H. apply union_is_Some in H. destruct H.
    - left. left. intro. inv H. by setoid_rewrite H0 in H1.
    - right. left. intro. inv H. by setoid_rewrite H0 in H1.
  * destruct_hyps. setoid_rewrite lookup_union in H.
    apply union_Some in H. intuition.
    - left. right. do 2 eexists; split; eassumption.
    - right. right. do 2 eexists; split; eassumption.
Qed.

(*
TODO: strengthen premise 'dom Π2 ⊆ O' to 'PIDsOf Π2 ⊆ O'
Theorem reduction_is_preserved_by_comp_l_with_O :
  forall O Π Π' ether ether' a ι,
    (ether, Π) -[a | ι]ₙ-> (ether', Π') with O ->
    forall (Π2 : ProcessPool),
      dom Π2 ⊆ O ->
      (ether, Π ∪ Π2) -[a | ι]ₙ-> (ether', Π' ∪ Π2) with O.
Proof.
  intros. inv H; cbn.
  * do 2 rewrite par_comp_assoc_pool. now apply n_send.
  * do 2 rewrite par_comp_assoc_pool. now apply n_arrive.
  * do 2 rewrite par_comp_assoc_pool. now apply n_other.
  * do 3 rewrite par_comp_assoc_pool. econstructor; eauto.
    intro. apply isUsedPool_insert_1 in H. destruct_or!.
    - setoid_rewrite delete_union in H.
      apply isUsedPool_union_1 in H. destruct H.
      + apply H7. apply isUsedPool_insert_2. by left.
      + 
    -
    -
    (* set_solver. *)
Abort.

Corollary reductions_are_preserved_by_comp_l_with_O : 
  forall O Π Π' ether ether' l,
    (ether, Π) -[l]ₙ->* (ether', Π') with O ->
    forall (Π2 : ProcessPool),
      dom Π2 ⊆ O ->
      (ether, Π ∪ Π2) -[l]ₙ->* (ether', Π' ∪ Π2) with O.
Proof.
  intros ???????. dependent induction H; intros.
  * constructor.
  * destruct n'. specialize (IHclosureNodeSem _ _ _ _ JMeq_refl JMeq_refl).
    eapply reduction_is_preserved_by_comp_l_with_O with (Π2 := Π2) in H.
    2: { assumption. }
    econstructor; eauto.
Qed.

Theorem reduction_is_preserved_by_comp_r_with_O :
  forall O Π Π' ether ether' a ι,
    (ether, Π) -[a | ι]ₙ-> (ether', Π') with O ->
    forall (Π2 : ProcessPool),
      ι ∉ dom Π2 ->
      dom Π2 ⊆ O ->
      (ether, Π2 ∪ Π) -[a | ι]ₙ-> (ether', Π2 ∪ Π') with O.
Proof.
  intros. inv H; cbn.
  * setoid_rewrite <- insert_union_r.
    2-3: now apply not_elem_of_dom. now apply n_send.
  * setoid_rewrite <- insert_union_r.
    2-3: now apply not_elem_of_dom. now apply n_arrive.
  * setoid_rewrite <- insert_union_r.
    2-3: now apply not_elem_of_dom. now apply n_other.
  * setoid_rewrite <- insert_union_r. setoid_rewrite <- insert_union_r.
    2-4: try now apply not_elem_of_dom.
    2: { apply not_elem_of_dom. set_solver. }
    econstructor; eauto.
    admit. (* TODO: technical, create not_isUsedPool_insert_2! *)
Abort.

Corollary reductions_are_preserved_by_comp_r_with_O : 
  forall O Π Π' ether ether' l,
    (ether, Π) -[l]ₙ->* (ether', Π') with O ->
    forall (Π2 : ProcessPool),
      (forall ι, ι  ∈ (map snd l) -> ¬isUsedPool ι Π2) ->
      dom Π2 ⊆ O ->
      (ether, Π2 ∪ Π) -[l]ₙ->* (ether', Π2 ∪ Π') with O.
Proof.
  intros ????????. dependent induction H; intros.
  * constructor.
  * destruct n'. specialize (IHclosureNodeSem _ _ _ _ JMeq_refl JMeq_refl).
    eapply reduction_is_preserved_by_comp_r_with_O with (Π2 := Π2) in H.
    2: {
      intro. apply (H1 ι). set_solver.
      left. intro. by apply not_elem_of_dom in H4.
    }
    2: { assumption. }
    econstructor; eauto.
    apply IHclosureNodeSem.
    intros. apply H1. cbn. now right.
    intros. apply H2.
Qed.

*)

(** Reduction sequences are preserved by extending the pool on the right, if
    the spawned PIDs are not used in the extension. *)
Corollary reductions_are_preserved_by_comp_l :
  forall O Π Π' ether ether' l,
    (ether, Π) -[l]ₙ->* (ether', Π') with O ->
    forall (Π2 : ProcessPool),
      (forall ι, ι ∈ (PIDsOf spawnPIDOf l) -> ¬isUsedPool ι Π2) ->
      (ether, Π ∪ Π2) -[l]ₙ->* (ether', Π' ∪ Π2) with O.
Proof.
  intros. revert Π Π' ether ether' H Π2 H0. induction l; simpl; intros.
  {
    inv H. constructor.
  }
  {
    inv H. destruct n'. eapply IHl in H6.
    2: {
      intros. apply H0. set_solver.
    }
    econstructor. 2: eassumption.
    simpl in *. clear H6.
    apply reduction_is_preserved_by_comp_l; try assumption.
    intros. apply H0.
    rewrite H. set_solver.
  }
Qed.

(** A step is preserved by extending the pool on the left, if the acting
    process is not in the extension, and the spawned PID is not used in
    it. *)
Theorem reduction_is_preserved_by_comp_r :
  forall O Π Π' ether ether' a ι,
    (ether, Π) -[a | ι]ₙ-> (ether', Π') with O ->
    forall (Π2 : ProcessPool),
      ι ∉ dom Π2 ->
      (forall ι, spawnPIDOf a = Some ι -> ¬isUsedPool ι Π2) ->
      (ether, Π2 ∪ Π) -[a | ι]ₙ-> (ether', Π2 ∪ Π') with O.
Proof.
  intros. inv H; cbn.
  * setoid_rewrite <- insert_union_r.
    2-3: now apply not_elem_of_dom. now apply n_send.
  * setoid_rewrite <- insert_union_r.
    2-3: now apply not_elem_of_dom. now apply n_arrive.
  * setoid_rewrite <- insert_union_r.
    2-3: now apply not_elem_of_dom. now apply n_other.
  * setoid_rewrite <- insert_union_r. setoid_rewrite <- insert_union_r.
    2-4: try now apply not_elem_of_dom.
    2: { specialize (H1 _ eq_refl). 
         apply eq_None_ne_Some_2. intros ? ?. apply H1. left.
         intro. by setoid_rewrite H in H2.
       }
    econstructor; eauto.
    specialize (H1 _ eq_refl).
    intro. destruct H.
    {
      assert (ι <> ι'). {
        intro. subst.
        apply H8. left. setoid_rewrite lookup_insert. by destruct_decide_eq.
      }
      setoid_rewrite lookup_insert_ne in H. 2: lia.
      setoid_rewrite lookup_union in H. apply H.
      apply union_None. split.
      * clear -H2 H1. rename H1 into H8. unfold isUsedPool in H8.
        apply eq_None_ne_Some_2. intros. intro. apply H8. left. intro.
        by setoid_rewrite H0 in H.
      * clear -H2 H8. rename H8 into H0. unfold isUsedPool in H0.
        apply eq_None_ne_Some_2. intros. intro. apply H0. left. intro.
        setoid_rewrite lookup_insert_ne in H1. 2: lia.
        by setoid_rewrite H1 in H.
    }
    {
      destruct_hyps.
      assert (x <> ι). {
        intro. subst.
        setoid_rewrite lookup_insert in H. inv H.
        apply H8. right. do 2 eexists. split.
        setoid_rewrite lookup_insert. rewrite decide_True in H4 by reflexivity.
        injection H4 as <-. rewrite decide_True. reflexivity. reflexivity.
        exact H2.
      }
      setoid_rewrite lookup_insert_ne in H. 2: lia.
      setoid_rewrite lookup_union in H. setoid_rewrite union_Some in H.
      destruct H.
      * apply H1. right. exists x, x0. split; assumption.
      * apply H8. right. exists x, x0. destruct_hyps.
        setoid_rewrite lookup_insert_ne. 2: lia. split; assumption.
    }
Qed.

(** Reduction sequences are preserved by extending the pool on the left, if
    the acting processes are not in the extension, and the spawned PIDs are
    not used in it. *)
Corollary reductions_are_preserved_by_comp_r :
  forall O Π Π' ether ether' l,
    (ether, Π) -[l]ₙ->* (ether', Π') with O ->
    forall (Π2 : ProcessPool),
      (forall ι, ι ∈ (map snd l) -> ι ∉ dom Π2) ->
      (forall ι, ι ∈ (PIDsOf spawnPIDOf l) -> ¬isUsedPool ι Π2) ->
      (ether, Π2 ∪ Π) -[l]ₙ->* (ether', Π2 ∪ Π') with O.
Proof.
  intros. revert Π Π' ether ether' H Π2 H0 H1. induction l; simpl; intros.
  {
    inv H. constructor.
  }
  {
    inv H. destruct n'. eapply IHl in H7.
    2: {
      intros. apply H0. set_solver.
    }
    2: {
      intros. apply H1. set_solver.
    }
    econstructor. 2: eassumption.
    simpl in *. clear H7.
    apply reduction_is_preserved_by_comp_r; try assumption.
    * intros. apply H0. set_solver.
    * intros. apply H1. rewrite H. set_solver.
  }
Qed.

(** * PID renaming in nodes *)

(** PID renaming commutes with adding a signal to the ether. *)
Lemma etherAdd_renamePID :
  forall ιs ιd s from to eth,
    renamePIDEther from to (etherAdd ιs ιd s eth) =
    etherAdd (renamePIDPID_sym from to ιs) (renamePIDPID_sym from to ιd) (renamePIDSignal from to s) (renamePIDEther from to eth).
Proof.
  intros. unfold etherAdd. unfold renamePIDEther at 2.
  replace (renamePIDPID_sym from to ιs, renamePIDPID_sym from to ιd) with
    (prod_map (renamePIDPID_sym from to) (renamePIDPID_sym from to) (ιs,ιd))
    by reflexivity.
  setoid_rewrite lookup_kmap; auto.
  setoid_rewrite lookup_fmap. case_match.
  * setoid_rewrite H. unfold renamePIDEther.
    setoid_rewrite <- kmap_insert; auto. f_equal.
    setoid_rewrite fmap_insert. by rewrite map_app.
  * setoid_rewrite H. unfold renamePIDEther.
    setoid_rewrite <- kmap_insert; auto. f_equal.
    by setoid_rewrite fmap_insert.
Qed.

(** PID renaming commutes with popping a signal from the ether. *)
Lemma etherPop_renamePID :
  forall eth ιs ιd from to,
  fmap (prod_map (renamePIDSignal from to) (renamePIDEther from to)) (etherPop ιs ιd eth)
  = etherPop (renamePIDPID_sym from to ιs) (renamePIDPID_sym from to ιd) eth .[ from ⇔ to ]ₑ.
Proof.
  unfold etherPop, renamePIDEther. intros.
  replace (renamePIDPID_sym from to ιs, renamePIDPID_sym from to ιd) with
    (prod_map (renamePIDPID_sym from to) (renamePIDPID_sym from to) (ιs,ιd))
    by reflexivity.
  setoid_rewrite lookup_kmap; auto.
  setoid_rewrite lookup_fmap. case_match; setoid_rewrite H; simpl. 2: by reflexivity.
  destruct l; try reflexivity.
  simpl. do 2 f_equal.
  replace (renamePIDPID_sym from to ιs, renamePIDPID_sym from to ιd) with
    (prod_map (renamePIDPID_sym from to) (renamePIDPID_sym from to) (ιs,ιd))
    by reflexivity.
  setoid_rewrite <- kmap_insert; auto. f_equal.
  by setoid_rewrite fmap_insert.
Qed.

(** PID renaming commutes with inserting a process into a pool. *)
Lemma pool_insert_renamePID :
  forall prs ι p from to,
  (ι ↦ p ∥ prs) .[ from ⇔ to ]ₚₚ =
  renamePIDPID_sym from to ι ↦ renamePIDProc from to p ∥ prs .[from ⇔ to]ₚₚ.
Proof.
  intros. unfold renamePIDPool.
  setoid_rewrite <- kmap_insert; auto.
  f_equal. by setoid_rewrite fmap_insert.
Qed.

(** `p` is targeted in the ether iff `p'` is targeted after swapping
    them. *)
Lemma isTargetedEther_rename_new :
  forall p p' eth, isTargetedEther p eth <-> isTargetedEther p' (renamePIDEther p p' eth).
Proof.
  split; intro.
  * unfold renamePIDEther, isTargetedEther in *.
    destruct H as [ιs [l H]].
    exists (renamePIDPID_sym p p' ιs), (map (renamePIDSignal p p') l).
    apply lookup_kmap_Some. auto.
    exists (ιs, p). split. cbn. unfold renamePIDPID_sym. rewrite Nat.eqb_refl. reflexivity.
    rewrite lookup_fmap. setoid_rewrite H. reflexivity.
  * unfold renamePIDEther, isTargetedEther in *.
    destruct H as [ιs [l H]].
    apply lookup_kmap_Some in H as [[ιs0 p0] [Eq H]]. inv Eq. 2: auto.
    rewrite lookup_fmap in H.
    destruct (eth !! (ιs0, p0)) eqn:P; setoid_rewrite P in H.
    2: simpl in H;congruence.
    inv H.
    destruct (decide (p0 = p)).
    - subst. do 2 eexists. eassumption.
    - unfold renamePIDPID_sym in H2. apply Nat.eqb_neq in n. rewrite n in H2.
      break_match_hyp; eqb_to_eq; subst.
      + congruence.
      + congruence.
Qed.

(** `p'` is targeted in the ether iff `p` is targeted after swapping
    them. *)
Lemma isTargetedEther_rename_old :
  forall p p' eth, isTargetedEther p' eth <-> isTargetedEther p (renamePIDEther p p' eth).
Proof.
  split; intro.
  * unfold renamePIDEther, isTargetedEther in *.
    destruct H as [ιs [l H]].
    exists (renamePIDPID_sym p p' ιs), (map (renamePIDSignal p p') l).
    apply lookup_kmap_Some. auto.
    exists (ιs, p'). split. cbn. unfold renamePIDPID_sym. rewrite Nat.eqb_refl.
    destruct (p' =? p) eqn:P. 2: reflexivity. eqb_to_eq. now subst.
    rewrite lookup_fmap. setoid_rewrite H. reflexivity.
  * unfold renamePIDEther, isTargetedEther in *.
    destruct H as [ιs [l H]].
    apply lookup_kmap_Some in H as [[ιs0 p0] [Eq H]]. inv Eq. 2: auto.
    rewrite lookup_fmap in H.
    destruct (eth !! (ιs0, p0)) eqn:P; setoid_rewrite P in H.
    2: simpl in H;congruence.
    inv H.
    destruct (decide (p0 = p')).
    - subst. do 2 eexists. eassumption.
    - unfold renamePIDPID_sym in H2. apply Nat.eqb_neq in n. rewrite n in H2.
      break_match_hyp; eqb_to_eq; subst.
      + congruence.
      + congruence.
Qed.

(** PID renaming does not change whether other PIDs are targeted in the
    ether. *)
Lemma isTargetedEther_rename_neq :
  forall ι p p' eth,
    ι <> p -> ι <> p' ->
    isTargetedEther ι eth <-> isTargetedEther ι (renamePIDEther p p' eth).
Proof.
  split; intro.
  * unfold renamePIDEther, isTargetedEther in *.
    destruct H1 as [ιs [l H1]].
    exists (renamePIDPID_sym p p' ιs), (map (renamePIDSignal p p') l).
    apply lookup_kmap_Some. auto.
    exists (ιs, ι). split. cbn. unfold renamePIDPID_sym. apply Nat.eqb_neq in H, H0.
    now rewrite H, H0.
    rewrite lookup_fmap. setoid_rewrite H1. reflexivity.
  * unfold renamePIDEther, isTargetedEther in *.
    destruct H1 as [ιs [l H1]].
    apply lookup_kmap_Some in H1 as [[ιs0 p0] [Eq H1]]. inv Eq. 2: auto.
    rewrite lookup_fmap in H1.
    destruct (eth !! (ιs0, p0)) eqn:P; setoid_rewrite P in H1.
    2: simpl in H1;congruence.
    inv H1.
    unfold renamePIDPID_sym in *. repeat case_match; eqb_to_eq; subst; try congruence.
    do 2 eexists. eassumption.
Qed.

(** A PID is targeted in the ether iff its swapped version is targeted in
    the renamed ether. *)
Corollary isTargetedEther_renamePID :
  forall ι eth from to,
    isTargetedEther ι eth <-> isTargetedEther (renamePIDPID_sym from to ι) (renamePIDEther from to eth).
Proof.
  intros. split; intro.
  {
    unfold renamePIDPID_sym. case_match; eqb_to_eq.
    2: case_match; eqb_to_eq.
    * subst. by apply isTargetedEther_rename_new.
    * subst. by apply isTargetedEther_rename_old.
    * subst. by apply isTargetedEther_rename_neq.
  }
  {
    unfold renamePIDPID_sym in H. case_match; eqb_to_eq.
    2: case_match; eqb_to_eq.
    * subst. by apply isTargetedEther_rename_new in H.
    * subst. by apply isTargetedEther_rename_old in H.
    * subst. by apply isTargetedEther_rename_neq in H.
  }
Qed.

(** PID renaming does not change whether other PIDs are used in a pool. *)
Lemma isUsedPool_rename_neq :
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
      - destruct x0. 1: rewrite usedPIDsLiveProc_rename; destruct decide; set_solver.
        by apply usedPIDsDeadProc_rename_neq.
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
      - destruct p0. 1: rewrite usedPIDsLiveProc_rename in H2; destruct decide; set_solver.
        by apply usedPIDsDeadProc_rename_neq in H2.
  }
Qed.

(** Renaming a PID to itself leaves an ether unchanged. *)
Corollary renamePID_id_ether :
  forall eth p, renamePIDEther p p eth = eth.
Proof.
  intros. unfold renamePIDEther.
  replace (prod_map _ _) with (id : PID * PID -> PID * PID).
  2: { extensionality x. unfold prod_map. destruct x.
       renamePIDPID_sym_case_match; try reflexivity. cbn in *. by inv H0. }
  replace (kmap id) with (id : Ether -> Ether). 2: {
    extensionality x. apply map_eq. intros.
    replace i with (id i) at 2 by reflexivity.
    setoid_rewrite lookup_kmap; auto.
  }
  unfold id.
  rewrite <- (map_fmap_id eth) at 2.
  apply map_fmap_ext. intros. unfold id.
  rewrite <- (map_id x) at 2. f_equal.
  extensionality s. by apply renamePID_id_sig.
Qed.

(** Renaming a PID to itself leaves a pool unchanged. *)
Corollary renamePID_id_pool :
  forall Π p, renamePIDPool p p Π = Π.
Proof.
  intros. unfold renamePIDPool.
  replace (renamePIDPID_sym _ _) with (id : PID -> PID).
  2: { extensionality x. renamePIDPID_sym_case_match; try reflexivity. }
  replace (kmap id) with (id : ProcessPool -> ProcessPool). 2: {
    extensionality x. apply map_eq. intros.
    replace i with (id i) at 2 by reflexivity.
    setoid_rewrite lookup_kmap; auto.
  }
  unfold id.
  rewrite <- (map_fmap_id Π) at 2.
  apply map_fmap_ext. intros. unfold id.
  by apply renamePID_id_proc.
Qed.

(** Renaming between PIDs that do not appear in an ether leaves it
    unchanged. *)
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
    apply isNotUsed_renamePID_sig.
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
      by setoid_rewrite H.
    * apply not_appearsEther_alt in H0; destruct_hyps.
      by setoid_rewrite H0.
  }
Qed.

(** Renaming between PIDs that are not used in a pool leaves it
    unchanged. *)
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
    * intro. apply H. right. do 2 eexists. split. exact P. assumption.
    * intro. apply H0. right. do 2 eexists. split. exact P. assumption.
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

(** If the renamed PID `p` is used in the renamed pool, then the new PID
    `p'` was used in the original pool. *)
Lemma isUsedPool_rename_old :
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
    destruct p0. 1: rewrite usedPIDsLiveProc_rename in H0; destruct decide; set_solver.
    apply usedPIDsDeadProc_rename_old in H0. right.
    exists x1, (inr d). by split.
Qed.

(** If `p` is used in a pool, then `p'` is used in the renamed pool. *)
Lemma isUsedPool_rename_new_1 :
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
    - destruct x0. 1: rewrite usedPIDsLiveProc_rename; destruct decide; set_solver.
      by apply usedPIDsDeadProc_rename_new_1.
Qed.

(** If `p'` is fresh in a pool, and it is used in the renamed pool, then `p`
    was used in the original pool. *)
Lemma isUsedPool_rename_new_2 :
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

(** If a PID is used in a pool after removing a process from it, then it was
    used in the pool before the removal as well. *)
Lemma isUsedPool_remove_1 :
  forall Π ι ι',
    isUsedPool ι (Π -- ι') ->
    isUsedPool ι Π.
Proof.
  intros. destruct H.
  * left. destruct (decide (ι = ι')).
    {
      intro. apply H. subst.  setoid_rewrite lookup_delete. by destruct_decide_eq.
    }
    intro. apply H.
    apply lookup_delete_None. by right.
  * destruct_hyps.
    destruct (decide (x = ι')).
    {
      subst. setoid_rewrite lookup_delete in H. by destruct_decide_eq.
    }
    right.
    exists x, x0. split. 2: assumption.
    apply lookup_delete_Some in H. apply H.
Qed.

(** A PID used in a pool stays used after removing another process which
    does not use it. *)
Lemma isUsedPool_remove_2 :
  forall Π ι ι',
    isUsedPool ι Π ->
    ι' <> ι ->
    (forall p, Π !! ι' = Some p -> ι ∉ usedPIDsProc p) ->
    isUsedPool ι (Π -- ι').
Proof.
  intros. destruct H.
  * left. 
    intro.
    apply lookup_delete_None in H2. destruct H2.
    congruence.
    by setoid_rewrite H2 in H.
  * destruct_hyps.
    destruct (decide (x = ι')).
    {
      subst. by apply H1 in H.
    }
    right.
    exists x, x0. split. 2: assumption.
    apply lookup_delete_Some. split; auto.
Qed.

(** PID renaming does not change whether other PIDs appear in the ether. *)
Lemma appearsEther_rename_neq :
  ∀ (ι p p' : PID) (eth : Ether),
    ι ≠ p → ι ≠ p' → appearsEther ι eth ↔ appearsEther ι eth .[ p ⇔ p' ]ₑ.
Proof.
  intros. split; intro.
  {
    destruct H1. 2: destruct H1.
    * destruct H1; destruct_hyps.
      left. exists (renamePIDPID_sym p p' x).
      replace ι with (renamePIDPID_sym p p' ι) by renamePIDPID_sym_case_match.
      eexists.
      unfold renamePIDEther.
      setoid_rewrite lookup_kmap_Some; auto.
      exists (x, ι). split. reflexivity.
      setoid_rewrite lookup_fmap. setoid_rewrite H1. reflexivity.
    * destruct_hyps.
      right. left.
      exists (renamePIDPID_sym p p' x).
      intro. setoid_rewrite lookup_kmap_None in H2; auto.
      specialize (H2 (ι, x)).
      assert (renamePIDPID_sym p p' ι = ι) by renamePIDPID_sym_case_match.
      cbn in H2. rewrite H3 in H2. specialize (H2 eq_refl).
      setoid_rewrite lookup_fmap in H2.
      destruct (eth !! _) eqn:P. 2: congruence.
      by setoid_rewrite P in H2.
    * destruct_hyps.
      right. right. exists (renamePIDPID_sym p p' x), (renamePIDPID_sym p p' x0).
      eexists. split.
      - unfold renamePIDEther. setoid_rewrite lookup_kmap_Some; auto.
        exists (x, x0). split. reflexivity.
        setoid_rewrite lookup_fmap. by setoid_rewrite H1.
      - apply elem_of_flat_union in H2. destruct_hyps.
        apply elem_of_flat_union. eexists.
        split. apply elem_of_map_iff. eexists. split. reflexivity. exact H2.
        rewrite usedPIDsSig_rename. destruct decide; set_solver.
  }
  {
    destruct H1. 2: destruct H1.
    * destruct H1; destruct_hyps.
      unfold renamePIDEther in H1.
      setoid_rewrite lookup_kmap_Some in H1; auto; destruct_hyps.
      destruct x1; inv H1.
      renamePIDPID_sym_case_match_hyp H0; renamePIDPID_sym_case_match_hyp H.
      setoid_rewrite lookup_fmap in H2. renamePIDPID_sym_case_match.
      destruct (eth !! (n, n0)) eqn:P; setoid_rewrite P in H2; inv H2.
      left. by do 2 eexists.
    * destruct_hyps.
      unfold renamePIDEther in H1.
      replace ι with (renamePIDPID_sym p p' ι) in H1 by renamePIDPID_sym_case_match.
      (* TODO: boiler plate, these separations are solved in a very similar way *)
      destruct (decide (x = p)).
      {
        subst. replace (_, p) with (prod_map (renamePIDPID_sym p p') (renamePIDPID_sym p p') (ι, p')) in H1 by (cbn; by renamePIDPID_sym_case_match).
        setoid_rewrite lookup_kmap in H1; auto; destruct_hyps.
        setoid_rewrite lookup_fmap in H1.
        destruct (eth !! (ι, p')) eqn:P; setoid_rewrite P in H1; cbn in H1; try congruence.
        right. left.
        exists p'. intro. by setoid_rewrite P in H2.
      }
      destruct (decide (x = p')).
      {
        subst. replace (_, p') with (prod_map (renamePIDPID_sym p p') (renamePIDPID_sym p p') (ι, p)) in H1 by (cbn; by renamePIDPID_sym_case_match).
        setoid_rewrite lookup_kmap in H1; auto; destruct_hyps.
        setoid_rewrite lookup_fmap in H1.
        destruct (eth !! (ι, p)) eqn:P; setoid_rewrite P in H1; cbn in H1; try congruence.
        right. left.
        exists p. intro. by setoid_rewrite P in H2.
      }
      replace (_, x) with (prod_map (renamePIDPID_sym p p') (renamePIDPID_sym p p') (ι, x)) in H1 by (cbn; by renamePIDPID_sym_case_match).
      setoid_rewrite lookup_kmap in H1; auto; destruct_hyps.
      setoid_rewrite lookup_fmap in H1.
      destruct (eth !! (ι, x)) eqn:P; setoid_rewrite P in H1; cbn in H1; try congruence.
      right. left.
      exists x. intro. by setoid_rewrite P in H2.
    * destruct_hyps.
      setoid_rewrite lookup_kmap_Some in H1; auto.
      destruct_hyps. destruct x2. inv H1.
      setoid_rewrite lookup_fmap in H3.
      destruct (eth !! (n, n0)) eqn:P; setoid_rewrite P in H3; cbn in H3; try congruence.
      inv H3.
      right. right.
      do 3 eexists. split.
      exact P.
      apply elem_of_flat_union in H2. destruct_hyps.
      apply elem_of_map_iff in H1. destruct_hyps. subst x.
      rewrite usedPIDsSig_rename in H2.
      apply elem_of_flat_union. exists x0. split. assumption.
      destruct decide; set_solver.
  }
Qed.

(** If the renamed PID `p` appears in the renamed ether, then the new PID
    `p'` appeared in the original ether. *)
Lemma appearsEther_rename_old :
  ∀ (p p' : PID) (eth : Ether),
    appearsEther p eth .[ p ⇔ p' ]ₑ -> appearsEther p' eth.
Proof.
  intros.
  destruct (decide (p = p')).
  {
    subst. by rewrite renamePID_id_ether in H.
  }
  destruct H. 2: destruct H.
  * destruct H. destruct_hyps.
    left. setoid_rewrite lookup_kmap_Some in H; auto.
    destruct_hyps. destruct x1; inv H.
    setoid_rewrite lookup_fmap in H0.
    renamePIDPID_sym_case_match_hyp H3.
    destruct (eth !! (n0, p')) eqn:P; setoid_rewrite P in H0.
    exists n0. eexists. exact P. by simpl in H0.
  * destruct_hyps.
    replace (p, x) with (prod_map (renamePIDPID_sym p p') (renamePIDPID_sym p p') (p', renamePIDPID_sym p' p x)) in H.
    2: cbn; renamePIDPID_sym_case_match; try reflexivity.
    setoid_rewrite lookup_kmap in H; auto.
    setoid_rewrite lookup_fmap in H. right. left.
    destruct (eth !! (p', renamePIDPID_sym p' p x)) eqn:P; setoid_rewrite P in H; simpl in H; try congruence.
    exists (renamePIDPID_sym p' p x). intro. congruence.
  * destruct_hyps.
    setoid_rewrite lookup_kmap_Some in H; auto.
    destruct_hyps. destruct x2. inv H.
    setoid_rewrite lookup_fmap in H1.
    destruct (eth !! (n0, n1)) eqn:P; setoid_rewrite P in H1; cbn in H1; try congruence.
    inv H1.
    right. right.
    do 3 eexists. split.
    exact P.
    apply elem_of_flat_union in H0. destruct_hyps.
    apply elem_of_map_iff in H. destruct_hyps. subst x.
    rewrite usedPIDsSig_rename in H0.
    apply elem_of_flat_union. exists x0. split. assumption.
    destruct decide; set_solver.
Qed.

(** If `p` appears in the ether, then `p'` appears in the renamed ether. *)
Lemma appearsEther_rename_new_1 :
  ∀ (p p' : PID) (eth : Ether),
    appearsEther p eth -> appearsEther p' eth .[ p ⇔ p' ]ₑ.
Proof.
  intros.
  destruct H. 2: destruct H.
  * destruct H; destruct_hyps.
    left. exists (renamePIDPID_sym p p' x).
    replace p' with (renamePIDPID_sym p p' p) at 2 by renamePIDPID_sym_case_match.
    eexists.
    unfold renamePIDEther.
    setoid_rewrite lookup_kmap_Some; auto.
    exists (x, p). split. cbn; by renamePIDPID_sym_case_match.
    setoid_rewrite lookup_fmap. setoid_rewrite H. reflexivity.
  * destruct_hyps.
    right. left.
    exists (renamePIDPID_sym p p' x).
    intro. setoid_rewrite lookup_kmap_None in H0; auto.
    specialize (H0 (p, x)).
    assert (renamePIDPID_sym p p' p = p') by renamePIDPID_sym_case_match.
    cbn in H0. rewrite H1 in H0. specialize (H0 eq_refl).
    setoid_rewrite lookup_fmap in H0.
    destruct (eth !! _) eqn:P. 2: congruence.
    by setoid_rewrite P in H0.
  * destruct_hyps.
    right. right. exists (renamePIDPID_sym p p' x), (renamePIDPID_sym p p' x0).
    eexists. split.
    - unfold renamePIDEther. setoid_rewrite lookup_kmap_Some; auto.
      exists (x, x0). split. reflexivity.
      setoid_rewrite lookup_fmap. by setoid_rewrite H.
    - apply elem_of_flat_union in H0. destruct_hyps.
      apply elem_of_flat_union. eexists.
      split. apply elem_of_map_iff. eexists. split. reflexivity. exact H0.
      rewrite usedPIDsSig_rename. destruct decide; set_solver.
Qed.

(** If `p'` does not appear in the ether, but it appears in the renamed
    ether, then `p` appeared in the original ether. *)
Lemma appearsEther_rename_new_2 :
  ∀ (p p' : PID) (eth : Ether),
    ¬appearsEther p' eth ->
    appearsEther p' eth .[ p ⇔ p' ]ₑ -> appearsEther p eth.
Proof.
  intros.
  destruct H0. 2: destruct H0.
  * destruct H0. destruct_hyps.
    left. setoid_rewrite lookup_kmap_Some in H0; auto.
    destruct_hyps. destruct x1; inv H0.
    setoid_rewrite lookup_fmap in H1.
    renamePIDPID_sym_case_match_hyp H4.
    destruct (eth !! (n, p)) eqn:P; setoid_rewrite P in H1; inv H1.
    exists n. eexists. exact P.
  * destruct_hyps.
    replace (p', x) with (prod_map (renamePIDPID_sym p p') (renamePIDPID_sym p p') (p, renamePIDPID_sym p' p x)) in H0.
    2: cbn; renamePIDPID_sym_case_match; try reflexivity.
    setoid_rewrite lookup_kmap in H0; auto.
    setoid_rewrite lookup_fmap in H0. right. left.
    destruct (eth !! (p, renamePIDPID_sym p' p x)) eqn:P; setoid_rewrite P in H0; simpl in H0; try congruence.
    exists (renamePIDPID_sym p' p x). intro. congruence.
  * destruct_hyps.
    setoid_rewrite lookup_kmap_Some in H0; auto.
    destruct_hyps. destruct x2. inv H0.
    setoid_rewrite lookup_fmap in H2.
    destruct (eth !! (n, n0)) eqn:P; setoid_rewrite P in H2; cbn in H2; try congruence.
    inv H2.
    right. right.
    do 3 eexists. split.
    exact P.
    apply elem_of_flat_union in H1. destruct_hyps.
    apply elem_of_map_iff in H0. destruct_hyps. subst x.
    rewrite usedPIDsSig_rename in H1.
    apply elem_of_flat_union. exists x0. split. assumption.
    destruct decide. set_solver.
    (* additional hypothesis is used here *)
    exfalso. apply H.
    right. right. do 3 eexists. split. eassumption.
    apply elem_of_flat_union. eexists. split. eassumption.
    set_solver.
Qed.

(** The steps of the node semantics are preserved by renaming to a fresh
    PID (one which is used neither by the node, nor by the action, and which
    is not observed). *)
Theorem renamePID_is_preserved :
  forall O eth eth' Π Π' a ι,
    (eth, Π) -[a | ι]ₙ-> (eth', Π') with O ->
    forall from to,
      to ∉ (usedPIDsAct a) ->
      ¬ appearsEther to eth ->
      ¬ isUsedPool to Π ->
      to ∉ O ->
      (renamePIDEther from to eth, renamePIDPool from to Π)
    -[renamePIDAct from to a | renamePIDPID_sym from to ι]ₙ->
      (renamePIDEther from to eth', renamePIDPool from to Π') with O.
Proof.
  intros ??????? H ?? H0 H1 H2 HO. inv H.
  * simpl in *. rewrite etherAdd_renamePID.
    do 2 rewrite pool_insert_renamePID.
    rewrite <- renamePIDPID_sym_neq; auto. rewrite <- renamePIDPID_sym_neq; auto. apply n_send.
    rewrite renamePIDPID_sym_neq, renamePIDPID_sym_neq; auto.
    eapply renamePID_is_preserved_local in H7. exact H7.
    all: try assumption.
    intro. apply H2. apply isUsedPool_insert_2. right. by right.
    all: set_solver.
  * simpl in *. rewrite <- renamePIDPID_sym_neq, <- renamePIDPID_sym_neq; auto.
    do 2 rewrite pool_insert_renamePID.
    constructor.
    2: {
      eapply renamePID_is_preserved_local in H10.
      rewrite renamePIDPID_sym_neq, renamePIDPID_sym_neq; auto. exact H10.
      all: auto.
      1-2: set_solver.
      intro. apply H2. apply isUsedPool_insert_2. right. subst. by right.
    }
    rewrite <- etherPop_renamePID, H8. by simpl.
    all: set_solver.
  * simpl in *. do 2 rewrite pool_insert_renamePID.
    constructor.
    eapply renamePID_is_preserved_local in H8. exact H8.
    all: auto.
    intro. apply H2. apply isUsedPool_insert_2. right. by right.
    simpl in *. destruct_or!; subst; simpl; intuition.
    right. left. rewrite renamePIDPID_sym_neq; auto.
    intro. apply H2. apply isUsedPool_insert_2. right. by left.
  * simpl in *. do 3 rewrite pool_insert_renamePID.
    rewrite <- renamePIDPID_sym_neq; auto. simpl.
    replace (set_map (renamePIDPID from to) (if link_flag then {[ι]} else ∅)) with
      (if link_flag then {[renamePIDPID_sym from to ι]} else ∅ : gset PID). 2: {
      break_match_goal.
      * rewrite renamePIDPID_sym_neq. by rewrite set_map_singleton_L.
        intro. subst. apply H2. left. setoid_rewrite lookup_insert. by destruct_decide_eq.
      * by rewrite set_map_empty.
    }
    econstructor.
    - rewrite renamePID_mk_list, H7. reflexivity.
    - unfold renamePIDPID_sym; intro. repeat case_match; eqb_to_eq; subst; auto.
      all: set_solver.
    - assert (ι' ≠ to) by set_solver.
      clear H13.
      apply not_isUsedPool_insert_1 in H9 as D. destruct D.
      replace (_ ↦ _∥_) with (renamePIDPool from to (ι↦p∥Π0)).
      2: { unfold renamePIDPool.
           setoid_rewrite fmap_insert. setoid_rewrite kmap_insert; auto.
         }
      intro X. destruct (decide (ι' = from)).
      {
        unfold renamePIDPID_sym in X. subst. rewrite Nat.eqb_refl in X.
        apply isUsedPool_rename_new_2 in X. congruence. assumption.
      }
      {
        unfold renamePIDPID_sym in X. renamePIDPID_sym_case_match_hyp X.
        apply isUsedPool_rename_neq in X; auto.
      }
    - assert (ι' ≠ to) by set_solver.
      clear H13.
      intro X. destruct (decide (ι' = from)).
      {
        unfold renamePIDPID_sym in X. subst. rewrite Nat.eqb_refl in X.
        apply appearsEther_rename_new_2 in X. congruence. assumption.
      }
      {
        unfold renamePIDPID_sym in X. renamePIDPID_sym_case_match_hyp X.
        apply appearsEther_rename_neq in X; auto.
      }
    - cbn. destruct v1; try now inv H13.
      case_match; inv H13; simpl; rewrite length_map, H.
      (* arity mismatch: badarity carries the arguments *)
      2: by rewrite renamePID_meta_to_cons.
      do 2 f_equal. rewrite split_renamePID_subst_exp.
      assert (list_subst
                   (convert_to_closlist
                      (map (λ '(id0, vl, e0), (id0, vl, renamePID from to e0)) ext) ++
                    map (renamePIDVal from to) l) idsubst = renamePID_subst from to
                   (list_subst (convert_to_closlist ext ++ l) idsubst)). {
        rewrite renamePID_subst_list_subst. rewrite map_app.
        f_equal. f_equal. unfold convert_to_closlist. do 2 rewrite map_map.
        f_equal. extensionality x. by destruct x, p0.
      }
      by rewrite H3.
    - eapply renamePID_is_preserved_local in H14.
      rewrite renamePIDPID_sym_neq; auto. exact H14.
      all: auto.
      set_solver.
      intro. apply H2. apply isUsedPool_insert_2. right. by right.
    - set_solver.
Qed.

(** * Used PIDs during reduction *)

(** A PID which does not appear in the ether and is not used by the action
    does not appear in the ether after the step. *)
Theorem not_isUsedEther_step :
  forall O eth Π eth' Π' a ι ι',
    ¬appearsEther ι' eth ->
    ι' ∉ (usedPIDsAct a) ->
    (eth, Π) -[a | ι]ₙ-> (eth', Π') with O ->
    ¬appearsEther ι' eth'.
Proof.
  intros. inv H1; try assumption.
  * intro. simpl in H0.
    apply appearsEther_etherAdd_rev in H1; auto.
    2: { simpl in *. intro. subst. apply H0. set_solver. }
    1-2: set_solver.
  * intro. eapply appearsEther_etherPop_rev in H7. 2: { eassumption. }
    congruence.
Qed.

(** Sequential steps do not introduce new PIDs. NOTE: the reverse of this
    theorem does not hold! *)
Theorem not_isUsedProc_sequential :
  forall fs r fs' r' ι',
    ι' ∈ (usedPIDsStack fs' ∪ usedPIDsRed r') ->
    ⟨fs, r⟩ --> ⟨fs', r'⟩ ->
    ι' ∈ (usedPIDsStack fs ∪ usedPIDsRed r).
Proof.
  intros. inv H0; simpl in *; try rewrite app_nil_r in *; auto.
  all: repeat (apply elem_of_union in H as [|]); try set_solver.
  * rewrite flat_union_app in H; simpl in H.
    apply elem_of_union in H as [|]; try set_solver.
  * repeat (apply elem_of_union in H as [|]).
    all: try set_solver.
    pose proof create_result_usedPIDs _ _ _ _ (eq_sym H2).
    set_solver.
  * repeat (apply elem_of_union in H as [|]).
    all: try set_solver.
    pose proof create_result_usedPIDs _ _ _ _ (eq_sym H1).
    rewrite flat_union_app in H0.
    set_solver.
  * repeat (apply elem_of_union in H as [|]).
    all: try set_solver.
    rewrite elem_of_flat_union in H. destruct_hyps.
    apply elem_of_union. right. apply elem_of_union. right.
    apply elem_of_flat_union.
    apply list_elem_of_In in H. apply in_flatten_list in H.
    destruct_hyps. inv H; apply list_elem_of_In in H1.
    - eexists; split. eassumption. set_solver.
    - eexists; split. eassumption. set_solver.
  * apply subst_usedPIDs in H as [|].
    - set_solver.
    - apply elem_of_union. right. destruct H as [n [v [P1 P2]]].
      apply elem_of_flat_union. eexists; split. 2: eassumption.
      by apply list_subst_idsubst_inl in P1.
  * apply subst_usedPIDs in H as [|].
    - set_solver.
    - apply elem_of_union. right. destruct H as [n [v [P1 P2]]].
      apply list_subst_idsubst_inl in P1.
      eapply match_pattern_list_usedPIDs in H1.
      2: { apply elem_of_flat_union. eexists; split; eassumption. }
      assumption.
  * apply subst_usedPIDs in H as [|].
    - set_solver.
    - apply elem_of_union. right. destruct H as [n [v [P1 P2]]].
      apply list_subst_idsubst_inl in P1.
      eapply match_pattern_list_usedPIDs in H1.
      2: { apply elem_of_flat_union. eexists; split; eassumption. }
      assumption.
  * unfold segment_to_bitstring in H1. repeat case_match; invSome; simpl.
    all: set_solver.
  * apply subst_usedPIDs in H as [|].
    - set_solver.
    - apply elem_of_union. right. apply elem_of_union.
      right. destruct H as [n [v [P1 P2]]].
      apply list_subst_idsubst_inl in P1.
      unfold convert_to_closlist in P1. rewrite map_map in P1.
      apply elem_of_map_iff in P1 as [x [P1 P3]]. destruct x. simpl in *.
      inv P1. simpl in *.
      apply elem_of_union in P2 as [|].
      + apply elem_of_flat_union. eexists; split; eassumption.
      + apply elem_of_flat_union in H; destruct_hyps.
        apply elem_of_map_iff in H; destruct_hyps. destruct x0. inv H0.
        apply elem_of_flat_union. eexists; split; eassumption.
  * apply subst_usedPIDs in H as [|].
    - set_solver.
    - apply elem_of_union. right. destruct H as [n [v [P1 P2]]].
      apply elem_of_flat_union. eexists; split. 2: eassumption.
      by apply list_subst_idsubst_inl in P1.
  * apply subst_usedPIDs in H as [|].
    - set_solver.
    - apply elem_of_union. right. destruct H as [n [v [P1 P2]]].
      replace (exclass_to_value class .: reason .: details .: idsubst) with
              (list_subst [exclass_to_value class; reason; details] idsubst) in P1
              by reflexivity.
      apply list_subst_idsubst_inl in P1. apply list_elem_of_In in P1. 
      inv P1. 2: inv H. 3: inv H0. 4: inv H.
      + destruct class; inv P2.
      + set_solver.
      + set_solver.
Qed.

(*
  NOTE: the reverse of this theorem does not hold!
*)
(** Process-local steps do not introduce new PIDs, except for the ones of the
    action. *)
Theorem not_isUsedProc_step :
  forall p p' a ι',
    ι' ∈ (usedPIDsProc p') ->
    ι' ∉ (usedPIDsAct a) ->
    p -⌈a⌉-> p' ->
    ι' ∈ (usedPIDsProc p).
Proof.
  intros. inv H1; try assumption.
  * simpl in *.
    repeat apply elem_of_union in H as [|]; try set_solver.
    all: eapply not_isUsedProc_sequential with (ι' := ι') in H2; set_solver.
  * simpl in *.
    repeat apply elem_of_union in H as [|]; try set_solver.
    apply elem_of_flat_union in H. destruct_hyps. apply elem_of_app in H as [|].
    - apply elem_of_union. right. apply elem_of_flat_union. set_solver.
    - set_solver.
  * simpl in *.
    unfold union_set in H. apply elem_of_union_list in H. destruct_hyps.
    apply elem_of_elements in H.
    apply elem_of_map_to_set in H. destruct_hyps. simpl in *.
    apply lookup_gset_to_gmap_Some in H. destruct_hyps. subst.
    apply elem_of_union in H1 as [|].
    - simpl in *. set_solver.
    - set_solver.
  * simpl in *.
    repeat apply elem_of_union in H as [|]; try set_solver.
    apply elem_of_flat_union in H as [x [H_1 H_2]].
    apply elem_of_app in H_1 as [? | ?].
    - apply elem_of_union. right. apply elem_of_flat_union. set_solver.
    - apply list_elem_of_singleton in H. subst. simpl in *.
      set_solver.
  * simpl in *. set_solver.
  * simpl in *. set_solver.
  * simpl in *. set_solver.
  * simpl in *. set_solver.
  * simpl in *. set_solver.
  * simpl in *. set_solver.
  * simpl in *.
    unfold union_set in H. apply elem_of_union_list in H. destruct_hyps.
    apply elem_of_elements in H.
    apply elem_of_map_to_set in H. destruct_hyps. subst.
    apply lookup_delete_Some in H as [? ?].
    unfold union_set. apply elem_of_union_list. exists ({[x0]} ∪ usedPIDsVal x1).
    split. 2: assumption.
    apply elem_of_elements, elem_of_map_to_set. exists x0, x1. split.
    2: reflexivity. assumption.
  * simpl in *. set_solver.
  * simpl in *. set_solver.
  * simpl in *. set_solver.
  * simpl in *.
    repeat apply elem_of_union in H as [|]; try set_solver.
    destruct mb. simpl in *. destruct l0; simpl in *. congruence. inv H2.
    set_solver.
  * simpl in *. set_solver.
  * simpl in *.
    repeat apply elem_of_union in H as [|]; try set_solver.
    - destruct mb, l0; simpl in *. set_solver. inv H2. simpl in H.
      rewrite flat_union_app in H.
      set_solver.
    - destruct mb, l0; simpl in *. set_solver. set_solver.
  * simpl in *.
    repeat apply elem_of_union in H as [|]; try set_solver.
    - destruct mb, l0; simpl in *. set_solver. inv H2. simpl in H.
      set_solver.
    - destruct mb, l0; simpl in *. set_solver. inv H2. simpl in H.
      rewrite flat_union_app in H. set_solver.
  * simpl in *. set_solver.
  * simpl in *. set_solver.
  * simpl in *. set_solver.
  * simpl in *.
    repeat apply elem_of_union in H as [|]; try set_solver.
    destruct flag; set_solver.
  * simpl in *.
    repeat apply elem_of_union in H as [|]; try set_solver.
  * simpl in *.
    unfold union_set in H. apply elem_of_union_list in H. destruct_hyps.
    apply elem_of_elements in H.
    apply elem_of_map_to_set in H. destruct_hyps. simpl in *.
    apply lookup_gset_to_gmap_Some in H. destruct_hyps. subst.
    apply elem_of_union in H1 as [|].
    - simpl in *. set_solver.
    - set_solver.
  * simpl in *.
    unfold union_set in H. apply elem_of_union_list in H. destruct_hyps.
    apply elem_of_elements in H.
    apply elem_of_map_to_set in H. destruct_hyps. simpl in *.
    apply lookup_gset_to_gmap_Some in H. destruct_hyps. subst.
    apply elem_of_union in H1 as [|].
    - simpl in *. set_solver.
    - destruct exc as [[c r] d], c; simpl in *; set_solver.
Qed.

(** A PID which is not used in a Core Erlang list is not used in its
    elements. *)
Lemma mk_list_not_usedPIDs :
  forall v ι' l,
  ι' ∉ (usedPIDsVal v) ->
  mk_list v = Some l ->
  ι' ∉ (flat_union usedPIDsVal l).
Proof.
  induction v; intros; inv H0; auto.
  case_match; invSome. simpl in *. apply not_elem_of_union in H as [? ?].
  eapply IHv2 in H1. 2: reflexivity.
  set_solver.
Qed.

(** The PIDs of a Core Erlang list are the PIDs of its elements. *)
Lemma mk_list_usedPIDs :
  forall v ι' l,
  mk_list v = Some l ->
  ι' ∈ (usedPIDsVal v) <->
  ι' ∈ (flat_union usedPIDsVal l).
Proof.
  induction v; intros; split; intros; inv H.
  * set_solver.
  * set_solver.
  * case_match; invSome. simpl in H0. simpl. set_solver.
  * case_match; invSome. simpl in H0. simpl. set_solver.
Qed.



(* NOTE: the reverse of this theorem does not hold! *)
(** A PID which is not used in the pool and by the action is not used in the
    pool after the step. *)
Theorem not_isUsedPool_step :
  forall O eth Π eth' Π' a ι ι',
    ¬isUsedPool ι' Π ->
    ι' ∉ (usedPIDsAct a) ->
    (eth, Π) -[a | ι]ₙ-> (eth', Π') with O ->
    ¬isUsedPool ι' Π'.
Proof.
  intros. inv H1; try assumption; intro; simpl in *.
  * apply isUsedPool_insert_1 in H1.
    apply H. apply isUsedPool_insert_2.
    destruct_or!; auto.
    right. right. eapply not_isUsedProc_step; try eauto.
    by simpl.
  * apply isUsedPool_insert_1 in H1.
    apply H. apply isUsedPool_insert_2.
    destruct_or!; auto.
    right. right. eapply not_isUsedProc_step; try eauto.
    by simpl.
  * apply isUsedPool_insert_1 in H1.
    apply H. apply isUsedPool_insert_2.
    destruct_or! H1; auto.
    right. right. eapply not_isUsedProc_step; try eauto.
  * assert (ι <> ι') as HXX. {
      intro. subst. apply H. left. setoid_rewrite lookup_insert.
      by destruct_decide_eq.
    }
    setoid_rewrite insert_insert in H1. destruct_decide_eq.
    1: { by apply not_isUsedPool_insert_1 in H8 as [_ X]. }
    apply isUsedPool_insert_1 in H1.
    apply H. apply isUsedPool_insert_2; intuition.
    - left.
      unfold isUsedPool in *.
      setoid_rewrite lookup_delete_None in H2.
      setoid_rewrite lookup_delete_None. destruct_or!.
      + left. intro. destruct H1. set_solver. apply H2. right.
        setoid_rewrite lookup_insert_ne. assumption. set_solver.
      + destruct H2 as [ι'1 [pp [H_1 H_2]]].
        apply lookup_delete_Some in H_1 as [H_11 H_12].
        destruct (decide (ι'1 = ι'0)).
        ** subst. setoid_rewrite lookup_insert in H_12. inv H_12.
           cbn in H_2. exfalso.
           destruct v1; try now inv H12.
           destruct_decide_eq. inv H2.
           destruct Nat.eqb eqn:P; inv H12.
           -- clear - H_2 H_11 H6 H0 HXX.
              apply not_elem_of_union in H0 as [P1 P2]. simpl in P1.
              apply not_elem_of_union in P1 as [P1 P3].
              apply not_elem_of_union in P3 as [P3 P4].
              simpl in H_2. rewrite union_empty_l_L in H_2.
              repeat rewrite union_empty_r_L in H_2.
              assert (ι'
      ∈ usedPIDsExp e.[list_subst (convert_to_closlist ext ++ l) idsubst]) as H_2'. {
                clear -H_2 HXX. case_match; set_solver.
              }
              apply subst_usedPIDs in H_2'.
              destruct H_2'.
              ++ congruence.
              ++ destruct H as [n [v [P5 P6]]].
                 apply list_subst_idsubst_inl in P5.
                 apply elem_of_app in P5 as [|].
                 *** unfold convert_to_closlist in H.
                     apply elem_of_map_iff in H. destruct_hyps. destruct x, p.
                     subst. simpl in P6.
                     apply elem_of_union in P6 as [|]; try congruence.
                     apply P4. apply elem_of_flat_union. eexists; split; eassumption.
                 *** eapply mk_list_not_usedPIDs in H6. 2: eassumption.
                     apply H6. apply elem_of_flat_union. eexists; split; eassumption.
           -- case_match; simpl in *.
              ++ clear - H_2 H0 H6 HXX.
                 rewrite meta_to_cons_usedPIDs in H_2.
                 assert (ι' ∉ usedPIDsVal v2) as Hv2 by set_solver.
                 eapply mk_list_not_usedPIDs in Hv2. 2: eassumption.
                 set_solver.
              ++ clear - H_2 H0 H6 HXX.
                 rewrite meta_to_cons_usedPIDs in H_2.
                 assert (ι' ∉ usedPIDsVal v2) as Hv2 by set_solver.
                 eapply mk_list_not_usedPIDs in Hv2. 2: eassumption.
                 set_solver.
        ** right. exists ι'1, pp. setoid_rewrite lookup_delete_Some.
           intuition. setoid_rewrite lookup_insert_ne in H_12; auto.
    - right. right. eapply not_isUsedProc_step; try eauto.
      simpl. set_solver.
Qed.

(** Reduction sequences are preserved by renaming to a fresh PID. *)
Corollary renamePID_is_preserved_steps :
  forall O eth eth' Π Π' l,
    (eth, Π) -[l]ₙ->* (eth', Π') with O ->
    forall from to,
      to ∉ (flat_union (usedPIDsAct ∘ fst) l) ->
      ¬ appearsEther to eth ->
      ¬ isUsedPool to Π ->
      to ∉ O ->
      (renamePIDEther from to eth, renamePIDPool from to Π)
    -[map (prod_map (renamePIDAct from to) (renamePIDPID_sym from to)) l]ₙ->*
      (renamePIDEther from to eth', renamePIDPool from to Π') with O.
Proof.
  intros O eth eth' Π Π' l.
  revert Π Π' eth eth'. induction l; simpl in *; intros.
  {
    inv H. constructor.
  }
  {
    inv H. destruct n'. eapply IHl in H9.
    econstructor. 2: eassumption.
    2: {
      set_solver.
    }
    2: {
      eapply not_isUsedEther_step; try eassumption.
      set_solver.
    }
    2: {
      eapply not_isUsedPool_step; try eassumption.
      set_solver.
    }
    2: {
      assumption.
    }
    simpl. apply renamePID_is_preserved; try assumption.
    set_solver.
  }
Qed.

(** The signals to a non-existing process are not affected by a reduction
    sequence in which all send targets exist at the end. *)
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
      2: { setoid_rewrite lookup_insert. by destruct_decide_eq. }
      by inv H0.
    - break_match_hyp; try congruence. destruct l0; try congruence. inv H3.
      setoid_rewrite lookup_insert_ne; auto.
Qed.

(** Renaming the PID `from` to `to` and then back restores an ether in which
    `to` does not appear. *)
Corollary double_renamePID_ether :
  forall eth from to, ¬ appearsEther to eth -> renamePIDEther to from (renamePIDEther from to eth) = eth.
Proof.
  intros.
  destruct (decide (from = to)).
  {
    subst. by do 2 rewrite renamePID_id_ether.
  }
  unfold renamePIDEther.
  apply map_eq. intros. destruct i as [ιs ιd].
  unfold appearsEther in H.
  rewrite <- kmap_fmap; auto.
  destruct (eth !! (ιs, ιd)) eqn:P; setoid_rewrite P.
  * apply lookup_kmap_Some; auto.
    assert (ιd ≠ to). {
      intro. subst. apply H. left. by exists ιs, l.
    }
    destruct (decide (ιs = from)). 2: destruct (decide (ιs = to)).
    - subst. destruct (decide (ιd = from)).
      + subst. exists (to, to). cbn. split. by renamePIDPID_sym_case_match.
        apply lookup_kmap_Some; auto.
        exists (from, from). cbn. split. by renamePIDPID_sym_case_match.
        do 2 setoid_rewrite lookup_fmap. setoid_rewrite P.
        cbn. f_equal.
        rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext_in.
        intros. apply double_renamePID_sig. intro.
        apply H. right. right. do 3 eexists. split. exact P.
        apply elem_of_flat_union.
        apply list_elem_of_In in H1. exists a. split; assumption.
      + subst. exists (to, ιd). cbn. split. by renamePIDPID_sym_case_match.
        apply lookup_kmap_Some; auto.
        exists (from, ιd). cbn. split. by renamePIDPID_sym_case_match.
        do 2 setoid_rewrite lookup_fmap. setoid_rewrite P.
        cbn. f_equal.
        rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext_in.
        intros. apply double_renamePID_sig. intro.
        apply H. right. right. do 3 eexists. split. exact P.
        apply elem_of_flat_union.
        apply list_elem_of_In in H1. exists a. split; assumption.
    - subst. destruct (decide (ιd = from)).
      + subst. exists (from, to). cbn. split. by renamePIDPID_sym_case_match.
        apply lookup_kmap_Some; auto.
        exists (to, from). cbn. split. by renamePIDPID_sym_case_match.
        do 2 setoid_rewrite lookup_fmap. setoid_rewrite P.
        cbn. f_equal.
        rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext_in.
        intros. apply double_renamePID_sig. intro.
        apply H. right. right. do 3 eexists. split. exact P.
        apply elem_of_flat_union.
        apply list_elem_of_In in H1. exists a. split; assumption.
      + subst. exists (from, ιd). cbn. split. by renamePIDPID_sym_case_match.
        apply lookup_kmap_Some; auto.
        exists (to, ιd). cbn. split. by renamePIDPID_sym_case_match.
        do 2 setoid_rewrite lookup_fmap. setoid_rewrite P.
        cbn. f_equal.
        rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext_in.
        intros. apply double_renamePID_sig. intro.
        apply H. right. right. do 3 eexists. split. exact P.
        apply elem_of_flat_union.
        apply list_elem_of_In in H1. exists a. split; assumption.
    - subst. destruct (decide (ιd = from)).
      + subst. exists (ιs, to). cbn. split. by renamePIDPID_sym_case_match.
        apply lookup_kmap_Some; auto.
        exists (ιs, from). cbn. split. by renamePIDPID_sym_case_match.
        do 2 setoid_rewrite lookup_fmap. setoid_rewrite P.
        cbn. f_equal.
        rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext_in.
        intros. apply double_renamePID_sig. intro.
        apply H. right. right. do 3 eexists. split. exact P.
        apply elem_of_flat_union.
        apply list_elem_of_In in H1. exists a. split; assumption.
      + subst. exists (ιs, ιd). cbn. split. by renamePIDPID_sym_case_match.
        apply lookup_kmap_Some; auto.
        exists (ιs, ιd). cbn. split. by renamePIDPID_sym_case_match.
        do 2 setoid_rewrite lookup_fmap. setoid_rewrite P.
        cbn. f_equal.
        rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext_in.
        intros. apply double_renamePID_sig. intro.
        apply H. right. right. do 3 eexists. split. exact P.
        apply elem_of_flat_union.
        apply list_elem_of_In in H1. exists a. split; assumption.
  * apply lookup_kmap_None; auto. intros.
    apply lookup_kmap_None; auto. intros.
    do 2 rewrite lookup_fmap. destruct i, i0. cbn in *.
    inv H0.
    renamePIDPID_sym_case_match_hyp P; by setoid_rewrite P.
Qed.

(** Renaming the PID `from` to `to` and then back restores a pool in which
    `to` is not used. *)
Corollary double_renamePID_pool :
  forall Π from to, ¬ isUsedPool to Π -> renamePIDPool to from (renamePIDPool from to Π) = Π.
Proof.
  intros.
  destruct (decide (from = to)).
  {
    subst. by do 2 rewrite renamePID_id_pool.
  }
  unfold renamePIDPool.
  apply map_eq. intros.
  unfold isUsedPool in H.
  rewrite <- kmap_fmap; auto.
  destruct (Π !! i) eqn:P; setoid_rewrite P.
  * apply lookup_kmap_Some; auto.
    assert (i ≠ to). {
      intro. subst. apply H. left. intro. congruence.
    }
    destruct (decide (i = from)).
    - subst. exists to. cbn. split. by renamePIDPID_sym_case_match.
      apply lookup_kmap_Some; auto.
      exists from. cbn. split. by renamePIDPID_sym_case_match.
      do 2 setoid_rewrite lookup_fmap. setoid_rewrite P.
      cbn. f_equal.
      apply double_renamePID_proc. intro.
      apply H. right. do 2 eexists. split. exact P.
      assumption.
    - subst. exists i. cbn. split. by renamePIDPID_sym_case_match.
      apply lookup_kmap_Some; auto.
      exists i. cbn. split. by renamePIDPID_sym_case_match.
      do 2 setoid_rewrite lookup_fmap. setoid_rewrite P.
      cbn. f_equal.
      apply double_renamePID_proc. intro.
      apply H. right. do 2 eexists. split. exact P.
      assumption.
  * apply lookup_kmap_None; auto. intros.
    apply lookup_kmap_None; auto. intros.
    do 2 rewrite lookup_fmap. cbn in *.
    subst. unfold renamePIDPID_sym in P.
    repeat case_match; eqb_to_eq; subst; try lia.
    all: by setoid_rewrite P.
Qed.

(** Two independent PID renamings with different new PIDs can be applied to
    an ether in either order. *)
Corollary renamePID_swap_ether :
  forall eth from1 from2 to1 to2,
    from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 -> to1 ≠ to2 ->
    renamePIDEther from2 to2 (renamePIDEther from1 to1 eth) =
    renamePIDEther from1 to1 (renamePIDEther from2 to2 eth).
Proof.
  intros.
  destruct (decide (from1 = to1)).
  {
    subst. by do 2 rewrite renamePID_id_ether.
  }
  destruct (decide (from2 = to2)).
  {
    subst. by do 2 rewrite renamePID_id_ether.
  }
  unfold renamePIDEther.
  apply map_eq. intros. destruct i as [ιs ιd].
  rewrite <- kmap_fmap; auto.
  rewrite <- kmap_fmap; auto.
  replace (map (renamePIDSignal from2 to2) <$> (map (renamePIDSignal from1 to1) <$> eth)) with
    (map (renamePIDSignal from1 to1) <$> (map (renamePIDSignal from2 to2) <$> eth)).
  2: {
    do 2 rewrite <- map_fmap_compose. f_equal. unfold compose.
    extensionality sigs.
    do 2 rewrite map_map. f_equal.
    extensionality s. rewrite renamePID_swap_sig; auto.
  }
  remember (map (renamePIDSignal from1 to1) <$> (map (renamePIDSignal from2 to2) <$> eth)) as E. clear HeqE.
  (* TODO:boiler plate, the following cases are very similar *)
  destruct (decide (ιs = from2)). 2: destruct (decide (ιs = to2)).
  3: destruct (decide (ιs = from1)). 4: destruct (decide (ιs = to1)).
  - subst. destruct (decide (ιd = to2)). 2: destruct (decide (ιd = from2)).
    + subst.
      assert ((from2, to2) = (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (to2, from2))).
      {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      rewrite H3 at 1.
      setoid_rewrite lookup_kmap; auto.
      replace (to2, from2) with
  (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (to2, from2)).
      2: {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      replace (from2, to2) with
  (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (from2, to2)).
      2: {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      setoid_rewrite lookup_kmap; auto.
      rewrite H3. setoid_rewrite lookup_kmap; auto.
    + subst.
      assert ((from2, from2) = (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (to2, to2))).
      {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      rewrite H3 at 1.
      setoid_rewrite lookup_kmap; auto.
      replace (to2, to2) with
  (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (to2, to2)).
      2: {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      replace (from2, from2) with
  (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (from2, from2)).
      2: {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      setoid_rewrite lookup_kmap; auto.
      rewrite H3. setoid_rewrite lookup_kmap; auto.
    + subst.
      assert ((from2, ιd) = (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (to2, ιd))).
      {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      rewrite H3 at 1.
      setoid_rewrite lookup_kmap; auto.
      destruct (decide (ιd = to1)). 2: destruct (decide (ιd = from1)).
      all: subst.
      ** replace (to2, to1) with
    (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (to2, from1)).
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
         replace (from2, to1) with
    (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (from2, from1)).
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
         replace (from2, from1) with
    (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (to2, from1)).
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
      ** replace (to2, from1) with
    (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (to2, to1)).
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
         replace (from2, from1) with
    (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (from2, to1)).
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
         replace (from2, to1) with
    (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (to2, to1)).
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
     ** replace (to2, ιd) with
    (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (to2, ιd)).
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
         replace (from2, ιd) with
    (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (from2, ιd)).
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto. rewrite H3.
         setoid_rewrite lookup_kmap; auto.
  - subst. destruct (decide (ιd = to2)). 2: destruct (decide (ιd = from2)).
    + subst.
      assert ((to2, to2) = (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (from2, from2))).
      {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      rewrite H3 at 1.
      setoid_rewrite lookup_kmap; auto.
      replace (from2, from2) with
  (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (from2, from2)).
      2: {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      replace (to2, to2) with
  (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (to2, to2)).
      2: {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      setoid_rewrite lookup_kmap; auto.
      rewrite H3. setoid_rewrite lookup_kmap; auto.
    + subst.
      assert ((to2, from2) = (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (from2, to2))).
      {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      rewrite H3 at 1.
      setoid_rewrite lookup_kmap; auto.
      replace (from2, to2) with
  (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (from2, to2)).
      2: {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      replace (to2, from2) with
  (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (to2, from2)).
      2: {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      setoid_rewrite lookup_kmap; auto.
      rewrite H3. setoid_rewrite lookup_kmap; auto.
    + subst.
      assert ((to2, ιd) = (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (from2, ιd))).
      {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      rewrite H3 at 1.
      setoid_rewrite lookup_kmap; auto.
      destruct (decide (ιd = to1)). 2: destruct (decide (ιd = from1)).
      all: subst.
      ** replace (from2, to1) with
    (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (from2, from1)).
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
         replace (to2, to1) with
    (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (to2, from1)).
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
         replace (to2, from1) with
    (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (from2, from1)).
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
      ** replace (from2, from1) with
    (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (from2, to1)).
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
         replace (to2, from1) with
    (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (to2, to1)).
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
         replace (to2, to1) with
    (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (from2, to1)).
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
     ** replace (from2, ιd) with
    (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (from2, ιd)).
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
         replace (to2, ιd) with
    (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (to2, ιd)).
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto. rewrite H3.
         setoid_rewrite lookup_kmap; auto.
  - subst. destruct (decide (ιd = to2)). 2: destruct (decide (ιd = from2)).
    + subst.
      assert ((from1, to2) = (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (from1, from2))).
      {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      rewrite H3 at 1.
      setoid_rewrite lookup_kmap; auto.
      replace (from1, from2) with
  (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (to1, from2)).
      2: {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      setoid_rewrite lookup_kmap; auto.
      replace (from1, to2) with
  (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (to1, to2)).
      2: {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      setoid_rewrite lookup_kmap; auto.
      replace (to1, to2) with
  (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (to1, from2)).
      2: {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      setoid_rewrite lookup_kmap; auto.
    + subst.
      assert ((from1, from2) = (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (from1, to2))).
      {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      rewrite H3 at 1.
      setoid_rewrite lookup_kmap; auto.
      replace (from1, to2) with
  (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (to1, to2)).
      2: {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      setoid_rewrite lookup_kmap; auto.
      replace (from1, from2) with
  (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (to1, from2)).
      2: {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      setoid_rewrite lookup_kmap; auto.
      replace (to1, from2) with
  (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (to1, to2)).
      2: {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      setoid_rewrite lookup_kmap; auto.
    + subst.
      assert ((from1, ιd) = (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (from1, ιd))).
      {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      rewrite H3 at 1.
      setoid_rewrite lookup_kmap; auto.
      destruct (decide (ιd = to1)). 2: destruct (decide (ιd = from1)).
      all: subst.
      ** replace (from1, to1) with
    (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (to1, from1)).
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
         replace (to1, from1) with
    (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (to1, from1)) at 2.
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
      ** replace (from1, from1) with
    (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (to1, to1)).
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
         replace (to1, to1) with
    (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (to1, to1)) at 2.
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
     ** replace (from1, ιd) with
    (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (to1, ιd)).
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
         replace (to1, ιd) with
    (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (to1, ιd)) at 2.
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
  - subst. destruct (decide (ιd = to2)). 2: destruct (decide (ιd = from2)).
    + subst.
      assert ((to1, to2) = (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (to1, from2))).
      {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      rewrite H3 at 1.
      setoid_rewrite lookup_kmap; auto.
      replace (to1, from2) with
  (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (from1, from2)).
      2: {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      setoid_rewrite lookup_kmap; auto.
      replace (to1, to2) with
  (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (from1, to2)).
      2: {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      setoid_rewrite lookup_kmap; auto.
      replace (from1, to2) with
  (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (from1, from2)).
      2: {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      setoid_rewrite lookup_kmap; auto.
    + subst.
      assert ((to1, from2) = (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (to1, to2))).
      {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      rewrite H3 at 1.
      setoid_rewrite lookup_kmap; auto.
      replace (to1, to2) with
  (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (from1, to2)).
      2: {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      setoid_rewrite lookup_kmap; auto.
      replace (to1, from2) with
  (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (from1, from2)).
      2: {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      setoid_rewrite lookup_kmap; auto.
      replace (from1, from2) with
  (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (from1, to2)).
      2: {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      setoid_rewrite lookup_kmap; auto.
    + subst.
      assert ((to1, ιd) = (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (to1, ιd))).
      {
        unfold prod_map. simpl. by renamePIDPID_sym_case_match.
      }
      rewrite H3 at 1.
      setoid_rewrite lookup_kmap; auto.
      destruct (decide (ιd = to1)). 2: destruct (decide (ιd = from1)).
      all: subst.
      ** replace (to1, to1) with
    (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (from1, from1)).
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
         replace (from1, from1) with
    (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (from1, from1)) at 2.
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
      ** replace (to1, from1) with
    (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (from1, to1)).
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
         replace (from1, to1) with
    (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (from1, to1)) at 2.
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
     ** replace (to1, ιd) with
    (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (from1, ιd)).
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
         replace (from1, ιd) with
    (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (from1, ιd)) at 2.
         2: {
           unfold prod_map. simpl. by renamePIDPID_sym_case_match.
         }
         setoid_rewrite lookup_kmap; auto.
  - destruct (decide (ιd = to1)). 2: destruct (decide (ιd = from1)).
    3: destruct (decide (ιd = to2)). 4: destruct (decide (ιd = from2)).
    all: subst.
    ** replace (ιs, to1) with
  (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (ιs, to1)) at 1.
       2: {
         unfold prod_map. simpl. by renamePIDPID_sym_case_match.
       }
       setoid_rewrite lookup_kmap; auto.
       replace (ιs, to1) with
  (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (ιs, from1)).
       2: {
         unfold prod_map. simpl. by renamePIDPID_sym_case_match.
       }
       setoid_rewrite lookup_kmap; auto.
       replace (ιs, from1) with
  (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (ιs, from1)) at 2.
       2: {
         unfold prod_map. simpl. by renamePIDPID_sym_case_match.
       }
       setoid_rewrite lookup_kmap; auto.
    ** replace (ιs, from1) with
  (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (ιs, from1)) at 1.
       2: {
         unfold prod_map. simpl. by renamePIDPID_sym_case_match.
       }
       setoid_rewrite lookup_kmap; auto.
       replace (ιs, from1) with
  (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (ιs, to1)).
       2: {
         unfold prod_map. simpl. by renamePIDPID_sym_case_match.
       }
       setoid_rewrite lookup_kmap; auto.
       replace (ιs, to1) with
  (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (ιs, to1)) at 2.
       2: {
         unfold prod_map. simpl. by renamePIDPID_sym_case_match.
       }
       setoid_rewrite lookup_kmap; auto.
    ** replace (ιs, to2) with
  (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (ιs, from2)) at 1.
       2: {
         unfold prod_map. simpl. by renamePIDPID_sym_case_match.
       }
       setoid_rewrite lookup_kmap; auto.
       replace (ιs, from2) with
  (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (ιs, from2)).
       2: {
         unfold prod_map. simpl. by renamePIDPID_sym_case_match.
       }
       setoid_rewrite lookup_kmap; auto.
       replace (ιs, to2) with
  (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (ιs, to2)).
       2: {
         unfold prod_map. simpl. by renamePIDPID_sym_case_match.
       }
       setoid_rewrite lookup_kmap; auto.
       replace (ιs, to2) with
  (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (ιs, from2)).
       2: {
         unfold prod_map. simpl. by renamePIDPID_sym_case_match.
       }
       setoid_rewrite lookup_kmap; auto.
    ** replace (ιs, from2) with
  (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (ιs, to2)) at 1.
       2: {
         unfold prod_map. simpl. by renamePIDPID_sym_case_match.
       }
       setoid_rewrite lookup_kmap; auto.
       replace (ιs, to2) with
  (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (ιs, to2)).
       2: {
         unfold prod_map. simpl. by renamePIDPID_sym_case_match.
       }
       setoid_rewrite lookup_kmap; auto.
       replace (ιs, from2) with
  (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (ιs, from2)).
       2: {
         unfold prod_map. simpl. by renamePIDPID_sym_case_match.
       }
       setoid_rewrite lookup_kmap; auto.
       replace (ιs, from2) with
  (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (ιs, to2)).
       2: {
         unfold prod_map. simpl. by renamePIDPID_sym_case_match.
       }
       setoid_rewrite lookup_kmap; auto.
   ** assert ((ιs, ιd) =
  (prod_map (renamePIDPID_sym from1 to1) (renamePIDPID_sym from1 to1) (ιs, ιd))).
       {
         unfold prod_map. simpl. by renamePIDPID_sym_case_match.
       }
       assert ((ιs, ιd) =
  (prod_map (renamePIDPID_sym from2 to2) (renamePIDPID_sym from2 to2) (ιs, ιd))).
       {
         unfold prod_map. simpl. by renamePIDPID_sym_case_match.
       }
       rewrite H4 at 1. rewrite H3 at 1.
       setoid_rewrite lookup_kmap; auto.
       setoid_rewrite lookup_kmap; auto.
       rewrite H3 at 2. rewrite H4 at 2.
       setoid_rewrite lookup_kmap; auto.
       setoid_rewrite lookup_kmap; auto.
Qed.

(** Two independent PID renamings with different new PIDs can be applied to
    a pool in either order. *)
Corollary renamePID_swap_pool :
  forall Π from1 from2 to1 to2,
    from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 -> to1 ≠ to2 ->
    renamePIDPool from2 to2 (renamePIDPool from1 to1 Π) =
    renamePIDPool from1 to1 (renamePIDPool from2 to2 Π).
Proof.
  intros.
  destruct (decide (from1 = to1)).
  {
    subst. by do 2 rewrite renamePID_id_pool.
  }
  destruct (decide (from2 = to2)).
  {
    subst. by do 2 rewrite renamePID_id_pool.
  }
  unfold renamePIDPool.
  apply map_eq. intros.
  rewrite <- kmap_fmap; auto.
  rewrite <- kmap_fmap; auto.
  replace (renamePIDProc from1 to1 <$> (renamePIDProc from2 to2 <$> Π)) with
          (renamePIDProc from2 to2 <$> (renamePIDProc from1 to1 <$> Π)).
  2: {
    do 2 rewrite <- map_fmap_compose. f_equal. unfold compose.
    extensionality proc. by rewrite renamePID_swap_proc.
  }
  remember (renamePIDProc from2 to2 <$> (renamePIDProc from1 to1 <$> Π)) as P. clear HeqP.
  (* TODO:boiler plate, the following cases are very similar *)
  destruct (decide (i = from2)). 2: destruct (decide (i = to2)).
  3: destruct (decide (i = from1)). 4: destruct (decide (i = to1)).
  - subst.
    replace from2 with (renamePIDPID_sym from2 to2 to2) at 1 by renamePIDPID_sym_case_match.
    setoid_rewrite lookup_kmap; auto.
    replace to2 with (renamePIDPID_sym from1 to1 to2) at 1 by renamePIDPID_sym_case_match.
    setoid_rewrite lookup_kmap; auto.
    replace from2 with (renamePIDPID_sym from1 to1 from2) at 1 by renamePIDPID_sym_case_match.
    setoid_rewrite lookup_kmap; auto.
    replace from2 with (renamePIDPID_sym from2 to2 to2) at 1 by renamePIDPID_sym_case_match.
    setoid_rewrite lookup_kmap; auto.
  - subst.
    replace to2 with (renamePIDPID_sym from2 to2 from2) at 1 by renamePIDPID_sym_case_match.
    setoid_rewrite lookup_kmap; auto.
    replace from2 with (renamePIDPID_sym from1 to1 from2) at 1 by renamePIDPID_sym_case_match.
    setoid_rewrite lookup_kmap; auto.
    replace to2 with (renamePIDPID_sym from1 to1 to2) at 1 by renamePIDPID_sym_case_match.
    setoid_rewrite lookup_kmap; auto.
    replace to2 with (renamePIDPID_sym from2 to2 from2) at 1 by renamePIDPID_sym_case_match.
    setoid_rewrite lookup_kmap; auto.
  - subst.
    replace from1 with (renamePIDPID_sym from2 to2 from1) at 1 by renamePIDPID_sym_case_match.
    setoid_rewrite lookup_kmap; auto.
    replace from1 with (renamePIDPID_sym from1 to1 to1) at 1 by renamePIDPID_sym_case_match.
    setoid_rewrite lookup_kmap; auto.
    replace from1 with (renamePIDPID_sym from1 to1 to1) at 1 by renamePIDPID_sym_case_match.
    setoid_rewrite lookup_kmap; auto.
    replace to1 with (renamePIDPID_sym from2 to2 to1) at 2 by renamePIDPID_sym_case_match.
    setoid_rewrite lookup_kmap; auto.
  - subst.
    replace to1 with (renamePIDPID_sym from2 to2 to1) at 1 by renamePIDPID_sym_case_match.
    setoid_rewrite lookup_kmap; auto.
    replace to1 with (renamePIDPID_sym from1 to1 from1) at 1 by renamePIDPID_sym_case_match.
    setoid_rewrite lookup_kmap; auto.
    replace to1 with (renamePIDPID_sym from1 to1 from1) at 1 by renamePIDPID_sym_case_match.
    setoid_rewrite lookup_kmap; auto.
    replace from1 with (renamePIDPID_sym from2 to2 from1) at 2 by renamePIDPID_sym_case_match.
    setoid_rewrite lookup_kmap; auto.
  - subst.
    replace i with (renamePIDPID_sym from2 to2 i) at 1 by renamePIDPID_sym_case_match.
    setoid_rewrite lookup_kmap; auto.
    replace i with (renamePIDPID_sym from1 to1 i) at 1 by renamePIDPID_sym_case_match.
    setoid_rewrite lookup_kmap; auto.
    replace i with (renamePIDPID_sym from1 to1 i) at 2 by renamePIDPID_sym_case_match.
    setoid_rewrite lookup_kmap; auto.
    replace i with (renamePIDPID_sym from2 to2 i) at 2 by renamePIDPID_sym_case_match.
    setoid_rewrite lookup_kmap; auto.
Qed.

(** * Confluence *)

(** Steps of different processes with compatible actions can be taken in
    either order, and they result in the same node. *)
Lemma confluence :
  forall O n n' ι a, n -[a | ι]ₙ-> n' with O -> forall n'' a' ι' 
    (Spawns : compatiblePIDOf a a'),
   n -[a' | ι']ₙ-> n'' with O ->
  ι <> ι'
->
  exists n''', n' -[a' | ι']ₙ-> n''' with O /\ n'' -[a | ι]ₙ-> n''' with O.
Proof.
  intros O n n' ι a IH. inv IH; intros; subst.
  * inv H0.
    (* NOTE: define exists by hand, do not use `eexists`! *)
    - exists (etherAdd ι'0 ι'1 t0 (etherAdd ι ι' t ether), ι'0 ↦ p'0 ∥ ι ↦ p' ∥ prs).
      split.
      + replace (ι ↦ p' ∥ prs) with (ι'0 ↦ p0 ∥ ι ↦ p' ∥ prs) at 1.
        2: { 
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H4.
             destruct (decide (ι'' = ι'0)).
             * subst. setoid_rewrite lookup_insert at 1.
               destruct_decide_eq.
               setoid_rewrite lookup_insert in H4. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne. all: auto.
             * setoid_rewrite lookup_insert_ne at 1 in H4.
               setoid_rewrite lookup_insert_ne at 1.
               all: auto.
           }
        now constructor.
      + setoid_rewrite insert_insert. destruct_decide_eq.
        rewrite etherAdd_swap_1. 2: now auto.
        replace (ι'0 ↦ p'0 ∥ prs0) with (ι ↦ p ∥ ι'0 ↦ p'0 ∥ prs) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H4.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1. destruct_decide_eq.
               setoid_rewrite lookup_insert in H4. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H4 at 2; auto.
               destruct (decide (ι'' = ι'0)).
               - subst.
                 setoid_rewrite lookup_insert; auto. by destruct_decide_eq.
               - setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in H4; auto.
           }
        now constructor.
    - exists (etherAdd ι ι' t ether', ι'0 ↦ p'0 ∥ ι ↦ p' ∥ prs).
      split.
      + replace (ι ↦ p' ∥ prs) with (ι'0 ↦ p0 ∥ ι ↦ p' ∥ prs) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H3.
             destruct (decide (ι'' = ι'0)).
             * subst. setoid_rewrite lookup_insert at 1. destruct_decide_eq.
               setoid_rewrite lookup_insert in H3. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne. all: auto.
             * setoid_rewrite lookup_insert_ne at 1 in H3.
               setoid_rewrite lookup_insert_ne at 1.
               all: auto.
           }
        constructor. 2: eauto.
        now apply etherPop_etherAdd.
      + setoid_rewrite insert_insert. destruct_decide_eq.
        replace (ι'0 ↦ p'0 ∥ prs0) with (ι ↦ p ∥ ι'0 ↦ p'0 ∥ prs) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H3.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1. destruct_decide_eq.
               setoid_rewrite lookup_insert in H3. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H3 at 2; auto.
               destruct (decide (ι'' = ι'0)).
               - subst.
                 setoid_rewrite lookup_insert; auto. by destruct_decide_eq.
               - setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in H3; auto.
           }
        now constructor.
    - exists (etherAdd ι ι' t ether, ι'0 ↦ p'0 ∥ ι ↦ p' ∥ prs).
      split.
      + replace (ι ↦ p' ∥ prs) with (ι'0 ↦ p0 ∥ ι ↦ p' ∥ prs) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H3.
             destruct (decide (ι'' = ι'0)).
             * subst. setoid_rewrite lookup_insert at 1. destruct_decide_eq.
               setoid_rewrite lookup_insert in H3. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne. all: auto.
             * setoid_rewrite lookup_insert_ne at 1 in H3.
               setoid_rewrite lookup_insert_ne at 1.
               all: auto.
           }
        apply n_other; eauto.
      + setoid_rewrite insert_insert. destruct_decide_eq.
        replace (ι'0 ↦ p'0 ∥ Π) with (ι ↦ p ∥ ι'0 ↦ p'0 ∥ prs) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H3.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1. destruct_decide_eq.
               setoid_rewrite lookup_insert in H3. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H3 at 2; auto.
               destruct (decide (ι'' = ι'0)).
               - subst.
                 setoid_rewrite lookup_insert; auto. by destruct_decide_eq.
               - setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in H3; auto.
           }
        now constructor.
    - exists (etherAdd ι ι' t ether, 
              ι'1 ↦ inl ([], r, emptyBox, if link_flag then {[ι'0]} else ∅, false) ∥ ι'0 ↦ p'0 ∥ ι ↦ p' ∥ prs).
      split.
      + replace (ι ↦ p' ∥ prs) with (ι'0 ↦ p0 ∥ ι ↦ p' ∥ prs) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H3.
             destruct (decide (ι'' = ι'0)).
             * subst. setoid_rewrite lookup_insert at 1. destruct_decide_eq.
               setoid_rewrite lookup_insert in H3. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne. all: auto.
             * setoid_rewrite lookup_insert_ne at 1 in H3.
               setoid_rewrite lookup_insert_ne at 1.
               all: auto.
           }
        eapply n_spawn; try eassumption.
        ** simpl in Spawns. clear -Spawns H H5 H6 H1 H3 H7.
           rename H into D.
           assert (ι'1 <> ι'0) as X. {
             intro. subst. apply H6. left.
             setoid_rewrite lookup_insert. by destruct_decide_eq.
           }
           intro. setoid_rewrite H3 in H6.
           apply H6. apply isUsedPool_insert_1 in H. destruct_or!.
           -- setoid_rewrite delete_insert_ne in H; auto.
              apply isUsedPool_insert_1 in H. destruct_or!.
              ++ apply isUsedPool_insert_2. left.
                 setoid_rewrite delete_delete in H.
                 by apply isUsedPool_remove_1 in H.
              ++ subst. left.
                 setoid_rewrite lookup_insert. by destruct_decide_eq.
              ++ right. exists ι, p.
                 split. setoid_rewrite lookup_insert. by destruct_decide_eq.
                 clear -D H. inv D; simpl in *; try set_solver.
                 unfold union_set in H. apply elem_of_union_list in H.
                 destruct_hyps. apply elem_of_elements in H.
                 apply elem_of_map_to_set in H. destruct_hyps.
                 apply lookup_delete_Some in H. destruct_hyps. subst.
                 apply elem_of_union_list. exists ({[x0]} ∪ usedPIDsVal x1).
                 split. 2: set_solver.
                 apply elem_of_elements, elem_of_map_to_set. exists x0, x1. by split.
           -- congruence.
           -- rewrite <- H3. right. exists ι'0, p0. split. setoid_rewrite lookup_insert.
              by destruct_decide_eq. assumption.
        ** (* in this case, the pool includes the given PID *)
           intro. apply appearsEther_etherAdd_rev in H0; try congruence.
           -- intro. subst. 
              apply H6. rewrite H3. left. setoid_rewrite lookup_insert. by destruct_decide_eq.
           -- intro. apply H6. rewrite H3. right.
              exists ι, p. split. setoid_rewrite lookup_insert. by destruct_decide_eq.
              clear -H2 H. inv H; simpl. 1-4: set_solver.
              apply elem_of_union_list. simpl in *.
              exists ({[ι']} ∪ usedPIDsVal reason). split. 2: set_solver.
              apply elem_of_elements, elem_of_map_to_set. exists ι', reason. by split.
      + destruct (decide (ι = ι'1)). {
          exfalso. subst.
          apply map_eq_iff with (i := ι'1) in H3.
          setoid_rewrite lookup_insert in H3. do 2 destruct_decide_eq.
          apply H6. left.
          setoid_rewrite lookup_insert_ne; auto. congruence.
        }
        setoid_rewrite insert_insert with (j := ι). destruct_decide_eq.
        setoid_rewrite insert_insert with (j := ι). destruct_decide_eq.
        replace (ι'1 ↦ inl ([], r, emptyBox, if link_flag then {[ι'0]} else ∅, false) ∥ ι'0 ↦ p'0 ∥ Π) with
          (ι ↦ p ∥ ι'1 ↦ inl ([], r, emptyBox, if link_flag then {[ι'0]} else ∅, false) ∥ ι'0 ↦ p'0 ∥ prs).
        2: { apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H3.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1. destruct_decide_eq.
               setoid_rewrite lookup_insert in H3. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H3 at 2; auto.
               destruct (decide (ι'' = ι'1)).
               - subst.
                 setoid_rewrite lookup_insert; auto. by destruct_decide_eq.
               - setoid_rewrite lookup_insert_ne; auto.
                 destruct (decide (ι'' = ι'0)).
                 + subst. setoid_rewrite lookup_insert. by destruct_decide_eq.
                 + setoid_rewrite lookup_insert_ne in H3; auto.
                   setoid_rewrite lookup_insert_ne; auto.
           }
        now constructor.
  * inv H1.
    - exists (etherAdd ι' ι'0 t0 ether', ι' ↦ p'0 ∥ ι ↦ p' ∥ prs).
      split.
      + replace (ι ↦ p' ∥ prs) with (ι' ↦ p0 ∥ ι ↦ p' ∥ prs) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H5.
             destruct (decide (ι'' = ι')).
             * subst. setoid_rewrite lookup_insert at 1. destruct_decide_eq.
               setoid_rewrite lookup_insert in H5. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne. all: auto.
             * setoid_rewrite lookup_insert_ne at 1 in H5.
               setoid_rewrite lookup_insert_ne at 1.
               all: auto.
           }
        now constructor.
      + setoid_rewrite insert_insert. destruct_decide_eq.
        replace (ι' ↦ p'0 ∥ prs0) with (ι ↦ p ∥ ι' ↦ p'0 ∥ prs) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H5.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1. destruct_decide_eq.
               setoid_rewrite lookup_insert in H5. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H5 at 2; auto.
               destruct (decide (ι'' = ι')).
               - subst.
                 setoid_rewrite lookup_insert; auto. by destruct_decide_eq.
               - setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in H5; auto.
           }
        constructor; auto.
        now apply etherPop_etherAdd.
    - assert (exists ether'', etherPop ι2 ι' ether'  = Some (t0, ether''))
                                 as [ether'' Eq].
      {
         unfold etherPop in H, H5. do 2 break_match_hyp; try congruence.
         break_match_hyp. 2: congruence.
         inv Heql0. destruct l1; try congruence. inv H.
         unfold etherPop. setoid_rewrite lookup_insert_ne. 2: intro D; inv D; auto.
         setoid_rewrite Heqo. eexists. reflexivity.
      }
      exists (ether'', ι' ↦ p'0 ∥ ι ↦ p' ∥ prs ).
      split.
      + replace (ι ↦ p' ∥ prs) with (ι' ↦ p0 ∥ ι ↦ p' ∥ prs) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H4.
             destruct (decide (ι'' = ι')).
             * subst. setoid_rewrite lookup_insert at 1. destruct_decide_eq.
               setoid_rewrite lookup_insert in H4. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne. all: auto.
             * setoid_rewrite lookup_insert_ne at 1 in H4.
               setoid_rewrite lookup_insert_ne at 1.
               all: auto.
           }
        constructor; auto.
      + setoid_rewrite insert_insert. destruct_decide_eq.
        replace (ι' ↦ p'0 ∥ prs0) with (ι ↦ p ∥ ι' ↦ p'0 ∥ prs) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H4.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1. destruct_decide_eq.
               setoid_rewrite lookup_insert in H4. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H4 at 2; auto.
               destruct (decide (ι'' = ι')).
               - subst.
                 setoid_rewrite lookup_insert; auto. by destruct_decide_eq.
               - setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in H4; auto.
           }
        constructor; auto.
        clear -H H5 H2 Eq. unfold etherPop in *.
        repeat break_match_hyp; try congruence. do 3 invSome.
        setoid_rewrite lookup_insert_ne. 2: intro D; inv D; auto.
        setoid_rewrite Heqo1. do 2 f_equal.
        setoid_rewrite insert_insert at 1. destruct_decide_eq. f_equal.
        setoid_rewrite lookup_insert_ne in Heqo. 2: intro D; inv D; auto.
        setoid_rewrite Heqo in Heqo0. now inv Heqo0.
    - exists (ether', ι' ↦ p'0 ∥ ι ↦ p' ∥ prs).
      split.
      + replace (ι ↦ p' ∥ prs) with (ι' ↦ p0 ∥ ι ↦ p' ∥ prs) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H4.
             destruct (decide (ι'' = ι')).
             * subst. setoid_rewrite lookup_insert at 1. destruct_decide_eq.
               setoid_rewrite lookup_insert in H4. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne. all: auto.
             * setoid_rewrite lookup_insert_ne at 1 in H4.
               setoid_rewrite lookup_insert_ne at 1.
               all: auto.
           }
        now constructor.
      + setoid_rewrite insert_insert. destruct_decide_eq.
        replace (ι' ↦ p'0 ∥ Π) with (ι ↦ p ∥ ι' ↦ p'0 ∥ prs) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H4.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1.
               setoid_rewrite lookup_insert in H4. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H4 at 2; auto.
               destruct (decide (ι'' = ι')).
               - subst.
                 setoid_rewrite lookup_insert; auto. by destruct_decide_eq.
               - setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in H4; auto.
           }
        now apply n_arrive.
    - exists (ether', ι'0 ↦ inl ([],r, emptyBox, if link_flag then {[ι']} else ∅, false) ∥ ι' ↦ p'0 ∥ ι ↦ p' ∥ prs).
      split.
      + replace (ι ↦ p' ∥ prs) with (ι' ↦ p0 ∥ ι ↦ p' ∥ prs) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H4.
             destruct (decide (ι'' = ι')).
             * subst. setoid_rewrite lookup_insert at 1. destruct_decide_eq.
               setoid_rewrite lookup_insert in H4. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne. all: auto.
             * setoid_rewrite lookup_insert_ne at 1 in H4.
               setoid_rewrite lookup_insert_ne at 1.
               all: auto.
           }
        eapply n_spawn; eauto.
        ** clear -H H0 H6 H7 H2 H4 H8.
           rename H into Heth.
           rename H0 into D.
           assert (ι'0 ≠ ι') as X. {
             intro. subst.
             apply H7. left. setoid_rewrite lookup_insert. by destruct_decide_eq.
           }
           intro.
           apply isUsedPool_insert_1 in H. destruct_or!.
           -- setoid_rewrite delete_insert_ne in H.
              apply isUsedPool_insert_1 in H. destruct_or!.
              ++ apply H7. rewrite H4. setoid_rewrite delete_delete in H. apply isUsedPool_insert_2.
                 left. by apply isUsedPool_remove_1 in H.
              ++ apply H7. rewrite H4. subst. left. setoid_rewrite lookup_insert.
                 by destruct_decide_eq.
              ++ (* Check whether ι'0 came from the ether: *)
                 destruct (decide (ι'0 ∈ usedPIDsProc p)). {
                    apply H7. rewrite H4. right.
                    exists ι, p. split; auto. setoid_rewrite lookup_insert.
                    by destruct_decide_eq.
                 }
                 clear -n H H4 H8 D Heth.
                 inv D; simpl in *; try rewrite flat_union_app in *; simpl in *.
                 2: set_solver.
                 *** destruct (decide (ι'0 ∈ usedPIDsVal v)). 2: set_solver.
                     apply H8. right. right. exists ι1, ι.
                     clear -Heth e0. unfold etherPop in Heth.
                     repeat case_match; try congruence.
                     exists l. subst. split; auto. simpl.
                     inv Heth. set_solver.
                 (* for links: *)
                 *** apply not_elem_of_union in n as [n _].
                     apply not_elem_of_union in n as [n _].
                     apply not_elem_of_union in n as [_ n].
                     apply elem_of_union_list in H. destruct_hyps.
                     apply elem_of_elements, elem_of_map_to_set in H. destruct_hyps.
                     subst.
                     rewrite lookup_gset_to_gmap in H. unfold guard in H.
                     case_match; clear H1; inv H.
                     apply elem_of_union in H0 as [|]. set_solver.
                     apply H8. do 2 right. exists ι1, ι.
                     unfold etherPop in Heth. repeat case_match; try congruence.
                     eexists. split. reflexivity. simpl. inv Heth. set_solver.
                 *** destruct (decide (ι'0 = ι1)).
                     2: destruct (decide (ι'0 ∈ usedPIDsVal reason)).
                     3: { clear-n0 n1 n H. set_solver. }
                     {
                       subst. apply H8. right. left. exists ι.
                       clear-Heth. unfold etherPop in Heth.
                       repeat case_match; try congruence.
                     }
                     {
                       apply H8. right. right. exists ι1, ι.
                       clear -Heth e0. unfold etherPop in Heth.
                       repeat case_match; try congruence.
                       exists l. subst. split; auto. simpl.
                       inv Heth. set_solver.
                     }
                 *** destruct (decide (ι'0 = ι1)). 2: set_solver.
                     subst. apply H8. right. left. exists ι.
                     clear-Heth. unfold etherPop in Heth.
                     repeat case_match; try congruence.
                 *** clear -H n. apply n. clear n. set_solver.
              ++ intro. subst. congruence.
           -- congruence.
           -- apply H7. right. exists ι', p0. split. setoid_rewrite lookup_insert.
              by destruct_decide_eq.
              assumption.
        ** intro. cbn in Spawns.
           apply H8. eapply appearsEther_etherPop_rev. exact H1.
           eassumption.
      + assert (ι <> ι'0). {
          apply map_eq_iff with (i := ι) in H4.
          setoid_rewrite lookup_insert in H4. do 2 destruct_decide_eq.
          intro. subst.
          apply H7. left.
          setoid_rewrite lookup_insert_ne; auto. congruence.
        }
        setoid_rewrite insert_insert with (j := ι). destruct_decide_eq.
        setoid_rewrite insert_insert with (j := ι). destruct_decide_eq.
        replace (ι'0 ↦ inl ([], r, emptyBox, if link_flag then {[ι']} else ∅, false) ∥ ι' ↦ p'0 ∥ Π) with
          (ι ↦ p ∥ ι'0 ↦ inl ([], r, emptyBox, if link_flag then {[ι']} else ∅, false) ∥ ι' ↦ p'0 ∥ prs).
        2: { apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H4.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1. destruct_decide_eq.
               setoid_rewrite lookup_insert in H4. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H4 at 2; auto.
               destruct (decide (ι'' = ι'0)).
               - subst.
                 setoid_rewrite lookup_insert; auto. destruct_decide_eq.
               - setoid_rewrite lookup_insert_ne; auto.
                 destruct (decide (ι'' = ι')).
                 + subst. setoid_rewrite lookup_insert. by destruct_decide_eq.
                 + setoid_rewrite lookup_insert_ne in H4; auto.
                   setoid_rewrite lookup_insert_ne; auto.
           }
        now constructor.
  * inv H1.
    - exists (etherAdd ι' ι'0 t ether, ι' ↦ p'0 ∥ ι ↦ p' ∥ Π).
      split.
      + replace (ι ↦ p' ∥ Π) with (ι' ↦ p0 ∥ ι ↦ p' ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H5.
             destruct (decide (ι'' = ι')).
             * subst. setoid_rewrite lookup_insert at 1. destruct_decide_eq.
               setoid_rewrite lookup_insert in H5. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne. all: auto.
             * setoid_rewrite lookup_insert_ne at 1 in H5.
               setoid_rewrite lookup_insert_ne at 1.
               all: auto.
           }
        now constructor.
      + setoid_rewrite insert_insert. destruct_decide_eq.
        replace (ι' ↦ p'0 ∥ prs) with (ι ↦ p ∥ ι' ↦ p'0 ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H5.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1. destruct_decide_eq.
               setoid_rewrite lookup_insert in H5. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H5 at 2; auto.
               destruct (decide (ι'' = ι')).
               - subst.
                 setoid_rewrite lookup_insert; auto. by destruct_decide_eq.
               - setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in H5; auto.
           }
        now constructor.
    - exists (ether', ι' ↦ p'0 ∥ ι ↦ p' ∥ Π ).
      split.
      + replace (ι ↦ p' ∥ Π) with (ι' ↦ p0 ∥ ι ↦ p' ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H4.
             destruct (decide (ι'' = ι')).
             * subst.
               setoid_rewrite lookup_insert in H4. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert. do 2 destruct_decide_eq.
             * setoid_rewrite lookup_insert_ne at 1; auto.
           }
        constructor; auto.
      + setoid_rewrite insert_insert. destruct_decide_eq.
        replace (ι' ↦ p'0 ∥ prs) with (ι ↦ p ∥ ι' ↦ p'0 ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H4.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1. destruct_decide_eq.
               setoid_rewrite lookup_insert in H4. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H4 at 2; auto.
               destruct (decide (ι'' = ι')).
               - subst.
                 setoid_rewrite lookup_insert; auto. by destruct_decide_eq.
               - setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in H4; auto.
           }
        now constructor.
    - exists (ether, ι' ↦ p'0 ∥ ι ↦ p' ∥ Π).
      split.
      + replace (ι ↦ p' ∥ Π) with (ι' ↦ p0 ∥ ι ↦ p' ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H4.
             destruct (decide (ι'' = ι')).
             * subst.
               setoid_rewrite lookup_insert in H4. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert. do 2 destruct_decide_eq.
             * setoid_rewrite lookup_insert_ne at 1; auto.
           }
        now constructor.
      + setoid_rewrite insert_insert. destruct_decide_eq.
        replace (ι' ↦ p'0 ∥ Π0) with (ι ↦ p ∥ ι' ↦ p'0 ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H4.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1. destruct_decide_eq.
               setoid_rewrite lookup_insert in H4. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H4 at 2; auto.
               destruct (decide (ι'' = ι')).
               - subst.
                 setoid_rewrite lookup_insert; auto. by destruct_decide_eq.
               - setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in H4; auto.
           }
        now constructor.
    - exists (ether, ι'0 ↦ inl ([], r, emptyBox, if link_flag then {[ι']} else ∅, false) ∥ ι' ↦ p'0 ∥ ι ↦ p' ∥ Π).
      split.
      + replace (ι ↦ p' ∥ Π) with (ι' ↦ p0 ∥ ι ↦ p' ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H4.
             destruct (decide (ι'' = ι')).
             * subst.
               setoid_rewrite lookup_insert in H4. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert. do 2 destruct_decide_eq.
             * setoid_rewrite lookup_insert_ne at 1; auto.
           }
        eapply n_spawn; eauto.
        ** clear -H6 H7 H2 H4 H8 H0 H.
           assert (ι'0 ≠ ι') as X. {
             intro. subst. apply H7. left. setoid_rewrite lookup_insert.
             by destruct_decide_eq.
           }
           intro. apply isUsedPool_insert_1 in H1. destruct_or! H1.
           -- setoid_rewrite delete_insert_ne in H1; auto.
              apply isUsedPool_insert_1 in H1. destruct_or! H1.
              ++ setoid_rewrite delete_delete in H1.
                 apply isUsedPool_remove_1 in H1; auto.
                 rewrite H4 in H7.
                 apply H7. apply isUsedPool_insert_2; auto.
              ++ subst. apply H7. rewrite H4. left. setoid_rewrite lookup_insert.
                 by destruct_decide_eq.
              ++ eapply not_isUsedProc_step in H. 2: exact H1.
                 apply H7. rewrite H4. right. do 2 eexists.
                 split. setoid_rewrite lookup_insert. by destruct_decide_eq. assumption.
                 assert (ι <> ι'0) as X1. {
                   intro. subst. apply H7. rewrite H4.
                   left. setoid_rewrite lookup_insert.
                   by destruct_decide_eq.
                 }
                 destruct_or! H0; subst; simpl; clear -X1; set_solver.
           -- subst. congruence.
           -- apply H7. right. exists ι', p0. split. setoid_rewrite lookup_insert.
              by destruct_decide_eq.
              assumption.
      + assert (ι <> ι'0). {
          apply map_eq_iff with (i := ι) in H4.
          setoid_rewrite lookup_insert in H4. destruct_decide_eq.
          clear -H4 H7. destruct_decide_eq. apply elem_of_dom_2 in H4.
          apply not_isUsedPool_insert_1 in H7. set_solver.
        }
        setoid_rewrite insert_insert with (j := ι). destruct_decide_eq.
        setoid_rewrite insert_insert with (j := ι). destruct_decide_eq.
        replace (ι'0 ↦ inl ([], r, emptyBox, if link_flag then {[ι']} else ∅, false) ∥ ι' ↦ p'0 ∥ Π0) with
          (ι ↦ p ∥ ι'0 ↦ inl ([], r, emptyBox, if link_flag then {[ι']} else ∅, false) ∥ ι' ↦ p'0 ∥ Π).
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H4.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1. destruct_decide_eq.
               setoid_rewrite lookup_insert in H4. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H4 at 2; auto.
               destruct (decide (ι'' = ι'0)).
               - subst.
                 setoid_rewrite lookup_insert; auto. by destruct_decide_eq.
               - setoid_rewrite lookup_insert_ne; auto.
                 destruct (decide (ι'' = ι')).
                 + subst. setoid_rewrite lookup_insert. by destruct_decide_eq.
                 + setoid_rewrite lookup_insert_ne in H4; auto.
                   setoid_rewrite lookup_insert_ne; auto.
           }
        now constructor.
  * inv H5.
    - exists (etherAdd ι'0 ι'1 t ether, ι'0 ↦ p'0 ∥
                                        ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false) ∥
                                        ι ↦ p' ∥ Π).
      split.
      + replace (ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false) ∥ ι ↦ p' ∥ Π) with 
                (ι'0 ↦ p0 ∥ ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false) ∥ ι ↦ p' ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H9.
             destruct (decide (ι'' = ι'0)).
             * subst.
               setoid_rewrite lookup_insert in H9. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert.
               destruct (decide (ι'0 = ι')).
               - subst. apply not_isUsedPool_insert_1 in H1 as [? _].
                 apply not_elem_of_dom in H1. congruence.
               - do 2 destruct_decide_eq. setoid_rewrite lookup_insert_ne.
                 all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
           }
        constructor; now eauto.
      + assert (ι'0 <> ι'). {
          apply map_eq_iff with (i := ι') in H9.
          setoid_rewrite lookup_insert_ne at 2 in H9. 2: by apply not_isUsedPool_insert_1 in H1 as [_ ?].
          destruct (decide (ι'0 = ι')); auto. subst.
          setoid_rewrite lookup_insert in H9.
          clear -H9 H1. apply not_isUsedPool_insert_1 in H1 as [? _].
          apply not_elem_of_dom in H. by destruct_decide_eq.
        }
        setoid_rewrite insert_insert with (j := ι'). destruct_decide_eq.
        setoid_rewrite insert_insert with (j := ι). destruct_decide_eq.
        replace (ι'0 ↦ p'0 ∥ prs) with
          (ι ↦ p ∥ ι'0 ↦ p'0 ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H9.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1. destruct_decide_eq.
               setoid_rewrite lookup_insert in H9. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne; auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H9 at 2; auto.
               destruct (decide (ι'' = ι'0)).
               - subst.
                 setoid_rewrite lookup_insert; auto. by destruct_decide_eq.
               - setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in H9; auto.
           }
         eapply n_spawn; eauto.
        ** simpl in *.
           clear H3.
           assert (ι' <> ι) as X. {
             intro. subst. apply H1. left.
             setoid_rewrite lookup_insert. by destruct_decide_eq.
           }
           intro.
           apply H1. apply isUsedPool_insert_1 in H3. destruct_or!.
           -- setoid_rewrite delete_insert_ne in H3; auto.
              apply isUsedPool_insert_1 in H3. destruct_or!.
              ++ apply isUsedPool_insert_2. left.
                 by apply isUsedPool_remove_1 in H3.
              ++ subst. congruence.
              ++ right. rewrite <- H9. exists ι'0, p0.
                 split. setoid_rewrite lookup_insert. by destruct_decide_eq.
                 clear -H12 H3. inv H12; simpl in *. 1-4: set_solver.
                 apply elem_of_union_list in H3. destruct_hyps.
                 apply elem_of_elements, elem_of_map_to_set in H. destruct_hyps. subst.
                 apply lookup_delete_Some in H as [? ?].
                 apply elem_of_union_list. exists ({[x0]} ∪ usedPIDsVal x1).
                 split. 2: set_solver.
                 apply elem_of_elements, elem_of_map_to_set.
                 exists x0, x1. by split.
           -- congruence.
           -- right. exists ι, p. split. setoid_rewrite lookup_insert. by destruct_decide_eq.
              assumption.
        ** intro. apply appearsEther_etherAdd_rev in H7; try by auto.
           intro. rewrite <- H9 in H1. apply H1.
           right. exists ι'0, p0. split. setoid_rewrite lookup_insert. by destruct_decide_eq.
           clear -H8 H12. inv H12; simpl in *. 1-4: set_solver.
           apply elem_of_union_list. exists ({[ι'1]} ∪ usedPIDsVal reason). split. 2: set_solver.
      apply elem_of_elements, elem_of_map_to_set.
      exists ι'1, reason. by split.
    - exists (ether', ι'0 ↦ p'0 ∥ ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false) 
                          ∥ ι ↦ p' ∥ Π ).
      split.
      + replace (ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false) ∥ ι ↦ p' ∥ Π) with 
                (ι'0 ↦ p0 ∥ ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false) ∥ ι ↦ p' ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H8.
             destruct (decide (ι'' = ι'0)).
             * subst.
               setoid_rewrite lookup_insert in H8. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert. do 2 destruct_decide_eq.
               - subst. exfalso.
                 apply H1. left. setoid_rewrite lookup_insert_ne; auto.
                 congruence.
               - setoid_rewrite lookup_insert_ne.
                 all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
           }
        constructor; auto.
      + assert (ι'0 <> ι'). {
          apply map_eq_iff with (i := ι') in H8.
          setoid_rewrite lookup_insert_ne at 2 in H8. 2: by apply not_isUsedPool_insert_1 in H1 as [_ ?].
          destruct (decide (ι'0 = ι')); auto. subst.
          setoid_rewrite lookup_insert in H8.
          clear -H8 H1. apply not_isUsedPool_insert_1 in H1 as [? _].
          apply not_elem_of_dom in H. by destruct_decide_eq.
        }
        setoid_rewrite insert_insert with (j := ι'). destruct_decide_eq.
        setoid_rewrite insert_insert with (j := ι). destruct_decide_eq.
        replace (ι'0 ↦ p'0 ∥ prs) with
          (ι ↦ p ∥ ι'0 ↦ p'0 ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H8.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1. destruct_decide_eq.
               setoid_rewrite lookup_insert in H8. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne; auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H8 at 2; auto.
               destruct (decide (ι'' = ι'0)).
               - subst.
                 setoid_rewrite lookup_insert; auto. by destruct_decide_eq.
               - setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in H8; auto.
           }
         eapply n_spawn; eauto.
         ** rename H9 into Heth.
           rename H13 into D.
           assert (ι ≠ ι') as X. {
             intro. subst.
             apply H1. left. setoid_rewrite lookup_insert. by destruct_decide_eq.
           }
           intro.
           apply isUsedPool_insert_1 in H7. destruct_or!.
           -- setoid_rewrite delete_insert_ne in H7.
              apply isUsedPool_insert_1 in H7. destruct_or!.
              ++ apply H1. apply isUsedPool_insert_2.
                 left. by apply isUsedPool_remove_1 in H7.
              ++ congruence.
              ++ (* Check whether ι' came from the ether: *)
                 destruct (decide (ι' ∈ usedPIDsProc p0)). {
                    apply H1. rewrite <- H8. right.
                    exists ι'0, p0. split; auto. setoid_rewrite lookup_insert.
                    by destruct_decide_eq.
                 }
                 inv D; simpl in *; try rewrite flat_union_app in *; simpl in *.
                 *** destruct (decide (ι' ∈ usedPIDsVal v)). 2: set_solver.
                     apply H2. right. right. exists ι1, ι'0.
                     clear -Heth e0. unfold etherPop in Heth.
                     repeat case_match; try congruence.
                     exists l. subst. split; auto. simpl.
                     inv Heth. set_solver.
                 (* for links: *)
                 *** apply not_elem_of_union in n1 as [n1 _].
                     apply not_elem_of_union in n1 as [n1 _].
                     apply not_elem_of_union in n1 as [_ n1].
                     apply elem_of_union_list in H7. destruct_hyps.
                     apply elem_of_elements, elem_of_map_to_set in H7. destruct_hyps.
                     subst.
                     rewrite lookup_gset_to_gmap in H7. unfold guard in H7.
                     case_match; clear H10 H3; inv H7.
                     apply elem_of_union in H9 as [|]. set_solver.
                     apply H2. do 2 right. exists ι1, ι'0.
                     unfold etherPop in Heth. repeat case_match; try congruence.
                     eexists. split. reflexivity. simpl. inv Heth. set_solver.
                 *** destruct (decide (ι' = ι1)).
                     2: destruct (decide (ι' ∈ usedPIDsVal reason)).
                     3: { clear-n0 n1 n2 n3 n H7. set_solver. }
                     {
                       subst. apply H2. right. left. exists ι'0.
                       clear-Heth. unfold etherPop in Heth.
                       repeat case_match; try congruence.
                     }
                     {
                       apply H2. right. right. exists ι1, ι'0.
                       clear -Heth e0. unfold etherPop in Heth.
                       repeat case_match; try congruence.
                       exists l. subst. split; auto. simpl.
                       inv Heth. set_solver.
                     }
                 *** destruct (decide (ι' = ι1)). 2: set_solver.
                     subst. apply H2. right. left. exists ι'0.
                     clear-Heth. unfold etherPop in Heth.
                     repeat case_match; try congruence.
                 *** set_solver.
              ++ intro. subst. congruence.
           -- congruence.
           -- apply H1. right. exists ι, p. split. setoid_rewrite lookup_insert.
              by destruct_decide_eq.
              assumption.
         ** intro. eapply appearsEther_etherPop_rev in H9. 2: eassumption.
            congruence.
    - exists (ether, ι'0 ↦ p'0 ∥ ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false)
                               ∥ ι ↦ p' ∥ Π).
      split.
      + replace (ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false) ∥ ι ↦ p' ∥ Π) with 
                (ι'0 ↦ p0 ∥ ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false) ∥ ι ↦ p' ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H8.
             destruct (decide (ι'' = ι'0)).
             * subst.
               setoid_rewrite lookup_insert in H8. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert. do 2 destruct_decide_eq.
               - subst.
                 exfalso.
                 apply H1. left.
                 setoid_rewrite lookup_insert_ne; auto. congruence.
               - setoid_rewrite lookup_insert_ne.
                 all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
           }
        now constructor.
      + assert (ι'0 <> ι'). {
          apply map_eq_iff with (i := ι') in H8.
          setoid_rewrite lookup_insert_ne at 2 in H8. 2: by apply not_isUsedPool_insert_1 in H1 as [_ ?].
          destruct (decide (ι'0 = ι')); auto. subst.
          setoid_rewrite lookup_insert in H8.
          clear -H8 H1. apply not_isUsedPool_insert_1 in H1 as [? _].
          apply not_elem_of_dom in H. by destruct_decide_eq.
        }
        setoid_rewrite insert_insert with (j := ι'). destruct_decide_eq.
        setoid_rewrite insert_insert with (j := ι). destruct_decide_eq.
        replace (ι'0 ↦ p'0 ∥ Π0) with
          (ι ↦ p ∥ ι'0 ↦ p'0 ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H8.
             destruct (decide (ι'' = ι)).
             * subst.
               setoid_rewrite lookup_insert in H8. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert. do 2 destruct_decide_eq.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               destruct (decide (ι'' = ι'0)).
               - subst.
                 setoid_rewrite lookup_insert; auto. by destruct_decide_eq.
               - setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in H8; auto.
           }
         eapply n_spawn; eauto.
         ** assert (ι ≠ ι') as X. {
             intro. subst. apply H1. left. setoid_rewrite lookup_insert. by destruct_decide_eq.
           }
           intro. apply isUsedPool_insert_1 in H7. destruct_or! H7.
           -- setoid_rewrite delete_insert_ne in H7; auto.
              apply isUsedPool_insert_1 in H7. destruct_or! H7.
              ++ apply isUsedPool_remove_1 in H7; auto.
                 apply H1. apply isUsedPool_insert_2; auto.
              ++ congruence.
              ++ eapply not_isUsedProc_step in H9. 2: exact H7.
                 apply H1. rewrite <- H8. right. do 2 eexists.
                 split. setoid_rewrite lookup_insert. by destruct_decide_eq. assumption.
                 destruct_or! H13; subst; simpl; clear -H5; set_solver.
           -- subst. congruence.
           -- apply H1. right. exists ι, p. split. setoid_rewrite lookup_insert. by destruct_decide_eq.
              assumption.
    - (** cannot be sure to generate different spawn PID-s *)
      exists (ether, ι'1 ↦ inl ([], r0, emptyBox, if link_flag0 then {[ι'0]} else ∅, false) ∥ ι'0 ↦ p'0 ∥ ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false) ∥ ι ↦ p' ∥ Π).
      assert (ι'0 ≠ ι') as X1. {
        intro. subst. apply H1. rewrite <- H8. left. setoid_rewrite lookup_insert.
        by destruct_decide_eq.
      }
      assert (ι'1 ≠ ι') as X2. {
        intro. subst. simpl in Spawns. congruence.
      }
      assert (ι'1 ≠ ι) as X3. {
        intro. subst. apply H11. rewrite H8. left. setoid_rewrite lookup_insert.
        by destruct_decide_eq.
      }
      assert (ι'1 ≠ ι'0) as X4. {
        intro. subst. apply H11. left. setoid_rewrite lookup_insert. by destruct_decide_eq.
      }
      assert (ι' ≠ ι) as X5. {
        intro. subst. apply H1. left. setoid_rewrite lookup_insert. by destruct_decide_eq.
      }
      split.
      + replace (ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false) ∥ ι ↦ p' ∥ Π) with
                (ι'0 ↦ p0 ∥ ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false) ∥ ι ↦ p' ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H8.
             destruct (decide (ι'' = ι'0)).
             * subst.
               setoid_rewrite lookup_insert in H8. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert.
               destruct (decide (ι'0 = ι')).
               - subst. exfalso.
                 apply H1. left.
                 setoid_rewrite lookup_insert_ne; auto.
               - do 2 destruct_decide_eq. setoid_rewrite lookup_insert_ne.
                 all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
           }
        eapply n_spawn; try eassumption.
        intro. apply isUsedPool_insert_1 in H5. destruct_or!.
        ** setoid_rewrite delete_insert_ne in H5; auto.
           apply isUsedPool_insert_1 in H5. destruct_or!.
           -- setoid_rewrite delete_insert_ne in H5; auto.
              setoid_rewrite delete_insert_ne in H5; auto.
              apply isUsedPool_insert_1 in H5. destruct_or!.
              ++ apply H11. rewrite H8. apply isUsedPool_insert_2. left.
                 setoid_rewrite delete_delete in H5; auto.
                 apply isUsedPool_remove_1 in H5; auto.
                 setoid_rewrite delete_delete in H5; auto.
                 apply isUsedPool_remove_1 in H5; auto.
              ++ congruence.
              ++ apply H11. rewrite H8.
                 right. exists ι, p. split.
                 1: by setoid_rewrite lookup_insert; destruct_decide_eq.
                 clear -H5 X2 H4. inv H4; simpl in *; set_solver.
           -- congruence.
           -- cbn in H5. apply H11. rewrite H8. right.
              exists ι, p. split. setoid_rewrite lookup_insert. by destruct_decide_eq.
              clear -H5 H4 H3 H X2 X3. inv H4.
              { (* spawn *)
                simpl in *.
                case_match; inv H3.
                ++ simpl in *.
                   do 3 rewrite union_empty_r_L in H5.
                   rewrite union_empty_l_L in H5.
                   apply subst_usedPIDs in H5 as [|]. set_solver.
                   destruct_hyps. apply list_subst_idsubst_inl in H1.
                   apply elem_of_app in H1 as [|].
                   *** apply elem_of_map_iff in H1. destruct_hyps. destruct x1, p.
                       subst. simpl in *. apply elem_of_union in H2 as [|]. 2: set_solver.
                       assert (ι'1 ∈ flat_union (λ x0 : nat * nat * Exp, usedPIDsExp x0.2) ext). {
                         apply elem_of_flat_union. eexists. split. exact H3.
                         assumption.
                       }
                       set_solver.
                   *** epose proof (proj2 (mk_list_usedPIDs _ ι'1 _ H) _).
                       set_solver.
                       Unshelve. apply elem_of_flat_union. eexists; split; eassumption.
                ++ simpl in *.
                   pose proof meta_to_cons_usedPIDs l as Hmeta.
                   pose proof mk_list_usedPIDs _ ι'1 _ H. set_solver.
              }
              { (* spawn_link *)
                simpl in *.
                case_match; inv H3.
                ++ simpl in *.
                   do 2 rewrite union_empty_r_L in H5.
                   rewrite union_empty_l_L in H5.
                   assert (ι'1 ∈ usedPIDsExp e.[list_subst (convert_to_closlist ext ++ l) idsubst]) as H5' by set_solver.
                   apply subst_usedPIDs in H5' as [|]. set_solver.
                   destruct_hyps. apply list_subst_idsubst_inl in H1.
                   apply elem_of_app in H1 as [|].
                   *** apply elem_of_map_iff in H1. destruct_hyps. destruct x1, p.
                       subst. simpl in *. apply elem_of_union in H2 as [|]. 2: set_solver.
                       assert (ι'1 ∈ flat_union (λ x0 : nat * nat * Exp, usedPIDsExp x0.2) ext). {
                         apply elem_of_flat_union. eexists. split. exact H3.
                         assumption.
                       }
                       set_solver.
                   *** epose proof (proj2 (mk_list_usedPIDs _ ι'1 _ H) _).
                       set_solver.
                       Unshelve. apply elem_of_flat_union. eexists; split; eassumption.
                ++ simpl in *.
                   pose proof meta_to_cons_usedPIDs l as Hmeta.
                   pose proof mk_list_usedPIDs _ ι'1 _ H. set_solver.
              }
        ** congruence.
        ** apply H11. right. exists ι'0, p0. split. setoid_rewrite lookup_insert. by destruct_decide_eq.
           assumption.
      + setoid_rewrite insert_insert with (j := ι'). destruct_decide_eq.
        setoid_rewrite insert_insert with (j := ι'). destruct_decide_eq.
        setoid_rewrite insert_insert with (j := ι). destruct_decide_eq.
        setoid_rewrite insert_insert with (j := ι). destruct_decide_eq.
        replace (ι'1 ↦ inl ([], r0, emptyBox, if link_flag0 then {[ι'0]} else ∅, false) ∥ ι'0 ↦ p'0 ∥ Π0) with
          (ι ↦ p ∥ ι'1 ↦ inl ([], r0, emptyBox, if link_flag0 then {[ι'0]} else ∅, false) ∥ ι'0 ↦ p'0 ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H8.
             destruct (decide (ι'' = ι)).
             * subst.
               setoid_rewrite lookup_insert in H8. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert. do 2 destruct_decide_eq.
               setoid_rewrite lookup_insert_ne; auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               destruct (decide (ι'' = ι'1)).
               - subst.
                 setoid_rewrite lookup_insert; auto. destruct_decide_eq.
               - setoid_rewrite lookup_insert_ne; auto.
                 destruct (decide (ι'' = ι'0)).
                 + subst.
                   setoid_rewrite lookup_insert; auto. by destruct_decide_eq.
                 + setoid_rewrite lookup_insert_ne in H8; auto.
                   setoid_rewrite lookup_insert_ne; auto.
           }
         eapply n_spawn; eauto.
         intro. apply isUsedPool_insert_1 in H5. destruct_or!.
          ** setoid_rewrite delete_insert_ne in H5; auto.
             apply isUsedPool_insert_1 in H5. destruct_or!.
             -- setoid_rewrite delete_insert_ne in H5; auto.
                setoid_rewrite delete_insert_ne in H5; auto.
                apply isUsedPool_insert_1 in H5. destruct_or!.
                ++ apply H1. apply isUsedPool_insert_2. left.
                   apply isUsedPool_remove_1 in H5; auto.
                   apply isUsedPool_remove_1 in H5; auto.
                ++ congruence.
                ++ apply H1. rewrite <- H8.
                   right. exists ι'0, p0. split.
                   1: by setoid_rewrite lookup_insert; destruct_decide_eq.
                   clear -H5 X2 H17. inv H17; simpl in *; set_solver.
             -- congruence.
             -- cbn in H5. apply H1. rewrite <- H8. right.
                exists ι'0, p0. split. by setoid_rewrite lookup_insert; destruct_decide_eq.
                clear -H5 H17 H13 H9 X2 X1. inv H17. 
                { (* spawn *)
                  simpl in *.
                  case_match; inv H13.
                  ++ simpl in *.
                     do 3 rewrite union_empty_r_L in H5.
                     rewrite union_empty_l_L in H5.
                     apply subst_usedPIDs in H5 as [|]. set_solver.
                     destruct_hyps. apply list_subst_idsubst_inl in H0.
                     apply elem_of_app in H0 as [|].
                     *** apply elem_of_map_iff in H0. destruct_hyps. destruct x1, p.
                         subst. simpl in *. apply elem_of_union in H1 as [|]. 2: set_solver.
                         assert (ι' ∈ flat_union (λ x0 : nat * nat * Exp, usedPIDsExp x0.2) ext). {
                           apply elem_of_flat_union. eexists. split. exact H2.
                           assumption.
                         }
                         set_solver.
                     *** epose proof (proj2 (mk_list_usedPIDs _ ι' _ H9) _).
                         set_solver.
                         Unshelve. apply elem_of_flat_union. eexists; split; eassumption.
                  ++ simpl in *.
                     pose proof meta_to_cons_usedPIDs l0 as Hmeta.
                     pose proof mk_list_usedPIDs _ ι' _ H9. set_solver.
                }
                { (* spawn_link *)
                  simpl in *.
                  case_match; inv H13.
                  ++ simpl in *.
                     do 2 rewrite union_empty_r_L in H5.
                     rewrite union_empty_l_L in H5.
                     assert (ι' ∈ usedPIDsExp e.[list_subst (convert_to_closlist ext ++ l0) idsubst]) as H5' by set_solver.
                     apply subst_usedPIDs in H5' as [|]. set_solver.
                     destruct_hyps. apply list_subst_idsubst_inl in H0.
                     apply elem_of_app in H0 as [|].
                     *** apply elem_of_map_iff in H0. destruct_hyps. destruct x1, p.
                         subst. simpl in *. apply elem_of_union in H1 as [|]. 2: set_solver.
                         assert (ι' ∈ flat_union (λ x0 : nat * nat * Exp, usedPIDsExp x0.2) ext). {
                           apply elem_of_flat_union. eexists. split. exact H2.
                           assumption.
                         }
                         set_solver.
                     *** epose proof (proj2 (mk_list_usedPIDs _ ι' _ H9) _).
                         set_solver.
                         Unshelve. apply elem_of_flat_union. eexists; split; eassumption.
                  ++ simpl in *.
                     pose proof meta_to_cons_usedPIDs l0 as Hmeta.
                     pose proof mk_list_usedPIDs _ ι' _ H9. set_solver.
                }
          ** congruence.
          ** apply H1. right. exists ι, p. split. by setoid_rewrite lookup_insert; destruct_decide_eq.
             assumption.
Qed.

(** * Further properties of composition and freshness *)

(** If inserting a process results in a union of two pools, then the process
    is in the left pool, or it is in the right pool and not in the left
    one. *)
Lemma insert_of_union :
  forall ι p Π Π2 prs,
  ι ↦ p ∥ prs = Π ∪ Π2 ->
  Π = ι ↦ p ∥ Π \/ ((ι ∉ dom Π) /\ Π2 = ι ↦ p ∥ Π2).
Proof.
  intros.
  put (lookup ι : ProcessPool -> _) on H as H'. simpl in H'.
  setoid_rewrite lookup_insert in H'.
  symmetry in H'. destruct_decide_eq.
  apply lookup_union_Some_raw in H'. destruct H' as [H' | [H_1 H_2]].
  * left. apply map_eq. intros.
    destruct (decide (i = ι)); subst.
    - by setoid_rewrite lookup_insert; destruct_decide_eq.
    - by setoid_rewrite lookup_insert_ne.
  * right. split. now apply not_elem_of_dom.
    apply map_eq. intros.
    destruct (decide (i = ι)); subst.
    - by setoid_rewrite lookup_insert; destruct_decide_eq.
    - by setoid_rewrite lookup_insert_ne.
Qed.

(** A step of a composed pool is a step of one of its components. This
    proof is not finished: it needs an additional condition on the domain of
    the right component. *)
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
      exists (ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false) ∥ ι ↦ p' ∥ Π).
      split. eapply n_spawn; eauto.
      {
        intro. apply H6.
        apply isUsedPool_insert_1 in H.
        apply isUsedPool_insert_2. destruct_or!.
        2-3: clear-H. 2: right; by left. 2: right; by right.
        left.
        destruct H.
        * left. intro. apply H.
          put (lookup ι' : ProcessPool -> option Process) on H1 as HL. simpl in HL.
          processpool_destruct.
          - by setoid_rewrite lookup_delete in H; destruct_decide_eq.
          - apply lookup_delete_None in H0 as [|]. congruence.
            setoid_rewrite H0 in HL. apply eq_sym, lookup_union_None in HL as [? ?].
            apply lookup_delete_None. by right.
        * destruct_hyps. right.
          put (lookup x : ProcessPool -> option Process) on H1 as HL. simpl in HL.
          setoid_rewrite lookup_delete_Some in H. destruct_hyps.
          processpool_destruct.
          setoid_rewrite lookup_union in HL.
          setoid_rewrite H2 in HL. rewrite union_Some_l in HL.
          exists x, x0. split. setoid_rewrite lookup_delete_Some. split; assumption.
          assumption.
      }
      {
        apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as H1''.
        simpl in *. do 2 rewrite par_comp_assoc_pool.
        repeat processpool_destruct; try congruence.
      }
    - inv H1'. setoid_rewrite H0. right. exists (ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false) ∥ ι ↦ p' ∥ Π2).
      split.
      {
        1: eapply n_spawn; eauto.
        rewrite H1 in H6. rewrite H0 in H6.
        setoid_rewrite <- insert_union_r in H6. 2: by apply not_elem_of_dom.
        intro X. destruct X.
        * apply H6; left. destruct (decide (ι = ι')).
          - subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          - setoid_rewrite lookup_insert_ne. 2: lia.
            setoid_rewrite lookup_insert_ne in H2. 2: lia.
            intro. apply H2.
            by apply lookup_union_None in H3 as [? ?].
        * (* destruct_hyps. apply H6.
          destruct (decide (x = ι)).
          - subst. setoid_rewrite lookup_insert in H2.
            inv H2. right. do 2 eexists.
            setoid_rewrite lookup_insert. split. reflexivity. assumption.
          - rewrite <- H0 in H2. apply not_isUsedPool_insert_1 in H6 as D.
            destruct D.
          
          
          
            setoid_rewrite lookup_insert_ne in H2. 2: lia.
            exists x, x0.
            setoid_rewrite lookup_insert_ne. 2: lia.
            split.
            setoid_rewrite lookup_union_r. 2: { apply not_elem_of_dom in H. *)
            admit. (* Additional condition is needed on the domain of Π2! *)
      }

      apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as H1''.
      simpl in *. repeat setoid_rewrite <- insert_union_r.
      2: now apply not_elem_of_dom.
      repeat processpool_destruct; try congruence.
      apply not_isUsedPool_insert_1 in H6 as [? ?].
      apply not_elem_of_dom.
      put (dom : ProcessPool -> gset PID) on H1 as H1'. simpl in H1'.
      clear -H1' H2 H3.
      setoid_rewrite dom_union_L in H1'. setoid_rewrite dom_insert_L in H1'.
      set_solver.
Abort.

(** Reduction sequences do not create processes with observed PIDs. *)
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

(** The spawned PIDs of an action log are among its used PIDs. *)
Lemma spawnPIDs_subset_all :
  forall l, list_to_set (PIDsOf spawnPIDOf l) ⊆ flat_union (fun '(a, ι) => {[ι]} ∪ usedPIDsAct a) l.
Proof.
  induction l; simpl; auto.
  destruct a; simpl in *. case_match; simpl.
  destruct a; inv H.
  cbn. set_solver.
  set_solver.
Qed.

(** The send targets of an action log are among its used PIDs. *)
Lemma sendPIDs_subset_all :
  forall l, list_to_set (PIDsOf sendPIDOf l) ⊆ flat_union (fun '(a, ι) => {[ι]} ∪ usedPIDsAct a) l.
Proof.
  induction l; simpl; auto.
  destruct a; simpl in *. case_match; simpl.
  destruct a; inv H.
  cbn. set_solver.
  set_solver.
Qed.

(** A PID which is fresh in a node (not used in the pool, not appearing in
    the ether, not observed) is not used by a step, except as the PID of a
    newly spawned process. *)
Lemma fresh_pid_is_not_in_step :
  forall O n n' a ι,
  n -[ a | ι ]ₙ-> n' with O ->
  (forall p',
    ¬ isUsedPool p' n.2 ->
    ¬ appearsEther p' n.1 ->
    p' ∉ O ->
   p' ∉ (usedPIDsAct a) \/ (exists v1 v2 f, a = ASpawn p' v1 v2 f /\ p' ∉ usedPIDsVal v1 ∪ usedPIDsVal v2)).
Proof.
  intros. inv H; simpl in *. 1-3: left; intro.
  * assert (p' = ι \/ (p' = ι' \/ p' ∈ usedPIDsSignal t)) by set_solver.
    destruct H4.
    - subst. apply H0. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
    - apply H0. clear -H3 H4.
      right. exists ι, p. split. by setoid_rewrite lookup_insert; destruct_decide_eq.
      inv H3; simpl in *. 1-4: set_solver.
      apply elem_of_union_list. exists ({[ι']} ∪ usedPIDsVal reason). split. 2: set_solver.
      apply elem_of_elements, elem_of_map_to_set.
      exists ι', reason. by split.
  * destruct (decide (ι = p')).
    - subst. apply H0. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
    - apply not_appearsEther_alt in H1. destruct_hyps.
      unfold etherPop in H3. case_match. 2: congruence.
      destruct l. 1: congruence.
      inv H3. destruct (decide (p' = ι1)).
      + subst. specialize (H5 ι). congruence.
      + apply H6 in H7. simpl in H7. set_solver.
  * destruct_or!; subst; simpl in *; try set_solver.
    apply H0. left. assert (p' = ι) by set_solver. subst.
    by setoid_rewrite lookup_insert; destruct_decide_eq.
  * destruct (decide (ι' = p')).
    - subst. right. do 3 eexists. split. reflexivity.
      intro. apply H0. right. exists ι, p. split. by setoid_rewrite lookup_insert; destruct_decide_eq.
      inv H8; set_solver.
    - left. intro.
      apply H0. right. exists ι, p. split. by setoid_rewrite lookup_insert; destruct_decide_eq.
      inv H8; simpl in *; clear-H n; set_solver.
Qed.

(** A PID which does not appear in the ether and is not used by the action
    does not appear in the ether after the step. *)
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
        ** inv e. setoid_rewrite lookup_insert in H. destruct_decide_eq. inv H.
           right. right. exists x, x0, l.
           split. assumption.
           rewrite flat_union_app in H3. set_solver.
        ** setoid_rewrite lookup_insert_ne in H; auto.
           right. right. exists x, x0, x1.
           split; assumption.
      + destruct (decide ((ι, ι'0) = (x, x0))).
        ** inv e. setoid_rewrite lookup_insert in H. destruct_decide_eq. inv H. set_solver.
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
      + inv e. setoid_rewrite lookup_insert in H2. destruct_decide_eq. inv H2.
        right. right. do 3 eexists. split. exact H.
        simpl. set_solver.
      + setoid_rewrite lookup_insert_ne in H2. 2: auto.
        right. right. do 3 eexists. split; eassumption.
Qed.

(** * Deciding the used PIDs *)

(** Decides whether a PID is used in a pool. *)
Definition usedInPool : PID -> ProcessPool -> bool :=
  fun pid prs =>
    if gset_elem_of_dec pid (allPIDsPool prs)
    then true
    else false.

(** Decides whether a PID appears in an ether. *)
Definition usedInEther : PID -> Ether -> bool :=
  fun pid eth =>
    if gset_elem_of_dec pid (allPIDsEther eth)
    then true
    else false.

(** `usedInEther` is false for PIDs that do not appear in the ether. *)
Lemma usedInEtherCorrect: forall ι' ether, ¬appearsEther ι' ether -> usedInEther ι' ether = false.
Proof.
  intros. unfold usedInEther. unfold appearsEther in H.
  destruct (gset_elem_of_dec ι' (allPIDsEther ether)); try auto.
  unfold allPIDsEther in e. unfold isTargetedEther in H.
  apply not_or_and in H. destruct H. apply not_or_and in H0. destruct H0.
  unfold flat_union in e.
  induction ether using map_first_key_ind.
  * setoid_rewrite map_to_list_empty in e. simpl in e. inv e.
  * assert ((map_to_list (<[i:=x]> m) = ((i, x) ::map_to_list m))).
    { apply map_to_list_insert_first_key; assumption. }
    setoid_rewrite H4 in e. clear H4. simpl in e.
    apply elem_of_union in e. destruct e.
    + destruct i. clear IHether. apply elem_of_union in H4. destruct H4.
      - apply elem_of_union in H4. destruct H4.
        ** apply elem_of_singleton in H4. subst ι'.
           apply not_ex_all_not with (n := p0) in H0.
           setoid_rewrite lookup_insert in H0. destruct_decide_eq. unfold not in H0.
           exfalso. apply H0. discriminate.
        ** apply elem_of_singleton in H4. subst ι'.
           apply not_ex_all_not with (n := p) in H.
           apply not_ex_all_not with (n := x) in H.
           setoid_rewrite lookup_insert in H. by destruct_decide_eq.
      - clear H H0.
        apply not_ex_all_not with (n := p) in H1.
        apply not_ex_all_not with (n := p0) in H1.
        apply not_ex_all_not with (n := x) in H1.
        setoid_rewrite lookup_insert in H1. destruct_decide_eq.
        apply not_and_or in H1. destruct H1; try congruence.
        unfold flat_union in H.
        contradiction.
    + apply IHether; try assumption.
      - clear -H H2.
        intros contra. destruct contra. destruct H0.
        apply not_ex_all_not with (n := x0) in H.
        apply not_ex_all_not with (n := x1) in H.
        destruct (decide (i = (x0, ι'))).
        ** subst i. setoid_rewrite H0 in H2. discriminate.
        ** setoid_rewrite (lookup_insert_ne _ _ _ _ n) in H.
           setoid_rewrite H0 in H. congruence.
      - clear -H0 H2.
        intros contra. destruct contra.
        apply not_ex_all_not with (n := x0) in H0.
        destruct (decide (i = (ι', x0))).
        ** subst i. apply H. assumption.
        ** setoid_rewrite (lookup_insert_ne _ _ _ _ n) in H0.
           apply H0 in H. assumption.
      - clear -H1 H2. intros contra. destruct contra. do 3 destruct H.
        apply H1. exists x0, x1, x2. split;[|assumption].
        destruct (decide (i = (x0, x1))).
        ** subst i. setoid_rewrite H2 in H. discriminate.
        ** setoid_rewrite (lookup_insert_ne _ _ _ _ n). assumption.
Qed.

(** PIDs for which `usedInEther` is false do not appear in the ether. *)
Lemma usedInEtherComplete: forall ι' ether, usedInEther ι' ether = false -> ¬appearsEther ι' ether.
Proof.
  intros. unfold usedInEther in H.
  destruct (gset_elem_of_dec ι' (allPIDsEther ether)); try discriminate.
  unfold allPIDsEther in n. clear H.
  unfold flat_union in n.
  unfold appearsEther. intros contra. destruct contra.
  + unfold isTargetedEther in H. destruct H, H.
    induction ether using map_first_key_ind.
    - inv H.
    - assert ((map_to_list (<[i:=x1]> m) = ((i, x1) ::map_to_list m))).
      { apply map_to_list_insert_first_key; assumption. }
      setoid_rewrite H2 in n. simpl in n. clear H2.
      setoid_rewrite elem_of_union in n.
      apply not_or_and in n. destruct n.
      apply IHether in H3; auto.
      clear IHether.
      destruct (decide (i = (x, ι'))).
      ** subst i.
         setoid_rewrite elem_of_union in H2.
         apply not_or_and in H2. destruct H2.
         setoid_rewrite elem_of_union in H2. apply not_or_and in H2. destruct H2.
         setoid_rewrite elem_of_singleton in H5. contradiction.
      ** setoid_rewrite (lookup_insert_ne _ _ _ _ n) in H. assumption. 
  + destruct H.
    - destruct H.
      induction ether using map_first_key_ind.
      ** setoid_rewrite lookup_empty in H. contradiction.
      ** assert ((map_to_list (<[i:=x0]> m) = ((i, x0) ::map_to_list m))).
         { apply map_to_list_insert_first_key; assumption. }
         setoid_rewrite H2 in n. simpl in n. clear H2.
         setoid_rewrite elem_of_union in n.
         apply not_or_and in n. destruct n.
         apply IHether in H3; auto.
         clear IHether.
         destruct (decide (i = (ι', x))).
         ++ subst i.
            setoid_rewrite elem_of_union in H2. apply not_or_and in H2. destruct H2.
            setoid_rewrite elem_of_union in H2. apply not_or_and in H2. destruct H2.
            setoid_rewrite elem_of_singleton in H2. contradiction.
         ++ setoid_rewrite (lookup_insert_ne _ _ _ _ n) in H. assumption.
    - destruct H, H, H, H.
      unfold flat_union in H0.
      induction ether using map_first_key_ind.
      ** inv H.
      ** assert ((map_to_list (<[i:=x2]> m) = ((i, x2) ::map_to_list m))).
         { apply map_to_list_insert_first_key; assumption. }
         setoid_rewrite H3 in n. clear H3. simpl in n.
         setoid_rewrite elem_of_union in n. apply not_or_and in n. destruct n.
         apply IHether in H4; auto.
         clear IHether.
         destruct (decide (i = (x, x0))).
         ++ subst i.
            setoid_rewrite elem_of_union in H3. apply not_or_and in H3. destruct H3.
            setoid_rewrite lookup_insert in H. by destruct_decide_eq.
         ++ setoid_rewrite (lookup_insert_ne _ _ _ _ n) in H. assumption.
Qed.

(** `usedInPool` is false for PIDs that are not used in the pool. *)
Lemma usedInPoolCorrect: forall prs ι', ¬ isUsedPool ι' prs -> usedInPool ι' prs = false.
Proof.
  intros. unfold usedInPool. unfold isUsedPool in H.
  destruct (gset_elem_of_dec ι' (allPIDsPool prs)); try auto.
  unfold allPIDsPool in e.
  apply not_or_and in H. destruct H.
  unfold flat_union in e.
  induction prs using map_first_key_ind.
  * setoid_rewrite map_to_list_empty in e. simpl in e. inv e.
  * assert ((map_to_list (<[i:=x]> m) = ((i, x) ::map_to_list m))).
    { apply map_to_list_insert_first_key; assumption. }
    setoid_rewrite H3 in e. clear H3. simpl in e.
    apply elem_of_union in e. destruct e.
    + clear IHprs. apply elem_of_union in H3. destruct H3.
      - apply elem_of_singleton in H3. subst ι'.
        setoid_rewrite lookup_insert in H. destruct_decide_eq.
        exfalso. apply H. discriminate.
      - apply not_ex_all_not with (n := i) in H0.
        apply not_ex_all_not with (n := x) in H0.
        setoid_rewrite lookup_insert in H0. destruct_decide_eq.
        apply not_and_or in H0. destruct H0; contradiction.
    + apply IHprs; auto; clear IHprs.
      - clear -H. intros contra.
        destruct (decide (i = ι')).
        ** subst i. setoid_rewrite lookup_insert in H. destruct_decide_eq.
           apply H. discriminate.
        ** setoid_rewrite (lookup_insert_ne _ _ _ _ n) in H. contradiction.
      - clear -H1 H0. intros contra.
        destruct contra, H, H.
        destruct (decide (i = x0)).
        ** subst i. setoid_rewrite H in H1. congruence.
        ** apply H0. exists x0, x1. split;auto.
           setoid_rewrite (lookup_insert_ne _ _ _ _ n). assumption.
Qed.

(** PIDs for which `usedInPool` is false are not used in the pool. *)
Lemma usedInPoolComplete: forall prs ι', usedInPool ι' prs = false -> ¬ isUsedPool ι' prs.
Proof.
  intros. unfold usedInPool in H.
  destruct (gset_elem_of_dec ι' (allPIDsPool prs)); try discriminate. clear H.
  unfold allPIDsPool in n. unfold isUsedPool.
  unfold flat_union in n.
  intros contra. destruct contra.
  * induction prs using map_first_key_ind.
    + setoid_rewrite lookup_empty in H. contradiction.
    + assert ((map_to_list (<[i:=x]> m) = ((i, x) ::map_to_list m))).
      { apply map_to_list_insert_first_key; assumption. }
      setoid_rewrite H2 in n. clear H2. simpl in n.
      setoid_rewrite elem_of_union in n. apply not_or_and in n. destruct n.
      apply IHprs in H3; auto.
      clear IHprs.
      destruct (decide (i = ι')).
      - subst i. setoid_rewrite elem_of_union in H2.
        apply not_or_and in H2. destruct H2. setoid_rewrite elem_of_singleton in H2. contradiction.
      - setoid_rewrite (lookup_insert_ne _ _ _ _ n) in H. assumption.
  * destruct H, H, H.
    induction prs using map_first_key_ind.
    + inv H.
    + assert ((map_to_list (<[i:=x1]> m) = ((i, x1) ::map_to_list m))).
      { apply map_to_list_insert_first_key; assumption. }
      setoid_rewrite H3 in n. clear H3. simpl in n.
      setoid_rewrite elem_of_union in n. apply not_or_and in n. destruct n.
      apply IHprs in H4; auto.
      clear IHprs.
      destruct (decide (i = x)).
      - subst i. setoid_rewrite lookup_insert in H. destruct_decide_eq. inv H.
        setoid_rewrite elem_of_union in H3. apply not_or_and in H3. destruct H3.
        contradiction.
      - setoid_rewrite (lookup_insert_ne _ _ _ _ n) in H. assumption.
Qed.

(** * Steps of nodes *)

(** A step of a node decomposes into the process-local step of the acting
    process, and the rest of the pool. *)
Theorem deconstruct_reduction :
  forall O A B ι a eth eth',
    (eth, A) -[a | ι]ₙ-> (eth', B) with O->
    exists p p' A' B', A = ι ↦ p ∥ A' /\ B = ι ↦ p' ∥ B' /\
      p -⌈a⌉-> p'.
Proof.
  intros. inv H; do 4 eexists; split_and!; try reflexivity; try assumption. 2: eassumption.
  setoid_rewrite insert_insert at 1. destruct_decide_eq.
  - exfalso. subst. apply H6. left. setoid_rewrite lookup_insert. by destruct_decide_eq.
  - by f_equal.
Qed.

(** Adding a signal to the ether does not prevent a step, if the signal is
    not in conflict with the step: the spawned PID (if any) does not appear
    in the signal, and the step does not send to the same target from the
    same source. *)
Theorem etherAdd_step :
  forall A B O ι a,
    A -[a | ι]ₙ-> B with O ->
    forall ιs ιd s,
      (forall ι', spawnPIDOf a = Some ι' -> ιs <> ι' /\ ιd <> ι' /\ (ι' ∉ usedPIDsSignal s)) ->
      (ι = ιs -> sendPIDOf a <> Some ιd) -> (* The addition to the ether should not be in conflict with the (send) action taken *)
      (etherAdd ιs ιd s A.1, A.2) -[a | ι]ₙ-> (etherAdd ιs ιd s B.1, B.2) with O.
Proof with by setoid_rewrite lookup_insert; destruct_decide_eq.
  intros. inv H; simpl in *; try constructor; auto.
  * destruct (decide (ιs = ι)). destruct (decide (ιd = ι')).
    - subst. exfalso. by apply (H1 eq_refl).
    - rewrite etherAdd_swap_2; auto. by apply n_send.
    - rewrite etherAdd_swap_1; auto. by apply n_send.
  * by apply etherPop_etherAdd.
  * econstructor; try eassumption.
    intro. apply appearsEther_etherAdd_rev in H. congruence.
    1-3: apply (H0 ι' eq_refl).
Qed.

(** A step of a node does not change the dead processes, apart from removing
    the link to the target of a send from the dead process taking the
    step. *)
Theorem dead_processes_stay_dead :
  forall O (A B : Node) (a : Action) (ι : PID),
    A -[a | ι]ₙ-> B with O ->
    forall (ι' : PID) (d : DeadProcess), A.2 !! ι' = Some (inr d) ->
      B.2 !! ι' = Some (inr (if decide (ι = ι')
                             then match sendPIDOf a with
                                  | Some ιd => delete ιd d
                                  | _ => d
                                  end
                             else d)).
Proof.
  intros. inv H; simpl in *.
  * case_match; clear H.
    - subst. setoid_rewrite lookup_insert.
      setoid_rewrite lookup_insert in H0. destruct_decide_eq. inv H0. by inv H1.
    - setoid_rewrite lookup_insert_ne; auto.
      setoid_rewrite lookup_insert_ne in H0; auto.
  * case_match; clear H.
    - subst. setoid_rewrite lookup_insert in H0. destruct_decide_eq. inv H0. inv H2.
    - setoid_rewrite lookup_insert_ne; auto.
      setoid_rewrite lookup_insert_ne in H0; auto.
  * case_match; clear H.
    - subst. setoid_rewrite lookup_insert in H0. destruct_decide_eq. inv H0.
      destruct_or!; subst; inv H1.
    - setoid_rewrite lookup_insert_ne; auto.
      setoid_rewrite lookup_insert_ne in H0; auto.
  * clear H5. destruct decide.
    - subst. setoid_rewrite lookup_insert in H0. destruct_decide_eq. inv H0. inv H6.
    - setoid_rewrite lookup_insert_ne; auto.
      setoid_rewrite lookup_insert_ne; auto.
      setoid_rewrite lookup_insert_ne in H0; auto.
      intro. subst.
      apply H3. left. setoid_rewrite lookup_insert_ne; auto.
      setoid_rewrite lookup_insert_ne in H0; auto.
      by setoid_rewrite H0.
Qed.

(** * Evaluating arrivals later *)

(** The actions after which the arrival of a signal to the acting process
    can still be evaluated (`chain_arrive_later`). Arrive and ε actions
    create non-confluent reductions with any other reduction of the same
    process. *)
Definition isChainable (a : Action) : Prop :=
match a with
 | AArrive _ _ _ | ε | ASend _ _ SLink | ASend _ _ SUnlink
 | ASpawn _ _ _ false => False (* normal spaws are not chainable, because
                                  they potentially create a process that
                                  communicates to an observable node, without
                                  killing it on exit arrival *)
 | _ => True
end.

(** `optional_update Π a ιbase s` is the pool `Π`, extended with the effect
    of `a` taken by the process `ιbase`, when `ιbase` was terminated by the
    arrival of `s` before `a`: for spawns, the new process is added, and for
    `spawn_link`, the new process is linked to the (dead) `ιbase`. *)
Definition optional_update (Π : ProcessPool) (a : Action) (ιbase : PID) (s : Signal) : ProcessPool :=
match a with
| ASpawn ι v1 v2 f =>
  match mk_list v2 with
  | Some l =>
    (* NOTE: keep this consistent with the definition in NodeSemantics.v *)
    match create_result (IApp v1) l, f with
    | Some (r, eff), true =>
      match Π !! ιbase, s with
      (* NOTE: Π !! ιbase is always going to be a dead process where this function is used *)
      | Some (inr links), SExit reas b =>
         match b, decide (reas = VLit "kill"%string) with
         | false, left _ =>
           ι ↦ inl ([], r, emptyBox, {[ιbase]}, false) ∥
           ιbase ↦ inr (<[ι:=VLit "killed"%string]>links) ∥ Π
         | _, _ =>
           ι ↦ inl ([], r, emptyBox, {[ιbase]}, false) ∥
           ιbase ↦ inr (<[ι:=reas]>links) ∥ Π
         end
      | _, _ => Π
      end
    | Some (r, eff), false => ι ↦ inl ([], r, emptyBox, ∅, false) ∥ Π
    | _, _ => Π
    end
  | _ => Π
  end
| _ => Π
end.

(* In Lanese et al., Lemma 9 does not hold for this semantics,
   because arrival can change the semantics of receive primops!!!
   E.g., recv_peek_message returns None for empty mailbox, while the
   first message if it is nonempty (and arrival can put a message into the
   empty mailbox).
*)

(** If the process `ι` can take a chainable step `a` and a signal can arrive
    to it, then the arrival can be evaluated after `a` too, and the results
    are joinable: either by taking `a` after the arrival, or (if the arrival
    terminated `ι`) the result is obtained by `optional_update`. *)
Theorem chain_arrive_later :
  forall O A B C a ι ιs s,
  A -[ a | ι ]ₙ-> B with O ->
  isChainable a ->
  A -[ AArrive ιs ι s | ι]ₙ-> C with O ->
  exists D, B -[ AArrive ιs ι s | ι]ₙ-> D with O /\ (* Arrive can be evaluated later *)
    ((exists neweth, etherPop ιs ι B.1 = Some (s, neweth) /\ (* We remove the arrived signal from B's ether *)
     (neweth, optional_update C.2 a ι s) = D
     ) \/ (* For spawns, there is a new process, moreover, for spawn_links the dead process has a new link in the list of links! *)
     C -[ a | ι ]ₙ-> D with O) (* For most actions, arrives are confluent *).
Proof.
  intros * HD1 ? HD2.
  inv HD2. 2: { destruct_or!; congruence. }
  inv H7.
  (* message arrival *)
  * rename ι0 into ι. inv HD1.
    - put (lookup ι : ProcessPool -> option _) on H2 as P.
      setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
      inv H5.
     (* message send *)
     (* TODO: proofs for these cases are almost identical *)
      + eexists. split.
        1: { constructor. apply etherPop_etherAdd. eassumption.
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
               * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_send. by constructor.
      (* exit send *)
      + eexists. split.
        1: { constructor. apply etherPop_etherAdd. eassumption.
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
               * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_send. by constructor.
      (* link send *)
      + eexists. split.
        1: { constructor. apply etherPop_etherAdd. eassumption.
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
               * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_send. by constructor.
      (* unlink send *)
      + eexists. split.
        1: { constructor. apply etherPop_etherAdd. eassumption.
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
               * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_send. by constructor.
    (* arrivals - cannot happen *)
    - inv H.
    (* local actions *)
    - put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
(* case separation is needed at this point, because
 exists can't be instantiated first, also ε actions
 could terminate a process -> no chaining

TODO: this cases a lot of boiler plate
*)
      destruct_or! H7; subst; inv H2.
      (* silent steps *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι ↦ inl (fs, e, mailboxPush mb v, links, flag) ∥ prs = ι ↦ inl (fs, e, mailboxPush mb v, links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. by constructor. by left.
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
               * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. eapply p_recv_peek_message_ok.
             { destruct mb; clear-H9. simpl.
               destruct l0; inv H9. reflexivity. }
             by left.
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
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other.
        econstructor.
        {
          clear -H9. destruct mb. simpl in *.
          destruct l0; invSome. by simpl.
        }
        by left.
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
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other.
        econstructor.
        {
          clear -H9. destruct mb. simpl in *.
          destruct l0; invSome. simpl.
          by rewrite app_assoc.
        }
        by left.
      (* recv_wait_timeout infinity *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [VLit "infinity"%string],
      mailboxPush (oldmb, msg :: newmb) v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [VLit "infinity"%string],
      mailboxPush (oldmb, msg :: newmb) v, links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
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
               * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
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
               * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. by constructor. by left.
      (* trap_exit exception *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v0], mailboxPush mb v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v0], mailboxPush mb v, links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
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
               * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. by constructor. by right; left.
      (* recv_peek_message - fail - This cannot be proved
         after pushing a message, peekMessage won't fail anymore *)
      + inv H.
      (* normal termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* exceptional termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* setflag *)
      + inv H.
    (* spawns *)
    - inv H11.
      (* spawn *)
      {
        eexists. split.
        1: {
          setoid_rewrite insert_insert. destruct_decide_eq. 1: {
            exfalso. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
          }
          constructor. eassumption.
          constructor. }
        right.
        assert (ι ↦ inl (fs, e, mailboxPush mb v, links, flag) ∥ prs = ι ↦ inl (fs, e, mailboxPush mb v, links, flag) ∥  Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        setoid_rewrite insert_insert. destruct_decide_eq. 1: {
          exfalso. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
        }
        eapply n_spawn; try eassumption.
        1: {
          rewrite <- H0. rewrite H1 in H4.
          clear -H4 H5 H6.
          intro. apply isUsedPool_insert_1 in H as [H | [H | H]].
          * apply H4. apply isUsedPool_insert_2. by left.
          * subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * simpl in H. rewrite flat_union_app in H. simpl in H.
            assert (ι' ∉ usedPIDsVal v). {
              intro. apply H5.
              unfold etherPop in H6. repeat case_match; try congruence.
              subst. inv H6.
              right. right. do 3 eexists. split. exact H1.
              set_solver.
            }
            apply H4. right. exists ι. eexists.
            split. by setoid_rewrite lookup_insert; destruct_decide_eq.
            simpl. set_solver.
        }
        1: {
          clear -H5 H6.
          intro. eapply appearsEther_etherPop_rev in H; eauto.
        }
        put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
      }
      { (* spawn_link - the proof is the same *)
         eexists. split.
        1: {
          setoid_rewrite insert_insert. destruct_decide_eq. 1: {
            exfalso. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
          }
          constructor. eassumption.
          constructor. }
        right.
        assert (ι ↦ inl (fs, e, mailboxPush mb v, links, flag) ∥ prs = ι ↦ inl (fs, e, mailboxPush mb v, links, flag) ∥  Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        setoid_rewrite insert_insert. destruct_decide_eq. 1: {
          exfalso. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
        }
        eapply n_spawn; try eassumption.
        1: {
          rewrite <- H0. rewrite H1 in H4.
          clear -H4 H5 H6.
          intro. apply isUsedPool_insert_1 in H as [H | [H | H]].
          * apply H4. apply isUsedPool_insert_2. by left.
          * subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * simpl in H. rewrite flat_union_app in H. simpl in H.
            assert (ι' ∉ usedPIDsVal v). {
              intro. apply H5.
              unfold etherPop in H6. repeat case_match; try congruence.
              subst. inv H6.
              right. right. do 3 eexists. split. exact H1.
              set_solver.
            }
            apply H4. right. exists ι. eexists.
            split. by setoid_rewrite lookup_insert; destruct_decide_eq.
            simpl. set_solver.
        }
        1: {
          clear -H5 H6.
          intro. eapply appearsEther_etherPop_rev in H; eauto.
        }
        put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
        constructor; assumption.
      }
  (* exit dropped - it is potentially influenced by links, process flag *)
  * inv HD1.
    - rename ι0 into ι.
      put (lookup ι : ProcessPool -> option _) on H2 as P.
      setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
      inv H7.
     (* message send *)
     (* TODO: proofs for these cases are almost identical *)
      + eexists. split.
        1: { constructor. apply etherPop_etherAdd. eassumption.
             constructor. set_solver.
           }
        right.
        eapply n_send. by constructor.
      (* exit send *)
      + eexists. split.
        1: { constructor. apply etherPop_etherAdd. eassumption.
             constructor. set_solver.
           }
        right.
        eapply n_send. by constructor.
      (* link send *)
      + inv H. (* can't be done *)
      (* unlink send *)
      + eexists. split.
        1: { constructor. apply etherPop_etherAdd. eassumption.
             constructor.
             set_solver.
           }
        right.
        eapply n_send. by constructor.
    (* arrivals - cannot happen *)
    - inv H.
    (* local actions *)
    - rename ι0 into ι.
      put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
(* case separation is needed at this point, because
 exists can't be instantiated first, also ε actions
 could terminate a process -> no chaining

TODO: this cases a lot of boiler plate
*)
      destruct_or! H8; subst; inv H2.
      (* silent steps *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by left.
      (* recv_peek_message - success *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by left.
      (* recv_next *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by left.
      (* removeMessage *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by intuition.
      (* recv_wait_timeout infinity *)
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
      (* trap_exit exception *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by left.
      (* self *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by right;left.
      (* recv_peek_message - fail *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by intuition.
      (* normal termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* exceptional termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* setflag *)
      + inv H.
    (* spawn *)
    - inv H12.
      { (* spawn *)
        rename ι0 into ι.
        put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
        eexists. split.
        1: {
          setoid_rewrite insert_insert. destruct_decide_eq.
          exfalso. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
          constructor. eassumption.
          constructor. assumption.
        }
        right.
        setoid_rewrite insert_insert. destruct_decide_eq.
        exfalso. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
        eapply n_spawn; try eassumption.
        1: {
          clear -H6 H7.
          intro. eapply appearsEther_etherPop_rev in H; eauto.
        }
        constructor; assumption.
      }
      { (* spawn_link *)
        rename ι0 into ι.
        put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
        eexists. split.
        1: {
          setoid_rewrite insert_insert. destruct_decide_eq.
          exfalso. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
          constructor. eassumption.
          constructor.
          assert (ιs ≠ ι'). {
            intro. subst.
            apply H7. right. left.
            exists ι. intro.
            clear -H0 H6.
            unfold etherPop in H6. repeat case_match; try congruence.
          }
          clear -H5 H0.
          set_solver.
        }
        right.
        setoid_rewrite insert_insert. destruct_decide_eq.
        exfalso. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
        eapply n_spawn; try eassumption.
        1: {
          clear -H6 H7.
          intro. eapply appearsEther_etherPop_rev in H; eauto.
        }
        constructor; assumption.
      }
  (* exit terminates - it is potentially influenced by links, process flag *)
  * inv HD1.
    - rename ι0 into ι.
      put (lookup ι : ProcessPool -> option _) on H2 as P.
      setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
      inv H7.
     (* message send *)
     (* TODO: proofs for these cases are almost identical *)
      + eexists. split.
        1: { constructor. apply etherPop_etherAdd. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: by apply etherPop_etherAdd.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert; destruct_decide_eq.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H2 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* exit send *)
      + eexists. split.
        1: { constructor. apply etherPop_etherAdd. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: by apply etherPop_etherAdd.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert; destruct_decide_eq.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H2 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* link send - can't be done, since links are potentially modified *)
      + inv H.
      (* unlink send - can't be done, since links are potentially modified *)
      + inv H.
    (* arrivals - cannot happen *)
    - inv H.
    (* local actions *)
    - rename ι0 into ι.
      put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
(* case separation is needed at this point, because
 exists can't be instantiated first, also ε actions
 could terminate a process -> no chaining

TODO: this cases a lot of boiler plate
*)
      destruct_or! H8; subst; inv H2.
      (* silent steps *)
      + eexists. split.
        1: { constructor. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: eassumption.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert; destruct_decide_eq.
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
        1: subst; by setoid_rewrite lookup_insert; destruct_decide_eq.
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
        1: subst; by setoid_rewrite lookup_insert; destruct_decide_eq.
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
        1: subst; by setoid_rewrite lookup_insert; destruct_decide_eq.
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
        1: subst; by setoid_rewrite lookup_insert; destruct_decide_eq.
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
        1: subst; by setoid_rewrite lookup_insert; destruct_decide_eq.
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
        1: subst; by setoid_rewrite lookup_insert; destruct_decide_eq.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H1 as H'.
        setoid_rewrite lookup_insert_ne in H'; auto.
      (* trap_exit exception *)
      + eexists. split.
        1: { constructor. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: eassumption.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert; destruct_decide_eq.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H1 as H'.
        setoid_rewrite lookup_insert_ne in H'; auto.
      (* self *)
      + eexists. split.
        1: { constructor. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: eassumption.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert; destruct_decide_eq.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H1 as H'.
        setoid_rewrite lookup_insert_ne in H'; auto.
      (* recv_peek_message - fail *)
      + eexists. split.
        1: { constructor. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: eassumption.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert; destruct_decide_eq.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H1 as H'.
        setoid_rewrite lookup_insert_ne in H'; auto.
      (* normal termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* exceptional termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* setflag *)
      + inv H.
    (* spawn -
       if the exit is delivered first, a process cannot be
       spawned *)
    - rename ι0 into ι. inv H12.
      {
        put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
        eexists. split.
        1: {
          setoid_rewrite insert_insert; destruct_decide_eq.
          exfalso. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq. 
          constructor. eassumption.
          apply p_exit_terminate. eassumption.
        }
        left.
        assert (ι' <> ι). {
          intro. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
        }
        eexists; split. simpl. eassumption.
        simpl. rewrite H2. simpl in H8. rewrite H8.
        f_equal.
        setoid_rewrite insert_insert at 1; destruct_decide_eq.
        apply map_eq. intros.
        destruct (decide (i = ι)). 2: destruct (decide (i = ι')).
        all: subst.
        1: by setoid_rewrite lookup_insert; destruct_decide_eq.
        1: setoid_rewrite lookup_insert_ne; try lia.
        1: by setoid_rewrite lookup_insert; destruct_decide_eq.
        do 2 (setoid_rewrite lookup_insert_ne; try lia).
        put (lookup i : ProcessPool -> _) on H1 as H'.
        simpl in H'.
        by (setoid_rewrite lookup_insert_ne in H'; try lia).
      }
      {
      (* spawn_link is more tricky - can the arrive not termiate it? - potentially
         not, since ι' does not appear anywhere - thus it could not affect the behaviour *)
      - put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
        eexists. split.
        1: {
          setoid_rewrite insert_insert; destruct_decide_eq.
          exfalso. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq. 
          constructor. eassumption.
          apply p_exit_terminate.
          assert (ιs ≠ ι'). {
            clear -H7 H6. intro. subst. apply H7.
            right. left. exists ι. intro.
            unfold etherPop in H6. repeat case_match; try congruence.
          }
          Unshelve. 2: exact reason'.
          clear -H0 H5. set_solver.
        }
        left.
        assert (ι' <> ι). {
          intro. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
        }
        eexists; split. simpl. eassumption.
        simpl. rewrite H2. simpl in H8. rewrite H8.
        f_equal.
        setoid_rewrite insert_insert at 1; auto.
        apply map_eq. intros.
        setoid_rewrite lookup_insert. destruct_decide_eq.
        clear H8. repeat case_match; try congruence.
        { (* NOTE: boiler plate for "killed" reason *)
          subst.
          destruct (decide (i = ι)). 2: destruct (decide (i = ι')).
          all: subst.
          1: {
             setoid_rewrite lookup_insert_ne; auto; setoid_rewrite lookup_insert.
             destruct_decide_eq.
             setoid_rewrite gset_to_gmap_union_singleton.
             clear -H5.
             intuition; subst; auto. congruence.
          }
          1: by setoid_rewrite lookup_insert; destruct_decide_eq.
          repeat (setoid_rewrite lookup_insert_ne; try lia).
          put (lookup i : ProcessPool -> _) on H1 as H'.
          simpl in H'.
          (setoid_rewrite lookup_insert_ne in H'; try lia).
          by repeat setoid_rewrite lookup_insert_ne.
        }
        { (* original reason is kept *)
          subst.
          destruct (decide (i = ι)). 2: destruct (decide (i = ι')).
          all: subst.
          1: {
             setoid_rewrite lookup_insert_ne; auto; setoid_rewrite lookup_insert.
             destruct_decide_eq.
             setoid_rewrite gset_to_gmap_union_singleton.
             clear -H5.
             intuition; subst; auto. congruence.
          }
          1: by setoid_rewrite lookup_insert; destruct_decide_eq.
          repeat (setoid_rewrite lookup_insert_ne; try lia).
          put (lookup i : ProcessPool -> _) on H1 as H'.
          simpl in H'.
          (setoid_rewrite lookup_insert_ne in H'; try lia).
          by repeat setoid_rewrite lookup_insert_ne.
        }
        { (* original reason is kept *)
          subst.
          destruct (decide (i = ι)). 2: destruct (decide (i = ι')).
          all: subst.
          1: {
             setoid_rewrite lookup_insert_ne; auto; setoid_rewrite lookup_insert.
             destruct_decide_eq.
             setoid_rewrite gset_to_gmap_union_singleton.
             clear -H5 n.
             intuition; subst; auto.
          }
          1: by setoid_rewrite lookup_insert; destruct_decide_eq.
          repeat (setoid_rewrite lookup_insert_ne; try lia).
          put (lookup i : ProcessPool -> _) on H1 as H'.
          simpl in H'.
          (setoid_rewrite lookup_insert_ne in H'; try lia).
          by repeat setoid_rewrite lookup_insert_ne.
        }
      }
  (* exit converted - it is potentially influenced by links, process flag, mailbox *)
  * rename ι0 into ι.
    inv HD1.
    - put (lookup ι : ProcessPool -> option _) on H2 as P.
      setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
      inv H7.
     (* message send *)
     (* TODO: proofs for these cases are almost identical *)
      + eexists. split.
        1: { constructor. apply etherPop_etherAdd. eassumption.
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
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_send. by constructor.
      (* exit send *)
      + eexists. split.
        1: { constructor. apply etherPop_etherAdd. eassumption.
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
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_send. by constructor.
      (* link send - maybe this should not be proved? *)
      + eexists. split.
        1: { constructor. apply etherPop_etherAdd. eassumption.
             apply p_exit_convert.
             clear -H5. set_solver.
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
        * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
        * setoid_rewrite lookup_insert_ne; auto.
          setoid_rewrite lookup_insert_ne in HH; auto.
      }
      setoid_rewrite H0.
      eapply n_send. by constructor.
      (* unlink send - can't be proved, list of links influence the behaviour of exits *)
      + inv H.
    (* arrivals - cannot happen *)
    - inv H.
    (* local actions *)
    - put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
(* case separation is needed at this point, because
 exists can't be instantiated first, also ε actions
 could terminate a process -> no chaining

TODO: this cases a lot of boiler plate
*)
      destruct_or! H8; subst; inv H2.
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
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. by constructor. by left.
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
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. eapply p_recv_peek_message_ok.
        { destruct mb; clear-H10. simpl.
          destruct l0; inv H10. reflexivity. }
        by left.
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
         * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
         * setoid_rewrite lookup_insert_ne; auto.
           setoid_rewrite lookup_insert_ne in HH; auto.
       }
       setoid_rewrite H0.
       eapply n_other.
       econstructor.
       {
         clear -H10. destruct mb. simpl in *.
         destruct l0; invSome. by simpl.
       }
       by intuition.
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
         * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
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
       by intuition.
      (* recv_wait_timeout infinity *)
      + eexists. split.
        1: { constructor. eassumption. by apply p_exit_convert. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [VLit "infinity"%string],
      mailboxPush (oldmb, msg :: newmb) (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links, true)
 ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [VLit "infinity"%string],
      mailboxPush (oldmb, msg :: newmb) (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links, true)
 ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
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
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
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
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. by constructor. by left.
      (* trap_exit exception *)
      + eexists. split.
        1: { constructor. eassumption. by apply p_exit_convert. }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links, true) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links, true) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
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
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. by constructor. by right; left.
      (* recv_peek_message - fail - This cannot be proved
         after pushing a message, peekMessage won't fail anymore *)
      + inv H.
      (* normal termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* exceptional termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* setflag *)
      + inv H.
    (* spawn *)
    - inv H12.
      {
        put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
        eexists. split.
        1: {
          setoid_rewrite insert_insert; destruct_decide_eq.
          exfalso. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
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
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        setoid_rewrite insert_insert; destruct_decide_eq.
        exfalso. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
        eapply n_spawn; try eassumption.
        1: {
          rewrite <- H0. rewrite H1 in H4.
          clear -H4 H7 H6.
          intro. apply isUsedPool_insert_1 in H as [H | [H | H]].
          * apply H4. apply isUsedPool_insert_2. by left.
          * subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * simpl in H. rewrite flat_union_app in H. simpl in H.
            assert ((ι' ∉ usedPIDsVal reason) /\ ι' <> ιs). {
              unfold etherPop in H6. repeat case_match; try congruence.
              split.
              * intro. apply H7.
                subst. inv H6.
                right. right. do 3 eexists. split. exact H0.
                set_solver.
              * intro. subst. apply H7. right. left.
                eexists. by rewrite H0.
            }
            apply H4. right. exists ι. eexists.
            split. by setoid_rewrite lookup_insert; destruct_decide_eq.
            simpl. set_solver.
        }
        1: {
          clear -H6 H7.
          intro. eapply appearsEther_etherPop_rev in H; eauto.
        }
        constructor; assumption.
      }
      { (* spawn_link *)
        put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
        eexists. split.
        1: {
          setoid_rewrite insert_insert; destruct_decide_eq.
          exfalso. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq. 
          constructor. eassumption.
          apply p_exit_convert.
          (* NOTE: at this point we exploit that ι' is not used anywhere! *)
          assert (ι' ≠ ιs) as X. {
            clear -H6 H7. intro. subst.
            apply H7. right. left. exists ι. intro.
            unfold etherPop in H6. repeat case_match; try congruence.
          }
          clear -X H5. set_solver.
        }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "spawn_link"%string)) [VClos ext id vars e0] []
      :: fs0, RValSeq [v2], mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links, true)
 ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "spawn_link"%string)) [VClos ext id vars e0] []
      :: fs0, RValSeq [v2], mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links, true)
 ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        setoid_rewrite insert_insert; destruct_decide_eq.
        exfalso. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq. 
        eapply n_spawn; try eassumption.
        1: {
          rewrite <- H0. rewrite H1 in H4.
          clear -H4 H6 H7.
          intro. apply isUsedPool_insert_1 in H as [H | [H | H]].
          * apply H4. apply isUsedPool_insert_2. by left.
          * subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * simpl in H. rewrite flat_union_app in H. simpl in H.
            assert ((ι' ∉ usedPIDsVal reason) /\ ι' <> ιs). {
              unfold etherPop in H6. repeat case_match; try congruence.
              split.
              * intro. apply H7.
                subst. inv H6.
                right. right. do 3 eexists. split. exact H0.
                set_solver.
              * intro. subst. apply H7. right. left.
                eexists. by rewrite H0.
            }
            apply H4. right. exists ι. eexists.
            split. by setoid_rewrite lookup_insert; destruct_decide_eq.
            simpl. set_solver.
        }
        1: {
          clear -H6 H7.
          intro. eapply appearsEther_etherPop_rev in H; eauto.
        }
        constructor; assumption.
      }
  (* link arrives *)
  * rename ι0 into ι. inv HD1.
    - put (lookup ι : ProcessPool -> option _) on H2 as P.
      setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
      inv H5.
     (* message send *)
     (* TODO: proofs for these cases are almost identical *)
      + eexists. split.
        1: { constructor. apply etherPop_etherAdd. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
      :: fs0, RValSeq [v], mb, {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
      :: fs0, RValSeq [v], mb, {[ιs]} ∪ links, flag) ∥ prs0). {
          apply map_eq. intros.
          clear -H2.
          put (lookup i : ProcessPool -> _) on H2 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_send. by constructor.
      (* exit send *)
      + eexists. split.
        1: { constructor. apply etherPop_etherAdd. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [
        VPid ι'] [] :: fs0, RValSeq [v], mb, {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [
        VPid ι'] [] :: fs0, RValSeq [v], mb, {[ιs]} ∪ links, flag) ∥ prs0). {
          apply map_eq. intros.
          clear -H2.
          put (lookup i : ProcessPool -> _) on H2 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_send. by constructor.
      (* link send - maybe this should not be proved? *)
      + eexists. split.
        1: { constructor. apply etherPop_etherAdd. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] []
      :: fs0, RValSeq [VPid ι'], mb, {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] []
      :: fs0, RValSeq [VPid ι'], mb, {[ιs]} ∪ links, flag) ∥ prs0). {
          apply map_eq. intros.
          clear -H2.
          put (lookup i : ProcessPool -> _) on H2 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_send. inv H. (* TODO: links should be formalised as sets *)
      (* unlink send - can't be proved if the same link is established and deleted in the two reductions *)
      + inv H.
    (* arrivals - cannot happen *)
    - inv H.
    (* local actions *)
    - put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
(* case separation is needed at this point, because
 exists can't be instantiated first, also ε actions
 could terminate a process -> no chaining

TODO: this cases a lot of boiler plate
*)
      destruct_or! H7; subst; inv H2.
      (* silent steps *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι ↦ inl (fs, e, mb, {[ιs]} ∪ links, flag) ∥ prs = ι ↦ inl (fs, e, mb, {[ιs]} ∪ links, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. by constructor. by left.
      (* recv_peek_message - success *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      {[ιs]} ∪ links, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. eapply p_recv_peek_message_ok.
        assumption.
        by intuition.
      (* recv_next *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_next") [] [] :: fs0, RBox, mb,
      {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_next") [] [] :: fs0, RBox, mb,
      {[ιs]} ∪ links, flag) ∥ Π). {
         apply map_eq. intros.
         clear -H1.
         put (lookup i : ProcessPool -> _) on H1 as HH.
         destruct (decide (i = ι)).
         * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
         * setoid_rewrite lookup_insert_ne; auto.
           setoid_rewrite lookup_insert_ne in HH; auto.
       }
       setoid_rewrite H0.
       eapply n_other.
       econstructor.
       assumption.
       by intuition.
      (* removeMessage *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "remove_message") [] [] :: fs0, RBox, mb,
      {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "remove_message") [] [] :: fs0, RBox, mb,
      {[ιs]} ∪ links, flag) ∥ Π). {
         apply map_eq. intros.
         clear -H1.
         put (lookup i : ProcessPool -> _) on H1 as HH.
         destruct (decide (i = ι)).
         * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
         * setoid_rewrite lookup_insert_ne; auto.
           setoid_rewrite lookup_insert_ne in HH; auto.
       }
       setoid_rewrite H0.
       eapply n_other.
       econstructor.
       assumption.
       by intuition.
     (* recv_wait_timeout infinity *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [VLit "infinity"%string],
      (oldmb, msg :: newmb), {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [VLit "infinity"%string],
      (oldmb, msg :: newmb), {[ιs]} ∪ links, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
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
      VLit 0%Z], mb, {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      VLit 0%Z], mb, {[ιs]} ∪ links, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
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
      {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [v], mb,
      {[ιs]} ∪ links, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. by constructor. by left.
      (* trap_exit exception *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v], mb, {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v], mb, {[ιs]} ∪ links, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
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
      :: fs0, RBox, mb, {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "self"%string)) [] []
      :: fs0, RBox, mb, {[ιs]} ∪ links, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. by constructor. by right; left.
      (* recv_peek_message - fail *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      {[ιs]} ∪ links, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. econstructor.
        assumption.
        by intuition.
      (* normal termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* exceptional termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* setflag *)
      + inv H.
    (* spawn *)
    - inv H11.
      {
        put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
        eexists. split.
        1: {
          setoid_rewrite insert_insert; destruct_decide_eq.
          exfalso. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq. 
          constructor. eassumption. constructor.
        }
        right.
        assert (ι
   ↦ inl
       (FParams (ICall (VLit "erlang"%string) (VLit "spawn"%string))
          [VClos ext id vars e0] [] :: fs0, RValSeq [v2], mb, 
        {[ιs]} ∪ links, flag) ∥ prs = ι
   ↦ inl
       (FParams (ICall (VLit "erlang"%string) (VLit "spawn"%string))
          [VClos ext id vars e0] [] :: fs0, RValSeq [v2], mb, 
        {[ιs]} ∪ links, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        setoid_rewrite insert_insert; destruct_decide_eq.
        exfalso. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq. 
        eapply n_spawn; try eassumption.
        1: {
          rewrite <- H0. rewrite H1 in H4.
          clear -H4 H5 H6.
          intro. apply isUsedPool_insert_1 in H as [H | [H | H]].
          * apply H4. apply isUsedPool_insert_2. by left.
          * subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * simpl in H.
            assert (ι' <> ιs). {
              unfold etherPop in H6. repeat case_match; try congruence.
              intro. subst. apply H5. right. left.
              eexists. by rewrite H0.
            }
            apply H4. right. exists ι. eexists.
            split. by setoid_rewrite lookup_insert; destruct_decide_eq.
            simpl. set_solver.
        }
        1: {
          clear -H5 H6.
          intro. eapply appearsEther_etherPop_rev in H; eauto.
        }
        constructor; assumption.
      }
      { (* spawn_link *)
        put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
        eexists. split.
        1: {
          setoid_rewrite insert_insert; destruct_decide_eq.
          exfalso. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq. 
          constructor. eassumption. constructor.
        }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "spawn_link"%string)) [VClos ext id vars e0] []
      :: fs0, RValSeq [v2], mb, {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "spawn_link"%string)) [VClos ext id vars e0] []
      :: fs0, RValSeq [v2], mb, {[ιs]} ∪ links, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        setoid_rewrite insert_insert; destruct_decide_eq.
        exfalso. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq. 
        eapply n_spawn; try eassumption.
        1: {
          rewrite <- H0. rewrite H1 in H4.
          clear -H4 H5 H6.
          intro. apply isUsedPool_insert_1 in H as [H | [H | H]].
          * apply H4. apply isUsedPool_insert_2. by left.
          * subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * simpl in H.
            assert (ι' <> ιs). {
              unfold etherPop in H6. repeat case_match; try congruence.
              intro. subst. apply H5. right. left.
              eexists. by rewrite H0.
            }
            apply H4. right. exists ι. eexists.
            split. by setoid_rewrite lookup_insert; destruct_decide_eq.
            simpl. set_solver.
        }
        1: {
          clear -H5 H6.
          intro. eapply appearsEther_etherPop_rev in H; eauto.
        }
        replace ({[ιs]} ∪ ({[ι']} ∪ links)) with
          ({[ι']} ∪ ({[ιs]} ∪ links)) by (clear; set_solver).
        constructor; assumption.
      }
  (* unlink arrives *)
  * rename ι0 into ι.
    inv HD1.
    - put (lookup ι : ProcessPool -> option _) on H2 as P.
      setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
      inv H5.
     (* message send *)
     (* TODO: proofs for these cases are almost identical *)
      + eexists. split.
        1: { constructor. apply etherPop_etherAdd. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
      :: fs0, RValSeq [v], mb, links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
      :: fs0, RValSeq [v], mb, links ∖ {[ιs]}, flag) ∥ prs0). {
          apply map_eq. intros.
          clear -H2.
          put (lookup i : ProcessPool -> _) on H2 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_send. by constructor.
      (* exit send *)
      + eexists. split.
        1: { constructor. apply etherPop_etherAdd. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [
        VPid ι'] [] :: fs0, RValSeq [v], mb, links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [
        VPid ι'] [] :: fs0, RValSeq [v], mb, links ∖ {[ιs]}, flag) ∥ prs0). {
          apply map_eq. intros.
          clear -H2.
          put (lookup i : ProcessPool -> _) on H2 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_send. by constructor.
      (* link send - maybe this should not be proved? *)
      + eexists. split.
        1: { constructor. apply etherPop_etherAdd. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] []
      :: fs0, RValSeq [VPid ι'], mb, links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] []
      :: fs0, RValSeq [VPid ι'], mb, links ∖ {[ιs]}, flag) ∥ prs0). {
          apply map_eq. intros.
          clear -H2.
          put (lookup i : ProcessPool -> _) on H2 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_send. inv H. (* TODO: links should be formalised as sets *)
      (* unlink send - can't be proved if the same link is established and deleted in the two reductions *)
      + inv H.
    (* arrivals - cannot happen *)
    - inv H.
    (* local actions *)
    - put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
(* case separation is needed at this point, because
 exists can't be instantiated first, also ε actions
 could terminate a process -> no chaining

TODO: this cases a lot of boiler plate
*)
      destruct_or! H7; subst; inv H2.
      (* silent steps *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι ↦ inl (fs, e, mb, links ∖ {[ιs]}, flag) ∥ prs = ι ↦ inl (fs, e, mb, links ∖ {[ιs]}, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. by constructor. by left.
      (* recv_peek_message - success *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      links ∖ {[ιs]}, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. eapply p_recv_peek_message_ok.
        assumption.
        by intuition.
      (* recv_next *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_next") [] [] :: fs0, RBox, mb, 
      links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_next") [] [] :: fs0, RBox, mb, 
      links ∖ {[ιs]}, flag) ∥ Π). {
           apply map_eq. intros.
           clear -H1.
           put (lookup i : ProcessPool -> _) on H1 as HH.
           destruct (decide (i = ι)).
           * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
           * setoid_rewrite lookup_insert_ne; auto.
             setoid_rewrite lookup_insert_ne in HH; auto.
         }
         setoid_rewrite H0.
         eapply n_other. by econstructor.
         by intuition.
      (* removeMessage *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "remove_message") [] [] :: fs0, RBox, mb,
      links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "remove_message") [] [] :: fs0, RBox, mb,
      links ∖ {[ιs]}, flag) ∥ Π). {
         apply map_eq. intros.
         clear -H1.
         put (lookup i : ProcessPool -> _) on H1 as HH.
         destruct (decide (i = ι)).
         * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
         * setoid_rewrite lookup_insert_ne; auto.
           setoid_rewrite lookup_insert_ne in HH; auto.
       }
       setoid_rewrite H0.
       eapply n_other.
       econstructor.
       assumption.
       by intuition.
      (* recv_wait_timeout infinity *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0,
      RValSeq [VLit "infinity"%string], (oldmb, msg :: newmb), 
      links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0,
      RValSeq [VLit "infinity"%string], (oldmb, msg :: newmb), 
      links ∖ {[ιs]}, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other.
        by econstructor.
        by intuition.
      (* recv_wait_timeout 0 *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      VLit 0%Z], mb, links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      VLit 0%Z], mb, links ∖ {[ιs]}, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
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
      links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [v], mb,
      links ∖ {[ιs]}, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. by constructor. by left.
      (* trap_exit exception *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v], mb, links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v], mb, links ∖ {[ιs]}, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
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
      :: fs0, RBox, mb, links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "self"%string)) [] []
      :: fs0, RBox, mb, links ∖ {[ιs]}, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. by constructor. by right; left.
      (* recv_peek_message - fail *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      links ∖ {[ιs]}, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. econstructor.
        assumption.
        by intuition.
      (* normal termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* exceptional termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* setflag *)
      + inv H.
    (* spawn *)
    - inv H11.
      {
        put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
        eexists. split.
        1: {
          setoid_rewrite insert_insert; destruct_decide_eq.
          exfalso. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq. 
          constructor. eassumption. constructor.
        }
        right.
        assert (ι
   ↦ inl
       (FParams (ICall (VLit "erlang"%string) (VLit "spawn"%string))
          [VClos ext id vars e0] [] :: fs0, RValSeq [v2], mb, 
        links ∖ {[ιs]}, flag) ∥ prs = ι
   ↦ inl
       (FParams (ICall (VLit "erlang"%string) (VLit "spawn"%string))
          [VClos ext id vars e0] [] :: fs0, RValSeq [v2], mb, 
        links ∖ {[ιs]}, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        setoid_rewrite insert_insert; destruct_decide_eq.
        exfalso. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq. 
        eapply n_spawn; try eassumption.
        1: {
          rewrite <- H0. rewrite H1 in H4.
          clear -H4 H5 H6.
          intro. apply isUsedPool_insert_1 in H as [H | [H | H]].
          * apply H4. apply isUsedPool_insert_2. by left.
          * subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * apply H4. right. exists ι. eexists.
            split. by setoid_rewrite lookup_insert; destruct_decide_eq.
            simpl.
            clear -H. simpl in H.
            set_solver.
        }
        1: {
          clear -H5 H6.
          intro. eapply appearsEther_etherPop_rev in H; eauto.
        }
        constructor; assumption.
      }
      { (* spawn_link *)
        put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. destruct_decide_eq. inv P.
        eexists. split.
        1: {
          setoid_rewrite insert_insert; destruct_decide_eq.
          exfalso. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq. 
          constructor. eassumption. constructor.
        }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "spawn_link"%string)) [VClos ext id vars e0] []
      :: fs0, RValSeq [v2], mb, links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "spawn_link"%string)) [VClos ext id vars e0] []
      :: fs0, RValSeq [v2], mb, links ∖ {[ιs]}, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        setoid_rewrite insert_insert; destruct_decide_eq.
        exfalso. subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq. 
        eapply n_spawn; try eassumption.
        1: {
          rewrite <- H0. rewrite H1 in H4.
          clear -H4 H5 H6.
          intro. apply isUsedPool_insert_1 in H as [H | [H | H]].
          * apply H4. apply isUsedPool_insert_2. by left.
          * subst. apply H4. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
          * apply H4. right. exists ι. eexists.
            split. by setoid_rewrite lookup_insert; destruct_decide_eq.
            simpl.
            clear -H. simpl in H.
            set_solver.
        }
        1: {
          clear -H5 H6.
          intro. eapply appearsEther_etherPop_rev in H; eauto.
        }
        replace (({[ι']} ∪ links) ∖ {[ιs]}) with
          ({[ι']} ∪ (links ∖ {[ιs]})). 2: {
          (* NOTE: we exploit that ι' is fresh *)
          clear -H5 H6.
          assert (ι' ≠ ιs) as X. {
            intro. subst. apply H5.
            right. left. exists ι. intro.
            unfold etherPop in H6. repeat case_match; congruence.
          }
          set_solver.
        }
        constructor; assumption.
      }
Qed.

(** The actions which do not modify the ether: τ, `spawn_link` and `self`.
    For these actions, the arrival of a signal can be evaluated later
    without modifying the ether of the result (`chain_arrive_later_2`). *)
Definition isChainable2 (a : Action) : Prop :=
match a with
 | τ | ASpawn _ _ _ true | ASelf _  => True
 | _ => False
end.

(** The version of `chain_arrive_later` for the actions in `isChainable2`:
    if the arrival has to be evaluated later, the ether of the result is the
    ether after the arrival. *)
Corollary chain_arrive_later_2 :
  forall O A B C a ι ιs s,
  A -[ a | ι ]ₙ-> B with O ->
  isChainable2 a ->
  A -[ AArrive ιs ι s | ι]ₙ-> C with O ->
  exists D, B -[ AArrive ιs ι s | ι]ₙ-> D with O /\ (* Arrive can be evaluated later *)
    ((C.1, optional_update C.2 a ι s) = D \/ (* For spawns, there is a new process, moreover, for spawn_links the dead process has a new link in the list of links! *)
     C -[ a | ι ]ₙ-> D with O) (* For most actions, arrives are confluent *).
Proof.
  intros.
  opose proof* chain_arrive_later. 1: exact H. 2: exact H1.
  * destruct a; by trivial.
  * destruct H2 as [D [HD [|]]].
    - destruct H2 as [neweth [Eq1 Eq2]].
      exists D. split. assumption. left.
      subst D. f_equal. clear HD. destruct B as [Beth BΠ].
      simpl in Eq1. unfold etherPop in Eq1. case_match. 2: congruence.
      destruct l. congruence. inv Eq1.
      inv H1. 2: { destruct_or!; congruence. }
      simpl. unfold etherPop in H9. case_match. destruct l0. 1,3: congruence.
      inv H9.
      inv H; simpl in H0.
      + contradiction.
      + contradiction.
      + reflexivity.
      + reflexivity.
    - exists D. split. assumption. by right.
Qed.
