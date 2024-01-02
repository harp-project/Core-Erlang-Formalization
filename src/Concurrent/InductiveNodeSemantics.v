From CoreErlang.Concurrent Require Export NodeSemantics.
From CoreErlang.FrameStack Require Export SubstSemanticsLemmas.

Import ListNotations.

(** Refexive, transitive closure, with action logs: *)
Reserved Notation "n -[ l ]ₙ->* n'" (at level 50).
Inductive closureNodeSem : Node -> list (Action * PID) -> Node -> Prop :=
| n_refl n (* n'  *): (* Permutation n n' -> *) n -[ [] ]ₙ->* n (* ' *)
| n_trans n n' n'' l a ι:
  n -[a|ι]ₙ-> n' -> n' -[l]ₙ->* n''
->
  n -[(a,ι)::l]ₙ->* n''
where "n -[ l ]ₙ->* n'" := (closureNodeSem n l n').

(* Properties *)

Theorem closureNodeSem_trans :
  forall n n' l, n -[l]ₙ->* n' -> forall n'' l', n' -[l']ₙ->* n''
->
  n -[l ++ l']ₙ->* n''.
Proof.
  intros n n' l D1; induction D1; intros; simpl.
  * exact H.
  * eapply n_trans. exact H.
    eapply (IHD1 _ _ H0).
Qed.

Theorem closureNodeSem_trans_rev :
  forall l n n'' l', n -[l ++ l']ₙ->* n''
->
  exists n', n -[l]ₙ->* n' /\ n' -[l']ₙ->* n''.
Proof.
  induction l; simpl; intros.
  * exists n. split; auto. constructor.
  * inversion H; subst. apply IHl in H5 as [n'2 [H5_1 H5_2]].
    exists n'2. split; auto.
    econstructor; eassumption.
Qed.

Definition internals (n n' : Node) : Prop :=
  exists l, Forall (fun e => e.1 = τ) l /\ n -[l]ₙ->* n'.

Notation "n -->* n'" := (internals n n') (at level 50).

Theorem internals_refl :
  forall n, n -->* n.
Proof.
  intros. exists []. split; auto. constructor.
Qed.

Theorem internals_trans :
  forall n n' n'', n -->* n' -> n' -->* n''
->
  n -->* n''.
Proof.
  intros. destruct H as [l1 [All1 D1]]. destruct H0 as [l2 [All2 D2]].
  exists (l1 ++ l2). split.
  * now apply Forall_app.
  * eapply closureNodeSem_trans; eassumption.
Qed.

Theorem bool_from_lit_val :
  forall y e, Some y = bool_from_lit e -> VALCLOSED e.
Proof.
  destruct e; intros; inversion H.
  now constructor.
Qed.

Definition onlyOne (a : Action) (ι : PID) (n n''' : Node) :=
  exists n' n'', n -->* n' /\ n' -[a|ι]ₙ-> n'' /\ n'' -->* n'''.

Notation "n -[* a | ι *]-> n'" := (onlyOne a ι n n') (at level 60).

Lemma process_local_determinism :
  forall p p' a, p -⌈a⌉-> p' -> forall p'', p -⌈a⌉-> p'' -> p' = p''.
Proof.
  intros p p' a IH. induction IH; intros; try now inv H.
  * inv H0; try (now inv H; cbn in *; invSome).
    - eapply step_determinism in H. 2: exact H7. destruct H. now subst.
  * inv H0; firstorder; subst; try congruence.
  * inv H0; firstorder; subst; try congruence.
  * inv H0; firstorder; subst; try congruence.
  * inv H0; firstorder; subst; try congruence.
  * now inv H0.
  * now inv H0.
  * now inv H0.
  * inv H0.
    - rewrite H in H6. now inv H6.
    - congruence.
  * inv H0.
    - congruence.
    - reflexivity.
  * inv H0. rewrite H in H6. now inv H6.
  * inv H.
    - inv H6. cbn in *. invSome.
    - now auto.
    - congruence.
  * inv H1.
    - inv H8. cbn in *. invSome.
    - now auto.
    - congruence.
  * inv H0. rewrite <-H in H7. now inv H7.
Qed.

Lemma insert_eq : forall {K T} {H : EqDecision K} {H0: Countable K} ι (p p' : T) (Π Π' : gmap K T),
  <[ι:=p]>Π = <[ι:=p']> Π' -> p = p'.
Proof.
  intros. apply map_eq_iff with (i := ι) in H1.
  setoid_rewrite lookup_insert in H1. now inv H1.
Qed.

Lemma insert_eq_Π : forall {K T} {H : EqDecision K} {H0: Countable K} ι (p p' : T) (Π Π' : gmap K T),
  <[ι:=p]>Π = <[ι:=p']>Π' -> forall p'', <[ι:=p'']>Π = <[ι:=p'']>Π'.
Proof.
  intros.
  apply map_eq_iff. intro ι''.
  apply map_eq_iff with (i := ι'') in H1.
  destruct (decide (ι'' = ι)).
  * subst. now setoid_rewrite lookup_insert.
  * setoid_rewrite lookup_insert_ne in H1; auto.
  setoid_rewrite lookup_insert_ne; auto.
Qed.

Lemma concurrent_determinism :
  forall Π a ι Π', Π -[a | ι]ₙ-> Π' -> forall Π'', Π -[a | ι]ₙ-> Π'' -> Π' = Π''.
Proof.
  intros Π a ι Π' IH. inversion IH; intros; subst.
  * inv H4.
    - apply insert_eq in H2 as H2'. subst.
      eapply process_local_determinism in H. 2:exact H8. subst. auto. f_equal.
      apply map_eq_iff. intros ι''.
      apply map_eq_iff with (i := ι'') in H2.
      destruct (decide (ι = ι'')).
      + subst. now setoid_rewrite lookup_insert.
      + setoid_rewrite lookup_insert_ne; auto.
        setoid_rewrite lookup_insert_ne in H2; auto.
    - intuition; try congruence.
  * inv H5.
    - apply insert_eq in H2 as H2'. subst.
      eapply process_local_determinism in H0. 2:exact H10. subst.
      rewrite H in H9. inv H9. f_equal.
      apply map_eq_iff. intros ι''.
      apply map_eq_iff with (i := ι'') in H2.
      destruct (decide (ι = ι'')).
      + subst. now setoid_rewrite lookup_insert.
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
      + subst. now setoid_rewrite lookup_insert.
      + setoid_rewrite lookup_insert_ne; auto.
        setoid_rewrite lookup_insert_ne in H2; auto.
    - intuition; try congruence.
  * inv H9.
    - intuition; try congruence.
    - apply insert_eq in H6 as H6'. subst.
      eapply process_local_determinism in H4. 2: exact H18. subst.
      f_equal. rewrite H in H11. inv H11.
      rewrite H3 in H17. inv H17.
      apply map_eq_iff. intros ι''.
      apply map_eq_iff with (i := ι'') in H6.
      destruct (decide (ι' = ι'')).
      + subst. now setoid_rewrite lookup_insert.
      + setoid_rewrite lookup_insert_ne; auto.
        destruct (decide (ι = ι'')).
        ** subst. now setoid_rewrite lookup_insert.
        ** setoid_rewrite lookup_insert_ne; auto.
           setoid_rewrite lookup_insert_ne in H6; auto.
Qed.

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
      + eexists. split. constructor. left. now constructor.
      + eexists. split. constructor. left. now constructor.
    - inv H.
      + eexists. split. constructor. assumption. left. now constructor.
      + eexists. split. constructor. assumption. left. now constructor.
      + eexists. split. constructor. assumption. left. now constructor.
    - inv H.
      + eexists. split. apply p_exit_terminate. eassumption. now right.
      + eexists. split. apply p_exit_terminate. eassumption. now right.
      + eexists. split. apply p_exit_terminate. eassumption. now right.
    - inv H.
      + eexists. split. apply p_exit_convert; auto. left. now constructor.
      + eexists. split. apply p_exit_convert; auto. left. now constructor.
      + eexists. split. apply p_exit_convert; auto. left. now constructor.
    - inv H.
      all: eexists; split; [constructor|];left; now constructor.
    - inv H.
      all: eexists; split; [constructor|];left; now constructor.
  * exfalso. inv H0; inv H. inv H6; cbn in *; invSome.
  * exfalso. inv H0; inv H. inv H7; cbn in *; invSome.
  * left. eapply process_local_determinism in H; eauto.
  * exfalso. inv H0; inv H; try (now inv H7 + now inv H6).
    congruence.
Qed.

Theorem internal_is_alive :
  forall p p', p -⌈τ⌉-> p' -> exists pa, p = inl pa.
Proof.
  intros. inversion H; subst; try (do 2 eexists; split; reflexivity).
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
  forall n n' n'' ι a, n -[τ | ι]ₙ-> n' -> n -[a | ι]ₙ-> n''
->
  (a = τ /\ n''= n') \/ (exists t ι', a = AArrive ι' ι t /\
                                 exists n''', n' -[AArrive ι' ι t | ι]ₙ-> n''' /\
                                 (n'' -[τ | ι]ₙ-> n''' \/ n'' = n''')).
Proof.
  intros. inv H; inv H0.
  * exfalso. inv H7.
    - apply insert_eq in H4. subst. inv H1. inv H7. now cbn in *.
    - apply insert_eq in H4. subst. inv H1. inv H7. now cbn in *.
    - apply insert_eq in H4. subst. inv H1. inv H7. now cbn in *.
    - apply insert_eq in H4. subst. inv H1. inv H7. now cbn in *.
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
      exact H3. reflexivity. Unshelve. exact (inr []).
    - right. subst. setoid_rewrite insert_eq_Π. reflexivity. eassumption.
      reflexivity. Unshelve. exact (inr []).
  * apply insert_eq in H3 as H3'. subst.
    destruct H8 as [H8 | [ H8 | H8]].
    - subst. left. split; auto. eapply process_local_determinism in H4. 2: exact H1.
      subst. eapply insert_eq_Π in H3. now rewrite H3.
    - subst. exfalso. inv H4. inv H1. inv H8.
      now cbn in *.
    - subst. exfalso. inv H4; inv H1; try inv H9; try inv H8; try now cbn in *.
  * apply insert_eq in H3 as H3'. subst.
    exfalso. inv H12. inv H1. inv H14. now cbn in *.
Qed.

Definition bothSpawn (a1 a2 : Action) : Prop:=
match a1, a2 with
| ASpawn _ _ _, ASpawn _ _ _ => True
| _, _ => False
end.

Definition compatiblePIDOf (a1 a2 : Action) :=
match a1, a2 with
| ASend _ ι1 _, ASpawn ι2 _ _
| ASpawn ι1 _ _, ASend _ ι2 _
| ASpawn ι1 _ _ , ASpawn ι2 _ _ => (ι1 <> ι2)%type
| _, _ => True
end.

(*

  n ---- ι:a ----> n'
  |                ∥
  | ι':a'          ∥ ι':a'
  |                ∥
  v                v
  n'' == ι:a ===> n'''

*)

Tactic Notation "put" constr(f) "on" constr(H) "as" ident(name) :=
match type of H with
| ?p = ?q => assert (name : f p = f q) by (now rewrite H + now setoid_rewrite H)
end.

Lemma confluence :
  forall n n' ι a, n -[a | ι]ₙ-> n' -> forall n'' a' ι' 
    (Spawns : compatiblePIDOf a a'),
   n -[a' | ι']ₙ-> n'' ->
  ι <> ι'
->
  exists n''', n' -[a' | ι']ₙ-> n''' /\ n'' -[a | ι]ₙ-> n'''.
Proof.
  intros n n' ι a IH. inv IH; intros; subst.
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
               setoid_rewrite lookup_insert in H4.
               setoid_rewrite lookup_insert_ne in H4.
               setoid_rewrite lookup_insert_ne. all: auto.
             * setoid_rewrite lookup_insert_ne at 1 in H4.
               setoid_rewrite lookup_insert_ne at 1.
               all: auto.
           }
        now constructor.
      + setoid_rewrite insert_commute.
        rewrite etherAdd_swap. 2-3: now auto.
        replace (ι'0 ↦ p'0 ∥ prs0) with (ι ↦ p ∥ ι'0 ↦ p'0 ∥ prs) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H4.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1.
               setoid_rewrite lookup_insert in H4.
               setoid_rewrite lookup_insert_ne in H4.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H4 at 2; auto.
               destruct (decide (ι'' = ι'0)).
               - subst.
                 setoid_rewrite lookup_insert; auto.
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
             * subst. setoid_rewrite lookup_insert at 1.
               setoid_rewrite lookup_insert in H3.
               setoid_rewrite lookup_insert_ne in H3.
               setoid_rewrite lookup_insert_ne. all: auto.
             * setoid_rewrite lookup_insert_ne at 1 in H3.
               setoid_rewrite lookup_insert_ne at 1.
               all: auto.
           }
        constructor. 2: eauto.
        now apply etherPop_greater.
      + setoid_rewrite insert_commute. 2: now auto.
        replace (ι'0 ↦ p'0 ∥ prs0) with (ι ↦ p ∥ ι'0 ↦ p'0 ∥ prs) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H3.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1.
               setoid_rewrite lookup_insert in H3.
               setoid_rewrite lookup_insert_ne in H3.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H3 at 2; auto.
               destruct (decide (ι'' = ι'0)).
               - subst.
                 setoid_rewrite lookup_insert; auto.
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
             * subst. setoid_rewrite lookup_insert at 1.
               setoid_rewrite lookup_insert in H3.
               setoid_rewrite lookup_insert_ne in H3.
               setoid_rewrite lookup_insert_ne. all: auto.
             * setoid_rewrite lookup_insert_ne at 1 in H3.
               setoid_rewrite lookup_insert_ne at 1.
               all: auto.
           }
        apply n_other; eauto.
      + setoid_rewrite insert_commute. 2: now auto.
        replace (ι'0 ↦ p'0 ∥ Π) with (ι ↦ p ∥ ι'0 ↦ p'0 ∥ prs) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H3.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1.
               setoid_rewrite lookup_insert in H3.
               setoid_rewrite lookup_insert_ne in H3.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H3 at 2; auto.
               destruct (decide (ι'' = ι'0)).
               - subst.
                 setoid_rewrite lookup_insert; auto.
               - setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in H3; auto.
           }
        now constructor.
    - exists (etherAdd ι ι' t ether, 
              ι'1 ↦ inl ([], r, emptyBox, [], false) ∥ ι'0 ↦ p'0 ∥ ι ↦ p' ∥ prs).
      split.
      + replace (ι ↦ p' ∥ prs) with (ι'0 ↦ p0 ∥ ι ↦ p' ∥ prs) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H3.
             destruct (decide (ι'' = ι'0)).
             * subst. setoid_rewrite lookup_insert at 1.
               setoid_rewrite lookup_insert in H3.
               setoid_rewrite lookup_insert_ne in H3.
               setoid_rewrite lookup_insert_ne. all: auto.
             * setoid_rewrite lookup_insert_ne at 1 in H3.
               setoid_rewrite lookup_insert_ne at 1.
               all: auto.
           }
        eapply n_spawn; try eassumption.
        ** clear -H5 H6 H1 H3.
           put (dom : ProcessPool -> _) on H3 as H3'.
           epose proof dom_insert_subseteq Π ι p'.
           set_solver.
        ** intro. apply isUsedEther_etherAdd_rev in H0. congruence.
           cbn in Spawns. intro. subst. now apply Spawns.
      + destruct (decide (ι = ι'1)). {
          subst.
          apply map_eq_iff with (i := ι'1) in H3.
          setoid_rewrite lookup_insert in H3.
          setoid_rewrite lookup_insert_ne in H3. 2: now auto.
          apply not_elem_of_dom in H5. congruence.
        }
        setoid_rewrite insert_commute with (j := ι).
        setoid_rewrite insert_commute with (j := ι).
        2-3: now auto.
        replace (ι'1 ↦ inl ([], r, emptyBox, [], false) ∥ ι'0 ↦ p'0 ∥ Π) with
          (ι ↦ p ∥ ι'1 ↦ inl ([], r, emptyBox, [], false) ∥ ι'0 ↦ p'0 ∥ prs).
        2: { apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H3.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1.
               setoid_rewrite lookup_insert in H3.
               setoid_rewrite lookup_insert_ne in H3.
               setoid_rewrite lookup_insert_ne.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H3 at 2; auto.
               destruct (decide (ι'' = ι'1)).
               - subst.
                 setoid_rewrite lookup_insert; auto.
               - setoid_rewrite lookup_insert_ne; auto.
                 destruct (decide (ι'' = ι'0)).
                 + subst. now setoid_rewrite lookup_insert.
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
             * subst. setoid_rewrite lookup_insert at 1.
               setoid_rewrite lookup_insert in H5.
               setoid_rewrite lookup_insert_ne in H5.
               setoid_rewrite lookup_insert_ne. all: auto.
             * setoid_rewrite lookup_insert_ne at 1 in H5.
               setoid_rewrite lookup_insert_ne at 1.
               all: auto.
           }
        now constructor.
      + setoid_rewrite insert_commute. 2: now auto.
        replace (ι' ↦ p'0 ∥ prs0) with (ι ↦ p ∥ ι' ↦ p'0 ∥ prs) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H5.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1.
               setoid_rewrite lookup_insert in H5.
               setoid_rewrite lookup_insert_ne in H5.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H5 at 2; auto.
               destruct (decide (ι'' = ι')).
               - subst.
                 setoid_rewrite lookup_insert; auto.
               - setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in H5; auto.
           }
        constructor; auto.
        now apply etherPop_greater.
    - assert (exists ether'', etherPop ι2 ι' ether'  = Some (t0, ether''))
                                 as [ether'' Eq].
      {
         unfold etherPop in H, H5. do 2 break_match_hyp; try congruence.
         break_match_hyp. 2: congruence.
         inv Heql0. destruct l1; try congruence. inv H. inv H5.
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
             * subst. setoid_rewrite lookup_insert at 1.
               setoid_rewrite lookup_insert in H4.
               setoid_rewrite lookup_insert_ne in H4.
               setoid_rewrite lookup_insert_ne. all: auto.
             * setoid_rewrite lookup_insert_ne at 1 in H4.
               setoid_rewrite lookup_insert_ne at 1.
               all: auto.
           }
        constructor; auto.
      + setoid_rewrite insert_commute. 2: now auto.
        replace (ι' ↦ p'0 ∥ prs0) with (ι ↦ p ∥ ι' ↦ p'0 ∥ prs) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H4.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1.
               setoid_rewrite lookup_insert in H4.
               setoid_rewrite lookup_insert_ne in H4.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H4 at 2; auto.
               destruct (decide (ι'' = ι')).
               - subst.
                 setoid_rewrite lookup_insert; auto.
               - setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in H4; auto.
           }
        constructor; auto.
        clear -H H5 H2 Eq. unfold etherPop in *.
        repeat break_match_hyp; try congruence. do 3 invSome.
        setoid_rewrite lookup_insert_ne. 2: intro D; inv D; auto.
        setoid_rewrite Heqo1. do 2 f_equal.
        setoid_rewrite insert_commute at 1. 2: intro D; inv D; auto. f_equal.
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
             * subst. setoid_rewrite lookup_insert at 1.
               setoid_rewrite lookup_insert in H4.
               setoid_rewrite lookup_insert_ne in H4.
               setoid_rewrite lookup_insert_ne. all: auto.
             * setoid_rewrite lookup_insert_ne at 1 in H4.
               setoid_rewrite lookup_insert_ne at 1.
               all: auto.
           }
        now constructor.
      + setoid_rewrite insert_commute. 2: now auto.
        replace (ι' ↦ p'0 ∥ Π) with (ι ↦ p ∥ ι' ↦ p'0 ∥ prs) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H4.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1.
               setoid_rewrite lookup_insert in H4.
               setoid_rewrite lookup_insert_ne in H4.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H4 at 2; auto.
               destruct (decide (ι'' = ι')).
               - subst.
                 setoid_rewrite lookup_insert; auto.
               - setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in H4; auto.
           }
        now apply n_arrive.
    - exists (ether', ι'0 ↦ inl ([],r, emptyBox, [], false) ∥ ι' ↦ p'0 ∥ ι ↦ p' ∥ prs).
      split.
      + replace (ι ↦ p' ∥ prs) with (ι' ↦ p0 ∥ ι ↦ p' ∥ prs) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H4.
             destruct (decide (ι'' = ι')).
             * subst. setoid_rewrite lookup_insert at 1.
               setoid_rewrite lookup_insert in H4.
               setoid_rewrite lookup_insert_ne in H4.
               setoid_rewrite lookup_insert_ne. all: auto.
             * setoid_rewrite lookup_insert_ne at 1 in H4.
               setoid_rewrite lookup_insert_ne at 1.
               all: auto.
           }
        eapply n_spawn; eauto.
        ** clear -H6 H7 H2 H4.
           put (dom : ProcessPool -> _) on H4 as H4'.
           epose proof dom_insert_subseteq Π ι p'.
           set_solver.
        ** intro. cbn in Spawns.
           eapply isUsedEther_etherPop_rev in H1. 2: eassumption.
           congruence.
      + assert (ι <> ι'0). {
          apply map_eq_iff with (i := ι) in H4.
          setoid_rewrite lookup_insert in H4.
          setoid_rewrite lookup_insert_ne in H4. 2: now auto.
          clear -H4 H6. apply elem_of_dom_2 in H4. set_solver.
        }
        setoid_rewrite insert_commute with (j := ι).
        setoid_rewrite insert_commute with (j := ι).
        2-3: now auto.
        replace (ι'0 ↦ inl ([], r, emptyBox, [], false) ∥ ι' ↦ p'0 ∥ Π) with
          (ι ↦ p ∥ ι'0 ↦ inl ([], r, emptyBox, [], false) ∥ ι' ↦ p'0 ∥ prs).
        2: { apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H4.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1.
               setoid_rewrite lookup_insert in H4.
               setoid_rewrite lookup_insert_ne in H4.
               setoid_rewrite lookup_insert_ne.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H4 at 2; auto.
               destruct (decide (ι'' = ι'0)).
               - subst.
                 setoid_rewrite lookup_insert; auto.
               - setoid_rewrite lookup_insert_ne; auto.
                 destruct (decide (ι'' = ι')).
                 + subst. now setoid_rewrite lookup_insert.
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
             * subst. setoid_rewrite lookup_insert at 1.
               setoid_rewrite lookup_insert in H5.
               setoid_rewrite lookup_insert_ne in H5.
               setoid_rewrite lookup_insert_ne. all: auto.
             * setoid_rewrite lookup_insert_ne at 1 in H5.
               setoid_rewrite lookup_insert_ne at 1.
               all: auto.
           }
        now constructor.
      + setoid_rewrite insert_commute. 2: now auto.
        replace (ι' ↦ p'0 ∥ prs) with (ι ↦ p ∥ ι' ↦ p'0 ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H5.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1.
               setoid_rewrite lookup_insert in H5.
               setoid_rewrite lookup_insert_ne in H5.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H5 at 2; auto.
               destruct (decide (ι'' = ι')).
               - subst.
                 setoid_rewrite lookup_insert; auto.
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
               setoid_rewrite lookup_insert in H4.
               setoid_rewrite lookup_insert_ne in H4.
               setoid_rewrite lookup_insert.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
           }
        constructor; auto.
      + setoid_rewrite insert_commute. 2: now auto.
        replace (ι' ↦ p'0 ∥ prs) with (ι ↦ p ∥ ι' ↦ p'0 ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H4.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1.
               setoid_rewrite lookup_insert in H4.
               setoid_rewrite lookup_insert_ne in H4.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H4 at 2; auto.
               destruct (decide (ι'' = ι')).
               - subst.
                 setoid_rewrite lookup_insert; auto.
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
               setoid_rewrite lookup_insert in H4.
               setoid_rewrite lookup_insert_ne in H4.
               setoid_rewrite lookup_insert.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
           }
        now constructor.
      + setoid_rewrite insert_commute. 2: now auto.
        replace (ι' ↦ p'0 ∥ Π0) with (ι ↦ p ∥ ι' ↦ p'0 ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H4.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1.
               setoid_rewrite lookup_insert in H4.
               setoid_rewrite lookup_insert_ne in H4.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H4 at 2; auto.
               destruct (decide (ι'' = ι')).
               - subst.
                 setoid_rewrite lookup_insert; auto.
               - setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in H4; auto.
           }
        now constructor.
    - exists (ether, ι'0 ↦ inl ([], r, emptyBox, [], false) ∥ ι' ↦ p'0 ∥ ι ↦ p' ∥ Π).
      split.
      + replace (ι ↦ p' ∥ Π) with (ι' ↦ p0 ∥ ι ↦ p' ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H4.
             destruct (decide (ι'' = ι')).
             * subst.
               setoid_rewrite lookup_insert in H4.
               setoid_rewrite lookup_insert_ne in H4.
               setoid_rewrite lookup_insert.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
           }
        eapply n_spawn; eauto.
        ** clear -H6 H7 H2 H4.
           put (dom : ProcessPool -> _) on H4 as H4'.
           epose proof dom_insert_subseteq Π ι p'.
           set_solver.
      + assert (ι <> ι'0). {
          apply map_eq_iff with (i := ι) in H4.
          setoid_rewrite lookup_insert in H4.
          setoid_rewrite lookup_insert_ne in H4. 2: now auto.
          clear -H4 H6. apply elem_of_dom_2 in H4. set_solver.
        }
        setoid_rewrite insert_commute with (j := ι).
        setoid_rewrite insert_commute with (j := ι).
        2-3: now auto.
        replace (ι'0 ↦ inl ([], r, emptyBox, [], false) ∥ ι' ↦ p'0 ∥ Π0) with
          (ι ↦ p ∥ ι'0 ↦ inl ([], r, emptyBox, [], false) ∥ ι' ↦ p'0 ∥ Π).
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H4.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1.
               setoid_rewrite lookup_insert in H4.
               setoid_rewrite lookup_insert_ne in H4.
               setoid_rewrite lookup_insert_ne.
               setoid_rewrite lookup_insert_ne.
               all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H4 at 2; auto.
               destruct (decide (ι'' = ι'0)).
               - subst.
                 setoid_rewrite lookup_insert; auto.
               - setoid_rewrite lookup_insert_ne; auto.
                 destruct (decide (ι'' = ι')).
                 + subst. now setoid_rewrite lookup_insert.
                 + setoid_rewrite lookup_insert_ne in H4; auto.
                   setoid_rewrite lookup_insert_ne; auto.
           }
        now constructor.
  * inv H5.
    - exists (etherAdd ι'0 ι'1 t ether, ι'0 ↦ p'0 ∥
                                        ι' ↦ inl ([], r, emptyBox, [], false) ∥
                                        ι ↦ p' ∥ Π).
      split.
      + replace (ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) with 
                (ι'0 ↦ p0 ∥ ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H9.
             destruct (decide (ι'' = ι'0)).
             * subst.
               setoid_rewrite lookup_insert in H9.
               setoid_rewrite lookup_insert_ne in H9; auto.
               setoid_rewrite lookup_insert.
               destruct (decide (ι'0 = ι')).
               - subst. apply not_elem_of_dom in H0. congruence.
               - setoid_rewrite lookup_insert_ne.
                 setoid_rewrite lookup_insert_ne.
                 all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
           }
        constructor; now eauto.
      + assert (ι'0 <> ι'). {
          apply map_eq_iff with (i := ι') in H9.
          setoid_rewrite lookup_insert_ne at 2 in H9. 2: now auto.
          destruct (decide (ι'0 = ι')); auto. subst.
          setoid_rewrite lookup_insert in H9.
          clear -H9 H0. apply not_elem_of_dom in H0. congruence.
        }
        setoid_rewrite insert_commute with (j := ι').
        setoid_rewrite insert_commute with (j := ι).
        2-3: now auto.
        replace (ι'0 ↦ p'0 ∥ prs) with
          (ι ↦ p ∥ ι'0 ↦ p'0 ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H9.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1.
               setoid_rewrite lookup_insert in H9.
               setoid_rewrite lookup_insert_ne in H9; auto.
               setoid_rewrite lookup_insert_ne; auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H9 at 2; auto.
               destruct (decide (ι'' = ι'0)).
               - subst.
                 setoid_rewrite lookup_insert; auto.
               - setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in H9; auto.
           }
         eapply n_spawn; eauto.
        ** clear -H5 H6 H0 H9.
           put (dom : ProcessPool -> _) on H9 as H9'.
           epose proof dom_insert_subseteq Π ι p'0.
           set_solver.
        ** intro. apply isUsedEther_etherAdd_rev in H7. congruence.
           cbn in Spawns. intro. subst. now apply Spawns.
    - exists (ether', ι'0 ↦ p'0 ∥ ι' ↦ inl ([], r, emptyBox, [], false) 
                          ∥ ι ↦ p' ∥ Π ).
      split.
      + replace (ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) with 
                (ι'0 ↦ p0 ∥ ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H8.
             destruct (decide (ι'' = ι'0)).
             * subst.
               setoid_rewrite lookup_insert in H8.
               setoid_rewrite lookup_insert_ne in H8; auto.
               setoid_rewrite lookup_insert.
               destruct (decide (ι'0 = ι')).
               - subst. apply not_elem_of_dom in H0. congruence.
               - setoid_rewrite lookup_insert_ne.
                 setoid_rewrite lookup_insert_ne.
                 all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
           }
        constructor; auto.
      + assert (ι'0 <> ι'). {
          apply map_eq_iff with (i := ι') in H8.
          setoid_rewrite lookup_insert_ne at 2 in H8. 2: now auto.
          destruct (decide (ι'0 = ι')); auto. subst.
          setoid_rewrite lookup_insert in H8.
          clear -H8 H0. apply not_elem_of_dom in H0. congruence.
        }
        setoid_rewrite insert_commute with (j := ι').
        setoid_rewrite insert_commute with (j := ι).
        2-3: now auto.
        replace (ι'0 ↦ p'0 ∥ prs) with
          (ι ↦ p ∥ ι'0 ↦ p'0 ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H8.
             destruct (decide (ι'' = ι)).
             * subst. setoid_rewrite lookup_insert at 1.
               setoid_rewrite lookup_insert in H8.
               setoid_rewrite lookup_insert_ne in H8; auto.
               setoid_rewrite lookup_insert_ne; auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               setoid_rewrite lookup_insert_ne in H8 at 2; auto.
               destruct (decide (ι'' = ι'0)).
               - subst.
                 setoid_rewrite lookup_insert; auto.
               - setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in H8; auto.
           }
         eapply n_spawn; eauto.
         ** clear -H5 H6 H0 H8.
            put (dom : ProcessPool -> _) on H8 as H8'.
            epose proof dom_insert_subseteq Π ι p'0.
            set_solver.
         ** intro. eapply isUsedEther_etherPop_rev in H7. 2: eassumption.
            congruence.
    - exists (ether, ι'0 ↦ p'0 ∥ ι' ↦ inl ([], r, emptyBox, [], false)
                               ∥ ι ↦ p' ∥ Π).
      split.
      + replace (ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) with 
                (ι'0 ↦ p0 ∥ ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H8.
             destruct (decide (ι'' = ι'0)).
             * subst.
               setoid_rewrite lookup_insert in H8.
               setoid_rewrite lookup_insert_ne in H8; auto.
               setoid_rewrite lookup_insert.
               destruct (decide (ι'0 = ι')).
               - subst. apply not_elem_of_dom in H0. congruence.
               - setoid_rewrite lookup_insert_ne.
                 setoid_rewrite lookup_insert_ne.
                 all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
           }
        now constructor.
      + assert (ι'0 <> ι'). {
          apply map_eq_iff with (i := ι') in H8.
          setoid_rewrite lookup_insert_ne at 2 in H8. 2: now auto.
          destruct (decide (ι'0 = ι')); auto. subst.
          setoid_rewrite lookup_insert in H8.
          clear -H8 H0. apply not_elem_of_dom in H0. congruence.
        }
        setoid_rewrite insert_commute with (j := ι').
        setoid_rewrite insert_commute with (j := ι).
        2-3: now auto.
        replace (ι'0 ↦ p'0 ∥ Π0) with
          (ι ↦ p ∥ ι'0 ↦ p'0 ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H8.
             destruct (decide (ι'' = ι)).
             * subst.
               setoid_rewrite lookup_insert in H8.
               setoid_rewrite lookup_insert_ne in H8; auto.
               setoid_rewrite lookup_insert.
               setoid_rewrite lookup_insert_ne; auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               destruct (decide (ι'' = ι'0)).
               - subst.
                 setoid_rewrite lookup_insert; auto.
               - setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in H8; auto.
           }
         eapply n_spawn; eauto.
         ** clear -H5 H6 H0 H8.
            put (dom : ProcessPool -> _) on H8 as H8'.
            epose proof dom_insert_subseteq Π ι p'0.
            set_solver.
    - (** cannot be sure to generate different spawn PID-s *)
      exists (ether, ι'1 ↦ inl ([], r0, emptyBox, [], false) ∥ ι'0 ↦ p'0 ∥ ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π).
      split.
      + replace (ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) with
                (ι'0 ↦ p0 ∥ ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H8.
             destruct (decide (ι'' = ι'0)).
             * subst.
               setoid_rewrite lookup_insert in H8.
               setoid_rewrite lookup_insert_ne in H8; auto.
               setoid_rewrite lookup_insert.
               destruct (decide (ι'0 = ι')).
               - subst. apply not_elem_of_dom in H0. congruence.
               - setoid_rewrite lookup_insert_ne.
                 setoid_rewrite lookup_insert_ne.
                 all: auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
           }
        eapply n_spawn; try eassumption.
        clear -H8 H6 H10 H0 H1 H11 Spawns. cbn in *.
        put (dom : ProcessPool -> _) on H8 as H8'. simpl in H8'.
        apply map_eq_iff with (i := ι'1) in H8.
        setoid_rewrite lookup_insert_ne in H8 at 1; auto.
        repeat setoid_rewrite dom_insert_L.
        setoid_rewrite dom_insert_L in H8'.
        set_solver. (* slightly slow *)
      + assert (ι'0 <> ι' /\ ι'1 <> ι /\ ι'1 <> ι'). {
          clear -H8 H6 H10 H0 H1 H11 Spawns. cbn in *.
          put (dom : ProcessPool -> _) on H8 as H8'. simpl in H8'.
          apply map_eq_iff with (i := ι'1) in H8.
          setoid_rewrite lookup_insert_ne in H8 at 1; auto.
          repeat setoid_rewrite dom_insert_L.
          setoid_rewrite dom_insert_L in H8'.
          set_solver. (* slightly slow *)
        }
        destruct_and!.
        setoid_rewrite insert_commute with (j := ι').
        setoid_rewrite insert_commute with (j := ι').
        setoid_rewrite insert_commute with (j := ι).
        setoid_rewrite insert_commute with (j := ι).
        2-5: now auto.
        replace (ι'1 ↦ inl ([], r0, emptyBox, [], false) ∥ ι'0 ↦ p'0 ∥ Π0) with
          (ι ↦ p ∥ ι'1 ↦ inl ([], r0, emptyBox, [], false) ∥ ι'0 ↦ p'0 ∥ Π) at 1.
        2: {
             apply map_eq_iff.
             intros ι''.
             apply map_eq_iff with (i := ι'') in H8.
             destruct (decide (ι'' = ι)).
             * subst.
               setoid_rewrite lookup_insert in H8.
               setoid_rewrite lookup_insert_ne in H8; auto.
               setoid_rewrite lookup_insert.
               setoid_rewrite lookup_insert_ne; auto.
               setoid_rewrite lookup_insert_ne; auto.
             * setoid_rewrite lookup_insert_ne at 1; auto.
               destruct (decide (ι'' = ι'1)).
               - subst.
                 setoid_rewrite lookup_insert; auto.
               - setoid_rewrite lookup_insert_ne; auto.
                 destruct (decide (ι'' = ι'0)).
                 + subst.
                   setoid_rewrite lookup_insert; auto.
                 + setoid_rewrite lookup_insert_ne in H8; auto.
                   setoid_rewrite lookup_insert_ne; auto.
           }
         eapply n_spawn; eauto.
         ** put (dom : ProcessPool -> _) on H8 as H8'.
            setoid_rewrite dom_insert_L in H8'.
            setoid_rewrite dom_insert_L.
            setoid_rewrite dom_insert_L.
            clear -H8' H7 H5 H15 H0.
            set_solver.
Qed.


(* Corollary chain_to_end :
  forall n n' l, n -[l]ₙ->* n' -> Forall (fun a => a.1 = τ) l -> 
   forall n'' a ι, n -[a | ι]ₙ-> n''
->
  (exists n3 n4 l1 l2, a = AInternal /\ 
    n -[l1]ₙ->* n3 /\ n3 -[a |ι]ₙ-> n4 /\ n4 -[l2]ₙ->* n' /\
    l = l1 ++ [(a, ι)] ++ l2
  ) \/ 
  (exists n''', n' -[a | ι]ₙ-> n''').
Proof.
  intros n n' l Steps.
  dependent induction Steps; intros.
  * right. eexists. eauto.
  * inversion H0; subst. simpl in H4. subst.
    destruct (Nat.eq_dec ι ι0); subst.
    - eapply internal_det in H1 as H1'. 2: exact H.
      destruct H1' as [[eq1 eq2] | [t H0']]; subst.
      + left. exists n, n', [], l. split; auto.
        split. 2: split. constructor.
        auto.
        split; auto.
      + destruct H0' as [source [eq [n''' [D _]]]]. subst.
        inversion H1; subst.
        2: { intuition; try congruence. destruct H4; congruence. }
        specialize (IHSteps H5 _ _ _ D).
           destruct IHSteps as [[n3 [n4 [l1 [l2 H2]]]]| [n3 D2]].
           -- left. destruct H2 as [eq1 [D1 [D2 [ D3 eq2]]]]. subst.
              congruence.
           -- right. eexists; eauto.
    - eapply step_chain in H1. 2: exact H. 2-3: auto.
      destruct H1. eapply IHSteps in H1 as H1'; auto.
      destruct H1' as [[n3 [n4 [l1 [l2 H2]]]] | [t H0']]; subst.
      + left. destruct H2 as [eq1 [D1 [D2 [ D3 eq2]]]]. subst.
        exists n3, n4, ((AInternal, ι)::l1), l2. split; auto.
        split. 2: split. 3: split. all: auto.
        eapply n_trans. 2: exact D1. auto.
      + right. now exists t.
Qed.

Lemma internal_keep :
  forall n n' ι, n -[AInternal | ι]ₙ-> n'
->
  forall x, x <> ι -> snd n x = snd n' x.
Proof.
  intros. inversion H; subst.
  simpl. unfold update. break_match_goal; auto. eqb_to_eq. congruence.
Qed.

(* general case wont work: message ordering is not the same *)
Theorem diamond_derivations :
  forall n1 n2 n3 n4 a ι1 ι2, ι1 <> ι2 ->
  n1 -[AInternal | ι1]ₙ-> n2 -> n1 -[a | ι2]ₙ-> n3 -> n2 -[a | ι2]ₙ-> n4
->
  n3 -[AInternal | ι1]ₙ-> n4.
Proof.
  intros.
  inversion H2; subst.
  * inversion H1; subst.
    2: { intuition; try congruence. destruct H6; congruence. }
    inversion H0; subst.
    assert (p = p0). {
      apply internal_keep with (x := ι2) in H0. simpl in H0.
      unfold update in H0. break_match_hyp. now inversion H0. eqb_to_eq. congruence.
      auto.
    }
    subst.
    subst. eapply internal_determinism in H3. 2: exact H10. subst.
    assert ((ι1 : p1 ∥ ι2 : p' ∥ prs0) = ι1 : p1 ∥ ι2 : p' ∥ prs) as EQ. {
      extensionality x. unfold update in *. break_match_goal; auto.
      apply internal_keep with (x := x) in H0. simpl in H0.
      break_match_goal; auto. eqb_to_eq. auto.
    }
    replace (ι2 : p' ∥ prs0) with (ι1 : p1 ∥ ι2 : p' ∥ prs0).
    replace (ι2 : p' ∥ prs) with (ι1 : p'1 ∥ ι2 : p' ∥ prs).
    rewrite EQ. constructor; auto.
    all: unfold update in *; extensionality x; 
         apply equal_f with x in H5; apply equal_f with x in H12;
         do 2 break_match_goal; eqb_to_eq; subst; auto; congruence.
  * inversion H1; subst.
    inversion H0; subst.
    2: { intuition; try congruence. destruct H7; congruence. }
    assert (p = p0). {
      apply internal_keep with (x := ι2) in H0. simpl in H0.
      unfold update in H0. break_match_hyp. now inversion H0. eqb_to_eq. congruence.
      auto.
    }
    subst.
    subst. eapply internal_determinism in H4. 2: exact H12. subst.
    assert ((ι1 : p1 ∥ ι2 : p' ∥ prs0) = ι1 : p1 ∥ ι2 : p' ∥ prs) as EQ. {
      extensionality x. unfold update in *. break_match_goal; auto.
      apply internal_keep with (x := x) in H0. simpl in H0.
      break_match_goal; auto. eqb_to_eq. auto.
    }
    replace (ι2 : p' ∥ prs0) with (ι1 : p1 ∥ ι2 : p' ∥ prs0).
    replace (ι2 : p' ∥ prs) with (ι1 : p'1 ∥ ι2 : p' ∥ prs).
    rewrite EQ. rewrite H3 in H11. inversion H11. subst. constructor; auto.
    all: unfold update in *; extensionality x; 
         apply equal_f with x in H6; apply equal_f with x in H14;
         do 2 break_match_goal; eqb_to_eq; subst; auto; congruence.
  * inversion H1; subst.
    1,2,4,5: intuition; try congruence;
      match goal with
      | [H : exists _, _ |- _] => destruct H; congruence
      | _ => idtac
      end.
    - inversion H0; subst.
      assert (p = inr []). {
        apply internal_keep with (x := ι2) in H0. simpl in H0.
        unfold update in H0. break_match_hyp. now inversion H0. eqb_to_eq. congruence.
        auto.
      }
      subst.
      inversion H3.
    - inversion H0; subst.
      assert (p = p0). {
        apply internal_keep with (x := ι2) in H0. simpl in H0.
        unfold update in H0. break_match_hyp. now inversion H0. eqb_to_eq. congruence.
        auto.
      }
      subst.
      subst. eapply internal_determinism in H3. 2: exact H5. subst.
      assert ((ι1 : p1 ∥ ι2 : p' ∥ Π0) = ι1 : p1 ∥ ι2 : p' ∥ Π) as EQ. {
        extensionality x. unfold update in *. break_match_goal; auto.
        apply internal_keep with (x := x) in H0. simpl in H0.
        break_match_goal; auto. eqb_to_eq. auto.
      }
      replace (ι2 : p' ∥ Π0) with (ι1 : p1 ∥ ι2 : p' ∥ Π0).
      replace (ι2 : p' ∥ Π) with (ι1 : p'1 ∥ ι2 : p' ∥ Π).
      rewrite EQ. constructor; auto.
      1-2: unfold update in *; extensionality x; 
           apply equal_f with x in H8; apply equal_f with x in H13;
           do 2 break_match_goal; eqb_to_eq; subst; auto; congruence.
  * inversion H1; subst.
    1: intuition; try congruence; destruct H8; congruence.
    inversion H0; subst.
    assert (p = p0). {
      apply internal_keep with (x := ι2) in H0. simpl in H0.
      unfold update in H0. break_match_hyp. now inversion H0. eqb_to_eq. congruence.
      auto.
    }
    subst.
    subst. eapply internal_determinism in H5. 2: exact H14. subst.
    assert ((ι1 : p1 ∥ ι' : inl ([], EApp v1 l0, [], [], false) ∥ ι2 : p' ∥ Π0) = 
             ι1 : p1 ∥ ι' : inl ([], EApp v1 l0, [], [], false) ∥ ι2 : p' ∥ Π) as EQ. {
      extensionality x. unfold update in *. break_match_goal; auto.
      break_match_goal; auto.
      apply internal_keep with (x := x) in H0. simpl in H0.
      break_match_goal; auto.
      eqb_to_eq. auto.
    }
    rewrite H3 in H10. inversion H10. subst.
    replace (ι' : inl ([], EApp v1 l0, [], [], false) ∥ ι2 : p' ∥ Π0) with
            (ι1 : p1 ∥ ι' : inl ([], EApp v1 l0, [], [], false) ∥ ι2 : p' ∥ Π0).
    replace (ι' : inl ([], EApp v1 l0, [], [], false) ∥ ι2 : p' ∥ Π) with
            (ι1 : p'1 ∥ ι' : inl ([], EApp v1 l0, [], [], false) ∥ ι2 : p' ∥ Π).
    rewrite EQ. apply n_other; auto.
    clear EQ H1 H2 H0.
    all: unfold update in *; extensionality x;
         apply equal_f with x in H7; apply equal_f with x in H15;
         do 2 break_match_goal; eqb_to_eq; subst; auto; try congruence.
    - break_match_goal; eqb_to_eq; auto. subst. congruence.
    - break_match_goal; eqb_to_eq; auto. subst. congruence.
  * inversion H1; subst.
    1: intuition; try congruence. destruct H5; congruence.
    - inversion H0; subst.
      assert (p = inr []). {
        apply internal_keep with (x := ι2) in H0. simpl in H0.
        unfold update in H0. break_match_hyp. now inversion H0. eqb_to_eq. congruence.
        auto.
      }
      subst.
      inversion H3.
    - inversion H0. subst.
      assert ((ι1 : p ∥ (Π0 -- ι2)) = 
               ι1 : p ∥ (Π  -- ι2)) as EQ. {
        extensionality x. unfold update in *. break_match_goal; auto.
        apply internal_keep with (x := x) in H0. simpl in H0.
        break_match_goal; auto. eqb_to_eq. auto.
      }
      replace (Π0 -- ι2) with
              (ι1 : p ∥ (Π0 -- ι2)).
      replace (Π -- ι2) with
              (ι1 : p' ∥ (Π -- ι2)).
      rewrite EQ. constructor; auto.
      all: unfold update in *; extensionality x;
       apply equal_f with x in H4; apply equal_f with x in H9;
       do 2 break_match_goal; eqb_to_eq; subst; auto; try congruence.
Qed.

Theorem delay_internal_same :
  forall n n1 ι,   n -[AInternal | ι]ₙ-> n1 ->
  forall n2 a, n1 -[a | ι]ₙ-> n2 ->
       forall n3, n -[a | ι]ₙ-> n3
->
  n3 -[AInternal | ι]ₙ-> n2 \/ n3 = n2.
Proof.
  intros. inversion H; subst.
  eapply internal_det in H1 as H1'. 2: exact H.
  destruct H1' as [[eq1 eq2]| [t [? [eq [n'' D]]]]]; subst.
  * auto.
  * inversion H0; subst.
    2: { intuition; try congruence; destruct H3; congruence. }
    simpl. apply insert_eq in H5 as H5'. subst.
    inversion H1; subst.
    - simpl. apply insert_eq in H6 as H5'. subst.
      clear H9 H7 H3.
      replace (ι : p'1 ∥ prs0) with (ι : p'1 ∥ prs).
      2: { extensionality xx.
           apply equal_f with xx in H5. apply equal_f with xx in H6.
           unfold update in *. break_match_hyp; auto. now rewrite <- H5 in H6.
         }
      rewrite H11 in H15. inversion H15. subst.
      inversion H12; subst.
      + left. apply n_other.
        inversion H16; subst.
        ** inversion H2; subst. now constructor.
        ** auto.
      (* drop signal *)
      + intuition. subst.
        all: inversion H16; subst; intuition; subst; try congruence.
        ** left. constructor. inversion H2; subst. now constructor. auto.
        ** left. constructor. inversion H2; subst. auto. auto.
        ** left. constructor. inversion H2; subst. auto.
        ** left. constructor. inversion H2; subst. auto.
        ** left. constructor. inversion H2; subst. now constructor. auto.
        ** left. constructor. inversion H2; subst. auto. auto.
        ** inversion H2.
        ** inversion H2.
        ** inversion H2; subst. left. now do 2 constructor.
        ** inversion H2; subst. left. now do 2 constructor.
        ** inversion H2; subst. left. congruence.
        ** inversion H2; subst. left. congruence.
        ** inversion H2; subst. left. now do 2 constructor.
        ** inversion H2; subst. left. now do 2 constructor.
        ** inversion H2; subst. left. congruence.
        ** inversion H2; subst. left. congruence.
      (* terminate process *)
      + inversion H2; subst. inversion H16; subst; intuition; subst; try congruence.
        all: now right.
      (* add signal to message queue *)
      + intuition. subst.
        all: inversion H16; subst; intuition; subst; try congruence.
        all: left; constructor; inversion H2; subst; auto.
        ** constructor; auto.
        ** constructor; auto.
        ** congruence.
        ** constructor; auto.
        ** congruence.
        ** constructor; auto.
      + left. apply n_other.
        inversion H16; subst.
        ** inversion H2; subst. now constructor.
        ** auto.
      + left. apply n_other.
        inversion H16; subst.
        ** inversion H2; subst. now constructor.
        ** auto.
    - intuition; subst; try congruence. now inversion H3.
      now inversion H3.
      now inversion H3.
      now inversion H3.
Qed.

Corollary chain_to_front_iff :
  forall n n', n -->* n' -> forall a ι n'' n3, (* a <> AInternal -> *)
  n' -[a | ι]ₙ-> n'' ->
  n  -[a | ι]ₙ-> n3
->
  n3 -->* n''.
Proof.
  intros n n' D.
  destruct D as [l [All D]]. induction D; intros.
  * eapply concurrent_determinism in H. 2: exact H0. subst. apply internals_refl.
  * inversion All; simpl in H4. subst.
    destruct (Nat.eq_dec ι0 ι).
    - subst.
      eapply internal_det in H1 as H2'. 2: exact H.
      destruct H2' as [[? ?] | [t [ι' [? [n4 [D1 _]]]]]]; subst.
      + eapply internals_trans.
        exists l. split; eauto.
        exists [(AInternal, ι)]. split. repeat constructor.
        eapply n_trans; eauto. constructor.
      + epose proof (delay_internal_same _ _ _ H _ _ D1 _ H1).
        epose proof (IHD H5 _ _ _ _ H0 D1).
        eapply internals_trans. 2: exact H3.
        destruct H2.
        ** exists [(AInternal, ι)]. split. repeat constructor.
           eapply n_trans. exact H2. apply n_refl.
        ** subst. apply internals_refl.
    - apply not_eq_sym in n0.
      epose proof (D2 := step_chain _ _ _ _ H _ _ _ _ H1 n0).
      destruct D2 as [n4 D2].
      epose proof (IHD H5 _ _ _ _ H0 D2).

      eapply internals_trans. 2: exact H2.
      exists [(AInternal, ι)]. split. repeat constructor.
      eapply n_trans. 2: apply n_refl.
      clear IHD H5 D All H2 H0.
      now epose proof (diamond_derivations _ _ _ _ _ _ _ n0 H H1 D2).
  Unshelve.
  ** intro. destruct a0; auto.
Qed. *)

Theorem split_reduction :
  forall l1 l2 Π Π'', Π -[l1 ++ l2]ₙ->* Π'' ->
   exists Π', Π -[l1]ₙ->* Π' /\
                    Π' -[l2]ₙ->* Π''.
Proof.
  intros. dependent induction H.
  * exists n. intuition; destruct l1, l2; inversion x; constructor.
  * destruct l1; simpl in *.
    - destruct l2; inversion x; subst; clear x.
      specialize (IHclosureNodeSem [] l2 eq_refl).
      destruct IHclosureNodeSem as [Π' [D1 D2]].
      exists n. intuition. constructor.
      econstructor.
      + inversion D1; subst. exact H.
      + auto.
    - inversion x; subst; clear x.
      specialize (IHclosureNodeSem l1 l2 eq_refl).
      destruct IHclosureNodeSem as [Π' [D1 D2]].
      exists Π'. intuition. econstructor. exact H. auto.
Qed.

Lemma no_ether_pop : forall l Π Π',
  Π -[ l ]ₙ->* Π' ->
  forall ι ι' sigs s sigs',
  ~In (AArrive ι ι' s, ι') l ->
  fst Π !! (ι, ι') = Some (sigs ++ s :: sigs') ->
  exists sigs1 sigs2, fst Π' !! (ι, ι') = Some (sigs1 ++ s :: sigs' ++ sigs2) /\ 
                      exists sigs1_1, sigs = sigs1_1 ++ sigs1.
Proof.
  intros ? ? ? D. induction D; intros.
  * eexists. exists []. rewrite app_nil_r. split. exact H0.
    exists []. reflexivity.
  * apply not_in_cons in H0 as [H0_1 H0_2].
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
        specialize (IHD eq_refl) as [sigs1 [sigs2 [IHD' IHD'']]].
        rewrite IHD'. exists sigs1. exists ([t] ++ sigs2).
        do 2 f_equal. now rewrite app_assoc.
      + break_match_hyp; simpl in IHD; apply IHD; auto;
        setoid_rewrite lookup_insert_ne; auto.
    (* Arrive: potentially removes something *)
    - cbn in *.
      destruct (ι0 =? ι2) eqn:Eq1.
      + destruct (ι' =? ι) eqn:Eq2.
        ** eqb_to_eq. subst.
           destruct sigs.
           -- unfold etherPop in H0. rewrite H1 in H0. cbn in H0. inversion H0.
              congruence.
           -- unfold etherPop in H0. break_match_hyp. 2: congruence.
              destruct l0. congruence.
              inversion H0. inversion H1. subst. clear H0 H1.
              specialize (IHD ι2 ι sigs s sigs' H0_2).
              setoid_rewrite lookup_insert in IHD.
              specialize (IHD eq_refl).
              destruct IHD as [sigs1 [sigs2 [Eq1 [sigs1_1 Eq2]]]].
              subst. do 2 eexists. split. eauto. exists (s0 :: sigs1_1).
              simpl. reflexivity.
        ** unfold etherPop in H0. break_match_hyp. 2: congruence.
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
(*     - eapply IHD. auto. cbn in *. rewrite H1. reflexivity. *)
Qed.

(** Signal ordering tests: *)
Lemma signal_ordering :
  forall l Π (ι ι' : PID) s1 s2 Π' Π'' Π''' (NEQ : s1 <> s2),
            Π -[ASend ι ι' s1 | ι]ₙ-> Π' ->
            Π' -[ASend ι ι' s2 | ι]ₙ-> Π'' ->
            ~In (AArrive ι ι' s1, ι') l ->
            (forall l, fst Π !! (ι, ι') = Some l -> ~In s1 l) ->
            (forall l, fst Π !! (ι, ι') = Some l -> ~In s2 l) ->
            Π'' -[l]ₙ->* Π''' ->
            ~exists Σ, Π''' -[AArrive ι ι' s2 | ι']ₙ-> Σ.
Proof.
  intros. inv H. inv H0.
  2-3: intuition; try congruence.
  cbn in *.
  (* inversion H13; subst. clear H13. *)
  assert (exists sigs sigs', etherAdd ι ι' s2 (etherAdd ι ι' s1 ether) !! (ι, ι') = Some (sigs ++ s1 :: sigs')) as [sigs1 [sigs2 H]]. {
    unfold etherAdd. destruct (ether !! (ι, ι')); do 2 setoid_rewrite lookup_insert. 
    * exists l0, [s2]. now rewrite <- app_assoc.
    * now exists [], [s2].
  }
  epose proof (no_ether_pop l _ _ H4 _ _ _ _ _ H1 H).
  intro. destruct H8 as [Π''''].
  destruct H0 as [sigs11 [sigs3]].
  clear H1 H4. inv H8.
  2: { intuition; try congruence. }
  destruct H0 as [H0 H0_1].
  cbn in *. unfold etherPop in H15. rewrite H0 in H15.
  destruct sigs11; cbn in *. inv H15. congruence.
  cbn in *. inv H15.
  unfold etherAdd in H. destruct (ether !! (ι, ι')); do 2 setoid_rewrite lookup_insert in H; try rewrite <- app_assoc in H; inv H.
  * destruct H0_1. subst.
    specialize (H2 l0 eq_refl). specialize (H3 l0 eq_refl).
    rewrite <- app_assoc in H4.
    apply in_list_order in H4; auto.
  * destruct H0_1. subst.
    destruct x. simpl in H4. inv H4. congruence.
    put (length : list Signal -> nat) on H4 as Hlen.
    simpl in Hlen. repeat rewrite app_length in Hlen. simpl in Hlen. lia.
Qed.

Lemma no_spawn_included :
  forall l n n', n -[l]ₙ->* n' ->
    forall ι, ~In ι (PIDsOf spawnPIDOf l) ->
      n.2 !! ι = None <-> n'.2 !! ι = None.
Proof.
  intros. induction H; auto;
  unfold PIDsOf in H0; simpl in H0; fold (PIDsOf spawnPIDOf l) in H0;
  apply not_in_app in H0 as [H0_1 H0_2]; apply IHclosureNodeSem in H0_2;
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
  * assert (ι' <> ι) by (clear- H0_1; firstorder). clear H4.
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
  * assert (ι' <> ι) by (clear- H0_1; firstorder). clear H4.
    setoid_rewrite lookup_insert_ne in I; auto.
    try (destruct (decide (ι0 = ι)); subst; [
       setoid_rewrite lookup_insert in I;
       try congruence
     |
       setoid_rewrite lookup_insert_ne in I; auto;
       setoid_rewrite lookup_insert_ne; auto;
       intro Z; now apply I in Z
     ]).
Qed.

Lemma no_spawn_included_2 :
  forall l n n', n -[l]ₙ->* n' ->
    forall ι, n'.2 !! ι = None ->
    ~In ι (PIDsOf spawnPIDOf l).
Proof.
  induction l using list_length_ind.
  intros. destruct (length l) eqn:Hlen.
  * apply length_zero_iff_nil in Hlen. subst. auto.
  * apply eq_sym, last_element_exists in Hlen as Hlen'.
    destruct Hlen' as [l' [x ?]]; subst.
    rename n' into n''.
    apply closureNodeSem_trans_rev in H0 as [n' [D1 D2]].
    rewrite app_length in Hlen. simpl in Hlen. inv D2. inv H6. inv H4.
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
         }
      unfold PIDsOf. rewrite flat_map_app. apply app_not_in.
      1-2: fold (PIDsOf spawnPIDOf l'); simpl; auto.
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
         }
      unfold PIDsOf. rewrite flat_map_app. apply app_not_in.
      1-2: fold (PIDsOf spawnPIDOf l'); simpl; auto.
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
         }
      unfold PIDsOf. rewrite flat_map_app. apply app_not_in.
      1-2: fold (PIDsOf spawnPIDOf l'); simpl; auto.
      destruct a; simpl; auto.
      destruct H2 as [? | [? | ?]]; congruence.
    - unfold PIDsOf. rewrite flat_map_app. apply app_not_in.
      1-2: fold (PIDsOf spawnPIDOf l'); simpl.
      + eapply H. lia. eassumption.
        simpl in *. clear H5.
        destruct (decide (ι' = ι)); subst.
        1: setoid_rewrite lookup_insert in H1; congruence.
        setoid_rewrite lookup_insert_ne in H1; auto.
        simpl in *; destruct (decide (ι0 = ι)); subst; [
          setoid_rewrite lookup_insert in H1;
          try congruence
        |
          setoid_rewrite lookup_insert_ne in H1; auto;
          setoid_rewrite lookup_insert_ne; auto;
          intro Z; now apply I in Z
        ].
      + intro. destruct H4. 2: auto. subst.
        simpl in H1. now setoid_rewrite lookup_insert in H1.
Qed.

(* TODO: generalize *)
Ltac processpool_destruct :=
match goal with
| [H : (?ι0 ↦ _ ∥ _) !! ?ι = _ |- _] =>
  simpl in *; destruct (decide (ι0 = ι)); subst; [
    setoid_rewrite lookup_insert in H
  |
    setoid_rewrite lookup_insert_ne in H; auto
  ]
| [|- (?ι0 ↦ _ ∥ _) !! ?ι = _] =>
  simpl in *; destruct (decide (ι0 = ι)); subst; [
    setoid_rewrite lookup_insert
  |
    setoid_rewrite lookup_insert_ne; auto
  ]
| [H : (?ι0 ↦ _ ∥ _) !! ?ι ≠ _ |- _] =>
  simpl in *; destruct (decide (ι0 = ι)); subst; [
    setoid_rewrite lookup_insert in H
  |
    setoid_rewrite lookup_insert_ne in H; auto
  ]
| [|- (?ι0 ↦ _ ∥ _) !! ?ι ≠ _] =>
  simpl in *; destruct (decide (ι0 = ι)); subst; [
    setoid_rewrite lookup_insert
  |
    setoid_rewrite lookup_insert_ne; auto
  ]
end.

Ltac processpool_destruct_manual_hyp ι0 ι H :=
  simpl in *; destruct (decide (ι0 = ι)); subst; [
    setoid_rewrite lookup_insert in H
  |
    setoid_rewrite lookup_insert_ne in H; auto
  ].

Ltac processpool_destruct_manual ι0 ι :=
  simpl in *; destruct (decide (ι0 = ι)); subst; [
    setoid_rewrite lookup_insert
  |
    setoid_rewrite lookup_insert_ne; auto
  ].

Lemma processes_dont_die_None :
  forall l n n', n -[l]ₙ->* n' ->
    forall ι, n'.2 !! ι = None -> n.2 !! ι = None.
Proof.
  induction l using list_length_ind.
  destruct (length l) eqn:Hl; intros.
  * apply length_zero_iff_nil in Hl; subst. inv H0. auto.
  * pose proof Hl.
    eapply eq_sym, last_element_exists in Hl as [l' [x Eq]]. subst.
    apply closureNodeSem_trans_rev in H0 as [n0' [D1 D2]].
    rewrite app_length in H2. simpl in *.
    inv D2. inv H7.
    eapply H in D1; eauto. lia. inv H5; simpl.
    1-3: repeat processpool_destruct; try congruence.
    clear -H3 H1. simpl in *.
    destruct (decide (ι' = ι)); subst.
    1: setoid_rewrite lookup_insert in H1; congruence.
    setoid_rewrite lookup_insert_ne in H1; auto.
    repeat processpool_destruct; try congruence.
Qed.

Lemma processes_dont_die :
  forall n n' l, n -[l]ₙ->* n' ->
    forall ι, n.2 !! ι <> None -> n'.2 !! ι <> None.
Proof.
  intros. induction H; auto.
  apply IHclosureNodeSem. clear IHclosureNodeSem H1. inv H.
  all: simpl in *.
  1-3: repeat processpool_destruct; auto.
  * clear H5.
    repeat processpool_destruct; try congruence.
Qed.


Corollary processes_dont_die_Some :
  forall n n' l, n -[l]ₙ->* n' ->
    forall ι p, n.2 !! ι = Some p -> exists p', n'.2 !! ι = Some p'.
Proof.
  intros.
  epose proof (processes_dont_die _ _ _ H ι _).
  Unshelve. 2: { intro D. rewrite D in H0. congruence. }
  destruct (n'.2 !! ι). eexists. reflexivity.
  congruence.
Qed.

Definition SIGCLOSED s :=
match s with
 | SMessage e => VALCLOSED e
 | SExit r b => VALCLOSED r
 | SLink => True
 | SUnlink => True
end.

Definition ether_wf (ether : Ether) :=
  forall ι ι' l, ether !! (ι, ι') = Some l -> Forall SIGCLOSED l.

Lemma ether_wf_etherAdd :
  forall ι ι' t ether,
    SIGCLOSED t ->
    ether_wf ether ->
      ether_wf (etherAdd ι ι' t ether).
Proof.
  intros. unfold etherAdd. intros i1 i2.
  specialize (H0 i1 i2).
  break_match_goal.
  * intros. destruct (decide ((ι, ι') = (i1, i2))).
    - inv e. setoid_rewrite lookup_insert in H1. inv H1.
      apply H0 in Heqo. apply Forall_app. split; auto.
    - setoid_rewrite lookup_insert_ne in H1; auto.
  * intros. destruct (decide ((ι, ι') = (i1, i2))).
    - inv e. setoid_rewrite lookup_insert in H1. inv H1. auto.
    - setoid_rewrite lookup_insert_ne in H1; auto.
Qed.

Lemma SIGCLOSED_derivation :
  forall p p' source dest s, p -⌈ASend source dest s⌉-> p' ->
    SIGCLOSED s.
Proof.
  intros. inv H; cbn; auto.
Qed.


Theorem ether_wf_preserved :
  forall n n' l, n -[l]ₙ->* n' ->
    ether_wf n.1 -> ether_wf n'.1.
Proof.
  intros n n' l H. induction H; intros; auto.
  apply IHclosureNodeSem. clear H0 IHclosureNodeSem.
  inv H; simpl; try assumption.
  * apply ether_wf_etherAdd; auto.
    now apply SIGCLOSED_derivation in H0.
  * unfold etherPop in H0. break_match_hyp. 2: congruence.
    destruct l0. congruence.
    inv H0. simpl in H1. unfold ether_wf in *.
    intros. specialize (H1 ι0 ι'). clear -H1 Heqo H.
    destruct (decide ((ι1, ι) = (ι0, ι'))); try invSome; subst; [
      setoid_rewrite lookup_insert in H
    |
      setoid_rewrite lookup_insert_ne in H; auto
    ].
    invSome. apply H1 in Heqo. now inv Heqo.
Qed.

Lemma no_spawn_on_Some :
  forall n n' l, n -[l]ₙ->* n' ->
    forall ι, n.2 !! ι <> None ->
      ~In ι (PIDsOf spawnPIDOf l).
Proof.
  intros n n' l H. induction H; intros; simpl; auto.
  intro Ha. inv H; simpl in *.
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
  * clear H5.
    destruct Ha.
    - subst. setoid_rewrite lookup_insert_ne in H1; auto.
      now apply not_elem_of_dom in H3.
    - assert ((ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) !! ι0 <> None). {
      repeat processpool_destruct; auto.
    }
    apply IHclosureNodeSem in H; auto.
Qed.

Proposition isUsedEther_dec :
  forall ι ether, isUsedEther ι ether \/ ~isUsedEther ι ether.
Proof.
  intros.
  unfold isUsedEther.
  remember (base.filter (fun '((ιs, ιd), l) => ι = ιd /\ l <> []) ether) as newmap.
  destruct (map_eq_dec_empty newmap).
  * right. intro. destruct H as [x [y [l H]]].
    subst newmap.
    destruct (ether !! (x, ι)) eqn:P. 2: congruence. destruct l0. congruence.
    eapply map_filter_empty_not_lookup with (i := (x, ι)) (x := s :: l) in e.
    inv H. contradiction. auto.
  * left.
    apply map_choose in n as n'. destruct n' as [x [l H]].
    destruct x.
    subst newmap. exists p.
    apply map_lookup_filter_Some_1_2 in H as H'. destruct H'.
    apply map_lookup_filter_Some_1_1 in H. subst.
    destruct l; try congruence. setoid_rewrite H. now do 2 eexists.
Qed.

Lemma isUsedEther_no_spawn :
  forall n n' l, n -[l]ₙ->* n' ->
    forall ι, isUsedEther ι n.1 ->
      ~In ι (PIDsOf spawnPIDOf l).
Proof.
  intros n n' l H. induction H; intros; simpl; auto.
  intro Ha. inv H; simpl in *.
  * pose proof (isUsedEther_etherAdd ether _ ι ι' t H1). apply IHclosureNodeSem in H.
    congruence.
  * apply (@isUsedEther_etherPop _ ι0) in H2 as [H2 | H2]; try assumption.
    now apply IHclosureNodeSem in H2.
    subst. remember (ether', ι ↦ p' ∥ prs) as n.
    assert (n.2 !! ι <> None). {
      subst n. cbn. now setoid_rewrite lookup_insert.
    }
    eapply no_spawn_on_Some in H0. 2: eassumption. congruence.
  * destruct a; simpl in *; try now apply IHclosureNodeSem in Ha.
    destruct H3 as [? | [? | ?]]; congruence.
  * clear H6. destruct Ha. congruence.
    apply IHclosureNodeSem in H; auto.
Qed.


(* ------------------------- *)

Definition isUntaken (ι : PID) (n : Node) : Prop :=
  n.2 !! ι = None /\ isUsedEther ι n.1.

Theorem compatibility_of_reduction :
  forall n n' a ι, n -[a | ι]ₙ-> n' ->
    forall ι, isUntaken ι n ->
      (isUntaken ι n' (* \/ spawnPIDOf a = Some ι /\ exists p, n'.2 ι = Some p *)).
Proof.
  intros. inv H.
  * (* left. *) destruct H0. split.
    - simpl in *. repeat processpool_destruct; congruence.
    - simpl in *. now apply isUsedEther_etherAdd.
  * (* left. *) destruct H0. split.
    - simpl in *. repeat processpool_destruct; congruence.
    - simpl in *. eapply isUsedEther_etherPop in H1 as [H1 | H1].
      + eassumption.
      + subst. repeat processpool_destruct; congruence.
      + assumption.
  * (* left. *) destruct H0. split.
    - simpl in *. repeat processpool_destruct; congruence.
    - assumption.
  * destruct H0. simpl in *.
    repeat processpool_destruct; try congruence.
    destruct (Nat.eq_dec ι0 ι').
    - subst.
      epose proof (isUsedEther_no_spawn (ether, ι ↦ p ∥ Π) (ether, ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) [(ASpawn ι' v1 v2, ι)] _ _ H0).
      simpl in H7. lia.
      Unshelve. econstructor. eapply n_spawn; try eassumption.
                constructor.
      (*  right. split; auto.
      eexists. unfold update. rewrite Nat.eqb_refl. reflexivity. *)
    -(*  left. *) split.
      + simpl. repeat processpool_destruct; congruence.
      + simpl. assumption.
Qed.


Corollary compatibility_of_reductions :
   forall n n' l, n -[l]ₙ->* n' ->
    forall ι, isUntaken ι n ->
      (isUntaken ι n' (* \/ In ι (PIDsOf spawnPIDOf l) /\ exists p, n'.2 ι = Some p *)).
Proof.
  intros n n' l H. induction H; intros; auto.
  apply (compatibility_of_reduction _ _ _ _ H) in H1(*  as [H1 | [H1_1 H1_2]] *).
  * now apply IHclosureNodeSem in H1. (*  destruct H1 as [? | [? ?]]; auto.
    right. simpl. break_match_goal; simpl; auto.
  * right. simpl. rewrite H1_1. split. now constructor.
    destruct H1_2. eapply processes_dont_die_Some in H1. eassumption.
    eauto. *)
Qed.



Theorem compatibility_of_reduction_rev :
  forall n n' a ι, n -[a | ι]ₙ-> n' ->
    forall ι,
      isUntaken ι n' ->
      isUntaken ι n \/
      (sendPIDOf a = Some ι /\ ~isUsedEther ι n.1 /\ n.2 !! ι = None).
(*       (spawnPIDOf a = Some ι /\ n.2 ι = None). *)
Proof.
  intros. inv H.
  * destruct H0.
    destruct (Nat.eq_dec ι' ι0); simpl; subst.
    - simpl in *.
      destruct (isUsedEther_dec ι0 ether).
      + left. split. simpl. repeat processpool_destruct; congruence.
        now simpl.
      + right. split; simpl; auto.
        split; auto. repeat processpool_destruct; congruence.
    - left. split.
      + simpl in *. repeat processpool_destruct; congruence.
      + simpl in *. eapply isUsedEther_etherAdd_rev. eassumption. assumption.
  * destruct H0. left. split.
    - simpl in *. repeat processpool_destruct; congruence.
    - simpl in *. eapply isUsedEther_etherPop_rev; eassumption.
  * destruct H0. left. split.
    - simpl in *. repeat processpool_destruct; congruence.
    - assumption.
  * clear H3 H4 H1. destruct H0. simpl in *.
    destruct (Nat.eq_dec ι0 ι').
    - subst. left. split.
      + repeat processpool_destruct; congruence.
      + now simpl.
    - left. split.
      + simpl. repeat processpool_destruct; congruence.
      + simpl. assumption.
Qed.

Corollary compatibility_of_reductions_rev :
   forall l n n', n -[l]ₙ->* n' ->
    forall ι,
      isUntaken ι n' ->
      isUntaken ι n \/
      (In ι (PIDsOf sendPIDOf l) /\ ~isUsedEther ι n.1 /\ n.2 !! ι = None).
Proof.
  induction l using list_length_ind.
  destruct (length l) eqn:Hl; intros.
  * apply length_zero_iff_nil in Hl; subst. inv H0. auto.
  * pose proof Hl.
    eapply eq_sym, last_element_exists in Hl as [l' [x Eq]]. subst.
    apply closureNodeSem_trans_rev in H0 as [n0' [D1 D2]].
    rewrite app_length in H2. simpl in *.
    inv D2. inv H7. eapply compatibility_of_reduction_rev in H5.
    2: eassumption.
    destruct H5. 2: destruct H0.
    - eapply H in D1. 2: lia. 2: eassumption.
      destruct D1; auto. destruct_hyps.
      right; split. 2: split; auto.
      unfold PIDsOf. rewrite flat_map_app. simpl.
      fold (PIDsOf spawnPIDOf l'). apply in_or_app. now left.
    - destruct_hyps. clear H H2 H1.
      unfold isUntaken.
      eapply processes_dont_die_None in D1 as P3. 2: eassumption.
      destruct (isUsedEther_dec ι n0.1).
      + left. easy.
      + right. split. 2: easy.
        unfold PIDsOf. rewrite flat_map_app.
        apply in_or_app. simpl. right. rewrite H0. now constructor.
Qed.

Lemma no_spawn_unTaken :
  forall n n' l, n -[l]ₙ->* n' ->
    forall ι, isUntaken ι n ->
      ~In ι (PIDsOf spawnPIDOf l).
Proof.
  intros n n' l H. induction H; intros; simpl.
  * congruence.
  * intro Hin. inv H; simpl in *.
    - apply IHclosureNodeSem in Hin. assumption.
      destruct H1. split; simpl in *.
      + repeat processpool_destruct; congruence.
      + now apply isUsedEther_etherAdd.
    - apply IHclosureNodeSem in Hin. assumption.
      destruct H1. split; simpl in *.
      + repeat processpool_destruct; congruence.
      + eapply isUsedEther_etherPop in H2 as [H2 | H2]; try eassumption.
        subst. repeat processpool_destruct; congruence.
    - assert (isUntaken ι0 (ether, ι ↦ p' ∥ Π)). {
        destruct H1; split; auto.
        simpl in *. repeat processpool_destruct; congruence.
      }
      apply IHclosureNodeSem in H. apply H.
      destruct a; auto. destruct H3 as [? | [? | ?]]; congruence.
    - destruct Hin.
      + clear H6. subst. destruct H1. simpl in *. congruence.
      + clear H6. assert (isUntaken ι0 (ether, ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π)). {
          destruct H1; split; auto.
          simpl in *. repeat processpool_destruct; congruence.
        }
        apply IHclosureNodeSem in H6. now apply H6.
Qed.

Lemma included_spawn :
  forall (l : list (Action * PID)) (n n' : Node),
  n -[ l ]ₙ->* n' ->
    forall ι : PID, In ι (PIDsOf spawnPIDOf l) ->
      n'.2 !! ι <> None.
Proof.
  intros l n n' H. induction H; intros.
  * intro. inv H.
  * inv H; simpl in *; try assumption.
    1-3: apply IHclosureNodeSem; try assumption.
    - firstorder; now subst.
    - clear H5. destruct H1. 2: apply IHclosureNodeSem; try assumption.
      subst. apply processes_dont_die with (ι := ι0) in H0; auto.
      cbn. repeat processpool_destruct; congruence.
Qed.

Lemma isUsedEther_after_send :
  forall n n' l, n -[l]ₙ->* n' ->
    forall ι,
      In ι (PIDsOf sendPIDOf l) ->
      ~In ι (PIDsOf spawnPIDOf l) ->
      n.2 !! ι = None ->
      isUsedEther ι n'.1.
Proof.
  intros n n' l H. induction H; intros; simpl; auto.
  * inv H.
  * unfold PIDsOf in H2. simpl in H2. apply not_in_app in H2.
    fold (PIDsOf spawnPIDOf l) in *. destruct H2. inv H.
    - simpl in *. inv H1.
      + apply compatibility_of_reductions with (ι := ι0) in H0.
        2: {
          split; simpl. repeat processpool_destruct; congruence.
          unfold isUsedEther. exists ι. unfold etherAdd.
          break_match_goal; setoid_rewrite lookup_insert; auto.
          2: do 2 eexists; reflexivity.
          destruct l0; do 2 eexists; reflexivity.
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
      lia.
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

Corollary par_comp_assoc_pool (Π1 Π2 : ProcessPool) (ι : PID) (p : Process) :
  (ι ↦ p ∥ Π1) ∪ Π2 = ι ↦ p ∥ (Π1 ∪ Π2).
Proof.
  now setoid_rewrite insert_union_l.
Qed.

(* Theorem par_comp_assoc (eth1 eth2 : Ether) (Π1 Π2 : ProcessPool) (ι : PID) (p : Process) :
  (eth1, ι ↦ p ∥ Π1) ∥∥ (eth2, Π2) = (comp_Ether eth1 eth2, ι ↦ p ∥ (comp_ProcessPool Π1 Π2)).
Proof.

Abort. *)


(* Lemma not_isUsedEther_comp :
  forall eth1 eth2 ι, ~isUsedEther ι eth1 -> ~isUsedEther ι eth2 ->
    ~isUsedEther ι (comp_ether eth1 eth2).
Proof.
  intros. unfold isUsedEther in *.
  firstorder. simpl in *. intro.
  destruct H1. apply (H x). intro.
  apply (H0 x). intro. unfold comp_ether in H1. rewrite H2, H3 in H1.
  simpl in H1. congruence.
Qed. *)

Theorem reduction_is_preserved_by_comp_l :
  forall Π Π' ether ether' a ι,
    (ether, Π) -[a | ι]ₙ-> (ether', Π') ->
    forall (Π2 : ProcessPool),
      (forall ι, spawnPIDOf a = Some ι -> ι ∉ dom Π2) ->
      (ether, Π ∪ Π2) -[a | ι]ₙ-> (ether', Π' ∪ Π2).
Proof.
  intros. inv H; cbn.
  * do 2 rewrite par_comp_assoc_pool. now apply n_send.
  * do 2 rewrite par_comp_assoc_pool. now apply n_arrive.
  * do 2 rewrite par_comp_assoc_pool. now apply n_other.
  * do 3 rewrite par_comp_assoc_pool. econstructor; eauto.
    specialize (H0 _ eq_refl). set_solver.
Qed.

Corollary reductions_are_preserved_by_comp_l : 
  forall Π Π' ether ether' l,
    (ether, Π) -[l]ₙ->* (ether', Π') ->
    forall (Π2 : ProcessPool),
      (forall ι, In ι (PIDsOf spawnPIDOf l) -> ι ∉ dom Π2) ->
      (ether, Π ∪ Π2) -[l]ₙ->* (ether', Π' ∪ Π2).
Proof.
  intros ??????. dependent induction H; intros.
  * constructor.
  * destruct n'. specialize (IHclosureNodeSem _ _ _ _ JMeq_refl JMeq_refl).
    eapply reduction_is_preserved_by_comp_l with (Π2 := Π2) in H.
    2: { intros. apply H1. cbn. apply in_app_iff. left. rewrite H2. now left. }
    econstructor; eauto.
    apply IHclosureNodeSem.
    intros. apply H1. cbn. apply in_app_iff. now right.
Qed.

Theorem reduction_is_preserved_by_comp_r :
  forall Π Π' ether ether' a ι,
    (ether, Π) -[a | ι]ₙ-> (ether', Π') ->
    forall (Π2 : ProcessPool),
      ι ∉ dom Π2 ->
      (forall ι, spawnPIDOf a = Some ι -> ι ∉ dom Π2) ->
      (ether, Π2 ∪ Π) -[a | ι]ₙ-> (ether', Π2 ∪ Π').
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
    2: { specialize (H1 _ eq_refl). now apply not_elem_of_dom. }
    econstructor; eauto.
    specialize (H1 _ eq_refl). set_solver.
Qed.

Corollary reductions_are_preserved_by_comp_r : 
  forall Π Π' ether ether' l,
    (ether, Π) -[l]ₙ->* (ether', Π') ->
    forall (Π2 : ProcessPool),
      (forall ι, In ι (map snd l) -> ι ∉ dom Π2) ->
      (forall ι, In ι (PIDsOf spawnPIDOf l) -> ι ∉ dom Π2) ->
      (ether, Π2 ∪ Π) -[l]ₙ->* (ether', Π2 ∪ Π').
Proof.
  intros ??????. dependent induction H; intros.
  * constructor.
  * destruct n'. specialize (IHclosureNodeSem _ _ _ _ JMeq_refl JMeq_refl).
    eapply reduction_is_preserved_by_comp_r with (Π2 := Π2) in H.
    2: { apply H1. now left. }
    2: { intros. apply H2. cbn. apply in_app_iff. left. rewrite H3. now left. }
    econstructor; eauto.
    apply IHclosureNodeSem.
    intros. apply H1. cbn. now right.
    intros. apply H2. cbn. apply in_app_iff. now right.
Qed.

(* Definition renamePIDPool (p p' : PID) (Π : ProcessPool) : ProcessPool :=
match Π !! p with
| None => Π
| Some proc =>
  <[p' := renamePIDProc p p' proc]>((renamePIDProc p p' <$> Π) -- p)
end.

Notation "e .[ x ↦ y ]ₚₚ" := (renamePIDPool x y e) (at level 2).
 *)

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

(* ONLY keys are symmetrically replaced  *)
Definition renamePIDPool (p p' : PID) (Π : ProcessPool) : ProcessPool :=
  kmap (renamePIDPID_sym p p') (renamePIDProc p p' <$> Π).

Notation "e .[ x ⇔ y ]ₚₚ" := (renamePIDPool x y e) (at level 2).

(* ONLY keys are symmetrically replaced  *)
Definition renamePIDEther (p p' : PID) (eth : Ether) : Ether :=
  kmap (prod_map (renamePIDPID_sym p p') (renamePIDPID_sym p p'))
    ((map (renamePIDSignal p p')) <$> eth).

Notation "e .[ x ⇔ y ]ₑ" := (renamePIDEther x y e) (at level 2).

Definition isUsedPool (ι : PID) (Π : ProcessPool) :=
  Π !! ι <> None \/
  (exists ι' p, Π !! ι' = Some p /\ In ι (usedPIDsProc p)).

Lemma isUsedPool_insert_1 :
  forall prs ι ι0 p,
    isUsedPool ι (ι0 ↦ p ∥ prs) ->
    isUsedPool ι prs \/ ι = ι0 \/ In ι (usedPIDsProc p).
Proof.
  intros. unfold isUsedPool in *. destruct (decide (ι = ι0)).
  * subst. setoid_rewrite lookup_insert in H; intros.
    all: firstorder.
  * setoid_rewrite lookup_insert_ne in H at 1; auto. intros; destruct_or!.
    all: try now firstorder.
    - destruct H as [ι' [p0 [H_1 H_2]]].
      destruct (decide (ι0 = ι')).
      + subst. setoid_rewrite lookup_insert in H_1. inv H_1.
        firstorder.
      + setoid_rewrite lookup_insert_ne in H_1; auto.
        firstorder.
Qed.

Lemma isUsedPool_insert_2 :
  forall prs ι ι0 p,
    (isUsedPool ι prs /\ ι0 ∉ dom prs) \/ ι = ι0 \/ In ι (usedPIDsProc p) ->
    isUsedPool ι (ι0 ↦ p ∥ prs).
Proof.
  intros. unfold isUsedPool in *.
  destruct (decide (ι = ι0)).
  * subst. setoid_rewrite lookup_insert. by left.
  * setoid_rewrite lookup_insert_ne at 1; auto. firstorder.
    - right. exists x, x0. setoid_rewrite lookup_insert_ne. split; auto.
      intro. subst. apply not_elem_of_dom in H0. by setoid_rewrite H in H0.
    - right. exists ι0, p. split; auto.
      by setoid_rewrite lookup_insert.
Qed.

(* Theorem renamePIDPool_lookup :
  forall Π from to ι,
    ¬isUsedPool to Π ->
    renamePIDPool from to Π !! ι = fmap (renamePIDProc from to) (Π !! renamePIDPID from to ι).
Proof.
  intros.
  unfold renamePIDPool.
  unfold kmap.
  Search list_to_map lookup.
  destruct (renamePIDProc from to <$> Π !! renamePIDPID from to ι) eqn:P.
  {
    apply elem_of_list_to_map.
    {
      unfold prod_map.
      Search map_to_list fmap.
      epose proof map_to_list_fmap.
      Search base.NoDup "≡ₚ".
      admit.
    }
    {
      eapply elem_of_list_fmap.
      unfold renamePIDPID in P. case_match; eqb_to_eq.
      * exists (to, p).
      *
      
    }
  }
  {
  
  }
Admitted. *)

(* Theorem renamePIDPool_lookup_same :
  forall Π from to,
    renamePIDPool from to Π !! from = fmap (renamePIDProc from to) (Π !! ι).
Proof.

Admitted. *)

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

Lemma pool_insert_renamePID :
  forall prs ι p from to,
  (ι ↦ p ∥ prs) .[ from ⇔ to ]ₚₚ =
  renamePIDPID_sym from to ι ↦ renamePIDProc from to p ∥ prs .[from ⇔ to]ₚₚ.
Proof.
  intros. unfold renamePIDPool.
  setoid_rewrite <- kmap_insert; auto.
  f_equal. by setoid_rewrite fmap_insert.
Qed.

Lemma rename_eq :
  forall from to ι,
  ι <> to ->
  renamePIDPID_sym from to ι = renamePIDPID from to ι.
Proof.
  unfold renamePIDPID_sym, renamePIDPID. intros.
  case_match; auto. case_match; auto.
  eqb_to_eq; congruence.
Qed.

Lemma mk_list_renamePID :
  forall v from to,
    mk_list (renamePIDVal from to v) = fmap (map (renamePIDVal from to)) (mk_list v).
Proof.
  intros. induction v; simpl; try reflexivity.
  * case_match; reflexivity.
  * rewrite IHv2. by destruct (mk_list v2).
Qed.

Lemma isUsedEther_rename_same_new :
  forall p p' eth, isUsedEther p eth <-> isUsedEther p' (renamePIDEther p p' eth).
Proof.
  split; intro.
  * unfold renamePIDEther, isUsedEther in *.
    destruct H as [ιs [x [l H]]].
    exists (renamePIDPID_sym p p' ιs), (renamePIDSignal p p' x), (map (renamePIDSignal p p') l).
    apply lookup_kmap_Some. auto.
    exists (ιs, p). split. cbn. unfold renamePIDPID_sym. rewrite Nat.eqb_refl. reflexivity.
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
    - unfold renamePIDPID_sym in H2. apply Nat.eqb_neq in n. rewrite n in H2.
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
    exists (renamePIDPID_sym p p' ιs), (renamePIDSignal p p' x), (map (renamePIDSignal p p') l).
    apply lookup_kmap_Some. auto.
    exists (ιs, p'). split. cbn. unfold renamePIDPID_sym. rewrite Nat.eqb_refl.
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
    - unfold renamePIDPID_sym in H2. apply Nat.eqb_neq in n. rewrite n in H2.
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
    exists (renamePIDPID_sym p p' ιs), (renamePIDSignal p p' x), (map (renamePIDSignal p p') l).
    apply lookup_kmap_Some. auto.
    exists (ιs, ι). split. cbn. unfold renamePIDPID_sym. apply Nat.eqb_neq in H, H0.
    now rewrite H, H0.
    rewrite lookup_fmap. setoid_rewrite H1. reflexivity.
  * unfold renamePIDEther, isUsedEther in *.
    destruct H1 as [ιs [x [l H1]]].
    apply lookup_kmap_Some in H1 as [[ιs0 p0] [Eq H1]]. inv Eq. 2: auto.
    rewrite lookup_fmap in H1.
    destruct (eth !! (ιs0, p0)) eqn:P; setoid_rewrite P in H1.
    2: simpl in H1;congruence.
    destruct l0. inv H1.
    unfold renamePIDPID_sym in *. repeat case_match; eqb_to_eq; subst; try congruence.
    do 3 eexists. eassumption.
Qed.

Corollary isUsedEther_renamePID :
  forall ι eth from to,
    isUsedEther ι eth <-> isUsedEther (renamePIDPID_sym from to ι) (renamePIDEther from to eth).
Proof.
  intros. split; intro.
  {
    unfold renamePIDPID_sym. case_match; eqb_to_eq.
    2: case_match; eqb_to_eq.
    * subst. by apply isUsedEther_rename_same_new.
    * subst. by apply isUsedEther_rename_same_old.
    * subst. by apply isUsedEther_rename_same_neq.
  }
  {
    unfold renamePIDPID_sym in H. case_match; eqb_to_eq.
    2: case_match; eqb_to_eq.
    * subst. by apply isUsedEther_rename_same_new in H.
    * subst. by apply isUsedEther_rename_same_old in H.
    * subst. by apply isUsedEther_rename_same_neq in H.
  }
Qed.

Theorem renamePID_is_preserved_node :
  forall eth eth' Π Π' a ι,
    (eth, Π) -[a | ι]ₙ-> (eth', Π') ->
    forall from to,
      ¬ In to (usedPIDsAct a) ->
      ¬ isUsedEther to eth ->
      ¬ isUsedPool to Π ->
      (renamePIDEther from to eth, renamePIDPool from to Π)
    -[renamePIDAct from to a | renamePIDPID_sym from to ι]ₙ->
      (renamePIDEther from to eth', renamePIDPool from to Π').
Proof.
  intros. inv H.
  * simpl in *. rewrite etherAdd_renamePID.
    do 2 rewrite pool_insert_renamePID.
    rewrite <- rename_eq; auto. rewrite <- rename_eq; auto. apply n_send.
    rewrite rename_eq, rename_eq; auto.
    eapply renamePID_is_preserved_local in H7. exact H7.
    all: auto.
    intro. apply H2. apply isUsedPool_insert_2. right. by right.
  * simpl in *. rewrite <- rename_eq, <- rename_eq; auto.
    do 2 rewrite pool_insert_renamePID.
    constructor.
    2: {
      eapply renamePID_is_preserved_local in H10.
      rewrite rename_eq, rename_eq; auto. exact H10.
      all: auto.
      intro. apply H2. apply isUsedPool_insert_2. right. by right.
    }
    rewrite <- etherPop_renamePID, H8. by simpl.
  * simpl in *. do 2 rewrite pool_insert_renamePID.
    constructor.
    eapply renamePID_is_preserved_local in H8. exact H8.
    all: auto.
    intro. apply H2. apply isUsedPool_insert_2. right. by right.
    simpl in *. destruct_or!; subst; simpl; intuition.
    right. left. rewrite rename_eq; auto.
    intro. apply H2. apply isUsedPool_insert_2. right. by left.
  * simpl in *. do 3 rewrite pool_insert_renamePID.
    rewrite <- rename_eq; auto. econstructor.
    - rewrite mk_list_renamePID, H7. reflexivity.
    - unfold renamePIDPool. setoid_rewrite dom_kmap_L; auto.
      setoid_rewrite dom_fmap_L.
      intro. apply elem_of_map in H as [n [H_1 H_2]].
      unfold renamePIDPID_sym in H_1. clear -H8 H9 H0 H1 H2 H_1 H_2.
      repeat case_match; eqb_to_eq; subst; try congruence; try lia.
      + contradiction.
      + contradiction.
    - unfold renamePIDPID_sym; intro. repeat case_match; eqb_to_eq; subst; auto.
    - intro. apply isUsedEther_renamePID in H. congruence.
    - cbn. destruct v1; try now inv H13.
      case_match; inv H13; simpl; rewrite map_length, H.
      2: reflexivity.
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
      rewrite rename_eq; auto. exact H14.
      all: auto.
      intro. apply H2. apply isUsedPool_insert_2. right. by right.
Qed.
