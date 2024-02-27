From CoreErlang.FrameStack Require Export SubstSemanticsLemmas.
From CoreErlang.Concurrent Require Export NodeSemantics.

Import ListNotations.


Lemma isUsedPool_insert_1 :
  forall prs ι ι0 p,
    isUsedPool ι (ι0 ↦ p ∥ prs) ->
    isUsedPool ι (prs -- ι0) \/ ι = ι0 \/ ι ∈ (usedPIDsProc p).
Proof.
  intros. unfold isUsedPool in *. destruct (decide (ι = ι0)).
  * subst. setoid_rewrite lookup_insert in H; intros.
    all: set_solver.
  * setoid_rewrite lookup_insert_ne in H at 1; auto. intros; destruct_or!.
    (* all: try now firstorder. *)
    - left. left. intro. apply lookup_delete_None in H0. firstorder.
    - destruct H as [ι' [p0 [H_1 H_2]]].
      destruct (decide (ι0 = ι')).
      + subst. setoid_rewrite lookup_insert in H_1. inv H_1.
        set_solver.
      + setoid_rewrite lookup_insert_ne in H_1; auto.
        left. right. exists ι', p0. split; auto.
        apply lookup_delete_Some. split; auto.
Qed.

Lemma isUsedPool_insert_2 :
  forall prs ι ι0 p,
    (isUsedPool ι (prs -- ι0)) \/ ι = ι0 \/ ι ∈ (usedPIDsProc p) ->
    isUsedPool ι (ι0 ↦ p ∥ prs).
Proof.
  intros. unfold isUsedPool in *.
  destruct (decide (ι = ι0)).
  * subst. setoid_rewrite lookup_insert. by left.
  * setoid_rewrite lookup_insert_ne at 1; auto. destruct_or!.
    - left. intro. apply H. apply lookup_delete_None. by right.
    - destruct_hyps. right. exists x, x0.
      apply lookup_delete_Some in H as [H_1 H_2].
      setoid_rewrite lookup_insert_ne; set_solver.
    - right. exists ι0, p. split; auto.
      by setoid_rewrite lookup_insert. set_solver.
    - right. exists ι0, p. setoid_rewrite lookup_insert. by split.
Qed.

Lemma not_isUsedPool_insert_1 :
  forall Π ι' ι p,
  ¬ isUsedPool ι' (ι ↦ p ∥ Π) ->
  ι' ∉ dom Π /\ ι' <> ι.
Proof.
  intros. unfold isUsedPool in H.
  split; intro; apply H.
  * left. apply elem_of_dom in H0. unfold is_Some in H0. destruct_hyps.
    destruct (decide (ι = ι')); subst.
    - by setoid_rewrite lookup_insert.
    - setoid_rewrite lookup_insert_ne; auto. by setoid_rewrite H0.
  * left. subst. by setoid_rewrite lookup_insert.
Qed.

(** Refexive, transitive closure, with action logs: *)
Reserved Notation "n -[ l ]ₙ->* n' 'with' O" (at level 50).
Inductive closureNodeSem (O : gset PID) : Node -> list (Action * PID) -> Node -> Prop :=
| n_refl n (* n'  *): (* Permutation n n' -> *) n -[ [] ]ₙ->* n with O(* ' *)
| n_trans n n' n'' l a ι:
  n -[a|ι]ₙ-> n' with O -> n' -[l]ₙ->* n'' with O
->
  n -[(a,ι)::l]ₙ->* n'' with O
where "n -[ l ]ₙ->* n' 'with' O" := (closureNodeSem O n l n').

(* Properties *)

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

Theorem reduce_O_step :
  forall O O' n n' a ι,
    O' ⊆ O ->
    n -[a | ι]ₙ-> n' with O ->
    n -[a | ι]ₙ-> n' with O'.
Proof.
  intros. inv H0; econstructor; try eassumption.
  set_solver.
Qed.

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

Definition internals O (n n' : Node) : Prop :=
  exists l, Forall (fun e => e.1 = τ) l /\ n -[l]ₙ->* n' with O.

Notation "n -->* n' 'with' O" := (internals O n n') (at level 50).

Theorem internals_refl :
  forall O n, n -->* n with O.
Proof.
  intros. exists []. split; auto. constructor.
Qed.

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

Theorem bool_from_lit_val :
  forall y e, Some y = bool_from_lit e -> VALCLOSED e.
Proof.
  destruct e; intros; inversion H.
  now constructor.
Qed.

Definition onlyOne O (a : Action) (ι : PID) (n n''' : Node) :=
  exists n' n'', n -->* n' with O /\ n' -[a|ι]ₙ-> n'' with O /\ n'' -->* n''' with O.

Notation "n -[* a | ι *]-> n' 'with' O" := (onlyOne O a ι n n') (at level 60).

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
  * now inv H1.
  * now inv H0.
  * now inv H0.
  * inv H0.
    - inv H7. by cbn in H6.
    - rewrite H in H6. now inv H6.
  * inv H0. congruence.
  * inv H0.
    - inv H7. by cbn in H6.
    - rewrite H in H6. now inv H6.
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
  forall O Π a ι Π', Π -[a | ι]ₙ-> Π' with O -> forall Π'', Π -[a | ι]ₙ-> Π'' with O -> Π' = Π''.
Proof.
  intros O Π a ι Π' IH. inversion IH; intros; subst.
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
    - apply insert_eq in H6 as P. subst.
      eapply process_local_determinism in H4. 2: exact H19. subst.
      f_equal. rewrite H in H12. inv H12.
      rewrite H3 in H18. inv H18.
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
      + eexists. split. constructor. left. apply p_recv_peek_message_ok.
        destruct mb. destruct l0; simpl in *; by invSome.
      + eexists. split. constructor. left. apply p_remove_message.
        destruct mb. destruct l0; simpl in *; invSome.
        simpl. by rewrite app_assoc.
      + eexists. split. constructor. left. apply p_recv_wait_timeout_0.
      + eexists. split. constructor. left. by apply p_recv_wait_timeout_invalid.
    - inv H.
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
    - inv H.
      + eexists. split. apply p_exit_convert; auto. left. now constructor.
      + eexists. split. apply p_exit_convert; auto. left.
        apply p_recv_peek_message_ok.
        destruct mb, l0; simpl in *; by invSome.
      + eexists. split. apply p_exit_convert; auto. left.
        apply p_remove_message.
        destruct mb, l0; simpl in *; invSome. by rewrite app_assoc.
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
  forall O n n' n'' ι a, n -[τ | ι]ₙ-> n' with O -> n -[a | ι]ₙ-> n'' with O
->
  (a = τ /\ n''= n') \/ (exists t ι', a = AArrive ι' ι t /\
                                 exists n''', n' -[AArrive ι' ι t | ι]ₙ-> n''' with O /\
                                 (n'' -[τ | ι]ₙ-> n''' with O \/ n'' = n''')).
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
      exact H3. reflexivity. Unshelve. exact (inr ∅).
    - right. subst. setoid_rewrite insert_eq_Π. reflexivity. eassumption.
      reflexivity. Unshelve. exact (inr ∅).
  * apply insert_eq in H3 as H3'. subst.
    destruct H8 as [H8 | [ H8 | H8]].
    - subst. left. split; auto. eapply process_local_determinism in H4. 2: exact H1.
      subst. eapply insert_eq_Π in H3. now rewrite H3.
    - subst. exfalso. inv H4. inv H1. inv H8.
      now cbn in *.
    - subst. exfalso. inv H4; inv H1; try inv H9; try inv H8; try by cbn in *.
      congruence.
  * apply insert_eq in H3 as H3'. subst.
    exfalso. inv H12; inv H1; inv H13; now cbn in *.
Qed.

Definition bothSpawn (a1 a2 : Action) : Prop:=
match a1, a2 with
| ASpawn _ _ _ _, ASpawn _ _ _ _ => True
| _, _ => False
end.

Definition compatiblePIDOf (a1 a2 : Action) :=
match a1, a2 with
| ASend _ ι1 _, ASpawn ι2 _ _ _
| ASpawn ι1 _ _ _, ASend _ ι2 _
| ASpawn ι1 _ _ _, ASpawn ι2 _ _ _ => (ι1 <> ι2)%type
| _, _ => True
end.

Lemma isUsedPool_delete :
  forall Π ι ι',
    ι <> ι' ->
    isUsedPool ι (Π -- ι') ->
    isUsedPool ι Π.
Proof.
  intros. unfold isUsedPool in *. destruct_or!; destruct_hyps.
  * left. setoid_rewrite lookup_delete_ne in H0; auto.
  * right. assert (x <> ι'). {
      intro. subst. by setoid_rewrite lookup_delete in H0.
    }
     setoid_rewrite lookup_delete_ne in H0; auto.
     do 2 eexists. by split.
Qed.

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
  forall O l1 l2 Π Π'', Π -[l1 ++ l2]ₙ->* Π'' with O ->
   exists Π', Π -[l1]ₙ->* Π' with O /\
                    Π' -[l2]ₙ->* Π'' with O.
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
    unfold etherAdd. destruct (ether !! (ι, ι')); do 2 setoid_rewrite lookup_insert. 
    * exists l0, [s2]. now rewrite <- app_assoc.
    * now exists [], [s2].
  }
  epose proof (no_ether_pop _ l _ _ H4 _ _ _ _ _ H1 H).
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
    apply in_list_order in H4; auto; rewrite <- elem_of_list_In; set_solver.
  * destruct H0_1. subst.
    destruct x. simpl in H4. inv H4. congruence.
    put (length : list Signal -> nat) on H4 as Hlen.
    simpl in Hlen. repeat rewrite app_length in Hlen. simpl in Hlen. lia.
Qed.

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
  * assert (ι' <> ι) by (clear- H0_1; set_solver). clear H4.
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
  forall O l n n', n -[l]ₙ->* n' with O ->
    forall ι, n'.2 !! ι = None ->
    ι ∉ (PIDsOf spawnPIDOf l).
Proof.
  induction l using list_length_ind.
  intros. destruct (length l) eqn:Hlen.
  * apply length_zero_iff_nil in Hlen. subst. set_solver.
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
      + intro. assert (ι = ι') by set_solver. subst.
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
  forall O l n n', n -[l]ₙ->* n' with O ->
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
  forall O n n' l, n -[l]ₙ->* n' with O ->
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
  forall O n n' l, n -[l]ₙ->* n' with O ->
    forall ι p, n.2 !! ι = Some p -> exists p', n'.2 !! ι = Some p'.
Proof.
  intros.
  epose proof (processes_dont_die _ _ _ _ H ι _).
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
  forall O n n' l, n -[l]ₙ->* n' with O ->
    ether_wf n.1 -> ether_wf n'.1.
Proof.
  intros O n n' l H. induction H; intros; auto.
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
    - assert ((ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι']} else ∅, false) ∥ ι ↦ p' ∥ Π) !! ι0 <> None). {
      repeat processpool_destruct; auto.
    }
    apply IHclosureNodeSem in H; auto.
Qed.


Proposition isTargetedEther_dec :
  forall ι ether, isTargetedEther ι ether \/ ~isTargetedEther ι ether.
Proof.
  intros.
  unfold isTargetedEther.
  remember (base.filter (fun '((ιs, ιd), l) => ι = ιd) ether) as newmap.
  destruct (map_eq_dec_empty newmap).
  * right. intro. destruct H as [x [l H]].
    subst newmap.
    destruct (ether !! (x, ι)) eqn:P. 2: congruence. inv H.
    eapply map_filter_empty_not_lookup with (i := (x, ι)) (x := l) in e.
    contradiction. auto.
  * left.
    apply map_choose in n as n'. destruct n' as [x [l H]].
    destruct x.
    subst newmap. exists p.
    apply map_lookup_filter_Some_1_2 in H as H'. destruct H'.
    apply map_lookup_filter_Some_1_1 in H. subst.
    setoid_rewrite H. now do 2 eexists.
Qed.

Proposition appearsEther_dec :
  forall ι ether, appearsEther ι ether \/ ~appearsEther ι ether.
Proof.
  intros.
  unfold appearsEther.
  remember (base.filter (fun '((ιs, ιd), l) => ι = ιd \/ ι = ιs \/ ι ∈ flat_union  usedPIDsSignal l) ether) as newmap.
  destruct (map_eq_dec_empty newmap).
  * right. intro. destruct H. 2: destruct H.
    {
      destruct H as [x [l H]].
      subst newmap.
      destruct (ether !! (x, ι)) eqn:P. 2: congruence. inv H.
      eapply map_filter_empty_not_lookup with (i := (x, ι)) (x := l) in e.
      contradiction. auto.
    }
    {
      subst newmap. destruct_hyps.
      destruct (ether !! (ι, x)) eqn:P. 2: congruence.
      eapply map_filter_empty_not_lookup with (i := (ι, x)) (x := l) in e.
      contradiction. auto.
    }
    {
      subst newmap. destruct_hyps.
      destruct (ether !! (x, x0)) eqn:P. 2: congruence. inv H.
      eapply map_filter_empty_not_lookup with (i := (x, x0)) (x := x1) in e.
      contradiction. auto.
    }
  * left.
    apply map_choose in n as n'. destruct n' as [x [l H]].
    destruct x.
    subst newmap.
    apply map_lookup_filter_Some_1_1 in H as Hin.
    apply map_lookup_filter_Some_1_2 in H.
    destruct H. 2: destruct H.
    {
      subst. left. do 2 eexists. exact Hin.
    }
    {
      subst. right. left. exists p0. intro. by setoid_rewrite Hin in H.
    }
    {
      right. right.
      do 3 eexists. split. exact Hin. assumption.
    }
Qed.


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
      subst n. cbn. now setoid_rewrite lookup_insert.
    }
    eapply no_spawn_on_Some in H0. 2: eassumption. congruence.
  * destruct a; simpl in *; try now apply IHclosureNodeSem in Ha.
    destruct H3 as [? | [? | ?]]; congruence.
  * clear H7. apply elem_of_cons in Ha as [|].
    subst. destruct_hyps. apply H5. left. by exists x, x0.
    apply IHclosureNodeSem in H; auto.
Qed.

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

(* ------------------------- *)


Definition isUntaken (ι : PID) (n : Node) : Prop :=
  n.2 !! ι = None /\ isTargetedEther ι n.1.

Theorem compatibility_of_reduction :
  forall O n n' a ι, n -[a | ι]ₙ-> n' with O ->
    forall ι, isUntaken ι n ->
      (isUntaken ι n' (* \/ spawnPIDOf a = Some ι /\ exists p, n'.2 ι = Some p *)).
Proof.
  intros. inv H.
  * (* left. *) destruct H0. split.
    - simpl in *. repeat processpool_destruct; congruence.
    - simpl in *. now apply isTargetedEther_etherAdd.
  * (* left. *) destruct H0. split.
    - simpl in *. repeat processpool_destruct; congruence.
    - simpl in *. eapply isTargetedEther_etherPop in H1 as [H1 | H1].
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
      epose proof (isTargetedEther_no_spawn _ (ether, ι ↦ p ∥ Π) (ether, ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι']} else ∅, false) ∥ ι ↦ p' ∥ Π) [(ASpawn ι' v1 v2 link_flag, ι)] _ _ H0).
      simpl in H7. set_solver.
      Unshelve. 2: econstructor. 2: eapply n_spawn; try eassumption.
                constructor.
      (*  right. split; auto.
      eexists. unfold update. rewrite Nat.eqb_refl. reflexivity. *)
    -(*  left. *) split.
      + simpl. repeat processpool_destruct; congruence.
      + simpl. assumption.
Qed.


Corollary compatibility_of_reductions :
   forall O n n' l, n -[l]ₙ->* n' with O ->
    forall ι, isUntaken ι n ->
      (isUntaken ι n' (* \/ In ι (PIDsOf spawnPIDOf l) /\ exists p, n'.2 ι = Some p *)).
Proof.
  intros O n n' l H. induction H; intros; auto.
  apply (compatibility_of_reduction _ _ _ _ _ H) in H1(*  as [H1 | [H1_1 H1_2]] *).
  * now apply IHclosureNodeSem in H1. (*  destruct H1 as [? | [? ?]]; auto.
    right. simpl. break_match_goal; simpl; auto.
  * right. simpl. rewrite H1_1. split. now constructor.
    destruct H1_2. eapply processes_dont_die_Some in H1. eassumption.
    eauto. *)
Qed.



Theorem compatibility_of_reduction_rev :
  forall O n n' a ι, n -[a | ι]ₙ-> n' with O ->
    forall ι,
      isUntaken ι n' ->
      isUntaken ι n \/
      (sendPIDOf a = Some ι /\ ~isTargetedEther ι n.1 /\ n.2 !! ι = None).
(*       (spawnPIDOf a = Some ι /\ n.2 ι = None). *)
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
    - subst. left. split.
      + repeat processpool_destruct; congruence.
      + now simpl.
    - left. split.
      + simpl. repeat processpool_destruct; congruence.
      + simpl. assumption.
Qed.

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

Lemma no_spawn_unTaken :
  forall O n n' l, n -[l]ₙ->* n' with O ->
    forall ι, isUntaken ι n ->
      ι ∉ (PIDsOf spawnPIDOf l).
Proof.
  intros O n n' l H. induction H; intros; simpl.
  * set_solver.
  * intro Hin. inv H; simpl in *.
    - apply IHclosureNodeSem in Hin. assumption.
      destruct H1. split; simpl in *.
      + repeat processpool_destruct; congruence.
      + now apply isTargetedEther_etherAdd.
    - apply IHclosureNodeSem in Hin. assumption.
      destruct H1. split; simpl in *.
      + repeat processpool_destruct; congruence.
      + eapply isTargetedEther_etherPop in H2 as [H2 | H2]; try eassumption.
        subst. repeat processpool_destruct; congruence.
    - assert (isUntaken ι0 (ether, ι ↦ p' ∥ Π)). {
        destruct H1; split; auto.
        simpl in *. repeat processpool_destruct; congruence.
      }
      apply IHclosureNodeSem in H. apply H.
      destruct a; auto. destruct H3 as [? | [? | ?]]; congruence.
    - apply elem_of_cons in Hin as [|].
      + clear H7. subst. destruct H1. simpl in *.
        apply H5. by left.
      + clear H6. assert (isUntaken ι0 (ether, ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι']} else ∅, false) ∥ ι ↦ p' ∥ Π)). {
          destruct H1; split; auto.
          simpl in *. repeat processpool_destruct; try congruence.
          exfalso. apply H5. by left.
        }
        apply IHclosureNodeSem in H6. now apply H6.
Qed.


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
      cbn. repeat processpool_destruct; congruence.
Qed.

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
        apply H7. left. by setoid_rewrite lookup_insert.
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
        setoid_rewrite lookup_insert. reflexivity.
        assumption.
      }
      setoid_rewrite lookup_insert_ne in H. 2: lia.
      setoid_rewrite lookup_union in H. setoid_rewrite union_Some in H.
      destruct H.
      * apply H7. right. exists x, x0.
        setoid_rewrite lookup_insert_ne. 2: lia. split; assumption.
      * apply H0. right. exists x, x0. destruct_hyps. split; assumption.
    }
Qed.

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
    (* set_solver. *)
Admitted.

Corollary reductions_are_preserved_by_comp_l : 
  forall O Π Π' ether ether' l,
    (ether, Π) -[l]ₙ->* (ether', Π') with O ->
    forall (Π2 : ProcessPool),
      (forall ι, ι ∈ (PIDsOf spawnPIDOf l) -> ¬isUsedPool ι Π2) ->
      (ether, Π ∪ Π2) -[l]ₙ->* (ether', Π' ∪ Π2) with O.
Proof.
  intros ???????. dependent induction H; intros.
  * constructor.
  * destruct n'. specialize (IHclosureNodeSem _ _ _ _ JMeq_refl JMeq_refl).
    eapply reduction_is_preserved_by_comp_l with (Π2 := Π2) in H.
    2: { intros. apply H1. cbn. apply elem_of_app. left. rewrite H2. now left. }
    econstructor; eauto.
    apply IHclosureNodeSem.
    intros. apply H1. cbn. apply elem_of_app. now right.
Qed.

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
        apply H8. left. by setoid_rewrite lookup_insert.
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
        setoid_rewrite lookup_insert. reflexivity.
        assumption.
      }
      setoid_rewrite lookup_insert_ne in H. 2: lia.
      setoid_rewrite lookup_union in H. setoid_rewrite union_Some in H.
      destruct H.
      * apply H1. right. exists x, x0. split; assumption.
      * apply H8. right. exists x, x0. destruct_hyps.
        setoid_rewrite lookup_insert_ne. 2: lia. split; assumption.
    }
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
Admitted.

Corollary reductions_are_preserved_by_comp_r : 
  forall O Π Π' ether ether' l,
    (ether, Π) -[l]ₙ->* (ether', Π') with O ->
    forall (Π2 : ProcessPool),
      (forall ι, ι ∈ (map snd l) -> ι ∉ dom Π2) ->
      (forall ι, ι ∈ (PIDsOf spawnPIDOf l) -> ¬isUsedPool ι Π2) ->
      (ether, Π2 ∪ Π) -[l]ₙ->* (ether', Π2 ∪ Π') with O.
Proof.
  intros ???????. dependent induction H; intros.
  * constructor.
  * destruct n'. specialize (IHclosureNodeSem _ _ _ _ JMeq_refl JMeq_refl).
    eapply reduction_is_preserved_by_comp_r with (Π2 := Π2) in H.
    2: { apply H1. now left. }
    2: { intros. apply H2. cbn. apply elem_of_app. left. rewrite H3. now left. }
    econstructor; eauto.
    apply IHclosureNodeSem.
    intros. apply H1. cbn. now right.
    intros. apply H2. cbn. apply elem_of_app. now right.
Qed.

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

(* Definition renamePIDPool (p p' : PID) (Π : ProcessPool) : ProcessPool :=
match Π !! p with
| None => Π
| Some proc =>
  <[p' := renamePIDProc p p' proc]>((renamePIDProc p p' <$> Π) -- p)
end.

Notation "e .[ x ↦ y ]ₚₚ" := (renamePIDPool x y e) (at level 2).
 *)

(* ONLY keys are symmetrically replaced  *)
Definition renamePIDPool (p p' : PID) (Π : ProcessPool) : ProcessPool :=
  kmap (renamePIDPID_sym p p') (renamePIDProc p p' <$> Π).

Notation "e .[ x ⇔ y ]ₚₚ" := (renamePIDPool x y e) (at level 2, left associativity).

(* ONLY keys are symmetrically replaced  *)
Definition renamePIDEther (p p' : PID) (eth : Ether) : Ether :=
  kmap (prod_map (renamePIDPID_sym p p') (renamePIDPID_sym p p'))
    ((map (renamePIDSignal p p')) <$> eth).

Notation "e .[ x ⇔ y ]ₑ" := (renamePIDEther x y e) (at level 2, left associativity).

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

Lemma mk_list_renamePID :
  forall v from to,
    mk_list (renamePIDVal from to v) = fmap (map (renamePIDVal from to)) (mk_list v).
Proof.
  intros. induction v; simpl; try reflexivity.
  * case_match; reflexivity.
  * rewrite IHv2. by destruct (mk_list v2).
Qed.

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
      - rewrite usedPIDsProc_rename. destruct decide; set_solver.
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
      - rewrite usedPIDsProc_rename in H2. destruct decide; set_solver.
  }
Qed.

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
      by setoid_rewrite H.
    * apply not_appearsEther_alt in H0; destruct_hyps.
      by setoid_rewrite H0.
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
    rewrite usedPIDsProc_rename in H0. destruct decide; set_solver.
Qed.

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
    - rewrite usedPIDsProc_rename. destruct decide; set_solver.
Qed.

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

Lemma isUsedPool_remove_1 :
  forall Π ι ι',
    isUsedPool ι (Π -- ι') ->
    isUsedPool ι Π.
Proof.
  intros. destruct H.
  * left. destruct (decide (ι = ι')).
    {
      intro. apply H. subst. apply lookup_delete.
    }
    intro. apply H.
    apply lookup_delete_None. by right.
  * destruct_hyps.
    destruct (decide (x = ι')).
    {
      subst. by setoid_rewrite lookup_delete in H.
    }
    right.
    exists x, x0. split. 2: assumption.
    apply lookup_delete_Some in H. apply H.
Qed.

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

Theorem renamePID_is_preserved_node_semantics :
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
    rewrite <- rename_eq; auto. rewrite <- rename_eq; auto. apply n_send.
    rewrite rename_eq, rename_eq; auto.
    eapply renamePID_is_preserved_local in H7. exact H7.
    all: try assumption.
    intro. apply H2. apply isUsedPool_insert_2. right. by right.
    all: set_solver.
  * simpl in *. rewrite <- rename_eq, <- rename_eq; auto.
    do 2 rewrite pool_insert_renamePID.
    constructor.
    2: {
      eapply renamePID_is_preserved_local in H10.
      rewrite rename_eq, rename_eq; auto. exact H10.
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
    right. left. rewrite rename_eq; auto.
    intro. apply H2. apply isUsedPool_insert_2. right. by left.
  * simpl in *. do 3 rewrite pool_insert_renamePID.
    rewrite <- rename_eq; auto. simpl.
    replace (set_map (renamePIDPID from to) (if link_flag then {[ι']} else ∅)) with
      (if link_flag then {[renamePIDPID_sym from to ι']} else ∅ : gset PID). 2: {
      break_match_goal.
      * rewrite rename_eq. 2: set_solver. by rewrite set_map_singleton_L.
      * by rewrite set_map_empty.
    }
    econstructor.
    - rewrite mk_list_renamePID, H7. reflexivity.
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
      set_solver.
      intro. apply H2. apply isUsedPool_insert_2. right. by right.
    - set_solver.
Qed.

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

(* Ltac In_app_solver :=
  (apply in_or_app; (by left + by right + (left;In_app_solver)+(right;In_app_solver))). *)

Lemma rename_usedPIDs :
  (forall e ρ, usedPIDsExp e = usedPIDsExp (rename ρ e)) /\
  (forall e ρ, usedPIDsNVal e = usedPIDsNVal (renameNonVal ρ e)) /\
  (forall e ρ, usedPIDsVal e = usedPIDsVal (renameVal ρ e)).
Proof.
  apply Exp_ind with
    (QV := fun l => Forall (fun e => forall ρ, usedPIDsVal e = usedPIDsVal (renameVal ρ e)) l)
    (Q := fun l => Forall (fun e => forall ρ, usedPIDsExp e = usedPIDsExp (rename ρ e)) l)
    (RV := fun l => Forall (fun '(e1, e2) => forall ρ,
        (usedPIDsVal e1 = usedPIDsVal (renameVal ρ e1)) /\
        (usedPIDsVal e2 = usedPIDsVal (renameVal ρ e2))) l)
    (R := fun l => Forall (fun '(e1, e2) => forall ρ,
        (usedPIDsExp e1 = usedPIDsExp (rename ρ e1)) /\
        (usedPIDsExp e2 = usedPIDsExp (rename ρ e2))) l)
    (W := fun l => Forall (fun '(p, g, e) => forall ρ,
       (usedPIDsExp g = usedPIDsExp (rename ρ g)) /\
       (usedPIDsExp e = usedPIDsExp (rename ρ e))) l)
    (Z := fun l => Forall (fun '(n, e) => forall ρ, usedPIDsExp e = usedPIDsExp (rename ρ e)) l)
   (VV := fun l => Forall
      (fun '(id, vl, e) => forall ρ,  usedPIDsExp e = usedPIDsExp (rename ρ e)) l).
  all: try now (constructor; auto).
  all: intros; simpl; try rewrite <- H; try rewrite <- H0; try rewrite H1; try reflexivity.
  * do 2 rewrite flat_union_map. rewrite map_map. f_equal.
    apply map_ext_in. intros. apply elem_of_list_In in H0.
    rewrite Forall_forall in H. eapply H in H0. exact H0.
  * do 2 rewrite flat_union_map. rewrite map_map. f_equal.
    apply map_ext_in. intros. apply elem_of_list_In in H0.
    rewrite Forall_forall in H. eapply H in H0.
    destruct a. set_solver.
  * by destruct n.
  * do 2 rewrite flat_union_map. rewrite map_map. do 2 f_equal.
    apply map_ext_in. intros. apply elem_of_list_In in H1.
    rewrite Forall_forall in H. eapply H in H1.
    destruct a, p. set_solver.
  * do 2 rewrite flat_union_map. rewrite map_map. f_equal.
    apply map_ext_in. intros. apply elem_of_list_In in H0.
    rewrite Forall_forall in H. eapply H in H0. exact H0.
  * do 2 rewrite flat_union_map. rewrite map_map. f_equal.
    apply map_ext_in. intros. apply elem_of_list_In in H0.
    rewrite Forall_forall in H. eapply H in H0. exact H0.
  * do 2 rewrite flat_union_map. rewrite map_map. f_equal.
    apply map_ext_in. intros. apply elem_of_list_In in H0.
    rewrite Forall_forall in H. eapply H in H0.
    destruct a. set_solver.
  * f_equal.
    do 2 rewrite flat_union_map. rewrite map_map. f_equal.
    apply map_ext_in. intros. apply elem_of_list_In in H2.
    rewrite Forall_forall in H1. eapply H1 in H2.
    set_solver.
  * do 2 rewrite flat_union_map. rewrite map_map. f_equal.
    apply map_ext_in. intros. apply elem_of_list_In in H0.
    rewrite Forall_forall in H. eapply H in H0. exact H0.
  * f_equal.
    do 2 rewrite flat_union_map. rewrite map_map. f_equal.
    apply map_ext_in. intros. apply elem_of_list_In in H1.
    rewrite Forall_forall in H0. eapply H0 in H1. exact H1.
  * f_equal.
    do 2 rewrite flat_union_map. rewrite map_map. f_equal.
    apply map_ext_in. intros. apply elem_of_list_In in H1.
    rewrite Forall_forall in H0. eapply H0 in H1.
    destruct a, p. set_solver.
  * f_equal.
    do 2 rewrite flat_union_map. rewrite map_map. f_equal.
    apply map_ext_in. intros. apply elem_of_list_In in H1.
    rewrite Forall_forall in H0. eapply H0 in H1. destruct a. set_solver.
  * by rewrite <- H1.
Qed.

Lemma subst_usedPIDs :
  (forall e ι ξ, ι ∈ (usedPIDsExp e.[ξ]) -> ι ∈ (usedPIDsExp e) \/ exists n v, ξ n = inl v /\ ι ∈ (usedPIDsVal v))
  /\
  (forall e ι ξ, ι ∈ (usedPIDsNVal e.[ξ]ₑ ) -> ι ∈ (usedPIDsNVal e) \/ exists n v, ξ n = inl v /\ ι ∈ (usedPIDsVal v))
  /\
  (forall e ι ξ, ι ∈ (usedPIDsVal e.[ξ]ᵥ ) -> ι ∈ (usedPIDsVal e) \/ exists n v, ξ n = inl v /\ ι ∈ (usedPIDsVal v)).
Proof.
  apply Exp_ind with
    (QV := fun l => Forall (fun e => forall ι ξ, ι ∈ (usedPIDsVal e.[ξ]ᵥ ) -> ι ∈ (usedPIDsVal e) \/ exists n v, ξ n = inl v /\ ι ∈ (usedPIDsVal v)) l)
    (Q := fun l => Forall (fun e => forall ι ξ, ι ∈ (usedPIDsExp e.[ξ]) -> ι ∈ (usedPIDsExp e) \/ exists n v, ξ n = inl v /\ ι ∈ (usedPIDsVal v)) l)
    (RV := fun l => Forall (fun '(e1, e2) => forall ι ξ,
        (ι ∈ (usedPIDsVal e1.[ξ]ᵥ ) -> ι ∈ (usedPIDsVal e1) \/ exists n v, ξ n = inl v /\ ι ∈ (usedPIDsVal v)) /\
        (ι ∈ (usedPIDsVal e2.[ξ]ᵥ ) -> ι ∈ (usedPIDsVal e2) \/ exists n v, ξ n = inl v /\ ι ∈ (usedPIDsVal v))) l)
    (R := fun l => Forall (fun '(e1, e2) => forall ι ξ,
        (ι ∈ (usedPIDsExp e1.[ξ]) -> ι ∈ (usedPIDsExp e1) \/ exists n v, ξ n = inl v /\ ι ∈ (usedPIDsVal v)) /\
        (ι ∈ (usedPIDsExp e2.[ξ]) -> ι ∈ (usedPIDsExp e2) \/ exists n v, ξ n = inl v /\ ι ∈ (usedPIDsVal v))) l)
    (W := fun l => Forall (fun '(p, g, e) => forall ι ξ,
       (ι ∈ (usedPIDsExp g.[ξ]) -> ι ∈ (usedPIDsExp g) \/ exists n v, ξ n = inl v /\ ι ∈ (usedPIDsVal v)) /\
       (ι ∈ (usedPIDsExp e.[ξ]) -> ι ∈ (usedPIDsExp e) \/ exists n v, ξ n = inl v /\ ι ∈ (usedPIDsVal v))) l)
    (Z := fun l => Forall (fun '(n, e) => forall ι ξ, ι ∈ (usedPIDsExp e.[ξ]) -> ι ∈ (usedPIDsExp e) \/ exists n v, ξ n = inl v /\ ι ∈ (usedPIDsVal v)) l)
   (VV := fun l => Forall
      (fun '(id, vl, e) => forall ι ξ,  ι ∈ (usedPIDsExp e.[ξ]) -> ι ∈ (usedPIDsExp e) \/ exists n v, ξ n = inl v /\ ι ∈ (usedPIDsVal v)) l).
  all: intros; simpl in *.
  all: try now (constructor; auto).
  * by apply H in H0.
  * by apply H in H0.
  * apply elem_of_union in H1 as [|]; [apply H in H1 | apply H0 in H1].
    - destruct_or!. left. set_solver. set_solver.
    - destruct_or!. left. set_solver. set_solver.
  * apply elem_of_flat_union in H0 as [x [P1 P2]].
    apply elem_of_map_iff in P1 as [y [P1 P3]].
    subst. rewrite Forall_forall in H. eapply H in P3 as P3'. 2: eassumption.
    clear -P2 P3 P3'. destruct_or!; auto.
    left. apply elem_of_flat_union. exists y. auto.
  * apply elem_of_flat_union in H0 as [x [P1 P2]].
    apply elem_of_map_iff in P1 as [y [P1 P3]].
    subst. rewrite Forall_forall in H. eapply H in P3 as P3'. destruct y.
    apply elem_of_union in P2 as [H0 | H0]; apply P3' in H0 as H0'; destruct_or!; auto.
    - left. simpl in *. apply elem_of_flat_union. exists (v, v0); split; auto.
      set_solver.
    - left. simpl in *. apply elem_of_flat_union. exists (v, v0); split; auto.
      set_solver.
  * right; case_match; try inv H. set_solver.
  * destruct n. right; case_match; try inv H. set_solver.
  * apply elem_of_union in H1 as [|].
    - apply H0 in H1. destruct H1. left. set_solver.
      right. destruct_hyps. eapply upn_inl_eq_1 in H1.
      do 2 eexists; split; try eassumption.
      by rewrite <- (proj2 (proj2 (rename_usedPIDs))).
    - rewrite Forall_forall in H. apply elem_of_flat_union in H1 as [x [P1 P2]].
      apply elem_of_map_iff in P1 as [y [P1 P3]]. eapply H in P3 as P3'. destruct y, p.
      inv P1. apply P3' in P2. destruct P2 as [|].
      + left. apply elem_of_union. right.
        apply elem_of_flat_union. exists (n, n0, e0); auto.
      + right. destruct H2 as [n' [v' [H2_1 H2_2]]].
        eapply upn_inl_eq_1 with (n:=length ext + n0) in H2_1.
        do 2 eexists; split; try eassumption.
        by rewrite <- (proj2 (proj2 (rename_usedPIDs))).
  * apply H in H0. destruct H0; auto.
    right. destruct H0 as [n' [v' [H0_1 H0_2]]].
    apply upn_inl_eq_1 in H0_1.
    do 2 eexists; split; try eassumption.
    by rewrite <- (proj2 (proj2 (rename_usedPIDs))).
  * apply elem_of_flat_union in H0 as [x [P1 P2]]. apply elem_of_map_iff in P1 as [y [P1 P3]].
    subst. rewrite Forall_forall in H. eapply H in P3 as P3'. 2: eassumption.
    clear -P2 P3 P3'. destruct_or!; auto.
    left. apply elem_of_flat_union. exists y. auto.
  * apply elem_of_union in H1 as [|]; [apply H in H1 | apply H0 in H1].
    - destruct_or!. left. apply elem_of_union. by left.
      by right.
    - destruct_or!. left. apply elem_of_union. by right.
      by right.
  * apply elem_of_flat_union in H0 as [x [P1 P2]]. apply elem_of_map_iff in P1 as [y [P1 P3]].
    subst. rewrite Forall_forall in H. eapply H in P3 as P3'. 2: eassumption.
    clear -P2 P3 P3'. destruct_or!; auto.
    left. apply elem_of_flat_union. exists y. auto.
  * apply elem_of_flat_union in H0 as [x [P1 P2]]. apply elem_of_map_iff in P1 as [y [P1 P3]].
    subst. rewrite Forall_forall in H. eapply H in P3 as P3'. destruct y.
    apply elem_of_union in P2 as [H0 | H0]; apply P3' in H0 as H0'; destruct_or!; auto.
    - left. simpl in *. apply elem_of_flat_union. exists (e, e0); split; auto.
      set_solver.
    - left. simpl in *. apply elem_of_flat_union. exists (e, e0); split; auto.
      set_solver.
  * apply elem_of_union in H2 as [|]. apply elem_of_union in H2 as [|].
    1: { apply H in H2 as [|]; auto. left. set_solver. }
    1: { apply H0 in H2 as [|]; auto. left. set_solver. }
    apply elem_of_flat_union in H2 as [x [P1 P2]]. apply elem_of_map_iff in P1 as [y [P1 P3]].
    subst. rewrite Forall_forall in H1. eapply H1 in P3 as P3'. 2: eassumption.
    clear -P2 P3 P3'. destruct_or!; auto.
    left. apply elem_of_union. right. apply elem_of_flat_union. exists y. auto.
  * apply elem_of_flat_union in H0 as [x [P1 P2]]. apply elem_of_map_iff in P1 as [y [P1 P3]].
    subst. rewrite Forall_forall in H. eapply H in P3 as P3'. 2: eassumption.
    clear -P2 P3 P3'. destruct_or!; auto.
    left. apply elem_of_flat_union. exists y. auto.
  * apply elem_of_union in H1 as [|].
    1: { apply H in H1 as [|]; auto. left. set_solver. }
    apply elem_of_flat_union in H1 as [x [P1 P2]]. apply elem_of_map_iff in P1 as [y [P1 P3]].
    subst. rewrite Forall_forall in H0. eapply H0 in P3 as P3'. 2: eassumption.
    clear -P2 P3 P3'. destruct_or!; auto.
    left. apply elem_of_union. right. apply elem_of_flat_union. exists y. auto.
  * apply elem_of_union in H1 as [|].
    1: { apply H in H1 as [|]; auto. left. set_solver. }
    apply elem_of_flat_union in H1 as [x [P1 P2]]. apply elem_of_map_iff in P1 as [y [P1 P3]].
    subst. destruct y, p. simpl in *.
    rewrite Forall_forall in H0. eapply H0 in P3 as P3'.
    apply elem_of_union in P2 as [P2|P2]; apply P3' in P2;
    clear -P2 P3 P3'; destruct_or!; auto.
    - left. apply elem_of_union. right. apply elem_of_flat_union. eexists. split. eassumption.
      set_solver.
    - right. destruct P2 as [n' [v' [H0_1 H0_2]]].
      apply upn_inl_eq_1 in H0_1.
      do 2 eexists; split; try eassumption.
      by rewrite <- (proj2 (proj2 (rename_usedPIDs))).
    - left. apply elem_of_union. right. apply elem_of_flat_union. eexists. split. eassumption.
      set_solver.
    - right. destruct P2 as [n' [v' [H0_1 H0_2]]].
      apply upn_inl_eq_1 in H0_1.
      do 2 eexists; split; try eassumption.
      by rewrite <- (proj2 (proj2 (rename_usedPIDs))).
  * apply elem_of_union in H1 as [|]; [apply H in H1 | apply H0 in H1].
    - destruct_or!. left. set_solver. set_solver.
    - destruct_or!. left. set_solver.
      right. destruct H1 as [n' [v' [H0_1 H0_2]]].
      apply upn_inl_eq_1 in H0_1.
      do 2 eexists; split; try eassumption.
      by rewrite <- (proj2 (proj2 (rename_usedPIDs))).
  * apply elem_of_union in H1 as [|]; [apply H in H1 | apply H0 in H1].
    - destruct_or!. left. set_solver. set_solver.
    - destruct_or!. left. set_solver. set_solver.
  * apply elem_of_union in H1 as [|].
    - apply H in H1. destruct_or!.
      left. set_solver.
      right. destruct H1 as [n' [v' [H0_1 H0_2]]].
      apply upn_inl_eq_1 in H0_1.
      do 2 eexists; split; try eassumption.
      by rewrite <- (proj2 (proj2 (rename_usedPIDs))).
    - rewrite Forall_forall in H0. apply elem_of_flat_union in H1 as [x [P1 P2]].
      apply elem_of_map_iff in P1 as [y [P1 P3]]. destruct y.
      inv P1. clear H1. apply H0 in P3 as P3'. apply P3' in P2. destruct_or!.
      left. apply elem_of_union. right. apply elem_of_flat_union. exists (n, e0). split; assumption.
      right.  destruct P2 as [n' [v' [H0_1 H0_2]]].
      apply upn_inl_eq_1 in H0_1.
      do 2 eexists; split; try eassumption.
      by rewrite <- (proj2 (proj2 (rename_usedPIDs))).
  * apply elem_of_union in H2 as [H2|H2]; [apply elem_of_union in H2 as [H2|H2]; [apply H in H2 | apply H0 in H2] | apply H1 in H2].
    - destruct_or!. left. set_solver. set_solver.
    - destruct_or!. set_solver.
      right. destruct H2 as [n' [v' [H0_1 H0_2]]].
      apply upn_inl_eq_1 in H0_1.
      do 2 eexists; split; try eassumption.
      by rewrite <- (proj2 (proj2 (rename_usedPIDs))).
    - destruct_or!. set_solver.
      right. destruct H2 as [n' [v' [H0_1 H0_2]]].
      apply upn_inl_eq_1 in H0_1.
      do 2 eexists; split; try eassumption.
      by rewrite <- (proj2 (proj2 (rename_usedPIDs))).
Qed.

Corollary list_subst_idsubst_inl :
  forall vs v x,
    list_subst vs idsubst x = inl v ->
    v ∈ vs.
Proof.
  intros. pose proof (list_subst_get_possibilities x vs idsubst).
  firstorder.
  * rewrite H in H0. inv H0. by apply nth_elem_of.
  * rewrite H in H0. inv H0.
Qed.

Lemma match_pattern_usedPIDs :
  forall p v vs' ι,
    match_pattern p v = Some vs' ->
    ι ∈ (flat_union usedPIDsVal vs') ->
    ι ∈ (usedPIDsVal v).
Proof.
  induction p using Pat_ind2 with
    (Q := fun l => Forall (fun p => forall v vs' ι, match_pattern p v = Some vs' ->
    ι ∈ (flat_union usedPIDsVal vs') ->
    ι ∈ (usedPIDsVal v)) l)
    (R := fun l => Forall (fun '(p1, p2) => (forall v vs' ι, match_pattern p1 v = Some vs' ->
    ι ∈ (flat_union usedPIDsVal vs') ->
    ι ∈ (usedPIDsVal v)) /\
    (forall v vs' ι, match_pattern p2 v = Some vs' ->
    ι ∈ (flat_union usedPIDsVal vs') ->
    ι ∈ (usedPIDsVal v))) l).
  all: intros; try now (constructor; auto).
  1-4: try destruct v; inv H.
  all: simpl in *; try by set_solver.
  * case_match. 2: congruence. inv H2. set_solver.
  * case_match; try congruence. case_match; try congruence.
    inv H2. rewrite flat_union_app in H0.
    apply elem_of_union in H0 as [|].
    - eapply IHp1 in H0. 2: exact H. set_solver.
    - eapply IHp2 in H0. 2: exact H1. set_solver.
  * destruct v; try now inv H. simpl in *. generalize dependent l0.
    generalize dependent vs'.
    induction l; intros; destruct l0; inv H. 1: inv H0.
    inv IHp. case_match; try congruence. case_match; try congruence. inv H2.
    apply elem_of_flat_union in H0. destruct_hyps. apply elem_of_app in H0 as [|].
    - apply elem_of_flat_union. eapply H3 in H; try eassumption.
      2: apply elem_of_flat_union; eexists; split; eassumption.
      eexists; split. 2: eassumption. by left.
    - apply IHl in H1; try assumption. clear IHl.
      simpl. set_solver.
      apply elem_of_flat_union. eexists. split; eassumption.
  * destruct v; try now inv H. simpl in *. generalize dependent l0.
    generalize dependent vs'.
    induction l; intros; destruct l0; inv H. 1: inv H0. 1: destruct a; inv H2.
    inv IHp. destruct p, a, H3. case_match; try congruence.
    case_match; try congruence. case_match; try congruence. inv H2.
    do 2 rewrite flat_union_app in H0. apply elem_of_union in H0 as [|].
    2: apply elem_of_union in H0 as [|].
    - apply elem_of_flat_union. eapply H in H3; try eassumption.
      exists (v, v0); split. 2: apply elem_of_union; left; exact H3. by left.
    - apply elem_of_flat_union. eapply H1 in H5; try eassumption.
      exists (v, v0); split. 2: apply elem_of_union; right; exact H5. by left.
    - apply IHl in H6; try assumption. clear IHl.
      simpl. set_solver.
Qed.

Lemma match_pattern_list_usedPIDs :
  forall lp vs vs' ι,
    match_pattern_list lp vs = Some vs' ->
    ι ∈ (flat_union usedPIDsVal vs') ->
    ι ∈ (flat_union usedPIDsVal vs).
Proof.
  induction lp; destruct vs; intros; inv H. inv H0.
  case_match. 2: congruence. case_match. 2: congruence. inv H2.
  rewrite flat_union_app in H0. apply elem_of_union in H0 as [|].
  - eapply match_pattern_usedPIDs in H. 2: eassumption.
    apply elem_of_union. by left.
  - eapply IHlp in H1; eauto. simpl.
    apply elem_of_union. by right.
Qed.

Lemma flatten_list_concat_map :
  forall {A B} (l : list (A * A)) (f : A -> list B),
    flat_map f (flatten_list l) =
    concat (flatten_list (map (prod_map f f) l)).
Proof.
  induction l; auto; intros; simpl.
  destruct a; simpl. do 2 f_equal.
  apply IHl.
Qed.

Lemma in_flatten_list :
  forall {A} (l : list (A * A)) x, In x (flatten_list l) ->
    exists y, In (x, y) l \/ In (y, x) l.
Proof.
  induction l; intros; simpl in H. destruct H.
  destruct a. inv H. 2: inv H0.
  * exists a0. left. by left.
  * exists a. right. by left.
  * apply IHl in H. firstorder.
Qed.

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
    admit. (* create_result helper needed *)
  * repeat (apply elem_of_union in H as [|]).
    all: try set_solver.
    admit. (* create_result helper needed *)
  * repeat (apply elem_of_union in H as [|]).
    all: try set_solver.
    rewrite elem_of_flat_union in H. destruct_hyps.
    apply elem_of_union. right. apply elem_of_union. right.
    apply elem_of_flat_union.
    apply elem_of_list_In in H. apply in_flatten_list in H.
    destruct_hyps. inv H; apply elem_of_list_In in H1.
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
      + apply elem_of_flat_union in H0; destruct_hyps.
        apply elem_of_map_iff in H0; destruct_hyps. destruct x0. inv H0.
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
      apply list_subst_idsubst_inl in P1. apply elem_of_list_In in P1. 
      inv P1. 2: inv H. 3: inv H0. 4: inv H.
      + destruct class; inv P2.
      + set_solver.
      + set_solver.
Admitted.

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
    - apply elem_of_list_singleton in H. subst. simpl in *.
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
    - destruct mb, l0; simpl in *. set_solver. rewrite flat_union_app in H.
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
    - set_solver.
Qed.

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
  * setoid_rewrite insert_commute in H1. 2: by apply not_isUsedPool_insert_1 in H8 as [_ ?].
    apply isUsedPool_insert_1 in H1.
    apply H. apply isUsedPool_insert_2; intuition.
    - left.
      unfold isUsedPool in *.
      setoid_rewrite lookup_delete_None in H2.
      setoid_rewrite lookup_delete_None. destruct_or!.
      + left. intro. destruct H1. set_solver. apply H2. right.
        setoid_rewrite lookup_insert_ne. assumption. set_solver.
      + right. destruct H2 as [ι'1 [pp [H_1 H_2]]].
        apply lookup_delete_Some in H_1 as [H_11 H_12].
        destruct (decide (ι'1 = ι'0)).
        ** subst. setoid_rewrite lookup_insert in H_12. inv H_12.
           cbn in H_2. exfalso.
           destruct v1; try now inv H12.
           destruct Nat.eqb eqn:P; inv H12.
           -- clear - H_2 H_11 H6 H0.
              apply not_elem_of_union in H0 as [P1 P2]. simpl in P1.
              apply not_elem_of_union in P1 as [P1 P3].
              apply not_elem_of_union in P3 as [P3 P4].
              simpl in H_2. rewrite union_empty_l_L in H_2.
              repeat rewrite union_empty_r_L in H_2.
              assert (ι'
      ∈ usedPIDsExp e.[list_subst (convert_to_closlist ext ++ l) idsubst]) as H_2'. {
                clear -P1 H_2. case_match; set_solver.
              }
              apply subst_usedPIDs in H_2'.
              destruct H_2'.
              ++ congruence.
              ++ destruct H as [n [v [P5 P6]]].
                 apply list_subst_idsubst_inl in P5.
                 apply elem_of_app in P5 as [|].
                 *** unfold convert_to_closlist in H.
                     apply elem_of_map_iff in H. destruct_hyps. destruct x, p.
                     inv H. clear H1. simpl in P6.
                     apply elem_of_union in P6 as [|]; try congruence.
                     apply P4. apply elem_of_flat_union. eexists; split; eassumption.
                 *** eapply mk_list_not_usedPIDs in H6. 2: eassumption.
                     apply H6. apply elem_of_flat_union. eexists; split; eassumption.
           -- case_match; set_solver.
        ** exists ι'1, pp. setoid_rewrite lookup_delete_Some.
           intuition. setoid_rewrite lookup_insert_ne in H_12; auto.
    - right. right. eapply not_isUsedProc_step; try eauto.
      simpl. set_solver.
Qed.

Corollary renamePID_is_preserved_node_semantics_steps :
  forall O eth eth' Π Π' l,
    (eth, Π) -[l]ₙ->* (eth', Π') with O ->
    forall from to,
      to ∉ (flat_union (fst >>> usedPIDsAct) l) ->
      ¬ appearsEther to eth ->
      ¬ isUsedPool to Π ->
      to ∉ O ->
      (renamePIDEther from to eth, renamePIDPool from to Π)
    -[map (prod_map (renamePIDAct from to) (renamePIDPID_sym from to)) l]ₙ->*
      (renamePIDEther from to eth', renamePIDPool from to Π') with O.
Proof.
  intros O eth eth' Π Π' l H. dependent induction H; intros.
  * constructor.
  * destruct n'. specialize (IHclosureNodeSem _ _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
    simpl in *. econstructor.
    - apply renamePID_is_preserved_node_semantics. exact H.
      all: try assumption.
      cbn in H1. by apply not_elem_of_union in H1 as [H1 _].
    - apply IHclosureNodeSem.
      + cbn in H1. by apply not_elem_of_union in H1 as [_ H1].
      + eapply not_isUsedEther_step; try eassumption.
        by apply not_elem_of_union in H1 as [? _].
      + eapply not_isUsedPool_step; try eassumption.
        by apply not_elem_of_union in H1 as [? _].
      + assumption.
Qed.

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
        intros. apply double_renamePID_signal. intro.
        apply H. right. right. do 3 eexists. split. exact P.
        apply elem_of_flat_union.
        apply elem_of_list_In in H1. exists a. split; assumption.
      + subst. exists (to, ιd). cbn. split. by renamePIDPID_sym_case_match.
        apply lookup_kmap_Some; auto.
        exists (from, ιd). cbn. split. by renamePIDPID_sym_case_match.
        do 2 setoid_rewrite lookup_fmap. setoid_rewrite P.
        cbn. f_equal.
        rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext_in.
        intros. apply double_renamePID_signal. intro.
        apply H. right. right. do 3 eexists. split. exact P.
        apply elem_of_flat_union.
        apply elem_of_list_In in H1. exists a. split; assumption.
    - subst. destruct (decide (ιd = from)).
      + subst. exists (from, to). cbn. split. by renamePIDPID_sym_case_match.
        apply lookup_kmap_Some; auto.
        exists (to, from). cbn. split. by renamePIDPID_sym_case_match.
        do 2 setoid_rewrite lookup_fmap. setoid_rewrite P.
        cbn. f_equal.
        rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext_in.
        intros. apply double_renamePID_signal. intro.
        apply H. right. right. do 3 eexists. split. exact P.
        apply elem_of_flat_union.
        apply elem_of_list_In in H1. exists a. split; assumption.
      + subst. exists (from, ιd). cbn. split. by renamePIDPID_sym_case_match.
        apply lookup_kmap_Some; auto.
        exists (to, ιd). cbn. split. by renamePIDPID_sym_case_match.
        do 2 setoid_rewrite lookup_fmap. setoid_rewrite P.
        cbn. f_equal.
        rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext_in.
        intros. apply double_renamePID_signal. intro.
        apply H. right. right. do 3 eexists. split. exact P.
        apply elem_of_flat_union.
        apply elem_of_list_In in H1. exists a. split; assumption.
    - subst. destruct (decide (ιd = from)).
      + subst. exists (ιs, to). cbn. split. by renamePIDPID_sym_case_match.
        apply lookup_kmap_Some; auto.
        exists (ιs, from). cbn. split. by renamePIDPID_sym_case_match.
        do 2 setoid_rewrite lookup_fmap. setoid_rewrite P.
        cbn. f_equal.
        rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext_in.
        intros. apply double_renamePID_signal. intro.
        apply H. right. right. do 3 eexists. split. exact P.
        apply elem_of_flat_union.
        apply elem_of_list_In in H1. exists a. split; assumption.
      + subst. exists (ιs, ιd). cbn. split. by renamePIDPID_sym_case_match.
        apply lookup_kmap_Some; auto.
        exists (ιs, ιd). cbn. split. by renamePIDPID_sym_case_match.
        do 2 setoid_rewrite lookup_fmap. setoid_rewrite P.
        cbn. f_equal.
        rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext_in.
        intros. apply double_renamePID_signal. intro.
        apply H. right. right. do 3 eexists. split. exact P.
        apply elem_of_flat_union.
        apply elem_of_list_In in H1. exists a. split; assumption.
  * apply lookup_kmap_None; auto. intros.
    apply lookup_kmap_None; auto. intros.
    do 2 rewrite lookup_fmap. destruct i, i0. cbn in *.
    renamePIDPID_sym_case_match_hyp H0; inv H0; try lia.
    all: renamePIDPID_sym_case_match_hyp H1; inv H1; try lia.
    all: by setoid_rewrite P.
Qed.

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
              ι'1 ↦ inl ([], r, emptyBox, if link_flag then {[ι'1]} else ∅, false) ∥ ι'0 ↦ p'0 ∥ ι ↦ p' ∥ prs).
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
        ** simpl in Spawns. clear -Spawns H H5 H6 H1 H3 H7.
           rename H into D.
           assert (ι'1 <> ι'0) as X. {
             intro. subst. apply H6. left.
             by setoid_rewrite lookup_insert.
           }
           intro. setoid_rewrite H3 in H6.
           apply H6. apply isUsedPool_insert_1 in H. destruct_or!.
           -- setoid_rewrite delete_insert_ne in H; auto.
              apply isUsedPool_insert_1 in H. destruct_or!.
              ++ apply isUsedPool_insert_2. left.
                 setoid_rewrite delete_commute in H.
                 by apply isUsedPool_delete in H.
              ++ subst. left.
                 by setoid_rewrite lookup_insert.
              ++ right. exists ι, p.
                 split. by setoid_rewrite lookup_insert.
                 clear -D H. inv D; simpl in *; try set_solver.
                 unfold union_set in H. apply elem_of_union_list in H.
                 destruct_hyps. apply elem_of_elements in H.
                 apply elem_of_map_to_set in H. destruct_hyps.
                 apply lookup_delete_Some in H. destruct_hyps. subst.
                 apply elem_of_union_list. exists ({[x0]} ∪ usedPIDsVal x1).
                 split. 2: set_solver.
                 apply elem_of_elements, elem_of_map_to_set. exists x0, x1. by split.
           -- congruence.
           -- rewrite <- H3. right. exists ι'0, p0. split. by setoid_rewrite lookup_insert. assumption.
        ** (* in this case, the pool includes the given PID *)
           intro. apply appearsEther_etherAdd_rev in H0; try congruence.
           -- intro. subst. 
              apply H6. rewrite H3. left. by setoid_rewrite lookup_insert.
           -- intro. apply H6. rewrite H3. right.
              exists ι, p. split. by setoid_rewrite lookup_insert.
              clear -H2 H. inv H; simpl. 1-4: set_solver.
              apply elem_of_union_list. simpl in *.
              exists ({[ι']} ∪ usedPIDsVal reason). split. 2: set_solver.
              apply elem_of_elements, elem_of_map_to_set. exists ι', reason. by split.
      + destruct (decide (ι = ι'1)). {
          exfalso. subst.
          apply map_eq_iff with (i := ι'1) in H3.
          setoid_rewrite lookup_insert in H3.
          setoid_rewrite lookup_insert_ne in H3. 2: now auto.
          apply H6. left.
          setoid_rewrite lookup_insert_ne; auto. congruence.
        }
        setoid_rewrite insert_commute with (j := ι).
        setoid_rewrite insert_commute with (j := ι).
        2-3: now auto.
        replace (ι'1 ↦ inl ([], r, emptyBox, if link_flag then {[ι'1]} else ∅, false) ∥ ι'0 ↦ p'0 ∥ Π) with
          (ι ↦ p ∥ ι'1 ↦ inl ([], r, emptyBox, if link_flag then {[ι'1]} else ∅, false) ∥ ι'0 ↦ p'0 ∥ prs).
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
    - exists (ether', ι'0 ↦ inl ([],r, emptyBox, if link_flag then {[ι'0]} else ∅, false) ∥ ι' ↦ p'0 ∥ ι ↦ p' ∥ prs).
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
        ** clear -H H0 H6 H7 H2 H4 H8.
           rename H into Heth.
           rename H0 into D.
           assert (ι'0 ≠ ι') as X. {
             intro. subst.
             apply H7. left. by setoid_rewrite lookup_insert.
           }
           intro.
           apply isUsedPool_insert_1 in H. destruct_or!.
           -- setoid_rewrite delete_insert_ne in H.
              apply isUsedPool_insert_1 in H. destruct_or!.
              ++ apply H7. rewrite H4. setoid_rewrite delete_commute in H. apply isUsedPool_insert_2.
                 left. by apply isUsedPool_delete in H.
              ++ apply H7. rewrite H4. subst. left. by setoid_rewrite lookup_insert.
              ++ (* Check whether ι'0 came from the ether: *)
                 destruct (decide (ι'0 ∈ usedPIDsProc p)). {
                    apply H7. rewrite H4. right.
                    exists ι, p. split; auto. by setoid_rewrite lookup_insert.
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
                     rewrite lookup_gset_to_gmap in H. unfold mguard, option_guard in H.
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
           -- apply H7. right. exists ι', p0. split. by setoid_rewrite lookup_insert.
              assumption.
        ** intro. cbn in Spawns.
           apply H8. eapply appearsEther_etherPop_rev. exact H1.
           eassumption.
      + assert (ι <> ι'0). {
          apply map_eq_iff with (i := ι) in H4.
          setoid_rewrite lookup_insert in H4.
          setoid_rewrite lookup_insert_ne in H4. 2: now auto.
          intro. subst.
          apply H7. left.
          setoid_rewrite lookup_insert_ne; auto. congruence.
        }
        setoid_rewrite insert_commute with (j := ι).
        setoid_rewrite insert_commute with (j := ι).
        2-3: now auto.
        replace (ι'0 ↦ inl ([], r, emptyBox, if link_flag then {[ι'0]} else ∅, false) ∥ ι' ↦ p'0 ∥ Π) with
          (ι ↦ p ∥ ι'0 ↦ inl ([], r, emptyBox, if link_flag then {[ι'0]} else ∅, false) ∥ ι' ↦ p'0 ∥ prs).
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
    - exists (ether, ι'0 ↦ inl ([], r, emptyBox, if link_flag then {[ι'0]} else ∅, false) ∥ ι' ↦ p'0 ∥ ι ↦ p' ∥ Π).
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
        ** clear -H6 H7 H2 H4 H8 H0 H.
           assert (ι'0 ≠ ι') as X. {
             intro. subst. apply H7. left. by setoid_rewrite lookup_insert.
           }
           intro. apply isUsedPool_insert_1 in H1. destruct_or! H1.
           -- setoid_rewrite delete_insert_ne in H1; auto.
              apply isUsedPool_insert_1 in H1. destruct_or! H1.
              ++ setoid_rewrite delete_commute in H1.
                 apply isUsedPool_delete in H1; auto.
                 rewrite H4 in H7.
                 apply H7. apply isUsedPool_insert_2; auto.
              ++ subst. apply H7. rewrite H4. left. by setoid_rewrite lookup_insert.
              ++ apply H7. rewrite H4. right. do 2 eexists.
                 split. by setoid_rewrite lookup_insert.
                 admit. (* TODO: separate thm needed about the fact that only spawn introduces new PID-s *)
           -- subst. congruence.
           -- apply H7. right. exists ι', p0. split. by setoid_rewrite lookup_insert.
              assumption.
      + assert (ι <> ι'0). {
          apply map_eq_iff with (i := ι) in H4.
          setoid_rewrite lookup_insert in H4.
          setoid_rewrite lookup_insert_ne in H4. 2: now auto.
          clear -H4 H7. apply elem_of_dom_2 in H4.
          apply not_isUsedPool_insert_1 in H7. set_solver.
        }
        setoid_rewrite insert_commute with (j := ι).
        setoid_rewrite insert_commute with (j := ι).
        2-3: now auto.
        replace (ι'0 ↦ inl ([], r, emptyBox, if link_flag then {[ι'0]} else ∅, false) ∥ ι' ↦ p'0 ∥ Π0) with
          (ι ↦ p ∥ ι'0 ↦ inl ([], r, emptyBox, if link_flag then {[ι'0]} else ∅, false) ∥ ι' ↦ p'0 ∥ Π).
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
                                        ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι']} else ∅, false) ∥
                                        ι ↦ p' ∥ Π).
      split.
      + replace (ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι']} else ∅, false) ∥ ι ↦ p' ∥ Π) with 
                (ι'0 ↦ p0 ∥ ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι']} else ∅, false) ∥ ι ↦ p' ∥ Π) at 1.
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
               - subst. apply not_isUsedPool_insert_1 in H1 as [? _].
                 apply not_elem_of_dom in H1. congruence.
               - setoid_rewrite lookup_insert_ne.
                 setoid_rewrite lookup_insert_ne.
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
          apply not_elem_of_dom in H. congruence.
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
        ** simpl in *.
           clear H3.
           assert (ι' <> ι) as X. {
             intro. subst. apply H1. left.
             by setoid_rewrite lookup_insert.
           }
           intro.
           apply H1. apply isUsedPool_insert_1 in H3. destruct_or!.
           -- setoid_rewrite delete_insert_ne in H3; auto.
              apply isUsedPool_insert_1 in H3. destruct_or!.
              ++ apply isUsedPool_insert_2. left.
                 by apply isUsedPool_delete in H3.
              ++ subst. congruence.
              ++ right. rewrite <- H9. exists ι'0, p0.
                 split. by setoid_rewrite lookup_insert.
                 clear -H12 H3. inv H12; simpl in *. 1-4: set_solver.
                 apply elem_of_union_list in H3. destruct_hyps.
                 apply elem_of_elements, elem_of_map_to_set in H. destruct_hyps. subst.
                 apply lookup_delete_Some in H as [? ?].
                 apply elem_of_union_list. exists ({[x0]} ∪ usedPIDsVal x1).
                 split. 2: set_solver.
                 apply elem_of_elements, elem_of_map_to_set.
                 exists x0, x1. by split.
           -- congruence.
           -- right. exists ι, p. split. by setoid_rewrite lookup_insert. assumption.
        ** intro. apply appearsEther_etherAdd_rev in H7; try by auto.
           intro. rewrite <- H9 in H1. apply H1.
           right. exists ι'0, p0. split. by setoid_rewrite lookup_insert.
           clear -H8 H12. inv H12; simpl in *. 1-4: set_solver.
           apply elem_of_union_list. exists ({[ι'1]} ∪ usedPIDsVal reason). split. 2: set_solver.
      apply elem_of_elements, elem_of_map_to_set.
      exists ι'1, reason. by split.
    - exists (ether', ι'0 ↦ p'0 ∥ ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι']} else ∅, false) 
                          ∥ ι ↦ p' ∥ Π ).
      split.
      + replace (ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι']} else ∅, false) ∥ ι ↦ p' ∥ Π) with 
                (ι'0 ↦ p0 ∥ ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι']} else ∅, false) ∥ ι ↦ p' ∥ Π) at 1.
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
               - subst. exfalso.
                 apply H1. left. setoid_rewrite lookup_insert_ne; auto.
                 congruence.
               - setoid_rewrite lookup_insert_ne.
                 setoid_rewrite lookup_insert_ne.
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
          apply not_elem_of_dom in H. congruence.
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
         ** rename H9 into Heth.
           rename H13 into D.
           assert (ι ≠ ι') as X. {
             intro. subst.
             apply H1. left. by setoid_rewrite lookup_insert.
           }
           intro.
           apply isUsedPool_insert_1 in H7. destruct_or!.
           -- setoid_rewrite delete_insert_ne in H7.
              apply isUsedPool_insert_1 in H7. destruct_or!.
              ++ apply H1. apply isUsedPool_insert_2.
                 left. by apply isUsedPool_delete in H7.
              ++ congruence.
              ++ (* Check whether ι' came from the ether: *)
                 destruct (decide (ι' ∈ usedPIDsProc p0)). {
                    apply H1. rewrite <- H8. right.
                    exists ι'0, p0. split; auto. by setoid_rewrite lookup_insert.
                 }
                 inv D; simpl in *; try rewrite flat_union_app in *; simpl in *.
                 2: set_solver.
                 *** destruct (decide (ι' ∈ usedPIDsVal v)). 2: set_solver.
                     apply H2. right. right. exists ι1, ι'0.
                     clear -Heth e0. unfold etherPop in Heth.
                     repeat case_match; try congruence.
                     exists l. subst. split; auto. simpl.
                     inv Heth. set_solver.
                 (* for links: *)
                 *** apply not_elem_of_union in n as [n _].
                     apply not_elem_of_union in n as [n _].
                     apply not_elem_of_union in n as [_ n].
                     apply elem_of_union_list in H7. destruct_hyps.
                     apply elem_of_elements, elem_of_map_to_set in H7. destruct_hyps.
                     subst.
                     rewrite lookup_gset_to_gmap in H7. unfold mguard, option_guard in H7.
                     case_match; clear H10 H3; inv H7.
                     apply elem_of_union in H9 as [|]. set_solver.
                     apply H2. do 2 right. exists ι1, ι'0.
                     unfold etherPop in Heth. repeat case_match; try congruence.
                     eexists. split. reflexivity. simpl. inv Heth. set_solver.
                 *** destruct (decide (ι' = ι1)).
                     2: destruct (decide (ι' ∈ usedPIDsVal reason)).
                     3: { clear-n0 n1 n H7. set_solver. }
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
           -- apply H1. right. exists ι, p. split. by setoid_rewrite lookup_insert.
              assumption.
         ** intro. eapply appearsEther_etherPop_rev in H9. 2: eassumption.
            congruence.
    - exists (ether, ι'0 ↦ p'0 ∥ ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι']} else ∅, false)
                               ∥ ι ↦ p' ∥ Π).
      split.
      + replace (ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι']} else ∅, false) ∥ ι ↦ p' ∥ Π) with 
                (ι'0 ↦ p0 ∥ ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι']} else ∅, false) ∥ ι ↦ p' ∥ Π) at 1.
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
               - subst.
                 exfalso.
                 apply H1. left.
                 setoid_rewrite lookup_insert_ne; auto. congruence.
               - setoid_rewrite lookup_insert_ne.
                 setoid_rewrite lookup_insert_ne.
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
          apply not_elem_of_dom in H. congruence.
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
         ** assert (ι ≠ ι') as X. {
             intro. subst. apply H1. left. by setoid_rewrite lookup_insert.
           }
           intro. apply isUsedPool_insert_1 in H7. destruct_or! H7.
           -- setoid_rewrite delete_insert_ne in H7; auto.
              apply isUsedPool_insert_1 in H7. destruct_or! H7.
              ++ apply isUsedPool_delete in H7; auto.
                 apply H1. apply isUsedPool_insert_2; auto.
              ++ congruence.
              ++ apply H1. rewrite <- H8. right. do 2 eexists.
                 split. by setoid_rewrite lookup_insert.
                 admit. (* TODO: separate thm needed about the fact that only spawn introduces new PID-s *)
           -- subst. congruence.
           -- apply H1. right. exists ι, p. split. by setoid_rewrite lookup_insert.
              assumption.
    - (** cannot be sure to generate different spawn PID-s *)
      exists (ether, ι'1 ↦ inl ([], r0, emptyBox, if link_flag0 then {[ι'1]} else ∅, false) ∥ ι'0 ↦ p'0 ∥ ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι']} else ∅, false) ∥ ι ↦ p' ∥ Π).
      assert (ι'0 ≠ ι') as X1. {
        intro. subst. apply H1. rewrite <- H8. left. by setoid_rewrite lookup_insert.
      }
      assert (ι'1 ≠ ι') as X2. {
        intro. subst. simpl in Spawns. congruence.
      }
      assert (ι'1 ≠ ι) as X3. {
        intro. subst. apply H11. rewrite H8. left. by setoid_rewrite lookup_insert.
      }
      assert (ι'1 ≠ ι'0) as X4. {
        intro. subst. apply H11. left. by setoid_rewrite lookup_insert.
      }
      assert (ι' ≠ ι) as X5. {
        intro. subst. apply H1. left. by setoid_rewrite lookup_insert.
      }
      split.
      + replace (ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι']} else ∅, false) ∥ ι ↦ p' ∥ Π) with
                (ι'0 ↦ p0 ∥ ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι']} else ∅, false) ∥ ι ↦ p' ∥ Π) at 1.
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
               - subst. exfalso.
                 apply H1. left.
                 setoid_rewrite lookup_insert_ne; auto.
               - setoid_rewrite lookup_insert_ne.
                 setoid_rewrite lookup_insert_ne.
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
                 setoid_rewrite delete_commute in H5; auto.
                 apply isUsedPool_delete in H5; auto.
                 setoid_rewrite delete_commute in H5; auto.
                 apply isUsedPool_delete in H5; auto.
              ++ congruence.
              ++ admit. (* TODO: same helper thm as for tau steps *)
           -- congruence.
           -- cbn in H5. apply H11. rewrite H8. right.
              exists ι, p. split. by setoid_rewrite lookup_insert.
              clear -H5 H4 H3 H X2. inv H4.
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
                ++ simpl in *. set_solver.
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
                ++ simpl in *. set_solver.
              }
        ** congruence.
        ** apply H11. right. exists ι'0, p0. split. by setoid_rewrite lookup_insert.
           assumption.
      + setoid_rewrite insert_commute with (j := ι').
        setoid_rewrite insert_commute with (j := ι').
        setoid_rewrite insert_commute with (j := ι).
        setoid_rewrite insert_commute with (j := ι).
        2-5: now auto.
        replace (ι'1 ↦ inl ([], r0, emptyBox, if link_flag0 then {[ι'1]} else ∅, false) ∥ ι'0 ↦ p'0 ∥ Π0) with
          (ι ↦ p ∥ ι'1 ↦ inl ([], r0, emptyBox, if link_flag0 then {[ι'1]} else ∅, false) ∥ ι'0 ↦ p'0 ∥ Π) at 1.
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
         intro. apply isUsedPool_insert_1 in H5. destruct_or!.
          ** setoid_rewrite delete_insert_ne in H5; auto.
             apply isUsedPool_insert_1 in H5. destruct_or!.
             -- setoid_rewrite delete_insert_ne in H5; auto.
                setoid_rewrite delete_insert_ne in H5; auto.
                apply isUsedPool_insert_1 in H5. destruct_or!.
                ++ apply H1. apply isUsedPool_insert_2. left.
                   apply isUsedPool_delete in H5; auto.
                   apply isUsedPool_delete in H5; auto.
                ++ congruence.
                ++ admit. (* TODO: same helper thm as for tau steps *)
             -- congruence.
             -- cbn in H5. apply H1. rewrite <- H8. right.
                exists ι'0, p0. split. by setoid_rewrite lookup_insert.
                clear -H5 H17 H13 H9 X2. inv H17. 
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
                  ++ simpl in *. set_solver.
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
                  ++ simpl in *. set_solver.
                }
          ** congruence.
          ** apply H1. right. exists ι, p. split. by setoid_rewrite lookup_insert.
             assumption.
Admitted.

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
      exists (ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι']} else ∅, false) ∥ ι ↦ p' ∥ Π).
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
          - by setoid_rewrite lookup_delete in H.
          - apply lookup_delete_None in H0 as [|]. congruence.
            setoid_rewrite H0 in HL. apply eq_sym, lookup_union_None in HL as [? ?].
            apply lookup_delete_None. by right.
        * destruct_hyps. right.
          put (lookup x : ProcessPool -> option Process) on H1 as HL. simpl in HL.
          setoid_rewrite lookup_delete_Some in H. destruct_hyps.
          processpool_destruct. 1: congruence.
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
    - inv H1'. setoid_rewrite H0. right. exists (ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι']} else ∅, false) ∥ ι ↦ p' ∥ Π2).
      split.
      {
        1: eapply n_spawn; eauto.
        rewrite H1 in H6. rewrite H0 in H6.
        setoid_rewrite <- insert_union_r in H6. 2: by apply not_elem_of_dom.
        intro X. destruct X.
        * apply H6; left. destruct (decide (ι = ι')).
          - subst. by setoid_rewrite lookup_insert.
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
    - subst. apply H0. left. by setoid_rewrite lookup_insert.
    - apply H0. clear -H3 H4.
      right. exists ι, p. split. by setoid_rewrite lookup_insert.
      inv H3; simpl in *. 1-4: set_solver.
      apply elem_of_union_list. exists ({[ι']} ∪ usedPIDsVal reason). split. 2: set_solver.
      apply elem_of_elements, elem_of_map_to_set.
      exists ι', reason. by split.
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
    - subst. right. do 3 eexists. split. reflexivity.
      intro. apply H0. right. exists ι, p. split. by setoid_rewrite lookup_insert.
      inv H8; set_solver.
    - left. intro.
      apply H0. right. exists ι, p. split. by setoid_rewrite lookup_insert.
      inv H8; simpl in *; clear-H n; set_solver.
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
