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

Lemma par_eq : forall T ι (p p' : T) Π Π',
  ι ↦ p ∥ Π = ι ↦ p' ∥ Π' -> p = p'.
Proof.
  intros. apply equal_f with ι in H as H'.
  unfold update in H'; break_match_hyp. 
  2: { apply Nat.eqb_neq in Heqb. congruence. } inversion H'. auto.
Qed.

Lemma par_eq_Π : forall T ι (p p' : T) Π Π',
  ι ↦ p ∥ Π = ι ↦ p' ∥ Π' -> forall p'', ι ↦ p'' ∥ Π = ι ↦ p'' ∥ Π'.
Proof.
  intros. extensionality ι'.
  unfold update. break_match_goal; auto.
  apply equal_f with ι' in H. unfold update in H. now rewrite Heqb in H.
Qed.

Lemma concurrent_determinism :
  forall Π a ι Π', Π -[a | ι]ₙ-> Π' -> forall Π'', Π -[a | ι]ₙ-> Π'' -> Π' = Π''.
Proof.
  intros Π a ι Π' IH. inversion IH; intros; subst.
  * inv H4.
    - apply par_eq in H2 as H2'. subst.
      eapply process_local_determinism in H. 2:exact H8. subst. auto. f_equal.
      extensionality ι''. apply equal_f with ι'' in H2. unfold update in *.
      break_match_goal; auto.
    - intuition; try congruence.
  * inv H5.
    - apply par_eq in H2 as H2'. inversion H2'. subst.
      eapply process_local_determinism in H0. 2: exact H10. subst.
      rewrite H in H9. inv H9.
      f_equal.
      extensionality ι''. apply equal_f with ι'' in H2. unfold update in *.
      break_match_goal; auto.
    - intuition; try congruence.
  * inv H5.
    - intuition; try congruence.
    - intuition; try congruence.
    - apply par_eq in H2 as H2'. subst.
      eapply process_local_determinism in H. 2: exact H3. subst. f_equal.
      extensionality ι''. apply equal_f with ι'' in H2. unfold update in *.
      break_match_goal; auto.
    - intuition; try congruence.
(*     - apply par_eq in H3 as H3'. subst.
      inv H. *)
  * inv H7.
    - intuition; try congruence.
    - apply par_eq in H4 as H4'. subst.
      eapply process_local_determinism in H2. 2: exact H14. subst.
      f_equal. rewrite H in H9. inv H9.
      rewrite H1 in H13. inv H13.
      extensionality ι''. apply equal_f with ι'' in H4. unfold update in *.
      break_match_goal; auto.
      break_match_goal; auto.
(*   * inv H3.
    - apply par_eq in H0 as H0'. subst.
      intuition; subst; try congruence.
    - unfold update in *. f_equal.
      extensionality ι'. apply equal_f with ι' in H1. break_match_goal; auto. *)
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
  * exfalso. inv H0; inv H; try inv H6; cbn in *; invSome.
(*   * inv H0. *)
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
    - apply par_eq in H4. subst. inv H1. inv H7. now cbn in *.
    - apply par_eq in H4. subst. inv H1. inv H7. now cbn in *.
    - apply par_eq in H4. subst. inv H1. inv H7. now cbn in *.
    - apply par_eq in H4. subst. inv H1. inv H7. now cbn in *.
    - apply par_eq in H4. subst. inv H1.
  * apply par_eq in H3 as H3'. subst.
    apply internal_is_alive in H1 as H1'. destruct H1'. subst.
    eapply internal_equal in H8. 2: eassumption.
    intuition; subst; try congruence.
    right. repeat destruct_hyps. do 2 eexists. split. reflexivity.
    inv H0.
    eexists. split. constructor; try eassumption. destruct H5.
    - left. erewrite par_eq_Π.
      apply n_other; now auto.
      eassumption.
    - right. subst. erewrite par_eq_Π. reflexivity. eassumption.
  * apply par_eq in H3 as H3'. subst.
    destruct H8 as [H8 | [ H8 | H8]].
    - subst. left. split; auto. eapply process_local_determinism in H4. 2: exact H1.
      subst. eapply par_eq_Π in H3. now rewrite H3.
    - subst. exfalso. inv H4. inv H1. inv H8.
      now cbn in *.
    - subst. exfalso. inv H4; inv H1; try inv H9; try inv H8; try now cbn in *.
  * apply par_eq in H3 as H3'. subst.
    exfalso. inv H10. inv H1. inv H12. now cbn in *.
(*   * apply par_eq in H4 as H4'. subst.
    inv H1. *)
Qed.

Definition bothSpawn (a1 a2 : Action) : Prop:=
match a1, a2 with
| ASpawn _ _ _, ASpawn _ _ _ => True
| _, _ => False
end.

(*

  n ---- ι:a ----> n'
  |                ∥
  | ι':a'          ∥ ι':a'
  |                ∥
  v                v
  n'' == ι:a ===> n'''

*)
Lemma confluence :
  forall n n' ι a, n -[a | ι]ₙ-> n' -> forall n'' a' ι' 
    (Spawns : PIDOf a <> PIDOf a'), n -[a' | ι']ₙ-> n'' ->
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
        2: { extensionality ι1. unfold update in *. apply equal_f with ι1 in H4.
             break_match_goal; subst.
             break_match_goal; subst. eqb_to_eq. congruence. auto.
             auto.
           }
        now constructor.
      + rewrite update_swap. rewrite etherAdd_swap. 2-3: now auto.
        replace (ι'0 ↦ p'0 ∥ prs0) with (ι ↦ p ∥ ι'0 ↦ p'0 ∥ prs) at 1.
        2: { extensionality ι1. unfold update in *. apply equal_f with ι1 in H4.
             break_match_goal; subst.
             break_match_goal; subst; eqb_to_eq; try congruence.
             break_match_goal; auto.
           }
        now constructor.
    - exists (etherAdd ι ι' t ether', ι'0 ↦ p'0 ∥ ι ↦ p' ∥ prs).
      split.
      + replace (ι ↦ p' ∥ prs) with (ι'0 ↦ p0 ∥ ι ↦ p' ∥ prs) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H3.
             break_match_goal; subst.
             break_match_goal; subst. eqb_to_eq. congruence. auto.
             auto.
           }
        constructor. 2: eauto.
        now apply etherPop_greater.
      + rewrite update_swap. 2: now auto.
        replace (ι'0 ↦ p'0 ∥ prs0) with (ι ↦ p ∥ ι'0 ↦ p'0 ∥ prs) at 1.
        2: { extensionality ι2. unfold update in *. apply equal_f with ι2 in H3.
             break_match_goal; subst.
             break_match_goal; subst; eqb_to_eq; try congruence.
             break_match_goal; auto.
           }
        now constructor.
    - exists (etherAdd ι ι' t ether, ι'0 ↦ p'0 ∥ ι ↦ p' ∥ prs).
      split.
      + replace (ι ↦ p' ∥ prs) with (ι'0 ↦ p0 ∥ ι ↦ p' ∥ prs) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H3.
             break_match_goal; subst.
             break_match_goal; subst. eqb_to_eq. congruence. auto.
             auto.
           }
        apply n_other; eauto.
      + rewrite update_swap. 2: now auto.
        replace (ι'0 ↦ p'0 ∥ Π) with (ι ↦ p ∥ ι'0 ↦ p'0 ∥ prs) at 1.
        2: { extensionality ι2. unfold update in *. apply equal_f with ι2 in H3.
             break_match_goal; subst.
             break_match_goal; subst; eqb_to_eq; try congruence.
             break_match_goal; auto.
           }
        now constructor.
    - exists (etherAdd ι ι' t ether, 
              ι'1 ↦ inl ([], r, emptyBox, [], false) ∥ ι'0 ↦ p'0 ∥ ι ↦ p' ∥ prs).
      split.
      + replace (ι ↦ p' ∥ prs) with (ι'0 ↦ p0 ∥ ι ↦ p' ∥ prs) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H3.
             break_match_goal; subst.
             break_match_goal; subst. eqb_to_eq. congruence. auto.
             auto.
           }
        eapply n_spawn; try eassumption.
        apply equal_f with ι'1 in H3.
        unfold update in *. break_match_goal; auto.
        break_match_goal; subst.
        ** congruence.
        ** now rewrite H3 in H5.
      + assert (ι <> ι'1). {
          unfold update in H5. break_match_hyp; try congruence.
          apply equal_f with ι'1 in H3. unfold update in H3.
          do 2 break_match_hyp; try congruence; now eqb_to_eq.
        }
        rewrite update_swap with (ι' := ι). rewrite update_swap with (ι' := ι).
        2-3: now auto.
        replace (ι'1 ↦ inl ([], r, emptyBox, [], false) ∥ ι'0 ↦ p'0 ∥ Π) with
          (ι ↦ p ∥ ι'1 ↦ inl ([], r, emptyBox, [], false) ∥ ι'0 ↦ p'0 ∥ prs).
        2: { extensionality x. unfold update in *. apply equal_f with x in H3.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence.
           }
        now constructor.
(*     - exists (etherAdd ι ι' t ether, (ι ↦ p' ∥ prs) -- ι'0).
      split.
      + replace (ι ↦ p' ∥ prs) with (ι'0 ↦ inr [] ∥ ι ↦ p' ∥ prs) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H4.
             break_match_goal; subst.
             break_match_goal; subst. eqb_to_eq. congruence. auto.
             auto.
           }
        apply n_terminate.
      + rewrite update_swap. 2: now auto.
        replace (Π -- ι'0) with (ι ↦ p ∥ prs -- ι'0).
        2: {
             extensionality x. unfold update in *. apply equal_f with x in H4.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
           }
        now apply n_send. *)
  * inv H1.
    - exists (etherAdd ι' ι'0 t0 ether', ι' ↦ p'0 ∥ ι ↦ p' ∥ prs).
      split.
      + replace (ι ↦ p' ∥ prs) with (ι' ↦ p0 ∥ ι ↦ p' ∥ prs) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H5.
             break_match_goal; subst.
             break_match_goal; subst. eqb_to_eq. congruence. auto.
             auto.
           }
        now constructor.
      + rewrite update_swap. 2: now auto.
        replace (ι' ↦ p'0 ∥ prs0) with (ι ↦ p ∥ ι' ↦ p'0 ∥ prs) at 1.
        2: {
             extensionality x. unfold update in *. apply equal_f with x in H5.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
           }
        now constructor.
    - assert (exists ether'', etherPop ι2 ι' ether'  = Some (t0, ether''))
                                 as [ether'' Eq].
      {
         unfold etherPop in H, H5. do 2 break_match_hyp. 1-3: congruence.
         inversion H. inv H5. subst.
         unfold etherPop, update. destruct (ι1 =? ι2) eqn:Eq; eqb_to_eq; subst.
         * apply Nat.eqb_neq in H2. rewrite H2, Heql. eexists. reflexivity.
         * rewrite Heql. eexists. reflexivity.
      }
      exists (ether'', ι' ↦ p'0 ∥ ι ↦ p' ∥ prs ).
      split.
      + replace (ι ↦ p' ∥ prs) with (ι' ↦ p0 ∥ ι ↦ p' ∥ prs) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H4.
             break_match_goal; subst.
             break_match_goal; subst. eqb_to_eq. congruence. auto.
             auto.
           }
        constructor; auto.
      + rewrite update_swap. 2: now auto.
        replace (ι' ↦ p'0 ∥ prs0) with (ι ↦ p ∥ ι' ↦ p'0 ∥ prs) at 1.
        2: {
             extensionality x. unfold update in *. apply equal_f with x in H4.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
           }
        constructor; auto.
        clear -H H5 H2 Eq. unfold etherPop in *.
        repeat break_match_hyp; try congruence. do 3 invSome.
        unfold update at 1. destruct (ι2 =? ι1) eqn:Eq2; eqb_to_eq.
        ** subst. unfold update at 1.
           destruct (ι' =? ι) eqn:Eq3; eqb_to_eq; try congruence.
           rewrite Heql1. rewrite update_same. do 2 f_equal.
           rewrite update_same. f_equal. unfold update in *. extensionality x.
           repeat break_match_goal; auto; eqb_to_eq; subst; try congruence.
           break_match_hyp; eqb_to_eq; try congruence.
        ** rewrite Heql1. do 2 f_equal.
           rewrite update_swap. 2: now auto. f_equal.
           -- unfold update in *. extensionality x.
              repeat break_match_goal; auto; eqb_to_eq; subst; try congruence.
              break_match_hyp; eqb_to_eq; try congruence.
           -- unfold update in *. extensionality x.
              repeat break_match_goal; auto; eqb_to_eq; subst; try congruence.
    - exists (ether', ι' ↦ p'0 ∥ ι ↦ p' ∥ prs).
      split.
      + replace (ι ↦ p' ∥ prs) with (ι' ↦ p0 ∥ ι ↦ p' ∥ prs) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H4.
             break_match_goal; subst.
             break_match_goal; subst. eqb_to_eq. congruence. auto.
             auto.
           }
        now constructor.
      + rewrite update_swap. 2: now auto.
        replace (ι' ↦ p'0 ∥ Π) with (ι ↦ p ∥ ι' ↦ p'0 ∥ prs) at 1.
        2: {
             extensionality x. unfold update in *. apply equal_f with x in H4.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
           }
        now apply n_arrive.
    - exists (ether', ι'0 ↦ inl ([],r, emptyBox, [], false) ∥ ι' ↦ p'0 ∥ ι ↦ p' ∥ prs).
      split.
      + replace (ι ↦ p' ∥ prs) with (ι' ↦ p0 ∥ ι ↦ p' ∥ prs) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H4.
             break_match_goal; subst.
             break_match_goal; subst. eqb_to_eq. congruence. auto.
             auto.
           }
        eapply n_spawn; eauto.
        apply equal_f with ι'0 in H4.
        unfold update in *. break_match_goal; auto.
        break_match_goal; subst.
        ** congruence.
        ** now rewrite H4 in H6.
      + assert (ι <> ι'0). {
          unfold update in H6. break_match_hyp; try congruence.
          apply equal_f with ι'0 in H4. unfold update in H4.
          do 2 break_match_hyp; try congruence; now eqb_to_eq.
        }
        rewrite update_swap with (ι' := ι). rewrite update_swap with (ι' := ι).
        2-3: now auto.
        replace (ι'0 ↦ inl ([], r, emptyBox, [], false) ∥ ι' ↦ p'0 ∥ Π) with
          (ι ↦ p ∥ ι'0 ↦ inl ([], r, emptyBox, [], false) ∥ ι' ↦ p'0 ∥ prs).
        2: {
              extensionality x. unfold update in *. apply equal_f with x in H4.
              break_match_goal; subst.
              all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
           }
        now constructor.
(*     - exists (ether', ι ↦ p' ∥ prs -- ι').
      split.
      + replace (ι ↦ p' ∥ prs) with (ι' ↦ inr [] ∥ ι ↦ p' ∥ prs) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H5.
             break_match_goal; subst.
             break_match_goal; subst. eqb_to_eq. congruence. auto.
             auto.
           }
        rewrite update_swap with (ι := ι); auto.
        constructor; auto.
      + replace (Π -- ι') with (ι ↦ p ∥ prs -- ι').
        2: {
             extensionality x. unfold update in *. apply equal_f with x in H5.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
           }
        now constructor. *)
  * inv H1.
    - exists (etherAdd ι' ι'0 t ether, ι' ↦ p'0 ∥ ι ↦ p' ∥ Π).
      split.
      + replace (ι ↦ p' ∥ Π) with (ι' ↦ p0 ∥ ι ↦ p' ∥ Π) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H5.
             break_match_goal; subst.
             break_match_goal; subst. eqb_to_eq. congruence. auto.
             auto.
           }
        now constructor.
      + rewrite update_swap. 2: now auto.
        replace (ι' ↦ p'0 ∥ prs) with (ι ↦ p ∥ ι' ↦ p'0 ∥ Π) at 1.
        2: {
             extensionality x. unfold update in *. apply equal_f with x in H5.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
           }
        now constructor.
    - exists (ether', ι' ↦ p'0 ∥ ι ↦ p' ∥ Π ).
      split.
      + replace (ι ↦ p' ∥ Π) with (ι' ↦ p0 ∥ ι ↦ p' ∥ Π) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H4.
             break_match_goal; subst.
             break_match_goal; subst. eqb_to_eq. congruence. auto.
             auto.
           }
        constructor; auto.
      + rewrite update_swap. 2: now auto.
        replace (ι' ↦ p'0 ∥ prs) with (ι ↦ p ∥ ι' ↦ p'0 ∥ Π) at 1.
        2: {
             extensionality x. unfold update in *. apply equal_f with x in H4.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
           }
        now constructor.
    - exists (ether, ι' ↦ p'0 ∥ ι ↦ p' ∥ Π).
      split.
      + replace (ι ↦ p' ∥ Π) with (ι' ↦ p0 ∥ ι ↦ p' ∥ Π) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H4.
             break_match_goal; subst.
             break_match_goal; subst. eqb_to_eq. congruence. auto.
             auto.
           }
        now constructor.
      + rewrite update_swap. 2: now auto.
        replace (ι' ↦ p'0 ∥ Π0) with (ι ↦ p ∥ ι' ↦ p'0 ∥ Π) at 1.
        2: {
             extensionality x. unfold update in *. apply equal_f with x in H4.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
           }
        now constructor.
    - exists (ether, ι'0 ↦ inl ([], r, emptyBox, [], false) ∥ ι' ↦ p'0 ∥ ι ↦ p' ∥ Π).
      split.
      + replace (ι ↦ p' ∥ Π) with (ι' ↦ p0 ∥ ι ↦ p' ∥ Π) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H4.
             break_match_goal; subst.
             break_match_goal; subst. eqb_to_eq. congruence. auto.
             auto.
           }
        eapply n_spawn; eauto.
        apply equal_f with ι'0 in H4.
        unfold update in *. break_match_goal; auto.
        break_match_goal; subst.
        ** congruence.
        ** now rewrite H4 in H6.
      + assert (ι <> ι'0). {
          unfold update in H6. break_match_hyp; try congruence.
          apply equal_f with ι'0 in H4. unfold update in H4.
          do 2 break_match_hyp; try congruence; now eqb_to_eq.
        }
        rewrite update_swap with (ι' := ι). rewrite update_swap with (ι' := ι).
        2-3: now auto.
        replace (ι'0 ↦ inl ([], r, emptyBox, [], false) ∥ ι' ↦ p'0 ∥ Π0) with
          (ι ↦ p ∥ ι'0 ↦ inl ([], r, emptyBox, [], false) ∥ ι' ↦ p'0 ∥ Π).
        2: {
             extensionality x. unfold update in *. apply equal_f with x in H4.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
           }
        now constructor.
(*     - exists (ether, ι ↦ p' ∥ Π -- ι').
      split.
      + replace (ι ↦ p' ∥ Π) with (ι' ↦ inr [] ∥ ι ↦ p' ∥ Π) at 1.
        2: { extensionality ι1. unfold update in *. apply equal_f with ι1 in H5.
             break_match_goal; subst.
             break_match_goal; subst. eqb_to_eq. congruence. auto.
             auto.
           }
        rewrite update_swap with (ι := ι); auto.
        constructor; auto.
      + replace (Π0 -- ι') with (ι ↦ p ∥ Π -- ι') at 1.
        2: {
             extensionality x. unfold update in *. apply equal_f with x in H5.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
           }
         now constructor. *)
  * inv H3.
    - exists (etherAdd ι'0 ι'1 t ether, ι'0 ↦ p'0 ∥
                                        ι' ↦ inl ([], r, emptyBox, [], false) ∥
                                        ι ↦ p' ∥ Π).
      split.
      + replace (ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) with 
                (ι'0 ↦ p0 ∥ ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H7.
             break_match_goal; subst;
             break_match_goal; subst; auto.
             all: break_match_hyp; eqb_to_eq; subst; auto; try congruence.
             break_match_hyp; congruence.
           }
        constructor; now eauto.
      + assert (ι'0 <> ι'). {
          unfold update in H0. break_match_hyp; try congruence.
          apply equal_f with ι' in H7. unfold update in H7.
          do 2 break_match_hyp; try congruence; now eqb_to_eq.
        }
        rewrite update_swap with (ι' := ι'). rewrite update_swap with (ι' := ι).
        2-3: now auto.
        replace (ι'0 ↦ p'0 ∥ prs) with
          (ι ↦ p ∥ ι'0 ↦ p'0 ∥ Π) at 1.
        2: {
             extensionality x. unfold update in *. apply equal_f with x in H7.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
           }
         eapply n_spawn; eauto.
         ** clear -H0 H7. unfold update in *. apply equal_f with ι' in H7.
            repeat break_match_hyp; try congruence.
    - exists (ether', ι'0 ↦ p'0 ∥ ι' ↦ inl ([], r, emptyBox, [], false) 
                          ∥ ι ↦ p' ∥ Π ).
      split.
      + replace (ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) with 
                (ι'0 ↦ p0 ∥ ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H6.
             break_match_goal; subst;
             break_match_goal; subst; auto.
             all: break_match_hyp; eqb_to_eq; subst; auto; try congruence.
             break_match_hyp; congruence.
           }
        constructor; auto.
      + assert (ι'0 <> ι'). {
          unfold update in H0. break_match_hyp; try congruence.
          apply equal_f with ι' in H6. unfold update in H6.
          do 2 break_match_hyp; try congruence; now eqb_to_eq.
        }
        rewrite update_swap with (ι' := ι'). rewrite update_swap with (ι' := ι).
        2-3: now auto.
        replace (ι'0 ↦ p'0 ∥ prs) with
          (ι ↦ p ∥ ι'0 ↦ p'0 ∥ Π) at 1.
        2: {
             extensionality x. unfold update in *. apply equal_f with x in H6.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
           }
         eapply n_spawn; eauto.
         ** clear -H0 H6. unfold update in *. apply equal_f with ι' in H6.
            repeat break_match_hyp; try congruence.
    - exists (ether, ι'0 ↦ p'0 ∥ ι' ↦ inl ([], r, emptyBox, [], false)
                               ∥ ι ↦ p' ∥ Π).
      split.
      + replace (ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) with 
                (ι'0 ↦ p0 ∥ ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H6.
             break_match_goal; subst;
             break_match_goal; subst; auto.
             all: break_match_hyp; eqb_to_eq; subst; auto; try congruence.
             break_match_hyp; congruence.
           }
        now constructor.
      + assert (ι'0 <> ι'). {
          unfold update in H0. break_match_hyp; try congruence.
          apply equal_f with ι' in H6. unfold update in H6.
          do 2 break_match_hyp; try congruence; now eqb_to_eq.
        }
        rewrite update_swap with (ι' := ι'). rewrite update_swap with (ι' := ι).
        2-3: now auto.
        replace (ι'0 ↦ p'0 ∥ Π0) with
          (ι ↦ p ∥ ι'0 ↦ p'0 ∥ Π) at 1.
        2: {
             extensionality x. unfold update in *. apply equal_f with x in H6.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
           }
         eapply n_spawn; eauto.
         ** clear -H0 H6. unfold update in *. apply equal_f with ι' in H6.
            repeat break_match_hyp; try congruence.
    - (** cannot be sure to generate different spawn PID-s *)
      exists (ether, ι'1 ↦ inl ([], r0, emptyBox, [], false) ∥ ι'0 ↦ p'0 ∥ ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π).
      split.
      + replace (ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) with
                (ι'0 ↦ p0 ∥ ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H6.
             break_match_goal; subst;
             break_match_goal; subst; auto.
             all: break_match_hyp; eqb_to_eq; subst; auto; try congruence.
             repeat break_match_hyp; try congruence.
           }
        eapply n_spawn; try eassumption.
        clear -H8 H6 H0 Spawns. unfold update in *. cbn in *.
        repeat break_match_goal; eqb_to_eq; subst; try congruence.
        ** break_match_hyp; eqb_to_eq; try congruence.
           apply equal_f with ι'1 in H6. rewrite Nat.eqb_refl in H6.
           break_match_hyp; eqb_to_eq; try congruence.
        ** break_match_hyp; eqb_to_eq; try congruence.
           apply equal_f with ι'1 in H6.
           break_match_hyp; eqb_to_eq; try congruence.
           break_match_hyp; eqb_to_eq; try congruence.
      + assert (ι'0 <> ι' /\ ι'1 <> ι /\ ι'1 <> ι'). {
          unfold update in H0, H8. break_match_hyp; try congruence.
          apply equal_f with ι' in H6 as H6'.
          apply equal_f with ι'1 in H6 as H6''.
          apply equal_f with ι in H6. unfold update in *.
          do 2 break_match_hyp; try congruence; eqb_to_eq.
          split; auto.
          all: repeat break_match_hyp; eqb_to_eq; try congruence; subst; eqb_to_eq.
          split; auto. cbn in Spawns. intro. apply Spawns. now auto.
        }
        rewrite update_swap with (ι' := ι'). rewrite update_swap with (ι' := ι).
        rewrite update_swap with (ι' := ι'). rewrite update_swap with (ι' := ι).
        2-5: try auto.
        replace (ι'1 ↦ inl ([], r0, emptyBox, [], false) ∥ ι'0 ↦ p'0 ∥ Π0) with
          (ι ↦ p ∥ ι'1 ↦ inl ([], r0, emptyBox, [], false) ∥ ι'0 ↦ p'0 ∥ Π) at 1.
        2: {
             extensionality x. unfold update in *. apply equal_f with x in H6.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
             repeat break_match_hyp; eqb_to_eq; subst; try congruence.
           }
         eapply n_spawn; eauto.
         ** unfold update in *. destruct_hyps.
            repeat break_match_goal; eqb_to_eq; try congruence.
         ** apply H3.
         ** apply H3.
         ** apply H3.
(*     - exists (ether,
               ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π -- ι'0).
      split.
      + replace (ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) with 
                (ι'0 ↦ inr [] ∥ ι' ↦ inl ([], r, emptyBox, [], false) 
                              ∥ ι ↦ p' ∥ Π) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H7.
             break_match_goal; subst.
             break_match_goal; subst. eqb_to_eq. subst.
             break_match_hyp; congruence.
             break_match_goal; auto. eqb_to_eq. congruence.
             break_match_goal; auto.
           }
        rewrite update_swap with (ι := ι); auto.
        rewrite update_swap with (ι := ι') (ι' := ι'0); auto.
        constructor; auto.
        apply equal_f with ι' in H7. unfold update in H7. cbn in H7.
        break_match_hyp; eqb_to_eq; auto; subst.
        break_match_hyp; eqb_to_eq; subst; try congruence; auto.
        unfold update in H0. break_match_hyp; congruence.
    + assert (ι'0 <> ι'). {
          unfold update in H0. break_match_hyp; try congruence.
          apply equal_f with ι' in H7. unfold update in H7.
          do 2 break_match_hyp; try congruence; now eqb_to_eq.
        }
        replace (Π0 -- ι'0) with (ι ↦ p ∥ Π -- ι'0) at 1.
        2: {
             extensionality x. unfold update in *. apply equal_f with x in H7.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
           }
         eapply n_spawn; eauto.
         ** clear -H0 H7. unfold update in *. apply equal_f with ι' in H7.
            repeat break_match_hyp; try congruence. *)
(*   * inv H; subst.
    - exists (etherAdd ι' ι'0 t ether, ι' ↦ p' ∥ (Π -- ι)).
      split.
      + replace (Π -- ι) with (ι' ↦ p ∥ (Π -- ι)) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H3.
             break_match_goal; subst.
             break_match_goal; subst. eqb_to_eq. congruence. auto.
             auto.
           }
        now constructor.
      + rewrite update_swap. 2: now auto.
        replace (ι' ↦ p' ∥ prs) with (ι ↦ inr [] ∥ ι' ↦ p' ∥ Π) at 1.
        2: {
             extensionality x. unfold update in *. apply equal_f with x in H3.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
           }
        now constructor.
    - exists (ether', ι' ↦ p' ∥ (Π -- ι) ).
      split.
      + replace (Π -- ι) with (ι' ↦ p ∥ (Π -- ι)) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H2.
             break_match_goal; subst.
             break_match_goal; subst. eqb_to_eq. congruence. auto.
             auto.
           }
        constructor; auto.
      + rewrite update_swap. 2: now auto.
        replace (ι' ↦ p' ∥ prs) with (ι ↦ inr [] ∥ ι' ↦ p' ∥ Π) at 1.
        2: {
             extensionality x. unfold update in *. apply equal_f with x in H2.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
           }
        now constructor.
    - exists (ether, ι' ↦ p' ∥ (Π -- ι)).
      split.
      + replace (Π -- ι) with (ι' ↦ p ∥ (Π -- ι)) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H2.
             break_match_goal; subst.
             break_match_goal; subst. eqb_to_eq. congruence. auto.
             auto.
           }
        now constructor.
      + rewrite update_swap. 2: now auto.
        replace (ι' ↦ p' ∥ Π0) with (ι ↦ inr [] ∥ ι' ↦ p' ∥ Π) at 1.
        2: {
             extensionality x. unfold update in *. apply equal_f with x in H2.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
           }
        now constructor.
    - exists (ether, 
              ι'0 ↦ inl ([], r, emptyBox, [], false) ∥ ι' ↦ p' ∥ (Π -- ι)).
      split.
      + replace (Π -- ι) with (ι' ↦ p ∥ (Π -- ι)) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H2.
             break_match_goal; subst.
             break_match_goal; subst. eqb_to_eq. congruence. auto.
             auto.
           }
        econstructor; eauto.
        apply equal_f with ι'0 in H2.
        unfold update in *. break_match_goal; auto.
        break_match_goal; subst; auto. congruence.
      + assert (ι'0 <> ι). {
          unfold update in H4. break_match_hyp; try congruence.
          apply equal_f with ι in H2. unfold update in H2.
          do 2 break_match_hyp; try congruence; now eqb_to_eq.
        }
        rewrite update_swap with (ι' := ι). rewrite update_swap with (ι' := ι).
        2-3: now auto.
        replace (ι'0 ↦ inl ([], r, emptyBox, [], false) ∥ ι' ↦ p' ∥ Π0) with (ι ↦ inr [] ∥ι'0 ↦ inl ([], r, emptyBox, [], false) ∥ ι' ↦ p' ∥ Π) at 1.
        2: {
             extensionality x. unfold update in *. apply equal_f with x in H2.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
           }
        now constructor.
    - exists (ether, (Π -- ι) -- ι').
      split.
      + replace (Π -- ι) with (ι' ↦ inr [] ∥ (Π -- ι)) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H3.
             break_match_goal; subst. auto.
             break_match_goal; subst. eqb_to_eq. congruence. auto.
             break_match_goal; subst; auto.
           }
        constructor; auto.
      + rewrite update_swap. 2: now auto.
        replace (Π0 -- ι') with (ι ↦ inr [] ∥ Π -- ι') at 1.
        2: {
             extensionality x. unfold update in *. apply equal_f with x in H3.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
           }
        now constructor. *)
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
    simpl. apply par_eq in H5 as H5'. subst.
    inversion H1; subst.
    - simpl. apply par_eq in H6 as H5'. subst.
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
  fst Π ι ι' = sigs ++ s :: sigs' ->
  exists sigs1 sigs2, fst Π' ι ι' = sigs1 ++ s :: sigs' ++ sigs2 /\ 
                      exists sigs1_1, sigs = sigs1_1 ++ sigs1.
Proof.
  intros ? ? ? D. induction D; intros.
  * eexists. exists []. rewrite app_nil_r. split. exact H0.
    exists []. reflexivity.
  * apply not_in_cons in H0 as [H0_1 H0_2].
    inversion H; subst.
    (* Send: potentially puts something at the end *)
    - unfold etherAdd, update in IHD. cbn in IHD.
      destruct (ι =? ι0) eqn:Eq1. destruct (ι'0 =? ι') eqn:Eq2.
      + eqb_to_eq; subst.
        specialize (IHD ι0 ι' sigs s (sigs' ++ [t]) H0_2).
        cbn in *. rewrite H1 in IHD. rewrite <- app_assoc in IHD.
        assert (sigs ++ (s :: sigs') ++ [t] = sigs ++ s :: sigs' ++ [t]). {
          f_equal.
        }
        do 2 rewrite Nat.eqb_refl in IHD.
        apply IHD in H2 as [sigs1 [sigs2 [IHD' IHD'']]].
        rewrite IHD'. exists sigs1. exists ([t] ++ sigs2).
        do 2 f_equal. now rewrite app_assoc.
      + cbn in H1.
        specialize (IHD ι0 ι' sigs s sigs' H0_2).
        rewrite Eq1, Eq2 in IHD.
        eqb_to_eq. subst. rewrite H1 in IHD. apply IHD. reflexivity.
      + cbn in H1.
        specialize (IHD ι0 ι' sigs s sigs' H0_2).
        rewrite Eq1, H1 in IHD. apply IHD. reflexivity.
    (* Arrive: potentially removes something *)
    - cbn in *.
      destruct (ι0 =? ι2) eqn:Eq1.
      + destruct (ι' =? ι) eqn:Eq2.
        ** eqb_to_eq. subst.
           destruct sigs.
           -- unfold etherPop in H0. rewrite H1 in H0. cbn in H0. inversion H0.
              congruence.
           -- unfold etherPop in H0. break_match_hyp. congruence.
              inversion H0. inversion H1. subst. clear H0 H1.
              specialize (IHD ι2 ι sigs s sigs' H0_2).
              unfold update in IHD. do 2 rewrite Nat.eqb_refl in IHD.
              specialize (IHD eq_refl).
              destruct IHD as [sigs1 [sigs2 [Eq1 [sigs1_1 Eq2]]]].
              subst. do 2 eexists. split. eauto. exists (s0 :: sigs1_1).
              simpl. reflexivity.
        ** unfold etherPop in H0. break_match_hyp. congruence.
           inversion H0. subst. eapply IHD in H0_2. apply H0_2.
           unfold update. rewrite Nat.eqb_sym in Eq1. rewrite Eq1.
           rewrite Nat.eqb_sym in Eq2. rewrite Eq2. eqb_to_eq. subst. eauto.
      + unfold etherPop in H0. break_match_hyp. congruence.
        inversion H0. subst. eapply IHD in H0_2. apply H0_2.
        unfold update. rewrite Nat.eqb_sym in Eq1. rewrite Eq1. eauto.
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
            ~In s1 (fst Π ι ι') ->
            ~In s2 (fst Π ι ι') ->
            Π'' -[l]ₙ->* Π''' ->
            ~exists Σ, Π''' -[AArrive ι ι' s2 | ι']ₙ-> Σ.
Proof.
  intros. inv H. inv H0.
  2-3: intuition; try congruence.
  cbn in *.
  (* inversion H13; subst. clear H13. *)
  assert (exists sigs sigs', etherAdd ι ι' s2 (etherAdd ι ι' s1 ether) ι ι' = sigs ++ s1 :: sigs') as [sigs1 [sigs2 H]]. {
    unfold etherAdd, update. do 2 rewrite Nat.eqb_refl.
    exists (ether ι ι'), [s2]. now rewrite <- app_assoc.
  }
  epose proof (no_ether_pop l _ _ H4 _ _ _ _ _ H1 H).
  intro. destruct H8 as [Π''''].
  destruct H0 as [sigs11 [sigs3]].
  clear H1 H4. inv H8.
  2: { intuition; try congruence. }
  destruct H0 as [H0 H0_1].
  cbn in *. unfold etherPop, update in H15. rewrite H0 in H15.
  destruct sigs11; cbn in *. inv H15. congruence.
  cbn in *. inv H15.
  unfold etherAdd, update in H. do 2 rewrite Nat.eqb_refl in H.
  rewrite <- app_assoc in H.
  destruct H0_1. subst.
  simpl in H.
  rewrite <- app_assoc in H.
  now apply in_list_order in H.
Qed.

