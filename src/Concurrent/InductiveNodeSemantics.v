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
  * inv H8.
    - intuition; try congruence.
    - apply par_eq in H5 as H5'. subst.
      eapply process_local_determinism in H3. 2: exact H16. subst.
      f_equal. rewrite H in H10. inv H10.
      rewrite H2 in H15. inv H15.
      extensionality ι''. apply equal_f with ι'' in H5. unfold update in *.
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
    exfalso. inv H11. inv H1. inv H13. now cbn in *.
(*   * apply par_eq in H4 as H4'. subst.
    inv H1. *)
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
        ** intro. apply isUsedEther_etherAdd_rev in H0. congruence.
           cbn in Spawns. intro. subst. now apply Spawns.
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
        constructor; auto.
        now apply etherPop_greater.
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
        ** intro. eapply isUsedEther_etherPop_rev in H. 2: eassumption. congruence.
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
  * inv H4.
    - exists (etherAdd ι'0 ι'1 t ether, ι'0 ↦ p'0 ∥
                                        ι' ↦ inl ([], r, emptyBox, [], false) ∥
                                        ι ↦ p' ∥ Π).
      split.
      + replace (ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) with 
                (ι'0 ↦ p0 ∥ ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H8.
             break_match_goal; subst;
             break_match_goal; subst; auto.
             all: break_match_hyp; eqb_to_eq; subst; auto; try congruence.
             break_match_hyp; congruence.
           }
        constructor; now eauto.
      + assert (ι'0 <> ι'). {
          unfold update in H0. break_match_hyp; try congruence.
          apply equal_f with ι' in H8. unfold update in H8.
          do 2 break_match_hyp; try congruence; now eqb_to_eq.
        }
        rewrite update_swap with (ι' := ι'). rewrite update_swap with (ι' := ι).
        2-3: now auto.
        replace (ι'0 ↦ p'0 ∥ prs) with
          (ι ↦ p ∥ ι'0 ↦ p'0 ∥ Π) at 1.
        2: {
             extensionality x. unfold update in *. apply equal_f with x in H8.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
           }
         eapply n_spawn; eauto.
         ** clear -H0 H8. unfold update in *. apply equal_f with ι' in H8.
            repeat break_match_hyp; try congruence.
         ** intro Q. apply isUsedEther_etherAdd_rev in Q. congruence.
            cbn in Spawns. intro. subst. now apply Spawns.
    - exists (ether', ι'0 ↦ p'0 ∥ ι' ↦ inl ([], r, emptyBox, [], false) 
                          ∥ ι ↦ p' ∥ Π ).
      split.
      + replace (ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) with 
                (ι'0 ↦ p0 ∥ ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H7.
             break_match_goal; subst;
             break_match_goal; subst; auto.
             all: break_match_hyp; eqb_to_eq; subst; auto; try congruence.
             break_match_hyp; congruence.
           }
        constructor; auto.
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
         ** intro Q. eapply isUsedEther_etherPop_rev in H8. 2: eassumption. congruence.
    - exists (ether, ι'0 ↦ p'0 ∥ ι' ↦ inl ([], r, emptyBox, [], false)
                               ∥ ι ↦ p' ∥ Π).
      split.
      + replace (ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) with 
                (ι'0 ↦ p0 ∥ ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H7.
             break_match_goal; subst;
             break_match_goal; subst; auto.
             all: break_match_hyp; eqb_to_eq; subst; auto; try congruence.
             break_match_hyp; congruence.
           }
        now constructor.
      + assert (ι'0 <> ι'). {
          unfold update in H0. break_match_hyp; try congruence.
          apply equal_f with ι' in H7. unfold update in H7.
          do 2 break_match_hyp; try congruence; now eqb_to_eq.
        }
        rewrite update_swap with (ι' := ι'). rewrite update_swap with (ι' := ι).
        2-3: now auto.
        replace (ι'0 ↦ p'0 ∥ Π0) with
          (ι ↦ p ∥ ι'0 ↦ p'0 ∥ Π) at 1.
        2: {
             extensionality x. unfold update in *. apply equal_f with x in H7.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
           }
         eapply n_spawn; eauto.
         ** clear -H0 H7. unfold update in *. apply equal_f with ι' in H7.
            repeat break_match_hyp; try congruence.
    - (** cannot be sure to generate different spawn PID-s *)
      exists (ether, ι'1 ↦ inl ([], r0, emptyBox, [], false) ∥ ι'0 ↦ p'0 ∥ ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π).
      split.
      + replace (ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) with
                (ι'0 ↦ p0 ∥ ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) at 1.
        2: { extensionality x. unfold update in *. apply equal_f with x in H7.
             break_match_goal; subst;
             break_match_goal; subst; auto.
             all: break_match_hyp; eqb_to_eq; subst; auto; try congruence.
             repeat break_match_hyp; try congruence.
           }
        eapply n_spawn; try eassumption.
        clear -H9 H7 H0 Spawns. unfold update in *. cbn in *.
        repeat break_match_goal; eqb_to_eq; subst; try congruence.
        ** break_match_hyp; eqb_to_eq; try congruence.
           apply equal_f with ι'1 in H7.
           break_match_hyp; eqb_to_eq; try congruence.
           break_match_hyp; eqb_to_eq; try congruence.
        ** break_match_hyp; eqb_to_eq; try congruence.
           apply equal_f with ι'1 in H7.
           break_match_hyp; eqb_to_eq; try congruence.
           break_match_hyp; eqb_to_eq; try congruence.
      + assert (ι'0 <> ι' /\ ι'1 <> ι /\ ι'1 <> ι'). {
          unfold update in H0, H8. break_match_hyp; try congruence.
          apply equal_f with ι' in H7 as H7'.
          apply equal_f with ι'1 in H7 as H7''.
          apply equal_f with ι in H7. unfold update in *.
          do 2 break_match_hyp; try congruence; eqb_to_eq.
          split; auto.
          all: repeat break_match_hyp; eqb_to_eq; try congruence; subst; eqb_to_eq.
        }
        rewrite update_swap with (ι' := ι'). rewrite update_swap with (ι' := ι).
        rewrite update_swap with (ι' := ι'). rewrite update_swap with (ι' := ι).
        2-5: try auto.
        replace (ι'1 ↦ inl ([], r0, emptyBox, [], false) ∥ ι'0 ↦ p'0 ∥ Π0) with
          (ι ↦ p ∥ ι'1 ↦ inl ([], r0, emptyBox, [], false) ∥ ι'0 ↦ p'0 ∥ Π) at 1.
        2: {
             extensionality x. unfold update in *. apply equal_f with x in H7.
             break_match_goal; subst.
             all: repeat break_match_goal; subst; eqb_to_eq; try congruence; auto.
             repeat break_match_hyp; eqb_to_eq; subst; try congruence.
           }
         eapply n_spawn; eauto.
         ** unfold update in *. destruct_hyps.
            repeat break_match_goal; eqb_to_eq; try congruence.
         ** apply H4.
         ** apply H4.
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

Lemma no_spawn_included :
  forall l n n', n -[l]ₙ->* n' ->
    forall ι, ~In ι (PIDsOf spawnPIDOf l) ->
      n.2 ι = None <-> n'.2 ι = None.
Proof.
  intros. induction H; auto.
  split; auto.
  unfold PIDsOf in H0; simpl in H0. fold (PIDsOf spawnPIDOf l) in H0.
  apply not_in_app in H0 as [H0_1 H0_2]. apply IHclosureNodeSem in H0_2.
  clear IHclosureNodeSem H1. inv H; simpl in *.
  1-3: unfold update in *; break_match_goal; destruct H0_2; split; intro F; auto; try congruence.
  1: now apply H1 in F.
  1: now apply H2 in F.
  1: destruct a; destruct H1 as [ | [ | ] ]; try congruence; simpl in *;
     now apply H2 in F.
  * clear H2 H3 H0. split; intro;
    unfold update in *; repeat break_match_hyp; eqb_to_eq; subst; try congruence.
    - exfalso. apply H0_1. now left.
    - now apply H0_2 in H.
    - break_match_goal; eqb_to_eq; congruence.
    - now apply H0_2 in H.
    - now apply H0_2 in H.
Qed.

Lemma no_spawn_included_2 :
  forall l n n', n -[l]ₙ->* n' ->
    forall ι, n'.2 ι = None ->
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
      2: { simpl in *. unfold update in *. break_match_goal; congruence. }
      unfold PIDsOf. rewrite flat_map_app. apply app_not_in.
      1-2: fold (PIDsOf spawnPIDOf l'); simpl; auto.
    - eapply H with (ι := ι) in D1. 2: lia.
      2: { simpl in *. unfold update in *. break_match_goal; congruence. }
      unfold PIDsOf. rewrite flat_map_app. apply app_not_in.
      1-2: fold (PIDsOf spawnPIDOf l'); simpl; auto.
    - eapply H with (ι := ι) in D1. 2: lia.
      2: { simpl in *. unfold update in *. break_match_goal; congruence. }
      unfold PIDsOf. rewrite flat_map_app. apply app_not_in.
      1-2: fold (PIDsOf spawnPIDOf l'); simpl; auto.
      destruct a; simpl; auto.
      destruct H2 as [? | [? | ?]]; congruence.
    - unfold PIDsOf. rewrite flat_map_app. apply app_not_in.
      1-2: fold (PIDsOf spawnPIDOf l'); simpl.
      + eapply H. lia. eassumption.
        simpl in *. clear H5. unfold update in *.
        repeat break_match_hyp; try break_match_goal; eqb_to_eq; try congruence.
      + intro. destruct H4. 2: auto. subst.
        simpl in H1. unfold update in H1. rewrite Nat.eqb_refl in H1.
        congruence.
Qed.

Lemma processes_dont_die_None :
  forall l n n', n -[l]ₙ->* n' ->
    forall ι, n'.2 ι = None -> n.2 ι = None.
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
    1-3: unfold update in *; simpl in *; break_match_goal; eqb_to_eq; try congruence; auto.
    clear -H3 H1. simpl in *.
    unfold update in *.
    repeat break_match_hyp; eqb_to_eq; try congruence; auto.
Qed.



Lemma processes_dont_die :
  forall n n' l, n -[l]ₙ->* n' ->
    forall ι, n.2 ι <> None -> n'.2 ι <> None.
Proof.
  intros. induction H; auto.
  apply IHclosureNodeSem. clear IHclosureNodeSem H1. inv H.
  all: simpl in *.
  1-3: unfold update in *; break_match_hyp; auto; congruence.
  * unfold update in *. clear H4.
    repeat break_match_hyp; auto; eqb_to_eq; subst; try congruence.
    - break_match_goal; congruence.
    - break_match_goal; congruence.
Qed.


Corollary processes_dont_die_Some :
  forall n n' l, n -[l]ₙ->* n' ->
    forall ι p, n.2 ι = Some p -> exists p', n'.2 ι = Some p'.
Proof.
  intros.
  epose proof (processes_dont_die _ _ _ H ι _).
  Unshelve. 2: { intro D. rewrite D in H0. congruence. }
  destruct (n'.2 ι). eexists. reflexivity.
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
  forall ι ι', Forall SIGCLOSED (ether ι ι').

Lemma ether_wf_etherAdd :
  forall ι ι' t ether,
    SIGCLOSED t ->
    ether_wf ether ->
      ether_wf (etherAdd ι ι' t ether).
Proof.
  intros. unfold etherAdd, update. intros i1 i2.
  specialize (H0 i1 i2).
  repeat break_match_goal; eqb_to_eq; subst; auto.
  apply Forall_app; split; auto.
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
  * unfold etherPop in H0. break_match_hyp. congruence.
    inv H0. simpl in H1. unfold update, ether_wf in *.
    intros. specialize (H1 ι0 ι'). clear -H1 Heql0.
    repeat break_match_goal; eqb_to_eq; subst; auto.
    rewrite Heql0 in H1. now inv H1.
Qed.

Lemma no_spawn_on_Some :
  forall n n' l, n -[l]ₙ->* n' ->
    forall ι, n.2 ι <> None ->
      ~In ι (PIDsOf spawnPIDOf l).
Proof.
  intros n n' l H. induction H; intros; simpl; auto.
  intro Ha. inv H; simpl in *.
  * assert ((ι ↦ p' ∥ prs) ι0 <> None). {
      unfold update in *. break_match_goal; auto. congruence.
    }
    now apply IHclosureNodeSem in H.
  * assert ((ι ↦ p' ∥ prs) ι0 <> None). {
      unfold update in *. break_match_goal; auto. congruence.
    }
    now apply IHclosureNodeSem in H.
  * assert ((ι ↦ p' ∥ Π) ι0 <> None). {
      unfold update in *. break_match_goal; auto. congruence.
    }
    apply IHclosureNodeSem in H. destruct a; auto.
    destruct H3 as [? | [? | ?]]; congruence.
  * clear H5.
    destruct Ha.
    - subst. congruence.
    - assert ((ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) ι0 <> None). {
      unfold update in *. break_match_goal; auto. congruence.
      eqb_to_eq. subst. break_match_hyp; try congruence.
      eqb_to_eq. break_match_hyp; try congruence.
      eqb_to_eq. subst.
      apply IHclosureNodeSem in H; auto.
      repeat break_match_goal; try congruence.
    }
    apply IHclosureNodeSem in H; auto.
Qed.



(* NOTE!!!!!!!!
   This depends on LEM!
   TODO: reformalise ethers with maps!
*)
From Coq Require Import Logic.Classical.
Proposition isUsedEther_dec :
  forall ι ether, isUsedEther ι ether \/ ~isUsedEther ι ether.
Proof.
  intros. apply classic.
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
    assert (n.2 ι <> None). {
      subst n. cbn. unfold update. rewrite Nat.eqb_refl. congruence.
    }
    eapply no_spawn_on_Some in H0. 2: eassumption. congruence.
  * destruct a; simpl in *; try now apply IHclosureNodeSem in Ha.
    destruct H3 as [? | [? | ?]]; congruence.
  * clear H5. destruct Ha. congruence.
    apply IHclosureNodeSem in H; auto.
Qed.


-------------------------

Definition isUntaken (ι : PID) (n : Node) : Prop :=
  n.2 ι = None /\ isUsedEther ι n.1.

Theorem compatibility_of_reduction :
  forall n n' a ι, n -[a | ι]ₙ-> n' ->
    forall ι, isUntaken ι n ->
      (isUntaken ι n' \/ spawnPIDOf a = Some ι /\ exists p, n'.2 ι = Some p).
Proof.
  intros. inv H.
  * left. destruct H0. split.
    - simpl in *. unfold update in *; now break_match_goal.
    - simpl in *. now apply isUsedEther_etherAdd.
  * left. destruct H0. split.
    - simpl in *. unfold update in *; now break_match_goal.
    - simpl in *. eapply isUsedEther_etherPop in H1 as [H1 | H1].
      + eassumption.
      + subst. unfold update in H. now rewrite Nat.eqb_refl in H.
      + assumption.
  * left. destruct H0. split.
    - simpl in *. unfold update in *; now break_match_goal.
    - assumption.
  * clear H3 H4 H1. destruct H0. simpl in *.
    destruct (Nat.eq_dec ι0 ι').
    - subst. right. split; auto.
      eexists. unfold update. rewrite Nat.eqb_refl. reflexivity.
    - left. split.
      + simpl. unfold update in *.
        repeat break_match_goal; eqb_to_eq; subst; try congruence.
      + simpl. assumption.
Qed.


Corollary compatibility_of_reductions :
   forall n n' l, n -[l]ₙ->* n' ->
    forall ι, isUntaken ι n ->
      (isUntaken ι n' \/ In ι (PIDsOf spawnPIDOf l) /\ exists p, n'.2 ι = Some p).
Proof.
  intros n n' l H. induction H; intros; auto.
  apply (compatibility_of_reduction _ _ _ _ H) in H1 as [H1 | [H1_1 H1_2]].
  * apply IHclosureNodeSem in H1. destruct H1 as [? | [? ?]]; auto.
    right. simpl. break_match_goal; simpl; auto.
  * right. simpl. rewrite H1_1. split. now constructor.
    destruct H1_2. eapply processes_dont_die_Some in H1. eassumption.
    eauto.
Qed.



Theorem compatibility_of_reduction_rev :
  forall n n' a ι, n -[a | ι]ₙ-> n' ->
    forall ι,
      isUntaken ι n' ->
      isUntaken ι n \/
      (sendPIDOf a = Some ι /\ ~isUsedEther ι n.1 /\ n.2 ι = None).
(*       (spawnPIDOf a = Some ι /\ n.2 ι = None). *)
Proof.
  intros. inv H.
  * destruct H0.
    destruct (Nat.eq_dec ι' ι0); simpl; subst.
    - simpl in *.
      destruct (isUsedEther_dec ι0 ether).
      + left. split. simpl. unfold update in *; now break_match_goal.
        now simpl.
      + right. split; simpl; auto.
        split; auto. unfold update in *; now break_match_goal.
    - left. split.
      + simpl in *. unfold update in *; now break_match_goal.
      + simpl in *. eapply isUsedEther_etherAdd_rev. eassumption. assumption.
  * destruct H0. left. split.
    - simpl in *. unfold update in *; now break_match_goal.
    - simpl in *. eapply isUsedEther_etherPop_rev; eassumption.
  * destruct H0. left. split.
    - simpl in *. unfold update in *; now break_match_goal.
    - assumption.
  * clear H3 H4 H1. destruct H0. simpl in *.
    destruct (Nat.eq_dec ι0 ι').
    - subst. left. split.
      + now simpl.
      + now simpl.
    - left. split.
      + simpl. unfold update in *.
        repeat break_match_hyp; eqb_to_eq; subst; try congruence.
      + simpl. assumption.
Qed.

Corollary compatibility_of_reductions_rev :
   forall l n n', n -[l]ₙ->* n' ->
    forall ι,
      isUntaken ι n' ->
      isUntaken ι n \/
      (In ι (PIDsOf sendPIDOf l) /\ ~isUsedEther ι n.1 /\ n.2 ι = None).
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
      + unfold update in *; break_match_goal; auto. congruence.
      + now apply isUsedEther_etherAdd.
    - apply IHclosureNodeSem in Hin. assumption.
      destruct H1. split; simpl in *.
      + unfold update in *; break_match_goal; auto. congruence.
      + eapply isUsedEther_etherPop in H2 as [H2 | H2]; try eassumption.
        subst. unfold update in H. now rewrite Nat.eqb_refl in H.
    - assert (isUntaken ι0 (ether, ι ↦ p' ∥ Π)). {
        destruct H1; split; auto.
        simpl in *. unfold update in *; break_match_goal; auto. congruence.
      }
      apply IHclosureNodeSem in H. apply H.
      destruct a; auto. destruct H3 as [? | [? | ?]]; congruence.
    - destruct Hin.
      + clear H5. subst. destruct H1. simpl in *. congruence.
      + clear H5. assert (isUntaken ι0 (ether, ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π)). {
          destruct H1; split; auto.
          simpl in *. unfold update in *.
          repeat break_match_goal; auto; try congruence.
          eqb_to_eq. subst. break_match_hyp; try congruence.
        }
        apply IHclosureNodeSem in H5. now apply H5.
Qed.

Lemma included_spawn :
  forall (l : list (Action * PID)) (n n' : Node),
  n -[ l ]ₙ->* n' ->
    forall ι : PID, In ι (PIDsOf spawnPIDOf l) ->
      n'.2 ι <> None.
Proof.
  intros l n n' H. induction H; intros.
  * intro. inv H.
  * inv H; simpl in *; try assumption.
    1-3: apply IHclosureNodeSem; try assumption.
    - firstorder; now subst.
    - clear H5. destruct H1. 2: apply IHclosureNodeSem; try assumption.
      subst. apply processes_dont_die with (ι := ι0) in H0; auto.
      cbn. unfold update. now rewrite Nat.eqb_refl.
Qed.

Lemma isUsedEther_after_send :
  forall n n' l, n -[l]ₙ->* n' ->
    forall ι,
      In ι (PIDsOf sendPIDOf l) ->
      ~In ι (PIDsOf spawnPIDOf l) ->
      n.2 ι = None ->
      isUsedEther ι n'.1.
Proof.
  intros n n' l H. induction H; intros; simpl; auto.
  * inv H.
  * unfold PIDsOf in H2. simpl in H2. apply not_in_app in H2.
    fold (PIDsOf spawnPIDOf l) in *. destruct H2. inv H.
    - simpl in *. inv H1.
      + apply compatibility_of_reductions with (ι := ι0) in H0.
        2: {
          split; simpl. unfold update in *; break_match_goal; congruence.
          unfold isUsedEther. exists ι. unfold etherAdd, update.
          do 2 rewrite Nat.eqb_refl. now destruct (ether ι ι0).
        }
        destruct H0. 1: apply H.
        destruct H. congruence.
      + apply IHclosureNodeSem; auto.
        unfold update in *; break_match_goal; congruence.
    - simpl in *. apply IHclosureNodeSem; auto.
      unfold update in *; break_match_goal; congruence.
    - simpl in *. apply IHclosureNodeSem; auto.
      2: unfold update in *; break_match_goal; congruence.
      destruct a; simpl in *; auto.
      destruct H6 as [? | [? | ?]]; congruence.
    - simpl in *. clear H8.
      apply IHclosureNodeSem; auto.
      unfold update in *; repeat break_match_goal; eqb_to_eq; subst; try congruence.
      break_match_hyp; try congruence. eqb_to_eq.
      lia.
 (* ι0 <> ι0 *)
Qed.

Definition comp_pool (Π₁ Π₂ : ProcessPool) : ProcessPool :=
  fun ι =>
    match Π₁ ι with
    | Some p => Some p
    | None => Π₂ ι
    end.

Definition comp_ether (e1 e2 : Ether) : Ether :=
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
Abort.

Theorem etherPop_comp :
  forall eth1 eth2 ether' (ι1 ι2 : PID) (s : Signal),
    etherPop ι1 ι2 eth1 = Some (s, ether') ->
    etherPop ι1 ι2 (comp_ether eth1 eth2) = Some (s, comp_ether ether' eth2).
Proof.

Abort.

Theorem par_comp_assoc_pool (Π1 Π2 : ProcessPool) (ι : PID) (p : Process) :
  (ι ↦ p ∥ Π1) ∥∥ Π2 = ι ↦ p ∥ (Π1 ∥∥ Π2).
Proof.
  unfold comp_pool, update. extensionality ι'.
  repeat break_match_goal; auto; congruence.
Qed.

(* Theorem par_comp_assoc (eth1 eth2 : Ether) (Π1 Π2 : ProcessPool) (ι : PID) (p : Process) :
  (eth1, ι ↦ p ∥ Π1) ∥∥ (eth2, Π2) = (comp_Ether eth1 eth2, ι ↦ p ∥ (comp_ProcessPool Π1 Π2)).
Proof.

Abort. *)


Lemma not_isUsedEther_comp :
  forall eth1 eth2 ι, ~isUsedEther ι eth1 -> ~isUsedEther ι eth2 ->
    ~isUsedEther ι (comp_ether eth1 eth2).
Proof.
  intros. unfold isUsedEther in *.
  firstorder. simpl in *. intro.
  destruct H1. apply (H x). intro.
  apply (H0 x). intro. unfold comp_ether in H1. rewrite H2, H3 in H1.
  simpl in H1. congruence.
Qed.

Theorem reduction_is_preserved_by_comp :
  forall Π Π' ether ether' a ι,
    (ether, Π) -[a | ι]ₙ-> (ether', Π') ->
    forall (Π2 : ProcessPool),
      (forall ι, spawnPIDOf a = Some ι -> Π2 ι = None) ->
      (ether, Π ∥∥ Π2) -[a | ι]ₙ-> (ether', Π' ∥∥ Π2).
Proof.
  intros. inv H; cbn.
  * do 2 rewrite par_comp_assoc_pool. now apply n_send.
  * do 2 rewrite par_comp_assoc_pool. now apply n_arrive.
  * do 2 rewrite par_comp_assoc_pool. now apply n_other.
  * do 3 rewrite par_comp_assoc_pool. econstructor; eauto.
    unfold comp_pool, update in *. break_match_hyp. congruence.
    rewrite H6. apply H0. reflexivity.
Qed.

Corollary reductions_are_preserved_by_comp: 
  forall Π Π' ether ether' l,
    (ether, Π) -[l]ₙ->* (ether', Π') ->
    forall (Π2 : ProcessPool),
      (forall ι, In ι (PIDsOf spawnPIDOf l) -> Π2 ι = None) ->
      (ether, Π ∥∥ Π2) -[l]ₙ->* (ether', Π' ∥∥ Π2).
Proof.
  intros ??????. dependent induction H; intros.
  * constructor.
  * destruct n'. specialize (IHclosureNodeSem _ _ _ _ JMeq_refl JMeq_refl).
    eapply reduction_is_preserved_by_comp with (Π2 := Π2) in H.
    2: { intros. apply H1. cbn. apply in_app_iff. left. rewrite H2. now left. }
    econstructor; eauto.
    apply IHclosureNodeSem.
    intros. apply H1. cbn. apply in_app_iff. now right.
Qed.

