(**
  This file contains a number of program pairs which are weakly equivalent.
*)
From CoreErlang.BigStep Require Export WeakEquivalence.

Import ListNotations.

Definition write (s : string) : Expression :=
  (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom s)]).

(* match goal with
| [ H : context [ match ?X with _=>_ end ] |- _] =>
     match type of X with
     | sumbool _ _=>destruct X
     | _=>destruct X eqn:? 
     end 
end *)

Ltac primitive_equivalence_solver :=
match goal with
| [H : Result _ _ _ = Result _ _ _ |- _] => idtac "a"; inversion H; subst
| [H : context [fbs_expr ?x _ _ _ _] |- _] => 
   idtac "b"; destruct x; [inversion H | simpl in H; primitive_equivalence_solver]
end.

Theorem ESeq_eval : forall e1 e2 x env modules own_module id eff id'' res'' eff'',
  fbs_expr (S x) env modules own_module id (ESeq e1 e2) eff = Result id'' res'' eff''
<->
  (exists id' v eff',
  fbs_expr x env modules own_module id e1 eff = Result id' (inl [v]) eff' /\
  fbs_expr x env modules own_module id' e2 eff' = Result id'' res'' eff'') \/ 
  (exists ex, fbs_expr x env modules own_module id e1 eff = Result id'' (inr ex) eff'' /\ inr ex = res'').
Proof.
  split; intros.
  * simpl in H. break_match_singleton.
    - subst. left. eexists. eexists. eexists. split. reflexivity. auto.
    - subst. right. eexists. inversion H. subst. split; reflexivity.
  * destruct H.
    - destruct H, H, H, H. simpl. rewrite H, H0. auto.
    - simpl. destruct H, H. rewrite H. subst. auto.
Qed.

Example weak1 e :
weakly_equivalent_expr valid_modules (ESeq (ESeq (write "a") (write "b")) e)
(                       ESeq (ESeq (write "b") (write "a")) e).
 
Proof.
  split; intros.
  * destruct H0.
    destruct x. inversion H0. simpl in H0.
    destruct x. inversion H0.
    break_match_singleton. subst.

    (*primitive_equivalence_solver. *)
    (*2: { clear H0. primitive_equivalence_solver. }*)
    - remember Heqr as H'. clear HeqH'.
      destruct x; [inversion Heqr | simpl in Heqr].
      destruct x; [inversion Heqr | simpl in Heqr].
      inversion H. unfold get_modfunc in Heqr. destruct H2.
      eapply module_lhs in H2.
      rewrite H2 in Heqr.
      inversion Heqr. subst.
      remember (S (S (S x))) as xx. simpl in H'. 
      eapply effect_extension_expr in H0 as H''. destruct H''. subst.
      eapply effect_irrelevant_expr in H0.
      exists (((eff ++ [(Output, [VLit (Atom "b")])]) ++ [(Output, [VLit (Atom "a")])]) ++ x0).
      split.
      + (* apply fbs_soundness. constructor. eapply eval_seq.
        + apply fbs_expr_correctness with (clock := 6 + x). simpl. reflexivity.
        + apply fbs_expr_correctness with (clock := 6 + x). simpl plus. exact H. *)
        remember (S (S x)) as x2. exists (S (S x2)).
        apply ESeq_eval. left. eexists. eexists. eexists. split.
        rewrite Heqx2. simpl.
        unfold get_modfunc. rewrite H2. reflexivity.
        exact H0.
        (* unfold fbs_expr. cbn delta. (* <- This simpl breaks everything *)
        break_match_goal.
        + rewrite Heqxxx in Heqr0.
          remember (fbs_expr xxx env id0 e eff0) as HHH.
          simpl in Heqr0. inversion Heqr0. subst. rewrite H. auto.
        + rewrite Heqxxx in Heqr0. simpl in Heqr0. inversion Heqr0.
        + rewrite Heqxxx in Heqr0. simpl in Heqr0. inversion Heqr0. *)
      + apply Permutation_app. 2: auto.
        repeat rewrite <- app_assoc. apply Permutation_app_head.
        apply perm_swap.
    - remember Heqr as H'. clear HeqH'.
      destruct x; [inversion Heqr | simpl in Heqr].
      destruct x; [inversion Heqr | simpl in Heqr].
      inversion H. unfold get_modfunc in Heqr.
      destruct H2. eapply module_lhs in H2.
      rewrite H2 in Heqr.
      inversion Heqr. 
  * destruct H0.
    destruct x. inversion H0. simpl in H0.
    destruct x. inversion H0.
    break_match_singleton. subst.
(*     clear H.
    primitive_equivalence_solver. *)
    (*2: { clear H. primitive_equivalence_solver. }*)
    - remember Heqr as H'. clear HeqH'.
      destruct x; [inversion Heqr | simpl in Heqr].
      destruct x; [inversion Heqr | simpl in Heqr].
      inversion H. unfold get_modfunc in Heqr.
      destruct H2. eapply module_lhs in H2.
      rewrite H2 in Heqr.
      inversion Heqr. subst.
      remember (S (S (S x))) as xx. simpl in H'.
      eapply effect_extension_expr in H0 as H''. destruct H''. subst.
      eapply effect_irrelevant_expr in H0.
      exists (((eff ++ [(Output, [VLit (Atom "a")])]) ++ [(Output, [VLit (Atom "b")])]) ++ x0).
      split.
      + (* apply fbs_soundness. constructor. eapply eval_seq.
        + apply fbs_expr_correctness with (clock := 6 + x). simpl. reflexivity.
        + apply fbs_expr_correctness with (clock := 6 + x). simpl plus. exact H. *)
        remember (S (S x)) as x2. exists (S (S x2)).
        apply ESeq_eval. left. eexists. eexists. eexists. split.
        rewrite Heqx2. simpl. unfold get_modfunc. rewrite H2. reflexivity.
        exact H0.
        (* unfold fbs_expr. cbn delta. (* <- This simpl breaks everything *)
        break_match_goal.
        + rewrite Heqxxx in Heqr0.
          remember (fbs_expr xxx env id0 e eff0) as HHH.
          simpl in Heqr0. inversion Heqr0. subst. rewrite H. auto.
        + rewrite Heqxxx in Heqr0. simpl in Heqr0. inversion Heqr0.
        + rewrite Heqxxx in Heqr0. simpl in Heqr0. inversion Heqr0. *)
      + apply Permutation_app. 2: auto.
        repeat rewrite <- app_assoc. apply Permutation_app_head.
        apply perm_swap.
    - remember Heqr as H'. clear HeqH'.
      destruct x; [inversion Heqr | simpl in Heqr].
      destruct x; [inversion Heqr | simpl in Heqr].
      inversion H. unfold get_modfunc in Heqr.
      destruct H2. eapply module_lhs in H2.
      rewrite H2 in Heqr.
      inversion Heqr. 
Qed.

Example weak2 e :
weakly_equivalent_expr valid_modules (ESeq (ESeq (write "a") (write "b")) e)
                       (ESeq (ESeq (write "b") (write "a")) e).
(* TODO: Refactor to valid modules! 
        - With empty_modules pred all proof works.
        - with valid_modules all but the last one. (With natural semantics it will work as well)  
*)

Proof.
  split; intros env modules own_module eff res eff' id1 id2 M H.
  * 
    destruct H.
    destruct x. inversion H. simpl in H.
    destruct x. inversion H. simpl fbs_expr in H at 1.
    destruct x. inversion H. simpl fbs_expr in H at 1.
    destruct x. inversion H. simpl fbs_expr in H at 1.
    remember (S (S (S x))) as xx. simpl in H.
    inversion M. unfold get_modfunc in H.
    destruct H1. eapply module_lhs in H1.
     rewrite H1 in H. 
    eapply effect_extension_expr in H as H'. destruct H'. subst.
    eapply effect_irrelevant_expr in H.
    exists (((eff ++ [(Output, [VLit (Atom "b")])]) ++ [(Output, [VLit (Atom "a")])]) ++ x0).
    split.
    - remember (S (S (S x))) as xxx. exists (S xxx).
      simpl. rewrite Heqxxx at 1. simpl.
      unfold get_modfunc. rewrite H1. 
      exact H.
    - apply Permutation_app. 2: auto.
      repeat rewrite <- app_assoc. apply Permutation_app_head.
      apply perm_swap.
  * 
    destruct H.
    destruct x. inversion H. simpl in H.
    destruct x. inversion H. simpl fbs_expr in H at 1.
    destruct x. inversion H. simpl fbs_expr in H at 1.
    destruct x. inversion H. simpl fbs_expr in H at 1.
    remember (S (S (S x))) as xx. simpl in H. 
    inversion M. unfold get_modfunc in H. 
    destruct H1. eapply module_lhs in H1.
    rewrite H1 in H.
    eapply effect_extension_expr in H as H'. destruct H'. subst.
    eapply effect_irrelevant_expr in H.
    exists (((eff ++ [(Output, [VLit (Atom "a")])]) ++ [(Output, [VLit (Atom "b")])]) ++ x0).
    split.
    - remember (S (S (S x))) as xxx. exists (S xxx).
      simpl. rewrite Heqxxx at 1. simpl.
      unfold get_modfunc.
       rewrite H1. 
      exact H.
    - apply Permutation_app. 2: auto.
      repeat rewrite <- app_assoc. apply Permutation_app_head.
      apply perm_swap.
(** Qed. <- This takes unreasonable amount of time (5-10 minutes) **)

(* The others only would work when natural semantics is ready. (for modules) 
Restart.
  split; intros env modules eff res eff' id1 id2 M H.
  destruct H. 
  *  apply fbs_expr_correctness in H. inversion H. inversion H3; subst.
    - eapply fbs_soundness in H5. destruct H5.
      destruct x0. inversion H0. simpl in H0.
      destruct x0. inversion H0. simpl in H0.
      destruct x0. inversion H0. simpl in H0. inversion H0. subst.
      eapply fbs_soundness in H10 as D. destruct D. eapply effect_extension_expr in H1. 
      destruct H1. subst.
      exists (((eff ++ [(Output, [VLit (Atom "b")])]) ++ [(Output, [VLit (Atom "a")])]) ++ x2). split.
      + apply fbs_soundness.
        eapply eval_seq. unfold write. solve.
        simpl. eapply fbs_soundness in H10 as D. destruct D.
        eapply effect_irrelevant_expr in H1. apply fbs_expr_correctness in H1. exact H1.
      + apply Permutation_app. 2: auto. repeat rewrite <- app_assoc.
        apply Permutation_app_head. apply perm_swap.
    - inversion H9; subst.
      + inversion H14. subst. pose (H8 0 (Nat.lt_0_succ _)).
        simpl length in *. repeat unfold_list_once.
        inversion H0. inversion H1. inversion H2. subst.
        inversion e0. simpl in H6, H10, H11. subst.
        inversion H19; subst.
        ** simpl length in *. repeat unfold_list_once.
           inversion H3. inversion H4. inversion H5. subst.
           pose (H16 0 (Nat.lt_0_succ _)). inversion e1.
           simpl in H11, H17, H14. subst. inversion H22.
        ** inversion H10. unfold_list_once. simpl length in *.
           repeat unfold_list_once. inversion H23. inversion H4.
      + inversion H18; subst.
        ** simpl length in *. repeat unfold_list_once.
           inversion H0. inversion H1. inversion H2. subst.
           pose (H8 0 (Nat.lt_0_succ _)). inversion e0.
           simpl in H10, H5, H7. subst. inversion H14.
        ** inversion H4. unfold_list_once. simpl length in *.
           repeat unfold_list_once. inversion H15. inversion H1.
  * destruct H.
    inversion M. rewrite H0 in H. 
    apply fbs_expr_correctness in H. inversion H. inversion H3; subst.
    - eapply fbs_soundness in H5. destruct H5.
      destruct x0. inversion H0. simpl in H0.
      destruct x0. inversion H0. simpl in H0.
      destruct x0. inversion H0. simpl in H0. inversion H0. subst.
      eapply fbs_soundness in H10 as D. destruct D. eapply effect_extension_expr in H1. 
      destruct H1. subst.
      exists (((eff ++ [(Output, [VLit (Atom "a")])]) ++ [(Output, [VLit (Atom "b")])]) ++ x2). split.
      + apply fbs_soundness.
        eapply eval_seq. unfold write. solve.
        simpl. eapply fbs_soundness in H10 as D. destruct D.
        eapply effect_irrelevant_expr in H1. apply fbs_expr_correctness in H1. exact H1.
      + apply Permutation_app. 2: auto. repeat rewrite <- app_assoc.
        apply Permutation_app_head. apply perm_swap.
    - inversion H9; subst.
      + inversion H14. subst. pose (H8 0 (Nat.lt_0_succ _)).
        simpl length in *. repeat unfold_list_once.
        inversion H0. inversion H1. inversion H2. subst.
        inversion e0. simpl in H6, H10, H11. subst.
        inversion H19; subst.
        ** simpl length in *. repeat unfold_list_once.
           inversion H3. inversion H4. inversion H5. subst.
           pose (H16 0 (Nat.lt_0_succ _)). inversion e1.
           simpl in H11, H17, H14. subst. inversion H22.
        ** inversion H10. unfold_list_once. simpl length in *.
           repeat unfold_list_once. inversion H23. inversion H4.
      + inversion H18; subst.
        ** simpl length in *. repeat unfold_list_once.
           inversion H0. inversion H1. inversion H2. subst.
           pose (H8 0 (Nat.lt_0_succ _)). inversion e0.
           simpl in H5, H10, H7. subst. inversion H14.
        ** inversion H4. unfold_list_once. simpl length in *.
           repeat unfold_list_once. inversion H15. inversion H1.
(** Qed. <- it's quicker, only 3-4 seconds **)(*TODO*)
Restart.
   apply (ESeq_weak_congr empty_modules) . 2: apply weakly_equivalent_expr_refl.
  split; intros env modules eff res eff' id1 id2 E H; inversion E; rewrite H0 in *.
  * destruct H.
    destruct x; [inversion H | simpl in H].
    destruct x; [inversion H | simpl in H].
    destruct x; [inversion H | simpl in H].
    inversion H. subst.
    exists ((eff ++ [(Output, [VLit (Atom "b")])]) ++ [(Output, [VLit (Atom "a")])]).
    split. exists 7. simpl. auto.
    repeat rewrite <- app_assoc.
    apply Permutation_app_head. apply perm_swap.
  * destruct H.
    destruct x; [inversion H | simpl in H].
    destruct x; [inversion H | simpl in H].
    destruct x; [inversion H | simpl in H].
    inversion H. subst.
    exists ((eff ++ [(Output, [VLit (Atom "a")])]) ++ [(Output, [VLit (Atom "b")])]).
    split. exists 7. simpl. auto.
    repeat rewrite <- app_assoc.
    apply Permutation_app_head. apply perm_swap.
(** Qed.  <- Quickest version, this is the best way, if it's usable **)
*)
Qed.
