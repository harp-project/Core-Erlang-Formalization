(**
  This file contains a number of proved properties of the big-step semantics.
*)

From CoreErlang.BigStep Require Export DeterminismHelpers.

(** Proofs about the semantics *)

Import ListNotations.
(* Import Coq.Init.Logic. *)

Proposition length_split_eq {A B : Type} (l : list (A * B)) :
  length (fst (split l)) = length (snd (split l)).
Proof.
  rewrite split_length_l, split_length_r. auto.
Qed.

Proposition split_eq {A B : Type} {l l0 : list (A * B)} : 
  split l = split l0 <-> l = l0.
Proof.
  split; generalize dependent l0.
  * induction l; intros.
    - inversion H. destruct l0.
      + reflexivity.
      + inversion H1. destruct p. destruct (split l0). inversion H2.
    - destruct l0.
      + inversion H. destruct a. destruct (split l). inversion H1.
      + inversion H. subst. assert (split l = split l0). {
        destruct a, p. destruct (split l), (split l0). inversion H1. subst. auto.
        }
        pose (IH := IHl l0 H0).
        destruct a, p. destruct (split l), (split l0) in H1. inversion H1. rewrite IH. auto.
  * intros. rewrite H. reflexivity.
Qed.

Theorem determinism :
(
  forall {env modules own_module id e eff id' v1 eff'},
  |env, modules, own_module, id, e, eff| -e> | id', v1, eff'|
->
  (forall v2 eff'' id'', |env, modules, own_module, id, e, eff| -e> |id'', v2, eff''| -> v1 = v2 /\ eff' = eff''
      /\ id' = id'')
).
Proof.
  intros env modules own_module id e eff id' v1 eff' H. induction H; intros.

  (* VALUE LIST *)
  * inversion H6; subst.
    - pose (P := explist_equality _ _ _ _ _ _ _ H3 H11 H8 H9 H H0 H1 H10).
      destruct P. destruct H5. subst. auto.
    - pose (P := explist_prefix_eq _ _ _ _ _ _ _ _ _ _ _ H H0 H10 H8 H1 H11 H3 H12 H17).
      inversion P.

  (* VALUE LIST EXCEPTION *)
  * inversion H6; subst.
    - epose (P := explist_prefix_eq_rev _ _ _ _ _ _ _ _ _ _ _ H4 H11 IHeval_expr H H1 H8 H9 H10 H2).
      inversion P.
    - epose (P := exception_equality _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H4 H17 IHeval_expr H12
        _ _ _ _ _ _ _ _).
      destruct P, H7, H9. subst. auto.
      Unshelve.
      all: auto.

(*   (* SINGLE EXPRESSION *)
  * apply H. inversion H0. auto. *)

  (* NIL *)
  * inversion H. auto.

  (* LIT *)
  * inversion H. auto.

  (* VAR *)
  * inversion H0. subst. rewrite H6 in H. inversion H. auto.

  (* FUNID *)
  * inversion H0.
    - subst. rewrite H6 in H. inversion H. auto.
    - congruence.

  (* FUNID WITH MODULE *)
  * inversion H3.
    - subst. congruence. 
    - subst. rewrite H6 in H0. inversion H0. subst. auto.

  (* FUN *)
  * inversion H. auto.

  (* TUPLE *)
  * inversion H6; subst.
    - pose (P := explist_equality _ _ _ _ _ _ _ H3 H11 H8 H9 H H0 H1 H10).
      destruct P, H5. subst. auto.
    - pose (P := explist_prefix_eq _ _ _ _ _ _ _ _ _ _ _ H H0 H10 H8 H1 H11 H3 H12 H17).
      inversion P.

  (* CONS *)
  * inversion H1; subst.
    - apply IHeval_expr1 in H8. destruct H8, H3. inversion H2. subst.
      apply IHeval_expr2 in H13. destruct H13, H4. inversion H3. subst. auto.
    - apply IHeval_expr1 in H12. destruct H12. congruence.
    - apply IHeval_expr1 in H8. destruct H8, H3. inversion H2. subst.
      apply IHeval_expr2 in H13. destruct H13, H4. congruence.

  (* CASE *)
  * inversion H6; subst.
    - apply IHeval_expr1 in H9. destruct H9, H8. inversion H7. subst.
      epose proof (P := index_case_equality _ _ _ _ _ _ _ _ _ _ _ _ H3 H12 H1 H11 H17 H4 _ _ IHeval_expr2). subst. rewrite H1 in H11. inversion H11. subst.
      apply IHeval_expr2 in H17. apply IHeval_expr3 in H22. auto.
      Unshelve. all: compute; congruence.
    - apply IHeval_expr1 in H17. destruct H17. congruence.
    - apply IHeval_expr1 in H13. destruct H13, H8. inversion H7. subst.
      pose (P := H18 i H0 _ _ _ H1).
      apply IHeval_expr2 in P. destruct P. inversion H8.
    - apply IHeval_expr1 in H9. destruct H9, H8. inversion H7. subst.
      epose proof (P := index_case_equality _ _ _ _ _ _ _ _ _ _ _ _ H3 H16 H1 H11 H21 H4 _ _ IHeval_expr2).
      subst. rewrite H1 in H11. inversion H11. subst.
      apply IHeval_expr2 in H21 as [? ?]. congruence.
      Unshelve. all: compute; congruence.
  (* CALL *)
   * inversion H9; subst.
    - apply IHeval_expr1 in H16. destruct H16, H10. inversion H8. subst.
      apply IHeval_expr2 in H17. destruct H17, H11. inversion H10. subst. 
      pose (P := explist_equality _ _ _ _ _ _ _ H5 H18 H13 H14 H H0 H1 H15).
      destruct P, H12. subst. rewrite H7 in H28. inversion H28. auto.
    - apply IHeval_expr1 in H16. destruct H16 , H10. inversion H8. subst.
      apply IHeval_expr2 in H17. destruct H17  , H11. inversion H10. subst.
      congruence.
    - apply IHeval_expr1 in H17. destruct H17  , H10. destruct H8. subst.
      apply IHeval_expr2 in H22. destruct H22  , H10. destruct H8. subst.
      pose (P := explist_prefix_eq _ _ _ _ _ _ _ _ _ _ _ H H0 H15 H13 H1 H16 H5 H27 H28).
      inversion P.
    - apply IHeval_expr1 in H21. destruct H21. congruence.  
    - apply IHeval_expr1 in H21. destruct H21, H10. inversion H8. subst.
      apply IHeval_expr2 in H22. destruct H22. congruence.
    - apply IHeval_expr1 in H16. destruct H16, H10. inversion H8. subst. congruence.  
    - apply IHeval_expr1 in H16. destruct H16, H10. inversion H8. subst.
      apply IHeval_expr2 in H17. destruct H17, H11. inversion H10. subst. congruence.

  * inversion H8; subst.
    - apply IHeval_expr1 in H15. destruct H15, H10. inversion H9. subst.
      apply IHeval_expr2 in H16. destruct H16, H11. inversion H10. subst. 
      pose (P := explist_equality _ _ _ _ _ _ _ H5 H17 H12 H13 H H0 H1 H14).
      destruct P , H15. subst. congruence.
    - apply IHeval_expr1 in H15. destruct H15, H10. inversion H9. subst.
      apply IHeval_expr2 in H16. destruct H16, H11. inversion H10. subst. 
      pose (P := explist_equality _ _ _ _ _ _ _ H5 H21 H12 H13 H H0 H1 H14).
      destruct P , H15. subst. rewrite H6 in H26. inversion H26. subst.
      apply IHeval_expr3 in H27. destruct H27, H15. inversion H11. subst. auto. 

    - apply IHeval_expr1 in H16. destruct H16, H10. inversion H9. subst.
      apply IHeval_expr2 in H21. destruct H21, H11. inversion H10. subst. 
      pose (P := explist_prefix_eq _ _ _ _ _ _ _ _ _ _ _ H H0 H14 H12 H1 H15 H5 H26 H27).
      inversion P.
    - apply IHeval_expr1 in H20. destruct H20, H10. congruence.
    - apply IHeval_expr1 in H20. destruct H20, H10. inversion H9. subst.
      apply IHeval_expr2 in H21. destruct H21, H11. congruence.
    - apply IHeval_expr1 in H15. destruct H15, H10. inversion H9. subst.
      apply IHeval_expr2 in H16. destruct H16, H11. inversion H10. subst. congruence.
    - apply IHeval_expr1 in H15. destruct H15, H10. inversion H9. subst.
      apply IHeval_expr2 in H16. destruct H16, H11. inversion H10. subst. congruence.  




  (* PRIMOP *)
  * inversion H6; subst.
    - pose (P := explist_equality vals vals0 eff eff4 id ids ids0 H3 H12 H9 H10 H H0 H1 H11).
      destruct P, H7. subst. rewrite H4 in H17. inversion H17. auto.
    - pose (P := explist_prefix_eq _ _ _ _ _ _ _ _ _ _ _ H H0 H11 H9 H1 H12 H3 H17 H22).
      inversion P.

  (* APP *)
  * inversion H7; subst.
    - apply IHeval_expr1 in H11. destruct H11, H9. inversion H8. subst.
      pose (P := explist_equality _ _ _ _ _ _ _ H5 H19 H10 H13 H H2 H3 H14).
      destruct P, H11. subst. apply IHeval_expr2. auto.
    - apply IHeval_expr1 in H18. destruct H18. congruence.
    - apply IHeval_expr1 in H14. destruct H14, H9. inversion H8. subst.
      pose (P := explist_prefix_eq _ _ _ _ _ _ _ _ _ _ _ H H2 H12 H10 H3 H13 H5 H19 H24).
      inversion P.
    - apply IHeval_expr1 in H13. destruct H13, H9. inversion H8. subst.
      congruence.
    - apply IHeval_expr1 in H13. destruct H13, H9. inversion H8. subst.
      lia.

  (* LET *)
  * inversion H2; subst.
    - apply IHeval_expr1 in H10. destruct H10, H4. inversion H3. subst.
      apply IHeval_expr2 in H16. auto.
    - apply IHeval_expr1 in H14. destruct H14. congruence.

  (* SEQ *)
  * inversion H1; subst.
    - apply IHeval_expr1 in H8. destruct H8, H3. inversion H2. subst.
      apply IHeval_expr2 in H13. auto.
    - apply IHeval_expr1 in H12. destruct H12. inversion H2.

  (* LETREC *)
  * inversion H0. subst. apply IHeval_expr in H11. auto.

  (* MAP *)
  * inversion H9; subst.
    - assert (exps = exps0). { auto. } rewrite <- H6 in *.
      assert (length vals0 = length l * 2). { unfold vals0. rewrite H12. eapply length_make_map_vals. lia. }
      assert (length vals = length l * 2). { unfold vals. rewrite H0. eapply length_make_map_vals. lia. }
      assert (length exps = length l * 2). { unfold exps. apply length_make_map_exps. }
      rewrite <- H10 in *.
      pose (P := explist_equality _ _ _ _ _ _ _ H4 H15 (eq_sym H7) H13 (eq_sym H8) H1 H2 H14).
      destruct P. destruct H18. subst.
      unfold vals, vals0 in H18. apply make_map_vals_eq in H18.
      2-4: lia.
      destruct H18. subst. rewrite H16 in H5. inversion H5. subst. auto.
    - assert (length exps = length vals). { unfold vals. unfold exps. rewrite length_make_map_vals. rewrite length_make_map_exps. lia. rewrite <- H, <- H0. auto. }
      assert (length eff4 = length vals0).
      {
        unfold vals0. case_eq (modulo_2 (length eff4)); intros.
        * rewrite e in *. rewrite length_make_map_vals. rewrite Nat.add_0_r in H13.
          2: lia. rewrite H13. simpl. apply n_div_2_mod_0. lia.
        * rewrite e in *. rewrite length_make_map_vals2. 2: lia.
          rewrite H12. apply n_div_2_mod_1. lia.
      }
      rewrite H7 in H16, H21.
      epose (P := explist_prefix_eq _ _ _ _ _ _ _ _ _ _ _ H6 _ _ _ _ _ H4 H16 H21).
      inversion P.
      Unshelve.
      + unfold exps. rewrite length_make_map_exps. lia.
      + auto.
      + unfold vals0, exps.
        rewrite length_make_map_exps.
        unfold vals0. case_eq (modulo_2 (length eff4)); intros.
        ** rewrite e in *. rewrite length_make_map_vals. rewrite Nat.add_0_r in H13.
          2: lia. rewrite H13. rewrite <- n_div_2_mod_0. lia. lia.
        ** rewrite e in *. rewrite length_make_map_vals2. 2: lia.
          rewrite H12. rewrite <- n_div_2_mod_1. lia. lia.
      + unfold exps. rewrite length_make_map_exps. lia.
      + lia.

  (* CONS TL EXCEPTION *)
  * inversion H0; subst.
    - apply IHeval_expr in H7. destruct H7. congruence.
    - apply IHeval_expr in H11. auto.
    - apply IHeval_expr in H7. destruct H7. congruence.

  (* CONS HEAD EXCEPTION *)
  * inversion H1; subst.
    - apply IHeval_expr1 in H8. destruct H8, H3. inversion H2. subst.
      apply IHeval_expr2 in H13. destruct H13. congruence.
    - apply IHeval_expr1 in H12. destruct H12. congruence.
    - apply IHeval_expr1 in H8. destruct H8, H3. inversion H2. subst.
      apply IHeval_expr2 in H13. destruct H13, H4. inversion H2. auto.

  (* TUPLE EXCEPTION *)
  * inversion H6; subst.
    - epose (P := explist_prefix_eq_rev _ _ _ _ _ _ _ _ _ _ _ H4 H11 IHeval_expr _ _ _ _ _ _).
      inversion P. Unshelve. all: auto.
    - epose (P := exception_equality _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H4 H17 IHeval_expr H12
        _ _ _ _ _ _ _ _).
      destruct P, H7, H9. subst. auto.
      Unshelve. all: auto.

  (* TRY *)
  * inversion H2; subst.
    - apply IHeval_expr1 in H16. destruct H16, H4. inversion H3. subst.
      apply IHeval_expr2 in H18. destruct H18, H5. auto.
    - apply IHeval_expr1 in H16. destruct H16. congruence.

  (* CATCH *)
  * inversion H1; subst.
    - apply IHeval_expr1 in H15. destruct H15. congruence.
    - apply IHeval_expr1 in H15. destruct H15, H3. inversion H2. subst.
      apply IHeval_expr2 in H16. destruct H16, H4. auto.

  (* CASE EXCEPTION *)
  * inversion H0; subst.
    - apply IHeval_expr in H3. destruct H3. congruence.
    - apply IHeval_expr in H11. auto.
    - apply IHeval_expr in H7. destruct H7. congruence.
    - apply IHeval_expr in H3. destruct H3. congruence.

  (* CASE IFCLAUSE EXCEPTION *)
  * inversion H2; subst.
    - apply IHeval_expr in H5. destruct H5, H4. inversion H3. subst.
      pose (P := H1 i H6 _ _ _ H7 _ _ _ H13). destruct P. inversion H4.
    - apply IHeval_expr in H13. destruct H13. congruence.
    - apply IHeval_expr in H9. destruct H9, H4. inversion H3. subst.
      auto.
    - apply IHeval_expr in H5. destruct H5, H4. inversion H3. subst.
      pose (P := H1 i H6 _ _ _ H7 _ _ _ H17). destruct P. inversion H4.

  (* CASE GUARD EXCEPTION *)
  * inversion H5; subst.
    - apply IHeval_expr1 in H8. destruct H8 as [? [? ?]]. inversion H6. subst.
      epose proof (P := index_case_equality _ _ _ _ _ _ _ _ _ _ _ _ H3 H11 H1 H10 H16 H4 _ _ IHeval_expr2). subst. rewrite H1 in H10. inversion H10. subst.
      apply IHeval_expr2 in H16 as [? _]. congruence.
      Unshelve. all: compute; congruence.
    - apply IHeval_expr1 in H16. destruct H16. congruence.
    - apply IHeval_expr1 in H12. destruct H12 as [? [? ?]]. inversion H6. subst.
      pose proof (P := H17 i H0 _ _ _ H1).
      apply IHeval_expr2 in P. destruct P. congruence.
    - apply IHeval_expr1 in H8. destruct H8 as [? [? ?]]. inversion H6. subst.
      epose proof (P := index_case_equality _ _ _ _ _ _ _ _ _ _ _ _ H3 H15 H1 H10 H20 H4 _ _ IHeval_expr2).
      subst. rewrite H1 in H10. inversion H10. subst.
      apply IHeval_expr2 in H20 as [? [? ?]]. now subst.
      Unshelve. all: compute; congruence.

  (* CALL *)
  
   * inversion H8; subst.
    - apply IHeval_expr1 in H15. destruct H15, H9. destruct H0. subst.
      apply IHeval_expr2 in H16. destruct H16, H9. destruct H0. subst.
      epose (P := explist_prefix_eq_rev _ _ _ _ _ _ _ _ _ _ _ H6 H17 IHeval_expr3 _ _ _ _ _ _).
      inversion P. Unshelve. all: auto.
    - apply IHeval_expr1 in H15. destruct H15, H9. destruct H0. subst.
      apply IHeval_expr2 in H16. destruct H16, H9. destruct H0. subst.
      epose (P := explist_prefix_eq_rev _ _ _ _ _ _ _ _ _ _ _ H6 H21 IHeval_expr3 _ _ _ _ _ _).
      inversion P. Unshelve. all: auto.
      
    - apply IHeval_expr1 in H16. destruct H16, H9. destruct H0. subst.
      apply IHeval_expr2 in H21. destruct H21, H9. destruct H0. subst.
    
      epose (P := exception_equality _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H6 H27 IHeval_expr3 H26
        _ _ _ _ _ _ _ _).
      destruct P, H9, H10. subst. auto.
      Unshelve. all: auto.
    - apply IHeval_expr1 in H20. destruct H20. congruence. 
    - apply IHeval_expr1 in H20. destruct H20, H9. inversion H9. subst.
      apply IHeval_expr2 in H21. destruct H21. congruence.  
    - apply IHeval_expr1 in H15. destruct H15, H9. inversion H0. subst.
      apply IHeval_expr2 in H16. destruct H16, H10. inversion H9. subst.
      epose (P := explist_prefix_eq_rev _ _ _ _ _ _ _ _ _ _ _ H6 H17 IHeval_expr3 _ _ _ _ _ _).
      inversion P. Unshelve. all: auto.
    - apply IHeval_expr1 in H15. destruct H15, H9. inversion H0. subst.
      apply IHeval_expr2 in H16. destruct H16, H10. inversion H9. subst.  
      epose (P := explist_prefix_eq_rev _ _ _ _ _ _ _ _ _ _ _ H6 H17 IHeval_expr3 _ _ _ _ _ _).
      inversion P. Unshelve. all: auto.

  * inversion H0; subst.
    - apply IHeval_expr in H7. destruct H7. congruence. (* ezekhez kene egy tactic *)
    -  apply IHeval_expr in H7. destruct H7. congruence.
    - apply IHeval_expr in H8. destruct H8. congruence. 
    - apply IHeval_expr in H12. destruct H12. auto.
    - apply IHeval_expr in H12. destruct H12. congruence.
    - apply IHeval_expr in H7. destruct H7. congruence.
    - apply IHeval_expr in H7. destruct H7. congruence.
  * inversion H1; subst.
    - apply IHeval_expr1 in H8. destruct H8, H3. inversion H2. subst.
      apply IHeval_expr2 in H9. destruct H9, H4. congruence.
    - apply IHeval_expr1 in H8. destruct H8, H3. inversion H2. subst.
      apply IHeval_expr2 in H9. destruct H9, H4. congruence.
    - apply IHeval_expr1 in H9. destruct H9, H3. subst.
      apply IHeval_expr2 in H14. destruct H14 , H4. congruence.
    - apply IHeval_expr1 in H13. destruct H13, H3. congruence. 
    - apply IHeval_expr1 in H13. destruct H13, H3. inversion H2. subst.
      apply IHeval_expr2 in H14. destruct H14. inversion H3. subst. auto.  
     
    - apply IHeval_expr1 in H8. destruct H8, H3. inversion H2. subst.
      apply IHeval_expr2 in H9. destruct H9, H4. inversion H3.
    - apply IHeval_expr1 in H8. destruct H8, H3. inversion H2. subst.
      apply IHeval_expr2 in H9. destruct H9, H4. inversion H3.  
  * inversion H9; subst.
    - apply IHeval_expr1 in H16. destruct H16, H8. inversion H7. subst.
      apply IHeval_expr2 in H17. destruct H17, H10. inversion H10. congruence.
    - apply IHeval_expr1 in H16. destruct H16, H8. inversion H7. subst.
      apply IHeval_expr2 in H17. destruct H17, H10. inversion H10. congruence.
    - apply IHeval_expr1 in H17. destruct H17, H8. inversion H7. subst.
      apply IHeval_expr2 in H22. destruct H22, H10. inversion H8. subst.
      epose (P := explist_prefix_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H5 H27 H28).
      destruct P. Unshelve. all: auto.
    - apply IHeval_expr1 in H21. destruct H21, H8. inversion H7. 
    - apply IHeval_expr1 in H21. destruct H21, H8. inversion H7. subst.
      apply IHeval_expr2 in H22. destruct H22. inversion H8.
    - apply IHeval_expr1 in H16. destruct H16, H8. inversion H7. subst.
      apply IHeval_expr2 in H17. destruct H17, H10. inversion H8. subst.
      epose (P := explist_equality _ _ _ _ _ _ _ H5 H18 _ _ _ _ _ _).
      destruct P, H11. subst. auto. Unshelve. all: auto. 
    - apply IHeval_expr1 in H16. destruct H16, H8. inversion H7. subst.
      apply IHeval_expr2 in H17. destruct H17, H10. inversion H8. subst. congruence.
     
  * inversion H9; subst.
    - apply IHeval_expr1 in H16. destruct H16, H8. inversion H7. subst.
      apply IHeval_expr2 in H17. destruct H17, H10. inversion H8. subst. congruence.
   - apply IHeval_expr1 in H16. destruct H16, H8. inversion H7. subst.
      apply IHeval_expr2 in H17. destruct H17, H10. inversion H8. subst. congruence.
    - apply IHeval_expr1 in H17. destruct H17, H8. inversion H7. subst.
      apply IHeval_expr2 in H22. destruct H22, H10. inversion H8. subst. 
      epose (P := explist_prefix_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H5 H27 H28).
      destruct P. Unshelve. all: auto.
    - apply IHeval_expr1 in H21. destruct H21. congruence.
    - apply IHeval_expr1 in H21. destruct H21, H8. inversion H7. subst.
      apply IHeval_expr2 in H22. destruct H22. congruence.
    - apply IHeval_expr1 in H16. destruct H16, H8. inversion H7. subst.
      apply IHeval_expr2 in H17. destruct H17, H10. inversion H8. subst. congruence.
    - apply IHeval_expr1 in H16. destruct H16, H8. inversion H7. subst.
      apply IHeval_expr2 in H17. destruct H17, H10. inversion H8. subst.
      epose (P := explist_equality _ _ _ _ _ _ _ H5 H18 _ _ _ _ _ _).
      destruct P, H11. subst. auto. Unshelve. all: auto. 


  (* PRIMOP *)
  * inversion H6; subst.
    - epose (P := explist_prefix_eq_rev _ _ _ _ _ _ _ _ _ _ _ H4 H12 IHeval_expr _ _ _ _ _ _).
      inversion P. Unshelve. all: auto.
    - epose (P := exception_equality _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H4 H22 IHeval_expr H17
        _ _ _ _ _ _ _ _).
      destruct P, H7, H8. subst. auto.
      Unshelve. all: auto.

  (* APP FUNEXP EXCEPTION *)
  * inversion H0; subst.
    - apply IHeval_expr in H4. destruct H4. congruence.
    - apply IHeval_expr in H11. auto.
    - apply IHeval_expr in H7. destruct H7. congruence.
    - apply IHeval_expr in H6. destruct H6. congruence.
    - apply IHeval_expr in H6. destruct H6. congruence.

  (* APP PARAM EXCEPTION *)
  * inversion H7; subst.
    - apply IHeval_expr1 in H11. destruct H11, H8. inversion H0. subst.
      epose (P := explist_prefix_eq_rev _ _ _ _ _ _ _ _ _ _ _ H5 H19 IHeval_expr2 _ _ _ _ _ _).
      inversion P.
      Unshelve. all: auto.
    - apply IHeval_expr1 in H18. destruct H18. congruence.
    - apply IHeval_expr1 in H14. destruct H14, H8. inversion H0. subst.
      epose (P := exception_equality _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H5 H24 IHeval_expr2 H19
        _ _ _ _ _ _ _ _).
      destruct P, H9, H11. subst. auto.
      Unshelve. all: auto.
    - apply IHeval_expr1 in H13. destruct H13, H8. inversion H0. subst.
      epose (P := explist_prefix_eq_rev _ _ _ _ _ _ _ _ _ _ _ H5 H14 IHeval_expr2 _ _ _ _ _ _).
      inversion P.
      Unshelve. all: auto.
    - apply IHeval_expr1 in H13. destruct H13, H8. inversion H0. subst.
      epose (P := explist_prefix_eq_rev _ _ _ _ _ _ _ _ _ _ _ H5 H14 IHeval_expr2 _ _ _ _ _ _).
      inversion P.
      Unshelve. all: auto.

  (* APP BADFUN EXCEPTION *)
  * inversion H8; subst.
    - apply IHeval_expr in H12. destruct H12, H7. inversion H6. subst.
      congruence.
    - apply IHeval_expr in H19. destruct H19. congruence.
    - apply IHeval_expr in H15. destruct H15, H7. inversion H6. subst.
      epose (P := explist_prefix_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H4 H20 H25).
      inversion P.
      Unshelve. all: auto.
    - apply IHeval_expr in H14. destruct H14, H7. inversion H6. subst.
      epose (P := explist_equality _ _ _ _ _ _ _ H4 H15 _ _ _ _ _ _).
      destruct P. destruct H9. subst. auto. Unshelve. all: auto.
    - apply IHeval_expr in H14. destruct H14, H7. inversion H6. subst.
      congruence.

  (* APP BADARITY EXCEPTION *)
  * inversion H8; subst.
    -  apply IHeval_expr in H12. destruct H12, H7. inversion H6. subst.
      congruence.
    - apply IHeval_expr in H19. destruct H19. congruence.
    - apply IHeval_expr in H15. destruct H15, H7. inversion H6. subst.
      epose (P := explist_prefix_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H4 H20 H25).
      inversion P.
      Unshelve. all: auto.
    - apply IHeval_expr in H14. destruct H14, H7. inversion H6. subst.
      congruence.
    - apply IHeval_expr in H14. destruct H14, H7. inversion H6. subst.
      epose (P := explist_equality _ _ _ _ _ _ _ H4 H15 _ _ _ _ _ _).
      destruct P. destruct H9. subst. auto.
      Unshelve. all: auto.

  (* LET EXCEPTION *)
  * inversion H0; subst.
    - apply IHeval_expr in H8. destruct H8. congruence.
    - apply IHeval_expr in H12. auto.

  (* SEQ EXCEPTION *)
  * inversion H0; subst.
    - apply IHeval_expr in H7. destruct H7. congruence.
    - apply IHeval_expr in H11. auto.


  (* MAP EXCEPTION *)
  * inversion H7; subst.
    - assert (length eff = length vals). 
      { 
        unfold vals.
        case_eq (modulo_2 (length eff)); intros.
        * rewrite e in *. rewrite length_make_map_vals. rewrite Nat.add_0_r in H1.
          2: lia. rewrite H1. simpl. apply n_div_2_mod_0. lia.
        * rewrite e in *. rewrite length_make_map_vals2. 2: lia.
          rewrite H0. apply n_div_2_mod_1. lia.
      }
      rewrite H2 in H5, IHeval_expr.
      epose (P := explist_prefix_eq_rev _ _ _ _ _ _ _ _ _ _ _ H5 H13 IHeval_expr _ _ _ _ _ _).
      inversion P.
      Unshelve.
      + unfold vals, exps. rewrite length_make_map_exps.
        case_eq (modulo_2 (length eff)); intros.
        ** rewrite e in *. rewrite length_make_map_vals. rewrite Nat.add_0_r in H1.
           2: lia. rewrite H1. rewrite <- n_div_2_mod_0. lia. lia.
        ** rewrite e in *. rewrite length_make_map_vals2. 2: lia.
           rewrite H0. rewrite <- n_div_2_mod_1. lia. lia.
      + lia.
      + unfold vals0. rewrite length_make_map_vals. 2: lia.
        unfold exps. rewrite length_make_map_exps. lia.
      + unfold exps. rewrite length_make_map_exps. lia.
      + unfold exps. rewrite length_make_map_exps. lia.
      + lia.
    - epose (P := exception_equality _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H5 H19 IHeval_expr H14
        _ _ _ _ _ _ _ _).
      destruct P, H8, H12. subst. apply IHeval_expr in H19. auto.
      Unshelve.
      all: try lia.
      + unfold vals. case_eq (modulo_2 (length eff)); intros.
        ** rewrite e in *. rewrite length_make_map_vals. rewrite Nat.add_0_r in H1.
          2: lia. rewrite H1. rewrite <- n_div_2_mod_0. lia. lia.
        ** rewrite e in *. rewrite length_make_map_vals2. 2: lia.
          rewrite H0. rewrite <- n_div_2_mod_1. lia. lia.
      + unfold exps. rewrite length_make_map_exps. lia.
      + unfold vals0. case_eq (modulo_2 (length eff4)); intros.
        ** rewrite e in *. rewrite length_make_map_vals. rewrite Nat.add_0_r in H11.
           2: lia. rewrite H11. rewrite <- n_div_2_mod_0. lia. lia.
        ** rewrite e in *. rewrite length_make_map_vals2. 2: lia.
           rewrite H10. rewrite <- n_div_2_mod_1. lia. lia.
      + unfold exps. rewrite length_make_map_exps. lia.
Qed.


(** Helper about variables contained in a list of expression *)
Proposition list_variables_not_in (x : Var) (exps : list Expression) :
~ In x ((flat_map variables exps)) ->
(forall exp : Expression, In exp exps -> ~ In x (variables exp)).
Proof.
  intros. induction exps.
  * inversion H0.
  * simpl in H. assert (~ In x (variables a) /\ ~ In x (flat_map variables exps)).
    {
      unfold not in *. split; intros.
      * apply H. apply in_or_app. left. assumption.
      * apply H. apply in_or_app. right. assumption.
    }
    inversion H1. inversion H0.
    - subst. assumption.
    - apply IHexps.
      + assumption.
      + assumption.
Qed.

(** Helpers regarding variables and their containment *)
Proposition var_not_in_neq (var s : Var):
  ~(In var (variables (EVar s))) ->
  s <> var.
Proof.
  intros. unfold not in *. intro. apply H. rewrite H0. simpl. left. reflexivity.
Qed.

Proposition var_neq_not_in (var s : Var) :
  s <> var -> 
  ~(In var (variables (EVar s))).
Proof.
  intros. unfold not in *. intro. destruct (string_dec s var).
  * exact (H e).
  * apply H. inversion H0.
    - assumption.
    - inversion H1.
Qed.

(** New variable binding doesn't affect previous ones *)
Proposition irrelevant_append (env : Environment) (s var : Var) (val : Value) (t : option ValueSequence):
  s <> var ->
  get_value env (inl s) = t <->
  get_value (append_vars_to_env [var] [val] env) (inl s) = t.
Proof.
  intros; split; intro.
  * simpl. induction env.
    - simpl in *. subst. apply eqb_neq in H. rewrite H. reflexivity.
    - destruct a. assert (get_value ((s0, v) :: env) (inl s) = t). { auto. }
      unfold get_value in H0. case_eq (var_funid_eqb (inl s) s0).
      + intro. rewrite H2 in H0. subst. inversion H2. destruct s0.
        ** apply eqb_eq in H3. subst. simpl. apply eqb_neq in H. rewrite H. simpl.
           rewrite eqb_refl. reflexivity.
        ** inversion H3.
      + intros. simpl in H1. destruct s0.
        ** inversion H2. rewrite H4 in H1. simpl. destruct ((v0 =? var)%string).
          ++ simpl. apply eqb_neq in H. rewrite H. assumption.
          ++ simpl. rewrite H4. apply eqb_neq in H. simpl. exact (IHenv H1).
        ** simpl. exact (IHenv H1).
  * simpl in H0. induction env.
    - simpl in H0. apply eqb_neq in H. rewrite H in H0. subst. simpl. reflexivity.
    - destruct a. simpl in *. case_eq (var_funid_eqb s0 (inl var)).
      + intro. destruct s0.
        ** inversion H1. apply eqb_eq in H3. rewrite H3. apply eqb_neq in H. rewrite H.
           rewrite H1 in H0. simpl in H0. rewrite H in H0. assumption.
        **  rewrite H1 in H0. simpl in H0. apply eqb_neq in H. rewrite H in H0. assumption.
      + intro. destruct s0.
        ** inversion H1. case_eq ((s =? v0)%string); intro.
          -- rewrite H1 in H0. simpl in H0. rewrite H2 in H0. assumption.
          -- rewrite H1 in H0. simpl in H0. rewrite H2 in H0. exact (IHenv H0).
        ** rewrite H1 in H0. simpl in H0. exact (IHenv H0).
Qed.

(** New variable binding doesn't affect previous ones *)
Proposition irrelevant_append_eq (env : Environment) (s var : Var) (val : Value):
  s <> var ->
  get_value env (inl s) = get_value (append_vars_to_env [var] [val] env) (inl s).
Proof.
  intros. pose (IRA := irrelevant_append env s var val (get_value env (inl s)) H).
  assert (get_value env (inl s) = get_value env (inl s)). reflexivity. inversion IRA.
  pose (P1 := H1 H0). apply eq_sym. assumption.
Qed.

(* Theorem variable_irrelevancy (env: Environment) (cl : Closures) (e : Expression) (t val : Value) (var : Var) :
  ~(In var (variables e)) -> (forall env' a b, t <> VClosure env' a b) ->
  |env, cl, e| -e> t <->
  |append_vars_to_env [var] [val] env, cl, e| -e> t.
Proof.
  intro. split; intro. 
  * induction H1 using eval_expr_ind_extended.
    - apply eval_lit.
    - assert (get_value env (inl s) = get_value (append_vars_to_env [var] [val] env) (inl s)). { apply (var_not_in_neq) in H. pose (irrelevant_append_eq env s var val H). assumption. } rewrite H1. apply eval_var.
    - admit.
    - pose (H0 (inl env) (snd (split l)) e).  unfold not in n. assert (VClosure (inl env) (snd (split l)) e = VClosure (inl env) (snd (split l)) e). reflexivity. pose (n H1). inversion f.
    - apply eval_tuple.
      + assumption.
      + intros. apply H3; try(assumption).
        ** simpl in H. apply (list_variables_not_in) with (exps := exps). assumption. apply in_combine_l in H4. assumption.
        ** intros.
Qed.*)

(** Last append result *)
Proposition get_value_here (env : Environment) (var : Var + FunctionIdentifier) (val : Value):
get_value (insert_value env var val) var = Some [val].
Proof.
  induction env.
  * simpl. rewrite var_funid_eqb_refl. reflexivity.
  * simpl. destruct a. case_eq (var_funid_eqb s var); intro.
    - simpl. rewrite var_funid_eqb_refl. reflexivity.
    - simpl. rewrite var_funid_eqb_sym, H. assumption.
Qed.

(** Previous append result *)
Proposition get_value_there (env : Environment) (var var' : Var + FunctionIdentifier) 
     (val : Value):
var <> var' ->
get_value (insert_value env var val) var' = get_value env var'.
Proof.
  intro. induction env.
  * simpl. apply var_funid_eqb_neq in H. rewrite var_funid_eqb_sym in H. rewrite H. reflexivity.
  * simpl. destruct a. case_eq (var_funid_eqb s var); intro.
    - apply var_funid_eqb_eq in H0. assert (var <> var'). auto. rewrite <- H0 in H.
      apply var_funid_eqb_neq in H. rewrite var_funid_eqb_sym in H. rewrite H. simpl. apply var_funid_eqb_neq in H1.
      rewrite var_funid_eqb_sym in H1. rewrite H1. reflexivity.
    - simpl. case_eq (var_funid_eqb var' s); intros.
      + reflexivity.
      + apply IHenv.
Qed.
