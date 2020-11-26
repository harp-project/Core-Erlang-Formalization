Require Core_Erlang_Weak_Equivalence.
Require Core_Erlang_Proofs.

Module Equivalence_Proofs.

Export Core_Erlang_Weak_Equivalence.
Export Core_Erlang_Proofs.Proofs.

Import ListNotations.

Theorem equivalence : forall env id eff e1 e2 id1 id2 res1 res2 eff1 eff2,
  | env, id, e1, eff | -e> |id1, res1, eff1 | ->
  | env, id, e2, eff | -e> |id2, res2, eff2 | ->
  res1 = res2
->
  (
    | env, id, e1, eff | -e> |id1, res1, eff1 | <->
    | env, id, e2, eff | -e> |id2, res1, eff2 |
  )
.
Proof.
  intros. rewrite H1 in *. split; auto.
Qed.

Definition strong_equivalent e1 e2 id1 id2 id1' id2' :=
forall  env eff res eff',
  |env, id1, e1, eff| -e> |id2, res, eff'|
<->
  |env, id1', e2, eff| -e> |id2', res, eff'|.


Example call_comm : forall (e e' : Expression) (x1 x2 t : Value) 
                           (env : Environment) (id : nat),
  |env, id, e, []| -e> |id, inl [x1], []| ->
  |env, id, e', []| -e> | id, inl [x2], []| ->
  |env, id, ECall "+"%string [e ; e'], []| -e> | id, inl [t], []| ->
  |env, id, ECall "+"%string [e' ; e], []| -e> | id, inl [t], []|.
Proof.
  intros. 
  (* List elements *)
  inversion H1. subst. inversion H5. subst.
  pose (EE1 := element_exist _ _ H4).
  inversion EE1. inversion H2. subst. inversion H4.
  pose (EE2 := element_exist 0 x0 H9).
  inversion EE2. inversion H3. subst. simpl in H4. inversion H4.
  apply eq_sym, length_zero_iff_nil in H12. subst.
  pose (WD1 := eval_expr_determinism H).
  pose (WD2 := eval_expr_determinism H0).
  pose (P1 := H8 0 Nat.lt_0_2).
  pose (P2 := H8 1 Nat.lt_1_2).
  apply WD1 in P1; inversion P1. inversion H10.
  destruct H12. subst.
  simpl in P2, H12, H13.
  rewrite <- H12, <- H13 in P2. subst.
  apply WD2 in P2. inversion P2. destruct H14.
  inversion H13. rewrite <- H15 in *. subst.
  eapply eval_single, eval_call with (vals := [x3; x]) (eff := [[];[]]) (ids := [nth 0 ids 0; nth 0 ids 0]); auto.
  * intros. inversion H17.
    - assumption.
    - inversion H19.
      + simpl. assumption.
      + inversion H21.
  * rewrite (@plus_comm_basic x x3 t). 
      - reflexivity.
      - simpl last.
        pose (EE3 := element_exist _ _ H6).
        inversion EE3. inversion H17.
        subst. inversion H6.
        pose (EE4 := element_exist _ _ H19).
        inversion EE4. inversion H18.
        subst. inversion H6. apply eq_sym, length_zero_iff_nil in H21. subst.
        simpl in H12, H14. subst.
        exact H11.
Qed.


Example let_1_comm (e1 e2 : Expression) (t x1 x2 : Value) (id : nat) :
  |[], id, e1, []| -e> |id, inl [x1], []| ->
  | [(inl "X"%string, x1)], id, e2, []| -e> |id, inl [x2], []| ->
  |[], id, ELet ["X"%string] e1 (ECall "+"%string [^EVar "X"%string ; e2]), []| 
  -e> | id, inl [t], []| ->
  |[], id, ELet ["X"%string] e1 (ECall "+"%string [e2 ; ^EVar "X"%string]), []| 
  -e> |id, inl [t], []|.
Proof.
  * intros. inversion H1. inversion H5. subst.
    pose (EE1 := element_exist 0 vals H20).
    inversion EE1. inversion H2. subst.
    inversion H20. apply eq_sym, length_zero_iff_nil in H4. subst.
    pose (P := eval_expr_determinism H15 _ _ _ H).
    destruct P, H4. inversion H3. subst.
    eapply eval_single, eval_let; auto.
    - exact H15.
    - reflexivity.
    - eapply (call_comm _ _ _ _ _ _ _ _ _ H21).
      Unshelve.
      exact x1.
      exact x2.
      apply eval_single, eval_var. simpl. auto.
      auto.
Qed.

Example call_comm_ex : forall (e e' : Expression) (x1 x2 : Value) (env : Environment)
       (t t' : Value) (id : nat),
  |env, id, e, []| -e> |id, inl [x1], []| ->
  |env, id, e', []| -e> |id, inl [x2], []| ->
  |env, id, ECall "+"%string [e ; e'], []| -e> |id, inl [t], []| ->
  |env, id, ECall "+"%string [e' ; e], []| -e> |id, inl [t'], []| ->
  t = t'.
Proof.
  intros. pose (P := call_comm e e' x1 x2 t env _ H H0 H1). 
  pose (DET := eval_expr_determinism P _ _ _ H2). inversion DET. inversion H3. reflexivity.
Qed.

Example let_1_comm_2_list (env: Environment) (e1 e2 : SingleExpression) (t t' v1 v2 : Value) 
   (eff eff1 eff2 : SideEffectList) (A B : Var) (VarHyp : A <> B) (id id1 id2 : nat)
(Hypo1 : |env, id, e1, eff| -s> | id + id1, inl [v1], eff ++ eff1|)
(Hypo2 : |env, id + id2, e1, eff ++ eff2| -s> | id + id1 + id2, inl [v1], eff ++ eff2 ++ eff1|)
(Hypo1' : |env, id, e2, eff| -s> | id + id2, inl [v2], eff ++ eff2|)
(Hypo2' : |env, id + id1, e2, eff ++ eff1| -s> | id + id2 + id1, inl [v2], eff ++ eff1 ++ eff2|) :
|env, id, ELet [A; B] (EValues [e1; e2])
     (ECall "+"%string [^EVar A ; ^EVar B]), eff| -e> |id + id1 + id2, inl [t], eff ++ eff1 ++ eff2|
->
|env, id, ELet [A; B] (EValues [e2; e1])
     (ECall "+"%string [^EVar A ; ^EVar B]), eff| -e> |id + id2 + id1, inl [t'], eff ++ eff2 ++ eff1|
->
t = t'.
Proof.
  intros.
  (* FROM LET HYPO1 *)
  inversion H. inversion H4. subst. simpl in H19.
  pose (EE1 := element_exist 1 vals H19).
  inversion EE1 as [v1']. inversion H1. subst. inversion H19.
  pose (EE2 := element_exist 0 x H3).
  inversion EE2 as [v2']. inversion H2. subst. inversion H19.
  apply eq_sym, length_zero_iff_nil in H6. subst.
  inversion H14. subst.
  pose (EE3 := element_exist _ _ H8). inversion EE3 as [eff1']. inversion H5. subst. inversion H8.
  pose (EE4 := element_exist _ _ H11). inversion EE4 as [eff2']. inversion H6. subst. inversion H8.
  apply eq_sym, length_zero_iff_nil in H13. subst.
  pose (EE5 := element_exist _ _ H9). inversion EE5 as [id1']. inversion H12. subst. inversion H9.
  pose (EE6 := element_exist _ _ H15). inversion EE6 as [id2']. inversion H13. subst. inversion H9.
  apply eq_sym, length_zero_iff_nil in H17. subst.
  (* FROM LET HYPO2 *)
  inversion H0. inversion H21. subst.
  pose (EE1' := element_exist _ _ H36). inversion EE1' as [v2'']. inversion H16. subst. inversion H36.
  pose (EE2' := element_exist _ _ H18). inversion EE2' as [v1'']. inversion H17. subst. inversion H36.
  apply eq_sym, length_zero_iff_nil in H23. subst.
  inversion H31. subst.
  pose (EE3' := element_exist _ _ H25). inversion EE3' as [eff2'']. inversion H22. subst. inversion H25.
  pose (EE4' := element_exist _ _ H28). inversion EE4' as [eff1'']. inversion H23. subst. inversion H25.
  apply eq_sym, length_zero_iff_nil in H30. subst.

  pose (EE5' := element_exist _ _ H26). inversion EE5' as [id2'']. inversion H29. subst. inversion H26.
  pose (EE6' := element_exist _ _ H32). inversion EE6' as [id1'']. inversion H30. subst. inversion H26.
  apply eq_sym, length_zero_iff_nil in H34. subst.
  clear EE1. clear EE2. clear EE3. clear EE4. clear EE5. clear EE6.
  clear EE1'. clear EE2'. clear EE3'. clear EE4'. clear EE5'. clear EE6'.
  
  (* assert (v1' = v1 /\ eff1' = eff1).
  { *)
    pose (P1 := H10 0 Nat.lt_0_2).
    simpl in P1.
    pose (WD1 := eval_singleexpr_determinism Hypo1).
    pose (PC1 := WD1 _ _ _ P1).
    destruct PC1. destruct H34. inversion H33. subst.
  (* } *)
  
  (* assert (v2'' = v2 /\ eff2'' = eff2).
  { *)
    pose (P2 := H27 0 Nat.lt_0_2).
    simpl in P2.
    pose (WD2 := eval_singleexpr_determinism Hypo1').
    pose (PC2 := WD2 _ _ _ P2).
    destruct PC2. destruct H35. inversion H34. subst.
  (* } *)

  (* assert (v1'' = v1 /\ v2' = v2 /\ eff1'' = eff1 /\ eff2' = eff2).
  { *)
    pose (P3 := H27 1 Nat.lt_1_2).
    simpl in P3.
    pose (WD3 := eval_singleexpr_determinism Hypo2).
    pose (PC3 := WD3 _ _ _ P3).
    inversion PC3. inversion H35. destruct H38. subst.
    pose (P4 := H10 1 Nat.lt_1_2).
    simpl in P4.
    pose (WD4 := eval_singleexpr_determinism Hypo2').
    pose (PC4 := WD4 _ _ _ P4).
    inversion PC4. destruct H39. inversion H38. subst.
  (* } *)
  clear dependent P1. clear dependent P2. clear dependent P3. clear dependent P4.

  (* FROM CALL HYPOS *)
 (* FROM CALL HYPO1 *)
  inversion H20. inversion H42. subst.
  pose (EC1 := element_exist _ _ H49). inversion EC1 as [v10]. inversion H39. subst. 
  inversion H49.
  pose (EC2 := element_exist _ _ H41). inversion EC2 as [v20]. inversion H40. subst. 
  inversion H49.
  apply eq_sym, length_zero_iff_nil in H44. subst.
  pose (EC3 := element_exist _ _ H50). inversion EC3 as [eff10]. inversion H43. subst.
  inversion H50.
  pose (EC4 := element_exist _ _ H45). inversion EC4 as [eff20]. inversion H44. subst.
  inversion H50.
  apply eq_sym, length_zero_iff_nil in H47. subst.
  pose (EC5 := element_exist _ _ H51). inversion EC5 as [id10]. inversion H46. subst.
  inversion H51.
  pose (EC6 := element_exist _ _ H48). inversion EC6 as [id20]. inversion H47. subst.
  inversion H51.
  apply eq_sym, length_zero_iff_nil in H54. subst.
  (* FROM CALL HYPO2 *)
  inversion H37. inversion H57. subst.
  pose (EC1' := element_exist _ _ H65). inversion EC1' as [v20']. inversion H53. subst.
  inversion H65.
  pose (EC2' := element_exist _ _ H56). inversion EC2' as [v10']. inversion H54. subst.
  inversion H65.
  apply eq_sym, length_zero_iff_nil in H59. subst.
  pose (EC3' := element_exist _ _ H66). inversion EC3' as [eff20']. inversion H58. subst.
  inversion H66.
  pose (EC4' := element_exist _ _ H61). inversion EC4' as [eff10']. inversion H59. subst.
  inversion H66.
  apply eq_sym, length_zero_iff_nil in H63. subst.
  pose (EC5' := element_exist _ _ H67). inversion EC5' as [id20']. inversion H62. subst.
  inversion H67.
  pose (EC6' := element_exist _ _ H64). inversion EC6' as [id10']. inversion H63. subst.
  inversion H67.
  apply eq_sym, length_zero_iff_nil in H70. subst.


  pose (PUM1 := plus_effect_unmodified _ _ _ H55).
  pose (PUM2 := plus_effect_unmodified _ _ _ H71).
  inversion PUM1. inversion PUM2. simpl in H69, H70. subst.
  (* EVERYTHING IS EQUAL *)
  (* assert (v1' = v1 /\ v1'' = v1 /\ v2' = v2 /\ v2'' = v2).
  { *)
    pose (P1 := H52 0 Nat.lt_0_2).
    pose (P2 := H52 1 Nat.lt_1_2).
    pose (P1' := H68 1 Nat.lt_1_2).
    pose (P2' := H68 0 Nat.lt_0_2).
    simpl in P1, P2, P1', P2'.
    inversion P1. inversion P2. inversion P1'. inversion P2'. subst.
    inversion H73. inversion H82. inversion H90. inversion H98. subst.
    rewrite get_value_there in H78, H105.
    2-3 : congruence.
    rewrite get_value_here in H78, H87, H96, H105.
    inversion H78. inversion H87. inversion H96. inversion H105. subst.
(* } *)
  clear PUM1. clear PUM2.
  apply (plus_comm_basic_value _ (eff ++ eff2 ++ eff1)) in H55.
  simpl last in H71.
  rewrite H55 in H71. inversion H71.
  reflexivity.
Qed.

Example exp_to_fun (e : Expression) (x : Var) (id id' : nat):
  strong_equivalent e (ELet [x] (EFun [] e) (EApp (EVar x) [])) (S id) id' id id'.
Proof.
  unfold strong_equivalent.
  split; intros.
  * eapply eval_single, eval_let; auto.
    - apply eval_single, eval_fun.
    - reflexivity.
    - eapply eval_single, eval_app with (vals := []) (eff := []) (ids := []); auto.
      + eapply eval_single, eval_var. simpl. rewrite get_value_here. reflexivity.
      + auto.
      + intros. inversion H0.
      + unfold get_env. simpl. auto.
  * inversion H. inversion H3; subst.
    - pose (EE1 := element_exist 0 vals H18). inversion EE1. inversion H0. subst.
      inversion H18. apply eq_sym, length_zero_iff_nil in H2. subst.
      inversion H13. subst. inversion H5. subst.

      inversion H19. inversion H6.
      + subst.
        apply eq_sym, length_zero_iff_nil in H17. subst.
        apply eq_sym, length_zero_iff_nil in H20. subst.
        apply eq_sym, length_zero_iff_nil in H14. subst.
        inversion H15. inversion H7. subst. simpl in H24.
        rewrite get_value_here in H24. inversion H24. subst.

        unfold get_env in H28. simpl in H28. assumption.
      + subst. inversion H22. inversion H7.
      + subst. inversion H14.
      + subst. inversion H17. inversion H7. subst.
        simpl in H27. rewrite get_value_here in H27. inversion H27. subst.
        congruence.
      + subst. inversion H17. inversion H7. subst.
        simpl in H27. rewrite get_value_here in H27. inversion H27. subst.
        contradiction.
    - inversion H17. inversion H4.
Qed.

Lemma X_neq_Y :
(@inl string FunctionIdentifier "X"%string) <> (inl "Y"%string).
Proof.
  unfold not. intros. inversion H.
Qed.

Lemma Y_neq_X :
(@inl string FunctionIdentifier "Y"%string) <> (inl "X"%string).
Proof.
  unfold not. intros. inversion H.
Qed.

Example let_2_comm (env: Environment)(e1 e2 : Expression) (t x x0 : Value) 
    (eff eff1 eff2 : SideEffectList) (id0 id1 id2 : nat) (A B : Var) (VarHyp : A <> B) :
  |env, id0, e2, eff| -e> |id0 + id2, inl [x0], eff ++ eff2|
 -> 
  |append_vars_to_env [A] [x] env, id0 + id1, e2, eff ++ eff1|
  -e> | id0 + id1 + id2, inl [x0], eff ++ eff1 ++ eff2|
 ->
  |env, id0, e1, eff| -e> |id0 + id1, inl [x], eff ++ eff1|
 -> 
  |append_vars_to_env [A] [x0] env, id0 + id2, e1, eff ++ eff2|
  -e> |id0 + id2 + id1, inl [x], eff ++ eff2 ++ eff1| 
 ->
  |env, id0, ELet [A] e1 (ELet [B] e2 
        (ECall "+"%string [^EVar A ; ^EVar B])), eff| -e>
  | id0 + id1 + id2, inl [t], eff ++ eff1 ++ eff2|
->
  |env, id0, ELet [A] e2 (ELet [B] e1
        (ECall "+"%string [^EVar A ; ^EVar B])), eff| -e>
  | id0 + id2 + id1, inl [t], eff ++ eff2 ++ eff1|
.
Proof.
  * intros. inversion H3. inversion H7. subst.
    pose (EE1 := element_exist 0 vals H22).
    inversion EE1 as [x'].
    inversion H4. subst. 
    inversion H22. apply eq_sym, length_zero_iff_nil in H6. subst.
(*     assert (x' = x /\ eff1' = eff ++ eff1 /\ id1' = (id0 + id1)%nat).
    { *)
      pose (WD := eval_expr_determinism H1 _ _ _ H17). destruct WD. destruct H6. inversion H5.
      subst.
(*     } *)
    inversion H23. inversion H10. subst.
    pose (EE1' := element_exist 0 vals H28).
    inversion EE1' as [x0'].
    inversion H6. subst. inversion H28.
    apply eq_sym, length_zero_iff_nil in H9.
(*     assert (x0' = x0 /\ eff2' = eff ++ eff1 ++ eff2 /\ id2' = (id0 + id1 + id2)%nat).
    { *)
      pose (WD := eval_expr_determinism H0 _ _ _ H21). 
      destruct WD. destruct H11. inversion H8.
      subst.
(*     } *)
   (*proving starts*)
   eapply eval_single, eval_let; auto.
   - exact H.
   - auto.
   - eapply eval_single, eval_let; auto.
     + exact H2.
     + auto.
   (* call information *)
     + inversion H29. inversion H13. subst.
       pose (EC1 := element_exist 1 _ H25).
       pose (EC2 := element_exist 1 _ H26).
       pose (EC3 := element_exist 1 _ H27).
       inversion EC1 as [x'']. inversion EC2 as [eff1'']. inversion EC3 as [id1''].
       inversion H9. inversion H11. inversion H12. subst.
       inversion H25. inversion H26. inversion H27.
       pose (EC1' := element_exist 0 _ H16).
       pose (EC2' := element_exist 0 _ H18).
       pose (EC3' := element_exist 0 _ H19).
       inversion EC1' as [x0'']. inversion EC2' as [eff2'']. inversion EC3' as [id2''].
       inversion H14. inversion H20. inversion H24. subst.
       inversion H16. inversion H18. inversion H19.
       apply eq_sym, length_zero_iff_nil in H32.
       apply eq_sym, length_zero_iff_nil in H34.
       apply eq_sym, length_zero_iff_nil in H35. subst.

         pose (P1' := H30 0 Nat.lt_0_2).
         pose (P2' := H30 1 Nat.lt_1_2).
         inversion P1'. inversion P2'. simpl in H45, H46, H47, H48. subst.

         inversion H35. inversion H44. subst.
         simpl in H40, H39, H41, H49, H48, H50.

         rewrite get_value_there in H40. 2: congruence.
         rewrite get_value_here in H40. inversion H40.
         rewrite get_value_here in H49. inversion H49. subst.

       (* BACK TO CALL PROOF *)
       eapply eval_single, eval_call with (vals := [x0'' ; x'']) (eff := [eff ++ eff2 ++ eff1;eff ++ eff2 ++ eff1]) 
                    (ids := [(id0 + id2 + id1)%nat; (id0 + id2 + id1)%nat]); auto.
       ** intros. inversion H31. 2: inversion H34.
         -- simpl. eapply eval_single, eval_var. rewrite get_value_here. auto.
         -- simpl. eapply eval_single, eval_var. rewrite get_value_there, get_value_here. auto. congruence.
         -- inversion H37.
       ** apply plus_comm_basic_value with (eff0 := eff ++ eff1 ++ eff2). assumption.
Qed.

Example let_2_comm_eq (env: Environment)(e1 e2 : Expression) (t x x0 : Value) 
    (eff eff1 eff2 : SideEffectList) (id0 id1 id2 : nat) (A B : Var) (VarHyp : A <> B) :
  |env, id0, e2, eff| -e> |id0 + id2, inl [x0], eff ++ eff2| -> 
  |append_vars_to_env [A] [x] env, id0 + id1, e2, eff ++ eff1|
  -e> | id0 + id1 + id2, inl [x0], eff ++ eff1 ++ eff2| ->
  |env, id0, e1, eff| -e> |id0 + id1, inl [x], eff ++ eff1| -> 
  |append_vars_to_env [A] [x0] env, id0 + id2, e1, eff ++ eff2|
  -e> |id0 + id2 + id1, inl [x], eff ++ eff2 ++ eff1| ->
  |env, id0, ELet [A] e1 (ELet [B] e2
        (ECall "+"%string [^EVar A ; ^EVar B])), eff| -e> 
  | id0 + id1 + id2, inl [t], eff ++ eff1 ++ eff2|
<->
  |env, id0, ELet [A] e2 (ELet [B] e1
        (ECall "+"%string [^EVar A ; ^EVar B])), eff| -e>
  | id0 + id2 + id1, inl [t], eff ++ eff2 ++ eff1|
.
Proof.
  split.
  * apply let_2_comm with (x := x) (x0 := x0); try (assumption).
  * apply let_2_comm with (x := x0) (x0 := x); try (assumption).
Qed.

(* THIS THEOREM COULD BE PROVEN WITH STRONG DETERMINISM
Example let_1_comm_2_list (env: Environment) (e1 e2 : Expression) (t t' : Value) eff eff1 eff2:
|env, ELet ["X"%string; "Y"%string] [e1 ; e2] (ECall "+"%string [EVar "X"%string ; EVar "Y"%string]), eff| -e> |inl t, eff ++ eff1 ++ eff2|
->
|env, ELet ["X"%string; "Y"%string] [e2 ; e1] (ECall "+"%string [EVar "X"%string ; EVar "Y"%string]), eff| -e> |inl t', eff ++ eff2 ++ eff1|
->
t = t'. *)

Example let_2_binding_swap (env: Environment)(e1 e2 : Expression) (t x x0 : Value) 
    (eff eff1 eff2 : SideEffectList) (A B : Var) (id0 id1 id2 : nat) (VarHyp : A <> B) :
  |env, id0, e2, eff| -e> |id0 + id2, inl [x0], eff ++ eff2| -> 
  |append_vars_to_env [A] [x] env, id0 + id1, e2, eff ++ eff1| -e>
  | id0 + id1 + id2, inl [x0], eff ++ eff1 ++ eff2| ->
  |env, id0, e1, eff| -e> |id0 + id1, inl [x], eff ++ eff1| -> 
  |append_vars_to_env [B] [x0] env, id0 + id2, e1, eff ++ eff2| -e>
  |id0 + id2 + id1, inl [x], eff ++ eff2 ++ eff1|
->
  |env, id0, ELet [A] e1 (ELet [B] e2
        (ECall "+"%string [^EVar A ; ^EVar B])), eff| -e>
  |id0 + id1 + id2, inl [t], eff ++ eff1 ++ eff2|
<->
  |env, id0, ELet [B] e2 (ELet [A] e1
        (ECall "+"%string [^EVar A ; ^EVar B])), eff| -e>
  |id0 + id2 + id1, inl [t], eff ++ eff2 ++ eff1|
.
Proof.
  split.
  * intros. inversion H3. inversion H7. subst.
    pose (EE1 := element_exist 0 vals H22).
    inversion EE1 as [x'].
    inversion H4. subst. 
    inversion H22. apply eq_sym, length_zero_iff_nil in H6. subst.
(*     assert (x' = x /\ eff1' = eff ++ eff1 /\ id1' = (id0 + id1)%nat).
    { *)
      pose (WD := eval_expr_determinism H1 _ _ _ H17). destruct WD. destruct H6. inversion H5.
      subst.
(*     } *)
    inversion H23. inversion H10. subst.
    pose (EE1' := element_exist 0 vals H28).
    inversion EE1' as [x0'].
    inversion H6. subst. inversion H28.
    apply eq_sym, length_zero_iff_nil in H9.
(*     assert (x0' = x0 /\ eff2' = eff ++ eff1 ++ eff2 /\ id2' = (id0 + id1 + id2)%nat).
    { *)
      pose (WD := eval_expr_determinism H0 _ _ _ H21). 
      destruct WD. destruct H11. inversion H8.
      subst.
(*     } *)
   (*proving starts*)
   eapply eval_single, eval_let; auto.
   - exact H.
   - auto.
   - eapply eval_single, eval_let; auto.
     + exact H2.
     + auto.
   (* call information *)
     + inversion H29. inversion H13. subst.
       pose (EC1 := element_exist 1 _ H25).
       pose (EC2 := element_exist 1 _ H26).
       pose (EC3 := element_exist 1 _ H27).
       inversion EC1 as [x'']. inversion EC2 as [eff1'']. inversion EC3 as [id1''].
       inversion H9. inversion H11. inversion H12. subst.
       inversion H25. inversion H26. inversion H27.
       pose (EC1' := element_exist 0 _ H16).
       pose (EC2' := element_exist 0 _ H18).
       pose (EC3' := element_exist 0 _ H19).
       inversion EC1' as [x0'']. inversion EC2' as [eff2'']. inversion EC3' as [id2''].
       inversion H14. inversion H20. inversion H24. subst.
       inversion H16. inversion H18. inversion H19.
       apply eq_sym, length_zero_iff_nil in H32.
       apply eq_sym, length_zero_iff_nil in H34.
       apply eq_sym, length_zero_iff_nil in H35. subst.

         pose (P1' := H30 0 Nat.lt_0_2).
         pose (P2' := H30 1 Nat.lt_1_2).
         inversion P1'. inversion P2'. simpl in H45, H46, H47, H48. subst.

         inversion H35. inversion H44. subst.
         simpl in H40, H39, H41, H49, H48, H50.

         rewrite get_value_there in H40. 2: congruence.
         rewrite get_value_here in H40. inversion H40.
         rewrite get_value_here in H49. inversion H49. subst.

       (* BACK TO CALL PROOF *)
       eapply eval_single, eval_call with (vals := [x'' ; x0'']) (eff := [eff ++ eff2 ++ eff1;eff ++ eff2 ++ eff1]) 
                    (ids := [(id0 + id2 + id1)%nat; (id0 + id2 + id1)%nat]); auto.
       ** intros. inversion H31. 2: inversion H34.
         -- simpl. eapply eval_single, eval_var. rewrite get_value_there, get_value_here. auto. congruence.
         -- simpl. eapply eval_single, eval_var. rewrite get_value_here. auto.
         -- inversion H37.
       ** apply plus_effect_changeable with (eff0 := eff ++ eff1 ++ eff2). assumption.
  * intros. inversion H3. inversion H7. subst.
    pose (EE1 := element_exist 0 vals H22).
    inversion EE1 as [x'].
    inversion H4. subst. 
    inversion H22. apply eq_sym, length_zero_iff_nil in H6. subst.
(*     assert (x' = x /\ eff1' = eff ++ eff1 /\ id1' = (id0 + id1)%nat).
    { *)
      pose (WD := eval_expr_determinism H _ _ _ H17). destruct WD. destruct H6. inversion H5.
      subst.
(*     } *)
    inversion H23. inversion H10. subst.
    pose (EE1' := element_exist 0 vals H28).
    inversion EE1' as [x0'].
    inversion H6. subst. inversion H28.
    apply eq_sym, length_zero_iff_nil in H9.
(*     assert (x0' = x0 /\ eff2' = eff ++ eff1 ++ eff2 /\ id2' = (id0 + id1 + id2)%nat).
    { *)
      pose (WD := eval_expr_determinism H2 _ _ _ H21). 
      destruct WD. destruct H11. inversion H8.
      subst.
(*     } *)
   (*proving starts*)
   eapply eval_single, eval_let; auto.
   - exact H1.
   - auto.
   - eapply eval_single, eval_let; auto.
     + exact H0.
     + auto.
   (* call information *)
     + inversion H29. inversion H13. subst.
       pose (EC1 := element_exist 1 _ H25).
       pose (EC2 := element_exist 1 _ H26).
       pose (EC3 := element_exist 1 _ H27).
       inversion EC1 as [x'']. inversion EC2 as [eff1'']. inversion EC3 as [id1''].
       inversion H9. inversion H11. inversion H12. subst.
       inversion H25. inversion H26. inversion H27.
       pose (EC1' := element_exist 0 _ H16).
       pose (EC2' := element_exist 0 _ H18).
       pose (EC3' := element_exist 0 _ H19).
       inversion EC1' as [x0'']. inversion EC2' as [eff2'']. inversion EC3' as [id2''].
       inversion H14. inversion H20. inversion H24. subst.
       inversion H16. inversion H18. inversion H19.
       apply eq_sym, length_zero_iff_nil in H32.
       apply eq_sym, length_zero_iff_nil in H34.
       apply eq_sym, length_zero_iff_nil in H35. subst.

         pose (P1' := H30 0 Nat.lt_0_2).
         pose (P2' := H30 1 Nat.lt_1_2).
         inversion P1'. inversion P2'. simpl in H45, H46, H47, H48. subst.

         inversion H35. inversion H44. subst.
         simpl in H40, H39, H41, H49, H48, H50.

         rewrite get_value_there in H49. 2: congruence.
         rewrite get_value_here in H49. inversion H49.
         rewrite get_value_here in H40. inversion H40. subst.

       (* BACK TO CALL PROOF *)
       eapply eval_single, eval_call with (vals := [x'' ; x0'']) (eff := [eff ++ eff1 ++ eff2;eff ++ eff1 ++ eff2]) 
                    (ids := [(id0 + id1 + id2)%nat; (id0 + id1 + id2)%nat]); auto.
       ** intros. inversion H31. 2: inversion H34.
         -- simpl. eapply eval_single, eval_var. rewrite get_value_here. auto.
         -- simpl. eapply eval_single, eval_var. rewrite get_value_there, get_value_here. auto. congruence.
         -- inversion H37.
       ** apply plus_effect_changeable with (eff0 := eff ++ eff2 ++ eff1). assumption.
Qed.

Example let_2_apply_effect_free (env: Environment)(e1 e2 exp : Expression) (v1 v2 : Value) 
       (v0 t : ValueSequence + Exception) (A B : Var) (VarHyp : A <> B) (id: nat) (eff : SideEffectList)
(E1 : | append_vars_to_env [A] [v1] (append_vars_to_env [B] [v2] env), id, exp, eff | -e> |id, v0, eff|)
(E2 : | append_vars_to_env [B] [v2] (append_vars_to_env [A] [v1] env), id, exp, eff | -e> |id, v0, eff|)
    :
  |env, id, e2, eff | -e> |id, inl [v2], eff| -> 
  |append_vars_to_env [A] [v1] env, id, e2, eff| -e> | id, inl [v2], eff| ->
  |env, id, e1, eff | -e> | id, inl [v1], eff| -> 
  |append_vars_to_env [B] [v2] env, id, e1, eff| -e> | id , inl [v1], eff |
->
  |env, id, ELet [A] e1 (ELet [B] e2
        (EApp exp [^EVar A ; ^EVar B])), eff| -e> |id , t, eff|
  <->
  |env, id, ELet [B] e2 (ELet [A] e1
        (EApp exp [^EVar A ; ^EVar B])), eff| -e> |id, t, eff |
.
Proof.
  split;intros.
   (** Deconstruct ELet-s *)
  * inversion H3. inversion H7. subst.
    pose (EE1 := element_exist 0 vals H22). inversion EE1 as [v1'].
    inversion H4. subst. inversion H22.
    apply eq_sym, length_zero_iff_nil in H6. subst.
    (* assert (v1' = v1 /\ eff1' = []).
    { *)
      pose (WD := eval_expr_determinism H1 _ _ _ H17). destruct WD. destruct H6. inversion H5.
      subst.
    (* } *)
    inversion H23. inversion H10. subst.
    pose (EE4 := element_exist 0 vals H28).
    inversion EE4 as [v2']. inversion H6. subst. inversion H28.
    apply eq_sym, length_zero_iff_nil in H9. subst.
    (* assert (v2' = v2 /\ eff2' = []). 
    { *)
      pose (WD := eval_expr_determinism H0 _ _ _ H21). destruct WD. destruct H9.
      inversion H8.
      subst.
    (* } *)
    eapply eval_single, eval_let; auto.
     - exact H.
     - auto.
     - eapply eval_single, eval_let; auto.
       + exact H2.
       + auto.
     (** Destruct application hypothesis *)
       + inversion H29. inversion H13; subst.
         ** pose (WD3 := eval_expr_determinism E2 _ _ _ H25). destruct WD3.
            inversion H9. destruct H11. subst.
            pose (EEA := element_exist _ _ H24).
            inversion EEA as [v1'']. inversion H9. subst. inversion H24.
            pose (EEA2 := element_exist _ _ H14).
            inversion EEA2 as [v2'']. inversion H11. subst. inversion H24.
            apply eq_sym, length_zero_iff_nil in H16. subst.
            pose (EEE := element_exist _ _ H27).
            inversion EEE as [eff1'']. inversion H15. subst. inversion H27.
            pose (EEE2 := element_exist _ _ H18).
            inversion EEE2 as [eff2'']. inversion H16. subst. inversion H27.
            apply eq_sym, length_zero_iff_nil in H20. subst.
            pose (EEI := element_exist _ _ H30).
            inversion EEI as [id1'']. inversion H19. subst. inversion H30.
            pose (EEI2 := element_exist _ _ H31).
            inversion EEI2 as [id2'']. inversion H20. subst. inversion H30.
            apply eq_sym, length_zero_iff_nil in H34. subst.
            clear dependent H24. clear dependent H14. clear dependent H27.
            clear dependent H18. clear dependent H30. clear dependent H31.
            (* assert (v1' = v1 /\ v2' = v2 /\ eff1' = [] /\ eff2' = []).
            { *)
              pose (P := H33 0 Nat.lt_0_2).
              inversion P. inversion H27.
              simpl in H40, H41, H42, H43, H39, H37. subst.
              rewrite get_value_there in H42. 2: congruence. 
              rewrite get_value_here in H42.
              inversion H42.
              subst.

              pose (P2 := H33 1 Nat.lt_1_2).
              inversion P2. inversion H30.
              simpl in H42, H43, H44, H45, H41, H40.
              rewrite get_value_here in H44. inversion H44.
              subst.

            (* } *)
            eapply eval_single, eval_app with (vals := [v1''; v2'']) (eff := [eff2''; eff2''])
                                   (ids := [id2'';id2'']); auto.
            -- exact E1.
            -- auto.
            -- intros. inversion H14. 2: inversion H24.
              ++ simpl. apply eval_single, eval_var. rewrite get_value_there, get_value_here. auto. congruence.
              ++ simpl. eapply eval_single, eval_var. rewrite get_value_here. auto.
              ++ inversion H32.
            -- simpl in H38. exact H38.
         ** eapply eval_single, eval_app_closure_ex; try(reflexivity).
            -- pose (WD := eval_expr_determinism E2 _ _ _ H32). destruct WD. destruct H11. subst.
               exact E1.
         ** inversion H24.
            -- pose (EEA := element_exist _ _  (eq_sym H11)). inversion EEA as [v1''].
               inversion H9. subst.
               inversion H11. apply length_zero_iff_nil in H14. subst. 
               simpl in H38. inversion H38. inversion H16.
            -- inversion H11.
              ++ rewrite H14 in *. simpl in H38. inversion H38. inversion H18.
              ++ inversion H14.
         ** pose (WD := eval_expr_determinism E2 _ _ _ H27).
            destruct WD. destruct H11.
            subst.
            eapply eval_single, eval_app_badfun_ex with (vals := [v1'; v2']) (eff := [eff2; eff2])
                                              (ids := [id'0;id'0]); auto.
           -- exact E1.
           -- intros. inversion H9. 2: inversion H15.
              ++ simpl.
                 apply eval_single, eval_var. rewrite get_value_there, get_value_here. auto. congruence.
              ++ simpl. rewrite H12, H11.
                 apply eval_single, eval_var. rewrite get_value_here. auto.
              ++ inversion H18.
         ** pose (WD := eval_expr_determinism E2 _ _ _ H27).
            inversion WD. destruct H11. subst.
            eapply eval_single, eval_app_badarity_ex with (vals := [v1'; v2']) (eff := [eff2;eff2])
                                   (ids := [id'0; id'0]); auto.
           -- exact E1.
           -- intros. inversion H9. 2: inversion H15.
              ++ simpl.
                 apply eval_single, eval_var. rewrite get_value_there, get_value_here. auto. congruence.
              ++ simpl.
                 rewrite H12, H11.
                 apply eval_single, eval_var. rewrite get_value_here. auto.
              ++ inversion H18.
           -- rewrite <- H24 in H31. auto.
      - subst.
        pose (WD := eval_expr_determinism H0 _ _ _ H27).
        destruct WD. destruct H8. inversion H6.
      - subst.
        pose (WD := eval_expr_determinism H1 _ _ _ H21).
        destruct WD. inversion H5.
        inversion H4.
    * inversion H3. inversion H7. subst.
    pose (EE1 := element_exist 0 vals H22). inversion EE1 as [v1'].
    inversion H4. subst. inversion H22.
    apply eq_sym, length_zero_iff_nil in H6. subst.
    (* assert (v1' = v1 /\ eff1' = []).
    { *)
      pose (WD := eval_expr_determinism H _ _ _ H17). destruct WD. destruct H6. inversion H5.
      subst.
    (* } *)
    inversion H23. inversion H10. subst.
    pose (EE4 := element_exist 0 vals H28).
    inversion EE4 as [v2']. inversion H6. subst. inversion H28.
    apply eq_sym, length_zero_iff_nil in H9. subst.
    (* assert (v2' = v2 /\ eff2' = []). 
    { *)
      pose (WD := eval_expr_determinism H2 _ _ _ H21). destruct WD. destruct H9.
      inversion H8.
      subst.
    (* } *)
    eapply eval_single, eval_let; auto.
     - exact H1.
     - auto.
     - eapply eval_single, eval_let; auto.
       + exact H0.
       + auto.
     (** Destruct application hypothesis *)
       + inversion H29. inversion H13; subst.
         ** pose (WD3 := eval_expr_determinism E1 _ _ _ H25). destruct WD3.
            inversion H9. destruct H11. subst.
            pose (EEA := element_exist _ _ H24).
            inversion EEA as [v1'']. inversion H9. subst. inversion H24.
            pose (EEA2 := element_exist _ _ H14).
            inversion EEA2 as [v2'']. inversion H11. subst. inversion H24.
            apply eq_sym, length_zero_iff_nil in H16. subst.
            pose (EEE := element_exist _ _ H27).
            inversion EEE as [eff1'']. inversion H15. subst. inversion H27.
            pose (EEE2 := element_exist _ _ H18).
            inversion EEE2 as [eff2'']. inversion H16. subst. inversion H27.
            apply eq_sym, length_zero_iff_nil in H20. subst.
            pose (EEI := element_exist _ _ H30).
            inversion EEI as [id1'']. inversion H19. subst. inversion H30.
            pose (EEI2 := element_exist _ _ H31).
            inversion EEI2 as [id2'']. inversion H20. subst. inversion H30.
            apply eq_sym, length_zero_iff_nil in H34. subst.
            clear dependent H24. clear dependent H14. clear dependent H27.
            clear dependent H18. clear dependent H30. clear dependent H31.
            (* assert (v1' = v1 /\ v2' = v2 /\ eff1' = [] /\ eff2' = []).
            { *)
              pose (P := H33 0 Nat.lt_0_2).
              inversion P. inversion H27.
              simpl in H40, H41, H42, H43, H39, H37. subst.
              rewrite get_value_here in H42.
              inversion H42.
              subst.

              pose (P2 := H33 1 Nat.lt_1_2).
              inversion P2. inversion H30.
              simpl in H42, H43, H44, H45, H41, H40.
              rewrite get_value_there in H44. 2: congruence. 
              rewrite get_value_here in H44. inversion H44.
              subst.

            (* } *)
            eapply eval_single, eval_app with (vals := [v1''; v2'']) (eff := [eff2''; eff2''])
                                   (ids := [id2'';id2'']); auto.
            -- exact E2.
            -- auto.
            -- intros. inversion H14. 2: inversion H24.
              ++ simpl. apply eval_single, eval_var. rewrite get_value_here. auto.
              ++ simpl. eapply eval_single, eval_var. rewrite get_value_there, get_value_here. auto. congruence.
              ++ inversion H32.
            -- simpl in H38. exact H38.
         ** eapply eval_single, eval_app_closure_ex; try(reflexivity).
            -- pose (WD := eval_expr_determinism E1 _ _ _ H32). destruct WD. destruct H11. subst.
               exact E2.
         ** inversion H24.
            -- pose (EEA := element_exist _ _  (eq_sym H11)). inversion EEA as [v1''].
               inversion H9. subst.
               inversion H11. apply length_zero_iff_nil in H14. subst. 
               simpl in H38. inversion H38. inversion H16.
            -- inversion H11.
              ++ rewrite H14 in *. simpl in H38. inversion H38. inversion H18.
              ++ inversion H14.
         ** pose (WD := eval_expr_determinism E1 _ _ _ H27).
            destruct WD. destruct H11.
            subst.
            eapply eval_single, eval_app_badfun_ex with (vals := [v2'; v1']) (eff := [eff2; eff2])
                                              (ids := [id'0;id'0]); auto.
           -- exact E2.
           -- intros. inversion H9. 2: inversion H15.
              ++ simpl.
                 apply eval_single, eval_var. rewrite get_value_here. auto.
              ++ simpl. rewrite H12, H11.
                 apply eval_single, eval_var. rewrite get_value_there, get_value_here. auto. congruence.
              ++ inversion H18.
         ** pose (WD := eval_expr_determinism E1 _ _ _ H27).
            inversion WD. destruct H11. subst.
            eapply eval_single, eval_app_badarity_ex with (vals := [v2'; v1']) (eff := [eff2;eff2])
                                   (ids := [id'0; id'0]); auto.
           -- exact E2.
           -- intros. inversion H9. 2: inversion H15.
              ++ simpl.
                 apply eval_single, eval_var. rewrite get_value_here. auto.
              ++ simpl.
                 rewrite H12, H11.
                 apply eval_single, eval_var. rewrite get_value_there, get_value_here. auto. congruence.
              ++ inversion H18.
           -- rewrite <- H24 in H31. auto.
      - subst.
        pose (WD := eval_expr_determinism H2 _ _ _ H27).
        destruct WD. destruct H8. inversion H6.
      - subst.
        pose (WD := eval_expr_determinism H _ _ _ H21).
        destruct WD. inversion H5.
        inversion H4.
Qed.

End Equivalence_Proofs.