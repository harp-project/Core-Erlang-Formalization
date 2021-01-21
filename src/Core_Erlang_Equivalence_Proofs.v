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
  inversion H1. subst.
  pose (EE1 := element_exist _ _ H4).
  inversion EE1. inversion H2. subst. inversion H4.
  pose (EE2 := element_exist 0 x0 H8).
  inversion EE2. inversion H3. subst. simpl in H4. inversion H4.
  apply eq_sym, length_zero_iff_nil in H11. subst.
  pose (WD1 := determinism H).
  pose (WD2 := determinism H0).
  pose (P1 := H7 0 Nat.lt_0_2).
  pose (P2 := H7 1 Nat.lt_1_2).
  apply WD1 in P1; inversion P1. inversion H9.
  destruct H11. subst.
  simpl in P2, H11, H12.
  rewrite <- H11, <- H12 in P2. subst.
  apply WD2 in P2. inversion P2. destruct H13.
  inversion H9. inversion H12. rewrite <- H13, <- H14, H17 in *. subst.
  eapply eval_call with (vals := [x3; x]) (eff := [[];[]]) (ids := [nth 0 ids 0; nth 0 ids 0]); auto.
  * intros. inversion H16.
    - assumption.
    - inversion H18.
      + simpl. assumption.
      + inversion H20.
  * rewrite (@plus_comm_basic x x3 t). 
      - reflexivity.
      - simpl last.
        pose (EE3 := element_exist _ _ H5).
        inversion EE3. inversion H16.
        subst. inversion H5.
        pose (EE4 := element_exist _ _ H18).
        inversion EE4. inversion H17.
        subst. inversion H5. apply eq_sym, length_zero_iff_nil in H20. subst.
        simpl in H10, H11, H13. subst.
        exact H10.
Qed.


Example let_1_comm (e1 e2 : Expression) (t x1 x2 : Value) (id : nat) :
  |[], id, e1, []| -e> |id, inl [x1], []| ->
  | [(inl "X"%string, x1)], id, e2, []| -e> |id, inl [x2], []| ->
  |[], id, ELet ["X"%string] e1 (ECall "+"%string [EVar "X"%string ; e2]), []| 
  -e> | id, inl [t], []| ->
  |[], id, ELet ["X"%string] e1 (ECall "+"%string [e2 ; EVar "X"%string]), []| 
  -e> |id, inl [t], []|.
Proof.
  * intros. inversion H1. subst.
    pose (EE1 := element_exist 0 vals H12).
    inversion EE1. inversion H2. subst.
    inversion H12. apply eq_sym, length_zero_iff_nil in H4. subst.
    pose (P := determinism H7 _ _ _ H).
    destruct P, H4. inversion H3. subst.
    eapply eval_let; auto.
    - exact H7.
    - reflexivity.
    - eapply (call_comm _ _ _ _ _ _ _ _ _ H13).
      Unshelve.
      exact x1.
      exact x2.
      apply eval_var. simpl. auto.
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
  pose (DET := determinism P _ _ _ H2). inversion DET. inversion H3. reflexivity.
Qed.

Example let_1_comm_2_list (env: Environment) (e1 e2 : Expression) (t t' v1 v2 : Value) 
   (eff eff1 eff2 : SideEffectList) (A B : Var) (VarHyp : A <> B) (id id1 id2 : nat)
(Hypo1 : |env, id, e1, eff| -e> | id + id1, inl [v1], eff ++ eff1|)
(Hypo2 : |env, id + id2, e1, eff ++ eff2| -e> | id + id1 + id2, inl [v1], eff ++ eff2 ++ eff1|)
(Hypo1' : |env, id, e2, eff| -e> | id + id2, inl [v2], eff ++ eff2|)
(Hypo2' : |env, id + id1, e2, eff ++ eff1| -e> | id + id2 + id1, inl [v2], eff ++ eff1 ++ eff2|) :
|env, id, ELet [A; B] (EValues [e1; e2])
     (ECall "+"%string [EVar A ; EVar B]), eff| -e> |id + id1 + id2, inl [t], eff ++ eff1 ++ eff2|
->
|env, id, ELet [A; B] (EValues [e2; e1])
     (ECall "+"%string [EVar A ; EVar B]), eff| -e> |id + id2 + id1, inl [t'], eff ++ eff2 ++ eff1|
->
t = t'.
Proof.
  intros.
  (* FROM LET HYPO1 *)
  inversion H. subst. simpl in H11.
  pose (EE1 := element_exist 1 vals H11).
  inversion EE1 as [v1']. inversion H1. subst. inversion H11.
  pose (EE2 := element_exist 0 x H3).
  inversion EE2 as [v2']. inversion H2. subst. inversion H11.
  apply eq_sym, length_zero_iff_nil in H5. subst.
  inversion H6. subst.
  pose (EE3 := element_exist _ _ H8). inversion EE3 as [eff1']. inversion H4. subst. inversion H8.
  pose (EE4 := element_exist _ _ H13). inversion EE4 as [eff2']. inversion H5. subst. inversion H8.
  apply eq_sym, length_zero_iff_nil in H15. subst.
  pose (EE5 := element_exist _ _ H9). inversion EE5 as [id1']. inversion H14. subst. inversion H9.
  pose (EE6 := element_exist _ _ H16). inversion EE6 as [id2']. inversion H15. subst. inversion H9.
  apply eq_sym, length_zero_iff_nil in H18. subst.
  (* FROM LET HYPO2 *)
  inversion H0. subst.
  pose (EE1' := element_exist _ _ H27). inversion EE1' as [v2'']. inversion H17. subst. inversion H27.
  pose (EE2' := element_exist _ _ H19). inversion EE2' as [v1'']. inversion H18. subst. inversion H27.
  apply eq_sym, length_zero_iff_nil in H21. subst.
  inversion H22. subst.
  pose (EE3' := element_exist _ _ H24). inversion EE3' as [eff2'']. inversion H20. subst. inversion H24.
  pose (EE4' := element_exist _ _ H29). inversion EE4' as [eff1'']. inversion H21. subst. inversion H24.
  apply eq_sym, length_zero_iff_nil in H31. subst.

  pose (EE5' := element_exist _ _ H25). inversion EE5' as [id2'']. inversion H30. subst. inversion H25.
  pose (EE6' := element_exist _ _ H32). inversion EE6' as [id1'']. inversion H31. subst. inversion H25.
  apply eq_sym, length_zero_iff_nil in H34. subst.
  clear EE1. clear EE2. clear EE3. clear EE4. clear EE5. clear EE6.
  clear EE1'. clear EE2'. clear EE3'. clear EE4'. clear EE5'. clear EE6'.
  
  (* assert (v1' = v1 /\ eff1' = eff1).
  { *)
    pose (P1 := H10 0 Nat.lt_0_2).
    simpl in P1.
    pose (WD1 := determinism Hypo1).
    pose (PC1 := WD1 _ _ _ P1).
    destruct PC1. destruct H34. inversion H33. subst.
  (* } *)
  
  (* assert (v2'' = v2 /\ eff2'' = eff2).
  { *)
    pose (P2 := H26 0 Nat.lt_0_2).
    simpl in P2.
    pose (WD2 := determinism Hypo1').
    pose (PC2 := WD2 _ _ _ P2).
    destruct PC2. destruct H35. inversion H34. subst.
  (* } *)

  (* assert (v1'' = v1 /\ v2' = v2 /\ eff1'' = eff1 /\ eff2' = eff2).
  { *)
    pose (P3 := H26 1 Nat.lt_1_2).
    simpl in P3.
    pose (WD3 := determinism Hypo2).
    pose (PC3 := WD3 _ _ _ P3).
    inversion PC3. inversion H35. destruct H36. subst.
    pose (P4 := H10 1 Nat.lt_1_2).
    simpl in P4.
    pose (WD4 := determinism Hypo2').
    pose (PC4 := WD4 _ _ _ P4).
    inversion PC4. destruct H37. inversion H36. subst.
  (* } *)
  clear dependent P1. clear dependent P2. clear dependent P3. clear dependent P4.

  (* FROM CALL HYPOS *)
 (* FROM CALL HYPO1 *)
  inversion H12. subst.
  pose (EC1 := element_exist _ _ H39). inversion EC1 as [v10]. inversion H37. subst. 
  inversion H39.
  pose (EC2 := element_exist _ _ H43). inversion EC2 as [v20]. inversion H38. subst. 
  inversion H39.
  apply eq_sym, length_zero_iff_nil in H46. subst.
  pose (EC3 := element_exist _ _ H40). inversion EC3 as [eff10]. inversion H44. subst.
  inversion H40.
  pose (EC4 := element_exist _ _ H47). inversion EC4 as [eff20]. inversion H46. subst.
  inversion H40.
  apply eq_sym, length_zero_iff_nil in H49. subst.
  pose (EC5 := element_exist _ _ H41). inversion EC5 as [id10]. inversion H48. subst.
  inversion H41.
  pose (EC6 := element_exist _ _ H51). inversion EC6 as [id20]. inversion H49. subst.
  inversion H41.
  apply eq_sym, length_zero_iff_nil in H53. subst.
  (* FROM CALL HYPO2 *)
  inversion H28. subst.
  pose (EC1' := element_exist _ _ H54). inversion EC1' as [v20']. inversion H52. subst.
  inversion H54.
  pose (EC2' := element_exist _ _ H58). inversion EC2' as [v10']. inversion H53. subst.
  inversion H54.
  apply eq_sym, length_zero_iff_nil in H61. subst.
  pose (EC3' := element_exist _ _ H55). inversion EC3' as [eff20']. inversion H59. subst.
  inversion H55.
  pose (EC4' := element_exist _ _ H62). inversion EC4' as [eff10']. inversion H61. subst.
  inversion H55.
  apply eq_sym, length_zero_iff_nil in H64. subst.
  pose (EC5' := element_exist _ _ H56). inversion EC5' as [id20']. inversion H63. subst.
  inversion H56.
  pose (EC6' := element_exist _ _ H66). inversion EC6' as [id10']. inversion H64. subst.
  inversion H56.
  apply eq_sym, length_zero_iff_nil in H68. subst.


  pose (PUM1 := plus_effect_unmodified _ _ _ H45).
  pose (PUM2 := plus_effect_unmodified _ _ _ H60).
  inversion PUM1. inversion PUM2. simpl in H67, H68. subst.
  (* EVERYTHING IS EQUAL *)
  (* assert (v1' = v1 /\ v1'' = v1 /\ v2' = v2 /\ v2'' = v2).
  { *)
    pose (P1 := H42 0 Nat.lt_0_2).
    pose (P2 := H42 1 Nat.lt_1_2).
    pose (P1' := H57 1 Nat.lt_1_2).
    pose (P2' := H57 0 Nat.lt_0_2).
    simpl in P1, P2, P1', P2'.
    inversion P1. inversion P2. inversion P1'. inversion P2'. subst.
    (* inversion H73. inversion H81. inversion H89. inversion H97. subst. *)
    rewrite get_value_there in H73, H97.
    2-3 : congruence.
    rewrite get_value_here in H73, H81, H97, H89.
    inversion H73. inversion H81. inversion H89. inversion H97. subst.
(* } *)
  clear PUM1. clear PUM2.
  apply (plus_comm_basic_value _ (eff ++ eff2 ++ eff1)) in H45.
  simpl last in H60.
  rewrite H45 in H60. inversion H60.
  reflexivity.
Qed.

Example exp_to_fun (e : Expression) (x : Var) (id id' : nat):
  strong_equivalent e (ELet [x] (EFun [] e) (EApp (EVar x) [])) (S id) id' id id'.
Proof.
  unfold strong_equivalent.
  split; intros.
  * eapply eval_let; auto.
    - apply eval_fun.
    - reflexivity.
    - eapply eval_app with (vals := []) (eff := []) (ids := []); auto.
      + eapply eval_var. simpl. rewrite get_value_here. reflexivity.
      + auto.
      + intros. inversion H0.
      + unfold get_env. simpl. auto.
  * inversion H; subst.
    - pose (EE1 := element_exist 0 vals H10). inversion EE1. inversion H0. subst.
      inversion H10. apply eq_sym, length_zero_iff_nil in H2. subst.
      inversion H5. subst.

      inversion H11; subst.
      + apply eq_sym, length_zero_iff_nil in H3. subst.
        apply eq_sym, length_zero_iff_nil in H8. subst.
        apply eq_sym, length_zero_iff_nil in H7. subst.
        inversion H4. subst. simpl in H12.
        rewrite get_value_here in H12. inversion H12. subst.
        unfold get_env in H18. simpl in H18. assumption.
      + inversion H12.
      + inversion H3.
      + inversion H7. subst.
        simpl in H16. rewrite get_value_here in H16. inversion H16. subst.
        congruence.
      + subst. inversion H7. subst.
        simpl in H16. rewrite get_value_here in H16. inversion H16. subst.
        contradiction.
    - inversion H9.
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
        (ECall "+"%string [EVar A ; EVar B])), eff| -e>
  | id0 + id1 + id2, inl [t], eff ++ eff1 ++ eff2|
->
  |env, id0, ELet [A] e2 (ELet [B] e1
        (ECall "+"%string [EVar A ; EVar B])), eff| -e>
  | id0 + id2 + id1, inl [t], eff ++ eff2 ++ eff1|
.
Proof.
  * intros. inversion H3. subst.
    pose (EE1 := element_exist 0 vals H14).
    inversion EE1 as [x'].
    inversion H4. subst. 
    inversion H14. apply eq_sym, length_zero_iff_nil in H6. subst.
(*     assert (x' = x /\ eff1' = eff ++ eff1 /\ id1' = (id0 + id1)%nat).
    { *)
      pose (WD := determinism H1 _ _ _ H9). destruct WD. destruct H6. inversion H5.
      subst.
(*     } *)
    inversion H15. subst.
    pose (EE1' := element_exist 0 vals H19).
    inversion EE1' as [x0'].
    inversion H6. subst. inversion H19.
    apply eq_sym, length_zero_iff_nil in H8.
(*     assert (x0' = x0 /\ eff2' = eff ++ eff1 ++ eff2 /\ id2' = (id0 + id1 + id2)%nat).
    { *)
      pose (WD := determinism H0 _ _ _ H12). 
      destruct WD. destruct H10. inversion H7.
      subst.
(*     } *)
   (*proving starts*)
   eapply eval_let; auto.
   - exact H.
   - auto.
   - eapply eval_let; auto.
     + exact H2.
     + auto.
   (* call information *)
     + inversion H20. subst.
       pose (EC1 := element_exist 1 _ H11).
       pose (EC2 := element_exist 1 _ H13).
       pose (EC3 := element_exist 1 _ H16).
       inversion EC1 as [x'']. inversion EC2 as [eff1'']. inversion EC3 as [id1''].
       inversion H8. inversion H10. inversion H21. subst.
       inversion H11. inversion H13. inversion H16.
       pose (EC1' := element_exist 0 _ H24).
       pose (EC2' := element_exist 0 _ H25).
       pose (EC3' := element_exist 0 _ H26).
       inversion EC1' as [x0'']. inversion EC2' as [eff2'']. inversion EC3' as [id2''].
       inversion H22. inversion H27. inversion H29. subst.
       inversion H24. inversion H25. inversion H26.
       apply eq_sym, length_zero_iff_nil in H31.
       apply eq_sym, length_zero_iff_nil in H32.
       apply eq_sym, length_zero_iff_nil in H33. subst.

         pose (P1' := H18 0 Nat.lt_0_2).
         pose (P2' := H18 1 Nat.lt_1_2).
         inversion P1'. inversion P2'. simpl in H42, H43, H41, H45. subst.

         simpl in H36, H44.

         rewrite get_value_there in H36. 2: congruence.
         rewrite get_value_here in H36. inversion H36.
         rewrite get_value_here in H44. inversion H44. subst.

       (* BACK TO CALL PROOF *)
       eapply eval_call with (vals := [x0'' ; x'']) (eff := [eff ++ eff2 ++ eff1;eff ++ eff2 ++ eff1]) 
                    (ids := [(id0 + id2 + id1)%nat; (id0 + id2 + id1)%nat]); auto.
       ** intros. inversion H30. 2: inversion H32.
         -- simpl. eapply eval_var. rewrite get_value_here. auto.
         -- simpl. eapply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
         -- inversion H34.
       ** apply plus_comm_basic_value with (eff0 := eff ++ eff1 ++ eff2).
          simpl in H35, H37. subst. assumption.
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
        (ECall "+"%string [EVar A ; EVar B])), eff| -e> 
  | id0 + id1 + id2, inl [t], eff ++ eff1 ++ eff2|
<->
  |env, id0, ELet [A] e2 (ELet [B] e1
        (ECall "+"%string [EVar A ; EVar B])), eff| -e>
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
        (ECall "+"%string [EVar A ; EVar B])), eff| -e>
  |id0 + id1 + id2, inl [t], eff ++ eff1 ++ eff2|
<->
  |env, id0, ELet [B] e2 (ELet [A] e1
        (ECall "+"%string [EVar A ; EVar B])), eff| -e>
  |id0 + id2 + id1, inl [t], eff ++ eff2 ++ eff1|
.
Proof.
  split.
  * intros. inversion H3. subst.
    pose (EE1 := element_exist 0 vals H14).
    inversion EE1 as [x'].
    inversion H4. subst.
    inversion H14. apply eq_sym, length_zero_iff_nil in H6. subst.
(*     assert (x' = x /\ eff1' = eff ++ eff1 /\ id1' = (id0 + id1)%nat).
    { *)
      pose (WD := determinism H1 _ _ _ H9). destruct WD. destruct H6. inversion H5.
      subst.
(*     } *)
    inversion H15. subst.
    pose (EE1' := element_exist 0 vals H19).
    inversion EE1' as [x0'].
    inversion H6. subst. inversion H19.
    apply eq_sym, length_zero_iff_nil in H8. subst.
(*     assert (x0' = x0 /\ eff2' = eff ++ eff1 ++ eff2 /\ id2' = (id0 + id1 + id2)%nat).
    { *)
      pose (WD := determinism H0 _ _ _ H12). 
      destruct WD. destruct H8. inversion H7.
      subst.
(*     } *)
   (*proving starts*)
   eapply eval_let; auto.
   - exact H.
   - auto.
   - eapply eval_let; auto.
     + exact H2.
     + auto.
   (* call information *)
     + inversion H20. subst.
       pose (EC1 := element_exist 1 _ H11).
       pose (EC2 := element_exist 1 _ H13).
       pose (EC3 := element_exist 1 _ H16).
       inversion EC1 as [x'']. inversion EC2 as [eff1'']. inversion EC3 as [id1''].
       inversion H8. inversion H10. inversion H18. subst.
       inversion H11. inversion H13. inversion H16.
       pose (EC1' := element_exist 0 _ H23).
       pose (EC2' := element_exist 0 _ H24).
       pose (EC3' := element_exist 0 _ H25).
       inversion EC1' as [x0'']. inversion EC2' as [eff2'']. inversion EC3' as [id2''].
       inversion H21. inversion H26. inversion H28. subst.
       inversion H11. inversion H13. inversion H16.
       apply eq_sym, length_zero_iff_nil in H30.
       apply eq_sym, length_zero_iff_nil in H31.
       apply eq_sym, length_zero_iff_nil in H32. subst.

         pose (P1' := H17 0 Nat.lt_0_2).
         pose (P2' := H17 1 Nat.lt_1_2).
         inversion P1'. inversion P2'. simpl in H34, H36, H43, H38, H41, H42, H44, H35, H43. subst.

         rewrite get_value_there in H35. 2: congruence.
         rewrite get_value_here in H35. inversion H35.
         rewrite get_value_here in H43. inversion H43. subst.

       (* BACK TO CALL PROOF *)
       eapply eval_call with (vals := [x'' ; x0'']) (eff := [eff ++ eff2 ++ eff1;eff ++ eff2 ++ eff1]) 
                    (ids := [(id0 + id2 + id1)%nat; (id0 + id2 + id1)%nat]); auto.
       ** intros. inversion H29. 2: inversion H31.
         -- simpl. eapply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
         -- simpl. eapply eval_var. rewrite get_value_here. auto.
         -- inversion H33.
       ** apply plus_effect_changeable with (eff0 := eff ++ eff1 ++ eff2). assumption.
  * intros. inversion H3. subst.
    pose (EE1 := element_exist 0 vals H14).
    inversion EE1 as [x'].
    inversion H4. subst.
    inversion H14. apply eq_sym, length_zero_iff_nil in H6. subst.
(*     assert (x' = x /\ eff1' = eff ++ eff1 /\ id1' = (id0 + id1)%nat).
    { *)
      pose (WD := determinism H _ _ _ H9). destruct WD. destruct H6. inversion H5.
      subst.
(*     } *)
    inversion H15. subst.
    pose (EE1' := element_exist 0 vals H19).
    inversion EE1' as [x0'].
    inversion H6. subst. inversion H19.
    apply eq_sym, length_zero_iff_nil in H8. subst.
(*     assert (x0' = x0 /\ eff2' = eff ++ eff1 ++ eff2 /\ id2' = (id0 + id1 + id2)%nat).
    { *)
      pose (WD := determinism H2 _ _ _ H12). 
      destruct WD. destruct H8. inversion H7.
      subst.
(*     } *)
   (*proving starts*)
   eapply eval_let; auto.
   - exact H1.
   - auto.
   - eapply eval_let; auto.
     + exact H0.
     + auto.
   (* call information *)
     + inversion H20. subst.
       pose (EC1 := element_exist 1 _ H11).
       pose (EC2 := element_exist 1 _ H13).
       pose (EC3 := element_exist 1 _ H16).
       inversion EC1 as [x'']. inversion EC2 as [eff1'']. inversion EC3 as [id1''].
       inversion H8. inversion H10. inversion H18. subst.
       inversion H11. inversion H13. inversion H16.
       pose (EC1' := element_exist 0 _ H23).
       pose (EC2' := element_exist 0 _ H24).
       pose (EC3' := element_exist 0 _ H25).
       inversion EC1' as [x0'']. inversion EC2' as [eff2'']. inversion EC3' as [id2''].
       inversion H21. inversion H26. inversion H28. subst.
       inversion H11. inversion H13. inversion H16.
       apply eq_sym, length_zero_iff_nil in H30.
       apply eq_sym, length_zero_iff_nil in H31.
       apply eq_sym, length_zero_iff_nil in H32. subst.

         pose (P1' := H17 0 Nat.lt_0_2).
         pose (P2' := H17 1 Nat.lt_1_2).
         inversion P1'. inversion P2'. simpl in H34, H36, H43, H38, H41, H42, H44, H35, H43. subst.

         rewrite get_value_there in H43. 2: congruence.
         rewrite get_value_here in H43. inversion H43.
         rewrite get_value_here in H35. inversion H35. subst.

       (* BACK TO CALL PROOF *)
       eapply eval_call with (vals := [x'' ; x0'']) (eff := [eff ++ eff1 ++ eff2;eff ++ eff1 ++ eff2]) 
                    (ids := [(id0 + id1 + id2)%nat; (id0 + id1 + id2)%nat]); auto.
       ** intros. inversion H29. 2: inversion H31.
         -- simpl. eapply eval_var. rewrite get_value_here. auto.
         -- simpl. eapply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
         -- inversion H33.
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
        (EApp exp [EVar A ; EVar B])), eff| -e> |id , t, eff|
  <->
  |env, id, ELet [B] e2 (ELet [A] e1
        (EApp exp [EVar A ; EVar B])), eff| -e> |id, t, eff |
.
Proof.
  split;intros.
   (** Deconstruct ELet-s *)
  * inversion H3. subst.
    pose (EE1 := element_exist 0 vals H14). inversion EE1 as [v1'].
    inversion H4. subst. inversion H14.
    apply eq_sym, length_zero_iff_nil in H6. subst.
    (* assert (v1' = v1 /\ eff1' = []).
    { *)
      pose (WD := determinism H1 _ _ _ H9). destruct WD. destruct H6. inversion H5.
      subst.
    (* } *)
    inversion H15. subst.
    pose (EE4 := element_exist 0 vals H19).
    inversion EE4 as [v2']. inversion H6. subst. inversion H19.
    apply eq_sym, length_zero_iff_nil in H8. subst.
    (* assert (v2' = v2 /\ eff2' = []). 
    { *)
      pose (WD := determinism H0 _ _ _ H12). destruct WD. destruct H8.
      inversion H7.
      subst.
    (* } *)
    eapply eval_let; auto.
     - exact H.
     - auto.
     - eapply eval_let; auto.
       + exact H2.
       + auto.
     (** Destruct application hypothesis *)
       + inversion H20; subst.
         ** pose (WD3 := determinism E2 _ _ _ H13). destruct WD3.
            inversion H8. destruct H10. subst.
            pose (EEA := element_exist _ _ H11).
            inversion EEA as [v1'']. inversion H8. subst. inversion H11.
            pose (EEA2 := element_exist _ _ H22).
            inversion EEA2 as [v2'']. inversion H10. subst. inversion H11.
            apply eq_sym, length_zero_iff_nil in H25. subst.
            pose (EEE := element_exist _ _ H17).
            inversion EEE as [eff1'']. inversion H24. subst. inversion H17.
            pose (EEE2 := element_exist _ _ H26).
            inversion EEE2 as [eff2'']. inversion H25. subst. inversion H17.
            apply eq_sym, length_zero_iff_nil in H29. subst.
            pose (EEI := element_exist _ _ H18).
            inversion EEI as [id1'']. inversion H27. subst. inversion H18.
            pose (EEI2 := element_exist _ _ H30).
            inversion EEI2 as [id2'']. inversion H29. subst. inversion H18.
            apply eq_sym, length_zero_iff_nil in H32. subst.
            clear dependent EEA. clear dependent EEA2. clear dependent EEE.
            clear dependent EEE2. clear dependent EEI. clear dependent EEI2.
            (* assert (v1' = v1 /\ v2' = v2 /\ eff1' = [] /\ eff2' = []).
            { *)
              pose (P := H23 0 Nat.lt_0_2).
              inversion P.
              simpl in H37, H32, H33, H35, H36, H38. subst.
              rewrite get_value_there in H37. 2: congruence. 
              rewrite get_value_here in H37.
              inversion H37.
              subst.

              pose (P2 := H23 1 Nat.lt_1_2).
              inversion P2.
              simpl in H38, H33, H35, H36, H39, H32.
              rewrite get_value_here in H38. inversion H38.
              subst.

            (* } *)
            eapply eval_app with (vals := [v1''; v2'']) (eff := [eff2''; eff2''])
                                   (ids := [id2'';id2'']); auto.
            -- exact E1.
            -- auto.
            -- intros. inversion H31. 2: inversion H33.
              ++ simpl. apply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
              ++ simpl. eapply eval_var. rewrite get_value_here. auto.
              ++ inversion H35.
            -- simpl in H28. exact H28.
         ** eapply eval_app_closure_ex; try(reflexivity).
            -- pose (WD := determinism E2 _ _ _ H22). destruct WD. destruct H10. subst.
               exact E1.
         ** inversion H11.
            -- pose (EEA := element_exist _ _  (eq_sym H10)). inversion EEA as [v1''].
               inversion H8. subst.
               inversion H10. apply length_zero_iff_nil in H21. subst. 
               simpl in H28. inversion H28.
            -- inversion H10.
              ++ rewrite H21 in *. simpl in H28. inversion H28.
              ++ inversion H21.
         ** pose (WD := determinism E2 _ _ _ H17).
            destruct WD. destruct H10.
            subst.
            eapply eval_app_badfun_ex with (vals := [v1'; v2']) (eff := [eff2; eff2])
                                              (ids := [id';id']); auto.
           -- exact E1.
           -- intros. inversion H8. 2: inversion H24.
              ++ simpl.
                 apply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
              ++ simpl. rewrite H10, H22.
                 apply eval_var. rewrite get_value_here. auto.
              ++ inversion H26.
         ** pose (WD := determinism E2 _ _ _ H17).
            inversion WD. destruct H10. subst.
            eapply eval_app_badarity_ex with (vals := [v1'; v2']) (eff := [eff2;eff2])
                                   (ids := [id'; id']); auto.
           -- exact E1.
           -- intros. inversion H8. 2: inversion H24.
              ++ simpl.
                 apply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
              ++ simpl.
                 rewrite H10, H22.
                 apply eval_var. rewrite get_value_here. auto.
              ++ inversion H26.
           -- rewrite <- H11 in H21. auto.
      - subst.
        pose (WD := determinism H0 _ _ _ H18).
        destruct WD. destruct H7. inversion H6.
      - subst.
        pose (WD := determinism H1 _ _ _ H13).
        destruct WD. inversion H4.
  * inversion H3. subst.
    pose (EE1 := element_exist 0 vals H14). inversion EE1 as [v1'].
    inversion H4. subst. inversion H14.
    apply eq_sym, length_zero_iff_nil in H6. subst.
    (* assert (v1' = v1 /\ eff1' = []).
    { *)
      pose (WD := determinism H _ _ _ H9). destruct WD. destruct H6. inversion H5.
      subst.
    (* } *)
    inversion H15. subst.
    pose (EE4 := element_exist 0 vals H19).
    inversion EE4 as [v2']. inversion H6. subst. inversion H19.
    apply eq_sym, length_zero_iff_nil in H8. subst.
    (* assert (v2' = v2 /\ eff2' = []). 
    { *)
      pose (WD := determinism H2 _ _ _ H12). destruct WD. destruct H8.
      inversion H7.
      subst.
    (* } *)
    eapply eval_let; auto.
     - exact H1.
     - auto.
     - eapply eval_let; auto.
       + exact H0.
       + auto.
     (** Destruct application hypothesis *)
       + inversion H20; subst.
         ** pose (WD3 := determinism E1 _ _ _ H13). destruct WD3.
            inversion H8. destruct H10. subst.
            pose (EEA := element_exist _ _ H11).
            inversion EEA as [v1'']. inversion H8. subst. inversion H11.
            pose (EEA2 := element_exist _ _ H22).
            inversion EEA2 as [v2'']. inversion H10. subst. inversion H11.
            apply eq_sym, length_zero_iff_nil in H25. subst.
            pose (EEE := element_exist _ _ H17).
            inversion EEE as [eff1'']. inversion H24. subst. inversion H17.
            pose (EEE2 := element_exist _ _ H26).
            inversion EEE2 as [eff2'']. inversion H25. subst. inversion H17.
            apply eq_sym, length_zero_iff_nil in H29. subst.
            pose (EEI := element_exist _ _ H18).
            inversion EEI as [id1'']. inversion H27. subst. inversion H18.
            pose (EEI2 := element_exist _ _ H30).
            inversion EEI2 as [id2'']. inversion H29. subst. inversion H18.
            apply eq_sym, length_zero_iff_nil in H32. subst.
            clear dependent EEA. clear dependent EEA2. clear dependent EEE.
            clear dependent EEE2. clear dependent EEI. clear dependent EEI2.
            (* assert (v1' = v1 /\ v2' = v2 /\ eff1' = [] /\ eff2' = []).
            { *)
              pose (P := H23 0 Nat.lt_0_2).
              inversion P.
              simpl in H37, H32, H33, H35, H36, H38. subst.
              rewrite get_value_here in H37.
              inversion H37.
              subst.

              pose (P2 := H23 1 Nat.lt_1_2).
              inversion P2.
              simpl in H38, H33, H35, H36, H39, H32.
              rewrite get_value_there in H38. 2: congruence. 
              rewrite get_value_here in H38. inversion H38.
              subst.

            (* } *)
            eapply eval_app with (vals := [v1''; v2'']) (eff := [eff2''; eff2''])
                                   (ids := [id2'';id2'']); auto.
            -- exact E2.
            -- auto.
            -- intros. inversion H31. 2: inversion H33.
              ++ simpl. eapply eval_var. rewrite get_value_here. auto.
              ++ simpl. apply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
              ++ inversion H35.
            -- simpl in H28. exact H28.
         ** eapply eval_app_closure_ex; try(reflexivity).
            -- pose (WD := determinism E1 _ _ _ H22). destruct WD. destruct H10. subst.
               exact E2.
         ** inversion H11.
            -- pose (EEA := element_exist _ _  (eq_sym H10)). inversion EEA as [v1''].
               inversion H8. subst.
               inversion H10. apply length_zero_iff_nil in H21. subst. 
               simpl in H28. inversion H28.
            -- inversion H10.
              ++ rewrite H21 in *. simpl in H28. inversion H28.
              ++ inversion H21.
         ** pose (WD := determinism E1 _ _ _ H17).
            destruct WD. destruct H10.
            subst.
            eapply eval_app_badfun_ex with (vals := [v2'; v1']) (eff := [eff2; eff2])
                                              (ids := [id';id']); auto.
           -- exact E2.
           -- intros. inversion H8. 2: inversion H24.
              ++ simpl. (* rewrite H10, H22. *)
                 apply eval_var. rewrite get_value_here. auto.
              ++ simpl. rewrite H10, H22. 
                 apply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
              ++ inversion H26.
         ** pose (WD := determinism E1 _ _ _ H17).
            inversion WD. destruct H10. subst.
            eapply eval_app_badarity_ex with (vals := [v2'; v1']) (eff := [eff2;eff2])
                                   (ids := [id'; id']); auto.
           -- exact E2.
           -- intros. inversion H8. 2: inversion H24.
              ++ simpl.
                 apply eval_var. rewrite get_value_here. auto.
              ++ simpl. rewrite H10, H22.
                 apply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
              ++ inversion H26.
           -- rewrite <- H11 in H21. auto.
      - subst.
        pose (WD := determinism H2 _ _ _ H18).
        destruct WD. destruct H7. inversion H6.
      - subst.
        pose (WD := determinism H _ _ _ H13).
        destruct WD. inversion H4.
Qed.

End Equivalence_Proofs.