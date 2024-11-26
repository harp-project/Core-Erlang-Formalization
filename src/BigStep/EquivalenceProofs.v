(**
  This file contains a number of strict program equivalence examples.
*)

From CoreErlang.BigStep Require Export WeakEquivalence.
From CoreErlang.BigStep Require Export SemanticsProofs.

Import ListNotations.

Theorem equivalence : forall env modules own_module id eff e1 e2 id1 id2 res1 res2 eff1 eff2,
  | env, modules, own_module, id, e1, eff | -e> |id1, res1, eff1 | ->
  | env, modules, own_module, id, e2, eff | -e> |id2, res2, eff2 | ->
  res1 = res2
->
  (
    | env, modules, own_module, id, e1, eff | -e> |id1, res1, eff1 | <->
    | env, modules, own_module, id, e2, eff | -e> |id2, res1, eff2 |
  )
.
Proof.
  intros. rewrite H1 in *. split; auto.
Qed.

Definition strong_equivalent e1 e2 id1 id2 id1' id2' :=
forall  env modules own_module eff res eff',
  |env, modules, own_module, id1, e1, eff| -e> |id2, res, eff'|
<->
  |env, modules, own_module, id1', e2, eff| -e> |id2', res, eff'|.

Example call_comm : forall (e e' : Expression) (x1 x2 t : Value) 
                           (env : Environment) (modules : list ErlModule) (own_module : string) (id : nat), valid_modules modules ->
  |env, modules, own_module, id, ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [e ; e'], []| -e> | id, inl [t], []| ->
  |env, modules, own_module, id, ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [e' ; e], []| -e> | id, inl [t], []|.
Proof.
  intros e e' x1 x2 t env modules own_module id VAL (* H H0 *) D. 
  (* List elements *)
  inversion D. subst.
  - inversion H5. inversion H6. subst.
    pose proof (EE1 := element_exist _ _ H2).
    inversion EE1. inversion H. subst. inversion H2.
    pose proof (EE2 := element_exist 0 x0 H1).
    inversion EE2. inversion H0. subst. simpl in H1. inversion H1.
    apply eq_sym, length_zero_iff_nil in H9. subst.
    pose proof (EE3 := element_exist _ _ H3).
    inversion EE3. inversion H8. subst. inversion H3.
    pose proof (EE4 := element_exist _ _ H10).
    inversion EE4. inversion H9. subst. simpl in H10. inversion H10.
    apply eq_sym, length_zero_iff_nil in H13. subst.
    pose proof (EE5 := element_exist _ _ H4).
    inversion EE5. inversion H11. subst. inversion H4.
    pose proof (EE6 := element_exist _ _ H14).
    inversion EE6. inversion H13. subst. simpl in H14. inversion H14.
    apply eq_sym, length_zero_iff_nil in H16. subst.
    pose proof (P1 := H7 0 Nat.lt_0_2).
    pose proof (P2 := H7 1 Nat.lt_1_2).
    simpl in P1, P2.
    cbn in H17. destruct x, x3; inversion H17.
    all: destruct l; try congruence.
    destruct l0; try congruence.
    inversion H16. subst. simpl.
    simpl in H22. subst.
    assert (x4 = id'' /\ x0 = []) as [? ?]. {
      apply fbs_soundness in P2 as P2'. destruct P2' as [? P2'].
      apply fbs_soundness in P1 as P1'. destruct P1' as [? P1'].
      apply effect_extension_expr_both in P2' as [? [? [? ?]]].
      apply effect_extension_expr_both in P1' as [? [? [? ?]]].
      subst. split. lia.
      destruct x9. reflexivity. inversion H15.
    }
    subst.
    eapply eval_call with (vals := [VLit (Integer x3); VLit (Integer x)]) (eff := [[]; []]) (ids := [id''; id'']); auto.
    * apply eval_lit.
    * apply eval_lit.
    * intros. inversion H15.
      + simpl. subst. eassumption.
      + subst. inversion H19.
        ++ subst. simpl. eassumption.
        ++ inversion H20.
    * assumption.
    * erewrite plus_comm_basic.
        + reflexivity.
        + assumption.
  - subst. inversion H5. inversion H6. subst.
    unfold get_modfunc in H16.
    rewrite module_lhs in H16.
    2: { apply VAL. }
    destruct get_module eqn:P; cbv in P; congruence.
Qed.


Example let_1_comm (e1 e2 : Expression) (modules : list ErlModule) (own_module : string) (t x1 x2 : Value) (id : nat) :
  valid_modules modules ->
  |[], modules, own_module, id, e1, []| -e> |id, inl [x1], []| ->
  | [(inl "X"%string, x1)], modules, own_module, id, e2, []| -e> |id, inl [x2], []| ->
  |[], modules, own_module, id, ELet ["X"%string] e1 (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [EVar "X"%string ; e2]), []| 
  -e> | id, inl [t], []| ->
  |[], modules, own_module, id, ELet ["X"%string] e1 (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [e2 ; EVar "X"%string]), []| 
  -e> |id, inl [t], []|.
Proof.
  * intros VAL H H0 H1. inversion H1. subst.
    pose (EE1 := element_exist 0 vals H14).
    inversion EE1. inversion H2. subst.
    inversion H14. apply eq_sym, length_zero_iff_nil in H4. subst.
    pose (P := determinism H9 _ _ _ H).
    destruct P, H4. inversion H3. subst.
    eapply eval_let; auto.
    - exact H9.
    - reflexivity.
    - eapply (call_comm _ _ _ _ _ _ _ _ _ _ H15).
      Unshelve.
      exact x1.
      exact x2.
      exact VAL.
Qed.

Example call_comm_ex : forall (e e' : Expression) (modules : list ErlModule) (own_module : string) (x1 x2 : Value) (env : Environment)
       (t t' : Value) (id : nat), valid_modules modules ->
  |env, modules, own_module, id, e, []| -e> |id, inl [x1], []| ->
  |env, modules, own_module, id, e', []| -e> |id, inl [x2], []| ->
  |env, modules, own_module, id, ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [e ; e'], []| -e> |id, inl [t], []| ->
  |env, modules, own_module, id, ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [e' ; e], []| -e> |id, inl [t'], []| ->
  t = t'.
Proof.
  intros e e' modules own_module x1 x2 env t t' id VAL H H0 H1 H2.
  pose (P := call_comm e e' x1 x2 t env _ _ _ VAL H1). 
  pose (DET := determinism P _ _ _ H2). inversion DET. inversion H3. reflexivity.
Qed.

Example let_comm_strict (env: Environment) (modules : list ErlModule) (own_module : string) (e1 e2 : Expression) (t t' v1 v2 : Value) 
   (eff eff1 eff2 : SideEffectList) (A B : Var) (VarHyp : A <> B) (id id1 id2 : nat) 
(Hypo1 : |env, modules, own_module, id, e1, eff| -e> | id, inl [v1], eff ++ eff1|)
(Hypo2 : |env, modules, own_module, id, e2, eff| -e> | id, inl [v2], eff ++ eff2|)
(VAL : valid_modules modules) :
|env, modules, own_module, id, ELet [A; B] (EValues [e1; e2])
     (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [EVar A ; EVar B]), eff| -e> |id + id1 + id2, inl [t], eff ++ eff1 ++ eff2|
->
|env, modules, own_module, id, ELet [A; B] (EValues [e2; e1])
     (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [EVar A ; EVar B]), eff| -e> |id + id2 + id1, inl [t], eff ++ eff2 ++ eff1|.
Proof.
  intro D. inversion D; subst; clear D.
  unfold_list.
  inversion H6; subst; clear H6.
  unfold_list.
  (* Deconstruct <e1, e2> evaluation *)
  specialize (H4 0 (ltac:(simpl; lia))) as D1.
  specialize (H4 1 (ltac:(simpl; lia))) as D2.
  clear H4.
  simpl in *.
  pose proof (determinism Hypo1 _ _ _ D1) as [? [? ?]]. inversion H. subst. clear H.
  apply fbs_soundness in D2 as D2'. destruct D2' as [? D2'].
  eapply effect_extension_expr_both in D2' as D2effs. destruct D2effs as [? [? [? ?]]].
  subst.
  eapply effect_irrelevant_expr in D2'.
  apply fbs_expr_correctness in D2'.
  pose proof (determinism Hypo2 _ _ _ D2') as [? [? ?]]. inversion H. subst. clear H.
  assert (0 = x6) by lia. clear H2.
  apply app_inv_head_iff in H0. subst.
  apply fbs_soundness in D1 as D1'. destruct D1' as [? D1'].
  eapply effect_irrelevant_expr with (eff0 := eff ++ x4) in D1'.
  apply fbs_expr_correctness in D1'.
  rewrite Nat.add_0_r in *.
  (* construct <e2, e1> evaluation *)
  eapply eval_let with (vals := [x1; x]). 2: reflexivity.
  eapply eval_values with (eff := [eff ++ x4; eff ++ x4 ++ eff1])
                          (ids := [x0; x0]); try reflexivity.
  * intros. inversion H.
    subst. 2: inversion H2. 3: lia.
    - simpl. rewrite app_assoc. assumption.
    - simpl. assumption.
  * (* Next, we deconstruct the BIF call, since we have to be sure that the result
       is a value, before being able to derive the goal *)
    inversion H12; subst; clear H12.
    - unfold_list.
      specialize (H8 0 (ltac:(simpl; lia))) as V1.
      specialize (H8 1 (ltac:(simpl; lia))) as V2.
      clear H8.
      simpl in *.
      inversion H6. subst. clear H6.
      inversion H7. subst. clear H7.
      inversion V1; subst; clear V1.
      inversion V2; subst; clear V2.
      rewrite get_value_there in H8. 2: congruence.
      rewrite get_value_here in H8, H9. inversion H8. inversion H9. subst.
      clear H8 H9.
      assert (id1 = 0 /\ id2 = 0) as [? ?] by lia. subst. clear H7.
      repeat rewrite Nat.add_0_r in *.
      (* Done, let's check the result of the simulation *)
      cbn in H19. destruct x8, x11; try congruence.
      all: destruct l; try congruence.
      destruct l0; try congruence.
      inversion H19. subst. clear H19 H2 H1.
      (* Done, let's contruct the rest of the derivation *)
      eapply eval_call with (vals := [VLit (Integer x0); VLit (Integer x)])
                            (eff := [(eff ++ x4) ++ eff1;(eff ++ x4) ++ eff1])
                            (ids := [x5; x5]); try reflexivity.
      1-2: now constructor.
      2: {
        unfold get_modfunc in *.
        destruct get_module eqn:MOD in H14; rewrite MOD. 2: congruence.
        rewrite module_lhs in MOD. 2: apply VAL.
        simpl. assumption.
      }
      + intros. assert (i = 0 \/ i = 1) as [ | ] by (simpl in H; lia).
        ** subst. simpl. rewrite app_assoc. eapply eval_var.
           rewrite get_value_there. 2: congruence.
           apply get_value_here.
        ** subst. simpl. apply eval_var. apply get_value_here.
      + cbn. rewrite app_assoc. do 5 f_equal. lia.
    - inversion H6. subst.
      inversion H7. subst.
      clear -H18 VAL.
      unfold get_modfunc in H18.
      rewrite module_lhs in H18.
      2: { apply VAL. }
      destruct get_module eqn:P; cbv in P; congruence.
Qed.

Example let_1_comm_2_list (env: Environment) (modules : list ErlModule) (own_module : string) (e1 e2 : Expression) (t t' v1 v2 : Value) 
   (eff eff1 eff2 : SideEffectList) (A B : Var) (VarHyp : A <> B) (id id1 id2 : nat) 
(Hypo1 : |env, modules, own_module, id, e1, eff| -e> | id + id1, inl [v1], eff ++ eff1|)
(Hypo2 : |env, modules, own_module, id + id2, e1, eff ++ eff2| -e> | id + id1 + id2, inl [v1], eff ++ eff2 ++ eff1|)
(Hypo1' : |env, modules, own_module, id, e2, eff| -e> | id + id2, inl [v2], eff ++ eff2|)
(Hypo2' : |env, modules, own_module, id + id1, e2, eff ++ eff1| -e> | id + id2 + id1, inl [v2], eff ++ eff1 ++ eff2|)
(VAL : valid_modules modules) :
|env, modules, own_module, id, ELet [A; B] (EValues [e1; e2])
     (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [EVar A ; EVar B]), eff| -e> |id + id1 + id2, inl [t], eff ++ eff1 ++ eff2|
->
|env, modules, own_module, id, ELet [A; B] (EValues [e2; e1])
     (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [EVar A ; EVar B]), eff| -e> |id + id2 + id1, inl [t'], eff ++ eff2 ++ eff1|
->
t = t'.
Proof.
  intros.
  (* FROM LET HYPO1 *)
  inversion H. subst. simpl in H13.
  pose (EE1 := element_exist 1 vals H13).
  inversion EE1 as [v1']. inversion H1. subst. inversion H13.
  pose (EE2 := element_exist 0 x H3).
  inversion EE2 as [v2']. inversion H2. subst. inversion H13.
  apply eq_sym, length_zero_iff_nil in H5. subst.
  inversion H8. subst.
  pose (EE3 := element_exist _ _ H7). inversion EE3 as [eff1']. inversion H4. subst. inversion H7.
  pose (EE4 := element_exist _ _ H11). inversion EE4 as [eff2']. inversion H5. subst. inversion H7.
  apply eq_sym, length_zero_iff_nil in H15. subst.
  pose (EE5 := element_exist _ _ H9). inversion EE5 as [id1']. inversion H12. subst. inversion H9.
  pose (EE6 := element_exist _ _ H16). inversion EE6 as [id2']. inversion H15. subst. inversion H9.
  apply eq_sym, length_zero_iff_nil in H18. subst.
  (* FROM LET HYPO2 *)
  inversion H0. subst.
  pose (EE1' := element_exist _ _ H29). inversion EE1' as [v2'']. inversion H17. subst. inversion H29.
  pose (EE2' := element_exist _ _ H19). inversion EE2' as [v1'']. inversion H18. subst. inversion H29.
  apply eq_sym, length_zero_iff_nil in H21. subst.
  inversion H24. subst.
  pose (EE3' := element_exist _ _ H23). inversion EE3' as [eff2'']. inversion H20. subst. inversion H23.
  pose (EE4' := element_exist _ _ H27). inversion EE4' as [eff1'']. inversion H21. subst. inversion H23.
  apply eq_sym, length_zero_iff_nil in H31. subst.

  pose (EE5' := element_exist _ _ H25). inversion EE5' as [id2'']. inversion H28. subst. inversion H25.
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
  inversion H14; subst.
  - pose (EC1 := element_exist _ _ H40). inversion EC1 as [v10]. inversion H37. subst. 
    inversion H40.
    pose (EC2 := element_exist _ _ H39). inversion EC2 as [v20]. inversion H38. subst. 
    inversion H40.
    apply eq_sym, length_zero_iff_nil in H47. subst.
    pose (EC3 := element_exist _ _ H41). inversion EC3 as [eff10]. inversion H46. subst.
    inversion H41.
    pose (EC4 := element_exist _ _ H48). inversion EC4 as [eff20]. inversion H47. subst.
    inversion H41.
    apply eq_sym, length_zero_iff_nil in H51. subst.
    pose (EC5 := element_exist _ _ H42). inversion EC5 as [id10]. inversion H49. subst.
    inversion H42.
    pose (EC6 := element_exist _ _ H52). inversion EC6 as [id20]. inversion H51. subst.
    inversion H42.
    apply eq_sym, length_zero_iff_nil in H54. subst.
    (* FROM CALL HYPO2 *)
    inversion H30; subst.
    * pose (EC1' := element_exist _ _ H58). inversion EC1' as [v20']. inversion H53. subst.
      inversion H58.
      pose (EC2' := element_exist _ _ H57). inversion EC2' as [v10']. inversion H54. subst.
      inversion H58.
      apply eq_sym, length_zero_iff_nil in H65. subst.
      pose (EC3' := element_exist _ _ H59). inversion EC3' as [eff20']. inversion H64. subst.
      inversion H59.
      pose (EC4' := element_exist _ _ H66). inversion EC4' as [eff10']. inversion H65. subst.
      inversion H59.
      apply eq_sym, length_zero_iff_nil in H69. subst.
      pose (EC5' := element_exist _ _ H60). inversion EC5' as [id20']. inversion H67. subst.
      inversion H60.
      pose (EC6' := element_exist _ _ H70). inversion EC6' as [id10']. inversion H69. subst.
      inversion H60.
      apply eq_sym, length_zero_iff_nil in H72. subst.
      inversion H43. subst. inversion H44. subst.
      inversion H61. subst. inversion H62. subst.

      
      pose (PUM1 := plus_effect_unmodified _ _ _ H55).        
      pose (PUM2 := plus_effect_unmodified _ _ _ H73).              
      inversion PUM1. inversion PUM2. simpl in H71, H72. subst.   
      
      (* EVERYTHING IS EQUAL *)
      (* assert (v1' = v1 /\ v1'' = v1 /\ v2' = v2 /\ v2'' = v2).
      { *)
        pose (P1 := H45 0 Nat.lt_0_2).
        pose (P2 := H45 1 Nat.lt_1_2).
        pose (P1' := H63 1 Nat.lt_1_2).
        pose (P2' := H63 0 Nat.lt_0_2).
        simpl in P1, P2, P1', P2'.
        inversion P1. inversion P2. inversion P1'. inversion P2'. subst.
        (* inversion H73. inversion H81. inversion H89. inversion H97. subst. *)
        rewrite get_value_there in H81, H111.
        2-3 : congruence. 
        rewrite get_value_here in H81, H91 , H101, H111.
        inversion H81. inversion H91. inversion H101. inversion H111.  subst. 
    (* } *)
      clear PUM1. clear PUM2. 
      apply (plus_comm_basic_value _ (eff ++ eff2 ++ eff1)) in H55. 
      simpl last in H73.
      rewrite H55 in H73. inversion H73.
      reflexivity.
    * inversion H43. subst. inversion H44. subst.
      inversion H61. subst. inversion H62. subst.
      congruence.
  - inversion H43. subst. inversion H44. subst.
    inversion VAL. unfold get_modfunc in H54. eapply module_lhs in H37.
    rewrite H37 in H54. simpl in H54.  congruence.
    
  
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
    - pose (EE1 := element_exist 0 vals H12). inversion EE1. inversion H0. subst.
      inversion H12. apply eq_sym, length_zero_iff_nil in H2. subst.
      inversion H7. subst.

      inversion H13; subst.
      + apply eq_sym, length_zero_iff_nil in H3. subst.
        apply eq_sym, length_zero_iff_nil in H8. subst.
        apply eq_sym, length_zero_iff_nil in H6. subst.
        inversion H4. subst. simpl in H14.
        rewrite get_value_here in H14. inversion H14. subst.
        unfold get_env in H20. simpl in H20. assumption.
      + inversion H14.
      + inversion H3.
      + inversion H6. subst.
        simpl in H18. rewrite get_value_here in H18. inversion H18. subst.
        congruence.
      + subst. inversion H6. subst.
        simpl in H18. rewrite get_value_here in H18. inversion H18. subst.
        contradiction.
    - inversion H11.
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

Example let_2_comm (env: Environment) (modules : list ErlModule) (own_module : string) (e1 e2 : Expression) (t x x0 : Value) 
    (eff eff1 eff2 : SideEffectList) (id0 id1 id2 : nat) (A B : Var) (VarHyp : A <> B) (VAL : valid_modules modules):
  |env, modules, own_module, id0, e2, eff| -e> |id0 + id2, inl [x0], eff ++ eff2|
 -> 
  |append_vars_to_env [A] [x] env, modules, own_module, id0 + id1, e2, eff ++ eff1|
  -e> | id0 + id1 + id2, inl [x0], eff ++ eff1 ++ eff2|
 ->
  |env, modules, own_module, id0, e1, eff| -e> |id0 + id1, inl [x], eff ++ eff1|
 -> 
  |append_vars_to_env [A] [x0] env, modules, own_module, id0 + id2, e1, eff ++ eff2|
  -e> |id0 + id2 + id1, inl [x], eff ++ eff2 ++ eff1| 
 ->
  |env, modules, own_module, id0, ELet [A] e1 (ELet [B] e2 
        (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [EVar A ; EVar B])), eff| -e>
  | id0 + id1 + id2, inl [t], eff ++ eff1 ++ eff2|
->
  |env, modules, own_module, id0, ELet [A] e2 (ELet [B] e1
        (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [EVar A ; EVar B])), eff| -e>
  | id0 + id2 + id1, inl [t], eff ++ eff2 ++ eff1|
.
Proof.
  * intros. inversion H3. subst.
    pose (EE1 := element_exist 0 vals H16).
    inversion EE1 as [x'].
    inversion H4. subst. 
    inversion H16. apply eq_sym, length_zero_iff_nil in H6. subst.
(*     assert (x' = x /\ eff1' = eff ++ eff1 /\ id1' = (id0 + id1)%nat).
    { *)
      pose (WD := determinism H1 _ _ _ H11). destruct WD. destruct H6. inversion H5.
      subst.
(*     } *)
    inversion H17. subst.
    pose (EE1' := element_exist 0 vals H21).
    inversion EE1' as [x0'].
    inversion H6. subst. inversion H21.
    apply eq_sym, length_zero_iff_nil in H8.
(*     assert (x0' = x0 /\ eff2' = eff ++ eff1 ++ eff2 /\ id2' = (id0 + id1 + id2)%nat).
    { *)
      pose (WD := determinism H0 _ _ _ H14). 
      destruct WD. destruct H9. inversion H7.
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
     + inversion H22; subst.
     ++ pose (EC1 := element_exist 1 _ H12).
       pose (EC2 := element_exist 1 _ H13).
       pose (EC3 := element_exist 1 _ H18).
       inversion EC1 as [x'']. inversion EC2 as [eff1'']. inversion EC3 as [id1''].
       inversion H8. inversion H9. inversion H10. subst.
       inversion H12. inversion H13. inversion H18.
       pose (EC1' := element_exist 0 _ H25).
       pose (EC2' := element_exist 0 _ H26).
       pose (EC3' := element_exist 0 _ H27).
       inversion EC1' as [x0'']. inversion EC2' as [eff2'']. inversion EC3' as [id2''].
       inversion H24. inversion H29. inversion H30. subst.
       inversion H25. inversion H26. inversion H27.
       apply eq_sym, length_zero_iff_nil in H32.
       apply eq_sym, length_zero_iff_nil in H35.
       apply eq_sym, length_zero_iff_nil in H36. subst.

         pose (P1' := H23 0 Nat.lt_0_2).
         pose (P2' := H23 1 Nat.lt_1_2).
         inversion P1'. inversion P2'. simpl in H49, H50, H48, H52. subst.

         simpl in H41, H51.

         rewrite get_value_there in H41. 2: congruence.
         rewrite get_value_here in H41. inversion H41.
         rewrite get_value_here in H51. inversion H51. subst.
         

       (* BACK TO CALL PROOF *)
       eapply eval_call with (vals := [x0'' ; x'']) (eff := [eff ++ eff2 ++ eff1;eff ++ eff2 ++ eff1]) 
                    (ids := [(id0 + id2 + id1)%nat; (id0 + id2 + id1)%nat]) ;auto.
                    
       ** eapply eval_lit.
       ** eapply eval_lit.
       ** intros. inversion H31. 2: inversion H35.
         -- simpl. eapply eval_var. rewrite get_value_here. auto.
         -- simpl. eapply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
         -- inversion H37.
       ** inversion H19. subst. inversion H20. subst. exact H28.
       ** inversion H19. subst. inversion H20. subst.
       apply plus_comm_basic_value with (eff := eff ++ eff1 ++ eff2).
          simpl in H40, H42. subst. assumption.
  ++  inversion H19. inversion H20. subst. 
      inversion VAL. unfold get_modfunc in H32. eapply module_lhs in H8.
      rewrite H8 in H32. simpl in H32. congruence.
 

Qed.

Example let_2_comm_eq (env: Environment) (modules : list ErlModule) (own_module : string) (e1 e2 : Expression) (t x x0 : Value) 
    (eff eff1 eff2 : SideEffectList) (id0 id1 id2 : nat) (A B : Var) (VarHyp : A <> B) (VAL : valid_modules modules) :
  |env, modules, own_module, id0, e2, eff| -e> |id0 + id2, inl [x0], eff ++ eff2| -> 
  |append_vars_to_env [A] [x] env, modules, own_module, id0 + id1, e2, eff ++ eff1|
  -e> | id0 + id1 + id2, inl [x0], eff ++ eff1 ++ eff2| ->
  |env, modules, own_module, id0, e1, eff| -e> |id0 + id1, inl [x], eff ++ eff1| -> 
  |append_vars_to_env [A] [x0] env, modules, own_module, id0 + id2, e1, eff ++ eff2|
  -e> |id0 + id2 + id1, inl [x], eff ++ eff2 ++ eff1| ->
  |env, modules, own_module, id0, ELet [A] e1 (ELet [B] e2
        (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [EVar A ; EVar B])), eff| -e> 
  | id0 + id1 + id2, inl [t], eff ++ eff1 ++ eff2|
<->
  |env, modules, own_module, id0, ELet [A] e2 (ELet [B] e1
        (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [EVar A ; EVar B])), eff| -e>
  | id0 + id2 + id1, inl [t], eff ++ eff2 ++ eff1|
.
Proof.
  split.
  * apply let_2_comm with (x := x) (x0 := x0); try (assumption).
  * apply let_2_comm with (x := x0) (x0 := x); try (assumption).
Qed.

(* THIS THEOREM COULD BE PROVEN WITH STRONG DETERMINISM
Example let_1_comm_2_list (env: Environment) (e1 e2 : Expression) (t t' : Value) eff eff1 eff2:
|env, ELet ["X"%string; "Y"%string] [e1 ; e2] (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [EVar "X"%string ; EVar "Y"%string]), eff| -e> |inl t, eff ++ eff1 ++ eff2|
->
|env, ELet ["X"%string; "Y"%string] [e2 ; e1] (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [EVar "X"%string ; EVar "Y"%string]), eff| -e> |inl t', eff ++ eff2 ++ eff1|
->
t = t'. *)

Example let_2_binding_swap (env: Environment) (modules : list ErlModule) (own_module : string) (e1 e2 : Expression) (t x x0 : Value) 
    (eff eff1 eff2 : SideEffectList) (A B : Var) (id0 id1 id2 : nat) (VarHyp : A <> B) (VAL : valid_modules modules):
  |env, modules, own_module, id0, e2, eff| -e> |id0 + id2, inl [x0], eff ++ eff2| -> 
  |append_vars_to_env [A] [x] env, modules, own_module, id0 + id1, e2, eff ++ eff1| -e>
  | id0 + id1 + id2, inl [x0], eff ++ eff1 ++ eff2| ->
  |env, modules, own_module, id0, e1, eff| -e> |id0 + id1, inl [x], eff ++ eff1| -> 
  |append_vars_to_env [B] [x0] env, modules, own_module, id0 + id2, e1, eff ++ eff2| -e>
  |id0 + id2 + id1, inl [x], eff ++ eff2 ++ eff1|
->
  |env, modules, own_module, id0, ELet [A] e1 (ELet [B] e2
        (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [EVar A ; EVar B])), eff| -e>
  |id0 + id1 + id2, inl [t], eff ++ eff1 ++ eff2|
<->
  |env, modules, own_module, id0, ELet [B] e2 (ELet [A] e1
        (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [EVar A ; EVar B])), eff| -e>
  |id0 + id2 + id1, inl [t], eff ++ eff2 ++ eff1|
.
Proof.
  split.
  * intros. inversion H3. subst.
    pose (EE1 := element_exist 0 vals H16).
    inversion EE1 as [x'].
    inversion H4. subst.
    inversion H16. apply eq_sym, length_zero_iff_nil in H6. subst.
(*     assert (x' = x /\ eff1' = eff ++ eff1 /\ id1' = (id0 + id1)%nat).
    { *)
      pose (WD := determinism H1 _ _ _ H11). destruct WD. destruct H6. inversion H5.
      subst.
(*     } *)
    inversion H17. subst.
    pose (EE1' := element_exist 0 vals H21).
    inversion EE1' as [x0'].
    inversion H6. subst. inversion H21.
    apply eq_sym, length_zero_iff_nil in H8. subst.
(*     assert (x0' = x0 /\ eff2' = eff ++ eff1 ++ eff2 /\ id2' = (id0 + id1 + id2)%nat).
    { *)
      pose (WD := determinism H0 _ _ _ H14). 
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
     + inversion H22; subst.
     ++ pose (EC1 := element_exist 1 _ H12).
        pose (EC2 := element_exist 1 _ H13).
        pose (EC3 := element_exist 1 _ H15).
        inversion EC1 as [x'']. inversion EC2 as [eff1'']. inversion EC3 as [id1''].
        inversion H8. inversion H9. inversion H10. subst.
        inversion H12. inversion H13. inversion H15.
        pose (EC1' := element_exist 0 _ H24).
        pose (EC2' := element_exist 0 _ H25).
        pose (EC3' := element_exist 0 _ H26).
        inversion EC1' as [x0'']. inversion EC2' as [eff2'']. inversion EC3' as [id2''].
        inversion H23. inversion H28. inversion H29. subst.
        inversion H12. inversion H13. inversion H15.
        apply eq_sym, length_zero_iff_nil in H31.
        apply eq_sym, length_zero_iff_nil in H34.
        apply eq_sym, length_zero_iff_nil in H35. subst.

          pose (P1' := H20 0 Nat.lt_0_2).
          pose (P2' := H20 1 Nat.lt_1_2).
          inversion P1'. inversion P2'. simpl in H39, H41, H50, H43, H48, H49, H51, H40, H50. subst.

          rewrite get_value_there in H40. 2: congruence.
          rewrite get_value_here in H40. inversion H40.
          rewrite get_value_here in H50. inversion H50. subst.

        (* BACK TO CALL PROOF *)
        eapply eval_call with (vals := [x'' ; x0'']) (eff := [eff ++ eff2 ++ eff1;eff ++ eff2 ++ eff1]) 
                      (ids := [(id0 + id2 + id1)%nat; (id0 + id2 + id1)%nat]); auto.
        ** eapply eval_lit.
        ** eapply eval_lit.
        ** intros. inversion H30. 2: inversion H34.
          -- simpl. eapply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
          -- simpl. eapply eval_var. rewrite get_value_here. auto.
          -- inversion H36.
        ** inversion H18. inversion H19. subst. exact H27. 
        ** apply plus_effect_changeable with (eff := eff ++ eff1 ++ eff2). 
           inversion H18. inversion H19. subst. assumption.
      ++ inversion H18. inversion H19. subst.
         inversion VAL. unfold get_modfunc in H31. eapply module_lhs in H8.
      rewrite H8 in H31. simpl in H31. congruence.
  * intros. inversion H3. subst.
    pose (EE1 := element_exist 0 vals H16).
    inversion EE1 as [x'].
    inversion H4. subst.
    inversion H16. apply eq_sym, length_zero_iff_nil in H6. subst.
(*     assert (x' = x /\ eff1' = eff ++ eff1 /\ id1' = (id0 + id1)%nat).
    { *)
      pose (WD := determinism H _ _ _ H11). destruct WD. destruct H6. inversion H5.
      subst.
(*     } *)
    inversion H17. subst.
    pose (EE1' := element_exist 0 vals H21).
    inversion EE1' as [x0'].
    inversion H6. subst. inversion H21.
    apply eq_sym, length_zero_iff_nil in H8. subst.
(*     assert (x0' = x0 /\ eff2' = eff ++ eff1 ++ eff2 /\ id2' = (id0 + id1 + id2)%nat).
    { *)
      pose (WD := determinism H2 _ _ _ H14). 
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
     + inversion H22; subst.
       ++ pose (EC1 := element_exist 1 _ H12).
          pose (EC2 := element_exist 1 _ H13).
          pose (EC3 := element_exist 1 _ H15).
          inversion EC1 as [x'']. inversion EC2 as [eff1'']. inversion EC3 as [id1''].
          inversion H8. inversion H9. inversion H10. subst.
          inversion H12. inversion H13. inversion H15.
          pose (EC1' := element_exist 0 _ H24).
          pose (EC2' := element_exist 0 _ H25).
          pose (EC3' := element_exist 0 _ H26).
          inversion EC1' as [x0'']. inversion EC2' as [eff2'']. inversion EC3' as [id2''].
          inversion H23. inversion H28. inversion H29. subst.
          inversion H12. inversion H13. inversion H15.
          apply eq_sym, length_zero_iff_nil in H31.
          apply eq_sym, length_zero_iff_nil in H34.
          apply eq_sym, length_zero_iff_nil in H35. subst.

            pose (P1' := H20 0 Nat.lt_0_2).
            pose (P2' := H20 1 Nat.lt_1_2).
            inversion P1'. inversion P2'. simpl in H39, H41, H50, H43, H48, H49, H51, H40, H50. subst.

            rewrite get_value_there in H50. 2: congruence.
            rewrite get_value_here in H50. inversion H50.
            rewrite get_value_here in H40. inversion H40. subst.

          (* BACK TO CALL PROOF *)
          eapply eval_call with (vals := [x'' ; x0'']) (eff := [eff ++ eff1 ++ eff2;eff ++ eff1 ++ eff2]) 
                        (ids := [(id0 + id1 + id2)%nat; (id0 + id1 + id2)%nat]); auto.
          ** eapply eval_lit.
          ** eapply eval_lit.
          ** intros. inversion H30. 2: inversion H34.
            -- simpl. eapply eval_var. rewrite get_value_here. auto.
            -- simpl. eapply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
            -- inversion H36.
          ** inversion H18. inversion H19. subst. exact H27.
          ** inversion H18. inversion H19. subst. apply plus_effect_changeable with (eff := eff ++ eff2 ++ eff1). assumption.
      ++ inversion H18. inversion H19. subst.
         inversion VAL. unfold get_modfunc in H31. eapply module_lhs in H8.
         rewrite H8 in H31. simpl in H31. congruence.
Qed.

Example let_2_apply_effect_free (env: Environment) (modules : list ErlModule) (own_module : string) (e1 e2 exp : Expression) (v1 v2 : Value) 
       (v0 t : ValueSequence + Exception) (A B : Var) (VarHyp : A <> B) (id: nat) (eff : SideEffectList)
(E1 : | append_vars_to_env [A] [v1] (append_vars_to_env [B] [v2] env), modules, own_module, id, exp, eff | -e> |id, v0, eff|)
(E2 : | append_vars_to_env [B] [v2] (append_vars_to_env [A] [v1] env), modules, own_module, id, exp, eff | -e> |id, v0, eff|)
(VAL : valid_modules modules)
    :
  |env, modules, own_module, id, e2, eff | -e> |id, inl [v2], eff| -> 
  |append_vars_to_env [A] [v1] env, modules, own_module, id, e2, eff| -e> | id, inl [v2], eff| ->
  |env, modules, own_module, id, e1, eff | -e> | id, inl [v1], eff| -> 
  |append_vars_to_env [B] [v2] env, modules, own_module, id, e1, eff| -e> | id , inl [v1], eff |
->
  |env, modules, own_module, id, ELet [A] e1 (ELet [B] e2
        (EApp exp [EVar A ; EVar B])), eff| -e> |id , t, eff|
  <->
  |env, modules, own_module, id, ELet [B] e2 (ELet [A] e1
        (EApp exp [EVar A ; EVar B])), eff| -e> |id, t, eff |
.
Proof.
  split;intros.
   (** Deconstruct ELet-s *)
  * inversion H3. subst.
    pose (EE1 := element_exist 0 vals H16). inversion EE1 as [v1'].
    inversion H4. subst. inversion H16.
    apply eq_sym, length_zero_iff_nil in H6. subst.
    (* assert (v1' = v1 /\ eff1' = []).
    { *)
      pose (WD := determinism H1 _ _ _ H11). destruct WD. destruct H6. inversion H5.
      subst.
    (* } *)
    inversion H17. subst.
    pose (EE4 := element_exist 0 vals H21).
    inversion EE4 as [v2']. inversion H6. subst. inversion H21.
    apply eq_sym, length_zero_iff_nil in H8. subst.
    (* assert (v2' = v2 /\ eff2' = []). 
    { *)
      pose (WD := determinism H0 _ _ _ H14). destruct WD. destruct H8.
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
       + inversion H22; subst.
         ** pose (WD3 := determinism E2 _ _ _ H12). destruct WD3.
            inversion H8. destruct H9. subst.
            pose (EEA := element_exist _ _ H10).
            inversion EEA as [v1'']. inversion H8. subst. inversion H10.
            pose (EEA2 := element_exist _ _ H20).
            inversion EEA2 as [v2'']. inversion H9. subst. inversion H10.
            apply eq_sym, length_zero_iff_nil in H24. subst.
            pose (EEE := element_exist _ _ H15).
            inversion EEE as [eff1'']. inversion H23. subst. inversion H15.
            pose (EEE2 := element_exist _ _ H26).
            inversion EEE2 as [eff2'']. inversion H24. subst. inversion H15.
            apply eq_sym, length_zero_iff_nil in H28. subst.
            pose (EEI := element_exist _ _ H18).
            inversion EEI as [id1'']. inversion H27. subst. inversion H18.
            pose (EEI2 := element_exist _ _ H29).
            inversion EEI2 as [id2'']. inversion H28. subst. inversion H18.
            apply eq_sym, length_zero_iff_nil in H32. subst.
            clear dependent EEA. clear dependent EEA2. clear dependent EEE.
            clear dependent EEE2. clear dependent EEI. clear dependent EEI2.
            (* assert (v1' = v1 /\ v2' = v2 /\ eff1' = [] /\ eff2' = []).
            { *)
              pose (P := H25 0 Nat.lt_0_2).
              inversion P.
              simpl in H37, H32, H33, H37, H38, H39, H40. subst.
              rewrite get_value_there in H39. 2: congruence. 
              rewrite get_value_here in H39.
              inversion H39.
              subst.

              pose (P2 := H25 1 Nat.lt_1_2).
              inversion P2.
              simpl in H37, H32, H33, H37, H38, H39, H40, H41.
              rewrite get_value_here in H40. inversion H40.
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
            -- simpl in H30. exact H30.
         ** eapply eval_app_closure_ex; try(reflexivity).
            -- pose (WD := determinism E2 _ _ _ H24). destruct WD. destruct H9. subst.
               exact E1.
         ** inversion H10.
            -- pose (EEA := element_exist _ _  (eq_sym H9)). inversion EEA as [v1''].
               inversion H8. subst.
               inversion H9. apply length_zero_iff_nil in H19. subst. 
               simpl in H30. inversion H30.
            -- inversion H9.
              ++ rewrite H19 in *. simpl in H30. inversion H30.
              ++ inversion H19.
         ** pose (WD := determinism E2 _ _ _ H15).
            destruct WD. destruct H9.
            subst.
            eapply eval_app_badfun_ex with (vals := [v1'; v2']) (eff := [eff2; eff2])
                                              (ids := [id';id']); auto.
           -- exact E1.
           -- intros. inversion H8. 2: inversion H24.
              ++ simpl.
                 apply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
              ++ simpl. rewrite H9, H20.
                 apply eval_var. rewrite get_value_here. auto.
              ++ inversion H26.
         ** pose (WD := determinism E2 _ _ _ H15).
            inversion WD. destruct H9. subst.
            eapply eval_app_badarity_ex with (vals := [v1'; v2']) (eff := [eff2;eff2])
                                   (ids := [id'; id']); auto.
           -- exact E1.
           -- intros. inversion H8. 2: inversion H24.
              ++ simpl.
                 apply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
              ++ simpl.
                 rewrite H9, H20.
                 apply eval_var. rewrite get_value_here. auto.
              ++ inversion H26.
           -- rewrite <- H10 in H19. auto.
      - subst.
        pose (WD := determinism H0 _ _ _ H20).
        destruct WD. destruct H7. inversion H6.
      - subst.
        pose (WD := determinism H1 _ _ _ H15).
        destruct WD. inversion H4.
  * inversion H3. subst.
    pose (EE1 := element_exist 0 vals H16). inversion EE1 as [v1'].
    inversion H4. subst. inversion H16.
    apply eq_sym, length_zero_iff_nil in H6. subst.
    (* assert (v1' = v1 /\ eff1' = []).
    { *)
      pose (WD := determinism H _ _ _ H11). destruct WD. destruct H6. inversion H5.
      subst.
    (* } *)
    inversion H17. subst.
    pose (EE4 := element_exist 0 vals H21).
    inversion EE4 as [v2']. inversion H6. subst. inversion H21.
    apply eq_sym, length_zero_iff_nil in H8. subst.
    (* assert (v2' = v2 /\ eff2' = []). 
    { *)
      pose (WD := determinism H2 _ _ _ H14). destruct WD. destruct H8.
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
       + inversion H22; subst.
         ** pose (WD3 := determinism E1 _ _ _ H12). destruct WD3.
            inversion H8. destruct H9. subst.
            pose (EEA := element_exist _ _ H10).
            inversion EEA as [v1'']. inversion H8. subst. inversion H10.
            pose (EEA2 := element_exist _ _ H20).
            inversion EEA2 as [v2'']. inversion H9. subst. inversion H10.
            apply eq_sym, length_zero_iff_nil in H24. subst.
            pose (EEE := element_exist _ _ H15).
            inversion EEE as [eff1'']. inversion H23. subst. inversion H15.
            pose (EEE2 := element_exist _ _ H26).
            inversion EEE2 as [eff2'']. inversion H24. subst. inversion H15.
            apply eq_sym, length_zero_iff_nil in H28. subst.
            pose (EEI := element_exist _ _ H18).
            inversion EEI as [id1'']. inversion H27. subst. inversion H18.
            pose (EEI2 := element_exist _ _ H29).
            inversion EEI2 as [id2'']. inversion H28. subst. inversion H18.
            apply eq_sym, length_zero_iff_nil in H32. subst.
            clear dependent EEA. clear dependent EEA2. clear dependent EEE.
            clear dependent EEE2. clear dependent EEI. clear dependent EEI2.
            (* assert (v1' = v1 /\ v2' = v2 /\ eff1' = [] /\ eff2' = []).
            { *)
              pose (P := H25 0 Nat.lt_0_2).
              inversion P.
              simpl in H37, H32, H33, H37, H38, H39, H40. subst.
              rewrite get_value_here in H39.
              inversion H39.
              subst.

              pose (P2 := H25 1 Nat.lt_1_2).
              inversion P2.
              simpl in H37, H32, H33, H37, H38, H39, H40, H41.
              rewrite get_value_there in H40. 2: congruence. 
              rewrite get_value_here in H40. inversion H40.
              subst.

            (* } *)
            eapply eval_app with (vals := [v1''; v2'']) (eff := [eff2''; eff2''])
                                   (ids := [id2'';id2'']); auto.
            -- eexact E2.
            -- auto.
            -- intros. inversion H31. 2: inversion H33.
              ++ simpl. eapply eval_var. rewrite get_value_here. auto.
              ++ simpl. apply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
              ++ inversion H35.
            -- simpl in H30. exact H30.
         ** eapply eval_app_closure_ex; try(reflexivity).
            -- pose (WD := determinism E1 _ _ _ H24). destruct WD. destruct H9. subst.
               exact E2.
         ** inversion H10.
            -- pose (EEA := element_exist _ _  (eq_sym H9)). inversion EEA as [v1''].
               inversion H8. subst.
               inversion H9. apply length_zero_iff_nil in H19. subst. 
               simpl in H30. inversion H30.
            -- inversion H9.
              ++ rewrite H19 in *. simpl in H30. inversion H30.
              ++ inversion H19.
         ** pose (WD := determinism E1 _ _ _ H15).
            destruct WD. destruct H9.
            subst.
            eapply eval_app_badfun_ex with (vals := [v2'; v1']) (eff := [eff2; eff2])
                                              (ids := [id';id']); auto.
           -- exact E2.
           -- intros. inversion H8. 2: inversion H24.
              ++ simpl. (* rewrite H10, H22. *)
                 apply eval_var. rewrite get_value_here. auto.
              ++ simpl. rewrite H9, H20. 
                 apply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
              ++ inversion H26.
         ** pose (WD := determinism E1 _ _ _ H15).
            inversion WD. destruct H9. subst.
            eapply eval_app_badarity_ex with (vals := [v2'; v1']) (eff := [eff2;eff2])
                                   (ids := [id'; id']); auto.
           -- exact E2.
           -- intros. inversion H8. 2: inversion H24.
              ++ simpl.
                 apply eval_var. rewrite get_value_here. auto.
              ++ simpl. rewrite H9, H20.
                 apply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
              ++ inversion H26.
           -- rewrite <- H10 in H19. auto.
      - subst.
        pose (WD := determinism H2 _ _ _ H20).
        destruct WD. destruct H7. inversion H6.
      - subst.
        pose (WD := determinism H _ _ _ H15).
        destruct WD. inversion H4.
Qed.
