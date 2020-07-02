Load Core_Erlang_Proofs.

Module Core_Erlang_Equivalence_Proofs.

Import Core_Erlang_Syntax.
Import Core_Erlang_Semantics.
Import Core_Erlang_Environment.
Import Core_Erlang_Helpers.
Import Core_Erlang_Proofs.
Import Core_Erlang_Equalities.
Import Core_Erlang_Side_Effects.
Import Core_Erlang_Determinism_Helpers.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.
Import Coq.Init.Logic.
Import Omega.

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



(* Example call_comm : forall (e e' : Expression) (x1 x2 t : Value) (env : Environment),
  |env, e, []| -e> |inl x1, []| ->
  |env, e', []| -e> |inl x2, []| ->
  |env, ECall "plus"%string [e ; e'], []| -e> |inl t, []| ->
  |env, ECall "plus"%string [e' ; e], []| -e> |inl t, []|.
Proof.
  intros. 
  (* List elements *)
  inversion H1; subst; simpl in H4; pose (EE1 := element_exist Value 1 vals H4);
  inversion EE1; inversion H2; subst; inversion H4; pose (EE2 := element_exist Value 0 x0 H6);
  inversion EE2; inversion H3; subst; simpl in H4; inversion H4;
  apply eq_sym, length_zero_iff_nil in H9; subst;
  pose (WD1 := determinism _ H);
  pose (WD2 := determinism _ H0);
  pose (P1 := H7 0 Nat.lt_0_2);
  pose (P2 := H7 1 Nat.lt_1_2);
  unfold concatn in P1, P2.
  apply WD1 in P1; inversion P1; simpl in H9; assert (concat (firstn 1 eff) = []).
  {
    destruct eff.
    * simpl. reflexivity.
    * simpl. inversion H9. auto.
  }
  rewrite H10 in *. rewrite app_nil_l in P2. simpl nth in P2.
  apply WD2 in P2. inversion P2. inversion H5. inversion H12. inversion P1. inversion H14. subst.
  eapply eval_call with (vals := [x3; x]) (eff := [[];[]]); auto.
  * intros. inversion H16.
    - unfold concatn. simpl. assumption.
    - inversion H19.
      + unfold concatn. simpl. assumption.
      + inversion H21.
  * rewrite (@plus_comm_basic x x3 t). unfold concatn. simpl concat.
    inversion H5. 
    pose (EE3 := element_exist SideEffectList _ _ H18). inversion EE3. inversion H16.
    subst. inversion H5.
    pose (EE4 := element_exist SideEffectList _ _ H20). inversion EE4. inversion H19.
    subst. inversion H20. apply eq_sym, length_zero_iff_nil in H22. subst.
    inversion H13. rewrite app_nil_r in H22. assert (x0 = [] /\ x2 = []). 
    { destruct x0.
      * simpl in H22. auto.
      * inversion H22.
    }
    inversion H21. subst. rewrite app_nil_r. reflexivity.
    - inversion H5. pose (EE3 := element_exist _ _ _ H18). inversion EE3. inversion H16.
      subst. inversion H18.
      pose (EE4 := element_exist _ _ _ H20). inversion EE4. inversion H19. subst. inversion H20.
      apply eq_sym, length_zero_iff_nil in H22. subst.
      
      unfold concatn in *. simpl app in *.
      rewrite app_nil_r in H13. assert (x0 = [] /\ x2 = []). { destruct x0. auto. inversion H13. }
      inversion H21. subst.
      assumption.
Qed. *)


(* Example let_1_comm (e1 e2 : Expression) (t x1 x2 : Value) :
  |[], e1, []| -e> |inl x1, []| ->
  | [(inl "X"%string, x1)], e2, []| -e> |inl x2, []| ->
  |[], ELet ["X"%string] [e1] (ECall "plus"%string [EVar "X"%string ; e2]), []| -e> |inl t, []| ->
  |[], ELet ["X"%string] [e1] (ECall "plus"%string [e2 ; EVar "X"%string]), []| -e> |inl t, []|.
Proof.
  * intros. inversion H1. subst. inversion H5. inversion H6.
    pose (EE1 := element_exist Value 0 vals H5). inversion EE1. inversion H2. subst.
    inversion H5. apply eq_sym, length_zero_iff_nil in H9. subst.
    pose (EE2 := element_exist _ 0 _ H6). inversion EE2. inversion H7. subst.
    inversion H6. apply eq_sym, length_zero_iff_nil in H10. subst.
    eapply eval_let with (vals := [x]) (eff := [[]]) (eff2 := []); auto.
    - intros. inversion H9. 2: inversion H11.
      simpl. pose (P1 := H8 0 Nat.lt_0_1). unfold concatn in P1. simpl in P1.
      pose (WD1 := determinism _ H). apply WD1 in P1 as P2. inversion P2. inversion H10.
      rewrite app_nil_r in H14. subst. exact P1.
    - unfold concatn. simpl. apply call_comm with (x1 := x) (x2 := x2).
      + apply eval_var.
      + pose (P1 := H8 0 Nat.lt_0_1). unfold concatn in P1. simpl in P1.
        pose (WD1 := determinism _ H). apply WD1 in P1 as P2. inversion P2. inversion H9.
        subst. assumption.
      + unfold concatn in H13. simpl in H13. 
        pose (P1 := H8 0 Nat.lt_0_1). unfold concatn in P1. simpl in P1.
        pose (WD1 := determinism _ H). apply WD1 in P1 as P2. inversion P2.
        rewrite app_nil_r in H10. subst. assumption.
Qed. *)

(* Example call_comm_ex : forall (e e' : Expression) (x1 x2 : Value) (env : Environment) (t t' : Value),
  |env, e, []| -e> |inl x1, []| ->
  |env, e', []| -e> |inl x2, []| ->
  |env, ECall "plus"%string [e ; e'], []| -e> |inl t, []| ->
  |env, ECall "plus"%string [e' ; e], []| -e> |inl t', []| ->
  t = t'.
Proof.
  intros. pose (P := call_comm e e' x1 x2 t env H H0 H1). 
  pose (DET := determinism _ P _ _ H2). inversion DET. inversion H3. reflexivity.
Qed. *)

Example let_2_comm_concrete_alternate_proof (t : Value + Exception) :
  |[], 0,  ELet ["X"%string] [ELit (Integer 5)] (ELet ["Y"%string] [ELit (Integer 6)]
           (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string])), []| -e> |0, t, []|
<->
|[], 0, ELet ["X"%string] [ELit (Integer 6)] (ELet ["Y"%string] [ELit (Integer 5)]
           (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string])), []| -e> |0, t, []|
.
Proof.
  split; intros.
  * (* let values *)
    assert (|[], 0, ELet ["X"%string] [ELit (Integer 5)]
      (ELet ["Y"%string] [ELit (Integer 6)] (ECall "plus" [EVar "X"%string; EVar "Y"%string])), []|
      -e> |0, inl (VLit (Integer 11)), []|).
    {
      eapply eval_let with (vals := [VLit (Integer 5)]) (eff := [[]]) (ids := [0]); auto.
      * intros. inversion H0; inversion H2. apply eval_lit.
      * reflexivity.
      * eapply eval_let with (vals := [VLit (Integer 6)]) (eff := [[]]) (ids := [0]); auto.
        - intros. inversion H0; inversion H2. apply eval_lit.
        - reflexivity.
        - eapply eval_call with (vals := [VLit (Integer 5); VLit (Integer 6)])
                                (eff := [[];[]]) (ids := [0;0]); auto.
          + intros. inversion H0; inversion H2; try(inversion H4); apply eval_var.
    }
    apply @determinism with (v1 := inl (VLit (Integer 11))) (eff' := []) (id' := 0) in H.
    inversion H. inversion H1. subst.
    {
      eapply eval_let with (vals := [VLit (Integer 6)]) (eff := [[]]) (ids := [0]); auto.
      * intros. inversion H1; inversion H5. apply eval_lit.
      * reflexivity.
      * eapply eval_let with (vals := [VLit (Integer 5)]) (eff := [[]]) (ids := [0]); auto.
        - intros. inversion H1; inversion H5. apply eval_lit.
        - reflexivity.
        - eapply eval_call with (vals := [VLit (Integer 6); VLit (Integer 5)])
                                (eff := [[];[]]) (ids := [0;0]); auto.
          + intros. inversion H1; inversion H5; try(inversion H7); apply eval_var.
    } assumption.
    
    
    (* Other way, basically the same*)
    * (* let values *)
    assert (|[], 0, ELet ["X"%string] [ELit (Integer 6)]
      (ELet ["Y"%string] [ELit (Integer 5)] (ECall "plus" [EVar "X"%string; EVar "Y"%string])), []|
      -e>  |0, inl (VLit (Integer 11)), []|).
    {
      eapply eval_let with (vals := [VLit (Integer 6)]) (eff := [[]]) (ids := [0]); auto.
      * intros. inversion H0; inversion H2. apply eval_lit.
      * reflexivity.
      * eapply eval_let with (vals := [VLit (Integer 5)]) (eff := [[]]) (ids := [0]); auto.
        - intros. inversion H0; inversion H2. apply eval_lit.
        - reflexivity.
        - eapply eval_call with (vals := [VLit (Integer 6); VLit (Integer 5)])
                                (eff := [[];[]]) (ids := [0;0]); auto.
          + intros. inversion H0; inversion H2; try(inversion H4); apply eval_var.
    }
    apply @determinism with (v1 := inl (VLit (Integer 11))) (eff' := []) (id' := 0) in H.
    inversion H. inversion H1. subst.
    {
      eapply eval_let with (vals := [VLit (Integer 5)]) (eff := [[]]) (ids := [0]); auto.
      * intros. inversion H1; inversion H5. apply eval_lit.
      * reflexivity.
      * eapply eval_let with (vals := [VLit (Integer 6)]) (eff := [[]]) (ids := [0]); auto.
        - intros. inversion H1; inversion H5. apply eval_lit.
        - reflexivity.
        - eapply eval_call with (vals := [VLit (Integer 5); VLit (Integer 6)])
                                (eff := [[];[]]) (ids := [0;0]); auto.
          + intros. inversion H1; inversion H5; try(inversion H7); apply eval_var.
    } assumption.
Qed.

Example let_1_comm_2_list (env: Environment) (e1 e2 : Expression) (t t' v1 v2 : Value) 
   (eff eff1 eff2 : SideEffectList) (A B : Var) (VarHyp : A <> B) (id id1 id2 : nat)
(Hypo1 : |env, id, e1, eff| -e> | id + id1, inl v1, eff ++ eff1|)
(Hypo2 : |env, id + id2, e1, eff ++ eff2| -e> | id + id1 + id2, inl v1, eff ++ eff2 ++ eff1|)
(Hypo1' : |env, id, e2, eff| -e> | id + id2, inl v2, eff ++ eff2|)
(Hypo2' : |env, id + id1, e2, eff ++ eff1| -e> | id + id2 + id1, inl v2, eff ++ eff1 ++ eff2|) :
|env, id, ELet [A; B] [e1 ; e2]
     (ECall "plus"%string [EVar A ; EVar B]), eff| -e> |id + id1 + id2, inl t, eff ++ eff1 ++ eff2|
->
|env, id, ELet [A; B] [e2 ; e1]
     (ECall "plus"%string [EVar A ; EVar B]), eff| -e> |id + id2 + id1, inl t', eff ++ eff2 ++ eff1|
->
t = t'.
Proof.
  intros.
  (* FROM LET HYPO1 *)
  inversion H. subst. simpl in H4, H5, H6.
  pose (EE1 := element_exist Value 1 vals H4).
  inversion EE1 as [v1']. inversion H1. subst. inversion H4.
  pose (EE2 := element_exist Value 0 x H3).
  inversion EE2 as [v2']. inversion H2. subst. inversion H4. 
  apply eq_sym, length_zero_iff_nil in H8. subst.
  pose (EE3 := element_exist _ _ _ H5). inversion EE3 as [eff1']. inversion H7. subst. inversion H5.
  pose (EE4 := element_exist _ _ _ H10). inversion EE4 as [eff2']. inversion H8. subst. inversion H5.
  apply eq_sym, length_zero_iff_nil in H12. subst.
  pose (EE5 := element_exist nat _ _ H6). inversion EE5 as [id1']. inversion H11. subst. inversion H6.
  pose (EE6 := element_exist _ _ _ H13). inversion EE6 as [id2']. inversion H12. subst. inversion H6.
  apply eq_sym, length_zero_iff_nil in H17. subst.
  (* FROM LET HYPO2 *)
  inversion H0. subst. simpl in H19, H20, H21.
  pose (EE1' := element_exist _ _ _ H19). inversion EE1' as [v2'']. inversion H16. subst. inversion H19.
  pose (EE2' := element_exist _ _ _ H18). inversion EE2' as [v1'']. inversion H17. subst. inversion H19.
  apply eq_sym, length_zero_iff_nil in H23. subst.
  pose (EE3' := element_exist _ _ _ H20). inversion EE3' as [eff2'']. inversion H22. subst. inversion H20.
  pose (EE4' := element_exist _ _ _ H25). inversion EE4' as [eff1'']. inversion H23. subst. inversion H25.
  apply eq_sym, length_zero_iff_nil in H27. subst.

  pose (EE5' := element_exist _ _ _ H21). inversion EE5' as [id2'']. inversion H26. subst. inversion H21.
  pose (EE6' := element_exist _ _ _ H28). inversion EE6' as [id1'']. inversion H27. subst. inversion H21.
  apply eq_sym, length_zero_iff_nil in H32. subst.

  (* assert (v1' = v1 /\ eff1' = eff1).
  { *)
    pose (P1 := H9 0 Nat.lt_0_2).
    unfold concatn in P1. simpl in P1. rewrite app_nil_r, app_nil_r in P1.
    pose (WD1 := determinism Hypo1).
    pose (PC1 := WD1 _ _ _ P1).
    destruct PC1. destruct H32. apply app_inv_head in H32. inversion H31. subst.
  (* } *)
  
  (* assert (v2'' = v2 /\ eff2'' = eff2).
  { *)
    pose (P2 := H24 0 Nat.lt_0_2).
    unfold concatn in P2. simpl in P2. rewrite app_nil_r, app_nil_r in P2.
    pose (WD2 := determinism Hypo1').
    pose (PC2 := WD2 _ _ _ P2).
    destruct PC2. destruct H33. inversion H32. apply app_inv_head in H33. subst. auto.
  (* } *)

  (* assert (v1'' = v1 /\ v2' = v2 /\ eff1'' = eff1 /\ eff2' = eff2).
  { *)
    pose (P3 := H24 1 Nat.lt_1_2).
    unfold concatn in P3. simpl in P3. rewrite app_nil_r, app_nil_r in P3.
    pose (WD3 := determinism Hypo2).
    pose (PC3 := WD3 _ _ _ P3).
    inversion PC3. inversion H34. inversion H33. apply app_inv_head, app_inv_head in H35. subst.
    pose (P4 := H9 1 Nat.lt_1_2).
    unfold concatn in P4. simpl in P4. rewrite app_nil_r, app_nil_r in P4.
    pose (WD4 := determinism Hypo2').
    pose (PC4 := WD4 _ _ _ P4).
    inversion PC4. inversion H36. inversion H35. apply app_inv_head, app_inv_head in H37. subst.
    clear EE1. clear EE2. clear EE3. clear EE4. clear EE5. clear EE6.
  (* } *)

  (* FROM CALL HYPOS *)
 (* FROM CALL HYPO1 *)
  inversion H15. subst. simpl in H39, H40, H41.
  pose (EC1 := element_exist _ _ _ H39). inversion EC1 as [v10]. inversion H37. subst. 
  inversion H39.
  pose (EC2 := element_exist _ _ _ H43). inversion EC2 as [v20]. inversion H38. subst. 
  inversion H39.
  apply eq_sym, length_zero_iff_nil in H46. subst.
  pose (EC3 := element_exist _ _ _ H40). inversion EC3 as [eff10]. inversion H44. subst.
  inversion H40.
  pose (EC4 := element_exist _ _ _ H47). inversion EC4 as [eff20]. inversion H46. subst.
  inversion H40.
  apply eq_sym, length_zero_iff_nil in H49. subst.
  pose (EC5 := element_exist _ _ _ H41). inversion EC5 as [id10]. inversion H48. subst.
  inversion H41.
  pose (EC6 := element_exist _ _ _ H51). inversion EC6 as [id20]. inversion H49. subst.
  inversion H41.
  apply eq_sym, length_zero_iff_nil in H53. subst.
  (* FROM CALL HYPO2 *)
  inversion H30. subst. simpl in H54, H55, H56.
  pose (EC1' := element_exist _ _ _ H54). inversion EC1' as [v20']. inversion H52. subst.
  inversion H54.
  pose (EC2' := element_exist _ _ _ H58). inversion EC2' as [v10']. inversion H53. subst.
  inversion H54.
  apply eq_sym, length_zero_iff_nil in H61. subst.
  pose (EC3' := element_exist _ _ _ H55). inversion EC3' as [eff20']. inversion H59. subst.
  inversion H55.
  pose (EC4' := element_exist _ _ _ H62). inversion EC4' as [eff10']. inversion H61. subst.
  inversion H55.
  apply eq_sym, length_zero_iff_nil in H64. subst.
  pose (EC5' := element_exist _ _ _ H56). inversion EC5' as [id20']. inversion H63. subst.
  inversion H56.
  pose (EC6' := element_exist _ _ _ H66). inversion EC6' as [id10']. inversion H64. subst.
  inversion H56.
  apply eq_sym, length_zero_iff_nil in H68. subst.

  unfold concatn in H45, H60. simpl app in H45, H60.
  pose (PUM1 := plus_effect_unmodified _ _ _ H45).
  pose (PUM2 := plus_effect_unmodified _ _ _ H60).
  rewrite app_nil_r, app_nil_r, <- app_nil_r in PUM1, PUM2.
  apply app_inv_head in PUM1. apply app_inv_head in PUM2.
  apply app_eq_nil in PUM1. apply app_eq_nil in PUM2.
  inversion PUM1. inversion PUM2. subst.
  (* EVERYTHING IS EQUAL *)
  (* assert (v1' = v1 /\ v1'' = v1 /\ v2' = v2 /\ v2'' = v2).
  { *)
    clear P1. clear P2.
    pose (P1 := H42 0 Nat.lt_0_2).
    pose (P2 := H42 1 Nat.lt_1_2).
    pose (P1' := H57 1 Nat.lt_1_2).
    pose (P2' := H57 0 Nat.lt_0_2).
    unfold concatn in P1, P2, P1', P2'. simpl in P1, P2, P1', P2'.
    rewrite app_nil_r, app_nil_r in P1, P1', P2, P2'.
    inversion P1. inversion P2. inversion P1'. inversion P2'. subst.
    rewrite get_value_there in H73, H91.
    2-3 : congruence.
    rewrite get_value_here in H73, H79, H85, H91.
    inversion H73. inversion H79. inversion H85. inversion H91. subst.
(* } *)
  rewrite app_nil_r, app_nil_r in H45, H60.
  
  apply (plus_comm_basic_value _ (eff ++ eff2' ++ eff1'')) in H45.
  rewrite H45 in H60. inversion H60.
  reflexivity.
Qed.

Example exp_to_fun (env : Environment) (e : Expression) (t : Value + Exception) (x : Var) 
    (eff eff' : SideEffectList) (id id' : nat):
|env, S id, e, eff| -e> |S id + id', t, eff ++ eff'|
<->
|env, id, ELet [x] [EFun [] e] (EApp (EVar x) []), eff| -e> | (S id) + id', t, eff ++ eff'|.
Proof.
  split; intros.
  * apply eval_let with (vals := [VClos env [] id [] e]) (eff := [[]]) (eff2 := eff') (ids := [S id]); auto.
    - intros. inversion H0; inversion H2. apply eval_fun.
    - unfold concatn. simpl. rewrite app_nil_r. reflexivity.
    - simpl. eapply eval_apply with (vals := []) (var_list := []) (body := e) (ref := env)
                                    (ext := []) (eff := []) (eff2 := []) (eff3 := eff') (ids := []); auto.
      + assert (get_value (insert_value env (inl x) (VClos env [] id [] e)) (inl x) 
                = inl (VClos env [] id [] e)). { apply get_value_here. }
        rewrite <- H0. unfold concatn. simpl. simpl_app. apply eval_var.
      + intros. inversion H0.
      + simpl. unfold concatn. simpl. repeat(rewrite app_nil_r). reflexivity.
      + unfold concatn. simpl. repeat(rewrite app_nil_r). unfold get_env. simpl. assumption.
  * inversion H.
    - pose (EE1 := element_exist Value 0 vals H3). inversion EE1. inversion H15. subst.
      inversion H3. apply eq_sym, length_zero_iff_nil in H1.
      pose (EE2 := element_exist _ _ _ H4). inversion EE2. inversion H0. subst. inversion H4.
      apply eq_sym, length_zero_iff_nil in H2.
      pose (EE3 := element_exist _ _ _ H5). inversion EE3. inversion H1. subst. inversion H5.
      apply eq_sym, length_zero_iff_nil in H6. subst.
      (* assert (x2 = []).
      { *)
        pose (P := H8 0 Nat.lt_0_1). unfold concatn in P. simpl in P. inversion P.
        rewrite app_nil_r, app_nil_r in H17. rewrite <- app_nil_r in H17 at 1.
        apply app_inv_head in H17. subst.
      (* } *)
      (* assert (x0 = VClos env [] (count_closures env) [] e).
      { *)
        (* assert (In (EFun [] e, x0) (combine [EFun [] e] [x0])). { simpl. auto. } 
        pose (P1 := H6 0 Nat.lt_0_1). simpl in P1. inversion P1. reflexivity.  *)
      (* } *)
      subst. inversion H14.
      + subst.
        apply eq_sym, length_zero_iff_nil in H11. subst.
        apply eq_sym, length_zero_iff_nil in H12. subst.
        apply eq_sym, length_zero_iff_nil in H7. subst.
        unfold concatn in H9. simpl in H9. inversion H9.
        unfold concatn in H19. simpl in H19.
        rewrite app_nil_r in H7, H20. subst.
        rewrite <- app_nil_r in H20 at 1. apply app_inv_head in H20. subst.
        rewrite app_nil_r, app_nil_r, app_nil_r in H19. apply app_inv_head in H19. subst.
        (* inversion H7. *) rewrite get_value_here in H18. inversion H18. subst.
        unfold concatn in H24. simpl in H24. repeat (rewrite app_nil_r in H24). assumption.
      + subst. inversion H18. rewrite get_value_here in H16. congruence.
      + subst. inversion H9.
      + subst. inversion H11. rewrite get_value_here in H22. inversion H22. subst.
        pose (P1 := H16 env [] [] e). congruence.
      + subst. inversion H11. rewrite get_value_here in H22. inversion H22. subst.
        rewrite <- H7 in H16. contradiction.
    - simpl in H4. inversion H4.
      + subst. simpl in H17. rewrite H17 in H15. inversion H15.
      + inversion H17.
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
  |env, id0, e2, eff| -e> |id0 + id2, inl x0, eff ++ eff2| -> 
  |append_vars_to_env [A] [x] env, id0 + id1, e2, eff ++ eff1| -e> | id0 + id1 + id2, inl x0, eff ++ eff1 ++ eff2| ->
  |env, id0, e1, eff| -e> |id0 + id1, inl x, eff ++ eff1| -> 
  |append_vars_to_env [A] [x0] env, id0 + id2, e1, eff ++ eff2| -e> |id0 + id2 + id1, inl x, eff ++ eff2 ++ eff1| ->
  |env, id0, ELet [A] [e1] (ELet [B] [e2] 
        (ECall "plus"%string [EVar A ; EVar B])), eff| -e> | id0 + id1 + id2, inl t, eff ++ eff1 ++ eff2|
->
|env, id0, ELet [A] [e2] (ELet [B] [e1]
        (ECall "plus"%string [EVar A ; EVar B])), eff| -e> | id0 + id2 + id1, inl t, eff ++ eff2 ++ eff1|
.
Proof.
  * intros. inversion H3. subst.
    pose (EE1 := element_exist Value 0 vals H7).
    pose (EE2 := element_exist _ 0 _ H8).
    pose (EE3 := element_exist _ 0 _ H9).
    inversion EE1 as [x']. inversion EE2 as [eff1']. inversion EE3 as [id1'].
    inversion H4. inversion H5. inversion H6. subst. 
    inversion H7. inversion H8. inversion H9.
    apply eq_sym, length_zero_iff_nil in H11.
    apply eq_sym, length_zero_iff_nil in H13.
    apply eq_sym, length_zero_iff_nil in H14. subst.
    assert (x' = x /\ eff1' = eff1 /\ id1' = (id0 + id1)%nat).
    {
      pose (P := H12 0 Nat.lt_0_1). unfold concatn in P. simpl in P. rewrite app_nil_r, app_nil_r in P.
      pose (WD := determinism H1 _ _ _ P). destruct WD. destruct H11. inversion H10. apply app_inv_head in H11.
      subst. auto.
    }
    destruct H10. destruct H11. subst.
    inversion H18. subst.
    pose (EE1' := element_exist Value 0 vals H14).
    pose (EE2' := element_exist _ 0 _ H15).
    pose (EE3' := element_exist _ 0 _ H16).
    inversion EE1' as [x0']. inversion EE2' as [eff2']. inversion EE3' as [id2'].
    inversion H10. inversion H11. inversion H13. subst. 
    inversion H14. inversion H15. inversion H16.
    apply eq_sym, length_zero_iff_nil in H20.
    apply eq_sym, length_zero_iff_nil in H22.
    apply eq_sym, length_zero_iff_nil in H23. subst.
    assert (x0' = x0 /\ eff2' = eff2 /\ id2' = (id0 + id1 + id2)%nat).
    {
      pose (P := H21 0 Nat.lt_0_1). unfold concatn in P. simpl in P.
      rewrite app_nil_r, app_nil_r, app_nil_r in P.
      pose (WD := determinism H0 _ _ _ P). 
      destruct WD. destruct H20. inversion H19.
      rewrite app_assoc in H20. apply app_inv_head in H20. subst. auto.
    }
    destruct H19. destruct H20. subst.
   (*proving starts*)
   apply eval_let with (vals := [x0]) (eff := [eff2]) (eff2 := eff1) (ids := [(id0 + id2)%nat]); auto.
   - intros. inversion H19.
     + unfold concatn. simpl. rewrite app_nil_r, app_nil_r. assumption.
     + inversion H22.
   - unfold concatn. simpl. rewrite app_nil_r, app_assoc. auto.
   - apply eval_let with (vals := [x]) (eff := [eff1]) (eff2 := []) (ids := [(id0 + id2 + id1)%nat]); auto.
     + intros. inversion H19.
       ** subst. unfold concatn. simpl concat. simpl nth.
       rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc. assumption.
       ** inversion H22.
     + unfold concatn. simpl. rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc. auto.
   (* call information *)
     + inversion H27. subst.
       pose (EC1 := element_exist _ 1 _ H22).
       pose (EC2 := element_exist _ 1 _ H23).
       pose (EC3 := element_exist _ 1 _ H24).
       inversion EC1 as [x']. inversion EC2 as [eff1']. inversion EC3 as [id1'].
       inversion H19. inversion H20. inversion H28. subst. 
       inversion H22. inversion H23. inversion H24.
       pose (EC1' := element_exist _ 0 _ H31).
       pose (EC2' := element_exist _ 0 _ H32).
       pose (EC3' := element_exist _ 0 _ H33).
       inversion EC1' as [x0']. inversion EC2' as [eff2']. inversion EC3' as [id2'].
       inversion H29. inversion H34. inversion H36. subst. 
       inversion H31. inversion H32. inversion H33.
       apply eq_sym, length_zero_iff_nil in H38.
       apply eq_sym, length_zero_iff_nil in H39.
       apply eq_sym, length_zero_iff_nil in H40. subst.
       assert (x' = x /\ x0' = x0 /\ eff1' = [] /\ eff2' = [] /\ id1' = (id0 + id1 + id2)%nat /\ id2' = (id0 + id1 + id2)%nat).
       {
         pose (P1 := H25 0 Nat.lt_0_2).
         pose (P2 := H25 1 Nat.lt_1_2).
         inversion P1. inversion P2. subst.
         
         simpl_concatn_H H51. simpl_concatn_H H44.
         rewrite <- app_nil_r in H44 at 1.
         apply app_inv_head in H44. subst.
         rewrite <- app_nil_r in H51 at 1.
         apply app_inv_head in H51. subst.
         
         simpl in H41, H48. subst.
         
         rewrite get_value_there in H43.
           - rewrite get_value_here in H43. inversion H43.
             rewrite get_value_here in H50. inversion H50. split; auto.
           - unfold not. intros. inversion H37. congruence.
       }
       destruct H37. destruct H38. destruct H39. destruct H40. destruct H41. subst.
       
       (* BACK TO CALL PROOF *)
       apply eval_call with (vals := [x0 ; x]) (eff := [[];[]]) (ids := [(id0 + id2 + id1)%nat; (id0 + id2 + id1)%nat]); auto.
       ** intros. inversion H37. 2: inversion H39. 3: inversion H41.
         -- simpl. assert (get_value (insert_value (insert_value env (inl A) x0) 
                                     (inl B) x) (inl B) = inl x). 
                                     { apply get_value_here. }
            rewrite <- H38. apply eval_var.
         -- simpl. subst. assert (get_value (insert_value (insert_value env (inl A) x0) 
                                           (inl B) x) (inl A) = inl x0).
                                           { rewrite get_value_there. apply get_value_here.
                                             unfold not. intros. inversion H33.
                                             congruence. }
            rewrite <- H38. apply eval_var.
       ** unfold concatn. simpl concat. rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc.
          unfold concatn in H30. simpl concat in H30.
          rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc in H30.
          apply plus_comm_basic_value with (eff0 := eff ++ eff1 ++ eff2). assumption.
Qed.

Example let_2_comm_eq (env: Environment)(e1 e2 : Expression) (t x x0 : Value) 
    (eff eff1 eff2 : SideEffectList) (id0 id1 id2 : nat) (A B : Var) (VarHyp : A <> B) :
  |env, id0, e2, eff| -e> |id0 + id2, inl x0, eff ++ eff2| -> 
  |append_vars_to_env [A] [x] env, id0 + id1, e2, eff ++ eff1| -e> | id0 + id1 + id2, inl x0, eff ++ eff1 ++ eff2| ->
  |env, id0, e1, eff| -e> |id0 + id1, inl x, eff ++ eff1| -> 
  |append_vars_to_env [A] [x0] env, id0 + id2, e1, eff ++ eff2| -e> |id0 + id2 + id1, inl x, eff ++ eff2 ++ eff1| ->
  |env, id0, ELet [A] [e1] (ELet [B] [e2] 
        (ECall "plus"%string [EVar A ; EVar B])), eff| -e> | id0 + id1 + id2, inl t, eff ++ eff1 ++ eff2|
<->
|env, id0, ELet [A] [e2] (ELet [B] [e1]
        (ECall "plus"%string [EVar A ; EVar B])), eff| -e> | id0 + id2 + id1, inl t, eff ++ eff2 ++ eff1|
.
Proof.
  split.
  * apply let_2_comm with (x := x) (x0 := x0); try (assumption).
  * apply let_2_comm with (x := x0) (x0 := x); try (assumption).
Qed.

(* THIS THEOREM COULD BE PROVEN WITH STRONG DETERMINISM
Example let_1_comm_2_list (env: Environment) (e1 e2 : Expression) (t t' : Value) eff eff1 eff2:
|env, ELet ["X"%string; "Y"%string] [e1 ; e2] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]), eff| -e> |inl t, eff ++ eff1 ++ eff2|
->
|env, ELet ["X"%string; "Y"%string] [e2 ; e1] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]), eff| -e> |inl t', eff ++ eff2 ++ eff1|
->
t = t'. *)

Example let_2_binding_swap (env: Environment)(e1 e2 : Expression) (t x x0 : Value) 
    (eff eff1 eff2 : SideEffectList) (A B : Var) (id0 id1 id2 : nat) (VarHyp : A <> B) :
  |env, id0, e2, eff| -e> |id0 + id2, inl x0, eff ++ eff2| -> 
  |append_vars_to_env [A] [x] env, id0 + id1, e2, eff ++ eff1| -e> | id0 + id1 + id2, inl x0, eff ++ eff1 ++ eff2| ->
  |env, id0, e1, eff| -e> |id0 + id1, inl x, eff ++ eff1| -> 
  |append_vars_to_env [B] [x0] env, id0 + id2, e1, eff ++ eff2| -e> |id0 + id2 + id1, inl x, eff ++ eff2 ++ eff1| ->
  |env, id0, ELet [A] [e1] (ELet [B] [e2] 
        (ECall "plus"%string [EVar A ; EVar B])), eff| -e> |id0 + id1 + id2, inl t, eff ++ eff1 ++ eff2|
<->
|env, id0, ELet [B] [e2] (ELet [A] [e1]
        (ECall "plus"%string [EVar A ; EVar B])), eff| -e> |id0 + id2 + id1, inl t, eff ++ eff2 ++ eff1|
.
Proof.
  split.
  * intros. inversion H3. subst.
    pose (EE1 := element_exist Value 0 vals H7).
    pose (EE2 := element_exist _ 0 _ H8).
    pose (EE3 := element_exist _ 0 _ H9).
    inversion EE1 as [x']. inversion EE2 as [eff1']. inversion EE3 as [id1'].
    inversion H4. inversion H5. inversion H6. subst. 
    inversion H7. inversion H8. inversion H9.
    apply eq_sym, length_zero_iff_nil in H11.
    apply eq_sym, length_zero_iff_nil in H13.
    apply eq_sym, length_zero_iff_nil in H14. subst.
    assert (x' = x /\ eff1' = eff1 /\ id1' = (id0 + id1)%nat).
    {
      pose (P := H12 0 Nat.lt_0_1). unfold concatn in P. simpl in P. rewrite app_nil_r, app_nil_r in P.
      pose (WD := determinism H1 _ _ _ P). destruct WD. destruct H11. inversion H10. apply app_inv_head in H11.
      subst. auto.
    }
    destruct H10. destruct H11. subst.
    inversion H18. subst.
    pose (EE1' := element_exist Value 0 vals H14).
    pose (EE2' := element_exist _ 0 _ H15).
    pose (EE3' := element_exist _ 0 _ H16).
    inversion EE1' as [x0']. inversion EE2' as [eff2']. inversion EE3' as [id2'].
    inversion H10. inversion H11. inversion H13. subst. 
    inversion H14. inversion H15. inversion H16.
    apply eq_sym, length_zero_iff_nil in H20.
    apply eq_sym, length_zero_iff_nil in H22.
    apply eq_sym, length_zero_iff_nil in H23. subst.
    assert (x0' = x0 /\ eff2' = eff2 /\ id2' = (id0 + id1 + id2)%nat).
    {
      pose (P := H21 0 Nat.lt_0_1). unfold concatn in P. simpl in P.
      rewrite app_nil_r, app_nil_r, app_nil_r in P.
      pose (WD := determinism H0 _ _ _ P). 
      destruct WD. destruct H20. inversion H19.
      rewrite app_assoc in H20. apply app_inv_head in H20. subst. auto.
    }
    destruct H19. destruct H20. subst.
   (*proving starts*)
   apply eval_let with (vals := [x0]) (eff := [eff2]) (eff2 := eff1) (ids := [(id0 + id2)%nat]); auto.
   - intros. inversion H19.
     + unfold concatn. simpl. rewrite app_nil_r, app_nil_r. assumption.
     + inversion H22.
   - unfold concatn. simpl. rewrite app_nil_r, app_assoc. auto.
   - apply eval_let with (vals := [x]) (eff := [eff1]) (eff2 := []) (ids := [(id0 + id2 + id1)%nat]); auto.
     + intros. inversion H19.
       ** subst. unfold concatn. simpl concat. simpl nth.
       rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc. simpl. assumption.
       ** inversion H22.
     + unfold concatn. simpl. rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc. auto.
   (* call information *)
     + inversion H27. subst.
       pose (EC1 := element_exist _ 1 _ H22).
       pose (EC2 := element_exist _ 1 _ H23).
       pose (EC3 := element_exist _ 1 _ H24).
       inversion EC1 as [x']. inversion EC2 as [eff1']. inversion EC3 as [id1'].
       inversion H19. inversion H20. inversion H28. subst. 
       inversion H22. inversion H23. inversion H24.
       pose (EC1' := element_exist _ 0 _ H31).
       pose (EC2' := element_exist _ 0 _ H32).
       pose (EC3' := element_exist _ 0 _ H33).
       inversion EC1' as [x0']. inversion EC2' as [eff2']. inversion EC3' as [id2'].
       inversion H29. inversion H34. inversion H36. subst. 
       inversion H31. inversion H32. inversion H33.
       apply eq_sym, length_zero_iff_nil in H38.
       apply eq_sym, length_zero_iff_nil in H39.
       apply eq_sym, length_zero_iff_nil in H40. subst.
       assert (x' = x /\ x0' = x0 /\ eff1' = [] /\ eff2' = [] /\ id1' = (id0 + id1 + id2)%nat /\ id2' = (id0 + id1 + id2)%nat).
       {
         pose (P1 := H25 0 Nat.lt_0_2).
         pose (P2 := H25 1 Nat.lt_1_2).
         inversion P1. inversion P2. subst.
         
         simpl_concatn_H H51. simpl_concatn_H H44.
         rewrite <- app_nil_r in H44 at 1.
         apply app_inv_head in H44. subst.
         rewrite <- app_nil_r in H51 at 1.
         apply app_inv_head in H51. subst.
         
         simpl in H41, H48. subst.
         
         rewrite get_value_there in H43.
           - rewrite get_value_here in H43. inversion H43.
             rewrite get_value_here in H50. inversion H50. split; auto.
           - unfold not. intros. inversion H37. congruence.
       }
       destruct H37. destruct H38. destruct H39. destruct H40. destruct H41. subst.
       
       (* BACK TO CALL PROOF *)
       apply eval_call with (vals := [x ; x0]) (eff := [[];[]]) (ids := [(id0 + id2 + id1)%nat; (id0 + id2 + id1)%nat]); auto.
       ** intros. inversion H37. 2: inversion H39. 3: inversion H41.
         -- simpl. assert (get_value (insert_value (insert_value env (inl B) x0) (inl A) x) (inl B) = inl x0). 
                                     { rewrite get_value_there. apply get_value_here.
                                             unfold not. intros. inversion H33.
                                             congruence. }
            rewrite <- H38. apply eval_var.
         -- simpl. subst. assert (get_value (insert_value (insert_value env (inl B) x0) (inl A) x) (inl A) = inl x).
                                           { apply get_value_here. }
            rewrite <- H38. apply eval_var.
       ** unfold concatn. simpl concat. rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc.
          unfold concatn in H30. simpl concat in H30.
          rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc in H30.
          apply plus_effect_changeable with (eff0 := eff ++ eff1 ++ eff2). assumption.
  * intros. inversion H3. subst.
    pose (EE1 := element_exist Value 0 vals H7).
    pose (EE2 := element_exist _ 0 _ H8).
    pose (EE3 := element_exist _ 0 _ H9).
    inversion EE1 as [x0']. inversion EE2 as [eff2']. inversion EE3 as [id2'].
    inversion H4. inversion H5. inversion H6. subst. 
    inversion H7. inversion H8. inversion H9.
    apply eq_sym, length_zero_iff_nil in H11.
    apply eq_sym, length_zero_iff_nil in H13.
    apply eq_sym, length_zero_iff_nil in H14. subst.
    assert (x0' = x0 /\ eff2' = eff2 /\ id2' = (id0 + id2)%nat).
    {
      pose (P := H12 0 Nat.lt_0_1). unfold concatn in P. simpl in P. rewrite app_nil_r, app_nil_r in P.
      pose (WD := determinism H _ _ _ P). destruct WD. destruct H11. inversion H10. apply app_inv_head in H11.
      subst. auto.
    }
    destruct H10. destruct H11. subst.
    inversion H18. subst.
    pose (EE1' := element_exist Value 0 vals H14).
    pose (EE2' := element_exist _ 0 _ H15).
    pose (EE3' := element_exist _ 0 _ H16).
    inversion EE1' as [x']. inversion EE2' as [eff1']. inversion EE3' as [id1'].
    inversion H10. inversion H11. inversion H13. subst. 
    inversion H14. inversion H15. inversion H16.
    apply eq_sym, length_zero_iff_nil in H20.
    apply eq_sym, length_zero_iff_nil in H22.
    apply eq_sym, length_zero_iff_nil in H23. subst.
    assert (x' = x /\ eff1' = eff1 /\ id1' = (id0 + id1 + id2)%nat).
    {
      pose (P := H21 0 Nat.lt_0_1). unfold concatn in P. simpl in P.
      rewrite app_nil_r, app_nil_r, app_nil_r in P.
      pose (WD := determinism H2 _ _ _ P). 
      destruct WD. destruct H20. inversion H19.
      rewrite app_assoc in H20. apply app_inv_head in H20. subst.
      split.
      - reflexivity.
      - split. reflexivity. omega.
    }
    destruct H19. destruct H20. subst.
   (*proving starts*)
   apply eval_let with (vals := [x]) (eff := [eff1]) (eff2 := eff2) (ids := [(id0 + id1)%nat]); auto.
   - intros. inversion H19.
     + unfold concatn. simpl. rewrite app_nil_r, app_nil_r. assumption.
     + inversion H22.
   - unfold concatn. simpl. rewrite app_nil_r, app_assoc. auto.
   - apply eval_let with (vals := [x0]) (eff := [eff2]) (eff2 := []) (ids := [(id0 + id1 + id2)%nat]); auto.
     + intros. inversion H19.
       ** subst. unfold concatn. simpl concat. simpl nth.
       rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc. simpl. assumption.
       ** inversion H22.
     + unfold concatn. simpl. rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc. auto.
   (* call information *)
     + inversion H27. subst.
       pose (EC1 := element_exist _ 1 _ H22).
       pose (EC2 := element_exist _ 1 _ H23).
       pose (EC3 := element_exist _ 1 _ H24).
       inversion EC1 as [x']. inversion EC2 as [eff1']. inversion EC3 as [id1'].
       inversion H19. inversion H20. inversion H28. subst. 
       inversion H22. inversion H23. inversion H24.
       pose (EC1' := element_exist _ 0 _ H31).
       pose (EC2' := element_exist _ 0 _ H32).
       pose (EC3' := element_exist _ 0 _ H33).
       inversion EC1' as [x0']. inversion EC2' as [eff2']. inversion EC3' as [id2'].
       inversion H29. inversion H34. inversion H36. subst. 
       inversion H31. inversion H32. inversion H33.
       apply eq_sym, length_zero_iff_nil in H38.
       apply eq_sym, length_zero_iff_nil in H39.
       apply eq_sym, length_zero_iff_nil in H40. subst.
       assert (x' = x /\ x0' = x0 /\ eff1' = [] /\ eff2' = [] /\ id1' = (id0 + id1 + id2)%nat /\ id2' = (id0 + id1 + id2)%nat).
       {
         pose (P1 := H25 0 Nat.lt_0_2).
         pose (P2 := H25 1 Nat.lt_1_2).
         inversion P1. inversion P2. subst.
         
         simpl_concatn_H H51. simpl_concatn_H H44.
         rewrite <- app_nil_r in H44 at 1.
         apply app_inv_head in H44. subst.
         rewrite <- app_nil_r in H51 at 1.
         apply app_inv_head in H51. subst.
         
         simpl in H41, H48. subst.
         
         rewrite get_value_here in H43. inversion H43.
         rewrite get_value_there in H50.
           - rewrite get_value_here in H50. inversion H50. split; auto.
           - congruence.
       }
       destruct H37. destruct H38. destruct H39. destruct H40. destruct H41. subst.
       
       (* BACK TO CALL PROOF *)
       apply eval_call with (vals := [x ; x0]) (eff := [[];[]]) (ids := [(id0 + id2 + id1)%nat; (id0 + id2 + id1)%nat]); auto.
       ** intros. inversion H37. 2: inversion H39. 3: inversion H41.
         -- simpl. assert (get_value (insert_value (insert_value env (inl A) x) (inl B) x0) (inl B) = inl x0). { apply get_value_here. }
                                     
            rewrite <- H38. apply eval_var.
         -- simpl. subst. assert (get_value (insert_value (insert_value env (inl A) x) (inl B) x0) (inl A) = inl x). { rewrite get_value_there. apply get_value_here.
                                             unfold not. intros. inversion H33.
                                             congruence. }
                                           
            rewrite <- H38. assert ((id0 + id2 + id1)%nat = (id0 + id1 + id2)%nat). { omega. } rewrite H40. apply eval_var.
       ** unfold concatn. simpl concat. rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc.
          unfold concatn in H30. simpl concat in H30.
          rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc in H30.
          apply plus_effect_changeable with (eff0 := eff ++ eff2 ++ eff1). assumption.
Qed.

Example let_1_binding_swap_2_list (env: Environment) (e1 e2 : Expression) (t t' v1 v2 : Value) 
   (eff eff1 eff2 : SideEffectList) (A B : Var) (VarHyp : A <> B)
(Hypo1 : |env, e1, eff| -e> |inl v1, eff ++ eff1|)
(Hypo2 : |env, e1, eff ++ eff2| -e> |inl v1, eff ++ eff2 ++ eff1|)
(Hypo1' : |env, e2, eff| -e> |inl v2, eff ++ eff2|)
(Hypo2' : |env, e2, eff ++ eff1| -e> |inl v2, eff ++ eff1 ++ eff2|) :
|env, ELet [A; B] [e1 ; e2]
     (ECall "plus"%string [EVar A ; EVar B]), eff| -e> |inl t, eff ++ eff1 ++ eff2|
->
|env, ELet [B; A] [e2 ; e1]
     (ECall "plus"%string [EVar B ; EVar A]), eff| -e> |inl t', eff ++ eff2 ++ eff1|
->
t = t'.
Proof.
  intros.
  (* FROM LET HYPO1 *)
  inversion H. subst. simpl in H4. simpl in H5.
  pose (EE1 := element_exist Value 1 vals H4). inversion EE1 as [v1']. inversion H1. subst. inversion H4.
  pose (EE2 := element_exist Value 0 x H3). inversion EE2 as [v2']. inversion H2. subst. inversion H4. 
  apply eq_sym, length_zero_iff_nil in H8. subst.
  pose (EE3 := element_exist _ _ _ H5). inversion EE3 as [eff1']. inversion H6. subst. inversion H5.
  pose (EE4 := element_exist _ _ _ H9). inversion EE4 as [eff2']. inversion H8. subst. inversion H5.
  apply eq_sym, length_zero_iff_nil in H13. subst.
  (* FROM LET HYPO2 *)
  inversion H0. subst. simpl in H15, H16.
  pose (EE1' := element_exist _ _ _ H15). inversion EE1' as [v2'']. inversion H10. subst. inversion H15.
  pose (EE2' := element_exist _ _ _ H14). inversion EE2' as [v1'']. inversion H13. subst. inversion H15.
  apply eq_sym, length_zero_iff_nil in H19. subst.
  pose (EE3' := element_exist _ _ _ H16). inversion EE3' as [eff2'']. inversion H17. subst. inversion H16.
  pose (EE4' := element_exist _ _ _ H20). inversion EE4' as [eff1'']. inversion H19. subst. inversion H16.
  apply eq_sym, length_zero_iff_nil in H24. subst.

  assert (v1' = v1 /\ eff1' = eff1).
  {
    pose (P1 := H7 0 Nat.lt_0_2).
    unfold concatn in P1. simpl in P1. rewrite app_nil_r, app_nil_r in P1.
    pose (WD1 := determinism _ Hypo1).
    pose (PC1 := WD1 _ _ P1).
    inversion PC1. inversion H21. apply app_inv_head in H24. subst. auto.
  }
  inversion H21. subst.
  
  assert (v2'' = v2 /\ eff2'' = eff2).
  {
    pose (P1 := H18 0 Nat.lt_0_2).
    unfold concatn in P1. simpl in P1. rewrite app_nil_r, app_nil_r in P1.
    pose (WD1 := determinism _ Hypo1').
    pose (PC1 := WD1 _ _ P1).
    inversion PC1. inversion H24. apply app_inv_head in H25. subst. auto.
  }
  inversion H24. subst.
  assert (v1'' = v1 /\ v2' = v2 /\ eff1'' = eff1 /\ eff2' = eff2).
  {
    pose (P1 := H18 1 Nat.lt_1_2).
    unfold concatn in P1. simpl in P1. rewrite app_nil_r, app_nil_r in P1.
    pose (WD1 := determinism _ Hypo2).
    pose (PC1 := WD1 _ _ P1).
    inversion PC1. inversion H25. apply app_inv_head, app_inv_head in H26. subst.
    pose (P2 := H7 1 Nat.lt_1_2).
    unfold concatn in P2. simpl in P2. rewrite app_nil_r, app_nil_r in P2.
    pose (WD2 := determinism _ Hypo2').
    pose (PC2 := WD2 _ _ P2).
    inversion PC2. inversion H26. apply app_inv_head, app_inv_head in H27. subst. auto.
  }
  inversion H25. inversion H27. inversion H29. subst.
  (* FROM CALL HYPOS *)
 (* FROM CALL HYPO1 *)
  inversion H12. subst. simpl in H30. simpl in H31.
  pose (EC1 := element_exist _ _ _ H30). inversion EC1 as [v1']. inversion H26. subst. inversion H30.
  pose (EC2 := element_exist _ _ _ H32). inversion EC2 as [v2']. inversion H28. subst. inversion H30.
  apply eq_sym, length_zero_iff_nil in H35. subst.
  pose (EC3 := element_exist _ _ _ H31). inversion EC3 as [eff1']. inversion H34. subst. inversion H31.
  pose (EC4 := element_exist _ _ _ H36). inversion EC4 as [eff2']. inversion H35. subst. inversion H36.
  apply eq_sym, length_zero_iff_nil in H39. subst.
  (* FROM CALL HYPO2 *)
  inversion H23. subst. simpl in H40, H41.
  pose (EC1' := element_exist _ _ _ H40). inversion EC1' as [v2'']. inversion H38. subst. inversion H40.
  pose (EC2' := element_exist _ _ _ H42). inversion EC2' as [v1'']. inversion H39. subst. inversion H40.
  apply eq_sym, length_zero_iff_nil in H45. subst.
  pose (EC3' := element_exist _ _ _ H41). inversion EC3' as [eff2'']. inversion H44. subst. inversion H41.
  pose (EC4' := element_exist _ _ _ H46). inversion EC4' as [eff1'']. inversion H45. subst. inversion H41.
  apply eq_sym, length_zero_iff_nil in H49. subst.

  unfold concatn in H47, H37. simpl app in H47, H37.
  pose (PUM1 := plus_effect_unmodified _ _ _ H37).
  pose (PUM2 := plus_effect_unmodified _ _ _ H47).
  rewrite app_nil_r, app_nil_r, <- app_nil_r in PUM1, PUM2.
  apply app_inv_head in PUM1. apply app_inv_head in PUM2.
  apply app_eq_nil in PUM1. apply app_eq_nil in PUM2.
  inversion PUM1. inversion PUM2. subst.
  (* EVERYTHING IS EQUAL *)
  assert (v1' = v1 /\ v1'' = v1 /\ v2' = v2 /\ v2'' = v2).
  {
    pose (P1 := H33 0 Nat.lt_0_2).
    pose (P2 := H33 1 Nat.lt_1_2).
    pose (P1' := H43 1 Nat.lt_1_2).
    pose (P2' := H43 0 Nat.lt_0_2).
    unfold concatn in P1, P2, P1', P2'. simpl in P1, P2, P1', P2'.
    rewrite app_nil_r, app_nil_r in P1, P1', P2, P2'.
    inversion P1. inversion P2. inversion P1'. inversion P2'. subst.
    rewrite get_value_there in H52, H64.
    2-3 : congruence.
    rewrite get_value_here in H52, H56, H60, H64.
    inversion H52. inversion H56. inversion H60. inversion H64. subst. auto.
  }
  inversion H48. inversion H50. inversion H52. subst.
  rewrite app_nil_r, app_nil_r in H37, H47.
  
  apply (plus_comm_basic_value _ (eff ++ eff2 ++ eff1)) in H37.
  rewrite H37 in H47. inversion H47.
  reflexivity.
Qed.

Example let_1_comm_2_list_alt (env: Environment) (e1 e2 : Expression) (t v1 v2 : Value) 
   (eff eff1 eff2 : SideEffectList) (A B : Var) (VarHyp : A <> B)
(Hypo1 : |env, e1, eff| -e> |inl v1, eff ++ eff1|)
(Hypo2 : |env, e1, eff ++ eff2| -e> |inl v1, eff ++ eff2 ++ eff1|)
(Hypo1' : |env, e2, eff| -e> |inl v2, eff ++ eff2|)
(Hypo2' : |env, e2, eff ++ eff1| -e> |inl v2, eff ++ eff1 ++ eff2|) :
|env, ELet [A; B] [e1 ; e2]
     (ECall "plus"%string [EVar A ; EVar B]), eff| -e> |inl t, eff ++ eff1 ++ eff2|
->
|env, ELet [A; B] [e2 ; e1]
     (ECall "plus"%string [EVar A ; EVar B]), eff| -e> |inl t, eff ++ eff2 ++ eff1|.
Proof.
  intros.
  (* FROM LET HYPO *)
  inversion H. subst. simpl in H4. simpl in H3.
  pose (EE1 := element_exist Value 1 vals H3). inversion EE1 as [v1']. inversion H0. subst. inversion H3.
  pose (EE2 := element_exist Value 0 x H2). inversion EE2 as [v2']. inversion H1. subst. inversion H3.
  apply eq_sym, length_zero_iff_nil in H7. subst.
  pose (EE3 := element_exist _ _ _ H4). inversion EE3 as [eff1']. inversion H5. subst. inversion H4.
  pose (EE4 := element_exist _ _ _ H8). inversion EE4 as [eff2']. inversion H7. subst. inversion H8.
  apply eq_sym, length_zero_iff_nil in H12. subst.
  assert (v1' = v1 /\ v2' = v2 /\ eff1' = eff1 /\ eff2' = eff2).
  {
    pose (P1 := H6 0 Nat.lt_0_2).
    pose (P2 := H6 1 Nat.lt_1_2).
    simpl_concatn_H P1. simpl_concatn_H P2. rewrite <- app_assoc in P2.
    pose (D1 := determinism _ Hypo1 _ _ P1). inversion D1. inversion H9. apply app_inv_head in H12. subst.
    pose (D2 := determinism _ Hypo2' _ _ P2). inversion D2. inversion H12. apply app_inv_head, app_inv_head in H13. subst. auto.
  }
  inversion H9. inversion H13. inversion H15. subst.

  (* Deconstruct call *)

  inversion H11. subst.
  pose (EE1' := element_exist Value 1 vals H16). inversion EE1' as [v1']. inversion H12. subst. inversion H16.
  pose (EE2' := element_exist Value 0 x H18). inversion EE2' as [v2']. inversion H14. subst. inversion H18.
  apply eq_sym, length_zero_iff_nil in H21. subst.
  pose (EE3' := element_exist _ _ _ H17). inversion EE3' as [eff1']. inversion H20. subst. inversion H17.
  pose (EE4' := element_exist _ _ _ H22). inversion EE4' as [eff2']. inversion H21. subst. inversion H22.
  apply eq_sym, length_zero_iff_nil in H25. subst.
  assert (v1' = v1 /\ v2' = v2 /\ eff1' = [] /\ eff2' = []).
  {
    pose (P1 := H19 0 Nat.lt_0_2).
    pose (P2 := H19 1 Nat.lt_1_2).
    simpl_concatn_H P1. simpl_concatn_H P2. repeat (rewrite <- app_assoc in P2, P1).
    inversion P1.
    inversion P2. subst.
    rewrite <- app_nil_r in H29 at 1, H34 at 1.
    repeat (rewrite <- app_assoc in H29). repeat (rewrite <- app_assoc in H34).
    repeat (apply app_inv_head in H29). repeat (apply app_inv_head in H34). subst.
    rewrite get_value_here in H33. inversion H33.
    rewrite get_value_there in H28. rewrite get_value_here in H28. inversion H28.
    subst. auto.
    - congruence.
  }

  (* construct derivation tree *)
  apply eval_let with (vals := [v2; v1]) (eff := [eff2; eff1]) (eff2 := []); auto.
  * intros. inversion H25. 2: inversion H27.
    1-2: simpl_concatn; try(rewrite <- app_assoc); assumption.
    - inversion H29.
  * simpl_concatn. auto.
  * simpl_concatn. apply eval_call with (vals := [v2; v1]) (eff := [[];[]]); auto.
    - intros. inversion H25. 2: inversion H27.
      + simpl_concatn. replace (inl v1) with (get_value (insert_original_value (insert_original_value env (inl A) v2) (inl B) v1) (inl B)). apply eval_var.
        apply get_value_here.
      + simpl_concatn. replace (inl v2) with (get_value (insert_original_value (insert_original_value env (inl A) v2) (inl B) v1) (inl A)). apply eval_var.
        rewrite get_value_there. apply get_value_here. congruence.
      + inversion H29.
    - inversion H24. inversion H26. inversion H28. subst.
      unfold concatn in *. simpl concat. repeat (rewrite <- app_assoc).
      simpl concat in H23. repeat (rewrite <- app_assoc in H23). repeat (rewrite app_nil_r in *).
      apply (plus_comm_basic_value _ _ H23).
Qed.

Example let_1_comm_2_list_alt_eq (env: Environment) (e1 e2 : Expression) (t v1 v2 : Value) 
   (eff eff1 eff2 : SideEffectList) (A B : Var) (VarHyp : A <> B)
(Hypo1 : |env, e1, eff| -e> |inl v1, eff ++ eff1|)
(Hypo2 : |env, e1, eff ++ eff2| -e> |inl v1, eff ++ eff2 ++ eff1|)
(Hypo1' : |env, e2, eff| -e> |inl v2, eff ++ eff2|)
(Hypo2' : |env, e2, eff ++ eff1| -e> |inl v2, eff ++ eff1 ++ eff2|) :
|env, ELet [A; B] [e1 ; e2]
     (ECall "plus"%string [EVar A ; EVar B]), eff| -e> |inl t, eff ++ eff1 ++ eff2|
<->
|env, ELet [A; B] [e2 ; e1]
     (ECall "plus"%string [EVar A ; EVar B]), eff| -e> |inl t, eff ++ eff2 ++ eff1|.
Proof.
  split.
  * apply let_1_comm_2_list_alt with (v1 := v1) (v2 := v2); assumption.
  * apply let_1_comm_2_list_alt with (v1 := v2) (v2 := v1); assumption.
Qed.

Example let_1_binding_swap_2_list_alt (env: Environment) (e1 e2 : Expression) (t v1 v2 : Value) 
   (eff eff1 eff2 : SideEffectList) (A B : Var) (VarHyp : A <> B)
(Hypo1 : |env, e1, eff| -e> |inl v1, eff ++ eff1|)
(Hypo2 : |env, e1, eff ++ eff2| -e> |inl v1, eff ++ eff2 ++ eff1|)
(Hypo1' : |env, e2, eff| -e> |inl v2, eff ++ eff2|)
(Hypo2' : |env, e2, eff ++ eff1| -e> |inl v2, eff ++ eff1 ++ eff2|) :
|env, ELet [A; B] [e1; e2]
     (ECall "plus"%string [EVar A ; EVar B]), eff| -e> |inl t, eff ++ eff1 ++ eff2|
<->
|env, ELet [B; A] [e2; e1]
     (ECall "plus"%string [EVar B ; EVar A]), eff| -e> |inl t, eff ++ eff2 ++ eff1|.
Proof.
  split.
  * intro. inversion H. subst.
    pose (EE1 := element_exist Value 1 vals H3). inversion EE1 as [v1']. inversion H0. subst. inversion H3.
    pose (EE2 := element_exist Value 0 x H2). inversion EE2 as [v2']. inversion H1. subst. inversion H2.
    apply eq_sym, length_zero_iff_nil in H7. subst.
    pose (EE3 := element_exist _ _ _ H4). inversion EE3 as [eff1']. inversion H5. subst. inversion H4.
    pose (EE4 := element_exist _ _ _ H8). inversion EE4 as [eff2']. inversion H7. subst. inversion H8.
    apply eq_sym, length_zero_iff_nil in H12. subst.
    assert (v1' = v1 /\ v2' = v2 /\ eff1' = eff1 /\ eff2' = eff2).
    {
      pose (P1 := H6 0 Nat.lt_0_2).
      pose (P2 := H6 1 Nat.lt_1_2).
      simpl_concatn_H P1. simpl_concatn_H P2. rewrite <- app_assoc in P2.
      pose (D1 := determinism _ Hypo1 _ _ P1). inversion D1. inversion H9. apply app_inv_head in H12. subst.
      pose (D2 := determinism _ Hypo2' _ _ P2). inversion D2. inversion H12. apply app_inv_head, app_inv_head in H13. subst. auto.
    }
    inversion H9. inversion H13. inversion H15. subst.

    (* Deconstruct call *)

    inversion H11. subst.
    pose (EE1' := element_exist Value 1 vals H16). inversion EE1' as [v1']. inversion H12. subst. inversion H16.
    pose (EE2' := element_exist Value 0 x H18). inversion EE2' as [v2']. inversion H14. subst. inversion H18.
    apply eq_sym, length_zero_iff_nil in H21. subst.
    pose (EE3' := element_exist _ _ _ H17). inversion EE3' as [eff1']. inversion H20. subst. inversion H17.
    pose (EE4' := element_exist _ _ _ H22). inversion EE4' as [eff2']. inversion H21. subst. inversion H22.
    apply eq_sym, length_zero_iff_nil in H25. subst.
    assert (v1' = v1 /\ v2' = v2 /\ eff1' = [] /\ eff2' = []).
    {
      pose (P1 := H19 0 Nat.lt_0_2).
      pose (P2 := H19 1 Nat.lt_1_2).
      simpl_concatn_H P1. simpl_concatn_H P2. repeat (rewrite <- app_assoc in P2, P1).
      inversion P1.
      inversion P2. subst.
      rewrite <- app_nil_r in H29 at 1, H34 at 1.
      repeat (rewrite <- app_assoc in H29). repeat (rewrite <- app_assoc in H34).
      repeat (apply app_inv_head in H29). repeat (apply app_inv_head in H34). subst.
      rewrite get_value_here in H33. inversion H33.
      rewrite get_value_there in H28. rewrite get_value_here in H28. inversion H28.
      subst. auto.
      - congruence.
    }
    (* construct derivation tree *)
    apply eval_let with (vals := [v2; v1]) (eff := [eff2; eff1]) (eff2 := []); auto.
    - intros. inversion H25. 2: inversion H27.
      1-2: simpl_concatn; try(rewrite <- app_assoc); assumption.
      + inversion H29.
    - simpl_concatn. auto.
    - simpl_concatn. apply eval_call with (vals := [v2; v1]) (eff := [[];[]]); auto.
      + intros. inversion H25. 2: inversion H27.
        ** simpl_concatn. replace (inl v1) with (get_value (insert_original_value (insert_original_value env (inl B) v2) (inl A) v1) (inl A)). apply eval_var.
           apply get_value_here.
        ** simpl_concatn. replace (inl v2) with (get_value (insert_original_value (insert_original_value env (inl B) v2) (inl A) v1) (inl B)). apply eval_var.
           rewrite get_value_there. apply get_value_here. congruence.
        ** inversion H29.
      + inversion H24. inversion H26. inversion H28. subst.
        unfold concatn in *. simpl concat. repeat (rewrite <- app_assoc).
        simpl concat in H23. repeat (rewrite <- app_assoc in H23). repeat (rewrite app_nil_r in *).
        apply (plus_comm_basic_value _ _ H23).
  * intro. inversion H. subst.
    pose (EE1 := element_exist Value 1 vals H3). inversion EE1 as [v2']. inversion H0. subst. inversion H3.
    pose (EE2 := element_exist Value 0 x H2). inversion EE2 as [v1']. inversion H1. subst. inversion H2.
    apply eq_sym, length_zero_iff_nil in H7. subst.
    pose (EE3 := element_exist _ _ _ H4). inversion EE3 as [eff2']. inversion H5. subst. inversion H4.
    pose (EE4 := element_exist _ _ _ H8). inversion EE4 as [eff1']. inversion H7. subst. inversion H8.
    apply eq_sym, length_zero_iff_nil in H12. subst.
    assert (v1' = v1 /\ v2' = v2 /\ eff1' = eff1 /\ eff2' = eff2).
    {
      pose (P1 := H6 0 Nat.lt_0_2).
      pose (P2 := H6 1 Nat.lt_1_2).
      simpl_concatn_H P1. simpl_concatn_H P2. rewrite <- app_assoc in P2.
      pose (D1 := determinism _ Hypo1' _ _ P1). inversion D1. inversion H9. apply app_inv_head in H12. subst.
      pose (D2 := determinism _ Hypo2 _ _ P2). inversion D2. inversion H12. apply app_inv_head, app_inv_head in H13. subst. auto.
    }
    inversion H9. inversion H13. inversion H15. subst.

    (* Deconstruct call *)

    inversion H11. subst.
    pose (EE1' := element_exist Value 1 vals H16). inversion EE1' as [v2']. inversion H12. subst. inversion H16.
    pose (EE2' := element_exist Value 0 x H18). inversion EE2' as [v1']. inversion H14. subst. inversion H18.
    apply eq_sym, length_zero_iff_nil in H21. subst.
    pose (EE3' := element_exist _ _ _ H17). inversion EE3' as [eff2']. inversion H20. subst. inversion H17.
    pose (EE4' := element_exist _ _ _ H22). inversion EE4' as [eff1']. inversion H21. subst. inversion H22.
    apply eq_sym, length_zero_iff_nil in H25. subst.
    assert (v1' = v1 /\ v2' = v2 /\ eff1' = [] /\ eff2' = []).
    {
      pose (P1 := H19 0 Nat.lt_0_2).
      pose (P2 := H19 1 Nat.lt_1_2).
      simpl_concatn_H P1. simpl_concatn_H P2. repeat (rewrite <- app_assoc in P2, P1).
      inversion P1.
      inversion P2. subst.
      rewrite <- app_nil_r in H29 at 1, H34 at 1.
      repeat (rewrite <- app_assoc in H29). repeat (rewrite <- app_assoc in H34).
      repeat (apply app_inv_head in H29). repeat (apply app_inv_head in H34). subst.
      rewrite get_value_here in H33. inversion H33.
      rewrite get_value_there in H28. rewrite get_value_here in H28. inversion H28.
      subst. auto.
      - congruence.
    }
    (* construct derivation tree *)
    apply eval_let with (vals := [v1; v2]) (eff := [eff1; eff2]) (eff2 := []); auto.
    - intros. inversion H25. 2: inversion H27.
      1-2: simpl_concatn; try(rewrite <- app_assoc); assumption.
      + inversion H29.
    - simpl_concatn. auto.
    - simpl_concatn. apply eval_call with (vals := [v1; v2]) (eff := [[];[]]); auto.
      + intros. inversion H25. 2: inversion H27.
        ** simpl_concatn. replace (inl v2) with (get_value (insert_original_value (insert_original_value env (inl A) v1) (inl B) v2) (inl B)). apply eval_var.
           apply get_value_here.
        ** simpl_concatn. replace (inl v1) with (get_value (insert_original_value (insert_original_value env (inl A) v1) (inl B) v2) (inl A)). apply eval_var.
           rewrite get_value_there. apply get_value_here. congruence.
        ** inversion H29.
      + inversion H24. inversion H26. inversion H28. subst.
        unfold concatn in *. simpl concat. repeat (rewrite <- app_assoc).
        simpl concat in H23. repeat (rewrite <- app_assoc in H23). repeat (rewrite app_nil_r in *).
        apply (plus_comm_basic_value _ _ H23).
Qed.


(* Example let_2_apply (env: Environment)(e1 e2 exp : Expression) (v1 v2 : Value) (v0 t : Value + Exception) (eff eff1 eff2 eff3 : SideEffectList) (A B : Var) (VarHyp : A <> B) 
(E1 : | append_vars_to_env [A] [v1] (append_vars_to_env [B] [v2] env), exp, eff ++ eff2 ++ eff1 | -e> |v0, eff ++ eff2 ++ eff1 ++ eff3|)
(E2 : | append_vars_to_env [B] [v2] (append_vars_to_env [A] [v1] env), exp, eff ++ eff1 ++ eff2 | -e> |v0, eff ++ eff1 ++ eff2 ++ eff3|)
    :
  |env, e2, eff| -e> |inl v2, eff ++ eff2| -> 
  |append_vars_to_env [A] [v1] env, e2, eff ++ eff1| -e> |inl v2, eff ++ eff1 ++ eff2| ->
  |env, e1, eff| -e> |inl v1, eff ++ eff1| -> 
  |append_vars_to_env [B] [v2] env, e1, eff ++ eff2| -e> |inl v1, eff ++ eff2 ++ eff1| ->
  |env, ELet [A] [e1] (ELet [B] [e2] 
        (EApp exp [EVar A ; EVar B])), eff| -e> |t, eff ++ eff1 ++ eff2 ++ eff3|
->
|env, ELet [B] [e2] (ELet [A] [e1]
        (EApp exp [EVar A ; EVar B])), eff| -e> |t, eff ++ eff2 ++ eff1 ++ eff3|
.
Proof.
  * intros. 
   (** Deconstruct ELet-s *)
    inversion H3. subst. simpl in H8. pose (EE1 := element_exist Value 0 vals H7). inversion EE1 as [v1']. inversion H4. subst. inversion H7. apply eq_sym, length_zero_iff_nil in H6. subst.
    pose (EE2 := element_exist _ 0 _ H8). inversion EE2 as [eff1']. inversion H5. subst. inversion H8. apply eq_sym, length_zero_iff_nil in H9. subst.
    assert (v1' = v1 /\ eff1' = eff1).
    {
      pose (P := H10 0 Nat.lt_0_1). unfold concatn in P. simpl in P. rewrite app_nil_r, app_nil_r in P.
      pose (WD := determinism _ H1 _ _ P). inversion WD. inversion H6. apply app_inv_head in H9.
      subst. auto.
    }
    inversion H6. subst.
    inversion H15. subst. simpl in H13, H16.
    pose (EE3 := element_exist Value 0 vals H13). inversion EE3 as [v2']. inversion H9.
    subst. inversion H13. apply eq_sym, length_zero_iff_nil in H12. subst.
    pose (EE4 := element_exist _ _ _ H16). inversion EE4 as [eff2']. inversion H11. subst.
    inversion H16. apply eq_sym, length_zero_iff_nil in H17. subst.
    assert (v2' = v2 /\ eff2' = eff2). 
    {
      pose (P := H18 0 Nat.lt_0_1). unfold concatn in P. simpl in P.
      rewrite app_nil_r, app_nil_r, app_nil_r in P.
      pose (WD := determinism _ H0 _ _ P). inversion WD. inversion H12.
      rewrite app_assoc in H17. apply app_inv_head in H17. subst. auto.
    }
    inversion H12. subst.
  (** Start building derivation tree *)
    apply eval_let with (vals := [v2]) (eff := [eff2]) (eff2 := eff1 ++ eff3); auto.
   - intros. inversion H17.
     + unfold concatn. simpl. rewrite app_nil_r, app_nil_r. assumption.
     + inversion H20.
   - unfold concatn. simpl. rewrite app_nil_r, app_assoc. auto.
   - apply eval_let with (vals := [v1]) (eff := [eff1]) (eff2 := eff3); auto.
     + intros. inversion H17.
       ** subst. unfold concatn. simpl concat. simpl nth.
       rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc. assumption.
       ** inversion H20.
     + unfold concatn. simpl. rewrite app_nil_r, app_nil_r, <- app_assoc, <- app_assoc. auto.
     + inversion H23; subst.
       ** unfold concatn in H21. simpl concat in H21. rewrite app_nil_r, app_nil_r, <- app_assoc, <- app_assoc in H21. pose (WD3 := determinism _ E2 _ _ H21). inversion WD3.
          apply app_inv_head in H19. rewrite <- app_assoc in H19. apply app_inv_head in H19. apply app_inv_head in H19. subst.
          pose (EEA := element_exist _ _ _ H20). inversion EEA as [v1']. inversion H17. subst. inversion H20. 
          pose (EEA2 := element_exist _ _ _ H27). inversion EEA2 as [v2']. inversion H19. subst. inversion H27. apply eq_sym, length_zero_iff_nil in H30. subst.
          simpl in H25.
          pose (EEE := element_exist _ _ _ H25). inversion EEE as [eff1']. inversion H29. subst. inversion H25.
          pose (EEE2 := element_exist _ _ _ H31). inversion EEE2 as [eff2']. inversion H30. subst. inversion H31. apply eq_sym, length_zero_iff_nil in H34. subst.
          assert (v1' = v1 /\ v2' = v2 /\ eff1' = [] /\ eff2' = []).
          {
            pose (P := H26 0 Nat.lt_0_2). unfold concatn in P. simpl in P.
            rewrite app_nil_r, app_nil_r, app_nil_r, app_nil_r in P. repeat (rewrite <- app_assoc in P).
            inversion P. rewrite get_value_there in H37. rewrite get_value_here in H37. inversion H37.
            rewrite <- app_nil_r in H38 at 1. repeat (rewrite <- app_assoc in H38). repeat (apply app_inv_head in H38). subst.

            pose (P2 := H26 1 Nat.lt_1_2). unfold concatn in P2. simpl in P2.
            rewrite app_nil_r, app_nil_r, app_nil_r, app_nil_r in P2. repeat (rewrite <- app_assoc in P2).
            inversion P2. rewrite get_value_here in H38. inversion H38.
            rewrite <- app_nil_r in H39 at 1. repeat (rewrite <- app_assoc in H39). repeat (apply app_inv_head in H39). subst. auto.
            congruence.
          }
          inversion H33. inversion H35. inversion H37. subst.
          eapply eval_apply with (vals := [v1; v2]) (eff := [[]; []]); auto.
          -- unfold concatn. simpl concat. rewrite app_nil_r, app_nil_r, <- app_assoc, <- app_assoc, <- app_assoc. exact E1.
          -- auto.
          -- intros. inversion H34. 2: inversion H38.
            ++ simpl_concatn. replace (inl v2) with (get_value (insert_value (insert_value env (inl B) v2) (inl A) v1) (inl B)). apply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
            ++ simpl_concatn. replace (inl v1) with (get_value (insert_value (insert_value env (inl B) v2) (inl A) v1) (inl A)). apply eval_var. rewrite get_value_here. auto.
            ++ inversion H40.
          -- unfold concatn. simpl. repeat (rewrite <- app_assoc, app_nil_r). reflexivity.
          -- unfold concatn in H32. simpl in H32. 
Abort. *)

Example let_2_apply_effect_free (env: Environment)(e1 e2 exp : Expression) (v1 v2 : Value) (v0 t : Value + Exception) (A B : Var) (VarHyp : A <> B) 
(E1 : | append_vars_to_env [A] [v1] (append_vars_to_env [B] [v2] env), exp, [] | -e> |v0, []|)
(E2 : | append_vars_to_env [B] [v2] (append_vars_to_env [A] [v1] env), exp, [] | -e> |v0, []|)
    :
  |env, e2, []| -e> |inl v2, []| -> 
  |append_vars_to_env [A] [v1] env, e2, []| -e> |inl v2, []| ->
  |env, e1, []| -e> |inl v1, []| -> 
  |append_vars_to_env [B] [v2] env, e1, []| -e> |inl v1, []| ->
  |env, ELet [A] [e1] (ELet [B] [e2] 
        (EApp exp [EVar A ; EVar B])), []| -e> |t, []|
<->
|env, ELet [B] [e2] (ELet [A] [e1]
        (EApp exp [EVar A ; EVar B])), []| -e> |t, []|
.
Proof.
  split;intros. 
   (** Deconstruct ELet-s *)
  * inversion H3. subst. simpl in H8. pose (EE1 := element_exist Value 0 vals H7). inversion EE1 as [v1']. inversion H4. subst. inversion H7. apply eq_sym, length_zero_iff_nil in H6. subst.
  pose (EE2 := element_exist _ 0 _ H8). inversion EE2 as [eff1']. inversion H5. subst. inversion H8. apply eq_sym, length_zero_iff_nil in H9. subst.
  assert (v1' = v1 /\ eff1' = []).
  {
    pose (P := H10 0 Nat.lt_0_1). unfold concatn in P. simpl in P. rewrite app_nil_r in P.
    pose (WD := determinism _ H1 _ _ P). inversion WD. inversion H6.
    subst. auto.
  }
  inversion H6. subst.
  inversion H15. subst. simpl in H13, H16.
  pose (EE3 := element_exist Value 0 vals H13). inversion EE3 as [v2']. inversion H9.
  subst. inversion H13. apply eq_sym, length_zero_iff_nil in H12. subst.
  pose (EE4 := element_exist _ _ _ H16). inversion EE4 as [eff2']. inversion H11. subst.
  inversion H16. apply eq_sym, length_zero_iff_nil in H17. subst.
  assert (v2' = v2 /\ eff2' = []). 
  {
    pose (P := H18 0 Nat.lt_0_1). unfold concatn in P. simpl in P.
    rewrite app_nil_r in P.
    pose (WD := determinism _ H0 _ _ P). inversion WD. inversion H12. subst. auto.
  }
  inversion H12. subst.
  apply eval_let with (vals := [v2]) (eff := [[]]) (eff2 := []); auto.
   - intros. inversion H17.
     + unfold concatn. simpl. assumption.
     + inversion H20.
   - apply eval_let with (vals := [v1]) (eff := [[]]) (eff2 := []); auto.
     + intros. inversion H17.
       ** subst. unfold concatn. simpl concat. simpl nth. assumption.
       ** inversion H20.
   (** Destruct application hypothesis *)
     + inversion H23; subst.
       ** unfold concatn in H21. simpl in H21. pose (WD3 := determinism _ E2 _ _ H21). inversion WD3. subst.
          pose (EEA := element_exist _ _ _ H20). inversion EEA as [v1']. inversion H17. subst. inversion H20. 
          pose (EEA2 := element_exist _ _ _ H27). inversion EEA2 as [v2']. inversion H19. subst. inversion H27. apply eq_sym, length_zero_iff_nil in H30. subst.
          simpl in H25.
          pose (EEE := element_exist _ _ _ H25). inversion EEE as [eff1']. inversion H29. subst. inversion H25.
          pose (EEE2 := element_exist _ _ _ H31). inversion EEE2 as [eff2']. inversion H30. subst. inversion H31. apply eq_sym, length_zero_iff_nil in H34. subst.
          assert (v1' = v1 /\ v2' = v2 /\ eff1' = [] /\ eff2' = []).
          {
            pose (P := H26 0 Nat.lt_0_2). unfold concatn in P. simpl in P.
            inversion P. rewrite get_value_there in H37. rewrite get_value_here in H37. inversion H37.
            rewrite app_nil_r in H38. subst.

            pose (P2 := H26 1 Nat.lt_1_2). unfold concatn in P2. simpl in P2.
            inversion P2. rewrite get_value_here in H38. inversion H38.
            rewrite app_nil_r in H39. subst. auto.
            congruence.
          }
          inversion H33. inversion H35. inversion H37. subst.
          eapply eval_apply with (vals := [v1; v2]) (eff := [[]; []]); auto.
          -- unfold concatn. simpl concat. exact E1.
          -- auto.
          -- intros. inversion H34. 2: inversion H38.
            ++ simpl_concatn. replace (inl v2) with (get_value (insert_original_value (insert_original_value env (inl B) v2) (inl A) v1) (inl B)). apply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
            ++ simpl_concatn. replace (inl v1) with (get_value (insert_original_value (insert_original_value env (inl B) v2) (inl A) v1) (inl A)). apply eval_var. rewrite get_value_here. auto.
            ++ inversion H40.
          -- unfold concatn. simpl. repeat (rewrite <- app_assoc, app_nil_r). reflexivity.
          -- simpl_concatn_H H32. simpl_concatn. exact H32.
       ** eapply eval_apply_ex_closure_ex; try(reflexivity).
          pose (WD := determinism _ E2 _ _ H27). inversion WD. subst. assumption.
       ** inversion H21.
          -- pose (EEA := element_exist _ _ _  (eq_sym H19)). inversion EEA as [v1']. inversion H17. subst. inversion H19. apply length_zero_iff_nil in H27. subst. simpl in H32. inversion H32.
             rewrite get_value_here in H31. congruence.
          -- inversion H19.
            ++ rewrite H27 in *. simpl in H32. inversion H32.
             rewrite get_value_there, get_value_here in H33; congruence.
            ++ inversion H27.
       ** simpl_concatn_H H24. pose (WD := determinism _ E2 _ _ H24). inversion WD. subst. eapply eval_apply_ex_closure with (vals := [v1; v2]) (eff := [[];[]]); auto.
         -- simpl_concatn. simpl in E1. exact E1.
         -- intros. inversion H17. 2: inversion H26.
            ++ simpl_concatn. replace (inl v2) with (get_value (insert_original_value (insert_original_value env (inl B) v2) (inl A) v1) (inl B)). apply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
            ++ simpl_concatn. replace (inl v1) with (get_value (insert_original_value (insert_original_value env (inl B) v2) (inl A) v1) (inl A)). apply eval_var. rewrite get_value_here. auto.
            ++ inversion H29.
         -- reflexivity.
       ** simpl_concatn_H H24. pose (WD := determinism _ E2 _ _ H24). inversion WD. subst.
          eapply eval_apply_ex_param_count with (vals := [v1; v2]) (eff := [[];[]]); auto.
         -- simpl_concatn. simpl in E1. exact E1.
         -- intros. inversion H17. 2: inversion H26.
            ++ simpl_concatn. replace (inl v2) with (get_value (insert_original_value (insert_original_value env (inl B) v2) (inl A) v1) (inl B)). apply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
            ++ simpl_concatn. replace (inl v1) with (get_value (insert_original_value (insert_original_value env (inl B) v2) (inl A) v1) (inl A)). apply eval_var. rewrite get_value_here. auto.
            ++ inversion H29.
         -- rewrite <- H20 in H27. auto.
         -- reflexivity.
    - inversion H16. simpl_concatn_H H24. subst. rewrite H26 in H24. pose (WD := determinism _ H0 _ _ H24). inversion WD. inversion H9. 
      inversion H26.
    - inversion H8. subst. simpl in H16. rewrite H18 in H16. pose (WD := determinism _ H1 _ _ H16). inversion WD. inversion H4.
      inversion H18.
  * inversion H3. subst. simpl in H8. pose (EE1 := element_exist Value 0 vals H7). inversion EE1 as [v2']. inversion H4. subst. inversion H7. apply eq_sym, length_zero_iff_nil in H6. subst.
  pose (EE2 := element_exist _ 0 _ H8). inversion EE2 as [eff2']. inversion H5. subst. inversion H8. apply eq_sym, length_zero_iff_nil in H9. subst.
  assert (v2' = v2 /\ eff2' = []).
  {
    pose (P := H10 0 Nat.lt_0_1). unfold concatn in P. simpl in P. rewrite app_nil_r in P.
    pose (WD := determinism _ H _ _ P). inversion WD. inversion H6.
    subst. auto.
  }
  inversion H6. subst.
  inversion H15. subst. simpl in H13, H16.
  pose (EE3 := element_exist Value 0 vals H13). inversion EE3 as [v1']. inversion H9.
  subst. inversion H13. apply eq_sym, length_zero_iff_nil in H12. subst.
  pose (EE4 := element_exist _ _ _ H16). inversion EE4 as [eff1']. inversion H11. subst.
  inversion H16. apply eq_sym, length_zero_iff_nil in H17. subst.
  assert (v1' = v1 /\ eff1' = []). 
  {
    pose (P := H18 0 Nat.lt_0_1). unfold concatn in P. simpl in P.
    rewrite app_nil_r in P.
    pose (WD := determinism _ H2 _ _ P). inversion WD. inversion H12. subst. auto.
  }
  inversion H12. subst.
  apply eval_let with (vals := [v1]) (eff := [[]]) (eff2 := []); auto.
   - intros. inversion H17.
     + unfold concatn. simpl. assumption.
     + inversion H20.
   - apply eval_let with (vals := [v2]) (eff := [[]]) (eff2 := []); auto.
     + intros. inversion H17.
       ** subst. unfold concatn. simpl concat. simpl nth. assumption.
       ** inversion H20.
   (** Destruct application hypothesis *)
     + inversion H23; subst.
       ** unfold concatn in H21. simpl in H21. pose (WD3 := determinism _ E1 _ _ H21). inversion WD3. subst.
          pose (EEA := element_exist _ _ _ H20). inversion EEA as [v1']. inversion H17. subst. inversion H20. 
          pose (EEA2 := element_exist _ _ _ H27). inversion EEA2 as [v2']. inversion H19. subst. inversion H27. apply eq_sym, length_zero_iff_nil in H30. subst.
          simpl in H25.
          pose (EEE := element_exist _ _ _ H25). inversion EEE as [eff1']. inversion H29. subst. inversion H25.
          pose (EEE2 := element_exist _ _ _ H31). inversion EEE2 as [eff2']. inversion H30. subst. inversion H31. apply eq_sym, length_zero_iff_nil in H34. subst.
          assert (v1' = v1 /\ v2' = v2 /\ eff1' = [] /\ eff2' = []).
          {
            pose (P := H26 0 Nat.lt_0_2). unfold concatn in P. simpl in P.
            inversion P. rewrite get_value_here in H37. inversion H37.
            rewrite app_nil_r in H38. subst.

            pose (P2 := H26 1 Nat.lt_1_2). unfold concatn in P2. simpl in P2.
            inversion P2. rewrite get_value_there in H38. rewrite get_value_here in H38. inversion H38.
            rewrite app_nil_r in H39. subst. auto.
            congruence.
          }
          inversion H33. inversion H35. inversion H37. subst.
          eapply eval_apply with (vals := [v1; v2]) (eff := [[]; []]); auto.
          -- unfold concatn. simpl concat. exact E2.
          -- auto.
          -- intros. inversion H34. 2: inversion H38.
            ++ simpl_concatn. replace (inl v2) with (get_value (insert_original_value (insert_original_value env (inl A) v1) (inl B) v2) (inl B)). apply eval_var. rewrite get_value_here. auto.
            ++ simpl_concatn. replace (inl v1) with (get_value (insert_original_value (insert_original_value env (inl A) v1) (inl B) v2) (inl A)). apply eval_var. rewrite get_value_there. rewrite get_value_here. auto. congruence.
            ++ inversion H40.
          -- unfold concatn. simpl. repeat (rewrite <- app_assoc, app_nil_r). reflexivity.
          -- simpl_concatn_H H32. simpl_concatn. exact H32.
       ** eapply eval_apply_ex_closure_ex; try(reflexivity).
          pose (WD := determinism _ E1 _ _ H27). inversion WD. subst. assumption.
       ** inversion H21.
          -- pose (EEA := element_exist _ _ _  (eq_sym H19)). inversion EEA as [v1']. inversion H17. subst. inversion H19. apply length_zero_iff_nil in H27. subst. simpl in H32. inversion H32.
             rewrite get_value_there, get_value_here in H31; congruence.
          -- inversion H19.
            ++ rewrite H27 in *. simpl in H32. inversion H32.
             rewrite get_value_here in H33. congruence.
            ++ inversion H27.
       ** simpl_concatn_H H24. pose (WD := determinism _ E1 _ _ H24). inversion WD. subst. eapply eval_apply_ex_closure with (vals := [v1; v2]) (eff := [[];[]]); auto.
         -- simpl_concatn. simpl in E1. exact E2.
         -- intros. inversion H17. 2: inversion H26.
            ++ simpl_concatn. replace (inl v2) with (get_value (insert_original_value (insert_original_value env (inl A) v1) (inl B) v2) (inl B)). apply eval_var. rewrite get_value_here. auto.
            ++ simpl_concatn. replace (inl v1) with (get_value (insert_original_value (insert_original_value env (inl A) v1) (inl B) v2) (inl A)). apply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
            ++ inversion H29.
         -- reflexivity.
       ** simpl_concatn_H H24. pose (WD := determinism _ E1 _ _ H24). inversion WD. subst.
          eapply eval_apply_ex_param_count with (vals := [v1; v2]) (eff := [[];[]]); auto.
         -- simpl_concatn. simpl in E1. exact E2.
         -- intros. inversion H17. 2: inversion H26.
            ++ simpl_concatn. replace (inl v2) with (get_value (insert_original_value (insert_original_value env (inl A) v1) (inl B) v2) (inl B)). apply eval_var. rewrite get_value_here. auto.
            ++ simpl_concatn. replace (inl v1) with (get_value (insert_original_value (insert_original_value env (inl A) v1) (inl B) v2) (inl A)). apply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
            ++ inversion H29.
         -- rewrite <- H20 in H27. auto.
         -- reflexivity.
    - inversion H16. simpl_concatn_H H24. subst. rewrite H26 in H24. pose (WD := determinism _ H2 _ _ H24). inversion WD. inversion H9. 
      inversion H26.
    - inversion H8. subst. simpl in H16. rewrite H18 in H16. pose (WD := determinism _ H _ _ H16). inversion WD. inversion H4.
      inversion H18.
Qed.

End Core_Erlang_Equivalence_Proofs.