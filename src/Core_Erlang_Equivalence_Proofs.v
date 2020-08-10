Require Core_Erlang_Proofs.

Module Equivalence_Proofs.

Export Core_Erlang_Proofs.Proofs.

Import Core_Erlang_Tactics.Tactics.
Import ListNotations.
(* Import Coq.Init.Logic. *)

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
  |env, id, e, []| -e> |id, inl x1, []| ->
  |env, id, e', []| -e> | id, inl x2, []| ->
  |env, id, ECall "+"%string [e ; e'], []| -e> | id, inl t, []| ->
  |env, id, ECall "+"%string [e' ; e], []| -e> | id, inl t, []|.
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
  apply WD1 in P1; inversion P1; simpl in H9.
  destruct H11.
  rewrite H12 in *.
  inversion H9. subst. rewrite <- H11 in P2. subst.
  apply WD2 in P2. inversion P2. destruct H14.
  inversion H13. rewrite <- H12 in *. subst.
  eapply eval_call with (vals := [x3; x]) (eff := [[];[]]) (ids := [id; id]); auto.
  * intros. inversion H17.
    - assumption.
    - inversion H19.
      + simpl. assumption.
      + inversion H21.
  * rewrite (@plus_comm_basic x x3 t). 
      - reflexivity.
      - simpl last.
        pose (EE3 := element_exist _ _ H5).
        inversion EE3. inversion H17.
        subst. inversion H5.
        pose (EE4 := element_exist _ _ H19).
        inversion EE4. inversion H18.
        subst. inversion H5. apply eq_sym, length_zero_iff_nil in H21. subst.
        simpl in H11, H14. subst.
        exact H10.
Qed.


Example let_1_comm (e1 e2 : Expression) (t x1 x2 : Value) (id : nat) :
  |[], id, e1, []| -e> |id, inl x1, []| ->
  | [(inl "X"%string, x1)], id, e2, []| -e> |id, inl x2, []| ->
  |[], id, ELet [("X"%string, e1)] (ECall "+"%string [EVar "X"%string ; e2]), []| 
  -e> | id, inl t, []| ->
  |[], id, ELet [("X"%string, e1)] (ECall "+"%string [e2 ; EVar "X"%string]), []| 
  -e> |id, inl t, []|.
Proof.
  * intros. inversion H1. subst.
    pose (EE1 := element_exist 0 vals H4).
    inversion EE1. inversion H2. subst.
    inversion H4. apply eq_sym, length_zero_iff_nil in H7. subst.
    pose (EE2 := element_exist 0 _ H5). inversion EE2. inversion H3. subst.
    inversion H5. apply eq_sym, length_zero_iff_nil in H8. subst.
    pose (EE3 := element_exist 0 _ H6). inversion EE3. inversion H7. subst.
    inversion H6. apply eq_sym, length_zero_iff_nil in H10. subst.
    eapply eval_let with (vals := [x]) (eff := [[]]) (eff2 := []) (ids := [id]); auto.
    - intros. inversion H8. 2: inversion H11.
      simpl. pose (P1 := H9 0 Nat.lt_0_1). simpl in P1.
      pose (WD1 := determinism H). apply WD1 in P1 as P2. destruct P2.
      inversion H10.
      destruct H12.
      subst. exact P1.
    - apply call_comm with (x1 := x) (x2 := x2).
      + apply eval_var. reflexivity.
      + pose (P1 := H9 0 Nat.lt_0_1). simpl in P1.
        pose (WD1 := determinism H). apply WD1 in P1 as P2. destruct P2. destruct H10.
        inversion H8.
        subst. exact H0.
      + pose (P1 := H9 0 Nat.lt_0_1). simpl in P1.
        pose (WD1 := determinism H). apply WD1 in P1 as P2. destruct P2.
        inversion H8. destruct H10. subst. exact H14.
Qed.

Example call_comm_ex : forall (e e' : Expression) (x1 x2 : Value) (env : Environment)
       (t t' : Value) (id : nat),
  |env, id, e, []| -e> |id, inl x1, []| ->
  |env, id, e', []| -e> |id, inl x2, []| ->
  |env, id, ECall "+"%string [e ; e'], []| -e> |id, inl t, []| ->
  |env, id, ECall "+"%string [e' ; e], []| -e> |id, inl t', []| ->
  t = t'.
Proof.
  intros. pose (P := call_comm e e' x1 x2 t env _ H H0 H1). 
  pose (DET := determinism P _ _ _ H2). inversion DET. inversion H3. reflexivity.
Qed.

Example let_2_comm_concrete_alternate_proof (t : Value + Exception) :
  |[], 0,  ELet [("X"%string, ELit (Integer 5))] (ELet [("Y"%string, ELit (Integer 6))]
           (ECall "+"%string [EVar "X"%string ; EVar "Y"%string])), []| -e> |0, t, []|
<->
|[], 0, ELet [("X"%string, ELit (Integer 6))] (ELet [("Y"%string, ELit (Integer 5))]
           (ECall "+"%string [EVar "X"%string ; EVar "Y"%string])), []| -e> |0, t, []|
.
Proof.
  split; intros.
  * (* let values *)
    assert (|[], 0, ELet [("X"%string, ELit (Integer 5))]
      (ELet [("Y"%string, ELit (Integer 6))] (ECall "+" [EVar "X"%string; EVar "Y"%string])), []|
      -e> |0, inl (VLit (Integer 11)), []|).
    {
      solve.
    }
    apply @determinism with (v1 := inl (VLit (Integer 11))) (eff' := []) (id' := 0) in H.
    inversion H. inversion H1. subst.
    {
      solve.
    } assumption.
    
    
    (* Other way, basically the same*)
    * (* let values *)
    assert (|[], 0, ELet [("X"%string, ELit (Integer 6))]
      (ELet [("Y"%string, ELit (Integer 5))] (ECall "+" [EVar "X"%string; EVar "Y"%string])), []|
      -e>  |0, inl (VLit (Integer 11)), []|).
    {
      solve.
    }
    apply @determinism with (v1 := inl (VLit (Integer 11))) (eff' := []) (id' := 0) in H.
    inversion H. inversion H1. subst.
    {
      solve.
    } assumption.
Qed.

Example let_1_comm_2_list (env: Environment) (e1 e2 : Expression) (t t' v1 v2 : Value) 
   (eff eff1 eff2 : SideEffectList) (A B : Var) (VarHyp : A <> B) (id id1 id2 : nat)
(Hypo1 : |env, id, e1, eff| -e> | id + id1, inl v1, eff ++ eff1|)
(Hypo2 : |env, id + id2, e1, eff ++ eff2| -e> | id + id1 + id2, inl v1, eff ++ eff2 ++ eff1|)
(Hypo1' : |env, id, e2, eff| -e> | id + id2, inl v2, eff ++ eff2|)
(Hypo2' : |env, id + id1, e2, eff ++ eff1| -e> | id + id2 + id1, inl v2, eff ++ eff1 ++ eff2|) :
|env, id, ELet [(A, e1); (B, e2)]
     (ECall "+"%string [EVar A ; EVar B]), eff| -e> |id + id1 + id2, inl t, eff ++ eff1 ++ eff2|
->
|env, id, ELet [(A, e2); (B, e1)]
     (ECall "+"%string [EVar A ; EVar B]), eff| -e> |id + id2 + id1, inl t', eff ++ eff2 ++ eff1|
->
t = t'.
Proof.
  intros.
  (* FROM LET HYPO1 *)
  inversion H. subst. simpl in H4, H5, H3.
  pose (EE1 := element_exist 1 vals H3).
  inversion EE1 as [v1']. inversion H1. subst. inversion H3.
  pose (EE2 := element_exist 0 x H6).
  inversion EE2 as [v2']. inversion H2. subst. inversion H3. 
  apply eq_sym, length_zero_iff_nil in H9. subst.
  pose (EE3 := element_exist _ _ H4). inversion EE3 as [eff1']. inversion H7. subst. inversion H4.
  pose (EE4 := element_exist _ _ H10). inversion EE4 as [eff2']. inversion H9. subst. inversion H4.
  apply eq_sym, length_zero_iff_nil in H12. subst.
  pose (EE5 := element_exist _ _ H5). inversion EE5 as [id1']. inversion H11. subst. inversion H5.
  pose (EE6 := element_exist _ _ H14). inversion EE6 as [id2']. inversion H12. subst. inversion H5.
  apply eq_sym, length_zero_iff_nil in H16. subst.
  (* FROM LET HYPO2 *)
  inversion H0. subst. simpl in H19, H17, H18.
  pose (EE1' := element_exist _ _ H17). inversion EE1' as [v2'']. inversion H15. subst. inversion H17.
  pose (EE2' := element_exist _ _ H20). inversion EE2' as [v1'']. inversion H16. subst. inversion H17.
  apply eq_sym, length_zero_iff_nil in H23. subst.
  pose (EE3' := element_exist _ _ H18). inversion EE3' as [eff2'']. inversion H21. subst. inversion H18.
  pose (EE4' := element_exist _ _ H24). inversion EE4' as [eff1'']. inversion H23. subst. inversion H18.
  apply eq_sym, length_zero_iff_nil in H26. subst.

  pose (EE5' := element_exist _ _ H19). inversion EE5' as [id2'']. inversion H25. subst. inversion H19.
  pose (EE6' := element_exist _ _ H28). inversion EE6' as [id1'']. inversion H26. subst. inversion H19.
  apply eq_sym, length_zero_iff_nil in H30. subst.

  (* assert (v1' = v1 /\ eff1' = eff1).
  { *)
    pose (P1 := H8 0 Nat.lt_0_2).
    simpl in P1.
    pose (WD1 := determinism Hypo1).
    pose (PC1 := WD1 _ _ _ P1).
    destruct PC1. destruct H30. inversion H29. subst.
  (* } *)
  
  (* assert (v2'' = v2 /\ eff2'' = eff2).
  { *)
    pose (P2 := H22 0 Nat.lt_0_2).
    simpl in P2.
    pose (WD2 := determinism Hypo1').
    pose (PC2 := WD2 _ _ _ P2).
    destruct PC2. destruct H31. inversion H30. subst.
  (* } *)

  (* assert (v1'' = v1 /\ v2' = v2 /\ eff1'' = eff1 /\ eff2' = eff2).
  { *)
    pose (P3 := H22 1 Nat.lt_1_2).
    simpl in P3.
    pose (WD3 := determinism Hypo2).
    pose (PC3 := WD3 _ _ _ P3).
    inversion PC3. inversion H31. destruct H32. subst.
    pose (P4 := H8 1 Nat.lt_1_2).
    simpl in P4.
    pose (WD4 := determinism Hypo2').
    pose (PC4 := WD4 _ _ _ P4).
    inversion PC4. inversion H33. inversion H32. subst.
    clear EE1. clear EE2. clear EE3. clear EE4. clear EE5. clear EE6.
  (* } *)

  (* FROM CALL HYPOS *)
 (* FROM CALL HYPO1 *)
  inversion H13. subst. simpl in H36, H37, H38.
  pose (EC1 := element_exist _ _ H36). inversion EC1 as [v10]. inversion H34. subst. 
  inversion H36.
  pose (EC2 := element_exist _ _ H40). inversion EC2 as [v20]. inversion H35. subst. 
  inversion H36.
  apply eq_sym, length_zero_iff_nil in H43. subst.
  pose (EC3 := element_exist _ _ H37). inversion EC3 as [eff10]. inversion H41. subst.
  inversion H37.
  pose (EC4 := element_exist _ _ H44). inversion EC4 as [eff20]. inversion H43. subst.
  inversion H37.
  apply eq_sym, length_zero_iff_nil in H46. subst.
  pose (EC5 := element_exist _ _ H38). inversion EC5 as [id10]. inversion H45. subst.
  inversion H38.
  pose (EC6 := element_exist _ _ H48). inversion EC6 as [id20]. inversion H46. subst.
  inversion H38.
  apply eq_sym, length_zero_iff_nil in H50. subst.
  (* FROM CALL HYPO2 *)
  inversion H27. subst. simpl in H51, H52, H53.
  pose (EC1' := element_exist _ _ H51). inversion EC1' as [v20']. inversion H49. subst.
  inversion H51.
  pose (EC2' := element_exist _ _ H55). inversion EC2' as [v10']. inversion H50. subst.
  inversion H51.
  apply eq_sym, length_zero_iff_nil in H58. subst.
  pose (EC3' := element_exist _ _ H52). inversion EC3' as [eff20']. inversion H56. subst.
  inversion H52.
  pose (EC4' := element_exist _ _ H59). inversion EC4' as [eff10']. inversion H58. subst.
  inversion H52.
  apply eq_sym, length_zero_iff_nil in H61. subst.
  pose (EC5' := element_exist _ _ H53). inversion EC5' as [id20']. inversion H60. subst.
  inversion H53.
  pose (EC6' := element_exist _ _ H63). inversion EC6' as [id10']. inversion H61. subst.
  inversion H53.
  apply eq_sym, length_zero_iff_nil in H65. subst.

  pose (PUM1 := plus_effect_unmodified _ _ _ H42).
  pose (PUM2 := plus_effect_unmodified _ _ _ H57).
  inversion PUM1. inversion PUM2. simpl in H64, H65. subst.
  (* EVERYTHING IS EQUAL *)
  (* assert (v1' = v1 /\ v1'' = v1 /\ v2' = v2 /\ v2'' = v2).
  { *)
    clear P1. clear P2.
    pose (P1 := H39 0 Nat.lt_0_2).
    pose (P2 := H39 1 Nat.lt_1_2).
    pose (P1' := H54 1 Nat.lt_1_2).
    pose (P2' := H54 0 Nat.lt_0_2).
    simpl in P1, P2, P1', P2'.
    inversion P1. inversion P2. inversion P1'. inversion P2'. subst.
    rewrite get_value_there in H67, H91.
    2-3 : congruence.
    rewrite get_value_here in H67, H75, H83, H91.
    inversion H67. inversion H75. inversion H83. inversion H91. subst.
(* } *)
  clear PUM1. clear PUM2.
  apply (plus_comm_basic_value _ (eff ++ eff2 ++ eff1)) in H42.
  simpl last in H57.
  rewrite H42 in H57. inversion H57.
  reflexivity.
Qed.

Example exp_to_fun (e : Expression) (x : Var) (id id' : nat):
  strong_equivalent e (ELet [(x, EFun [] e)] (EApp (EVar x) [])) (S id) id' id id'.
Proof.
  unfold strong_equivalent.
  split; intros.
  * apply eval_let with (vals := [VClos env [] id [] e]) (eff := [eff]) (eff2 := eff') (ids := [S id]); auto.
    - intros. inversion H0; inversion H2. simpl. apply eval_fun.
    - simpl. eapply eval_app with (vals := []) (var_list := []) (body := e) (ref := env)
                                    (ext := []) (eff := []) (eff2 := eff) (eff3 := eff') (ids := []); auto.
      + assert (get_value (insert_value env (inl x) (VClos env [] id [] e)) (inl x) 
                = inl (VClos env [] id [] e)). { apply get_value_here. }
        rewrite <- H0. apply eval_var. reflexivity.
      + intros. inversion H0.
      + simpl. unfold get_env. simpl. assumption.
  * inversion H.
    - pose (EE1 := element_exist 0 vals H2). inversion EE1. inversion H13. subst.
      inversion H2. apply eq_sym, length_zero_iff_nil in H1.
      pose (EE2 := element_exist _ _ H3). inversion EE2. inversion H0. subst. inversion H3.
      apply eq_sym, length_zero_iff_nil in H5.
      pose (EE3 := element_exist _ _ H4). inversion EE3. inversion H1. subst. inversion H4.
      apply eq_sym, length_zero_iff_nil in H6. subst.
      (* assert (x2 = []).
      { *)
        pose (P := H7 0 Nat.lt_0_1). simpl in P. inversion P.
        subst.
      (* } *)
      (* assert (x0 = VClos env [] (count_closures env) [] e).
      { *)
        (* assert (In (EFun [] e, x0) (combine [EFun [] e] [x0])). { simpl. auto. } 
        pose (P1 := H6 0 Nat.lt_0_1). simpl in P1. inversion P1. reflexivity.  *)
      (* } *)
      subst. inversion H12.
      + subst.
        apply eq_sym, length_zero_iff_nil in H11. subst.
        apply eq_sym, length_zero_iff_nil in H14. subst.
        apply eq_sym, length_zero_iff_nil in H8. subst.
        simpl in H9.
        simpl in H22.
        subst.
        inversion H9.
        (* inversion H7. *) rewrite get_value_here in H11. inversion H11. subst.
        unfold get_env in H22. simpl in H22. assumption.
      + subst. inversion H16. simpl in H9. rewrite get_value_here in H9. congruence.
      + subst. inversion H8.
      + subst. inversion H11. simpl in H17. rewrite get_value_here in H17. inversion H17. subst.
        pose (P1 := H15 env [] [] e). congruence.
      + subst. inversion H11. simpl in H17. rewrite get_value_here in H17. inversion H17. subst.
        rewrite <- H8 in H15. contradiction.
    - simpl in H2. inversion H2.
      + subst. rewrite H15 in H13. inversion H13.
      + inversion H15.
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
  |env, id0, e2, eff| -e> |id0 + id2, inl x0, eff ++ eff2|
 -> 
  |append_vars_to_env [A] [x] env, id0 + id1, e2, eff ++ eff1|
  -e> | id0 + id1 + id2, inl x0, eff ++ eff1 ++ eff2|
 ->
  |env, id0, e1, eff| -e> |id0 + id1, inl x, eff ++ eff1|
 -> 
  |append_vars_to_env [A] [x0] env, id0 + id2, e1, eff ++ eff2|
  -e> |id0 + id2 + id1, inl x, eff ++ eff2 ++ eff1| 
 ->
  |env, id0, ELet [(A, e1)] (ELet [(B, e2)] 
        (ECall "+"%string [EVar A ; EVar B])), eff| -e>
  | id0 + id1 + id2, inl t, eff ++ eff1 ++ eff2|
->
  |env, id0, ELet [(A, e2)] (ELet [(B, e1)]
        (ECall "+"%string [EVar A ; EVar B])), eff| -e>
  | id0 + id2 + id1, inl t, eff ++ eff2 ++ eff1|
.
Proof.
  * intros. inversion H3. subst.
    pose (EE1 := element_exist 0 vals H6).
    pose (EE2 := element_exist 0 _ H7).
    pose (EE3 := element_exist 0 _ H8).
    inversion EE1 as [x']. inversion EE2 as [eff1']. inversion EE3 as [id1'].
    inversion H4. inversion H5. inversion H9. subst. 
    inversion H7. inversion H8. inversion H6.
    apply eq_sym, length_zero_iff_nil in H12.
    apply eq_sym, length_zero_iff_nil in H13.
    apply eq_sym, length_zero_iff_nil in H14. subst.
(*     assert (x' = x /\ eff1' = eff ++ eff1 /\ id1' = (id0 + id1)%nat).
    { *)
      pose (P := H11 0 Nat.lt_0_1). simpl in P.
      pose (WD := determinism H1 _ _ _ P). destruct WD. destruct H12. inversion H10.
      subst.
(*     } *)
    inversion H16. subst.
    pose (EE1' := element_exist 0 vals H14).
    pose (EE2' := element_exist 0 _ H15).
    pose (EE3' := element_exist 0 _ H17).
    inversion EE1' as [x0']. inversion EE2' as [eff2']. inversion EE3' as [id2'].
    inversion H12. inversion H13. inversion H18. subst. 
    inversion H14. inversion H15. inversion H17.
    apply eq_sym, length_zero_iff_nil in H21.
    apply eq_sym, length_zero_iff_nil in H22.
    apply eq_sym, length_zero_iff_nil in H23. subst.
(*     assert (x0' = x0 /\ eff2' = eff ++ eff1 ++ eff2 /\ id2' = (id0 + id1 + id2)%nat).
    { *)
      pose (P2 := H20 0 Nat.lt_0_1). simpl in P.
      pose (WD := determinism H0 _ _ _ P2). 
      destruct WD. destruct H21. inversion H19.
      simpl in H21. simpl in H22. subst.
(*     } *)
   (*proving starts*)
   apply eval_let with (vals := [x0']) (eff := [eff ++ eff2]) (eff2 := eff ++ eff2 ++ eff1) 
                       (ids := [(id0 + id2)%nat]); auto.
   - intros. inversion H21.
     + assumption.
     + inversion H23.
   - apply eval_let with (vals := [x']) (eff := [eff ++ eff2 ++ eff1]) (eff2 := eff ++ eff2 ++ eff1)
                         (ids := [(id0 + id2 + id1)%nat]); auto.
     + intros. inversion H21.
       ** subst. simpl. assumption.
       ** inversion H23.
   (* call information *)
     + inversion H25. subst.
       pose (EC1 := element_exist 1 _ H23).
       pose (EC2 := element_exist 1 _ H24).
       pose (EC3 := element_exist 1 _ H26).
       inversion EC1 as [x'']. inversion EC2 as [eff1'']. inversion EC3 as [id1''].
       inversion H21. inversion H22. inversion H28. subst. 
       inversion H23. inversion H24. inversion H26.
       pose (EC1' := element_exist 0 _ H31).
       pose (EC2' := element_exist 0 _ H32).
       pose (EC3' := element_exist 0 _ H33).
       inversion EC1' as [x0'']. inversion EC2' as [eff2'']. inversion EC3' as [id2''].
       inversion H29. inversion H34. inversion H36. subst. 
       inversion H31. inversion H32. inversion H33.
       apply eq_sym, length_zero_iff_nil in H38.
       apply eq_sym, length_zero_iff_nil in H39.
       apply eq_sym, length_zero_iff_nil in H40. subst.
         
         pose (P1' := H27 0 Nat.lt_0_2).
         pose (P2' := H27 1 Nat.lt_1_2).
         inversion P1'. inversion P2'. simpl in H51, H52, H50, H49. subst.
         
         simpl in H42, H44, H40, H48. subst.
         
         rewrite get_value_there in H40. 2: congruence.
         rewrite get_value_here in H40. inversion H40.
         rewrite get_value_here in H48. inversion H48. subst.
       
       (* BACK TO CALL PROOF *)
       apply eval_call with (vals := [x0' ; x']) (eff := [eff ++ eff2 ++ eff1;eff ++ eff2 ++ eff1]) 
                    (ids := [(id0 + id2 + id1)%nat; (id0 + id2 + id1)%nat]); auto.
       ** intros. inversion H37. 2: inversion H39. 3: inversion H42.
         -- simpl. assert (get_value (insert_value (insert_value env (inl A) x0') 
                                     (inl B) x') (inl B) = inl x'). 
                                     { apply get_value_here. }
            rewrite <- H38. apply eval_var. reflexivity.
         -- simpl. subst. assert (get_value (insert_value (insert_value env (inl A) x0') 
                                           (inl B) x') (inl A) = inl x0').
                                           { rewrite get_value_there. apply get_value_here.
                                             unfold not. intros. inversion H33.
                                             congruence. }
            rewrite <- H38. apply eval_var. reflexivity.
       ** apply plus_comm_basic_value with (eff0 := eff ++ eff1 ++ eff2). assumption.
Qed.

Example let_2_comm_eq (env: Environment)(e1 e2 : Expression) (t x x0 : Value) 
    (eff eff1 eff2 : SideEffectList) (id0 id1 id2 : nat) (A B : Var) (VarHyp : A <> B) :
  |env, id0, e2, eff| -e> |id0 + id2, inl x0, eff ++ eff2| -> 
  |append_vars_to_env [A] [x] env, id0 + id1, e2, eff ++ eff1|
  -e> | id0 + id1 + id2, inl x0, eff ++ eff1 ++ eff2| ->
  |env, id0, e1, eff| -e> |id0 + id1, inl x, eff ++ eff1| -> 
  |append_vars_to_env [A] [x0] env, id0 + id2, e1, eff ++ eff2|
  -e> |id0 + id2 + id1, inl x, eff ++ eff2 ++ eff1| ->
  |env, id0, ELet [(A, e1)] (ELet [(B, e2)] 
        (ECall "+"%string [EVar A ; EVar B])), eff| -e> 
  | id0 + id1 + id2, inl t, eff ++ eff1 ++ eff2|
<->
  |env, id0, ELet [(A, e2)] (ELet [(B, e1)]
        (ECall "+"%string [EVar A ; EVar B])), eff| -e>
  | id0 + id2 + id1, inl t, eff ++ eff2 ++ eff1|
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
  |env, id0, e2, eff| -e> |id0 + id2, inl x0, eff ++ eff2| -> 
  |append_vars_to_env [A] [x] env, id0 + id1, e2, eff ++ eff1| -e>
  | id0 + id1 + id2, inl x0, eff ++ eff1 ++ eff2| ->
  |env, id0, e1, eff| -e> |id0 + id1, inl x, eff ++ eff1| -> 
  |append_vars_to_env [B] [x0] env, id0 + id2, e1, eff ++ eff2| -e>
  |id0 + id2 + id1, inl x, eff ++ eff2 ++ eff1|
->
  |env, id0, ELet [(A, e1)] (ELet [(B, e2)] 
        (ECall "+"%string [EVar A ; EVar B])), eff| -e>
  |id0 + id1 + id2, inl t, eff ++ eff1 ++ eff2|
<->
  |env, id0, ELet [(B, e2)] (ELet [(A, e1)]
        (ECall "+"%string [EVar A ; EVar B])), eff| -e>
  |id0 + id2 + id1, inl t, eff ++ eff2 ++ eff1|
.
Proof.
  split.
  * intros. inversion H3. subst.
    pose (EE1 := element_exist 0 vals H6).
    pose (EE2 := element_exist 0 _ H7).
    pose (EE3 := element_exist 0 _ H8).
    inversion EE1 as [x']. inversion EE2 as [eff1']. inversion EE3 as [id1'].
    inversion H4. inversion H5. inversion H9. subst. 
    inversion H7. inversion H8. inversion H6.
    apply eq_sym, length_zero_iff_nil in H12.
    apply eq_sym, length_zero_iff_nil in H13.
    apply eq_sym, length_zero_iff_nil in H14. subst.
      pose (P := H11 0 Nat.lt_0_1). simpl in P.
      pose (WD := determinism H1 _ _ _ P). destruct WD. destruct H12. inversion H10.
      subst.
    inversion H16. subst.
    pose (EE1' := element_exist 0 vals H14).
    pose (EE2' := element_exist 0 _ H15).
    pose (EE3' := element_exist 0 _ H17).
    inversion EE1' as [x0']. inversion EE2' as [eff2']. inversion EE3' as [id2'].
    inversion H12. inversion H13. inversion H18. subst. 
    inversion H14. inversion H15. inversion H17.
    apply eq_sym, length_zero_iff_nil in H22.
    apply eq_sym, length_zero_iff_nil in H23.
    apply eq_sym, length_zero_iff_nil in H21. subst.
      pose (P2 := H20 0 Nat.lt_0_1). simpl in P2.
      pose (WD := determinism H0 _ _ _ P2). 
      destruct WD. destruct H21. inversion H19. subst.
   (*proving starts*)
   apply eval_let with (vals := [x0']) (eff := [eff ++ eff2]) (eff2 := eff ++ eff2 ++ eff1) 
                       (ids := [(id0 + id2)%nat]); auto.
   - intros. inversion H21.
     + assumption.
     + inversion H23.
   - apply eval_let with (vals := [x']) (eff := [eff ++ eff2 ++ eff1]) (eff2 := eff ++ eff2 ++ eff1)
                         (ids := [(id0 + id2 + id1)%nat]); auto.
     + intros. inversion H21.
       ** subst. assumption.
       ** inversion H23.
   (* call information *)
     + inversion H25. subst.
       pose (EC1 := element_exist 1 _ H23).
       pose (EC2 := element_exist 1 _ H24).
       pose (EC3 := element_exist 1 _ H26).
       inversion EC1 as [x'']. inversion EC2 as [eff1'']. inversion EC3 as [id1''].
       inversion H21. inversion H22. inversion H28. subst. 
       inversion H23. inversion H24. inversion H26.
       pose (EC1' := element_exist 0 _ H31).
       pose (EC2' := element_exist 0 _ H32).
       pose (EC3' := element_exist 0 _ H33).
       inversion EC1' as [x0'']. inversion EC2' as [eff2'']. inversion EC3' as [id2''].
       inversion H29. inversion H34. inversion H36. subst. 
       inversion H31. inversion H32. inversion H33.
       apply eq_sym, length_zero_iff_nil in H38.
       apply eq_sym, length_zero_iff_nil in H39.
       apply eq_sym, length_zero_iff_nil in H40. subst.
         pose (P1' := H27 0 Nat.lt_0_2).
         pose (P2' := H27 1 Nat.lt_1_2).
         inversion P1'. inversion P2'. subst.
         
         simpl in H40, H42, H44, H48, H50, H52. subst.
         
         rewrite get_value_there in H40. 2: congruence.
         rewrite get_value_here in H40. inversion H40.
         rewrite get_value_here in H48. inversion H48.
         subst.
       
       (* BACK TO CALL PROOF *)
       apply eval_call with (vals := [x' ; x0']) (eff := [eff ++ eff2 ++ eff1;eff ++ eff2 ++ eff1]) 
                    (ids := [(id0 + id2 + id1)%nat; (id0 + id2 + id1)%nat]); auto.
       ** intros. inversion H37. 2: inversion H39. 3: inversion H42.
         -- simpl. assert (get_value (insert_value (insert_value env (inl B) x0') (inl A) x') (inl B) = inl x0'). 
                                     { rewrite get_value_there. apply get_value_here.
                                             unfold not. intros. inversion H33.
                                             congruence. }
            rewrite <- H38. apply eval_var. reflexivity.
         -- simpl. subst. assert (get_value (insert_value (insert_value env (inl B) x0') (inl A) x') (inl A) = inl x').
                                           { apply get_value_here. }
            rewrite <- H38. apply eval_var. reflexivity.
       ** apply plus_effect_changeable with (eff0 := eff ++ eff1 ++ eff2). assumption.
  * intros. inversion H3. subst.
    pose (EE1 := element_exist 0 vals H6).
    pose (EE2 := element_exist 0 _ H7).
    pose (EE3 := element_exist 0 _ H8).
    inversion EE1 as [x0']. inversion EE2 as [eff2']. inversion EE3 as [id2'].
    inversion H4. inversion H5. inversion H9. subst. 
    inversion H7. inversion H8. inversion H6.
    apply eq_sym, length_zero_iff_nil in H12.
    apply eq_sym, length_zero_iff_nil in H13.
    apply eq_sym, length_zero_iff_nil in H14. subst.
      pose (P := H11 0 Nat.lt_0_1). simpl in P.
      pose (WD := determinism H _ _ _ P). destruct WD. destruct H12. inversion H10.
      subst.
    inversion H16. subst.
    pose (EE1' := element_exist 0 vals H14).
    pose (EE2' := element_exist 0 _ H15).
    pose (EE3' := element_exist 0 _ H17).
    inversion EE1' as [x']. inversion EE2' as [eff1']. inversion EE3' as [id1'].
    inversion H12. inversion H13. inversion H18. subst. 
    inversion H14. inversion H15. inversion H17.
    apply eq_sym, length_zero_iff_nil in H21.
    apply eq_sym, length_zero_iff_nil in H23.
    apply eq_sym, length_zero_iff_nil in H22. subst.
      pose (P2 := H20 0 Nat.lt_0_1). simpl in P2.
      pose (WD := determinism H2 _ _ _ P2). 
      destruct WD. destruct H21. inversion H19. subst.
   (*proving starts*)
   apply eval_let with (vals := [x']) (eff := [eff ++ eff1]) (eff2 := eff ++ eff1 ++ eff2) 
                       (ids := [(id0 + id1)%nat]); auto.
   - intros. inversion H21.
     + assumption.
     + inversion H23.
   - apply eval_let with (vals := [x0']) (eff := [eff ++ eff1 ++ eff2]) (eff2 := eff ++ eff1 ++ eff2)
                         (ids := [(id0 + id1 + id2)%nat]); auto.
     + intros. inversion H21.
       ** subst. assumption.
       ** inversion H23.
   (* call information *)
     + inversion H25. subst.
       pose (EC1 := element_exist 1 _ H23).
       pose (EC2 := element_exist 1 _ H24).
       pose (EC3 := element_exist 1 _ H26).
       inversion EC1 as [x'']. inversion EC2 as [eff1'']. inversion EC3 as [id1''].
       inversion H21. inversion H22. inversion H28. subst. 
       inversion H23. inversion H24. inversion H26.
       pose (EC1' := element_exist 0 _ H31).
       pose (EC2' := element_exist 0 _ H32).
       pose (EC3' := element_exist 0 _ H33).
       inversion EC1' as [x0'']. inversion EC2' as [eff2'']. inversion EC3' as [id2''].
       inversion H29. inversion H34. inversion H36. subst. 
       inversion H31. inversion H32. inversion H33.
       apply eq_sym, length_zero_iff_nil in H38.
       apply eq_sym, length_zero_iff_nil in H39.
       apply eq_sym, length_zero_iff_nil in H40. subst.
         pose (P1' := H27 0 Nat.lt_0_2).
         pose (P2' := H27 1 Nat.lt_1_2).
         inversion P1'. inversion P2'. subst.
         
         simpl in H40, H42, H44, H48, H50, H52. subst.
         
         rewrite get_value_here in H40.
         rewrite get_value_there, get_value_here in H48. 2: congruence.
         inversion H40. inversion H48. subst.
       
       (* BACK TO CALL PROOF *)
       apply eval_call with (vals := [x' ; x0']) (eff := [eff ++ eff1 ++ eff2;eff ++ eff1 ++ eff2]) 
                    (ids := [(id0 + id1 + id2)%nat; (id0 + id1 + id2)%nat]); auto.
       ** intros. inversion H37. 2: inversion H39. 3: inversion H42.
         -- simpl. assert (get_value (insert_value (insert_value env (inl A) x') (inl B) x0') (inl B) = inl x0'). 
                                     { apply get_value_here. }
            rewrite <- H38. apply eval_var. reflexivity.
         -- simpl. subst. assert (get_value (insert_value (insert_value env (inl A) x') (inl B) x0') (inl A) = inl x').
                                           { rewrite get_value_there. apply get_value_here. congruence. }
            rewrite <- H38. apply eval_var. reflexivity.
       ** apply plus_effect_changeable with (eff0 := eff ++ eff2 ++ eff1). assumption.
Qed.

(* Example let_1_binding_swap_2_list (env: Environment) (e1 e2 : Expression) (t t' v1 v2 : Value) 
   (eff eff1 eff2 : SideEffectList) (A B : Var) (VarHyp : A <> B) (id id1 id2 : nat)
(Hypo1 : |env, id, e1, eff| -e> | id + id1, inl v1, eff ++ eff1|)
(Hypo2 : |env, id + id2, e1, eff ++ eff2| -e> | id + id1 + id2, inl v1, eff ++ eff2 ++ eff1|)
(Hypo1' : |env, id, e2, eff| -e> | id + id2, inl v2, eff ++ eff2|)
(Hypo2' : |env, id + id1, e2, eff ++ eff1| -e> | id + id2 + id1, inl v2, eff ++ eff1 ++ eff2|) :
|env, id, ELet [(A, e1); (B, e2)]
     (ECall "+"%string [EVar A ; EVar B]), eff| -e> | id + id1 + id2, inl t, eff ++ eff1 ++ eff2|
->
|env, id, ELet [(B, e2); (A, e1)]
     (ECall "+"%string [EVar B ; EVar A]), eff| -e> |id + id2 + id1, inl t', eff ++ eff2 ++ eff1|
->
t = t'.
Proof.
  intros.
  (* FROM LET HYPO1 *)
  inversion H. subst. simpl in H4, H5, H3.
  pose (EE1 := element_exist Value 1 vals H3).
  inversion EE1 as [v1']. inversion H1. subst. inversion H3.
  pose (EE2 := element_exist Value 0 x H7).
  inversion EE2 as [v2']. inversion H2. subst. inversion H3. 
  apply eq_sym, length_zero_iff_nil in H10. subst.
  pose (EE3 := element_exist _ _ _ H4). inversion EE3 as [eff1']. inversion H8. subst. inversion H4.
  pose (EE4 := element_exist _ _ _ H11). inversion EE4 as [eff2']. inversion H10. subst. inversion H4.
  apply eq_sym, length_zero_iff_nil in H13. subst.
  pose (EE5 := element_exist nat _ _ H5). inversion EE5 as [id1']. inversion H12. subst. inversion H5.
  pose (EE6 := element_exist _ _ _ H15). inversion EE6 as [id2']. inversion H13. subst. inversion H5.
  apply eq_sym, length_zero_iff_nil in H17. subst.
  (* FROM LET HYPO2 *)
  inversion H0. subst. simpl in H19, H20, H18.
  pose (EE1' := element_exist _ _ _ H18). inversion EE1' as [v2'']. inversion H16. subst. inversion H18.
  pose (EE2' := element_exist _ _ _ H22). inversion EE2' as [v1'']. inversion H17. subst. inversion H18.
  apply eq_sym, length_zero_iff_nil in H25. subst.
  pose (EE3' := element_exist _ _ _ H19). inversion EE3' as [eff2'']. inversion H23. subst. inversion H19.
  pose (EE4' := element_exist _ _ _ H26). inversion EE4' as [eff1'']. inversion H25. subst. inversion H19.
  apply eq_sym, length_zero_iff_nil in H28. subst.

  pose (EE5' := element_exist _ _ _ H20). inversion EE5' as [id2'']. inversion H27. subst. inversion H20.
  pose (EE6' := element_exist _ _ _ H30). inversion EE6' as [id1'']. inversion H28. subst. inversion H20.
  apply eq_sym, length_zero_iff_nil in H32. subst.

  (* assert (v1' = v1 /\ eff1' = eff1).
  { *)
    pose (P1 := H6 0 Nat.lt_0_2).
    unfold concatn in P1. simpl in P1. rewrite app_nil_r, app_nil_r in P1.
    pose (WD1 := determinism Hypo1).
    pose (PC1 := WD1 _ _ _ P1).
    destruct PC1. destruct H32. apply app_inv_head in H32. inversion H31. subst.
  (* } *)
  
  (* assert (v2'' = v2 /\ eff2'' = eff2).
  { *)
    pose (P2 := H21 0 Nat.lt_0_2).
    unfold concatn in P2. simpl in P2. rewrite app_nil_r, app_nil_r in P2.
    pose (WD2 := determinism Hypo1').
    pose (PC2 := WD2 _ _ _ P2).
    destruct PC2. destruct H33. inversion H32. apply app_inv_head in H33. subst. auto.
  (* } *)

  (* assert (v1'' = v1 /\ v2' = v2 /\ eff1'' = eff1 /\ eff2' = eff2).
  { *)
    pose (P3 := H21 1 Nat.lt_1_2).
    unfold concatn in P3. simpl in P3. rewrite app_nil_r, app_nil_r in P3.
    pose (WD3 := determinism Hypo2).
    pose (PC3 := WD3 _ _ _ P3).
    inversion PC3. inversion H34. inversion H33. apply app_inv_head, app_inv_head in H35. subst.
    pose (P4 := H6 1 Nat.lt_1_2).
    unfold concatn in P4. simpl in P4. rewrite app_nil_r, app_nil_r in P4.
    pose (WD4 := determinism Hypo2').
    pose (PC4 := WD4 _ _ _ P4).
    inversion PC4. inversion H36. inversion H35. apply app_inv_head, app_inv_head in H37. subst.
    clear EE1. clear EE2. clear EE3. clear EE4. clear EE5. clear EE6.
  (* } *)

  (* FROM CALL HYPOS *)
 (* FROM CALL HYPO1 *)
  inversion H14. subst. simpl in H39, H40, H41.
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
  inversion H29. subst. simpl in H54, H55, H56.
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
Qed. *)

Example let_1_comm_2_list_alt (env: Environment) (e1 e2 : Expression) (t v1 v2 : Value) 
   (eff eff1 eff2 : SideEffectList) (A B : Var) (VarHyp : A <> B) (id id1 id2 : nat)
(Hypo1 : |env, id, e1, eff| -e> | id + id1, inl v1, eff ++ eff1|)
(Hypo2 : |env, id + id2, e1, eff ++ eff2| -e> | id + id1 + id2, inl v1, eff ++ eff2 ++ eff1|)
(Hypo1' : |env, id, e2, eff| -e> | id + id2, inl v2, eff ++ eff2|)
(Hypo2' : |env, id + id1, e2, eff ++ eff1| -e> | id + id2 + id1, inl v2, eff ++ eff1 ++ eff2|) :
|env, id, ELet [(A, e1); (B, e2)]
     (ECall "+"%string [EVar A ; EVar B]), eff| -e> | id + id1 + id2, inl t, eff ++ eff1 ++ eff2|
->
|env, id, ELet [(A, e2); (B, e1)]
     (ECall "+"%string [EVar A ; EVar B]), eff| -e> | id + id2 + id1, inl t, eff ++ eff2 ++ eff1|.
Proof.
  intros.
  (* FROM LET HYPO *)
  inversion H. subst. simpl in H3, H4, H2.
  pose (EE1 := element_exist Value 1 vals H2). inversion EE1 as [v1']. inversion H0. subst. inversion H2.
  pose (EE2 := element_exist Value 0 x H6). inversion EE2 as [v2']. inversion H1. subst. inversion H2.
  apply eq_sym, length_zero_iff_nil in H9. subst.
  pose (EE3 := element_exist _ _ _ H3). inversion EE3 as [eff1']. inversion H7. subst. inversion H3.
  pose (EE4 := element_exist _ _ _ H10). inversion EE4 as [eff2']. inversion H9. subst. inversion H3.
  apply eq_sym, length_zero_iff_nil in H12. subst.
  pose (EE5 := element_exist _ _ _ H4). inversion EE5 as [id1']. inversion H11. subst. inversion H4.
  pose (EE6 := element_exist _ _ _ H14). inversion EE6 as [id2']. inversion H12. subst. inversion H4.
  apply eq_sym, length_zero_iff_nil in H16. subst.
  clear dependent H2. clear dependent H4. clear dependent H3.
  clear dependent H10. clear dependent H14. clear dependent H6.
  (* assert (v1' = v1 /\ v2' = v2 /\ eff1' = eff1 /\ eff2' = eff2).
  { *)
    pose (P1 := H5 0 Nat.lt_0_2).
    pose (P2 := H5 1 Nat.lt_1_2).
    simpl_concatn_H P1. simpl_concatn_H P2. rewrite <- app_assoc in P2.
    pose (D1 := determinism Hypo1 _ _ _ P1).
    destruct D1. destruct H3. inversion H2. apply app_inv_head in H3. subst.
    pose (D2 := determinism Hypo2' _ _ _ P2).
    destruct D2. destruct H4. inversion H3. apply app_inv_head, app_inv_head in H4. subst.
  (* } *)

  (* Deconstruct call *)

  inversion H13. subst.
  pose (EE1' := element_exist Value 1 vals H10). inversion EE1' as [v1''].
  inversion H4. subst. inversion H10.
  pose (EE2' := element_exist Value 0 x H17). inversion EE2' as [v2''].
  inversion H6. subst. inversion H10.
  apply eq_sym, length_zero_iff_nil in H20. subst.
  pose (EE3' := element_exist _ _ _ H14). inversion EE3' as [eff1'']. inversion H18. subst. inversion H14.
  pose (EE4' := element_exist _ _ _ H21). inversion EE4' as [eff2'']. inversion H20. subst. inversion H14.
  apply eq_sym, length_zero_iff_nil in H23. subst.
  pose (EE5' := element_exist _ _ _ H15). inversion EE5' as [id1'']. inversion H22. subst. inversion H15.
  pose (EE6' := element_exist _ _ _ H25). inversion EE6' as [id2'']. inversion H23. subst. inversion H15.
  apply eq_sym, length_zero_iff_nil in H27. subst.
  clear dependent H14. clear dependent H11. clear dependent H21.
  clear dependent H15. clear dependent H17. clear dependent H22.
  clear dependent H25. clear P1. clear dependent P2.
  (* assert (v1' = v1 /\ v2' = v2 /\ eff1' = [] /\ eff2' = []).
  { *)
    pose (P1 := H16 0 Nat.lt_0_2).
    pose (P2 := H16 1 Nat.lt_1_2).
    simpl_concatn_H P1. simpl_concatn_H P2. repeat (rewrite <- app_assoc in P2, P1).
    inversion P1.
    inversion P2. subst.
    rewrite <- app_nil_r in H26 at 1, H33 at 1.
    repeat (rewrite <- app_assoc in H26). repeat (rewrite <- app_assoc in H33).
    repeat (apply app_inv_head in H26). repeat (apply app_inv_head in H33). subst.
    simpl in H24.
    rewrite get_value_here in H32. inversion H32.
    rewrite get_value_there in H25. rewrite get_value_here in H25. inversion H25.
    subst.
    2: congruence.
  (* } *)

  (* construct derivation tree *)
  apply eval_let with (vals := [v2''; v1'']) (eff := [eff2'; eff1']) (eff2 := []) 
                      (ids := [(id + id2)%nat; (id + id2 + id1)%nat]); auto.
  * intros. inversion H11. 2: inversion H15.
    1-2: simpl_concatn; try(rewrite <- app_assoc).
    - rewrite <- H24. exact Hypo2.
    - assumption.
    - inversion H21.
  * simpl_concatn. auto.
  * simpl_concatn. apply eval_call with (vals := [v2''; v1'']) (eff := [[];[]])
                             (ids := [(id + id2 + id1)%nat; (id + id2 + id1)%nat]); auto.
    - intros. inversion H11. 2: inversion H15.
      + simpl_concatn. replace (inl v1'') with 
          (get_value (insert_value (insert_value env (inl A) v2'') (inl B) v1'') (inl B)).
        apply eval_var.
        apply get_value_here.
      + simpl_concatn. replace (inl v2'') with
          (get_value (insert_value (insert_value env (inl A) v2'') (inl B) v1'') (inl A)).
        apply eval_var.
        rewrite get_value_there. apply get_value_here. congruence.
      + inversion H21.
    - unfold concatn in *. simpl concat. repeat (rewrite <- app_assoc).
      simpl concat in H19. repeat (rewrite <- app_assoc in H19).
      repeat (rewrite app_nil_r in *).
      apply (plus_comm_basic_value _ _ H19).
Qed.

Example let_1_comm_2_list_alt_eq (env: Environment) (e1 e2 : Expression) (t v1 v2 : Value) 
   (eff eff1 eff2 : SideEffectList) (A B : Var) (VarHyp : A <> B) (id id1 id2 : nat)
(Hypo1 : |env, id, e1, eff| -e> | id + id1, inl v1, eff ++ eff1|)
(Hypo2 : |env, id + id2, e1, eff ++ eff2| -e> | id + id1 + id2, inl v1, eff ++ eff2 ++ eff1|)
(Hypo1' : |env, id, e2, eff| -e> | id + id2, inl v2, eff ++ eff2|)
(Hypo2' : |env, id + id1, e2, eff ++ eff1| -e> | id + id2 + id1, inl v2, eff ++ eff1 ++ eff2|) :
|env, id, ELet [(A, e1); (B, e2)]
     (ECall "+"%string [EVar A ; EVar B]), eff| -e> | id + id1 + id2, inl t, eff ++ eff1 ++ eff2|
<->
|env, id, ELet [(A, e2); (B, e1)]
     (ECall "+"%string [EVar A ; EVar B]), eff| -e> | id + id2 + id1, inl t, eff ++ eff2 ++ eff1|.
Proof.
  split.
  * apply let_1_comm_2_list_alt with (v1 := v1) (v2 := v2); assumption.
  * apply let_1_comm_2_list_alt with (v1 := v2) (v2 := v1); assumption.
Qed.

Example let_1_binding_swap_2_list_alt (env: Environment) (e1 e2 : Expression) (t v1 v2 : Value) 
   (eff eff1 eff2 : SideEffectList) (A B : Var) (VarHyp : A <> B) (id id1 id2 : nat)
(Hypo1 : |env, id, e1, eff| -e> | id + id1, inl v1, eff ++ eff1|)
(Hypo2 : |env, id + id2, e1, eff ++ eff2| -e> | id + id1 + id2, inl v1, eff ++ eff2 ++ eff1|)
(Hypo1' : |env, id, e2, eff| -e> | id + id2, inl v2, eff ++ eff2|)
(Hypo2' : |env, id + id1, e2, eff ++ eff1| -e> | id + id2 + id1, inl v2, eff ++ eff1 ++ eff2|) :
|env, id, ELet [(A, e1); (B, e2)]
     (ECall "+"%string [EVar A ; EVar B]), eff| -e> | id + id1 + id2, inl t, eff ++ eff1 ++ eff2|
<->
|env, id, ELet [(B, e2); (A, e1)]
     (ECall "+"%string [EVar B ; EVar A]), eff| -e> | id + id2 + id1, inl t, eff ++ eff2 ++ eff1|.
Proof.
  split.
  * intros.
  (* FROM LET HYPO *)
  inversion H. subst. simpl in H3, H4, H2.
  pose (EE1 := element_exist Value 1 vals H2). inversion EE1 as [v1']. inversion H0. subst. inversion H2.
  pose (EE2 := element_exist Value 0 x H6). inversion EE2 as [v2']. inversion H1. subst. inversion H2.
  apply eq_sym, length_zero_iff_nil in H9. subst.
  pose (EE3 := element_exist _ _ _ H3). inversion EE3 as [eff1']. inversion H7. subst. inversion H3.
  pose (EE4 := element_exist _ _ _ H10). inversion EE4 as [eff2']. inversion H9. subst. inversion H3.
  apply eq_sym, length_zero_iff_nil in H12. subst.
  pose (EE5 := element_exist _ _ _ H4). inversion EE5 as [id1']. inversion H11. subst. inversion H4.
  pose (EE6 := element_exist _ _ _ H14). inversion EE6 as [id2']. inversion H12. subst. inversion H4.
  apply eq_sym, length_zero_iff_nil in H16. subst.
  clear dependent H2. clear dependent H4. clear dependent H3.
  clear dependent H10. clear dependent H14. clear dependent H6.
  (* assert (v1' = v1 /\ v2' = v2 /\ eff1' = eff1 /\ eff2' = eff2).
  { *)
    pose (P1 := H5 0 Nat.lt_0_2).
    pose (P2 := H5 1 Nat.lt_1_2).
    simpl_concatn_H P1. simpl_concatn_H P2. rewrite <- app_assoc in P2.
    pose (D1 := determinism Hypo1 _ _ _ P1).
    destruct D1. destruct H3. inversion H2. apply app_inv_head in H3. subst.
    pose (D2 := determinism Hypo2' _ _ _ P2).
    destruct D2. destruct H4. inversion H3. apply app_inv_head, app_inv_head in H4. subst.
  (* } *)

  (* Deconstruct call *)

  inversion H13. subst.
  pose (EE1' := element_exist Value 1 vals H10). inversion EE1' as [v1''].
  inversion H4. subst. inversion H10.
  pose (EE2' := element_exist Value 0 x H17). inversion EE2' as [v2''].
  inversion H6. subst. inversion H10.
  apply eq_sym, length_zero_iff_nil in H20. subst.
  pose (EE3' := element_exist _ _ _ H14). inversion EE3' as [eff1'']. inversion H18. subst. inversion H14.
  pose (EE4' := element_exist _ _ _ H21). inversion EE4' as [eff2'']. inversion H20. subst. inversion H14.
  apply eq_sym, length_zero_iff_nil in H23. subst.
  pose (EE5' := element_exist _ _ _ H15). inversion EE5' as [id1'']. inversion H22. subst. inversion H15.
  pose (EE6' := element_exist _ _ _ H25). inversion EE6' as [id2'']. inversion H23. subst. inversion H15.
  apply eq_sym, length_zero_iff_nil in H27. subst.
  clear dependent H14. clear dependent H11. clear dependent H21.
  clear dependent H15. clear dependent H17. clear dependent H22.
  clear dependent H25. clear P1. clear dependent P2.
  (* assert (v1' = v1 /\ v2' = v2 /\ eff1' = [] /\ eff2' = []).
  { *)
    pose (P1 := H16 0 Nat.lt_0_2).
    pose (P2 := H16 1 Nat.lt_1_2).
    simpl_concatn_H P1. simpl_concatn_H P2. repeat (rewrite <- app_assoc in P2, P1).
    inversion P1.
    inversion P2. subst.
    rewrite <- app_nil_r in H26 at 1, H33 at 1.
    repeat (rewrite <- app_assoc in H26). repeat (rewrite <- app_assoc in H33).
    repeat (apply app_inv_head in H26). repeat (apply app_inv_head in H33). subst.
    simpl in H24.
    rewrite get_value_here in H32. inversion H32.
    rewrite get_value_there in H25. rewrite get_value_here in H25. inversion H25.
    subst.
    2: congruence.
  (* } *)

  (* construct derivation tree *)
  apply eval_let with (vals := [v2''; v1'']) (eff := [eff2'; eff1']) (eff2 := []) 
                      (ids := [(id + id2)%nat; (id + id2 + id1)%nat]); auto.
  - intros. inversion H11. 2: inversion H15.
    1-2: simpl_concatn; try(rewrite <- app_assoc).
    + rewrite <- H24. exact Hypo2.
    + assumption.
    + inversion H21.
  - simpl_concatn. auto.
  - simpl_concatn. apply eval_call with (vals := [v2''; v1'']) (eff := [[];[]])
                             (ids := [(id + id2 + id1)%nat; (id + id2 + id1)%nat]); auto.
    + intros. inversion H11. 2: inversion H15.
      ** simpl_concatn. replace (inl v1'') with 
          (get_value (insert_value (insert_value env (inl B) v2'') (inl A) v1'') (inl A)).
         apply eval_var.
         apply get_value_here.
      ** simpl_concatn. replace (inl v2'') with
          (get_value (insert_value (insert_value env (inl B) v2'') (inl A) v1'') (inl B)).
         apply eval_var.
         rewrite get_value_there. apply get_value_here. congruence.
      ** inversion H21.
    + unfold concatn in *. simpl concat. repeat (rewrite <- app_assoc).
      simpl concat in H19. repeat (rewrite <- app_assoc in H19).
      repeat (rewrite app_nil_r in *).
      apply (plus_comm_basic_value _ _ H19).
  * intros.
  (* FROM LET HYPO *)
  inversion H. subst. simpl in H3, H4, H2.
  pose (EE1 := element_exist Value 1 vals H2). inversion EE1 as [v2']. inversion H0. subst. inversion H2.
  pose (EE2 := element_exist Value 0 x H6). inversion EE2 as [v1']. inversion H1. subst. inversion H2.
  apply eq_sym, length_zero_iff_nil in H9. subst.
  pose (EE3 := element_exist _ _ _ H3). inversion EE3 as [eff2']. inversion H7. subst. inversion H3.
  pose (EE4 := element_exist _ _ _ H10). inversion EE4 as [eff1']. inversion H9. subst. inversion H3.
  apply eq_sym, length_zero_iff_nil in H12. subst.
  pose (EE5 := element_exist _ _ _ H4). inversion EE5 as [id2']. inversion H11. subst. inversion H4.
  pose (EE6 := element_exist _ _ _ H14). inversion EE6 as [id1']. inversion H12. subst. inversion H4.
  apply eq_sym, length_zero_iff_nil in H16. subst.
  clear dependent H2. clear dependent H4. clear dependent H3.
  clear dependent H10. clear dependent H14. clear dependent H6.
  (* assert (v1' = v1 /\ v2' = v2 /\ eff1' = eff1 /\ eff2' = eff2).
  { *)
    pose (P1 := H5 0 Nat.lt_0_2).
    pose (P2 := H5 1 Nat.lt_1_2).
    simpl_concatn_H P1. simpl_concatn_H P2. rewrite <- app_assoc in P2.
    pose (D1 := determinism Hypo1' _ _ _ P1).
    destruct D1. destruct H3. inversion H2. apply app_inv_head in H3. subst.
    pose (D2 := determinism Hypo2 _ _ _ P2).
    destruct D2. destruct H4. inversion H3. apply app_inv_head, app_inv_head in H4. subst.
  (* } *)

  (* Deconstruct call *)

  inversion H13. subst.
  pose (EE1' := element_exist Value 1 vals H10). inversion EE1' as [v2''].
  inversion H4. subst. inversion H10.
  pose (EE2' := element_exist Value 0 x H17). inversion EE2' as [v1''].
  inversion H6. subst. inversion H10.
  apply eq_sym, length_zero_iff_nil in H20. subst.
  pose (EE3' := element_exist _ _ _ H14). inversion EE3' as [eff2'']. inversion H18. subst. inversion H14.
  pose (EE4' := element_exist _ _ _ H21). inversion EE4' as [eff1'']. inversion H20. subst. inversion H14.
  apply eq_sym, length_zero_iff_nil in H23. subst.
  pose (EE5' := element_exist _ _ _ H15). inversion EE5' as [id2'']. inversion H22. subst. inversion H15.
  pose (EE6' := element_exist _ _ _ H25). inversion EE6' as [id1'']. inversion H23. subst. inversion H15.
  apply eq_sym, length_zero_iff_nil in H27. subst.
  clear dependent H14. clear dependent H11. clear dependent H21.
  clear dependent H15. clear dependent H17. clear dependent H22.
  clear dependent H25. clear P1. clear dependent P2.
  (* assert (v1' = v1 /\ v2' = v2 /\ eff1' = [] /\ eff2' = []).
  { *)
    pose (P1 := H16 0 Nat.lt_0_2).
    pose (P2 := H16 1 Nat.lt_1_2).
    simpl_concatn_H P1. simpl_concatn_H P2. repeat (rewrite <- app_assoc in P2, P1).
    inversion P1.
    inversion P2. subst.
    rewrite <- app_nil_r in H26 at 1, H33 at 1.
    repeat (rewrite <- app_assoc in H26). repeat (rewrite <- app_assoc in H33).
    repeat (apply app_inv_head in H26). repeat (apply app_inv_head in H33). subst.
    simpl in H24.
    rewrite get_value_here in H32. inversion H32.
    rewrite get_value_there in H25. rewrite get_value_here in H25. inversion H25.
    subst.
    2: congruence.
  (* } *)

  (* construct derivation tree *)
  apply eval_let with (vals := [v1''; v2'']) (eff := [eff1'; eff2']) (eff2 := []) 
                      (ids := [(id + id1)%nat; (id + id1 + id2)%nat]); auto.
  - intros. inversion H11. 2: inversion H15.
    1-2: simpl_concatn; try(rewrite <- app_assoc).
    + rewrite <- H24. exact Hypo2'.
    + assumption.
    + inversion H21.
  - simpl_concatn. auto.
  - simpl_concatn. apply eval_call with (vals := [v1''; v2'']) (eff := [[];[]])
                             (ids := [(id + id1 + id2)%nat; (id + id1 + id2)%nat]); auto.
    + intros. inversion H11. 2: inversion H15.
      ** simpl_concatn. replace (inl v2'') with 
          (get_value (insert_value (insert_value env (inl A) v1'') (inl B) v2'') (inl B)).
         apply eval_var. apply get_value_here.
      ** simpl_concatn. replace (inl v1'') with
          (get_value (insert_value (insert_value env (inl A) v1'') (inl B) v2'') (inl A)).
         apply eval_var.
         rewrite get_value_there. apply get_value_here. congruence.
      ** inversion H21.
    + unfold concatn in *. simpl concat. repeat (rewrite <- app_assoc).
      simpl concat in H19. repeat (rewrite <- app_assoc in H19).
      repeat (rewrite app_nil_r in *).
      apply (plus_comm_basic_value _ _ H19).
Qed.

Example let_2_apply_effect_free (env: Environment)(e1 e2 exp : Expression) (v1 v2 : Value) 
       (v0 t : Value + Exception) (A B : Var) (VarHyp : A <> B) (id : nat) (eff : SideEffectList)
(E1 : | append_vars_to_env [A] [v1] (append_vars_to_env [B] [v2] env), id, exp, eff | -e> |id, v0, eff|)
(E2 : | append_vars_to_env [B] [v2] (append_vars_to_env [A] [v1] env), id, exp, eff | -e> |id, v0, eff|)
    :
  |env, id, e2, eff| -e> |id, inl v2, eff| -> 
  |append_vars_to_env [A] [v1] env, id, e2, eff| -e> | id, inl v2, eff| ->
  |env, id, e1, eff| -e> | id, inl v1, eff| -> 
  |append_vars_to_env [B] [v2] env, id, e1, eff| -e> | id, inl v1, eff|
->
  |env, id, ELet [(A, e1)] (ELet [(B, e2)] 
        (EApp exp [EVar A ; EVar B])), eff| -e> |id, t, eff|
  <->
  |env, id, ELet [(B, e2)] (ELet [(A, e1)]
        (EApp exp [EVar A ; EVar B])), eff| -e> |id, t, eff|
.
Proof.
  split;intros. 
   (** Deconstruct ELet-s *)
  * inversion H3. subst.
    pose (EE1 := element_exist Value 0 vals H6). inversion EE1 as [v1'].
    inversion H4. subst. inversion H6.
    apply eq_sym, length_zero_iff_nil in H10. subst.
    pose (EE2 := element_exist _ 0 _ H7). inversion EE2 as [eff1'].
    inversion H5. subst. inversion H7.
    apply eq_sym, length_zero_iff_nil in H11. subst.
    pose (EE3 := element_exist _ 0 _ H8). inversion EE3 as [id1'].
    inversion H10. subst. inversion H8.
    apply eq_sym, length_zero_iff_nil in H13. subst.
    (* assert (v1' = v1 /\ eff1' = []).
    { *)
      pose (P := H9 0 Nat.lt_0_1).
      unfold concatn in P. simpl in P. rewrite app_nil_r in P.
      pose (WD := determinism H1 _ _ _ P). destruct WD. destruct H13. inversion H11.
      rewrite <- app_nil_r in H13 at 1. apply app_inv_head in H13.
      rewrite app_nil_r in H13.
      subst.
    (* } *)
    simpl_concatn_H H12.
    rewrite <- app_nil_r in H12 at 1.
    apply app_inv_head in H12. subst.
    inversion H17. subst.
    pose (EE4 := element_exist Value 0 vals H14).
    inversion EE4 as [v2']. inversion H12. subst. inversion H14.
    apply eq_sym, length_zero_iff_nil in H19. subst.
    pose (EE5 := element_exist _ _ _ H15).
    inversion EE5 as [eff2']. inversion H13. subst.
    inversion H15.
    apply eq_sym, length_zero_iff_nil in H20. subst.
    pose (EE6 := element_exist _ _ _ H16). inversion EE6 as [id2']. 
    inversion H19. subst.
    inversion H16. apply eq_sym, length_zero_iff_nil in H22. subst.
    clear dependent H14. clear dependent H15. clear dependent H16.
    clear dependent P.
    (* assert (v2' = v2 /\ eff2' = []). 
    { *)
      pose (P := H18 0 Nat.lt_0_1). unfold concatn in P. simpl in P.
      rewrite app_nil_r, app_nil_r in P.
      pose (WD := determinism H0 _ _ _ P). destruct WD. destruct H15.
      rewrite <- app_nil_r in H15 at 1. apply app_inv_head in H15. rewrite app_nil_r in H15.
      inversion H14.
      subst.
      simpl_concatn_H H21. rewrite <- app_nil_r in H21 at 1. apply app_inv_head in H21.
      subst.
    (* } *)
    apply eval_let with (vals := [v2']) (eff := [[]]) (eff2 := []) (ids := [id2']); auto.
     - intros. inversion H15.
       + unfold concatn. simpl_app. assumption.
       + inversion H20.
     - simpl_concatn. auto.
     - apply eval_let with (vals := [v1']) (eff := [[]]) (eff2 := []) (ids := [id2']); auto.
       + intros. inversion H15.
         ** subst. unfold concatn. simpl concat. simpl nth. simpl_app. assumption.
         ** inversion H20.
       + simpl_concatn. auto.
     (** Destruct application hypothesis *)
       + inversion H26; subst.
         ** simpl_concatn_H H21.
            pose (WD3 := determinism E2 _ _ _ H21). destruct WD3.
            inversion H15. destruct H16. subst.
            pose (EEA := element_exist _ _ _ H20).
            inversion EEA as [v1'']. inversion H15. subst. inversion H20. 
            pose (EEA2 := element_exist _ _ _ H30).
            inversion EEA2 as [v2'']. inversion H28. subst. inversion H20.
            apply eq_sym, length_zero_iff_nil in H32. subst.
            pose (EEE := element_exist _ _ _ H23).
            inversion EEE as [eff1'']. inversion H31. subst. inversion H23.
            pose (EEE2 := element_exist _ _ _ H33).
            inversion EEE2 as [eff2'']. inversion H32. subst. inversion H33.
            apply eq_sym, length_zero_iff_nil in H36. subst.
            pose (EEI := element_exist _ _ _ H24).
            inversion EEI as [id1'']. inversion H35. subst. inversion H24.
            pose (EEI2 := element_exist _ _ _ H37).
            inversion EEI2 as [id2'']. inversion H36. subst. inversion H24.
            apply eq_sym, length_zero_iff_nil in H39. subst.
            clear dependent H20. clear dependent H23. clear dependent H24.
            clear dependent H30. clear dependent H33. clear dependent H37.
            clear dependent P.
            (* assert (v1' = v1 /\ v2' = v2 /\ eff1' = [] /\ eff2' = []).
            { *)
              pose (P := H25 0 Nat.lt_0_2). unfold concatn in P. simpl in P.
              inversion P.
              rewrite get_value_there in H38. 2: congruence. 
              rewrite get_value_here in H38.
              inversion H38.
              simpl_app_H H39.
              rewrite <- app_nil_r in H39 at 1. apply app_inv_head in H39.
              subst.

              pose (P2 := H25 1 Nat.lt_1_2). unfold concatn in P2. simpl in P2.
              inversion P2. rewrite get_value_here in H39. inversion H39.
              apply app_inv_head in H40.
              rewrite app_nil_r in H40.
              simpl_concatn_H H29.
              rewrite <- app_nil_r in H16 at 1. apply app_inv_head in H16. subst.
              repeat (rewrite app_nil_r in *).
              rewrite <- app_nil_r in H29 at 1. apply app_inv_head in H29. subst.
            (* } *)
            eapply eval_apply with (vals := [v1''; v2'']) (eff := [[]; []])
                                   (ids := [id2'';id2'']); auto.
            -- unfold concatn. simpl concat. repeat (rewrite app_nil_r). exact E1.
            -- auto.
            -- intros. inversion H16. 2: inversion H23.
              ++ simpl_concatn. replace (inl v2'') with
                   (get_value (insert_value (insert_value env (inl B) v2'') (inl A) v1'') (inl B)).
                 apply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
              ++ simpl_concatn. replace (inl v1'') with
                   (get_value (insert_value (insert_value env (inl B) v2'') (inl A) v1'') (inl A)).
                 apply eval_var. rewrite get_value_here. auto.
              ++ inversion H29.
            -- unfold concatn. simpl_app. reflexivity.
            -- simpl_concatn. simpl_concatn_H H34. simpl_concatn. exact H34.
         ** eapply eval_apply_ex_closure_ex; try(reflexivity).
            -- exact H22.
            -- simpl_concatn_H H28.
               pose (WD := determinism E2 _ _ _ H28). destruct WD. destruct H16.
               simpl_concatn. simpl in E1. subst. exact E1.
         ** inversion H21.
            -- pose (EEA := element_exist _ _ _  (eq_sym H16)). inversion EEA as [v1''].
               inversion H15. subst.
               inversion H16. apply length_zero_iff_nil in H27. subst. 
               simpl in H34. inversion H34.
               rewrite get_value_here in H33. congruence.
            -- inversion H16.
              ++ rewrite H27 in *. simpl in H34. inversion H34.
               rewrite get_value_there, get_value_here in H35; congruence.
              ++ inversion H27.
         ** simpl_concatn_H H23.
            pose (WD := determinism E2 _ _ _ H23).
            destruct WD. destruct H16.
            rewrite <- app_nil_r in H16 at 1.
            apply app_inv_head in H16.
            subst.
            eapply eval_apply_ex_closure with (vals := [v1'; v2']) (eff := [[];[]])
                                              (ids := [id';id']); auto.
           -- simpl_concatn. simpl in E1. exact E1.
           -- intros. inversion H15. 2: inversion H28.
              ++ simpl_concatn. replace (inl v2') with
                   (get_value (insert_value (insert_value env (inl B) v2') (inl A) v1') (inl B)).
                 apply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
              ++ simpl_concatn. replace (inl v1') with
                   (get_value (insert_value (insert_value env (inl B) v2') (inl A) v1') (inl A)).
                 rewrite H27.
                 apply eval_var. rewrite get_value_here. auto.
              ++ inversion H31.
           -- simpl_concatn. reflexivity.
         ** simpl_concatn_H H23. pose (WD := determinism E2 _ _ _ H23).
            inversion WD. destruct H16. subst.
            eapply eval_apply_ex_param_count with (vals := [v1'; v2']) (eff := [[];[]])
                                   (ids := [id'; id']); auto.
           -- simpl_concatn. simpl in E1. exact E1.
           -- intros. inversion H15. 2: inversion H30.
              ++ simpl_concatn. replace (inl v2') with
                   (get_value (insert_value (insert_value env (inl B) v2') (inl A) v1') (inl B)).
                 apply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
              ++ simpl_concatn. replace (inl v1') with
                   (get_value (insert_value (insert_value env (inl B) v2') (inl A) v1') (inl A)).
              rewrite H27.
              apply eval_var. rewrite get_value_here. auto.
              ++ inversion H32.
           -- rewrite <- H20 in H25. auto.
           -- simpl_concatn. reflexivity.
      - simpl_concatn_H H23. subst. inversion H15.
        rewrite H13 in *.
        apply length_zero_iff_nil in H18. subst.
        simpl_concatn_H H27.
        pose (WD := determinism H0 _ _ _ H27).
        destruct WD. destruct H14. inversion H12.
        inversion H13.
      - subst. inversion H7. rewrite H5 in *.
        apply length_zero_iff_nil in H9. subst.
        simpl_concatn_H H18.
        pose (WD := determinism H1 _ _ _ H18).
        destruct WD. inversion H4.
        inversion H5.
    * inversion H3. subst.
    pose (EE1 := element_exist Value 0 vals H6). inversion EE1 as [v2'].
    inversion H4. subst. inversion H6.
    apply eq_sym, length_zero_iff_nil in H10. subst.
    pose (EE2 := element_exist _ 0 _ H7). inversion EE2 as [eff2'].
    inversion H5. subst. inversion H7.
    apply eq_sym, length_zero_iff_nil in H11. subst.
    pose (EE3 := element_exist _ 0 _ H8). inversion EE3 as [id2'].
    inversion H10. subst. inversion H8.
    apply eq_sym, length_zero_iff_nil in H13. subst.
    (* assert (v1' = v1 /\ eff1' = []).
    { *)
      pose (P := H9 0 Nat.lt_0_1).
      unfold concatn in P. simpl in P. rewrite app_nil_r in P.
      pose (WD := determinism H _ _ _ P). destruct WD. destruct H13. inversion H11.
      rewrite <- app_nil_r in H13 at 1. apply app_inv_head in H13.
      rewrite app_nil_r in H13.
      subst.
    (* } *)
    simpl_concatn_H H12.
    rewrite <- app_nil_r in H12 at 1.
    apply app_inv_head in H12. subst.
    inversion H17. subst.
    pose (EE4 := element_exist Value 0 vals H14).
    inversion EE4 as [v1']. inversion H12. subst. inversion H14.
    apply eq_sym, length_zero_iff_nil in H19. subst.
    pose (EE5 := element_exist _ _ _ H15).
    inversion EE5 as [eff1']. inversion H13. subst.
    inversion H15.
    apply eq_sym, length_zero_iff_nil in H20. subst.
    pose (EE6 := element_exist _ _ _ H16). inversion EE6 as [id1']. 
    inversion H19. subst.
    inversion H16. apply eq_sym, length_zero_iff_nil in H22. subst.
    clear dependent H14. clear dependent H15. clear dependent H16.
    clear dependent P.
    (* assert (v2' = v2 /\ eff2' = []). 
    { *)
      pose (P := H18 0 Nat.lt_0_1). unfold concatn in P. simpl in P.
      rewrite app_nil_r, app_nil_r in P.
      pose (WD := determinism H2 _ _ _ P). destruct WD. destruct H15.
      rewrite <- app_nil_r in H15 at 1. apply app_inv_head in H15. rewrite app_nil_r in H15.
      inversion H14.
      subst.
      simpl_concatn_H H21. rewrite <- app_nil_r in H21 at 1. apply app_inv_head in H21.
      subst.
    (* } *)
    apply eval_let with (vals := [v1']) (eff := [[]]) (eff2 := []) (ids := [id1']); auto.
     - intros. inversion H15.
       + unfold concatn. simpl_app. assumption.
       + inversion H20.
     - simpl_concatn. auto.
     - apply eval_let with (vals := [v2']) (eff := [[]]) (eff2 := []) (ids := [id1']); auto.
       + intros. inversion H15.
         ** subst. unfold concatn. simpl concat. simpl nth. simpl_app. assumption.
         ** inversion H20.
       + simpl_concatn. auto.
     (** Destruct application hypothesis *)
       + inversion H26; subst.
         ** simpl_concatn_H H21.
            pose (WD3 := determinism E1 _ _ _ H21). destruct WD3.
            inversion H15. destruct H16. subst.
            pose (EEA := element_exist _ _ _ H20).
            inversion EEA as [v1'']. inversion H15. subst. inversion H20. 
            pose (EEA2 := element_exist _ _ _ H30).
            inversion EEA2 as [v2'']. inversion H28. subst. inversion H20.
            apply eq_sym, length_zero_iff_nil in H32. subst.
            pose (EEE := element_exist _ _ _ H23).
            inversion EEE as [eff1'']. inversion H31. subst. inversion H23.
            pose (EEE2 := element_exist _ _ _ H33).
            inversion EEE2 as [eff2'']. inversion H32. subst. inversion H33.
            apply eq_sym, length_zero_iff_nil in H36. subst.
            pose (EEI := element_exist _ _ _ H24).
            inversion EEI as [id1'']. inversion H35. subst. inversion H24.
            pose (EEI2 := element_exist _ _ _ H37).
            inversion EEI2 as [id2'']. inversion H36. subst. inversion H24.
            apply eq_sym, length_zero_iff_nil in H39. subst.
            clear dependent H20. clear dependent H23. clear dependent H24.
            clear dependent H30. clear dependent H33. clear dependent H37.
            clear dependent P.
            (* assert (v1' = v1 /\ v2' = v2 /\ eff1' = [] /\ eff2' = []).
            { *)
              pose (P := H25 0 Nat.lt_0_2). unfold concatn in P. simpl in P.
              inversion P.
              rewrite get_value_here in H38.
              inversion H38.
              simpl_app_H H39.
              rewrite <- app_nil_r in H39 at 1. apply app_inv_head in H39.
              subst.

              pose (P2 := H25 1 Nat.lt_1_2). unfold concatn in P2. simpl in P2.
              inversion P2. rewrite get_value_there, get_value_here in H39.
              2: congruence.
              inversion H39.
              apply app_inv_head in H40.
              rewrite app_nil_r in H40.
              simpl_concatn_H H29.
              rewrite <- app_nil_r in H16 at 1. apply app_inv_head in H16. subst.
              repeat (rewrite app_nil_r in *).
              rewrite <- app_nil_r in H29 at 1. apply app_inv_head in H29. subst.
            (* } *)
            eapply eval_apply with (vals := [v1''; v2'']) (eff := [[]; []])
                                   (ids := [id2'';id2'']); auto.
            -- unfold concatn. simpl concat. repeat (rewrite app_nil_r). exact E2.
            -- auto.
            -- intros. inversion H16. 2: inversion H23.
              ++ simpl_concatn. replace (inl v2'') with
                   (get_value (insert_value (insert_value env (inl A) v1'') (inl B) v2'') (inl B)).
                 apply eval_var. 
                 rewrite get_value_here. auto.
              ++ simpl_concatn. replace (inl v1'') with
                   (get_value (insert_value (insert_value env (inl A) v1'') (inl B) v2'') (inl A)).
                 apply eval_var. rewrite get_value_there, get_value_here. auto. congruence.
              ++ inversion H29.
            -- unfold concatn. simpl_app. reflexivity.
            -- simpl_concatn. simpl_concatn_H H34. simpl_concatn. exact H34.
         ** eapply eval_apply_ex_closure_ex; try(reflexivity).
            -- exact H22.
            -- simpl_concatn_H H28.
               pose (WD := determinism E1 _ _ _ H28). destruct WD. destruct H16.
               simpl_concatn. simpl in E2. subst. exact E2.
         ** inversion H21.
            -- pose (EEA := element_exist _ _ _  (eq_sym H16)). inversion EEA as [v1''].
               inversion H15. subst.
               inversion H16. apply length_zero_iff_nil in H27. subst. 
               simpl in H34. inversion H34.
               rewrite get_value_there, get_value_here in H33; congruence.
            -- inversion H16.
              ++ rewrite H27 in *. simpl in H34. inversion H34.
               rewrite get_value_here in H35. congruence.
              ++ inversion H27.
         ** simpl_concatn_H H23.
            pose (WD := determinism E1 _ _ _ H23).
            destruct WD. destruct H16.
            rewrite <- app_nil_r in H16 at 1.
            apply app_inv_head in H16.
            subst.
            eapply eval_apply_ex_closure with (vals := [v1'; v2']) (eff := [[];[]])
                                              (ids := [id';id']); auto.
           -- simpl_concatn. simpl in E1. exact E2.
           -- intros. inversion H15. 2: inversion H28.
              ++ simpl_concatn. replace (inl v2') with
                   (get_value (insert_value (insert_value env (inl A) v1') (inl B) v2') (inl B)).
                 apply eval_var.
                 rewrite get_value_here. auto.
              ++ simpl_concatn. replace (inl v1') with
                   (get_value (insert_value (insert_value env (inl A) v1') (inl B) v2') (inl A)).
                 rewrite H27.
                 apply eval_var. 
                 rewrite get_value_there, get_value_here. auto. congruence.
              ++ inversion H31.
           -- simpl_concatn. reflexivity.
         ** simpl_concatn_H H23. pose (WD := determinism E1 _ _ _ H23).
            inversion WD. destruct H16. subst.
            eapply eval_apply_ex_param_count with (vals := [v1'; v2']) (eff := [[];[]])
                                   (ids := [id'; id']); auto.
           -- simpl_concatn. simpl in E1. exact E2.
           -- intros. inversion H15. 2: inversion H30.
              ++ simpl_concatn. replace (inl v2') with
                   (get_value (insert_value (insert_value env (inl A) v1') (inl B) v2') (inl B)).
                 apply eval_var. 
                 rewrite get_value_here. auto.
              ++ simpl_concatn. replace (inl v1') with
                   (get_value (insert_value (insert_value env (inl A) v1') (inl B) v2') (inl A)).
              rewrite H27. apply eval_var.
              rewrite get_value_there, get_value_here. auto. congruence.
              ++ inversion H32.
           -- rewrite <- H20 in H25. auto.
           -- simpl_concatn. reflexivity.
      - simpl_concatn_H H23. subst. inversion H15.
        rewrite H13 in *.
        apply length_zero_iff_nil in H18. subst.
        simpl_concatn_H H27.
        pose (WD := determinism H2 _ _ _ H27).
        destruct WD. destruct H14. inversion H12.
        inversion H13.
      - subst. inversion H7. rewrite H5 in *.
        apply length_zero_iff_nil in H9. subst.
        simpl_concatn_H H18.
        pose (WD := determinism H _ _ _ H18).
        destruct WD. inversion H4.
        inversion H5.
Qed.

End Equivalence_Proofs.