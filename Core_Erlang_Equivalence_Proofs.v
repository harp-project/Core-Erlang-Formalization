Load Core_Erlang_Proofs.

Module Core_Erlang_Equivalence_Proofs.

Import Core_Erlang_Syntax.
Import Core_Erlang_Semantics.
Import Core_Erlang_Environment.
Import Core_Erlang_Helpers.
Import Core_Erlang_Proofs.
Import Core_Erlang_Equalities.
Import Core_Erlang_Side_Effects.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.
Import Coq.Init.Logic.
Import Omega.

Example call_comm : forall e e' x1 x2 env t,
  |env, e, []| -e> |inl x1, []| ->
  |env, e', []| -e> |inl x2, []| ->
  |env, ECall "plus"%string [e ; e'], []| -e> |inl t, []| ->
  |env, ECall "plus"%string [e' ; e], []| -e> |inl t, []|.
Proof.
  intros. 
  (* List elements *)
   inversion H1; subst; simpl in H4; pose (EE1 := element_exist Value 1 vals (eq_sym H4)); inversion EE1; inversion H2; subst; inversion H4; pose (EE2 := element_exist Value 0 x0 (eq_sym H6)); inversion EE2; inversion H3; subst; simpl in H4; inversion H4; apply eq_sym, length_zero_iff_nil in H9; subst;
  pose (WD1 := weak_determinism _ H);
  pose (WD2 := weak_determinism _ H0);
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
  * rewrite plus_comm_basic. unfold concatn. simpl concat.
    inversion H5. 
    pose (EE3 := element_exist SideEffectList _ _ (eq_sym H18)). inversion EE3. inversion H16. subst. inversion H5.
    pose (EE4 := element_exist SideEffectList _ _ (eq_sym H20)). inversion EE4. inversion H19. subst. inversion H20. apply eq_sym, length_zero_iff_nil in H22. subst.
    inversion H13. rewrite app_nil_r in H22. assert (x0 = [] /\ x2 = []). 
    { destruct x0.
      * simpl in H22. auto.
      * inversion H22.
    }
    inversion H21. subst. assumption.
Qed.


Example let_1_comm (e1 e2 : Expression) (t x1 x2 : Value) :
  |[], e1, []| -e> |inl x1, []| ->
  | [(inl "X"%string, x1)], e2, []| -e> |inl x2, []| ->
  |[], ELet ["X"%string] [e1] (ECall "plus"%string [EVar "X"%string ; e2]), []| -e> |inl t, []| ->
  |[], ELet ["X"%string] [e1] (ECall "plus"%string [e2 ; EVar "X"%string]), []| -e> |inl t, []|.
Proof.
  * intros. inversion H1. subst. inversion H5. inversion H6.
    pose (EE1 := element_exist Value 0 vals H5). inversion EE1. inversion H2. subst. inversion H5. apply length_zero_iff_nil in H9. subst.
    pose (EE2 := element_exist _ 0 _ (eq_sym H6)). inversion EE2. inversion H7. subst. inversion H6. apply eq_sym, length_zero_iff_nil in H10. subst.
  eapply eval_let with (vals := [x]) (eff := [[]]) (eff2 := []); auto.
    - intros. inversion H9. 2: inversion H11.
      simpl. pose (P1 := H8 0 Nat.lt_0_1). unfold concatn in P1. simpl in P1.
      pose (WD1 := weak_determinism _ H). apply WD1 in P1 as P2. inversion P2. inversion H10. rewrite app_nil_r in H14. subst. exact P1.
    - unfold concatn. simpl. apply call_comm with (x1 := x) (x2 := x2).
      + apply eval_var.
      + pose (P1 := H8 0 Nat.lt_0_1). unfold concatn in P1. simpl in P1.
        pose (WD1 := weak_determinism _ H). apply WD1 in P1 as P2. inversion P2. inversion H9.  subst. assumption.
      + unfold concatn in H13. simpl in H13. 
        pose (P1 := H8 0 Nat.lt_0_1). unfold concatn in P1. simpl in P1.
        pose (WD1 := weak_determinism _ H). apply WD1 in P1 as P2. inversion P2. rewrite app_nil_r in H10. subst. assumption.
Qed.

Example call_comm_ex : forall e e' x1 x2 env t t',
  |env, e, []| -e> |inl x1, []| ->
  |env, e', []| -e> |inl x2, []| ->
  |env, ECall "plus"%string [e ; e'], []| -e> |inl t, []| ->
  |env, ECall "plus"%string [e' ; e], []| -e> |inl t', []| ->
  t = t'.
Proof.
  intros. pose (P := call_comm e e' x1 x2 env t H H0 H1). 
  pose (DET := weak_determinism _ P _ _ H2). inversion DET. inversion H3. reflexivity.
Qed.

Example let_2_comm_concrete_alternate_proof (t : Value + Exception) :
  |[], ELet ["X"%string] [ELiteral (Integer 5)] (ELet ["Y"%string] [ELiteral (Integer 6)] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string])), []| -e> |t, []|
<->
|[], ELet ["X"%string] [ELiteral (Integer 6)] (ELet ["Y"%string] [ELiteral (Integer 5)] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string])), []| -e> |t, []|
.
Proof.
  split; intros.
  * (* let values *)
    assert (|[], ELet ["X"%string] [ELiteral (Integer 5)]
      (ELet ["Y"%string] [ELiteral (Integer 6)] (ECall "plus" [EVar "X"%string; EVar "Y"%string])), []| -e> |inl (VLiteral (Integer 11)), []|).
    {
      eapply eval_let with (vals := [VLiteral (Integer 5)]) (eff := [[]]); auto.
      * intros. inversion H0; inversion H2. apply eval_lit.
      * reflexivity.
      * eapply eval_let with (vals := [VLiteral (Integer 6)]) (eff := [[]]); auto.
        - intros. inversion H0; inversion H2. apply eval_lit.
        - reflexivity.
        - eapply eval_call with (vals := [VLiteral (Integer 5); VLiteral (Integer 6)]) (eff := [[];[]]); auto.
          + intros. inversion H0; inversion H2; try(inversion H4); apply eval_var.
    }
    apply @weak_determinism with (v1 := inl (VLiteral (Integer 11))) (eff' := []) in H. inversion H. inversion H1. subst.
    {
      eapply eval_let with (vals := [VLiteral (Integer 6)]) (eff := [[]]); auto.
      * intros. inversion H1; inversion H5. apply eval_lit.
      * reflexivity.
      * eapply eval_let with (vals := [VLiteral (Integer 5)]) (eff := [[]]); auto.
        - intros. inversion H1; inversion H5. apply eval_lit.
        - reflexivity.
        - eapply eval_call with (vals := [VLiteral (Integer 6); VLiteral (Integer 5)]) (eff := [[];[]]); auto.
          + intros. inversion H1; inversion H5; try(inversion H7); apply eval_var.
    } assumption.
    
    
    (* Other way, basically the same*)
    * (* let values *)
    assert (|[], ELet ["X"%string] [ELiteral (Integer 6)]
      (ELet ["Y"%string] [ELiteral (Integer 5)] (ECall "plus" [EVar "X"%string; EVar "Y"%string])), []| -e>  |inl (VLiteral (Integer 11)), []|).
    {
      eapply eval_let with (vals := [VLiteral (Integer 6)]) (eff := [[]]); auto.
      * intros. inversion H0; inversion H2. apply eval_lit.
      * reflexivity.
      * eapply eval_let with (vals := [VLiteral (Integer 5)]) (eff := [[]]); auto.
        - intros. inversion H0; inversion H2. apply eval_lit.
        - reflexivity.
        - eapply eval_call with (vals := [VLiteral (Integer 6); VLiteral (Integer 5)]) (eff := [[];[]]); auto.
          + intros. inversion H0; inversion H2; try(inversion H4); apply eval_var.
    }
    apply @weak_determinism with (v1 := inl (VLiteral (Integer 11))) (eff' := []) in H. inversion H. inversion H1. subst.
    {
      eapply eval_let with (vals := [VLiteral (Integer 5)]) (eff := [[]]); auto.
      * intros. inversion H1; inversion H5. apply eval_lit.
      * reflexivity.
      * eapply eval_let with (vals := [VLiteral (Integer 6)]) (eff := [[]]); auto.
        - intros. inversion H1; inversion H5. apply eval_lit.
        - reflexivity.
        - eapply eval_call with (vals := [VLiteral (Integer 5); VLiteral (Integer 6)]) (eff := [[];[]]); auto.
          + intros. inversion H1; inversion H5; try(inversion H7); apply eval_var.
    } assumption.
Qed.

Example exp_to_fun env e t x eff':
|env, e, []| -e> |inl t, eff'|
<->
|env, ELet [x] [EFun [] e] (EApply (EVar x) []), []| -e> |inl t, eff'|.
Proof.
  split; intros.
  * eapply eval_let with (vals := [VClosure env [] [] e]) (eff := [[]]); auto.
    - intros. inversion H0; inversion H2. apply eval_fun.
    - reflexivity.
    - simpl. eapply eval_apply with (vals := []) (var_list := []) (body := e) (ref := env) (ext := []) (eff := []); auto.
      + assert (get_value (insert_value env (inl x) (VClosure env [] [] e)) (inl x) = inl (VClosure env [] [] e)). { apply env_app_get. }
        rewrite <- H0. apply eval_var.
      + intros. inversion H0.
      + simpl. reflexivity.
      + simpl. assumption.
  * inversion H. subst. simpl in H4. 
    pose (EE1 := element_exist Value 0 vals H3). inversion EE1. inversion H0. subst. inversion H3. apply length_zero_iff_nil in H2.
    pose (EE2 := element_exist _ _ _ (eq_sym H4)). inversion EE2. inversion H1. subst. inversion H4. apply eq_sym, length_zero_iff_nil in H5. subst.
    assert (x2 = []).
    {
      pose (P := H6 0 Nat.lt_0_1). unfold concatn in P. simpl in P. inversion P. rewrite app_nil_r in H12. auto.
    }
    assert (x0 = VClosure env [] [] e).
    {
      assert (In (EFun [] e, x0) (combine [EFun [] e] [x0])). { simpl. auto. } 
      pose (P1 := H6 0 Nat.lt_0_1). simpl in P1. inversion P1. reflexivity. 
    }
    subst. inversion H11. subst. simpl in H7.
    apply eq_sym, length_zero_iff_nil in H10. subst.
    apply eq_sym, length_zero_iff_nil in H7. subst.
    inversion H8. unfold concatn in H10. simpl in H10. subst.
    rewrite env_app_get in H13. inversion H13. subst. unfold concatn in H18. simpl in H18. assumption.
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

(* Additional hypotheses needed: see details at the admit statements *)
(* It would be sufficient the X and Y are new (fresh) variables *)
Example let_2_comm (env: Environment)(e1 e2 : Expression) (t x x0 : Value) eff eff1 eff2 :
  |env, e2, eff| -e> |inl x0, eff ++ eff2| -> |append_vars_to_env ["X"%string] [x] env, e2, eff ++ eff1| -e> |inl x0, eff ++ eff1 ++ eff2| ->
  |env, e1, eff| -e> |inl x, eff ++ eff1| -> |append_vars_to_env ["X"%string] [x0] env, e1, eff ++ eff2| -e> |inl x, eff ++ eff2 ++ eff1| ->
  |env, ELet ["X"%string] [e1] (ELet ["Y"%string] [e2] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string])), eff| -e> |inl t, eff ++ eff1 ++ eff2|
->
|env, ELet ["X"%string] [e2] (ELet ["Y"%string] [e1] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string])), eff| -e> |inl t, eff ++ eff2 ++ eff1|
.
Proof.
  * intros. inversion H3. subst. simpl in H8. pose (EE1 := element_exist Value 0 vals H7). inversion EE1 as [x']. inversion H4. subst. inversion H7. apply length_zero_iff_nil in H6. subst.
    pose (EE2 := element_exist _ 0 _ (eq_sym H8)). inversion EE2 as [eff1']. inversion H5. subst. inversion H8. apply eq_sym, length_zero_iff_nil in H9. subst.
    assert (x' = x /\ eff1' = eff1).
    {
      pose (P := H10 0 Nat.lt_0_1). unfold concatn in P. simpl in P. rewrite app_nil_r, app_nil_r in P.
      pose (WD := weak_determinism _ H1 _ _ P). inversion WD. inversion H6. apply app_inv_head in H9. subst. auto.
    }
    inversion H6. subst.
    inversion H15. subst. simpl in H13, H16.
    pose (EE3 := element_exist Value 0 vals H13). inversion EE3 as [x0']. inversion H9. subst. inversion H13. apply length_zero_iff_nil in H12. subst.
    pose (EE4 := element_exist _ _ _ (eq_sym H16)). inversion EE4 as [eff2']. inversion H11. subst. inversion H16. apply eq_sym, length_zero_iff_nil in H17. subst.
    assert (x0' = x0 /\ eff2' = eff2). 
    {
      pose (P := H18 0 Nat.lt_0_1). unfold concatn in P. simpl in P. rewrite app_nil_r, app_nil_r, app_nil_r in P.
      pose (WD := weak_determinism _ H0 _ _ P). inversion WD. inversion H12. rewrite app_assoc in H17. apply app_inv_head in H17. subst. auto.
    }
    inversion H12. subst.
   (*proving starts*)
   apply eval_let with (vals := [x0]) (eff := [eff2]) (eff2 := eff1); auto.
   - intros. inversion H17.
     + unfold concatn. simpl. rewrite app_nil_r, app_nil_r. assumption. (*hypo needed: ([],[],e2)-e>x0*) 
     + inversion H20.
   - unfold concatn. simpl. rewrite app_nil_r, app_assoc. auto.
   - apply eval_let with (vals := [x]) (eff := [eff1]) (eff2 := []); auto.
     + intros. inversion H17.
       ** subst. unfold concatn. simpl concat. simpl nth. rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc. assumption.
       ** inversion H20.
     + unfold concatn. simpl. rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc. auto.
   (* call information *)
     + inversion H23. subst. simpl in H20, H21.
       pose (EE5 := element_exist Value 1 vals (eq_sym H20)). inversion EE5 as [x']. inversion H17. subst. inversion H20.
       pose (EE6 := element_exist Value 0 x1 (eq_sym H24)). inversion EE6 as [x0']. inversion H19. subst. inversion H24. apply eq_sym, length_zero_iff_nil in H27. subst.
       pose (EE7 := element_exist _ _ _ (eq_sym H21)). inversion EE7 as [eff1']. inversion H26. subst. inversion H21.
       pose (EE8 := element_exist _ _ _ (eq_sym H28)). inversion EE8 as [eff2']. inversion H27. subst. inversion H28. apply eq_sym, length_zero_iff_nil in H31. subst.
       assert (x' = x /\ x0' = x0 /\ eff1' = [] /\ eff2' = []).
       {
         pose (P1 := H25 0 Nat.lt_0_2).
         pose (P2 := H25 1 Nat.lt_1_2).
         inversion P1. inversion P2. subst.
         
         unfold concatn in H35, H40. simpl in H35, H40.
         apply app_inv_head in H35. apply app_inv_head, app_inv_head in H40.
         rewrite app_nil_r in H35. rewrite app_nil_r in H40. subst.
         
         rewrite get_value_there in H34.
           - rewrite get_value_here in H34. inversion H34. rewrite get_value_here in H39. inversion H39. auto.
           - apply Y_neq_X.
       }
       inversion H30. inversion H32. inversion H34. subst.
       
       (* BACK TO CALL PROOF *)
       apply eval_call with (vals := [x0 ; x]) (eff := [[];[]]); auto.
       ** intros. inversion H31. 2: inversion H35. 3: inversion H37.
         -- simpl. assert (get_value (insert_value (insert_value env (inl "X"%string) x0) (inl "Y"%string) x) (inl "Y"%string) = inl x). { apply get_value_here. } rewrite <- H33. apply eval_var.
         -- simpl. subst. assert (get_value (insert_value (insert_value env (inl "X"%string) x0) (inl "Y"%string) x) (inl "X"%string) = inl x0). { rewrite get_value_there. apply get_value_here. exact Y_neq_X. } rewrite <- H33. apply eval_var.
       ** unfold concatn. simpl concat. rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc.
          unfold concatn in H29. simpl concat in H29. rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc in H29.
          apply (plus_comm_extended _ _ _ H29).
Qed.

Example let_2_comm_eq (env: Environment) (e1 e2 : Expression) (t x x0 : Value) :
  |env, e2| -e> inl x0 -> |append_vars_to_env ["X"%string] [x] env, e2| -e> inl x0 ->
  |env, e1| -e> inl x -> |append_vars_to_env ["X"%string] [x0] env, e1| -e> inl x ->
  |env, ELet ["X"%string] [e1] (ELet ["Y"%string] [e2] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]))| -e> inl t
<->
|env, ELet ["X"%string] [e2] (ELet ["Y"%string] [e1] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]))| -e> inl t
.
Proof.
  split.
  * apply let_2_comm with (x := x) (x0 := x0); try (assumption).
  * apply let_2_comm with (x := x0) (x0 := x); try (assumption).
Qed.

Example let_1_comm_2_list (env: Environment) (e1 e2 : Expression) (t : Value) :
|env, ELet ["X"%string; "Y"%string] [e1 ; e2] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string])| -e> inl t
->
|env, ELet ["X"%string; "Y"%string] [e2 ; e1] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string])| -e> inl t.
Proof.
  intros.
  (* FROM LET HYPO *)
  inversion H. subst. simpl in H4. pose (EE1 := element_exist Value 1 vals H4). inversion EE1. inversion H0. subst. inversion H4. pose (EE2 := element_exist Value 0 x0 H2). inversion EE2. inversion H1. subst. inversion H4. apply length_zero_iff_nil in H5. subst.
  (* FROM CALL HYPO *)
  inversion H7. subst. simpl in H8. pose (EE3 := element_exist Value 1 vals (eq_sym H8)). inversion EE3. inversion H3. subst. inversion H8. pose (EE4 := element_exist Value 0 x2 (eq_sym H9)). inversion EE4. inversion H5. subst. inversion H9. apply eq_sym, length_zero_iff_nil in H13. subst. assert (x = x0 /\ x3 = x1).
  {
    assert (In (EVar "X"%string, x0) (combine [EVar "X"%string; EVar "Y"%string] [x0; x3])). { simpl. auto. }
    assert (In (EVar "Y"%string, x3) (combine [EVar "X"%string; EVar "Y"%string] [x0; x3])). { simpl. auto. }
    pose (P1 := H10 (EVar "X"%string) x0 H11).
    pose (P2 := H10 (EVar "Y"%string) x3 H13).
    
    inversion P1. inversion P2. simpl. split.
    * rewrite get_value_there in H17. rewrite get_value_here in H17. inversion H17. reflexivity. apply Y_neq_X.
    * rewrite get_value_here in H20. inversion H20. reflexivity.
  }
  inversion H11. subst.

  (* EVALUATING THE OTHER ONE *)
  apply eval_let with (vals := [x1; x0]).
  * reflexivity.
  * intros. inversion H13.
    - inversion H14. subst. apply H6. simpl. auto.
    - inversion H14; inversion H15. subst. apply H6. simpl. auto.
  * apply eval_call with (vals := [x1 ; x0]).
    - reflexivity.
    - intros. inversion H13.
      + inversion H14. simpl.
        assert (get_value (insert_value (insert_value env (inl "X"%string) val) (inl "Y"%string) x0) (inl "X"%string) = inl val). { rewrite get_value_there. apply get_value_here. apply Y_neq_X. } rewrite <- H15. apply eval_var.
      + inversion H14; inversion H15.
        assert (get_value (insert_value (insert_value env (inl "X"%string) x1) (inl "Y"%string) val) (inl "Y"%string) = inl val). { rewrite get_value_here. reflexivity. } rewrite <- H16. apply eval_var.
    - rewrite <- H12. apply plus_comm_basic.
Qed.

Example let_1_comm_2_list_eq (env: Environment) (e1 e2 : Expression) (t : Value) :
|env, ELet ["X"%string; "Y"%string] [e1 ; e2] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string])| -e> inl t
<->
|env, ELet ["X"%string; "Y"%string] [e2 ; e1] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string])| -e> inl t.
Proof.
  split; intros.
  * apply let_1_comm_2_list. assumption.
  * apply let_1_comm_2_list. assumption.
Qed.


End Core_Erlang_Equivalence_Proofs.