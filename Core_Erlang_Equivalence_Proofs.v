Load Core_Erlang_Proofs.

Module Core_Erlang_Equivalence_Proofs.

Import Core_Erlang_Syntax.
Import Core_Erlang_Semantics.
Import Core_Erlang_Environment.
(* Import Core_Erlang_Closures. *)
Import Core_Erlang_Helpers.
Import Core_Erlang_Induction.
Import Core_Erlang_Proofs.
Import Core_Erlang_Equalities.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.
Import Coq.Init.Logic.
Import Omega.


Example call_comm : forall e e' env t,
  |env, ECall "plus"%string [e ; e']| -e> inl t <->
  |env, ECall "plus"%string [e' ; e]| -e> inl t.
Proof.
  intros. split.
  (* List elements *)
  1-2: intros; inversion H; subst; simpl in H2; pose (EE1 := element_exist Value 1 vals (eq_sym H2)); inversion EE1; inversion H0; subst; simpl in H2; inversion H2; pose (EE2 := element_exist Value 0 x0 (eq_sym H3)); inversion EE2; inversion H1; subst; simpl in H2; inversion H2; apply eq_sym in H6; apply eq_sym, length_zero_iff_nil in H7; subst;
  (* equivalence *)
  apply eval_call with ([x1;x]).
    1, 4: reflexivity.
    1, 3: intros.
    { inversion H5.
        inversion H7. rewrite H10, H9 in *. apply H4. simpl. auto.
        
        inversion H7.
        inversion H8. rewrite H11, H10 in *. apply H4. simpl. auto.
        inversion H8.
      }
    2, 3 : rewrite H6; apply plus_comm_basic.
    { inversion H5.
        inversion H7. rewrite H10, H9 in *. apply H4. simpl. auto.
        
        inversion H7.
        inversion H8. rewrite H11, H10 in *. apply H4. simpl. auto.
        inversion H8.
      }
Qed.


Example let_1_comm (e1 e2 : Expression) (t : Value) :
  |[], ELet ["X"%string] [e1] (ECall "plus"%string [EVar "X"%string ; e2])| -e> inl t <->
  |[], ELet ["X"%string] [e1] (ECall "plus"%string [e2 ; EVar "X"%string])| -e> inl t.
Proof.
  split; intros.
  * inversion H. subst. inversion H4. pose (EE1 := element_exist Value 0 vals H4). inversion EE1. inversion H0. subst. inversion H4. apply length_zero_iff_nil in H3. subst.
  apply eval_let with (vals := [x]).
    - reflexivity.
    - intros. inversion H2. inversion H3. subst. apply H6. assumption. inversion H3.
    - apply call_comm. assumption.
  * inversion H. subst. inversion H4. pose (EE1 := element_exist Value 0 vals H4). inversion EE1. inversion H0. subst. inversion H4. apply length_zero_iff_nil in H3. subst.
  apply eval_let with (vals := [x]).
    - reflexivity.
    - intros. inversion H2. inversion H3. subst. apply H6. assumption. inversion H3.
    - apply call_comm. assumption.
Qed.

Example call_comm_ex : forall e e' env t t',
  |env, ECall "plus"%string [e ; e']| -e> inl t ->
  |env, ECall "plus"%string [e' ; e]| -e> inl t' ->
  t = t'.
Proof.
  intros. apply call_comm in H. pose (DET := determinism H (inl t') H0). inversion DET. reflexivity.
Qed.

(* 
Example let_2_comm_concrete (t : Value) :
  |[], [], ELet ["X"%string] [ELiteral (Integer 5)] (ELet ["Y"%string] [ELiteral (Integer 6)] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]))| -e> inl t
<->
|[], [], ELet ["X"%string] [ELiteral (Integer 6)] (ELet ["Y"%string] [ELiteral (Integer 5)] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]))| -e> inl t
.
Proof.
  split; intros.
  (*let value lists elements*)
  * inversion H. subst. simpl in H5. pose (element_exist Value 0 vals H5). inversion e. inversion H0. subst. inversion H5. apply length_zero_iff_nil in H2. subst. assert (x = VLiteral (Integer 5)).
  {
    assert (In ((ELiteral (Integer 5)), x) (combine [ELiteral (Integer 5)] [x])). simpl. auto.
    pose (H7 (ELiteral (Integer 5)) x H1). inversion e0. reflexivity.
  }
  subst. simpl in *. inversion H8. subst.
  simpl in H9. pose (element_exist Value 0 vals H9). inversion e0. inversion H1. subst. inversion H9. apply length_zero_iff_nil in H3. subst. assert (x = VLiteral (Integer 6)).
  {
    assert (In ((ELiteral (Integer 6)), x) (combine [ELiteral (Integer 6)] [x])). simpl. auto.
    pose (H11 (ELiteral (Integer 6)) x H2). inversion e1. reflexivity.
  }
  subst. simpl in *. inversion H12. subst. simpl in H4. pose (element_exist Value 1 vals (eq_sym H4)). inversion e1. inversion H2. subst. inversion H4. pose (element_exist Value 0 x0 (eq_sym H6)). inversion e2. inversion H3. subst. inversion H4. apply eq_sym, length_zero_iff_nil in H14. subst. rewrite <- H15 in *. assert ().
  (* let evaluation *)
  apply eval_let with (vals := [VLiteral (Integer 6)]).
  - reflexivity.
  - intros. inversion H2; inversion H3. apply eval_lit.
  - apply eval_let with (vals := [VLiteral (Integer 5)]).
    + reflexivity.
    + intros. inversion H2; inversion H3. apply eval_lit.
    + apply eval_call with (vals := [VLiteral (Integer 6); VLiteral (Integer 5)]).
      ** reflexivity.
      ** intros. inversion H2.
        -- inversion H3. apply eval_var.
        -- inversion H3; inversion H6. apply eval_var.
      ** rewrite <- H15.

      (* Call value list elements *)
      inversion H12. pose (element_exist Value 1 vals (eq_sym H13)). inversion e1. inversion H18. subst. inversion H13. pose (element_exist Value 0 x0 (eq_sym H3)). inversion e2. inversion H2. subst. inversion H3. apply eq_sym, length_zero_iff_nil in H6. subst.

      (* Back to the original goal *)
      assert (x = VLiteral (Integer 5) /\ x1 = VLiteral (Integer 6)).
      {
         assert (In ((EVar "X"%string), x) (combine [EVar "X"%string ; EVar "Y"%string] [x ; x1])). simpl. auto.
         assert (In ((EVar "Y"%string), x1) (combine [EVar "X"%string ; EVar "Y"%string] [x ; x1])). simpl. auto.
        pose (H14 (EVar "X"%string) x H4).
        pose (H14 (EVar "Y"%string) x1 H6).
        inversion e3. inversion e4. simpl. auto.
      }
      inversion H4. subst. simpl. reflexivity.
  * inversion H. subst. simpl in H5. pose (element_exist Value 0 vals H5). inversion e. inversion H0. subst. inversion H5. apply length_zero_iff_nil in H2. subst. assert (x = VLiteral (Integer 6)).
  {
    assert (In ((ELiteral (Integer 6)), x) (combine [ELiteral (Integer 6)] [x])). simpl. auto.
    pose (H7 (ELiteral (Integer 6)) x H1). inversion e0. reflexivity.
  }
  subst. simpl in *. inversion H8. subst.
  simpl in H10. pose (element_exist Value 0 vals H10). inversion e0. inversion H1. subst. inversion H10. apply length_zero_iff_nil in H3. subst. assert (x = VLiteral (Integer 5)).
  {
    assert (In ((ELiteral (Integer 5)), x) (combine [ELiteral (Integer 5)] [x])). simpl. auto.
    pose (H11 (ELiteral (Integer 5)) x H2). inversion e1. reflexivity.
  }
  subst. simpl in *. inversion H12. subst.
  (* let evaluation *)
  apply eval_let with (vals := [VLiteral (Integer 5)]).
  - reflexivity.
  - intros. inversion H2; inversion H3. apply eval_lit.
  - apply eval_let with (vals := [VLiteral (Integer 6)]).
    + reflexivity.
    + intros. inversion H2; inversion H3. apply eval_lit.
    + apply eval_call with (vals := [VLiteral (Integer 5); VLiteral (Integer 6)]).
      ** reflexivity.
      ** intros. inversion H2.
        -- inversion H3. apply eval_var.
        -- inversion H3; inversion H4. apply eval_var.
      ** simpl append_vars_to_env.

      (* Call value list elements *)
      inversion H12. pose (element_exist Value 1 vals (eq_sym H13)). inversion e1. inversion H18. subst. inversion H13. pose (element_exist Value 0 x0 (eq_sym H3)). inversion e2. inversion H2. subst. inversion H3. apply eq_sym, length_zero_iff_nil in H6. subst.

      (* Back to the original goal *)
      assert (x = VLiteral (Integer 6) /\ x1 = VLiteral (Integer 5)).
      {
         assert (In ((EVar "X"%string), x) (combine [EVar "X"%string ; EVar "Y"%string] [x ; x1])). simpl. auto.
         assert (In ((EVar "Y"%string), x1) (combine [EVar "X"%string ; EVar "Y"%string] [x ; x1])). simpl. auto.
        pose (H14 (EVar "X"%string) x H4).
        pose (H14 (EVar "Y"%string) x1 H6).
        inversion e3. inversion e4. simpl. auto.
      }
      inversion H4. subst. simpl. reflexivity.
Qed.
 *)


Example let_2_comm_concrete_alternate_proof (t : Value + Exception) :
  |[], ELet ["X"%string] [ELiteral (Integer 5)] (ELet ["Y"%string] [ELiteral (Integer 6)] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]))| -e> t
<->
|[], ELet ["X"%string] [ELiteral (Integer 6)] (ELet ["Y"%string] [ELiteral (Integer 5)] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]))| -e> t
.
Proof.
  split; intros.
  * (* let values *)
    assert (|[], ELet ["X"%string] [ELiteral (Integer 5)]
      (ELet ["Y"%string] [ELiteral (Integer 6)] (ECall "plus" [EVar "X"%string; EVar "Y"%string]))| -e>  inl (VLiteral (Integer 11))).
    {
      apply eval_let with ([VLiteral (Integer 5)]).
      * reflexivity.
      * intros. inversion H0; inversion H1. apply eval_lit.
      * apply eval_let with ([VLiteral (Integer 6)]).
        - reflexivity.
        - intros. inversion H0; inversion H1. apply eval_lit.
        - apply eval_call with ([VLiteral (Integer 5); VLiteral (Integer 6)]).
          + reflexivity.
          + intros. inversion H0; inversion H1; try(inversion H2); apply eval_var.
          + simpl. reflexivity.
    }
    apply @determinism with (v1 := inl (VLiteral (Integer 11))) in H; subst.
    {
      apply eval_let with ([VLiteral (Integer 6)]).
      * reflexivity.
      * intros. inversion H; inversion H1. apply eval_lit.
      * apply eval_let with ([VLiteral (Integer 5)]).
        - reflexivity.
        - intros. inversion H; inversion H1. apply eval_lit.
        - apply eval_call with ([VLiteral (Integer 6); VLiteral (Integer 5)]).
          + reflexivity.
          + intros. inversion H; inversion H1; try(inversion H2); apply eval_var.
          + simpl. reflexivity.
    } assumption.
    
    
    (* Other way, basically the same*)
    * (* let values *)
    assert (|[], ELet ["X"%string] [ELiteral (Integer 6)]
      (ELet ["Y"%string] [ELiteral (Integer 5)] (ECall "plus" [EVar "X"%string; EVar "Y"%string]))| -e>  inl (VLiteral (Integer 11))).
    {
      apply eval_let with ([VLiteral (Integer 6)]).
      * reflexivity.
      * intros. inversion H0; inversion H1. apply eval_lit.
      * apply eval_let with ([VLiteral (Integer 5)]).
        - reflexivity.
        - intros. inversion H0; inversion H1. apply eval_lit.
        - apply eval_call with ([VLiteral (Integer 6); VLiteral (Integer 5)]).
          + reflexivity.
          + intros. inversion H0; inversion H1; try(inversion H2); apply eval_var.
          + simpl. reflexivity.
    }
    apply @determinism with (v1 := inl (VLiteral (Integer 11))) in H; subst.
    {
      apply eval_let with ([VLiteral (Integer 5)]).
      * reflexivity.
      * intros. inversion H; inversion H1. apply eval_lit.
      * apply eval_let with ([VLiteral (Integer 6)]).
        - reflexivity.
        - intros. inversion H; inversion H1. apply eval_lit.
        - apply eval_call with ([VLiteral (Integer 5); VLiteral (Integer 6)]).
          + reflexivity.
          + intros. inversion H; inversion H1; try(inversion H2); apply eval_var.
          + simpl. reflexivity.
    } assumption.
Qed.

Example exp_to_fun env e t x:
|env, e| -e> inl t
<->
|env, ELet [x] [EFun [] e] (EApply (EVar x) [])| -e> inl t.
Proof.
  split; intros.
  * eapply eval_let with (vals := [VClosure env [] [] e]).
    - reflexivity.
    - intros. inversion H0; inversion H1. apply eval_fun.
    - simpl. apply eval_apply with (vals := []) (var_list := []) (body := e) (ref := env) (ext := []).
      + reflexivity.
      + assert (get_value (insert_value env (inl x) (VClosure env [] [] e)) (inl x) = inl (VClosure env [] [] e)). { apply env_app_get. }
        rewrite <- H0. apply eval_var.
      + reflexivity.
      + intros. inversion H0.
      + simpl. assumption.
  * inversion H. subst. simpl in H4. pose (EE1 := element_exist Value 0 vals H4). inversion EE1. inversion H0. subst. inversion H4. apply length_zero_iff_nil in H2. subst. assert (x0 = VClosure env [] [] e). { assert (In (EFun [] e, x0) (combine [EFun [] e] [x0])). { simpl. auto. } pose (P1 := H6 (EFun [] e) x0 H1). inversion P1. reflexivity. } subst. inversion H7. subst. apply eq_sym, length_zero_iff_nil in H3. subst. inversion H5. rewrite env_app_get in H9. inversion H9. subst. simpl in H12. assumption.
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
Example let_2_comm (env: Environment)(e1 e2 : Expression) (t x x0 : Value) :
  |env, e2| -e> inl x0 -> |append_vars_to_env ["X"%string] [x] env, e2| -e> inl x0 ->
  |env, e1| -e> inl x -> |append_vars_to_env ["X"%string] [x0] env, e1| -e> inl x ->
  |env, ELet ["X"%string] [e1] (ELet ["Y"%string] [e2] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]))| -e> inl t
->
|env, ELet ["X"%string] [e2] (ELet ["Y"%string] [e1] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]))| -e> inl t
.
Proof.
  * intros. inversion H3. subst. simpl in H8. pose (EE1 := element_exist Value 0 vals H8). inversion EE1. inversion H4. subst. inversion H8. apply length_zero_iff_nil in H6. subst. assert (x1 = x).
    {
      assert (In (e1, x1) (combine [e1] [x1])). simpl. auto.
      pose (P1 := H10 e1 x1 H5). pose (DET := determinism P1 (inl x) H1). inversion DET. reflexivity.
    }
    inversion H11. subst. simpl in H13. pose (EE2 := element_exist Value 0 vals H13). inversion EE2. inversion H5. subst. inversion H13. apply length_zero_iff_nil in H7. subst. assert (x1 = x0). 
    {
       assert (In (e2, x1) (combine [e2] [x1])). simpl. auto.
       pose (P1 := H15 e2 x1 H6). pose (DET := determinism P1 (inl x0) H0). inversion DET. reflexivity.
    }
    subst.
   (*proving starts*)
   apply eval_let with (vals := [x0]).
   - reflexivity.
   - intros. inversion H6. 
     + inversion H7. subst. assumption. (*hypo needed: ([],[],e2)-e>x0*) 
     + inversion H7.
   - apply eval_let with (vals := [x]).
     + reflexivity.
     + intros. inversion H6.
       ** inversion H7. subst. assumption. (*hypo needed: ((append_vars_to_env ["X"%string] [x0] [],
append_vars_to_closure ["X"%string] [x0] [] [], e1) -e> x)*)
       ** inversion H7.
     + (* call information *)
       inversion H16. subst. simpl in H9. pose (EE3 := element_exist Value 1 vals (eq_sym H9)). inversion EE3. inversion H6. subst. inversion H9. pose (EE4 := element_exist Value 0 x2 (eq_sym H12)). inversion EE4. inversion H7. subst. inversion H12. apply eq_sym, length_zero_iff_nil in H19. subst.
       assert (x1 = x /\ x3 = x0).
       {
         assert (In (EVar "X"%string, x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). { simpl. auto. }
         
         assert (In (EVar "Y"%string, x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). { simpl. auto. }
         
         pose (P1 := H14 (EVar "X"%string) x1 H17).
         pose (P2 := H14 (EVar "Y"%string) x3 H19).
         inversion P1. inversion P2. simpl. split.
         * rewrite get_value_there in H23. rewrite get_value_here in H23.
           - inversion H23. reflexivity.
           - apply Y_neq_X. 
         * rewrite get_value_here in H26. inversion H26. reflexivity.
       }
       inversion H17. rewrite H19, H20 in *.
       
       (* BACK TO CALL PROOF *)
       apply eval_call with (vals := [x0 ; x]).
       ** reflexivity.
       ** intros. simpl. inversion H21.
         -- inversion H22. subst. assert (get_value (insert_value (insert_value env (inl "X"%string) val) (inl "Y"%string) x) (inl "X"%string) = inl val). { rewrite get_value_there. apply get_value_here. apply Y_neq_X. } rewrite <- H19. apply eval_var.
         -- inversion H22; inversion H23. subst. assert (get_value (insert_value (insert_value env (inl "X"%string) x0) (inl "Y"%string) val) (inl "Y"%string) = inl val). { rewrite get_value_here. reflexivity. } rewrite <- H19. apply eval_var.
       ** rewrite <- H18. apply plus_comm_basic.
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