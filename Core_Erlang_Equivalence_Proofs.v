Load Core_Erlang_Proofs.

Module Core_Erlang_Equivalence_Proofs.

Import Core_Erlang_Syntax.
Import Core_Erlang_Semantics.
Import Core_Erlang_Environment.
Import Core_Erlang_Closures.
Import Core_Erlang_Helpers.
(* Import Core_Erlang_Induction. *)
Import Core_Erlang_Proofs.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.
Import Coq.Init.Logic.
Import Omega.


Example call_comm : forall e e' cl env t,
  |env, cl, ECall "plus"%string [e ; e']| -e> t <->
  |env, cl, ECall "plus"%string [e' ; e]| -e> t.
Proof.
  intros. split.
  (* List elements *)
  1-2: intros; inversion H; subst; simpl in H2; pose (element_exist Value 1 vals (eq_sym H2)); inversion e0; inversion H0; subst; simpl in H2; inversion H2; pose (element_exist Value 0 x0 (eq_sym H3)); inversion e1; inversion H1; subst; simpl in H2; inversion H2; apply eq_sym in H6; apply length_zero_iff_nil in H6; subst;
  (* equivalence *)
  apply eval_call with ([x1;x]).
    1, 4: reflexivity.
    1, 3: intros.
    { inversion H4.
        inversion H6. rewrite H8, H9 in *. apply H5. simpl. auto.
        
        inversion H6.
        inversion H7. rewrite H9, H10 in *. apply H5. simpl. auto.
        inversion H7.
      }
    2, 3 : apply plus_comm_basic.
    { inversion H4.
        inversion H6. rewrite H8, H9 in *. apply H5. simpl. auto.
        
        inversion H6.
        inversion H7. rewrite H9, H10 in *. apply H5. simpl. auto.
        inversion H7.
      }
Qed.


Example let_1_comm (e1 e2 : Expression) (t : Value) :
  |[], [], ELet ["X"%string] [e1] (ECall "plus"%string [EVar "X"%string ; e2])| -e> t <->
  |[], [], ELet ["X"%string] [e1] (ECall "plus"%string [e2 ; EVar "X"%string])| -e> t.
Proof.
  split; intros.
  * inversion H. subst. inversion H5. pose (element_exist Value 0 vals H5). inversion e. inversion H0. subst. inversion H5. apply length_zero_iff_nil in H3. subst.
  apply eval_let with (vals := [x]).
    - reflexivity.
    - intros. inversion H2. inversion H3. subst. apply H7. assumption. inversion H3.
    - apply call_comm. assumption.
  * inversion H. subst. inversion H5. pose (element_exist Value 0 vals H5). inversion e. inversion H0. subst. inversion H5. apply length_zero_iff_nil in H3. subst.
  apply eval_let with (vals := [x]).
    - reflexivity.
    - intros. inversion H2. inversion H3. subst. apply H7. assumption. inversion H3.
    - apply call_comm. assumption.
Qed.

Example call_comm_ex : forall e e' cl env t t',
  |env, cl, ECall "plus"%string [e ; e']| -e> t ->
  |env, cl, ECall "plus"%string [e' ; e]| -e> t' ->
  t = t'.
Proof.
  intros. apply call_comm in H. pose (determinism env cl (ECall "plus" [e' ; e]) t H t' H0). assumption.
Qed.


Example let_2_comm_concrete (e1 e2 : Expression) (t : Value) :
  |[], [], ELet ["X"%string] [ELiteral (Integer 5)] (ELet ["Y"%string] [ELiteral (Integer 6)] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]))| -e> t
<->
|[], [], ELet ["X"%string] [ELiteral (Integer 6)] (ELet ["Y"%string] [ELiteral (Integer 5)] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]))| -e> t
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
    pose (H11 (ELiteral (Integer 6)) x H2). inversion e3. reflexivity.
  }
  subst. simpl in *. inversion H12. subst.
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
      ** simpl append_vars_to_env.

      (* Call value list elements *)
      inversion H4. pose (element_exist Value 1 vals (eq_sym H3)). inversion e3. inversion H2. subst. inversion H3. pose (element_exist Value 0 x0 (eq_sym H10)). inversion e4. inversion H6. subst. inversion H3. apply eq_sym, length_zero_iff_nil in H15. subst.

      (* Back to the original goal *)
      assert (x = VLiteral (Integer 5) /\ x1 = VLiteral (Integer 6)).
      {
         assert (In ((EVar "X"%string), x) (combine [EVar "X"%string ; EVar "Y"%string] [x ; x1])). simpl. auto.
         assert (In ((EVar "Y"%string), x1) (combine [EVar "X"%string ; EVar "Y"%string] [x ; x1])). simpl. auto.
        pose (H13 (EVar "X"%string) x H14).
        pose (H13 (EVar "Y"%string) x1 H15).
        inversion e5. inversion e6. simpl. auto.
      }
      inversion H14. subst. simpl. reflexivity.
  * inversion H. subst. simpl in H5. pose (element_exist Value 0 vals H5). inversion e. inversion H0. subst. inversion H5. apply length_zero_iff_nil in H2. subst. assert (x = VLiteral (Integer 6)).
  {
    assert (In ((ELiteral (Integer 6)), x) (combine [ELiteral (Integer 6)] [x])). simpl. auto.
    pose (H7 (ELiteral (Integer 6)) x H1). inversion e0. reflexivity.
  }
  subst. simpl in *. inversion H8. subst.
  simpl in H9. pose (element_exist Value 0 vals H9). inversion e0. inversion H1. subst. inversion H9. apply length_zero_iff_nil in H3. subst. assert (x = VLiteral (Integer 5)).
  {
    assert (In ((ELiteral (Integer 5)), x) (combine [ELiteral (Integer 5)] [x])). simpl. auto.
    pose (H11 (ELiteral (Integer 5)) x H2). inversion e3. reflexivity.
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
        -- inversion H3; inversion H6. apply eval_var.
      ** simpl append_vars_to_env.

      (* Call value list elements *)
      inversion H4. pose (element_exist Value 1 vals (eq_sym H3)). inversion e3. inversion H2. subst. inversion H3. pose (element_exist Value 0 x0 (eq_sym H10)). inversion e4. inversion H6. subst. inversion H3. apply eq_sym, length_zero_iff_nil in H15. subst.

      (* Back to the original goal *)
      assert (x = VLiteral (Integer 6) /\ x1 = VLiteral (Integer 5)).
      {
         assert (In ((EVar "X"%string), x) (combine [EVar "X"%string ; EVar "Y"%string] [x ; x1])). simpl. auto.
         assert (In ((EVar "Y"%string), x1) (combine [EVar "X"%string ; EVar "Y"%string] [x ; x1])). simpl. auto.
        pose (H13 (EVar "X"%string) x H14).
        pose (H13 (EVar "Y"%string) x1 H15).
        inversion e5. inversion e6. simpl. auto.
      }
      inversion H14. subst. simpl. reflexivity.
Qed.

Example let_2_comm_concrete_alternate_proof (e1 e2 : Expression) (t : Value) :
  |[], [], ELet ["X"%string] [ELiteral (Integer 5)] (ELet ["Y"%string] [ELiteral (Integer 6)] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]))| -e> t
<->
|[], [], ELet ["X"%string] [ELiteral (Integer 6)] (ELet ["Y"%string] [ELiteral (Integer 5)] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]))| -e> t
.
Proof.
  split; intros.
  * (* let values *)
    assert (|[], [], ELet ["X"%string] [ELiteral (Integer 5)]
      (ELet ["Y"%string] [ELiteral (Integer 6)] (ECall "plus" [EVar "X"%string; EVar "Y"%string]))| -e>  VLiteral (Integer 11)).
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
    apply determinism with (v1 := VLiteral (Integer 11)) in H; subst.
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
    assert (|[], [], ELet ["X"%string] [ELiteral (Integer 6)]
      (ELet ["Y"%string] [ELiteral (Integer 5)] (ECall "plus" [EVar "X"%string; EVar "Y"%string]))| -e>  VLiteral (Integer 11)).
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
    apply determinism with (v1 := VLiteral (Integer 11)) in H; subst.
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

Example exp_to_fun env cl e t x:
|env, cl, e| -e> t
<->
|env, cl, ELet [x] [EFun [] e] (EApply (EVar x) [])| -e> t.
Proof.
  split; intros.
  * eapply eval_let with ([VClosure (inl env) [] e]).
    - reflexivity.
    - intros. inversion H0; inversion H1. apply eval_fun.
    - simpl. apply eval_apply with (vals := []) (var_list := []) (body := e) (ref := inl env).
      + reflexivity.
      + assert (get_value (insert_value env (inl x) (VClosure (inl env) [] e)) (inl x) = VClosure (inl env) [] e). { apply env_app_get. }
        rewrite <- H0 at 2. apply eval_var.
      + intros. inversion H0.
      + simpl. assumption.
  * inversion H. subst. simpl in H5. pose (element_exist Value 0 vals H5). inversion e0. inversion H0. subst. inversion H5. apply length_zero_iff_nil in H2. subst. assert (x0 = VClosure (inl env) [] e). { assert (In (EFun [] e, x0) (combine [EFun [] e] [x0])). { simpl. auto. } pose (H7 (EFun [] e) x0 H1). inversion e1. reflexivity. } subst. inversion H8. subst. apply eq_sym, length_zero_iff_nil in H3. inversion H4. subst. pose (env_app_get env (inl x) (VClosure (inl env) [] e)). rewrite e1 in H11. inversion H11. subst. simpl in H12. assumption.
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
Example let_2_comm (env: Environment) (cl : Closures) (e1 e2 : Expression) (t x x0 : Value) :
  |env, cl, e2| -e> x0 -> |append_vars_to_env ["X"%string] [x] env, cl, e2| -e> x0 ->
  |env, cl, e1| -e> x -> |append_vars_to_env ["X"%string] [x0] env, cl, e1| -e> x ->
  |env, cl, ELet ["X"%string] [e1] (ELet ["Y"%string] [e2] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]))| -e> t
->
|env, cl, ELet ["X"%string] [e2] (ELet ["Y"%string] [e1] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]))| -e> t
.
Proof.
  * intros. inversion H3. subst. simpl in H9. pose (element_exist Value 0 vals H9). inversion e. inversion H4. subst. inversion H9. apply length_zero_iff_nil in H6. subst. assert (x1 = x).
    {
      assert (In (e1, x1) (combine [e1] [x1])). simpl. auto.
      pose (H11 e1 x1 H5). pose (determinism env cl e1 x1 e0 x H1). assumption.
    }
    inversion H12. subst. simpl in H14. pose (element_exist Value 0 vals H14). inversion e0. inversion H5. subst. inversion H14. apply length_zero_iff_nil in H7. subst. assert (x1 = x0). 
    {
       assert (In (e2, x1) (combine [e2] [x1])). simpl. auto.
       pose (H16 e2 x1 H6). pose (determinism (append_vars_to_env ["X"%string] [x] env) cl e2 x1 e3 x0 H0). assumption.
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
       inversion H17. subst. simpl in H8. pose (element_exist Value 1 vals (eq_sym H8)). inversion e3. inversion H6. subst. inversion H8. pose (element_exist Value 0 x2 (eq_sym H10)). inversion e4. inversion H7. subst. inversion H10. apply eq_sym, length_zero_iff_nil in H18. subst.
       assert (x1 = x /\ x3 = x0).
       {
         assert (In (EVar "X"%string, x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). { simpl. auto. }
         
         assert (In (EVar "Y"%string, x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). { simpl. auto. }
         
         pose (H15 (EVar "X"%string) x1 H13).
         pose (H15 (EVar "Y"%string) x3 H18).
         inversion e5. inversion e6. simpl. split.
         * rewrite get_value_there. rewrite get_value_here.
           - reflexivity.
           - apply Y_neq_X. 
         * apply get_value_here.
       }
       inversion H13. rewrite H18, H19 in *.
       
       (* BACK TO CALL PROOF *)
       apply eval_call with (vals := [x0 ; x]).
       ** reflexivity.
       ** intros. simpl. inversion H20.
         -- inversion H21. subst. assert (get_value (insert_value (insert_value env (inl "X"%string) val) (inl "Y"%string) x) (inl "X"%string) = val). { rewrite get_value_there. apply get_value_here. apply Y_neq_X. } rewrite <- H18 at 2. apply eval_var.
         -- inversion H21; inversion H22. subst. assert (get_value (insert_value (insert_value env (inl "X"%string) x0) (inl "Y"%string) val) (inl "Y"%string) = val). { rewrite get_value_here. reflexivity. } rewrite <- H18 at 2. apply eval_var.
       ** apply plus_comm_basic.
Qed.

Example let_2_comm_eq (env: Environment) (cl : Closures) (e1 e2 : Expression) (t x x0 : Value) :
  |env, cl, e2| -e> x0 -> |append_vars_to_env ["X"%string] [x] env, cl, e2| -e> x0 ->
  |env, cl, e1| -e> x -> |append_vars_to_env ["X"%string] [x0] env, cl, e1| -e> x ->
  |env, cl, ELet ["X"%string] [e1] (ELet ["Y"%string] [e2] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]))| -e> t
<->
|env, cl, ELet ["X"%string] [e2] (ELet ["Y"%string] [e1] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]))| -e> t
.
Proof.
  split.
  * apply let_2_comm with (x := x) (x0 := x0); try (assumption).
  * apply let_2_comm with (x := x0) (x0 := x); try (assumption).
Qed.

Example let_1_comm_2_list (env: Environment) (cl : Closures) (e1 e2 : Expression) (t : Value) :
|env, cl, ELet ["X"%string; "Y"%string] [e1 ; e2] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string])| -e> t
->
|env, cl, ELet ["X"%string; "Y"%string] [e2 ; e1] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string])| -e> t.
Proof.
  intros.
  (* FROM LET HYPO *)
  inversion H. subst. simpl in H5. pose (element_exist Value 1 vals H5). inversion e. inversion H0. subst. inversion H5. pose (element_exist Value 0 x0 H2). inversion e0. inversion H1. subst. inversion H5. apply length_zero_iff_nil in H4. subst.
  (* FROM CALL HYPO *)
  inversion H8. subst. simpl in H6. pose (element_exist Value 1 vals (eq_sym H6)). inversion e3. inversion H3. subst. inversion H6. pose (element_exist Value 0 x2 (eq_sym H9)). inversion e4. inversion H4. subst. inversion H6. apply eq_sym, length_zero_iff_nil in H12. subst. assert (x = x0 /\ x3 = x1).
  {
    assert (In (EVar "X"%string, x0) (combine [EVar "X"%string; EVar "Y"%string] [x0; x3])). { simpl. auto. }
    assert (In (EVar "Y"%string, x3) (combine [EVar "X"%string; EVar "Y"%string] [x0; x3])). { simpl. auto. }
    pose (H11 (EVar "X"%string) x0 H10).
    pose (H11 (EVar "Y"%string) x3 H12).
    
    inversion e5. inversion e6. simpl. split.
    * rewrite get_value_there. rewrite get_value_here. reflexivity. apply Y_neq_X.
    * apply get_value_here.
  }
  inversion H10. subst.

  (* EVALUATING THE OTHER ONE *)
  apply eval_let with (vals := [x1; x0]).
  * reflexivity.
  * intros. inversion H12.
    - inversion H13. subst. apply H7. simpl. auto.
    - inversion H13; inversion H14. subst. apply H7. simpl. auto.
  * apply eval_call with (vals := [x1 ; x0]).
    - reflexivity.
    - intros. inversion H12.
      + inversion H13. simpl.
        assert (get_value (insert_value (insert_value env (inl "X"%string) val) (inl "Y"%string) x0) (inl "X"%string) = val). { rewrite get_value_there. apply get_value_here. apply Y_neq_X. } rewrite <- H14 at 2. apply eval_var.
      + inversion H13; inversion H14. 
        assert (get_value (insert_value (insert_value env (inl "X"%string) x1) (inl "Y"%string) val) (inl "Y"%string) = val). { rewrite get_value_here. reflexivity. } rewrite <- H15 at 2. apply eval_var.
    - apply plus_comm_basic.
Qed.

Example let_1_comm_2_list_eq (env: Environment) (cl : Closures) (e1 e2 : Expression) (t : Value) :
|env, cl, ELet ["X"%string; "Y"%string] [e1 ; e2] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string])| -e> t
<->
|env, cl, ELet ["X"%string; "Y"%string] [e2 ; e1] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string])| -e> t.
Proof.
  split; intros.
  * apply let_1_comm_2_list. assumption.
  * apply let_1_comm_2_list. assumption.
Qed.


End Core_Erlang_Equivalence_Proofs.