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

Example call_comm : forall (e e' : Expression) (x1 x2 t : Value) (env : Environment),
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
Qed.


Example let_1_comm (e1 e2 : Expression) (t x1 x2 : Value) :
  |[], e1, []| -e> |inl x1, []| ->
  | [(inl "X"%string, x1)], e2, []| -e> |inl x2, []| ->
  |[], ELet [("X"%string, e1)] (ECall "plus"%string [EVar "X"%string ; e2]), []| -e> |inl t, []| ->
  |[], ELet [("X"%string, e1)] (ECall "plus"%string [e2 ; EVar "X"%string]), []| -e> |inl t, []|.
Proof.
  * intros. inversion H1. subst. inversion H5. inversion H4.
    pose (EE1 := element_exist Value 0 vals H7). inversion EE1. inversion H2. subst.
    inversion H4. apply eq_sym, length_zero_iff_nil in H10. subst.
    pose (EE2 := element_exist _ 0 _ H3). inversion EE2. inversion H9. subst.
    inversion H5. apply eq_sym, length_zero_iff_nil in H11. subst.
    eapply eval_let with (vals := [x]) (eff := [[]]) (eff2 := []); auto.
    - intros. inversion H10. 2: inversion H13.
      simpl. pose (P1 := H6 0 Nat.lt_0_1). unfold concatn in P1. simpl in P1.
      pose (WD1 := determinism _ H). apply WD1 in P1 as P2. inversion P2. inversion H11.
      rewrite app_nil_r in H14. subst. exact P1.
    - unfold concatn. simpl. apply call_comm with (x1 := x) (x2 := x2).
      + apply eval_var.
      + pose (P1 := H6 0 Nat.lt_0_1). unfold concatn in P1. simpl in P1.
        pose (WD1 := determinism _ H). apply WD1 in P1 as P2. inversion P2. inversion H10.
        subst. assumption.
      + unfold concatn in H12. simpl in H12. 
        pose (P1 := H6 0 Nat.lt_0_1). unfold concatn in P1. simpl in P1.
        pose (WD1 := determinism _ H). apply WD1 in P1 as P2. inversion P2.
        rewrite app_nil_r in H11. subst. assumption.
Qed.

Example call_comm_ex : forall (e e' : Expression) (x1 x2 : Value) (env : Environment) (t t' : Value),
  |env, e, []| -e> |inl x1, []| ->
  |env, e', []| -e> |inl x2, []| ->
  |env, ECall "plus"%string [e ; e'], []| -e> |inl t, []| ->
  |env, ECall "plus"%string [e' ; e], []| -e> |inl t', []| ->
  t = t'.
Proof.
  intros. pose (P := call_comm e e' x1 x2 t env H H0 H1). 
  pose (DET := determinism _ P _ _ H2). inversion DET. inversion H3. reflexivity.
Qed.

Example let_2_comm_concrete_alternate_proof (t : Value + Exception) :
  |[], ELet [("X"%string, ELiteral (Integer 5))] (ELet [("Y"%string, ELiteral (Integer 6))]
           (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string])), []| -e> |t, []|
<->
|[], ELet [("X"%string, ELiteral (Integer 6))] (ELet [("Y"%string, ELiteral (Integer 5))]
           (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string])), []| -e> |t, []|
.
Proof.
  split; intros.
  * (* let values *)
    assert (|[], ELet [("X"%string, ELiteral (Integer 5))]
      (ELet [("Y"%string, ELiteral (Integer 6))] (ECall "plus" [EVar "X"%string; EVar "Y"%string])), []|
      -e> |inl (VLiteral (Integer 11)), []|).
    {
      eapply eval_let with (vals := [VLiteral (Integer 5)]) (eff := [[]]); auto.
      * intros. inversion H0; inversion H2. apply eval_lit.
      * reflexivity.
      * eapply eval_let with (vals := [VLiteral (Integer 6)]) (eff := [[]]); auto.
        - intros. inversion H0; inversion H2. apply eval_lit.
        - reflexivity.
        - eapply eval_call with (vals := [VLiteral (Integer 5); VLiteral (Integer 6)])
                                (eff := [[];[]]); auto.
          + intros. inversion H0; inversion H2; try(inversion H4); apply eval_var.
    }
    apply @determinism with (v1 := inl (VLiteral (Integer 11))) (eff' := []) in H.
    inversion H. inversion H1. subst.
    {
      eapply eval_let with (vals := [VLiteral (Integer 6)]) (eff := [[]]); auto.
      * intros. inversion H1; inversion H5. apply eval_lit.
      * reflexivity.
      * eapply eval_let with (vals := [VLiteral (Integer 5)]) (eff := [[]]); auto.
        - intros. inversion H1; inversion H5. apply eval_lit.
        - reflexivity.
        - eapply eval_call with (vals := [VLiteral (Integer 6); VLiteral (Integer 5)])
                                (eff := [[];[]]); auto.
          + intros. inversion H1; inversion H5; try(inversion H7); apply eval_var.
    } assumption.
    
    
    (* Other way, basically the same*)
    * (* let values *)
    assert (|[], ELet [("X"%string, ELiteral (Integer 6))]
      (ELet [("Y"%string, ELiteral (Integer 5))] (ECall "plus" [EVar "X"%string; EVar "Y"%string])), []|
      -e>  |inl (VLiteral (Integer 11)), []|).
    {
      eapply eval_let with (vals := [VLiteral (Integer 6)]) (eff := [[]]); auto.
      * intros. inversion H0; inversion H2. apply eval_lit.
      * reflexivity.
      * eapply eval_let with (vals := [VLiteral (Integer 5)]) (eff := [[]]); auto.
        - intros. inversion H0; inversion H2. apply eval_lit.
        - reflexivity.
        - eapply eval_call with (vals := [VLiteral (Integer 6); VLiteral (Integer 5)])
                                (eff := [[];[]]); auto.
          + intros. inversion H0; inversion H2; try(inversion H4); apply eval_var.
    }
    apply @determinism with (v1 := inl (VLiteral (Integer 11))) (eff' := []) in H.
    inversion H. inversion H1. subst.
    {
      eapply eval_let with (vals := [VLiteral (Integer 5)]) (eff := [[]]); auto.
      * intros. inversion H1; inversion H5. apply eval_lit.
      * reflexivity.
      * eapply eval_let with (vals := [VLiteral (Integer 6)]) (eff := [[]]); auto.
        - intros. inversion H1; inversion H5. apply eval_lit.
        - reflexivity.
        - eapply eval_call with (vals := [VLiteral (Integer 5); VLiteral (Integer 6)])
                                (eff := [[];[]]); auto.
          + intros. inversion H1; inversion H5; try(inversion H7); apply eval_var.
    } assumption.
Qed.

Example exp_to_fun (env : Environment) (e : Expression) (t : Value + Exception) (x : Var) 
    (eff eff' : SideEffectList):
|env, e, eff| -e> |t, eff ++ eff'|
<->
|env, ELet [(x, EFun [] e)] (EApply (EVar x) []), eff| -e> |t, eff ++ eff'|.
Proof.
  split; intros.
  * apply eval_let with (vals := [VClosure env [] [] e]) (eff := [[]]) (eff2 := eff'); auto.
    - intros. inversion H0; inversion H2. apply eval_fun.
    - unfold concatn. simpl. rewrite app_nil_r. reflexivity.
    - simpl. eapply eval_apply with (vals := []) (var_list := []) (body := e) (ref := env)
                                    (ext := []) (eff := []) (eff2 := []) (eff3 := eff'); auto.
      + assert (get_value (insert_value env (inl x) (VClosure env [] [] e)) (inl x) 
                = inl (VClosure env [] [] e)). { apply get_value_here. }
        rewrite <- H0. unfold concatn. simpl. simpl_app. apply eval_var.
      + intros. inversion H0.
      + simpl. unfold concatn. simpl. repeat(rewrite app_nil_r). reflexivity.
      + unfold concatn. simpl. repeat(rewrite app_nil_r). assumption.
  * inversion H.
    - pose (EE1 := element_exist Value 0 vals H2). inversion EE1. inversion H11. subst.
      inversion H2. apply eq_sym, length_zero_iff_nil in H1.
      pose (EE2 := element_exist _ _ _ H3). inversion EE2. inversion H0. subst. inversion H3.
      apply eq_sym, length_zero_iff_nil in H5. subst.
      assert (x2 = []).
      {
        pose (P := H4 0 Nat.lt_0_1). unfold concatn in P. simpl in P. inversion P.
        rewrite app_nil_r, app_nil_r in H13. rewrite <- app_nil_r in H13 at 1.
        apply app_inv_head in H13. auto.
      }
      assert (x0 = VClosure env [] [] e).
      {
        assert (In (EFun [] e, x0) (combine [EFun [] e] [x0])). { simpl. auto. } 
        pose (P1 := H4 0 Nat.lt_0_1). simpl in P1. inversion P1. reflexivity. 
      }
      subst. inversion H10.
      + subst. simpl in H19.
        apply eq_sym, length_zero_iff_nil in H12. subst.
        apply eq_sym, length_zero_iff_nil in H7. subst.
        apply length_zero_iff_nil in H9. subst.
        unfold concatn in H8. simpl in H8. inversion H8.
        unfold concatn in H14. simpl in H14.
        rewrite app_nil_r in H14, H5.
        rewrite <- app_nil_r in H14 at 1. apply app_inv_head in H14. subst.
        unfold concatn in H15. simpl in H15.
        simpl_app_H H15. apply app_inv_head in H15. subst.
        inversion H8. rewrite get_value_here in H14. inversion H14. subst.
        simpl_concatn_H H19. assumption.
      + subst. inversion H14. rewrite get_value_here in H12. inversion H12.
      + subst. inversion H8.
      + subst. inversion H9. rewrite get_value_here in H16. inversion H16. subst.
        pose (P := H14 env [] [] e). congruence.
      + subst. inversion H9. rewrite get_value_here in H16. inversion H16. subst.
        rewrite <- H7 in H14. contradiction.
    - simpl in H4. inversion H3.
      + subst. simpl in H13. rewrite H13 in H11. inversion H11.
      + inversion H13.
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
Example let_2_comm (env: Environment)(e1 e2 : Expression) (t x x0 : Value) 
    (eff eff1 eff2 : SideEffectList) (A B : Var) (VarHyp : A <> B) :
  |env, e2, eff| -e> |inl x0, eff ++ eff2| -> 
  |append_vars_to_env [A] [x] env, e2, eff ++ eff1| -e> |inl x0, eff ++ eff1 ++ eff2| ->
  |env, e1, eff| -e> |inl x, eff ++ eff1| -> 
  |append_vars_to_env [A] [x0] env, e1, eff ++ eff2| -e> |inl x, eff ++ eff2 ++ eff1| ->
  |env, ELet [(A, e1)] (ELet [(B, e2)] 
        (ECall "plus"%string [EVar A ; EVar B])), eff| -e> |inl t, eff ++ eff1 ++ eff2|
->
|env, ELet [(A, e2)] (ELet [(B, e1)]
        (ECall "plus"%string [EVar A ; EVar B])), eff| -e> |inl t, eff ++ eff2 ++ eff1|
.
Proof.
  * intros. inversion H3. subst. pose (EE1 := element_exist Value 0 vals H6). inversion EE1 as [x']. inversion H4. subst. inversion H6. apply eq_sym, length_zero_iff_nil in H9. subst.
    pose (EE2 := element_exist _ 0 _ H7). inversion EE2 as [eff1']. inversion H5. subst. inversion H7. apply eq_sym, length_zero_iff_nil in H11. subst.
    assert (x' = x /\ eff1' = eff1).
    {
      pose (P := H8 0 Nat.lt_0_1). unfold concatn in P. simpl in P. rewrite app_nil_r, app_nil_r in P.
      pose (WD := determinism _ H1 _ _ P). inversion WD. inversion H9. apply app_inv_head in H11.
      subst. auto.
    }
    inversion H9. subst.
    inversion H14. subst.
    pose (EE3 := element_exist Value 0 vals H13). inversion EE3 as [x0']. inversion H11.
    subst. inversion H13. apply eq_sym, length_zero_iff_nil in H17. subst.
    pose (EE4 := element_exist _ _ _ H15). inversion EE4 as [eff2']. inversion H12. subst.
    inversion H15. apply eq_sym, length_zero_iff_nil in H19. subst.
    assert (x0' = x0 /\ eff2' = eff2). 
    {
      pose (P := H16 0 Nat.lt_0_1). unfold concatn in P. simpl in P.
      rewrite app_nil_r, app_nil_r, app_nil_r in P.
      pose (WD := determinism _ H0 _ _ P). inversion WD. inversion H17.
      rewrite app_assoc in H19. apply app_inv_head in H19. subst. auto.
    }
    inversion H17. subst.
   (* proving starts *)
   apply eval_let with (vals := [x0]) (eff := [eff2]) (eff2 := eff1); auto.
   - intros. inversion H19.
     + unfold concatn. simpl. rewrite app_nil_r, app_nil_r. assumption.
     + inversion H21.
   - unfold concatn. simpl. rewrite app_nil_r, app_assoc. auto.
   - apply eval_let with (vals := [x]) (eff := [eff1]) (eff2 := []); auto.
     + intros. inversion H19.
       ** subst. unfold concatn. simpl concat. simpl nth.
       rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc. assumption.
       ** inversion H21.
     + unfold concatn. simpl. rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc. auto.
   (* call information *)
     + inversion H22. subst.
       pose (EE5 := element_exist Value 1 vals H21). inversion EE5 as [x'].
       inversion H19. subst. inversion H21.
       pose (EE6 := element_exist Value 0 x1 H24). inversion EE6 as [x0'].
       inversion H20. subst. inversion H24. apply eq_sym, length_zero_iff_nil in H27. subst.
       pose (EE7 := element_exist _ _ _ H23). inversion EE7 as [eff1'].
       inversion H26. subst. inversion H23.
       pose (EE8 := element_exist _ _ _ H28). inversion EE8 as [eff2'].
       inversion H27. subst. inversion H28. apply eq_sym, length_zero_iff_nil in H31. subst.
       assert (x' = x /\ x0' = x0 /\ eff1' = [] /\ eff2' = []).
       {
         pose (P1 := H25 0 Nat.lt_0_2).
         pose (P2 := H25 1 Nat.lt_1_2).
         inversion P1. inversion P2. subst.
         
         unfold concatn in H35, H40. simpl in H35, H40.
         apply app_inv_head in H35. apply app_inv_head, app_inv_head in H40.
         rewrite app_nil_r in H35. rewrite app_nil_r in H40. subst.
         
         rewrite get_value_there in H34.
           - rewrite get_value_here in H34. inversion H34.
             rewrite get_value_here in H39. inversion H39. auto.
           - unfold not. intros. inversion H30. congruence.
       }
       inversion H30. inversion H32. inversion H34. subst.
       
       (* BACK TO CALL PROOF *)
       apply eval_call with (vals := [x0 ; x]) (eff := [[];[]]); auto.
       ** intros. inversion H31. 2: inversion H35. 3: inversion H37.
         -- simpl. assert (get_value (insert_value (insert_value env (inl A) x0) 
                                     (inl B) x) (inl B) = inl x). 
                                     { apply get_value_here. }
            rewrite <- H33. apply eval_var.
         -- simpl. subst. assert (get_value (insert_value (insert_value env (inl A) x0) 
                                           (inl B) x) (inl A) = inl x0).
                                           { rewrite get_value_there. apply get_value_here.
                                             unfold not. intros. inversion H33.
                                             congruence. }
            rewrite <- H33. apply eval_var.
       ** unfold concatn. simpl concat. rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc.
          unfold concatn in H29. simpl concat in H29.
          rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc in H29.
          apply plus_comm_basic_value with (eff0 := eff ++ eff1 ++ eff2). assumption.
Qed.

Example let_2_comm_eq (env: Environment) (e1 e2 : Expression) (t x x0 : Value) 
    (eff eff1 eff2 : SideEffectList) (A B : Var) (VarHyp : A <> B):
  |env, e2, eff| -e> |inl x0, eff ++ eff2| -> 
  |append_vars_to_env [A] [x] env, e2, eff ++ eff1| -e> |inl x0, eff ++ eff1 ++ eff2| ->
  |env, e1, eff| -e> |inl x, eff ++ eff1| -> 
  |append_vars_to_env [A] [x0] env, e1, eff ++ eff2| -e> |inl x, eff ++ eff2 ++ eff1| ->
  |env, ELet [(A, e1)]
      (ELet [(B, e2)] (ECall "plus"%string [EVar A ; EVar B])), eff| -e> |inl t, eff ++ eff1 ++ eff2|
<->
  |env, ELet [(A, e2)]
      (ELet [(B, e1)] (ECall "plus"%string [EVar A ; EVar B])), eff| -e> |inl t, eff ++ eff2 ++ eff1|
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

Example let_1_comm_2_list (env: Environment) (e1 e2 : Expression) (t t' v1 v2 : Value) 
   (eff eff1 eff2 : SideEffectList) (A B : Var) (VarHyp : A <> B)
(Hypo1 : |env, e1, eff| -e> |inl v1, eff ++ eff1|)
(Hypo2 : |env, e1, eff ++ eff2| -e> |inl v1, eff ++ eff2 ++ eff1|)
(Hypo1' : |env, e2, eff| -e> |inl v2, eff ++ eff2|)
(Hypo2' : |env, e2, eff ++ eff1| -e> |inl v2, eff ++ eff1 ++ eff2|) :
|env, ELet [(A, e1); (B, e2)]
     (ECall "plus"%string [EVar A ; EVar B]), eff| -e> |inl t, eff ++ eff1 ++ eff2|
->
|env, ELet [(A, e2); (B, e1)]
     (ECall "plus"%string [EVar A ; EVar B]), eff| -e> |inl t', eff ++ eff2 ++ eff1|
->
t = t'.
Proof.
  intros.
  (* FROM LET HYPO1 *)
  inversion H. subst.
  pose (EE1 := element_exist Value 1 vals H3). inversion EE1 as [v1']. inversion H1. subst. inversion H3.
  pose (EE2 := element_exist Value 0 x H6). inversion EE2 as [v2']. inversion H2. subst. inversion H6.
  apply eq_sym, length_zero_iff_nil in H9. subst.
  pose (EE3 := element_exist _ _ _ H4). inversion EE3 as [eff1']. inversion H8. subst. inversion H4.
  pose (EE4 := element_exist _ _ _ H10). inversion EE4 as [eff2']. inversion H9. subst. inversion H10.
  apply eq_sym, length_zero_iff_nil in H13. subst.
  (* FROM LET HYPO2 *)
  inversion H0. subst.
  pose (EE1' := element_exist _ _ _ H14). inversion EE1' as [v2'']. inversion H12. subst. inversion H14.
  pose (EE2' := element_exist _ _ _ H17). inversion EE2' as [v1'']. inversion H13. subst. inversion H17.
  apply eq_sym, length_zero_iff_nil in H20. subst.
  pose (EE3' := element_exist _ _ _ H15). inversion EE3' as [eff2'']. inversion H19. subst. inversion H15.
  pose (EE4' := element_exist _ _ _ H21). inversion EE4' as [eff1'']. inversion H20. subst. inversion H21.
  apply eq_sym, length_zero_iff_nil in H24. subst.

  assert (v1' = v1 /\ eff1' = eff1).
  {
    pose (P1 := H5 0 Nat.lt_0_2).
    unfold concatn in P1. simpl in P1. rewrite app_nil_r, app_nil_r in P1.
    pose (WD1 := determinism _ Hypo1).
    pose (PC1 := WD1 _ _ P1).
    inversion PC1. inversion H23. apply app_inv_head in H24. subst. auto.
  }
  inversion H23. subst.
  
  assert (v2'' = v2 /\ eff2'' = eff2).
  {
    pose (P1 := H16 0 Nat.lt_0_2).
    unfold concatn in P1. simpl in P1. rewrite app_nil_r, app_nil_r in P1.
    pose (WD1 := determinism _ Hypo1').
    pose (PC1 := WD1 _ _ P1).
    inversion PC1. inversion H24. apply app_inv_head in H25. subst. auto.
  }
  inversion H24. subst.
  assert (v1'' = v1 /\ v2' = v2 /\ eff1'' = eff1 /\ eff2' = eff2).
  {
    pose (P1 := H16 1 Nat.lt_1_2).
    unfold concatn in P1. simpl in P1. rewrite app_nil_r, app_nil_r in P1.
    pose (WD1 := determinism _ Hypo2).
    pose (PC1 := WD1 _ _ P1).
    inversion PC1. inversion H25. apply app_inv_head, app_inv_head in H26. subst.
    pose (P2 := H5 1 Nat.lt_1_2).
    unfold concatn in P2. simpl in P2. rewrite app_nil_r, app_nil_r in P2.
    pose (WD2 := determinism _ Hypo2').
    pose (PC2 := WD2 _ _ P2).
    inversion PC2. inversion H26. apply app_inv_head, app_inv_head in H27. subst. auto.
  }
  inversion H25. inversion H27. inversion H29. subst.
  (* FROM CALL HYPOS *)
 (* FROM CALL HYPO1 *)
  inversion H11. subst.
  pose (EC1 := element_exist _ _ _ H30). inversion EC1 as [v1']. inversion H26. subst. inversion H30.
  pose (EC2 := element_exist _ _ _ H32). inversion EC2 as [v2']. inversion H28. subst. inversion H30.
  apply eq_sym, length_zero_iff_nil in H35. subst.
  pose (EC3 := element_exist _ _ _ H31). inversion EC3 as [eff1']. inversion H34. subst. inversion H31.
  pose (EC4 := element_exist _ _ _ H36). inversion EC4 as [eff2']. inversion H35. subst. inversion H36.
  apply eq_sym, length_zero_iff_nil in H39. subst.
  (* FROM CALL HYPO2 *)
  inversion H22. subst.
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

Example let_2_binding_swap (env: Environment)(e1 e2 : Expression) (t x x0 : Value) 
    (eff eff1 eff2 : SideEffectList) (A B : Var) (VarHyp : A <> B) :
  |env, e2, eff| -e> |inl x0, eff ++ eff2| -> 
  |append_vars_to_env [A] [x] env, e2, eff ++ eff1| -e> |inl x0, eff ++ eff1 ++ eff2| ->
  |env, e1, eff| -e> |inl x, eff ++ eff1| -> 
  |append_vars_to_env [B] [x0] env, e1, eff ++ eff2| -e> |inl x, eff ++ eff2 ++ eff1| ->
  |env, ELet [(A, e1)] (ELet [(B, e2)] 
        (ECall "plus"%string [EVar A ; EVar B])), eff| -e> |inl t, eff ++ eff1 ++ eff2|
<->
|env, ELet [(B, e2)] (ELet [(A, e1)]
        (ECall "plus"%string [EVar A ; EVar B])), eff| -e> |inl t, eff ++ eff2 ++ eff1|
.
Proof.
  split.
  * intros. inversion H3. subst. pose (EE1 := element_exist Value 0 vals H6). inversion EE1 as [x']. inversion H4. subst. inversion H6. apply eq_sym, length_zero_iff_nil in H9. subst.
    pose (EE2 := element_exist _ 0 _ H7). inversion EE2 as [eff1']. inversion H5. subst. inversion H7. apply eq_sym, length_zero_iff_nil in H11. subst.
    assert (x' = x /\ eff1' = eff1).
    {
      pose (P := H8 0 Nat.lt_0_1). unfold concatn in P. simpl in P. rewrite app_nil_r, app_nil_r in P.
      pose (WD := determinism _ H1 _ _ P). inversion WD. inversion H9. apply app_inv_head in H11.
      subst. auto.
    }
    inversion H9. subst.
    inversion H14. subst. simpl in H13, H15.
    pose (EE3 := element_exist Value 0 vals H13). inversion EE3 as [x0']. inversion H11.
    subst. inversion H13. apply eq_sym, length_zero_iff_nil in H17. subst.
    pose (EE4 := element_exist _ _ _ H15). inversion EE4 as [eff2']. inversion H12. subst.
    inversion H15. apply eq_sym, length_zero_iff_nil in H19. subst.
    assert (x0' = x0 /\ eff2' = eff2). 
    {
      pose (P := H16 0 Nat.lt_0_1). unfold concatn in P. simpl in P.
      rewrite app_nil_r, app_nil_r, app_nil_r in P.
      pose (WD := determinism _ H0 _ _ P). inversion WD. inversion H17.
      rewrite app_assoc in H19. apply app_inv_head in H19. subst. auto.
    }
    inversion H17. subst.
   (*proving starts*)
   apply eval_let with (vals := [x0]) (eff := [eff2]) (eff2 := eff1); auto.
   - intros. inversion H19.
     + unfold concatn. simpl. rewrite app_nil_r, app_nil_r. assumption.
     + inversion H21.
   - unfold concatn. simpl. rewrite app_nil_r, app_assoc. auto.
   - apply eval_let with (vals := [x]) (eff := [eff1]) (eff2 := []); auto.
     + intros. inversion H19.
       ** subst. unfold concatn. simpl concat. simpl nth.
       rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc. assumption.
       ** inversion H21.
     + unfold concatn. simpl. rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc. auto.
   (* call information *)
     + inversion H22. subst. simpl in H23, H21.
       pose (EE5 := element_exist Value 1 vals H21). inversion EE5 as [x'].
       inversion H19. subst. inversion H21.
       pose (EE6 := element_exist Value 0 x1 H24). inversion EE6 as [x0'].
       inversion H20. subst. inversion H24. apply eq_sym, length_zero_iff_nil in H27. subst.
       pose (EE7 := element_exist _ _ _ H23). inversion EE7 as [eff1'].
       inversion H26. subst. inversion H23.
       pose (EE8 := element_exist _ _ _ H28). inversion EE8 as [eff2'].
       inversion H27. subst. inversion H28. apply eq_sym, length_zero_iff_nil in H31. subst.
       assert (x' = x /\ x0' = x0 /\ eff1' = [] /\ eff2' = []).
       {
         pose (P1 := H25 0 Nat.lt_0_2).
         pose (P2 := H25 1 Nat.lt_1_2).
         inversion P1. inversion P2. subst.
         
         unfold concatn in H35, H40. simpl in H35, H40.
         apply app_inv_head in H35. apply app_inv_head, app_inv_head in H40.
         rewrite app_nil_r in H35. rewrite app_nil_r in H40. subst.
         
         rewrite get_value_there in H34.
           - rewrite get_value_here in H34. inversion H34.
             rewrite get_value_here in H39. inversion H39. auto.
           - unfold not. intros. inversion H30. congruence.
       }
       inversion H30. inversion H32. inversion H34. subst.
       
       (* BACK TO CALL PROOF *)
       apply eval_call with (vals := [x ; x0]) (eff := [[];[]]); auto.
       ** intros. inversion H31. 2: inversion H35. 3: inversion H37.
         -- unfold concatn. simpl. assert (get_value (insert_value (insert_value env (inl B) x0) 
                                     (inl A) x) (inl B) = inl x0). 
                                     { rewrite get_value_there. apply get_value_here. congruence. }
            rewrite <- H33. apply eval_var.
         -- simpl. subst. assert (get_value (insert_value (insert_value env (inl B) x0) 
                                           (inl A) x) (inl A) = inl x).
                                           {  apply get_value_here. }
            rewrite <- H33. apply eval_var.
       ** unfold concatn. simpl concat. rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc.
          unfold concatn in H29. simpl concat in H29.
          rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc in H29.
          apply plus_effect_changeable with (eff ++ eff1 ++ eff2). assumption.
  * intros. inversion H3. subst. pose (EE1 := element_exist Value 0 vals H6). inversion EE1 as [x0']. inversion H4. subst. inversion H6. apply eq_sym, length_zero_iff_nil in H9. subst.
    pose (EE2 := element_exist _ 0 _ H7). inversion EE2 as [eff2']. inversion H5. subst. inversion H7. apply eq_sym, length_zero_iff_nil in H11. subst.
    assert (x0' = x0 /\ eff2' = eff2).
    {
      pose (P := H8 0 Nat.lt_0_1). unfold concatn in P. simpl in P. rewrite app_nil_r, app_nil_r in P.
      pose (WD := determinism _ H _ _ P). inversion WD. inversion H9. apply app_inv_head in H11.
      subst. auto.
    }
    inversion H9. subst.
    inversion H14. subst. simpl in H13, H15.
    pose (EE3 := element_exist Value 0 vals H13). inversion EE3 as [x']. inversion H11.
    subst. inversion H13. apply eq_sym, length_zero_iff_nil in H17. subst.
    pose (EE4 := element_exist _ _ _ H15). inversion EE4 as [eff1']. inversion H12. subst.
    inversion H15. apply eq_sym, length_zero_iff_nil in H19. subst.
    assert (x' = x /\ eff1' = eff1). 
    {
      pose (P := H16 0 Nat.lt_0_1). unfold concatn in P. simpl in P.
      rewrite app_nil_r, app_nil_r, app_nil_r in P.
      pose (WD := determinism _ H2 _ _ P). inversion WD. inversion H17.
      rewrite app_assoc in H19. apply app_inv_head in H19. subst. auto.
    }
    inversion H17. subst.
   (*proving starts*)
   apply eval_let with (vals := [x]) (eff := [eff1]) (eff2 := eff2); auto.
   - intros. inversion H19.
     + unfold concatn. simpl. rewrite app_nil_r, app_nil_r. assumption.
     + inversion H21.
   - unfold concatn. simpl. rewrite app_nil_r, app_assoc. auto.
   - apply eval_let with (vals := [x0]) (eff := [eff2]) (eff2 := []); auto.
     + intros. inversion H19.
       ** subst. unfold concatn. simpl concat. simpl nth.
       rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc. assumption.
       ** inversion H21.
     + unfold concatn. simpl. rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc. auto.
   (* call information *)
     + inversion H22. subst. simpl in H23, H21.
       pose (EE5 := element_exist Value 1 vals H21). inversion EE5 as [x'].
       inversion H19. subst. inversion H21.
       pose (EE6 := element_exist Value 0 x1 H24). inversion EE6 as [x0'].
       inversion H20. subst. inversion H24. apply eq_sym, length_zero_iff_nil in H27. subst.
       pose (EE7 := element_exist _ _ _ H23). inversion EE7 as [eff1'].
       inversion H26. subst. inversion H23.
       pose (EE8 := element_exist _ _ _ H28). inversion EE8 as [eff2'].
       inversion H27. subst. inversion H28. apply eq_sym, length_zero_iff_nil in H31. subst.
       assert (x' = x /\ x0' = x0 /\ eff1' = [] /\ eff2' = []).
       {
         pose (P1 := H25 0 Nat.lt_0_2).
         pose (P2 := H25 1 Nat.lt_1_2).
         inversion P1. inversion P2. subst.
         
         unfold concatn in H35, H40. simpl in H35, H40.
         apply app_inv_head in H35. apply app_inv_head, app_inv_head in H40.
         rewrite app_nil_r in H35. rewrite app_nil_r in H40. subst.
         
         rewrite get_value_here in H34. inversion H34.
         rewrite get_value_there in H39. rewrite get_value_here in H39. inversion H39.
         subst. auto.
         congruence.
       }
       inversion H30. inversion H32. inversion H34. subst.
       
       (* BACK TO CALL PROOF *)
       apply eval_call with (vals := [x ; x0]) (eff := [[];[]]); auto.
       ** intros. inversion H31. 2: inversion H35. 3: inversion H37.
         -- unfold concatn. simpl. assert (get_value (insert_value (insert_value env (inl A) x) 
                                           (inl B) x0) (inl B) = inl x0).
                                           {  apply get_value_here. }
            rewrite <- H33. apply eval_var.
         -- simpl. subst. assert (get_value (insert_value (insert_value env (inl A) x) 
                                     (inl B) x0) (inl A) = inl x). 
                                     { rewrite get_value_there. apply get_value_here. congruence. }
            rewrite <- H33. apply eval_var.
       ** unfold concatn. simpl concat. rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc.
          unfold concatn in H29. simpl concat in H29.
          rewrite app_nil_r, app_nil_r, app_nil_r, <- app_assoc in H29.
          apply plus_effect_changeable with (eff ++ eff2 ++ eff1). assumption.
Qed.

Example let_1_binding_swap_2_list (env: Environment) (e1 e2 : Expression) (t t' v1 v2 : Value) 
   (eff eff1 eff2 : SideEffectList) (A B : Var) (VarHyp : A <> B)
(Hypo1 : |env, e1, eff| -e> |inl v1, eff ++ eff1|)
(Hypo2 : |env, e1, eff ++ eff2| -e> |inl v1, eff ++ eff2 ++ eff1|)
(Hypo1' : |env, e2, eff| -e> |inl v2, eff ++ eff2|)
(Hypo2' : |env, e2, eff ++ eff1| -e> |inl v2, eff ++ eff1 ++ eff2|) :
|env, ELet [(A, e1); (B, e2)]
     (ECall "plus"%string [EVar A ; EVar B]), eff| -e> |inl t, eff ++ eff1 ++ eff2|
->
|env, ELet [(B, e2); (A, e1)]
     (ECall "plus"%string [EVar B ; EVar A]), eff| -e> |inl t', eff ++ eff2 ++ eff1|
->
t = t'.
Proof.
  intros.
  (* FROM LET HYPO1 *)
  inversion H. subst. simpl in H3. simpl in H4.
  pose (EE1 := element_exist Value 1 vals H3). inversion EE1 as [v1']. inversion H1. subst. inversion H3.
  pose (EE2 := element_exist Value 0 x H6). inversion EE2 as [v2']. inversion H2. subst. inversion H6. 
  apply eq_sym, length_zero_iff_nil in H9. subst.
  pose (EE3 := element_exist _ _ _ H4). inversion EE3 as [eff1']. inversion H8. subst. inversion H4.
  pose (EE4 := element_exist _ _ _ H10). inversion EE4 as [eff2']. inversion H9. subst. inversion H10.
  apply eq_sym, length_zero_iff_nil in H13. subst.
  (* FROM LET HYPO2 *)
  inversion H0. subst. simpl in H14, H15.
  pose (EE1' := element_exist _ _ _ H14). inversion EE1' as [v2'']. inversion H12. subst. inversion H14.
  pose (EE2' := element_exist _ _ _ H17). inversion EE2' as [v1'']. inversion H13. subst. inversion H17.
  apply eq_sym, length_zero_iff_nil in H20. subst.
  pose (EE3' := element_exist _ _ _ H15). inversion EE3' as [eff2'']. inversion H19. subst. inversion H15.
  pose (EE4' := element_exist _ _ _ H21). inversion EE4' as [eff1'']. inversion H20. subst. inversion H21.
  apply eq_sym, length_zero_iff_nil in H24. subst.

  assert (v1' = v1 /\ eff1' = eff1).
  {
    pose (P1 := H5 0 Nat.lt_0_2).
    unfold concatn in P1. simpl in P1. rewrite app_nil_r, app_nil_r in P1.
    pose (WD1 := determinism _ Hypo1).
    pose (PC1 := WD1 _ _ P1).
    inversion PC1. inversion H23. apply app_inv_head in H24. subst. auto.
  }
  inversion H23. subst.
  
  assert (v2'' = v2 /\ eff2'' = eff2).
  {
    pose (P1 := H16 0 Nat.lt_0_2).
    unfold concatn in P1. simpl in P1. rewrite app_nil_r, app_nil_r in P1.
    pose (WD1 := determinism _ Hypo1').
    pose (PC1 := WD1 _ _ P1).
    inversion PC1. inversion H24. apply app_inv_head in H25. subst. auto.
  }
  inversion H24. subst.
  assert (v1'' = v1 /\ v2' = v2 /\ eff1'' = eff1 /\ eff2' = eff2).
  {
    pose (P1 := H16 1 Nat.lt_1_2).
    unfold concatn in P1. simpl in P1. rewrite app_nil_r, app_nil_r in P1.
    pose (WD1 := determinism _ Hypo2).
    pose (PC1 := WD1 _ _ P1).
    inversion PC1. inversion H25. apply app_inv_head, app_inv_head in H26. subst.
    pose (P2 := H5 1 Nat.lt_1_2).
    unfold concatn in P2. simpl in P2. rewrite app_nil_r, app_nil_r in P2.
    pose (WD2 := determinism _ Hypo2').
    pose (PC2 := WD2 _ _ P2).
    inversion PC2. inversion H26. apply app_inv_head, app_inv_head in H27. subst. auto.
  }
  inversion H25. inversion H27. inversion H29. subst.
  (* FROM CALL HYPOS *)
 (* FROM CALL HYPO1 *)
  inversion H11. subst. simpl in H30. simpl in H31.
  pose (EC1 := element_exist _ _ _ H30). inversion EC1 as [v1']. inversion H26. subst. inversion H30.
  pose (EC2 := element_exist _ _ _ H32). inversion EC2 as [v2']. inversion H28. subst. inversion H30.
  apply eq_sym, length_zero_iff_nil in H35. subst.
  pose (EC3 := element_exist _ _ _ H31). inversion EC3 as [eff1']. inversion H34. subst. inversion H31.
  pose (EC4 := element_exist _ _ _ H36). inversion EC4 as [eff2']. inversion H35. subst. inversion H36.
  apply eq_sym, length_zero_iff_nil in H39. subst.
  (* FROM CALL HYPO2 *)
  inversion H22. subst. simpl in H40, H41.
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
|env, ELet [(A, e1); (B, e2)]
     (ECall "plus"%string [EVar A ; EVar B]), eff| -e> |inl t, eff ++ eff1 ++ eff2|
->
|env, ELet [(A, e2); (B, e1)]
     (ECall "plus"%string [EVar A ; EVar B]), eff| -e> |inl t, eff ++ eff2 ++ eff1|.
Proof.
  intros.
  (* FROM LET HYPO *)
  inversion H. subst. simpl in H2. simpl in H3.
  pose (EE1 := element_exist Value 1 vals H2). inversion EE1 as [v1']. inversion H0. subst. inversion H2.
  pose (EE2 := element_exist Value 0 x H5). inversion EE2 as [v2']. inversion H1. subst. inversion H5.
  apply eq_sym, length_zero_iff_nil in H8. subst.
  pose (EE3 := element_exist _ _ _ H3). inversion EE3 as [eff1']. inversion H7. subst. inversion H3.
  pose (EE4 := element_exist _ _ _ H9). inversion EE4 as [eff2']. inversion H8. subst. inversion H9.
  apply eq_sym, length_zero_iff_nil in H12. subst.
  assert (v1' = v1 /\ v2' = v2 /\ eff1' = eff1 /\ eff2' = eff2).
  {
    pose (P1 := H4 0 Nat.lt_0_2).
    pose (P2 := H4 1 Nat.lt_1_2).
    simpl_concatn_H P1. simpl_concatn_H P2. rewrite <- app_assoc in P2.
    pose (D1 := determinism _ Hypo1 _ _ P1). inversion D1. inversion H11. apply app_inv_head in H12. subst.
    pose (D2 := determinism _ Hypo2' _ _ P2). inversion D2. inversion H12. apply app_inv_head, app_inv_head in H13. subst. auto.
  }
  inversion H11. inversion H13. inversion H15. subst.

  (* Deconstruct call *)

  inversion H10. subst.
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
      + simpl_concatn. replace (inl v1) with (get_value (insert_value (insert_value env (inl A) v2) (inl B) v1) (inl B)). apply eval_var.
        apply get_value_here.
      + simpl_concatn. replace (inl v2) with (get_value (insert_value (insert_value env (inl A) v2) (inl B) v1) (inl A)). apply eval_var.
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
|env, ELet [(A, e1); (B, e2)]
     (ECall "plus"%string [EVar A ; EVar B]), eff| -e> |inl t, eff ++ eff1 ++ eff2|
<->
|env, ELet [(A, e2); (B, e1)]
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
|env, ELet [(A, e1); (B, e2)]
     (ECall "plus"%string [EVar A ; EVar B]), eff| -e> |inl t, eff ++ eff1 ++ eff2|
<->
|env, ELet [(B, e2); (A, e1)]
     (ECall "plus"%string [EVar B ; EVar A]), eff| -e> |inl t, eff ++ eff2 ++ eff1|.
Proof.
  split.
  * intro. inversion H. subst.
    pose (EE1 := element_exist Value 1 vals H2). inversion EE1 as [v1']. inversion H0. subst. inversion H2.
    pose (EE2 := element_exist Value 0 x H5). inversion EE2 as [v2']. inversion H1. subst. inversion H5.
    apply eq_sym, length_zero_iff_nil in H8. subst.
    pose (EE3 := element_exist _ _ _ H3). inversion EE3 as [eff1']. inversion H7. subst. inversion H3.
    pose (EE4 := element_exist _ _ _ H9). inversion EE4 as [eff2']. inversion H8. subst. inversion H9.
    apply eq_sym, length_zero_iff_nil in H12. subst.
    assert (v1' = v1 /\ v2' = v2 /\ eff1' = eff1 /\ eff2' = eff2).
    {
      pose (P1 := H4 0 Nat.lt_0_2).
      pose (P2 := H4 1 Nat.lt_1_2).
      simpl_concatn_H P1. simpl_concatn_H P2. rewrite <- app_assoc in P2.
      pose (D1 := determinism _ Hypo1 _ _ P1). inversion D1. inversion H11. apply app_inv_head in H12. subst.
      pose (D2 := determinism _ Hypo2' _ _ P2). inversion D2. inversion H12. apply app_inv_head, app_inv_head in H13. subst. auto.
    }
    inversion H11. inversion H13. inversion H15. subst.

    (* Deconstruct call *)

    inversion H10. subst.
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
        ** simpl_concatn. replace (inl v1) with (get_value (insert_value (insert_value env (inl B) v2) (inl A) v1) (inl A)). apply eval_var.
           apply get_value_here.
        ** simpl_concatn. replace (inl v2) with (get_value (insert_value (insert_value env (inl B) v2) (inl A) v1) (inl B)). apply eval_var.
           rewrite get_value_there. apply get_value_here. congruence.
        ** inversion H29.
      + inversion H24. inversion H26. inversion H28. subst.
        unfold concatn in *. simpl concat. repeat (rewrite <- app_assoc).
        simpl concat in H23. repeat (rewrite <- app_assoc in H23). repeat (rewrite app_nil_r in *).
        apply (plus_comm_basic_value _ _ H23).
  * intro. inversion H. subst.
    pose (EE1 := element_exist Value 1 vals H2). inversion EE1 as [v2']. inversion H0. subst. inversion H2.
    pose (EE2 := element_exist Value 0 x H5). inversion EE2 as [v1']. inversion H1. subst. inversion H5.
    apply eq_sym, length_zero_iff_nil in H8. subst.
    pose (EE3 := element_exist _ _ _ H3). inversion EE3 as [eff2']. inversion H7. subst. inversion H3.
    pose (EE4 := element_exist _ _ _ H9). inversion EE4 as [eff1']. inversion H8. subst. inversion H9.
    apply eq_sym, length_zero_iff_nil in H12. subst.
    assert (v1' = v1 /\ v2' = v2 /\ eff1' = eff1 /\ eff2' = eff2).
    {
      pose (P1 := H4 0 Nat.lt_0_2).
      pose (P2 := H4 1 Nat.lt_1_2).
      simpl_concatn_H P1. simpl_concatn_H P2. rewrite <- app_assoc in P2.
      pose (D1 := determinism _ Hypo1' _ _ P1). inversion D1. inversion H11. apply app_inv_head in H12. subst.
      pose (D2 := determinism _ Hypo2 _ _ P2). inversion D2. inversion H12. apply app_inv_head, app_inv_head in H13. subst. auto.
    }
    inversion H11. inversion H13. inversion H15. subst.

    (* Deconstruct call *)

    inversion H10. subst.
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
        ** simpl_concatn. replace (inl v2) with (get_value (insert_value (insert_value env (inl A) v1) (inl B) v2) (inl B)). apply eval_var.
           apply get_value_here.
        ** simpl_concatn. replace (inl v1) with (get_value (insert_value (insert_value env (inl A) v1) (inl B) v2) (inl A)). apply eval_var.
           rewrite get_value_there. apply get_value_here. congruence.
        ** inversion H29.
      + inversion H24. inversion H26. inversion H28. subst.
        unfold concatn in *. simpl concat. repeat (rewrite <- app_assoc).
        simpl concat in H23. repeat (rewrite <- app_assoc in H23). repeat (rewrite app_nil_r in *).
        apply (plus_comm_basic_value _ _ H23).
Qed.

End Core_Erlang_Equivalence_Proofs.