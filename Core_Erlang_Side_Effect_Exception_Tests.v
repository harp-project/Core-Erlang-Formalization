Load Core_Erlang_Semantics.

Module Core_Erlang_Side_Effect_Exception_Tests.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.

Import Core_Erlang_Environment.
Import Core_Erlang_Helpers.
Import Core_Erlang_Syntax.
Import Core_Erlang_Side_Effects.
Import Core_Erlang_Semantics.

Definition side_exception_exp (a : Z) (s : string) :  Expression := ELet
   [("X"%string, ECall "fwrite" [ELiteral (Atom s)])]
      (EApply (ELiteral (Integer a)) []).

Example side_exception (env : Environment) (eff : SideEffectList) (a : Z) (s : string) :
  | env, side_exception_exp a s , eff| 
-e>
  |inr (badfun (VLiteral (Integer a))), eff ++ [(Output, [VLiteral (Atom s)])]|.
Proof.
  eapply eval_let with (vals := [ok]) (eff := [[(Output, [VLiteral (Atom s)])]]); auto.
  * intros. inversion H. 2: inversion H1. simpl. 
    eapply eval_call with (vals := [VLiteral (Atom s)]) (eff := [[]]); auto.
    - intros. inversion H0. 2: inversion H3. simpl. apply eval_lit.
    - unfold concatn. simpl. rewrite app_nil_r, app_nil_r. reflexivity.
  * unfold concatn. simpl. rewrite app_nil_r. reflexivity.
  * unfold concatn. simpl. 
    eapply eval_apply_ex_closure with (vals := []) (eff := []) 
                                      (v := VLiteral (Integer a)) (eff2 := []); auto.
    - rewrite app_nil_r. apply eval_lit.
    - intros. inversion H.
    - intros. congruence.
    - unfold concatn. simpl. rewrite app_nil_r, app_nil_r. reflexivity.
Qed.

Example eval_list_tail :
  | [], EList (ECall "fwrite" [ELiteral (Atom "a")]) (side_exception_exp 0 "b"), []|
-e>
  | inr (badfun (VLiteral (Integer 0))), [(Output, [VLiteral (Atom "b")])]|.
Proof.
  eapply eval_list_ex_tl.
  * reflexivity.
  * apply side_exception.
Qed.

Example eval_list_head :
  | [], EList (EApply (ELiteral (Integer 0)) []) (ECall "fwrite" [ELiteral (Atom "a")]), []| 
-e>
  | inr (badfun (VLiteral (Integer 0))), [(Output, [VLiteral (Atom "a")])]|.
Proof.
  eapply eval_list_ex_hd with (eff2 := [(Output, [VLiteral (Atom "a")])]).
  * reflexivity.
  * eapply eval_call with (vals := [VLiteral (Atom "a")]) (eff := [[]]); auto.
    - intros. inversion H. 2: inversion H1. simpl. apply eval_lit.
    - unfold concatn. simpl. reflexivity.
  * simpl. eapply eval_apply_ex_closure with (vals := []) (eff := []); auto.
    - apply eval_lit.
    - intros. inversion H.
    - intros. congruence.
    - reflexivity.
Qed.

Example eval_tuple_s_e :
  | [], ETuple [ECall "fwrite" [ELiteral (Atom "a")]; side_exception_exp 0 "b"], []|
-e>
  | inr (badfun (VLiteral (Integer 0))), 
   [(Output, [VLiteral (Atom "a")]); (Output, [VLiteral (Atom "b")])]|.
Proof.
  eapply eval_tuple_ex with (vals := [ok]) 
                            (eff := [[(Output, [VLiteral (Atom "a")])]]) 
                            (i := 1); auto.
  * intros. inversion H. 2: inversion H1. simpl. 
    eapply eval_call with (vals := [VLiteral (Atom "a")]) (eff := [[]]); auto.
    - intros. inversion H0. 2: inversion H3. simpl. apply eval_lit.
  * reflexivity.
  * simpl. apply side_exception.
Qed.

Example eval_try_s_e :
  | [], ETry [ECall "fwrite" [ELiteral (Atom "a")]] (side_exception_exp 0 "b") (ErrorExp)
             ["X"%string] "Ex1"%string "Ex2"%string "Ex3"%string, []|
-e>
  | inr (badfun (VLiteral (Integer 0))), 
    [(Output, [VLiteral (Atom "a")]); (Output, [VLiteral (Atom "b")])]|.
Proof.
  eapply eval_try with (vals := [VLiteral (Atom "ok")]) (eff := [[(Output, [VLiteral (Atom "a")])]]); auto.
  * intros. inversion H. 2: inversion H1. eapply eval_call with (vals := [VLiteral (Atom "a")]) (eff := [[]]); auto.
    - intros. inversion H0. 2: inversion H3. apply eval_lit.
  * reflexivity.
  * apply side_exception.
Qed.

Example eval_catch :
  | [], ETry [side_exception_exp 0 "a"]
             (ECall "fwrite" [ELiteral (Atom "a")]) (ECall "fwrite" [ELiteral (Atom "c")])
             ["X"%string] "Ex1"%string "Ex2"%string "Ex3"%string, []|
-e>
  | inl ok, [(Output, [VLiteral (Atom "a")]); (Output, [VLiteral (Atom "c")])]|.
Proof.
  eapply eval_try_catch with (i := 0) (vals := []) (eff := []); auto.
  * intros. inversion H.
  * apply side_exception.
  * reflexivity.
  * simpl. eapply eval_call with (vals := [VLiteral (Atom "c")]) (eff := [[]]); auto.
    - intros. inversion H. 2: inversion H1. apply eval_lit.
Qed.

Example eval_case_pat :
  | [], ECase (side_exception_exp 0 "a") [(PVar "X"%string, ELiteral (Atom "true"), ECall "fwrite" [ELiteral (Atom "b")])], []|
-e>
  | inr (badfun (VLiteral (Integer 0))), [(Output, [VLiteral (Atom "a")])]|.
Proof.
  eapply eval_case_ex_pat; auto.
  * reflexivity.
  * apply side_exception.
Qed.

Example eval_case_clause :
  | [(inl "Y"%string, VLiteral (Integer 2))], 
     ECase (ELet [("X"%string, ECall "fwrite" [ELiteral (Atom "a")])] (EVar "Y"%string)) 
          [(PLiteral (Integer 1), ELiteral (Atom "true"), ECall "fwrite" [ELiteral (Atom "b")]);
           (PVar "Z"%string, ELiteral (Atom "false"), ECall "fwrite" [ELiteral (Atom "c")])], []|
-e>
  | inr (if_clause (VLiteral (Integer 2))), [(Output, [VLiteral (Atom "a")])]|.
Proof.
  eapply eval_case_clause_ex; auto.
  * reflexivity.
  * eapply eval_let with (vals := [ok]) (eff := [[(Output, [VLiteral (Atom "a")])]]); auto.
    - intros. inversion H. 2: inversion H1.
      apply eval_call with (vals := [VLiteral (Atom "a")]) (eff := [[]]); auto.
      + intros. inversion H0. 2: inversion H3. apply eval_lit.
    - reflexivity.
    - apply eval_var.
  * intros. inversion H. 2: inversion H2. 3: omega.
    - subst. inversion H0. apply eval_lit.
    - subst. inversion H0.
Qed.

Example eval_call_s_e :
  | [], ECall "fwrite" [ECall "fwrite" [ELiteral (Atom "a")]; EApply (ELiteral (Integer 0)) []], []|
-e>
  | inr (badfun (VLiteral (Integer 0))), [(Output, [VLiteral (Atom "a")])]|.
Proof.
  eapply eval_call_ex with (vals := [ok])
                           (eff := [[(Output, [VLiteral (Atom "a")])]])
                           (i := 1); auto.
  * intros. inversion H. 2: inversion H1.
    eapply eval_call with (vals := [VLiteral (Atom "a")]) (eff := [[]]); auto.
    - intros. inversion H0. 2: inversion H3. apply eval_lit.
  * reflexivity.
  * simpl. eapply eval_apply_ex_closure with (vals := []) (eff := []); auto.
    - apply eval_lit.
    - intros. inversion H.
    - intros. congruence.
    - reflexivity.
Qed.

Example eval_apply_closure_ex :
  | [], EApply (side_exception_exp 0 "a") [], []|
-e>
  | inr (badfun (VLiteral (Integer 0))), [(Output, [VLiteral (Atom "a")])]|.
Proof.
  eapply eval_apply_ex_closure_ex.
  * reflexivity.
  * apply side_exception.
Qed.

Example eval_apply_param :
  | [], EApply (ECall "fwrite" [ELiteral (Atom "a")]) [side_exception_exp 0 "b"], []|
-e>
  | inr (badfun (VLiteral (Integer 0))), 
    [(Output, [VLiteral (Atom "a")]); (Output, [VLiteral (Atom "b")])]|.
Proof.
  eapply eval_apply_ex_params with (vals := []) (eff := []); auto.
  * eapply eval_call with (vals := [VLiteral (Atom "a")]) (eff := [[]]); auto.
    - intros. inversion H. 2: inversion H1. apply eval_lit.
    - reflexivity.
  * intros. inversion H.
  * reflexivity.
  * apply side_exception.
Qed.

Example eval_apply_closure :
  | [], EApply (ECall "fwrite" [ELiteral (Atom "a")]) [ECall "fwrite" [ELiteral (Atom "b")]], []|
-e>
  | inr (badfun ok), 
   [(Output, [VLiteral (Atom "a")]); (Output, [VLiteral (Atom "b")])]|.
Proof.
  eapply eval_apply_ex_closure with (vals := [ok])
                                    (eff := [[(Output, [VLiteral (Atom "b")])]]); auto.
  * eapply eval_call with (vals := [VLiteral (Atom "a")]) (eff := [[]]); auto.
    - intros. inversion H. 2: inversion H1. apply eval_lit.
    - reflexivity.
  * intros. inversion H. 2: inversion H1.
    eapply eval_call with (vals := [VLiteral (Atom "b")]) (eff := [[]]); auto.
    - intros. inversion H0. 2: inversion H3. simpl. apply eval_lit.
  * intros. unfold ok. congruence.
  * reflexivity.
Qed.

Example eval_apply_param_len :
  | [(inl "X"%string, VClosure [] [] [] (ELiteral (Integer 5)))], 
    EApply (EVar "X"%string) [ECall "fwrite" [ELiteral (Atom "a")]], []|
-e>
  | inr (badarity (VClosure [] [] [] (ELiteral (Integer 5)))), 
    [(Output, [VLiteral (Atom "a")])]|.
Proof.
  eapply eval_apply_ex_param_count with (vals := [ok]) 
                                        (eff := [[(Output, [VLiteral (Atom "a")])]]); auto.
  * apply eval_var.
  * intros. inversion H. 2: inversion H1. eapply eval_call with (vals := [VLiteral (Atom "a")]) 
                                                                (eff := [[]]); auto.
    - intros. inversion H0. 2: inversion H3. apply eval_lit.
  * simpl. auto.
  * reflexivity.
Qed.

Example eval_let:
  | [], ELet [("X"%string, side_exception_exp 2 "a")] (EApply (ELiteral (Integer 0)) []), []|
-e>
  | inr (badfun (VLiteral (Integer 2))), [(Output, [VLiteral (Atom "a")])]|.
Proof.
  eapply eval_let_ex_param with (vals := []) (eff := []) (i := 0); auto.
  * intros. inversion H.
  * reflexivity.
  * apply side_exception.
Qed.

Example eval_map_key:
  | [], EMap [(ECall "fwrite" [ELiteral (Atom "a")], ECall "fwrite" [ELiteral (Atom "b")]); (side_exception_exp 0 "c", ECall "fwrite" [ELiteral (Atom "d")])], []|
-e>
  | inr (badfun (VLiteral (Integer 0))), 
    [(Output, [VLiteral (Atom "a")]); (Output, [VLiteral (Atom "b")]); 
     (Output, [VLiteral (Atom "c")])]|.
Proof.
  eapply eval_map_ex_key with (i := 1) (kvals := [ok]) (vvals := [ok]) 
                              (eff := [[(Output, [VLiteral (Atom "a")])];
                                       [(Output, [VLiteral (Atom "b")])]]); auto.
  * intros. inversion H. 2: inversion H1. eapply eval_call with (vals := [VLiteral (Atom "a")]) 
                                                                (eff := [[]]); auto.
    - intros. inversion H0. 2: inversion H3. apply eval_lit.
  * intros. inversion H. 2: inversion H1. eapply eval_call with (vals := [VLiteral (Atom "b")]) 
                                                                (eff := [[]]); auto.
    - intros. inversion H0. 2: inversion H3. apply eval_lit.
  * reflexivity.
  * apply side_exception.
Qed.

Example eval_map_value:
  | [], EMap [(ECall "fwrite" [ELiteral (Atom "a")], ECall "fwrite" [ELiteral (Atom "b")]); 
              (ECall "fwrite" [ELiteral (Atom "c")], side_exception_exp 0 "d")] , []|
-e>
  | inr (badfun (VLiteral (Integer 0))), 
    [(Output, [VLiteral (Atom "a")]); (Output, [VLiteral (Atom "b")]); 
     (Output, [VLiteral (Atom "c")]); (Output, [VLiteral (Atom "d")])]|.
Proof.
  eapply eval_map_ex_val with (i := 1) (kvals := [ok]) (vvals := [ok]) 
                              (eff := [[(Output, [VLiteral (Atom "a")])]; 
                                       [(Output, [VLiteral (Atom "b")])]]); auto.
  * intros. inversion H. 2: inversion H1. eapply eval_call with (vals := [VLiteral (Atom "a")]) 
                                                                (eff := [[]]); auto.
    - intros. inversion H0. 2: inversion H3. apply eval_lit.
  * intros. inversion H. 2: inversion H1. eapply eval_call with (vals := [VLiteral (Atom "b")]) 
                                                                (eff := [[]]); auto.
    - intros. inversion H0. 2: inversion H3. apply eval_lit.
  * eapply eval_call with (vals := [VLiteral (Atom "c")]) (eff := [[]]); auto.
    - intros. inversion H. 2: inversion H1. apply eval_lit.
    - reflexivity.
  * reflexivity.
  * simpl. apply side_exception.
Qed.

End Core_Erlang_Side_Effect_Exception_Tests.