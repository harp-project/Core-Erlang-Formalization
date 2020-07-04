Require Core_Erlang_Semantics.

Module Side_Effect_Exception_Tests.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.
Import Omega.

Import Core_Erlang_Syntax.Syntax.
Import Core_Erlang_Environment.Environment.
Import Core_Erlang_Semantics.Semantics.
Import Core_Erlang_Helpers.Helpers.
Import Core_Erlang_Side_Effects.Side_Effects.

Definition side_exception_exp (a : Z) (s : string) :  Expression := ELet
   ["X"%string] [ECall "fwrite" [ELit (Atom s)]]
      (EApp (ELit (Integer a)) []).

Example side_exception (env : Environment) (eff : SideEffectList) (a : Z)
                       (s : string) (id : nat) :
  | env, id, side_exception_exp a s , eff| 
-e>
  |id, inr (badfun (VLit (Integer a))), eff ++ [(Output, [VLit (Atom s)])]|.
Proof.
  eapply eval_let with (vals := [ok]) (eff := [[(Output, [VLit (Atom s)])]])
                       (ids := [id]); auto.
  * intros. inversion H. 2: inversion H1. simpl. 
    eapply eval_call with (vals := [VLit (Atom s)]) (eff := [[]]) (ids := [id]); auto.
    - intros. inversion H0. 2: inversion H3. simpl. apply eval_lit.
    - unfold concatn. simpl. rewrite app_nil_r, app_nil_r. reflexivity.
  * unfold concatn. simpl. rewrite app_nil_r. reflexivity.
  * unfold concatn. simpl. 
    eapply eval_apply_ex_closure with (vals := []) (eff := []) (ids := [])
                                      (v := VLit (Integer a)) (eff2 := []); auto.
    - rewrite app_nil_r. apply eval_lit.
    - intros. inversion H.
    - intros. congruence.
    - unfold concatn. simpl. rewrite app_nil_r, app_nil_r. reflexivity.
    - simpl. auto.
Qed.

Example eval_list_tail :
  | [], 0, ECons (ECall "fwrite" [ELit (Atom "a")]) (side_exception_exp 0 "b"), []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), [(Output, [VLit (Atom "b")])]|.
Proof.
  eapply eval_list_ex_tl.
  * reflexivity.
  * apply side_exception.
Qed.

Example eval_list_head :
  | [], 0, ECons (EApp (ELit (Integer 0)) []) (ECall "fwrite" [ELit (Atom "a")]), []| 
-e>
  | 0, inr (badfun (VLit (Integer 0))), [(Output, [VLit (Atom "a")])]|.
Proof.
  eapply eval_list_ex_hd with (eff2 := [(Output, [VLit (Atom "a")])]).
  * reflexivity.
  * eapply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]]) (ids := [0]); auto.
    - intros. inversion H. 2: inversion H1. simpl. apply eval_lit.
    - unfold concatn. simpl. reflexivity.
  * simpl. eapply eval_apply_ex_closure with (vals := []) (eff := []) (ids := []); auto.
    - apply eval_lit.
    - intros. inversion H.
    - intros. congruence.
    - reflexivity.
    - simpl. auto.
Qed.

Example eval_tuple_s_e :
  | [], 0, ETuple [ECall "fwrite" [ELit (Atom "a")]; side_exception_exp 0 "b"], []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), 
          [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]|.
Proof.
  eapply eval_tuple_ex with (vals := [ok]) (ids := [0])
                            (eff := [[(Output, [VLit (Atom "a")])]]) 
                            (i := 1); auto.
  * intros. inversion H. 2: inversion H1. simpl. 
    eapply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]]) (ids := [0]); auto.
    - intros. inversion H0. 2: inversion H3. simpl. apply eval_lit.
  * reflexivity.
  * simpl. apply side_exception.
Qed.

Example eval_try_s_e :
  | [], 0, ETry (ECall "fwrite" [ELit (Atom "a")]) (side_exception_exp 0 "b") (ErrorExp)
             "X"%string "Ex1"%string "Ex2"%string "Ex3"%string, []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), 
       [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]|.
Proof.
  eapply eval_try.
  * eapply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]]) (ids := [0]); auto.
    - intros. inversion H. 2: inversion H1. apply eval_lit.
    - unfold concatn. simpl. reflexivity.
  * reflexivity.
  * apply side_exception.
Qed.

Example eval_catch :
  | [], 0, ETry (side_exception_exp 0 "a") 
             (ECall "fwrite" [ELit (Atom "a")]) (ECall "fwrite" [ELit (Atom "c")])
             "X"%string "Ex1"%string "Ex2"%string "Ex3"%string, []|
-e>
  | 0, inl ok, [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "c")])]|.
Proof.
  eapply eval_try_catch.
  * apply side_exception.
  * reflexivity.
  * simpl. eapply eval_call with (vals := [VLit (Atom "c")]) (eff := [[]]) (ids := [0]); auto.
    - intros. inversion H. 2: inversion H1. apply eval_lit.
Qed.

Example eval_case_pat :
  | [],0,  ECase (side_exception_exp 0 "a") [PVar "X"%string] 
              [ELit (Atom "true")] 
              [ECall "fwrite" [ELit (Atom "b")]], []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), [(Output, [VLit (Atom "a")])]|.
Proof.
  eapply eval_case_ex_pat; auto.
  * reflexivity.
  * apply side_exception.
Qed.

Example eval_case_clause :
  | [(inl "Y"%string, VLit (Integer 2))], 0,
     ECase (ELet ["X"%string] [ECall "fwrite" [ELit (Atom "a")]] (EVar "Y"%string)) 
          [PLit (Integer 1); PVar "Z"%string]
          [ELit (Atom "true"); ELit (Atom "false")]
          [ECall "fwrite" [ELit (Atom "b")]; ECall "fwrite" [ELit (Atom "c")]], []|
-e>
  | 0, inr (if_clause (VLit (Integer 2))), [(Output, [VLit (Atom "a")])]|.
Proof.
  eapply eval_case_clause_ex; auto.
  * reflexivity.
  * eapply eval_let with (vals := [ok]) (eff := [[(Output, [VLit (Atom "a")])]])
                         (ids := [0]); auto.
    - intros. inversion H. 2: inversion H1.
      apply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]]) (ids := [0]); auto.
      + intros. inversion H0. 2: inversion H3. apply eval_lit.
    - reflexivity.
    - apply eval_var.
  * intros. inversion H. 2: inversion H2. 3: omega.
    - subst. inversion H0. apply eval_lit.
    - subst. inversion H0.
Qed.

Example eval_call_s_e :
  | [], 0, ECall "fwrite" [ECall "fwrite" [ELit (Atom "a")]; EApp (ELit (Integer 0)) []], []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), [(Output, [VLit (Atom "a")])]|.
Proof.
  eapply eval_call_ex with (vals := [ok])(ids := [0])
                           (eff := [[(Output, [VLit (Atom "a")])]])
                           (i := 1); auto.
  * intros. inversion H. 2: inversion H1.
    eapply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]]) (ids := [0]); auto.
    - intros. inversion H0. 2: inversion H3. apply eval_lit.
  * reflexivity.
  * simpl. eapply eval_apply_ex_closure with (vals := []) (eff := []) (ids := []); auto.
    - apply eval_lit.
    - intros. inversion H.
    - intros. congruence.
    - reflexivity.
    - auto.
Qed.

Example eval_apply_closure_ex :
  | [], 0, EApp (side_exception_exp 0 "a") [], []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), [(Output, [VLit (Atom "a")])]|.
Proof.
  eapply eval_apply_ex_closure_ex.
  * reflexivity.
  * apply side_exception.
Qed.

Example eval_apply_param :
  | [], 0, EApp (ECall "fwrite" [ELit (Atom "a")]) [side_exception_exp 0 "b"], []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), 
       [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]|.
Proof.
  eapply eval_apply_ex_params with (vals := []) (eff := []) (ids := []); auto.
  * eapply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]]) (ids := [0]); auto.
    - intros. inversion H. 2: inversion H1. apply eval_lit.
    - reflexivity.
  * intros. inversion H.
  * reflexivity.
  * apply side_exception.
Qed.

Example eval_apply_closure :
  | [], 0, EApp (ECall "fwrite" [ELit (Atom "a")]) [ECall "fwrite" [ELit (Atom "b")]], []|
-e>
  | 0, inr (badfun ok), 
      [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]|.
Proof.
  eapply eval_apply_ex_closure with (vals := [ok]) (ids := [0])
                                    (eff := [[(Output, [VLit (Atom "b")])]]); auto.
  * eapply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]]) (ids := [0]); auto.
    - intros. inversion H. 2: inversion H1. apply eval_lit.
    - reflexivity.
  * intros. inversion H. 2: inversion H1.
    eapply eval_call with (vals := [VLit (Atom "b")]) (eff := [[]]) (ids := [0]); auto.
    - intros. inversion H0. 2: inversion H3. simpl. apply eval_lit.
  * intros. unfold ok. congruence.
  * reflexivity.
Qed.

Example eval_apply_param_len :
  | [(inl "X"%string, VClos [] [] 0 [] (ELit (Integer 5)))], 1,
    EApp (EVar "X"%string) [ECall "fwrite" [ELit (Atom "a")]], []|
-e>
  | 1, inr (badarity (VClos [] [] 0 [] (ELit (Integer 5)))), 
       [(Output, [VLit (Atom "a")])]|.
Proof.
  eapply eval_apply_ex_param_count with (vals := [ok]) (n := 0) (ids := [1])
                                        (eff := [[(Output, [VLit (Atom "a")])]]); auto.
  * apply eval_var.
  * intros. inversion H. 2: inversion H1. eapply eval_call with (vals := [VLit (Atom "a")]) 
                                                                (eff := [[]]) (ids := [1]); auto.
    - intros. inversion H0. 2: inversion H3. apply eval_lit.
  * simpl. auto.
  * reflexivity.
Qed.

Example eval_let:
  | [], 0, ELet ["X"%string] [side_exception_exp 2 "a"] (EApp (ELit (Integer 0)) []), []|
-e>
  | 0, inr (badfun (VLit (Integer 2))), [(Output, [VLit (Atom "a")])]|.
Proof.
  eapply eval_let_ex_param with (vals := []) (eff := []) (i := 0) (ids := []); auto.
  * intros. inversion H.
  * reflexivity.
  * apply side_exception.
Qed.

Example eval_map_key:
  | [], 0, EMap [ECall "fwrite" [ELit (Atom "a")]; side_exception_exp 0 "c"] 
             [ECall "fwrite" [ELit (Atom "b")]; ECall "fwrite" [ELit (Atom "d")]], []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), 
       [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")]); 
        (Output, [VLit (Atom "c")])]|.
Proof.
  eapply eval_map_ex_key with (i := 1) (kvals := [ok]) (vvals := [ok]) 
                              (ids := [0;0])
                              (eff := [[(Output, [VLit (Atom "a")])];
                                       [(Output, [VLit (Atom "b")])]]); auto.
  * intros. inversion H. 2: inversion H1. eapply eval_call with (vals := [VLit (Atom "a")]) 
                                                                (eff := [[]]) (ids := [0]); auto.
    - intros. inversion H0. 2: inversion H3. apply eval_lit.
  * intros. inversion H. 2: inversion H1. eapply eval_call with (vals := [VLit (Atom "b")]) 
                                                                (eff := [[]]) (ids := [0]); auto.
    - intros. inversion H0. 2: inversion H3. apply eval_lit.
  * reflexivity.
  * apply side_exception.
Qed.

Example eval_map_value:
  | [], 0, EMap [ECall "fwrite" [ELit (Atom "a")]; ECall "fwrite" [ELit (Atom "c")]] 
             [ECall "fwrite" [ELit (Atom "b")]; side_exception_exp 0 "d"], []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), 
        [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")]); 
         (Output, [VLit (Atom "c")]); (Output, [VLit (Atom "d")])]|.
Proof.
  eapply eval_map_ex_val with (i := 1) (kvals := [ok]) (vvals := [ok])
                              (ids := [0;0])
                              (eff := [[(Output, [VLit (Atom "a")])]; 
                                       [(Output, [VLit (Atom "b")])]]); auto.
  * intros. inversion H. 2: inversion H1. eapply eval_call with (vals := [VLit (Atom "a")]) 
                                                                (eff := [[]]) (ids := [0]); auto.
    - intros. inversion H0. 2: inversion H3. apply eval_lit.
  * intros. inversion H. 2: inversion H1. eapply eval_call with (vals := [VLit (Atom "b")]) 
                                                                (eff := [[]]) (ids := [0]); auto.
    - intros. inversion H0. 2: inversion H3. apply eval_lit.
  * eapply eval_call with (vals := [VLit (Atom "c")]) (eff := [[]]) (ids := [0]); auto.
    - intros. inversion H. 2: inversion H1. apply eval_lit.
    - reflexivity.
  * reflexivity.
  * simpl. apply side_exception.
Qed.

End Side_Effect_Exception_Tests.