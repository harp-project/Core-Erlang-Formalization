Require Core_Erlang_Semantics.

Module Side_Effect_Exception_Tests.

Import Core_Erlang_Semantics.Semantics.

Import ListNotations.

Definition side_exception_exp (a : Z) (s : string) :  Expression := ELet
   [("X"%string,ECall "fwrite" [ELit (Atom s)])]
      (EApp (ELit (Integer a)) []).

Example side_exception (env : Environment) (eff : SideEffectList) (a : Z)
                       (s : string) (id : nat) :
  | env, id, side_exception_exp a s , eff| 
-e>
  |id, inr (badfun (VLit (Integer a))), eff ++ [(Output, [VLit (Atom s)])]|.
Proof.
  eapply eval_let with (vals := [ok]) (eff := [eff ++ [(Output, [VLit (Atom s)])]])
                       (ids := [id]); auto.
  * intros. inversion H. 2: inversion H1. simpl. 
    eapply eval_call with (vals := [VLit (Atom s)]) (eff := [eff]) (ids := [id]); auto.
    - intros. inversion H0. 2: inversion H3. simpl. apply eval_lit.
  * eapply eval_app_badfun_ex with (vals := []) (eff := []) (ids := [])
                                   (v := VLit (Integer a)); auto.
    - simpl. apply eval_lit.
    - intros. inversion H.
    - intros. congruence.
    - reflexivity.
    - simpl. auto.
Qed.

Example eval_list_tail :
  | [], 0, ECons (ECall "fwrite" [ELit (Atom "a")]) (side_exception_exp 0 "b"), []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), [(Output, [VLit (Atom "b")])]|.
Proof.
  eapply eval_cons_tl_ex.
  * apply side_exception.
Qed.

Example eval_list_head :
  | [], 0, ECons (EApp (ELit (Integer 0)) []) (ECall "fwrite" [ELit (Atom "a")]), []| 
-e>
  | 0, inr (badfun (VLit (Integer 0))), [(Output, [VLit (Atom "a")])]|.
Proof.
  eapply eval_cons_hd_ex with (eff2 := [(Output, [VLit (Atom "a")])]).
  * eapply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]]) (ids := [0]); auto.
    - intros. inversion H. 2: inversion H1. simpl. apply eval_lit.
    - reflexivity.
  * simpl. eapply eval_app_badfun_ex with (vals := []) (eff := []) (ids := []); auto.
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
  * simpl. apply side_exception.
Qed.

Example eval_try_s_e :
  | [], 0, ETry [(ECall "fwrite" [ELit (Atom "a")], "X"%string)] (side_exception_exp 0 "b") (ErrorExp)
             "Ex1"%string "Ex2"%string "Ex3"%string, []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), 
       [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]|.
Proof.
  eapply eval_try with (vals := [VLit (Atom "ok")]) (ids := [0]) (eff := [[(Output, [VLit (Atom "a")])]]); auto.
  * intros. inversion H. 2: inversion H1. eapply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]]) (ids := [0]); auto.
    - intros. inversion H0. 2: inversion H3. apply eval_lit.
  * apply side_exception.
Qed.

Example eval_catch :
  | [], 0, ETry [(side_exception_exp 0 "a", "X"%string)]
             (ECall "fwrite" [ELit (Atom "a")]) (ECall "fwrite" [ELit (Atom "c")])
             "Ex1"%string "Ex2"%string "Ex3"%string, []|
-e>
  | 0, inl ok, [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "c")])]|.
Proof.
  eapply eval_catch with (vals := []) (eff := []) (ids := []) (i := 0); auto.
  * intros. inversion H.
  * apply side_exception.
  * simpl. eapply eval_call with (vals := [VLit (Atom "c")]) (eff := [[(Output, [VLit (Atom "a")])]]) (ids := [0]); auto.
    - intros. inversion H. 2: inversion H1. apply eval_lit.
Qed.

Example eval_case_pat :
  | [],0,  ECase [side_exception_exp 0 "a"]
                 [([PVar "X"%string], ELit (Atom "true"), ECall "fwrite" [ELit (Atom "b")])]
  , []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), [(Output, [VLit (Atom "a")])]|.
Proof.
  eapply eval_case_pat_ex with (vals := []) (eff := []) (ids := []) (i := 0); auto.
  * intros. inversion H.
  * apply side_exception.
Qed.

Example eval_case_clause :
  | [(inl "Y"%string, VLit (Integer 2))], 0,
     ECase [ELet [("X"%string, ECall "fwrite" [ELit (Atom "a")])] (EVar "Y"%string)]
          [([PLit (Integer 1)], ELit (Atom "true"), ECall "fwrite" [ELit (Atom "b")]); 
           ([PVar "Z"%string], ELit (Atom "false"), ECall "fwrite" [ELit (Atom "c")])]
  , []|
-e>
  | 0, inr if_clause, [(Output, [VLit (Atom "a")])]|.
Proof.
  eapply eval_case_clause_ex with (vals := [VLit (Integer 2)]) (eff := [[(Output, [VLit (Atom "a")])]]) (ids := [0]); auto.
  * intros.  inversion H. 
    - eapply eval_let with (vals := [ok]) (eff := [[(Output, [VLit (Atom "a")])]])
                         (ids := [0]); auto.
      + intros. inversion H0. 2: inversion H3.
        apply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]]) (ids := [0]); auto.
        ** intros. inversion H2. 2: inversion H5. apply eval_lit.
      + apply eval_var. reflexivity.
    - inversion H1.
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
  * simpl. eapply eval_app_badfun_ex with (vals := []) (eff := []) (ids := []); auto.
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
  eapply eval_app_closure_ex.
  * apply side_exception.
Qed.

Example eval_apply_param :
  | [], 0, EApp (ECall "fwrite" [ELit (Atom "a")]) [side_exception_exp 0 "b"], []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), 
       [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]|.
Proof.
  eapply eval_app_param_ex with (vals := []) (eff := []) (ids := []); auto.
  * auto.
  * eapply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]]) (ids := [0]); auto.
    - intros. inversion H. 2: inversion H1. apply eval_lit.
    - reflexivity.
  * intros. inversion H.
  * apply side_exception.
Qed.

Example eval_apply_closure :
  | [], 0, EApp (ECall "fwrite" [ELit (Atom "a")]) [ECall "fwrite" [ELit (Atom "b")]], []|
-e>
  | 0, inr (badfun ok), 
      [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]|.
Proof.
  eapply eval_app_badfun_ex with (vals := [ok]) (ids := [0])
                                 (eff := [[(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]]); auto.
  * eapply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]]) (ids := [0]); auto.
    - intros. inversion H. 2: inversion H1. apply eval_lit.
    - reflexivity.
  * intros. inversion H. 2: inversion H1.
    eapply eval_call with (vals := [VLit (Atom "b")]) (eff := [[(Output, [VLit (Atom "a")])]]) (ids := [0]); auto.
    - intros. inversion H0. 2: inversion H3. simpl. apply eval_lit.
  * intros. unfold ok. congruence.
Qed.

Example eval_apply_param_len :
  | [(inl "X"%string, VClos [] [] 0 [] (ELit (Integer 5)))], 1,
    EApp (EVar "X"%string) [ECall "fwrite" [ELit (Atom "a")]], []|
-e>
  | 1, inr (badarity (VClos [] [] 0 [] (ELit (Integer 5)))), 
       [(Output, [VLit (Atom "a")])]|.
Proof.
  eapply eval_app_badarity_ex with (vals := [ok]) (n := 0) (ids := [1])
                                   (eff := [[(Output, [VLit (Atom "a")])]]); auto.
  * apply eval_var. reflexivity.
  * intros. inversion H. 2: inversion H1. eapply eval_call with (vals := [VLit (Atom "a")]) 
                                                                (eff := [[]]) (ids := [1]); auto.
    - intros. inversion H0. 2: inversion H3. apply eval_lit.
  * simpl. auto.
Qed.

Example eval_let:
  | [], 0, ELet [("X"%string, side_exception_exp 2 "a")] (EApp (ELit (Integer 0)) []), []|
-e>
  | 0, inr (badfun (VLit (Integer 2))), [(Output, [VLit (Atom "a")])]|.
Proof.
  eapply eval_let_ex with (vals := []) (eff := []) (i := 0) (ids := []); auto.
  * intros. inversion H.
  * apply side_exception.
Qed.

Example eval_map_key:
  | [], 0, EMap [(ECall "fwrite" [ELit (Atom "a")], ECall "fwrite" [ELit (Atom "b")]);
                 (side_exception_exp 0 "c", ECall "fwrite" [ELit (Atom "d")])]
  , []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), 
       [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")]); 
        (Output, [VLit (Atom "c")])]|.
Proof.
  eapply eval_map_key_ex with (i := 1) (kvals := [ok]) (vvals := [ok]) 
                              (ids := [0;0])
                              (eff := [[(Output, [VLit (Atom "a")])];
                                       [(Output, [VLit (Atom "a")]);(Output, [VLit (Atom "b")])]]); auto.
  * intros. inversion H. 2: inversion H1. eapply eval_call with (vals := [VLit (Atom "a")]) 
                                                                (eff := [[]]) (ids := [0]); auto.
    - intros. inversion H0. 2: inversion H3. simpl. apply eval_lit.
  * intros. inversion H. 2: inversion H1. eapply eval_call with (vals := [VLit (Atom "b")]) 
                                                                (eff := [[(Output, [VLit (Atom "a")])]]) (ids := [0]); auto.
    - intros. inversion H0. 2: inversion H3. apply eval_lit.
  * apply side_exception.
Qed.

Example eval_map_value:
  | [], 0, EMap [(ECall "fwrite" [ELit (Atom "a")], ECall "fwrite" [ELit (Atom "b")]);
                 (ECall "fwrite" [ELit (Atom "c")], side_exception_exp 0 "d")]
  , []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), 
        [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")]); 
         (Output, [VLit (Atom "c")]); (Output, [VLit (Atom "d")])]|.
Proof.
  eapply eval_map_val_ex with (i := 1) (kvals := [ok]) (vvals := [ok])
                              (ids := [0;0])
                              (eff := [[(Output, [VLit (Atom "a")])]; 
                                       [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]]); auto.
  * intros. inversion H. 2: inversion H1. eapply eval_call with (vals := [VLit (Atom "a")]) 
                                                                (eff := [[]]) (ids := [0]); auto.
    - intros. inversion H0. 2: inversion H3. apply eval_lit.
  * intros. inversion H. 2: inversion H1. eapply eval_call with (vals := [VLit (Atom "b")]) 
                                                                (eff := [[(Output, [VLit (Atom "a")])]]) (ids := [0]); auto.
    - intros. inversion H0. 2: inversion H3. apply eval_lit.
  * eapply eval_call with (vals := [VLit (Atom "c")]) (eff := [[(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]]) (ids := [0]); auto.
    - intros. inversion H. 2: inversion H1. apply eval_lit.
    - reflexivity.
  * simpl. apply side_exception.
Qed.

Example seq_eval_ex_1 :
  | [], 0, ESeq (side_exception_exp 0 "a")
                (ECall "fwrite" [ELit (Atom "b")])
   , [] |
-e>
  | 0, inr (badfun (VLit (Integer 0))), [(Output, [VLit (Atom "a")])] |.
Proof.
  eapply eval_seq_ex.
  * apply side_exception.
Qed.

Example seq_eval_ex_2 :
  | [], 0, ESeq (ECall "fwrite" [ELit (Atom "a")])
                (ESeq (side_exception_exp 0 "b")
                      (ECall "fwrite" [ELit (Atom "c")]))
   , [] |
-e>
  | 0, inr (badfun (VLit (Integer 0))), [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])] |.
Proof.
  eapply eval_seq.
  * eapply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]]) (ids := [0]); auto.
    - intros. inversion H. 2: inversion H1. apply eval_lit.
    - reflexivity.
  * simpl. eapply eval_seq_ex.
    - apply side_exception.
Qed.

End Side_Effect_Exception_Tests.