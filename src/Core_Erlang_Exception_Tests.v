Require Core_Erlang_Semantics.

Module Exception_Tests.

Import Core_Erlang_Semantics.Semantics.

Import ListNotations.

Definition exception_call : Expression := ECall "+" [ELit (Integer 5); EEmptyTuple].

Definition exception_value : Value := VCons (VLit (Integer 5)) (VEmptyTuple).

Example eval_exception_call :
  forall {env : Environment} {eff : SideEffectList} {id : nat}, 
  |env, id, exception_call, eff|
-e> 
 |id, inr (badarith exception_value), eff|.
Proof.
  intros. eapply eval_call with (vals := [VLit (Integer 5); VEmptyTuple]) 
                                (eff := [eff; eff]) (ids := [id; id]); auto.
  * intros. inversion H. 2: inversion H1. 3: inversion H3.
    - simpl. eapply eval_tuple with (eff := []) (ids := []); auto.
      + intros. inversion H0.
    - simpl. apply eval_lit.
Qed.

(** DOES NOT COMPILE IN CORE ERLANG *)
Example exception_var :
  |[], 0, EVar "X"%string, []|
-e>
  |0, inr novar, []|.
Proof.
  apply eval_var. reflexivity.
Qed.

Example exception_list_hd :
  |[], 0, ECons (exception_call) (ErrorExp), []|
-e>
  | 0, inr (badarith exception_value), []|.
Proof.
  eapply eval_cons_hd_ex with (eff2 := []).
  * apply eval_lit.
  * apply eval_exception_call.
Qed.

Example exception_list_tl : 
  |[], 0, ECons (ErrorExp) (ECons (exception_call) (ENil)), []|
-e> 
  | 0, inr (badarith exception_value), []|.
Proof.
  eapply eval_cons_tl_ex.
  * eapply eval_cons_hd_ex with (eff2 := []).
    - apply eval_nil.
    - apply eval_exception_call.
Qed.

Example exception_tuple : 
  |[], 0, ETuple [ErrorExp ; ErrorExp; exception_call], []|
-e>
  | 0, inr (badarith exception_value), []|.
Proof.
  eapply eval_tuple_ex with (i := 2) (vals := [ErrorValue; ErrorValue])
                            (eff := [[];[]]) (ids := [0;0]); auto.
  * intros. inversion H.
    - simpl. apply eval_lit.
    - inversion H1.
      + simpl. apply eval_lit.
      + inversion H3.
  * simpl. apply eval_exception_call.
Qed.

Example try_eval : 
  |[], 0, ETry [(EEmptyTuple, "X"%string)]
               (ELit (Atom "ok"%string)) 
               (ELit (Atom "error"%string)) 
               "Ex1"%string "Ex2"%string "Ex3"%string, []|
-e>
  |0, inl ok, []|
.
Proof.
  eapply eval_try with (vals := [VEmptyTuple]) (eff := [[]]) (ids := [0]); auto.
  * intros. inversion H. 2: inversion H1.
    eapply eval_tuple with (eff := []) (ids := []); auto.
    - intros. inversion H0.
  * simpl. apply eval_lit.
Qed.

Example try_eval_catch : 
  |[], 0, ETry [(exception_call, "X"%string)]
               (ELit (Atom "ok"%string)) 
               (ELit (Atom "error"%string)) 
               "Ex1"%string "Ex2"%string "Ex3"%string, []|
-e> 
  |0, inl (VLit (Atom "error"%string)), []|
.
Proof.
  eapply eval_catch with (ex := badarith exception_value) (eff2 := [])
                         (vals := []) (i := 0) (eff := []) (ids := []); auto.
  * intros. inversion H.
  * simpl. apply eval_exception_call.
  * simpl. apply eval_lit.
Qed.

Example try_eval_exception : 
  |[], 0, ETry [(exception_call, "X"%string)]
               (ELit (Atom "ok"%string)) 
               (exception_call) 
                "Ex1"%string "Ex2"%string "Ex3"%string, []|
-e>
  |0, inr (badarith exception_value), []|
.
Proof.
  eapply eval_catch with (ex := badarith exception_value) (eff2 := [])
                         (vals := []) (i := 0) (eff := []) (ids := []); auto.
  * intros. inversion H.
  * simpl. apply eval_exception_call.
  * simpl. apply eval_exception_call.
Qed.

Example try_eval_exception2 : 
  |[], 0, ETry [(EEmptyTuple, "X"%string)]
               (exception_call)
               (ELit (Atom "error"%string)) 
                "Ex1"%string "Ex2"%string "Ex3"%string, []|
-e>
  | 0, inr (badarith exception_value), []|
.
Proof.
  eapply eval_try with (vals := [VEmptyTuple]) (eff := [[]]) (ids := [0]); auto.
  * intros. inversion H. 2: inversion H1.
    eapply eval_tuple with (eff := []) (ids := []); auto.
    - intros. inversion H0.
  * simpl. apply eval_exception_call.
Qed.

Example eval_case_pat_ex :
  | [], 0, ECase (exception_call) 
                 [(PVar "X"%string, ELit (Atom "true"), ELit (Integer 1))], []|
-e>
  | 0, inr (badarith exception_value), []|.
Proof.
  eapply eval_case_pat_ex; auto.
  * apply eval_exception_call.
Qed.

Example eval_case_clause_ex :
  | [(inl "Y"%string, VLit (Integer 2))], 0,
     ECase (EVar "Y"%string)
          [(PLit (Integer 1), ELit (Atom "true"), ELit (Integer 1)); 
           (PVar "Z"%string, ELit (Atom "false"), ELit (Integer 2))], []|
-e>
  | 0, inr (if_clause (VLit (Integer 2))), []|.
Proof.
  eapply eval_case_clause_ex; auto.
  * apply eval_var. reflexivity.
  * intros. inversion H. 2: inversion H2. 3: omega.
    - subst. inversion H0. apply eval_lit.
    - subst. inversion H0.
Qed.

Example call_eval_body_ex : 
  |[], 0, ECall "+"%string [], []|
-e>
  | 0, inr (undef (VLit (Atom "+"))), []|.
Proof.
  eapply eval_call with (vals := []) (eff := []) (ids := []); auto.
  * intros. inversion H.
Qed.

Example call_eval_body_ex2 :
  |[], 0, ECall "+"%string [ELit (Integer 5); EEmptyTuple], []|
-e>
  | 0, inr (badarith exception_value), []|.
Proof.
  apply eval_call with (vals := [VLit (Integer 5); VEmptyTuple]) (eff := [[];[]])
                       (ids := [0;0]); auto.
  * intros. inversion H. 2: inversion H1. 3: inversion H3.
    - apply eval_tuple with (eff := []) (ids := []); auto.
      + intros. inversion H0.
    - apply eval_lit.
Qed.

Example call_eval_param_ex :
  |[], 0, ECall "+"%string [ELit (Integer 5); exception_call], []|
-e>
  |0, inr (badarith exception_value), []|.
Proof.
  eapply eval_call_ex with (i := 1) (vals := [VLit (Integer 5)]) (eff := [[]])
                           (ids := [0]); auto.
  * intros. inversion H.
    - apply eval_lit.
    - inversion H1.
  * simpl. apply eval_exception_call.
Qed.

Example let_eval_exception_params :
  |[], 0, ELet [("X"%string, ELit (Integer 5)); 
                 ("Y"%string, exception_call)] (EEmptyTuple), []|
-e>
  | 0, inr (badarith exception_value), []|.
Proof.
  eapply eval_let_ex with (i := 1) (vals := [VLit (Integer 5)]) (eff := [[]])
                          (ids := [0]); auto.
  * intros. inversion H. 2: inversion H1.
    - simpl. apply eval_lit.
  * simpl. apply eval_exception_call.
Qed.

Example let_eval_exception_body :
  |[], 0, ELet [("X"%string, ELit (Integer 5)); 
                ("Y"%string, ELit (Integer 5))] 
               (exception_call), []|
-e>
  |0, inr (badarith exception_value), []|.
Proof.
  eapply eval_let with (vals := [VLit (Integer 5); VLit (Integer 5)]) 
                       (eff := [[];[]]) (ids := [0; 0]); auto.
  * intros. inversion H.
    - simpl. apply eval_lit.
    - inversion H1. 2: inversion H3. apply eval_lit.
  * apply eval_exception_call.
Qed.

Example apply_eval_exception_closure :
  |[], 0, EApp (ELit (Integer 4)) [ELit (Integer 5); ELit (Integer 5)], []|
-e>
  | 0, inr (badfun (VLit (Integer 4))), []|.
Proof.
  eapply eval_app_badfun_ex with (v := VLit (Integer 4)) 
                                  (vals := [VLit (Integer 5); VLit (Integer 5)])
                                  (eff := [[];[]]) (ids := [0; 0]); auto.
  * apply eval_lit.
  * intros. inversion H. 2: inversion H1. 3: inversion H3.
    - apply eval_lit.
    - apply eval_lit.
  * intros. unfold not. intros. inversion H.
Qed.

Example apply_eval_exception_closure2 :
  |[], 0, EApp (exception_call) [ELit (Integer 5); ELit (Integer 5)], []|
-e>
  | 0, inr (badarith exception_value), []|.
Proof.
  eapply eval_app_closure_ex.
  * apply eval_exception_call.
Qed.

Example apply_eval_exception_param :
  |[(inl "X"%string, VClos [] [] 0 [] (ELit (Integer 4)))], 1,
    EApp (EVar "X"%string) [exception_call], []|
-e>
  |1, inr (badarith exception_value), []|.
Proof.
  eapply eval_app_param_ex with (i := 0) (vals := [])
                                (v := VClos [] [] 0 [] (ELit (Integer 4)))
                                (eff := []) (ids := []); auto.
  * apply eval_var. reflexivity.
  * intros. inversion H.
  * apply eval_exception_call.
Qed.

Example apply_eval_exception_param_count :
  |[(inl "X"%string, VClos [] [] 0 [] (ELit (Integer 4)))], 1,
   EApp (EVar "X"%string) [ELit (Integer 2)], []|
-e>
  |1, inr (badarity (VClos [] [] 0 [] (ELit (Integer 4)))), []|.
Proof.
  eapply eval_app_badarity_ex with (vals := [VLit (Integer 2)]) (n := 0)
                                   (var_list := []) (body := ELit (Integer 4)) 
                                   (ref := []) (ext := []) (eff := [[]])
                                   (ids := [1]); auto.
  * apply eval_var. reflexivity.
  * intros. inversion H. 2: inversion H1. apply eval_lit.
  * simpl. trivial.
Qed.

Example apply_eval_exception_body :
  |[(inl "X"%string, VClos [] [] 0 [] (exception_call))], 1,
   EApp (EVar "X"%string) [], []|
-e> 
  | 1, inr (badarith exception_value), []|.
Proof.
  eapply eval_app with (vals := []) (var_list := []) (body := exception_call) (n := 0)
                       (ref := []) (ext := []) (eff := []) (ids := []); auto.
  * simpl. apply eval_var. reflexivity.
  * intros. inversion H.
  * simpl. apply eval_exception_call.
Qed.

Example letrec_exception : 
  |[], 0, ELetRec [(("fun1"%string, 0), ([], ErrorExp))] (exception_call), []|
-e>
  |1, inr (badarith exception_value), []|.
Proof.
  eapply eval_letrec; try (reflexivity).
  * simpl. apply eval_exception_call.
Qed.

Example map_eval_ex_key :
  |[], 0, EMap [(ErrorExp, ErrorExp); 
                (ErrorExp, ErrorExp);
                (exception_call, ErrorExp);
                (ErrorExp, ErrorExp)], []|
-e>
  |0, inr (badarith exception_value), []|.
Proof.
  eapply eval_map_key_ex with (i := 2) (kvals := [ErrorValue; ErrorValue]) 
                              (vvals := [ErrorValue; ErrorValue]) (ids := [0;0;0;0])
                              (eff := [[];[];[];[]]); try(reflexivity).
  * simpl. auto.
  * intros. inversion H.
    - apply eval_lit.
    - inversion H1. 
      + apply eval_lit.
      + inversion H3.
  * intros. inversion H.
    - apply eval_lit.
    - inversion H1. 
      + apply eval_lit.
      + inversion H3.
  * simpl. apply eval_exception_call.
Qed.

Example map_eval_ex_val :
  |[], 0, EMap [(ErrorExp, ErrorExp); 
                (ErrorExp, exception_call);
                (ErrorExp, ErrorExp);
                (ErrorExp, ErrorExp)], []|
-e>
  |0, inr (badarith exception_value), []|.
Proof.
  eapply eval_map_val_ex with (i := 1) (kvals := [ErrorValue]) 
                              (vvals := [ErrorValue]) (ids := [0;0])
                              (val := ErrorValue) (eff := [[];[]]); try (reflexivity).
  * simpl. auto.
  * intros. inversion H.
    - apply eval_lit.
    - inversion H1.
  * intros. inversion H.
    - apply eval_lit.
    - inversion H1.
  * simpl. apply eval_lit.
  * simpl. apply eval_exception_call.
Qed.

Example seq_eval_ex_1 :
  | [], 0, ESeq exception_call
                (ELit (Integer 42))
   , [] |
-e>
  | 0, inr (badarith exception_value), [] |.
Proof.
  eapply eval_seq_ex.
  * apply eval_exception_call.
Qed.

Example seq_eval_ex_2 :
  | [], 0, ESeq (ELit (Integer 42))
                exception_call
   , [] |
-e>
  | 0, inr (badarith exception_value), [] |.
Proof.
  eapply eval_seq.
  * apply eval_lit.
  * apply eval_exception_call.
Qed.

End Exception_Tests.