Load Core_Erlang_Semantics.

Module Core_Erlang_Exception_Tests.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.

Import Core_Erlang_Environment.
Import Core_Erlang_Helpers.
Import Core_Erlang_Syntax.
Import Core_Erlang_Side_Effects.
Import Core_Erlang_Semantics.

Definition exception_call : Expression := ECall "plus" [ELiteral (Integer 5); EEmptyTuple].

Definition exception_value : Value := VList (VLiteral (Integer 5)) (VEmptyTuple).

Example eval_exception_call :
  forall {env eff}, |env, exception_call, eff|
-e> 
 |inr (badarith exception_value), eff|.
Proof.
  intros. eapply eval_call with (vals := [VLiteral (Integer 5); VEmptyTuple]) 
                                (eff := [[]; []]); auto.
  * intros. inversion H. 2: inversion H1. 3: inversion H3.
    - simpl. apply eval_tuple with (eff := []); auto.
      + intros. inversion H0.
      + unfold concatn. simpl. apply app_nil_end.
    - simpl. apply eval_lit.
  * unfold concatn. simpl. assert (eff ++ [] = eff). symmetry. 
    apply app_nil_end. rewrite H. reflexivity. 
Qed.

(** DOES NOT COMPPILE IN CORE ERLANG *)
Example exception_var :
  |[], EVar "X"%string, []|
-e>
  |inr novar, []|.
Proof.
  apply eval_var.
Qed.

Example exception_list_hd :
  |[], EList (exception_call) (ErrorExp), []|
-e>
  |inr (badarith exception_value), []|.
Proof.
  eapply eval_list_ex_hd with (eff2 := []).
  * reflexivity.
  * apply eval_lit.
  * apply eval_exception_call.
Qed.

Example exception_list_tl : 
  |[], EList (ErrorExp) (EList (exception_call) (EEmptyList)), []|
-e> 
  |inr (badarith exception_value), []|.
Proof.
  eapply eval_list_ex_tl.
  * reflexivity.
  * eapply eval_list_ex_hd with (eff2 := []).
    - reflexivity.
    - apply eval_emptylist.
    - apply eval_exception_call.
Qed.

Example exception_tuple : 
  |[], ETuple [ErrorExp ; ErrorExp; exception_call], []|
-e>
  |inr (badarith exception_value), []|.
Proof.
  eapply eval_tuple_ex with (i := 2) (vals := [ErrorValue; ErrorValue]) (eff := [[];[]]).
  * simpl. auto.
  * simpl. auto.
  * simpl. auto.
  * intros. inversion H.
    - simpl. apply eval_lit.
    - inversion H1.
      + simpl. apply eval_lit.
      + inversion H3.
  * reflexivity.
  * simpl. apply eval_exception_call.
Qed.

Example try_eval : 
  |[], ETry (EEmptyTuple) 
            (ELiteral (Atom "ok"%string)) 
            (ELiteral (Atom "error"%string)) 
            "X"%string "Ex1"%string "Ex2"%string "Ex3"%string, []|
-e>
  |inl ok, []|
.
Proof.
  eapply eval_try with (val' := VEmptyTuple).
  * instantiate (1 := []). simpl. eapply eval_tuple with (eff := []).
    - reflexivity.
    - simpl. reflexivity.
    - intros. inversion H.
    - reflexivity.
  * reflexivity.
  * simpl. apply eval_lit.
Qed.

Example try_eval_catch : 
  |[], ETry (exception_call) 
            (ELiteral (Atom "ok"%string)) 
            (ELiteral (Atom "error"%string)) 
            "X"%string "Ex1"%string "Ex2"%string "Ex3"%string, []|
-e> 
  |inl (VLiteral (Atom "error"%string)), []|
.
Proof.
  eapply eval_try_catch with (ex := badarith exception_value) (eff2 := []).
  * simpl. apply eval_exception_call.
  * reflexivity.
  * simpl. apply eval_lit.
Qed.

Example try_eval_exception : 
  |[], ETry (exception_call) 
       (ELiteral (Atom "ok"%string)) 
       (exception_call) 
        "X"%string "Ex1"%string "Ex2"%string "Ex3"%string, []|
-e>
  |inr (badarith exception_value), []|
.
Proof.
  eapply eval_try_catch with (ex := badarith exception_value) (eff2 := []).
  * apply eval_exception_call.
  * reflexivity.
  * simpl. apply eval_exception_call.
Qed.

Example try_eval_exception2 : 
  |[], ETry (EEmptyTuple)
            (exception_call)
            (ELiteral (Atom "error"%string)) 
            "X"%string "Ex1"%string "Ex2"%string "Ex3"%string, []|
-e>
  |inr (badarith exception_value), []|
.
Proof.
  eapply eval_try with (val' := VEmptyTuple) (eff2 := []).
  * apply eval_tuple with (eff := []); auto. intros. inversion H.
  * reflexivity.
  * simpl. apply eval_exception_call.
Qed.

Example call_eval_body_ex : 
  |[], ECall "plus"%string [], []|
-e>
  |inr (undef (VLiteral (Atom "plus"))), []|.
Proof.
  eapply eval_call with (vals := []) (eff := []); auto.
  * intros. inversion H.
Qed.

Example call_eval_body_ex2 :
  |[], ECall "plus"%string [ELiteral (Integer 5); EEmptyTuple], []|
-e>
  |inr (badarith exception_value), []|.
Proof.
  apply eval_call with (vals := [VLiteral (Integer 5); VEmptyTuple]) (eff := [[];[]]); auto.
  * intros. inversion H. 2: inversion H1. 3: inversion H3.
    - unfold concatn. simpl. apply eval_tuple with (eff := []); auto.
      + intros. inversion H0.
    - apply eval_lit.
Qed.

Example call_eval_param_ex :
  |[], ECall "plus"%string [ELiteral (Integer 5); exception_call], []|
-e>
  |inr (badarith exception_value), []|.
Proof.
  eapply eval_call_ex with (i := 1) (vals := [VLiteral (Integer 5)]) (eff := [[]]).
  * simpl. auto.
  * simpl. auto.
  * simpl. auto.
  * intros. inversion H.
    - apply eval_lit.
    - inversion H1.
  * unfold concatn. simpl. reflexivity.
  * simpl. apply eval_exception_call.
Qed.

Example let_eval_exception_params :
  |[], ELet ["X"%string; "Y"%string] [ELiteral (Integer 5); exception_call] (EEmptyTuple), []|
-e>
  |inr (badarith exception_value), []|.
Proof.
  eapply eval_let_ex_param with (i := 1) (vals := [VLiteral (Integer 5)]) (eff := [[]]).
  * reflexivity.
  * simpl. auto.
  * reflexivity.
  * intros. inversion H. 2: inversion H1.
    - simpl. apply eval_lit.
  * simpl. reflexivity.
  * simpl. apply eval_exception_call.
Qed.

Example let_eval_exception_body :
  |[], ELet ["X"%string; "Y"%string] [ELiteral (Integer 5); ELiteral (Integer 5)] 
         (exception_call), []|
-e>
  |inr (badarith exception_value), []|.
Proof.
  eapply eval_let with (vals := [VLiteral (Integer 5); VLiteral (Integer 5)]) 
                       (eff := [[];[]]); auto.
  * intros. inversion H.
    - simpl. apply eval_lit.
    - inversion H1. 2: inversion H3. apply eval_lit.
  * unfold concatn. simpl. reflexivity.
  * apply eval_exception_call.
Qed.

Example apply_eval_exception_closure :
  |[], EApply (ELiteral (Integer 4)) [ELiteral (Integer 5); ELiteral (Integer 5)], []|
-e>
  |inr (noclosure (VLiteral (Integer 4))), []|.
Proof.
  eapply eval_apply_ex_closure with (v := VLiteral (Integer 4)) 
                                    (vals := [VLiteral (Integer 5); VLiteral (Integer 5)])
                                    (eff := [[];[]]); auto.
  * apply eval_lit.
  * intros. inversion H. 2: inversion H1. 3: inversion H3.
    - apply eval_lit.
    - apply eval_lit.
  * intros. unfold not. intros. inversion H.
  * simpl. reflexivity.
Qed.

Example apply_eval_exception_closure2 :
  |[], EApply (exception_call) [ELiteral (Integer 5); ELiteral (Integer 5)], []|
-e>
  |inr (badarith exception_value), []|.
Proof.
  eapply eval_apply_ex_closure_ex.
  * reflexivity.
  * apply eval_exception_call.
Qed.

Example apply_eval_exception_param :
  |[(inl "X"%string, VClosure [] [] [] (ELiteral (Integer 4)))], 
    EApply (EVar "X"%string) [exception_call], []|
-e>
  |inr (badarith exception_value), []|.
Proof.
  eapply eval_apply_ex_params with (i := 0) (vals := []) 
                                   (v := VClosure [] [] [] (ELiteral (Integer 4)))
                                   (eff := []); auto.
  * apply eval_var.
  * intros. inversion H.
  * reflexivity.
  * unfold concatn. simpl. apply eval_exception_call.
Qed.

Example apply_eval_exception_param_count :
  |[(inl "X"%string, VClosure [] [] [] (ELiteral (Integer 4)))],
   EApply (EVar "X"%string) [ELiteral (Integer 2)], []|
-e>
  |inr (args (VClosure [] [] [] (ELiteral (Integer 4)))), []|.
Proof.
  eapply eval_apply_ex_param_count with (vals := [VLiteral (Integer 2)]) 
                                        (var_list := []) (body := ELiteral (Integer 4)) 
                                        (ref := []) (ext := []) (eff := [[]]); auto.
  * apply eval_var.
  * intros. inversion H. 2: inversion H1. apply eval_lit.
  * simpl. trivial.
  * reflexivity.
Qed.

Example apply_eval_exception_body :
  |[(inl "X"%string, VClosure [] [] [] (exception_call))],
   EApply (EVar "X"%string) [], []|
-e> 
  |inr (badarith exception_value), []|.
Proof.
  eapply eval_apply with (vals := []) (var_list := []) (body := exception_call)
                         (ref := []) (ext := []) (eff := []); auto.
  * simpl. apply eval_var.
  * intros. inversion H.
  * simpl. reflexivity.
  * unfold concatn. simpl. apply eval_exception_call.
Qed.

Example letrec_exception : 
  |[], ELetrec [("fun1"%string, 0)] [[]] [(ErrorExp)] (exception_call), []|
-e>
  |inr (badarith exception_value), []|.
Proof.
  eapply eval_letrec; try (reflexivity).
  * simpl. apply eval_exception_call.
Qed.

Example map_eval_ex_key :
  |[], EMap [ErrorExp; ErrorExp; exception_call; ErrorExp]
            [ErrorExp; ErrorExp; ErrorExp; ErrorExp], []|
-e>
  |inr (badarith exception_value), []|.
Proof.
  eapply eval_map_ex_key with (i := 2) (kvals := [ErrorValue; ErrorValue]) 
                              (vvals := [ErrorValue; ErrorValue]) 
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
  |[], EMap [ErrorExp; ErrorExp; exception_call; ErrorExp] 
            [ErrorExp; exception_call; ErrorExp; ErrorExp], []|
-e>
  |inr (badarith exception_value), []|.
Proof.
  eapply eval_map_ex_val with (i := 1) (kvals := [ErrorValue]) (vvals := [ErrorValue]) 
                              (val := ErrorValue) (eff := [[];[]]); try (reflexivity).
  * simpl. auto.
  * intros. inversion H.
    - apply eval_lit.
    - inversion H1.
  * intros. inversion H.
    - apply eval_lit.
    - inversion H1.
  * simpl. apply eval_lit.
  * reflexivity.
  * simpl. apply eval_exception_call.
Qed.

End Core_Erlang_Exception_Tests.