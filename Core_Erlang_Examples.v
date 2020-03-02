Load Core_Erlang_Semantics.

Module Core_Erlang_Examples.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.

Import Core_Erlang_Syntax.
Import Core_Erlang_Semantics.
Import Core_Erlang_Helpers.
Import Core_Erlang_Closures.

(* This is an edless recursion *)
Example eval_letrec1 : |[], [], ELetrec [("x"%string, 1)] [["X"%string]] [EApply (EFunSig ("x"%string, 1)) [EVar "X"%string]] (EApply (EFunSig ("x"%string, 1)) [ELiteral EmptyTuple])| -e> inl ErrorValue.
Proof.
  apply eval_letrec; try (reflexivity).
  * simpl. apply eval_apply with (vals := [VLiteral EmptyTuple]) (body := (EApply (EFunSig ("x"%string, 1)) [EVar "X"%string])) (var_list := ["X"%string]) (ref := (inr ("x"%string, 1))); try (reflexivity).
    - apply eval_funsig.
    - intros. inversion H.
      + inversion H0. apply eval_lit.
      + inversion H0.
    - simpl. apply eval_apply with (vals := [VLiteral EmptyTuple]) (body := (EApply (EFunSig ("x"%string, 1)) [EVar "X"%string])) (var_list := ["X"%string]) (ref := inr ("x"%string, 1)); try (reflexivity).
    + apply eval_funsig.
    + intros. inversion H.
      ** inversion H0. apply eval_var.
      ** inversion H0.
    + simpl. apply eval_apply with (vals := [VLiteral EmptyTuple]) (body := (EApply (EFunSig ("x"%string, 1)) [EVar "X"%string])) (var_list := ["X"%string]) (ref := inr ("x"%string, 1)).
Admitted.

(* This is not recursive, but can't be derivated, because the expression is faulty *)
Example eval_letrec2 : |[], [], ELet ["F"%string] [EFun ["X"%string] (EApply (EVar "F"%string) [EVar "X"%string])] (EApply (EVar "F"%string) [ELiteral EmptyTuple])| -e> inl ErrorValue.
Proof.
  apply eval_let with (vals := [VClosure (inl []) ["X"%string] (EApply (EVar "F"%string) [EVar "X"%string])]).
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. apply eval_fun.
    - inversion H0.
  * simpl. eapply eval_apply with (vals := [VLiteral EmptyTuple]) (ref := inl []) (var_list := ["X"%string]) (body := (EApply (EVar "F"%string) [EVar "X"%string])).
    - reflexivity.
    - apply eval_var.
    - reflexivity.
    - intros. inversion H.
      + inversion H0. apply eval_lit.
      + inversion H0.
    - simpl. eapply eval_apply with (vals := [VLiteral EmptyTuple]). (* Here, I cant say anything about F's var_list, body and app_env *)
      + reflexivity.
      + shelve.
      + shelve.
      + intros. inversion H.
        ** inversion H0. apply eval_var.
        ** inversion H0.
      + simpl. admit.
Admitted.

(* Top level functions, and their closures must be added initially *)
Example multiple_top_level_funs : |[(inr ("fun1"%string, 0), VClosure (inr ("fun1"%string, 0)) [] (EApply (EFunSig ("fun3"%string, 0)) [])) ; 
                                    (inr ("fun2"%string, 0), VClosure (inr ("fun2"%string, 0)) [] (ELiteral (Integer 42))) ;
                                    (inr ("fun3"%string, 0), VClosure (inr ("fun3"%string, 0)) [] (EApply (EFunSig ("fun2"%string, 0)) []))]
                                    ,
                                    [
                                      (("fun1"%string, 0), [(inr ("fun1"%string, 0), VClosure (inr ("fun1"%string, 0)) [] (EApply (EFunSig ("fun3"%string, 0)) [])) ; 
                                    (inr ("fun2"%string, 0), VClosure (inr ("fun2"%string, 0)) [] (ELiteral (Integer 42))) ;
                                    (inr ("fun3"%string, 0), VClosure (inr ("fun3"%string, 0)) [] (EApply (EFunSig ("fun2"%string, 0)) []))]) ;
                                      (("fun2"%string, 0), [(inr ("fun1"%string, 0), VClosure (inr ("fun1"%string, 0)) [] (EApply (EFunSig ("fun3"%string, 0)) [])) ; 
                                    (inr ("fun2"%string, 0), VClosure (inr ("fun2"%string, 0)) [] (ELiteral (Integer 42))) ;
                                    (inr ("fun3"%string, 0), VClosure (inr ("fun3"%string, 0)) [] (EApply (EFunSig ("fun2"%string, 0)) []))]) ;
                                      (("fun3"%string, 0), [(inr ("fun1"%string, 0), VClosure (inr ("fun1"%string, 0)) [] (EApply (EFunSig ("fun3"%string, 0)) [])) ; 
                                    (inr ("fun2"%string, 0), VClosure (inr ("fun2"%string, 0)) [] (ELiteral (Integer 42))) ;
                                    (inr ("fun3"%string, 0), VClosure (inr ("fun3"%string, 0)) [] (EApply (EFunSig ("fun2"%string, 0)) []))])
                                    ]
                                    , EApply (EFunSig ("fun1"%string,0)) []| -e> inl (VLiteral (Integer 42)).
Proof.
  eapply eval_apply with (vals := []) (ref := inr ("fun1"%string, 0)) (body := (EApply (EFunSig ("fun3"%string, 0)) [])) (var_list := []). 
  * reflexivity.
  * apply eval_funsig.
  * reflexivity.
  * simpl. intros. inversion H.
  * simpl. apply eval_apply with (vals := []) (ref := inr ("fun3"%string, 0)) (body := (EApply (EFunSig ("fun2"%string, 0)) [])) (var_list := []).
    - reflexivity.
    - apply eval_funsig.
    - reflexivity.
    - intros. inversion H.
    - simpl. apply eval_apply with (vals := []) (ref := inr ("fun2"%string, 0)) (body := (ELiteral (Integer 42))) (var_list := []).
      + reflexivity.
      + apply eval_funsig.
      + reflexivity.
      + intros. inversion H.
      + apply eval_lit.
Qed.

Example top_overwrite : |[(inr ("fun1"%string, 0), VClosure (inr ("fun1"%string, 0)) [] (ELiteral (Integer 42)))],
[(("fun1"%string, 0), [(inr ("fun1"%string, 0), VClosure (inr ("fun1"%string, 0)) [] (ELiteral (Integer 42)))]) ],
  ELetrec [("fun1"%string, 0)] [[]] [ELiteral (Integer 40)] (EApply (EFunSig ("fun1"%string, 0)) []) | -e> inl (VLiteral (Integer 40)).
Proof.
  apply eval_letrec; auto.
  * simpl. apply eval_apply with (vals := []) (ref := inr ("fun1"%string, 0)) (body := (ELiteral (Integer 40))) (var_list := []); auto.
    - apply eval_funsig.
    - intros. inversion H.
    - apply eval_lit.
Qed.

Example top_no_overwrite : |[(inr ("fun2"%string, 0), VClosure (inr ("fun2"%string, 0)) [] (ELiteral (Integer 42))) ]
                       ,[(("fun2"%string, 0), [(inr ("fun2"%string, 0), VClosure (inr ("fun2"%string, 0)) [] (ELiteral (Integer 42)))])]
                       , ELetrec [("fun2"%string, 1)] [["X"%string]] [(ELiteral (Integer 40))] (EApply (EFunSig ("fun2"%string, 0)) []) | -e> inl (VLiteral (Integer 42)).
Proof.
  apply eval_letrec; auto.
  * simpl. apply eval_apply with (vals := []) (ref := (inr ("fun2"%string, 0))) (body := ELiteral (Integer 42)) (var_list := []).
    - reflexivity.
    - apply eval_funsig.
    - reflexivity.
    - intros. inversion H.
    - apply eval_lit.
Qed.

(* This is not accepted by the compiler *)
Example eval_let_func : |[(inl "X"%string, VLiteral (Integer 42))], [], ELet ["X"%string; "X"%string] [EFun [] (ELiteral EmptyList); EFun [] (ELiteral EmptyMap)] (ELiteral EmptyMap)| -e> inl (VLiteral EmptyMap).
Proof.
  apply eval_let with (vals := [VClosure (inl [(inl "X"%string, VLiteral (Integer 42))]) [] (ELiteral EmptyList); 
                                VClosure (inl [(inl "X"%string, VLiteral (Integer 42))]) [] (ELiteral EmptyMap)]).
  * simpl. reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. apply eval_fun.
    - inversion H0.
      + inversion H1. apply eval_fun.
      + inversion H1.
  * simpl. apply eval_lit.
Qed.

Example eval_let_apply : |[(inl "X"%string, VLiteral (Integer 42))], [], ELet ["Y"%string] [EFun [] (EVar "X"%string)] (EApply (EVar "Y"%string) [])| -e> inl (VLiteral (Integer 42)).
Proof.
  apply eval_let with (vals := [VClosure (inl [(inl "X"%string, VLiteral (Integer 42))]) [] (EVar "X"%string)]).
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. apply eval_fun.
    - inversion H0.
  * simpl. apply eval_apply with (vals := []) (ref := inl [(inl "X"%string, VLiteral (Integer 42))]) (body := (EVar "X"%string)) (var_list := []).
    - reflexivity.
    - apply eval_var.
    - reflexivity.
    - simpl. intros. inversion H.
    - apply eval_var.
Qed.

Example eval_muliple_let : |[], [], ELet ["X"%string] [ELiteral (Integer 1)] (ELet ["X"%string] [ELiteral (Integer 2)] (EVar "X"%string))| -e> inl (VLiteral (Integer 2)).
Proof.
  apply eval_let with (vals := [VLiteral (Integer 1)]).
  * reflexivity.
  * intros. inversion H.
    - inversion H0. apply eval_lit.
    - inversion H0.
  * simpl. apply eval_let with (vals := [VLiteral (Integer 2)]).
    - reflexivity.
    - simpl. intros. inversion H.
      + inversion H0. apply eval_lit.
      + inversion H0.
    - apply eval_var.
Qed.

Example let_eval_1 : |[], [], ELet ["X"%string] [ELiteral EmptyTuple] (ELiteral EmptyMap)| -e> inl (VLiteral EmptyMap).
Proof.
  apply eval_let with (vals := [VLiteral EmptyTuple]).
  * reflexivity.
  * intros. simpl in *. inversion H.
    - inversion H0. apply eval_lit.
    - inversion H0.
  * simpl. apply eval_lit.
Qed.

Example let_eval_2 : |[(inl "X"%string, VLiteral EmptyMap)], [], ELet ["X"%string] [ELiteral EmptyTuple] (ELiteral EmptyMap)| -e> inl (VLiteral EmptyMap).
Proof.
  apply eval_let with (vals := [VLiteral EmptyTuple]).
  * reflexivity.
  * intros. simpl in *. inversion H.
    - inversion H0. apply eval_lit.
    - inversion H0.
  * simpl. apply eval_lit.
Qed.

(* This shouldn't compile *)
Example eval_let_3 : |[(inl "X"%string, VLiteral EmptyMap)], [], ELet ["X"%string; "X"%string; "Y"%string] [ELiteral EmptyTuple; ELiteral EmptyList; EVar "X"%string] (EVar "Y"%string)| -e> inl (VLiteral EmptyMap).
Proof.
  apply eval_let with (vals := [(VLiteral EmptyTuple) ; (VLiteral EmptyList); (VLiteral EmptyMap)]).
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. apply eval_lit.
    - inversion H0.
      + inversion H1. apply eval_lit.
      + inversion H1.
        ** inversion H2. apply eval_var.
        ** inversion H2.
  * simpl. apply eval_var.
Qed.

Example let_eval_4 : |[], [], ELet ["X"%string] [ELiteral (Integer 5)] (EVar "X"%string)| -e> inl (VLiteral (Integer 5)).
Proof.
  apply eval_let with (vals := [VLiteral (Integer 5)]).
  * reflexivity.
  * intros. simpl in *. inversion H.
    - inversion H0. apply eval_lit.
    - inversion H0.
  * simpl. apply eval_var.
Qed.

Example tuple_eval : |[(inl "X"%string, VLiteral (Atom "asd"%string)); (inl "Y"%string, VLiteral EmptyTuple)], [], ETuple [ELiteral (Integer 5); EVar "X"%string; EVar "Y"%string]| -e> 
                      inl (VTuple [VLiteral (Integer 5); VLiteral (Atom "asd"%string); VLiteral EmptyTuple]).
Proof.
  apply eval_tuple.
  * reflexivity.
  * intros. inversion H.
    - inversion H0. apply eval_lit.
    - inversion H0.
      + inversion H1. apply eval_var.
      + inversion H1.
        ** inversion H2. apply eval_var.
        ** inversion H2.
Qed.

Example apply_top_eval : |[(inr ("Plus"%string, 2), VClosure (inr ("Plus"%string, 2)) ["X"%string ; "Y"%string] (ELiteral (Integer 3)))], [], EApply (EFunSig ("Plus"%string, 2)) [ELiteral (Integer 2); ELiteral (Integer 3)]| -e> inl ((VLiteral (Integer 3))).
Proof.
  apply eval_apply with (vals := [VLiteral (Integer 2) ; VLiteral (Integer 3)]) (var_list := ["X"%string; "Y"%string]) (body := ELiteral (Integer 3)) (ref := inr ("Plus"%string, 2)).
  * reflexivity.
  * apply eval_funsig.
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. apply eval_lit.
    - inversion H0.
      + inversion H1. apply eval_lit.
      + inversion H1.
  * simpl. apply eval_lit.
Qed.

Example apply_eval : |[(inl "Minus"%string, VClosure (inl []) ["X"%string; "Y"%string] (ELiteral (Integer 42))) ; (inl "X"%string, VLiteral EmptyMap)], [], EApply (EVar "Minus"%string) [EVar "X"%string; EVar "X"%string]| -e> inl (VLiteral (Integer 42)).
Proof.
  apply eval_apply with (vals := [VLiteral EmptyMap; VLiteral EmptyMap]) (var_list := ["X"%string; "Y"%string]) (body := (ELiteral (Integer 42))) (ref := inl []).
  * reflexivity.
  * apply eval_var.
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. apply eval_var.
    - inversion H0.
      + inversion H1. apply eval_var.
      + inversion H1.
  * simpl. apply eval_lit.
Qed.


Example list_eval : |[(inl "X"%string, VLiteral (Integer 5))], [], EList (EVar "X"%string) (ELiteral EmptyList)| -e> inl (VList (VLiteral (Integer 5)) (VLiteral EmptyList)).
Proof.
  apply eval_list.
  * apply eval_var.
  * apply eval_lit.
Qed.

Example list_eval2 : |[(inl "X"%string, VLiteral (Integer 5))], [], EList (EVar "X"%string) (EList (EVar "X"%string) (ELiteral EmptyList))| -e> inl (VList (VLiteral (Integer 5)) (VList (VLiteral (Integer 5)) (VLiteral EmptyList))).
Proof.
  apply eval_list.
  * apply eval_var.
  * apply eval_list.
    - apply eval_var.
    - apply eval_lit.
Qed.

Example let_eval_overwrite : |[], [], ELet ["X"%string] [EFun [] (ELiteral EmptyTuple)] (ELet ["X"%string] [ELiteral (Integer 5)] (EVar "X"%string))| -e> inl (VLiteral (Integer 5)).
Proof.
  apply eval_let with (vals := [VClosure (inl []) [] (ELiteral EmptyTuple)]).
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. apply eval_fun.
    - inversion H0.
  * simpl. apply eval_let with (vals := [VLiteral (Integer 5)]).
    - reflexivity.
    - simpl. intros. inversion H.
      + inversion H0. apply eval_lit.
      + inversion H0.
    - simpl. apply eval_var.
Qed.

(* Example map_eval : |[(inl "X"%string, VLiteral (Integer 42))], [], EMap [ELiteral (Integer 5)] [EVar "X"%string]| -e> inl (VMap [VLiteral (Integer 5)] [VLiteral (Integer 42)]).
Proof.
  apply eval_map.
  1-3: reflexivity.
  * intros. inversion H.
    - inversion H0. subst. split. apply eval_lit. apply eval_var.
    - inversion H0.
Qed.

Example map_eval2 : |[(inl "X"%string, VLiteral (Integer 42))], [], EMap [ELiteral (Integer 5); EVar "X"%string] [EVar "X"%string; EVar "X"%string]| -e> inl (VMap [VLiteral (Integer 5); VLiteral (Integer 42)] [VLiteral (Integer 42); VLiteral (Integer 42)]).
Proof.
  apply eval_map.
  1-3: reflexivity.
  * intros. inversion H.
    - inversion H0. split. apply eval_lit. apply eval_var.
    - inversion H0; inversion H1. split. apply eval_var. apply eval_var.
Qed. *)

(** Function parameter always overwrites everything *)
Example let_closure_apply_eval_without_overwrite :
|[], [], ELet ["X"%string] [ELiteral (Integer 42)] (ELet ["Y"%string] [EFun ["X"%string] (EVar "X"%string)] (ELet ["X"%string] [ELiteral (Integer 5)] (EApply (EVar "Y"%string) [ELiteral (Integer 7)])))| -e> inl (VLiteral (Integer 7)).
Proof.
  apply eval_let with (vals := [VLiteral (Integer 42)]).
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. apply eval_lit.
    - inversion H0.
  * simpl. apply eval_let with (vals := [VClosure (inl [(inl "X"%string, VLiteral (Integer 42))]) ["X"%string] (EVar "X"%string)]).
    - reflexivity.
    - simpl. intros. inversion H.
      + inversion H0. apply eval_fun.
      + inversion H0.
    - simpl. apply eval_let with (vals := [VLiteral (Integer 5)]).
      + reflexivity.
      + simpl. intros. inversion H.
        ** inversion H0. apply eval_lit.
        ** inversion H0.
      + simpl. apply eval_apply with (vals := [VLiteral (Integer 7)]) (ref := (inl [(inl "X"%string, VLiteral (Integer 42))])) (body := (EVar "X"%string)) (var_list := ["X"%string]).
        ** reflexivity.
        ** simpl. intros. apply eval_var.
        ** reflexivity.
        ** intros. inversion H.
          -- inversion H0. apply eval_lit.
          -- inversion H0.
        ** apply eval_var.
Qed.


(** Example to test that value overwriting does not affect the value in the closure *)
Example let_closure_apply_eval_without_overwrite2 :
|[], [], ELet ["X"%string] [ELiteral (Integer 42)] (ELet ["Y"%string] [EFun [] (EVar "X"%string)] (ELet ["X"%string] [ELiteral (Integer 5)] (EApply (EVar "Y"%string) [])))| -e> inl (VLiteral (Integer 42)).
Proof.
  apply eval_let with (vals := [VLiteral (Integer 42)]).
  * reflexivity.
  * intros. inversion H; inversion H0.
    - apply eval_lit.
  * simpl. apply eval_let with (vals := [VClosure (inl [(inl "X"%string, VLiteral (Integer 42))]) [] (EVar "X"%string)]).
    - reflexivity.
    - intros. inversion H; inversion H0.
      + apply eval_fun. 
    - apply eval_let with (vals := [VLiteral (Integer 5)]).
      + reflexivity.
      + intros. inversion H; inversion H0.
        ** apply eval_lit.
      + simpl. apply eval_apply with (vals := []) (var_list := []) (body := (EVar "X"%string)) (ref := (inl [(inl "X"%string, VLiteral (Integer 42))])).
        ** reflexivity.
        ** apply eval_var.
        ** reflexivity.
        ** intros. inversion H.
        ** apply eval_var.
Qed.

Example call_eval : |[(inl "X"%string, VLiteral (Integer 5))], [], ECall "plus"%string [EVar "X"%string ; ELiteral (Integer 2)]| -e> inl (VLiteral (Integer 7)).
Proof.
  apply eval_call with (vals := ([VLiteral (Integer 5) ; VLiteral (Integer 2)])).
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. apply eval_var.
    - inversion H0.
      + inversion H1. apply eval_lit.
      + inversion H1.
  * reflexivity.
Qed.

Example mutliple_function_let : |[], [], ELet ["Z"%string] [ECall "plus"%string [ELiteral (Integer 2) ; ELiteral (Integer 2)] ] (ELet ["Y"%string] [EFun [] (EVar "Z"%string)] (ELet ["X"%string] [EFun [] (EApply (EVar "Y"%string) [])] (EApply (EVar "X"%string) [])))| -e> inl (VLiteral (Integer 4)).
Proof.
  apply eval_let with (vals := [VLiteral (Integer 4)]).
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. apply eval_call with (vals := [VLiteral (Integer 2); VLiteral (Integer 2)]).
      + reflexivity.
      + simpl. intros. inversion H1.
        ** inversion H4. apply eval_lit.
        ** inversion H4.
          -- inversion H5. apply eval_lit.
          -- inversion H5.
      + simpl. reflexivity.
    - inversion H0.
  * simpl. apply eval_let with (vals := [VClosure (inl [(inl "Z"%string, VLiteral (Integer 4))]) [] (EVar "Z"%string)]).
    - reflexivity.
    - simpl. intros. inversion H.
      + inversion H0. apply eval_fun.
      + inversion H0.
    - simpl. apply eval_let with (vals := [VClosure (inl [(inl "Z"%string, VLiteral (Integer 4));
  (inl "Y"%string,
  VClosure (inl [(inl "Z"%string, VLiteral (Integer 4))]) []
    (EVar "Z"%string))]) [] (EApply (EVar "Y"%string) [])]).
      + reflexivity.
      + simpl. intros. inversion H.
        ** inversion H0. apply eval_fun.
        ** inversion H0.
      + simpl. apply eval_apply with (vals := []) (var_list := []) (body := (EApply (EVar "Y"%string) [])) (ref := inl [(inl "Z"%string, VLiteral (Integer 4));
       (inl "Y"%string,
       VClosure (inl [(inl "Z"%string, VLiteral (Integer 4))]) []
         (EVar "Z"%string))]).
        ** reflexivity.
        ** simpl. apply eval_var.
        ** reflexivity.
        ** simpl. intros. inversion H.
        ** simpl. apply eval_apply with (vals := []) (var_list := []) (body := (EVar "Z"%string)) (ref := (inl [(inl "Z"%string, VLiteral (Integer 4))])).
          -- reflexivity.
          -- apply eval_var.
          -- reflexivity.
          -- intros. inversion H.
          -- simpl. apply eval_var.
Qed.

Example case_eval : |[(inl "X"%string, VLiteral EmptyTuple)],[], 
  ECase (EVar "X"%string) 
        [(PLiteral (Integer 5)); (PLiteral (Integer 6)); (PVar "Z"%string) ]
        [(ELiteral (Atom "true"%string)); (ELiteral (Atom "true"%string)); (ELiteral (Atom "true"%string))]
        [(ELiteral (Integer 5)); (ELiteral (Integer 6)); (EVar "Z"%string)]| 
-e> inl (VLiteral EmptyTuple).
Proof.
  eapply eval_case with (i := 2) (v := VLiteral EmptyTuple); auto.
  * apply eval_var.
  * simpl. reflexivity.
  * intros. inversion H.
    - subst. inversion H0.
    - inversion H2.
      + subst. inversion H0.
      + subst. inversion H4.
  * simpl. apply eval_lit.
  * simpl. apply eval_var.
Qed.

Example case_eval2 : |[(inl "X"%string, VLiteral EmptyTuple)],[], 
  ECase (EVar "X"%string) 
         [(PLiteral (Integer 5)); (PLiteral (Integer 6)); (PVar "Z"%string); (PVar "Z"%string)]
         [(ELiteral (Atom "true"%string)); (ELiteral (Atom "true"%string)); (ELiteral (Atom "false"%string)); (ELiteral (Atom "true"%string))]
         [(ELiteral (Integer 5)); (ELiteral (Integer 6)); (EVar "Z"%string); (ELiteral EmptyMap)]| 
-e> inl (VLiteral EmptyMap).
Proof.
  eapply eval_case with (i := 3) (v := VLiteral EmptyTuple); auto.
  * apply eval_var.
  * simpl. reflexivity.
  * intros. inversion H.
    - subst. inversion H0. apply eval_lit.
    - inversion H2.
      + subst. inversion H0.
      + inversion H4.
        ** subst. inversion H0.
        ** inversion H6.
  * apply eval_lit.
  * apply eval_lit.
Qed.

Example case_eval_fun : |[(inl "X"%string, VClosure (inl [(inl "Y"%string, ttrue)]) [] (EVar "Y"%string))], [], 
  ECase (EVar "X"%string) 
        [(PLiteral (Integer 5)); (PLiteral (Integer 6)); (PVar "Z"%string)] 
        [(ELiteral (Atom "true"%string)); (ELiteral (Atom "true"%string)); (ELiteral (Atom "true"%string))] 
        [(ELiteral (Integer 5)); (ELiteral (Integer 6)); (EApply (EVar "Z"%string) [])]| 
-e> inl (ttrue).
Proof.
  eapply eval_case with (i := 2) (v := VClosure (inl [(inl "Y"%string, ttrue)]) [] (EVar "Y"%string)); auto.
  * apply eval_var.
  * simpl. reflexivity.
  * intros. inversion H.
    - subst. inversion H0.
    - inversion H2.
      + subst. inversion H0.
      + inversion H4.
  * apply eval_lit.
  * simpl. apply eval_apply with (vals := []) (var_list := []) (ref := (inl [(inl "Y"%string, ttrue)])) (body := (EVar "Y"%string)); auto.
   - apply eval_var.
   - intros. inversion H.
   - simpl. apply eval_var.
Qed.


Example letrec_eval : |[(inr ("fun4"%string, 0), VClosure (inr ("fun4"%string, 0)) [] (ELiteral EmptyMap)) ; (inl "X"%string, VLiteral (Integer 42))], [], ELetrec [("fun2"%string, 0); ("fun4"%string, 1)] [[]; ["Z"%string]] [(EVar "X"%string) ; (EVar "Z"%string)] (EApply (EFunSig ("fun4"%string, 0)) [])| -e> inl (VLiteral EmptyMap).
Proof.
  apply eval_letrec; try (reflexivity).
  * simpl. apply eval_apply with (vals := []) (var_list := []) (body := (ELiteral EmptyMap)) (ref := (inr ("fun4"%string,0))); try (reflexivity).
    - apply eval_funsig.
    - simpl. intros. inversion H.
    - simpl. apply eval_lit.
Qed.


Example unnamed_eval : |[(inl "X"%string, VLiteral (Integer 5))], [], EApply (EFun ["Y"%string] (EVar "Y"%string)) [EVar "X"%string]| -e> inl (VLiteral (Integer 5)).
Proof.
  apply eval_apply with (vals := [VLiteral (Integer 5)]) (var_list := ["Y"%string]) (body := (EVar "Y"%string)) (ref := inl [(inl "X"%string, VLiteral (Integer 5))]).
  * reflexivity.
  * apply eval_fun.
  * reflexivity.
  * intros. inversion H; inversion H0. apply eval_var.
  * simpl. apply eval_var.
Qed.


Section B_Core.

Definition B : ErlModule := ErlMod "b"%string [
  TopLevelFun ("fun1"%string, 0) ([], (ELiteral (Integer 6))) ;
  TopLevelFun ("fun2"%string, 0) ([], (ELet ["X"%string] [(EFun [] (ELiteral (Integer 5)))] (ELet ["X"%string] [(EFun [] (ELiteral (Integer 6)))] (EApply (EVar "X"%string) []))) )
].


Example fun2 : |[], [], ELet ["X"%string] [(EFun [] (ELiteral (Integer 5)))] (ELet ["X"%string] [(EFun [] (ELiteral (Integer 6)))] (EApply (EVar "X"%string) []))| -e> inl (VLiteral (Integer 6)).
Proof.
  apply eval_let with (vals := [VClosure (inl []) [] (ELiteral (Integer 5))]).
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. apply eval_fun.
    - inversion H0.
  * simpl. apply eval_let with (vals := [VClosure (inl [(inl "X"%string, VClosure (inl []) [] (ELiteral (Integer 5)))]) [] (ELiteral (Integer 6))]).
    - reflexivity.
    - simpl. intros. inversion H.
      + inversion H0. apply eval_fun.
      + inversion H0.
    - simpl. apply eval_apply with (vals := []) (var_list := []) (body := (ELiteral (Integer 6))) (ref := (inl [(inl "X"%string, VClosure (inl []) [] (ELiteral (Integer 5)))])).
      + reflexivity.
      + apply eval_var.
      + reflexivity.
      + intros. inversion H.
      + apply eval_lit.
Qed.

Compute initialize_proving B.

Compute initialize_proving_closures B.

End B_Core.

Section Documentation_Examples.

Example ex1 : |[], [], ELet ["X"%string] [ELiteral (Integer 5)] (EVar "X"%string)| -e> inl (VLiteral (Integer 5)).
Proof.
  apply eval_let with ([VLiteral (Integer 5)]).
  * reflexivity.
  * intros. inversion H.
    - inversion H0. subst. apply eval_lit.
    - inversion H0.
  * simpl. apply eval_var.
Qed.

Example ex2 : |[], [], ELet ["X"%string] [EFun [] (EApply (EVar "X"%string) [])] (EApply (EVar "X"%string) [])| -e> inl ErrorValue.
Proof.
  apply eval_let with ([VClosure (inl []) [] (EApply ( EVar "X"%string) [])]).
  * reflexivity.
  * intros. inversion H.
    - inversion H0. subst. apply eval_fun.
    - inversion H0.
  * simpl. apply eval_apply with (vals := []) (var_list := []) (body := (EApply (EVar "X"%string) [])) (ref := (inl [])).
    - reflexivity.
    - apply eval_var.
    - reflexivity.
    - intros. inversion H.
    - simpl. eapply eval_apply with (vals := []).
      + reflexivity.
      + admit. (* eapply eval_var.*)
      + shelve.
      + intros. inversion H.
      + simpl. apply eval_lit.
  Unshelve.
  exact [].
  exact (inl []).
Admitted.

Example ex3 :  |[], [], ELetrec [("X"%string, 0)] [[]] [(EApply (EFunSig ("X"%string, 0)) [])] (EApply (EFunSig ("X"%string, 0)) [])| -e> inl (VLiteral EmptyTuple).
Proof.
  apply eval_letrec; try (reflexivity).
  * simpl. eapply eval_apply with (vals := []) (var_list := []) (body := (EApply (EFunSig ("X"%string, 0)) [])) (ref := (inr ("X"%string, 0))); try (reflexivity).
    - apply eval_funsig.
    - intros. inversion H.
    - simpl. eapply eval_apply with (vals := []) (var_list := []) (body := (EApply (EFunSig ("X"%string, 0)) [])) (ref := (inr ("X"%string, 0))); try (reflexivity).
      + apply eval_funsig.
      + intros. inversion H.
      + simpl. eapply eval_apply with (vals := []) (var_list := []) (body := (EApply (EFunSig ("X"%string, 0)) [])) (ref := (inr ("X"%string, 0))); try (reflexivity).
        ** apply eval_funsig.
        ** intros. inversion H.
        ** simpl.
Admitted.

End Documentation_Examples.

Example ex4 : |[], [], ELet ["X"%string] [ELiteral (Integer 4)] 
                         (ELet ["X"%string] [EFun [] (EVar "X"%string)] 
                           (ELet ["X"%string] [EFun [] (EApply (EVar "X"%string) [])] 
                             (EApply (EVar "X"%string) [])))| -e> inl (VLiteral (Integer 4)).
Proof.
  apply eval_let with ([VLiteral (Integer 4)]).
  * reflexivity.
  * intros. inversion H; inversion H0. apply eval_lit.
  * simpl. apply eval_let with ([VClosure (inl [(inl "X"%string, VLiteral (Integer 4))]) [] (EVar "X"%string)]).
    - reflexivity.
    - intros. inversion H; inversion H0. apply eval_fun.
    - simpl. apply eval_let with ([VClosure (inl [(inl "X"%string,
   VClosure (inl [(inl "X"%string, VLiteral (Integer 4))]) []
     (EVar "X"%string))]) [] (EApply (EVar "X"%string) []) ]).
       + reflexivity.
       + intros. inversion H; inversion H0. apply eval_fun.
       + simpl. apply eval_apply with (vals := []) (var_list := []) (body := EApply (EVar "X"%string) []) (ref := inl [(inl "X"%string,
         VClosure (inl [(inl "X"%string, VLiteral (Integer 4))]) []
           (EVar "X"%string))]).
         ** reflexivity.
         ** apply eval_var.
         ** reflexivity.
         ** intros. inversion H.
         ** simpl. apply eval_apply with (vals := []) (var_list := []) (body := EVar "X"%string) (ref := inl [(inl "X"%string, VLiteral (Integer 4))]).
           -- reflexivity.
           -- apply eval_var.
           -- reflexivity.
           -- intros. inversion H.
           -- apply eval_var.
Qed.

Example returned_function : |[], [], ELet ["X"%string] [EFun [] (EFun [] (ELiteral (Integer 5)))] (EApply (EApply (EVar "X"%string) []) [])| -e> inl (VLiteral (Integer 5)).
Proof.
  apply eval_let with ([VClosure (inl []) [] (EFun [] (ELiteral (Integer 5)))]).
  * reflexivity.
  * intros. inversion H; inversion H0. apply eval_fun.
  * simpl. apply eval_apply with (vals := []) (ref := inl []) (body := ELiteral (Integer 5)) (var_list := []).
    - reflexivity.
    - apply eval_apply with (vals := []) (var_list := []) (body := EFun [] (ELiteral (Integer 5))) (ref := inl []).
      + reflexivity.
      + apply eval_var.
      + reflexivity.
      + intros. inversion H.
      + simpl. apply eval_fun.
    - reflexivity.
    - intros. inversion H.
    - apply eval_lit.
Qed.

Example returned_recursive_function : |[], [], ELetrec [("fun1"%string, 0)] [[]] [(EFun [] (ELiteral (Integer 5)))] (EApply (EApply (EFunSig ("fun1"%string, 0)) []) [])| -e> inl (VLiteral (Integer 5)).
Proof.
  apply eval_letrec; try (reflexivity).
  * simpl. apply eval_apply with (vals := []) (ref := inl [(inr ("fun1"%string, 0),
   VClosure (inr ("fun1"%string, 0)) []
     (EFun [] (ELiteral (Integer 5))))]) (body := ELiteral (Integer 5)) (var_list := []); try (reflexivity).
    - apply eval_apply with (vals := []) (var_list := []) (body := EFun [] (ELiteral (Integer 5))) (ref := inr ("fun1"%string, 0)); try (reflexivity).
      + apply eval_funsig.
      + intros. inversion H.
      + simpl. apply eval_fun.
    - intros. inversion H.
    - apply eval_lit.
Qed.

Example returned_function2 : |[(inl "X"%string, VLiteral (Integer 7))], [], ELet ["X"%string] [EFun [] (EFun [] (EVar "X"%string))] (EApply (EApply (EVar "X"%string) []) [])| -e> inl (VLiteral (Integer 7)).
Proof.
  apply eval_let with ([VClosure (inl [(inl "X"%string, VLiteral (Integer 7))]) [] (EFun [] (EVar "X"%string))]).
  * reflexivity.
  * intros. inversion H; inversion H0. apply eval_fun.
  * simpl. apply eval_apply with (vals := []) (ref := inl [(inl "X"%string, VLiteral (Integer 7))]) (body := EVar "X"%string) (var_list := []).
    - reflexivity.
    - apply eval_apply with (vals := []) (var_list := []) (body := EFun [] (EVar "X"%string)) (ref := inl [(inl "X"%string, VLiteral (Integer 7))]).
      + reflexivity.
      + apply eval_var.
      + reflexivity.
      + intros. inversion H.
      + simpl. apply eval_fun.
    - reflexivity.
    - intros. inversion H.
    - simpl. apply eval_var.
Qed.

Example returned_recursive_function2 : |[(inl "X"%string, VLiteral (Integer 7))], [], ELetrec [("fun1"%string, 0)] [[]] [(EFun [] (EVar "X"%string))] (EApply (EApply (EFunSig ("fun1"%string, 0)) []) [])| -e> inl (VLiteral (Integer 7)).
Proof.
  apply eval_letrec; try (reflexivity).
  * simpl. apply eval_apply with (vals := []) (ref := inl [(inl "X"%string, VLiteral (Integer 7)) ; (inr ("fun1"%string, 0),
   VClosure (inr ("fun1"%string, 0)) [] (EFun [] (EVar "X"%string)))]) (body := EVar "X"%string) (var_list := []); try (reflexivity).
    - apply eval_apply with (vals := []) (var_list := []) (body := EFun [] (EVar "X"%string)) (ref := inr ("fun1"%string, 0)); try (reflexivity).
      + apply eval_funsig.
      + intros. inversion H.
      + simpl. apply eval_fun.
    - intros. inversion H.
    - simpl. apply eval_var.
Qed.

Example returned_function3 : |[], [], ELet ["F"%string] [
  EFun ["X"%string] (ELet ["Y"%string] [ECall "plus"%string [EVar "X"%string; ELiteral (Integer 3)] ] 
    (EFun ["Z"%string] (ECall "plus"%string [ECall "plus"%string [EVar "X"%string; EVar "Y"%string] ; EVar "Z"%string])))
] (EApply (EApply (EVar "F"%string) [ELiteral (Integer 1)]) [ELiteral (Integer 1)])| -e> inl (VLiteral (Integer 6)).
Proof.
  apply eval_let with ([VClosure (inl []) ["X"%string] (ELet ["Y"%string]
        [ECall "plus"
           [EVar "X"%string; ELiteral (Integer 3)] ]
        (EFun ["Z"%string]
           (ECall "plus"
              [ECall "plus"
                 [EVar "X"%string; EVar "Y"%string];
              EVar "Z"%string])))]).
  * reflexivity.
  * intros. inversion H; inversion H0. apply eval_fun.
  * simpl. apply eval_apply with (var_list := ["Z"%string]) (body := (ECall "plus"
              [ECall "plus"
                 [EVar "X"%string; EVar "Y"%string];
              EVar "Z"%string])) (ref := inl [(inl "X"%string, VLiteral (Integer 1)); (inl "Y"%string, VLiteral (Integer 4))]) (vals := [VLiteral (Integer 1)]).
    - reflexivity.
    - apply eval_apply with (vals := [VLiteral (Integer 1)]) (var_list := ["X"%string]) (body := ELet ["Y"%string]
        [ECall "plus"
           [EVar "X"%string; ELiteral (Integer 3)] ]
        (EFun ["Z"%string]
           (ECall "plus"
              [ECall "plus"
                 [EVar "X"%string; EVar "Y"%string];
              EVar "Z"%string]))) (ref := inl []).
      + reflexivity.
      + apply eval_var.
      + reflexivity.
      + intros. inversion H; inversion H0. apply eval_lit.
      + apply eval_let with ([VLiteral (Integer 4)]).
        ** reflexivity.
        ** intros. inversion H; inversion H0. apply eval_call with ([VLiteral (Integer 1); VLiteral (Integer 3)]).
          -- reflexivity.
          -- intros. inversion H1.
            ++ inversion H4. apply eval_var.
            ++ inversion H4; inversion H5. apply eval_lit.
          -- simpl. reflexivity.
        ** simpl. apply eval_fun.
    - reflexivity.
    - intros. inversion H; inversion H0. apply eval_lit.
    - apply eval_call with [VLiteral (Integer 5) ; VLiteral (Integer 1)].
      + reflexivity.
      + intros. inversion H.
        ** inversion H0. apply eval_call with [VLiteral (Integer 1) ; VLiteral (Integer 4)].
          -- reflexivity.
          -- intros. inversion H1.
            ++ inversion H4. apply eval_var.
            ++ inversion H4; inversion H5. apply eval_var.
          -- simpl. reflexivity.
        ** simpl. inversion H0; inversion H1. apply eval_var.
      + simpl. reflexivity.
Qed.

Section Exception_Examples.

Example exception_var : |[], [], EVar "X"%string| -e> inr novar.
Proof.
  apply eval_var.
Qed.

Example exception_list_hd : |[], [], EList (EVar "X"%string) (ErrorExp)| -e> inr novar.
Proof.
  apply eval_list_ex_hd.
  apply eval_var.
Qed.

Example exception_list_tl : |[], [], EList (ErrorExp) (EList (EVar "X"%string) (ELiteral EmptyList))| -e> inr novar.
Proof.
  apply eval_list_ex_tl with ErrorValue.
  * apply eval_lit. 
  * apply eval_list_ex_hd. apply eval_var.
Qed.

Example exception_tuple : |[], [], ETuple [ErrorExp ; ErrorExp; EVar "X"%string]| -e> inr novar.
Proof.
  apply eval_tuple_ex with (i := 2) (vals := [ErrorValue; ErrorValue]).
  * simpl. auto.
  * simpl. auto.
  * intros. inversion H.
    - simpl. apply eval_lit.
    - inversion H1.
      + simpl. apply eval_lit.
      + inversion H3.
  * simpl. apply eval_var.
Qed.

Example try_eval : |[], [], ETry (ELiteral EmptyTuple) 
                                 (ELiteral (Atom "ok"%string)) 
                                 (ELiteral (Atom "error"%string)) 
                                 "X"%string "Ex1"%string "Ex2"%string "Ex3"%string| -e> inl ok
.
Proof.
  apply eval_try with (VLiteral EmptyTuple).
  * apply eval_lit.
  * simpl. apply eval_lit.
Qed.

Example try_eval_catch : |[], [], ETry (EVar "Z"%string) 
                                  (ELiteral (Atom "ok"%string)) 
                                  (ELiteral (Atom "error"%string)) 
                                  "X"%string "Ex1"%string "Ex2"%string "Ex3"%string| -e> inl (VLiteral (Atom "error"%string))
.
Proof.
  apply eval_try_catch with novar.
  * apply eval_var.
  * simpl. apply eval_lit.
Qed.

Example try_eval_exception : |[], [], ETry (EVar "Z"%string) 
                                           (ELiteral (Atom "ok"%string)) 
                                           (EVar "Z"%string) 
                                            "X"%string "Ex1"%string "Ex2"%string "Ex3"%string| -e> inr novar
.
Proof.
  apply eval_try_catch with novar.
  * apply eval_var.
  * simpl. apply eval_var.
Qed.

Example try_eval_exception2 : |[], [], ETry (ELiteral EmptyTuple)
                                 (EVar "Z"%string)
                                 (ELiteral (Atom "error"%string)) 
                                 "X"%string "Ex1"%string "Ex2"%string "Ex3"%string| -e> inr novar
.
Proof.
  apply eval_try with (VLiteral EmptyTuple).
  * apply eval_lit.
  * simpl. apply eval_var.
Qed.

Example call_eval_body_ex : |[], [], ECall "plus"%string []| -e> inr badarith.
Proof.
  apply eval_call with [].
  * reflexivity.
  * intros. inversion H.
  * simpl. reflexivity.
Qed.

Example call_eval_body_ex2 : |[], [], ECall "plus"%string [ELiteral (Integer 5); ELiteral (EmptyTuple)]| -e> inr badarith.
Proof.
  apply eval_call with [VLiteral (Integer 5); VLiteral EmptyTuple].
  * reflexivity.
  * intros. inversion H; inversion H0.
    - apply eval_lit.
    - inversion H1. apply eval_lit.
    - inversion H1.
  * simpl. reflexivity.
Qed.

Example call_eval_param_ex : |[], [], ECall "plus"%string [ELiteral (Integer 5); EVar "Y"%string]| -e> inr novar.
Proof.
  apply eval_call_ex with (i := 1) (vals := [VLiteral (Integer 5)]).
  * simpl. auto.
  * simpl. auto.
  * intros. inversion H.
    - apply eval_lit.
    - inversion H1.
  * apply eval_var.
Qed.

Example let_eval_exception_params : |[], [], ELet ["X"%string; "Y"%string] [ELiteral (Integer 5); EVar "Y"%string] (ELiteral EmptyTuple)| -e> inr novar.
Proof.
  apply eval_let_ex_param with (i := 1) (vals := [VLiteral (Integer 5)]).
  * reflexivity.
  * simpl. auto.
  * intros. inversion H.
    - simpl. apply eval_lit.
    - inversion H1.
  * simpl. apply eval_var.
Qed.

Example let_eval_exception_body : |[], [], ELet ["X"%string; "Y"%string] [ELiteral (Integer 5); ELiteral (Integer 5)] (EVar "C"%string)| -e> inr novar.
Proof.
  apply eval_let with (vals := [VLiteral (Integer 5); VLiteral (Integer 5)]).
  * reflexivity.
  * intros. inversion H.
    - inversion H0. simpl. apply eval_lit.
    - inversion H0; inversion H1. apply eval_lit.
  * simpl. apply eval_var.
Qed.

Example apply_eval_exception_closure : |[], [], EApply (ELiteral (Integer 4)) [ELiteral (Integer 5); ELiteral (Integer 5)]| -e> inr noclosure.
Proof.
  apply eval_apply_ex_closure with (v := VLiteral (Integer 4)) (vals := [VLiteral (Integer 5); VLiteral (Integer 5)]).
  * reflexivity.
  * intros. inversion H; inversion H0.
    - apply eval_lit.
    - inversion H1. apply eval_lit.
    - inversion H1.
  * apply eval_lit.
  * intros. unfold not. intros. inversion H.
Qed.

Example apply_eval_exception_closure2 : |[], [], EApply (EVar "X"%string) [ELiteral (Integer 5); ELiteral (Integer 5)]| -e> inr novar.
Proof.
  apply eval_apply_ex_closure_ex.
  * apply eval_var.
Qed.

Example apply_eval_exception_param : |[(inl "X"%string, VClosure (inl []) [] (ELiteral (Integer 4)))], [], EApply (EVar "X"%string) [EVar "Y"%string]| -e> inr novar.
Proof.
  apply eval_apply_ex_params with (i := 0) (vals := []) (v := VClosure (inl []) [] (ELiteral (Integer 4))).
  * reflexivity.
  * auto.
  * apply eval_var.
  * intros. inversion H.
  * simpl. apply eval_var.
Qed.

Example apply_eval_exception_param_count : |[(inl "X"%string, VClosure (inl []) [] (ELiteral (Integer 4)))], [], EApply (EVar "X"%string) [ELiteral (Integer 2)]| -e> inr args.
Proof.
  apply eval_apply_ex_param_count with (vals := [VLiteral (Integer 2)]) (var_list := []) (body := ELiteral (Integer 4)) (ref := inl []).
  * reflexivity.
  * apply eval_var.
  * intros. inversion H; inversion H0. apply eval_lit.
  * simpl. trivial.
Qed.

Example apply_eval_exception_body : |[(inl "X"%string, VClosure (inl []) [] (EVar "X"%string))], [], EApply (EVar "X"%string) []| -e> inr novar.
Proof.
  apply eval_apply with (vals := []) (var_list := []) (body := EVar "X"%string) (ref := inl []).
  * reflexivity.
  * apply eval_var.
  * reflexivity.
  * intros. inversion H.
  * simpl. apply eval_var.
Qed.

Example letrec_exception : |[], [], ELetrec [("fun1"%string, 0)] [[]] [(ErrorExp)] (EVar "X"%string)| -e> inr novar.
Proof.
  apply eval_letrec; try (reflexivity).
  * simpl. apply eval_var.
Qed.

(* Example map_eval_ex_key : |[], [], EMap [ErrorExp; ErrorExp; EVar "X"%string; ErrorExp] [ErrorExp; ErrorExp; ErrorExp; ErrorExp]| -e> inr novar.
Proof.
  apply eval_map_ex_key with (i := 2) (kvals := [ErrorValue; ErrorValue]) (vvals := [ErrorValue; ErrorValue]).
  1-3: reflexivity.
  * simpl. auto.
  * intros. inversion H; inversion H0.
    - split; apply eval_lit.
    - inversion H1. split; apply eval_lit.
    - inversion H1.
  * simpl. apply eval_var.
Qed. *)

End Exception_Examples.




End Core_Erlang_Examples.