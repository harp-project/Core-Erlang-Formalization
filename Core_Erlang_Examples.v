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
Example eval_letrec1 : ([], [], ELetrec [("fun1"%string, 1)] [(["X"%string], EApply (EFunSig ("fun1"%string, 1)) [EVar "X"%string])] (EApply (EFunSig ("fun1"%string, 1)) [ELiteral EmptyTuple])) -e> ErrorValue.
Proof.
  apply eval_letrec.
  * reflexivity.
  * simpl. apply eval_apply with (vals := [VLiteral EmptyTuple]) (body := (EApply (EFunSig ("fun1"%string, 1)) [EVar "X"%string])) (var_list := ["X"%string]) (ref := (inr ("fun1"%string, 1))).
    - reflexivity.
    - apply eval_funsig.
    - intros. inversion H.
      + inversion H0. apply eval_lit.
      + inversion H0.
    - simpl. apply eval_apply with (vals := [VLiteral EmptyTuple]) (body := (EApply (EFunSig ("fun1"%string, 1)) [EVar "X"%string])) (var_list := ["X"%string]) (ref := inr ("fun1"%string, 1)).
    + reflexivity.
    + apply eval_funsig.
    + intros. inversion H.
      ** inversion H0. apply eval_var.
      ** inversion H0.
    + simpl. apply eval_apply with (vals := [VLiteral EmptyTuple]) (body := (EApply (EFunSig ("fun1"%string, 1)) [EVar "X"%string])) (var_list := ["X"%string]) (ref := inr ("fun1"%string, 1)).
Admitted.

(* This is not recursive, but can't be derivated, because the expression is faulty *)
Example eval_letrec2 : ([], [], ELet ["F"%string] [EFun ["X"%string] (EApply (EVar "F"%string) [EVar "X"%string])] (EApply (EVar "F"%string) [ELiteral EmptyTuple])) -e> ErrorValue.
Proof.
  apply eval_let with (vals := [VClosure (inl ""%string) ["X"%string] (EApply (EVar "F"%string) [EVar "X"%string])]).
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. apply eval_fun.
    - inversion H0.
  * simpl. eapply eval_apply with (vals := [VLiteral EmptyTuple]) (ref := inl ("F"%string)) (var_list := ["X"%string]) (body := (EApply (EVar "F"%string) [EVar "X"%string])).
    - reflexivity.
    - apply eval_var.
    - intros. inversion H.
      + inversion H0. apply eval_lit.
      + inversion H0.
    - simpl. eapply eval_apply with (vals := [VLiteral EmptyTuple]). (* Here, I cant say anything about F's var_list, body and app_env *)
      + reflexivity.
      + shelve.
      + intros. inversion H.
        ** inversion H0. apply eval_var.
        ** inversion H0.
      + simpl. admit.
Admitted.

(* Top level functions, and their closures must be added initially *)
Example multiple_top_level_funs : ([(inr ("fun1"%string, 0), VClosure (inr ("fun1"%string, 0)) [] (EApply (EFunSig ("fun3"%string, 0)) [])) ; 
                                    (inr ("fun2"%string, 0), VClosure (inr ("fun2"%string, 0)) [] (ELiteral (Integer 42))) ;
                                    (inr ("fun3"%string, 0), VClosure (inr ("fun3"%string, 0)) [] (EApply (EFunSig ("fun2"%string, 0)) []))]
                                    ,
                                    [
                                      (inr ("fun1"%string, 0), [(inr ("fun1"%string, 0), VClosure (inr ("fun1"%string, 0)) [] (EApply (EFunSig ("fun3"%string, 0)) [])) ; 
                                    (inr ("fun2"%string, 0), VClosure (inr ("fun2"%string, 0)) [] (ELiteral (Integer 42))) ;
                                    (inr ("fun3"%string, 0), VClosure (inr ("fun3"%string, 0)) [] (EApply (EFunSig ("fun2"%string, 0)) []))]) ;
                                      (inr ("fun2"%string, 0), [(inr ("fun1"%string, 0), VClosure (inr ("fun1"%string, 0)) [] (EApply (EFunSig ("fun3"%string, 0)) [])) ; 
                                    (inr ("fun2"%string, 0), VClosure (inr ("fun2"%string, 0)) [] (ELiteral (Integer 42))) ;
                                    (inr ("fun3"%string, 0), VClosure (inr ("fun3"%string, 0)) [] (EApply (EFunSig ("fun2"%string, 0)) []))]) ;
                                      (inr ("fun3"%string, 0), [(inr ("fun1"%string, 0), VClosure (inr ("fun1"%string, 0)) [] (EApply (EFunSig ("fun3"%string, 0)) [])) ; 
                                    (inr ("fun2"%string, 0), VClosure (inr ("fun2"%string, 0)) [] (ELiteral (Integer 42))) ;
                                    (inr ("fun3"%string, 0), VClosure (inr ("fun3"%string, 0)) [] (EApply (EFunSig ("fun2"%string, 0)) []))])
                                    ]
                                    , EApply (EFunSig ("fun1"%string,0)) []) -e> VLiteral (Integer 42).
Proof.
  eapply eval_apply with (vals := []) (ref := inr ("fun1"%string, 0)) (body := (EApply (EFunSig ("fun3"%string, 0)) [])) (var_list := []). 
  * reflexivity.
  * apply eval_funsig.
  * simpl. intros. inversion H.
  * simpl. apply eval_apply with (vals := []) (ref := inr ("fun3"%string, 0)) (body := (EApply (EFunSig ("fun2"%string, 0)) [])) (var_list := []).
    - reflexivity.
    - apply eval_funsig.
    - intros. inversion H.
    - simpl. apply eval_apply with (vals := []) (ref := inr ("fun2"%string, 0)) (body := (ELiteral (Integer 42))) (var_list := []).
      + reflexivity.
      + apply eval_funsig.
      + intros. inversion H.
      + apply eval_lit.
Qed.

Example top_overwrite : ([(inr ("fun1"%string, 0), VClosure (inr ("fun1"%string, 0)) [] (ELiteral (Integer 42)))],
[(inr ("fun1"%string, 0), [(inr ("fun1"%string, 0), VClosure (inr ("fun1"%string, 0)) [] (ELiteral (Integer 42)))]) ],
  ELetrec [("fun1"%string, 0)] [([], ELiteral (Integer 40))] (EApply (EFunSig ("fun1"%string, 0)) []) ) -e> VLiteral (Integer 40).
Proof.
  apply eval_letrec.
  * simpl. reflexivity.
  * simpl. apply eval_apply with (vals := []) (ref := inr ("fun1"%string, 0)) (body := (ELiteral (Integer 40))) (var_list := []).
    - reflexivity.
    - apply eval_funsig.
    - intros. inversion H.
    - apply eval_lit.
Qed.

Example top_no_overwrite : ([(inr ("fun1"%string, 0), VClosure (inr ("fun1"%string, 0)) [] (ELiteral (Integer 42))) ]
                       ,[(inr ("fun1"%string, 0), [(inr ("fun1"%string, 0), VClosure (inr ("fun1"%string, 0)) [] (ELiteral (Integer 42)))])]
                       , ELetrec [("fun1"%string, 1)] [(["X"%string], (ELiteral (Integer 40)))] (EApply (EFunSig ("fun1"%string, 0)) []) ) -e> VLiteral (Integer 42).
Proof.
  apply eval_letrec.
  * simpl. reflexivity.
  * simpl. apply eval_apply with (vals := []) (ref := (inr ("fun1"%string, 0))) (body := ELiteral (Integer 42)) (var_list := []).
    - reflexivity.
    - apply eval_funsig.
    - intros. inversion H.
    - apply eval_lit.
Qed.

(* This is not accepted by the compiler *)
Example eval_let_func : ([(inl "X"%string, VLiteral (Integer 42))], [], ELet ["X"%string; "X"%string] [EFun [] (ELiteral EmptyList); EFun [] (ELiteral EmptyMap)] (ELiteral EmptyMap)) -e> VLiteral EmptyMap.
Proof.
  apply eval_let with (vals := [VClosure (inl ""%string) [] (ELiteral EmptyList); 
                                VClosure (inl ""%string) [] (ELiteral EmptyMap)]).
  * simpl. reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. apply eval_fun.
    - inversion H0.
      + inversion H1. apply eval_fun.
      + inversion H1.
  * simpl. apply eval_lit.
Qed.

Example eval_let_apply : ([(inl "X"%string, VLiteral (Integer 42))], [], ELet ["Y"%string] [EFun [] (EVar "X"%string)] (EApply (EVar "Y"%string) [])) -e> VLiteral (Integer 42).
Proof.
  apply eval_let with (vals := [VClosure (inl ""%string) [] (EVar "X"%string)]).
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. apply eval_fun.
    - inversion H0.
  * simpl. apply eval_apply with (vals := []) (ref := inl "Y"%string) (body := (EVar "X"%string)) (var_list := []).
    - reflexivity.
    - apply eval_var.
    - simpl. intros. inversion H.
    - apply eval_var.
Qed.

Example eval_muliple_let : ([], [], ELet ["X"%string] [ELiteral (Integer 1)] (ELet ["X"%string] [ELiteral (Integer 2)] (EVar "X"%string))) -e>  VLiteral (Integer 2).
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

Example let_eval_1 : ([], [], ELet ["X"%string] [ELiteral EmptyTuple] (ELiteral EmptyMap)) -e> VLiteral EmptyMap.
Proof.
  apply eval_let with (vals := [VLiteral EmptyTuple]).
  * reflexivity.
  * intros. simpl in *. inversion H.
    - inversion H0. apply eval_lit.
    - inversion H0.
  * simpl. apply eval_lit.
Qed.

Example let_eval_2 : ([(inl "X"%string, VLiteral EmptyMap)], [], ELet ["X"%string] [ELiteral EmptyTuple] (ELiteral EmptyMap)) -e> VLiteral EmptyMap.
Proof.
  apply eval_let with (vals := [VLiteral EmptyTuple]).
  * reflexivity.
  * intros. simpl in *. inversion H.
    - inversion H0. apply eval_lit.
    - inversion H0.
  * simpl. apply eval_lit.
Qed.

(* This shouldn't compile *)
Example eval_let_3 : ([(inl "X"%string, VLiteral EmptyMap)], [], ELet ["X"%string; "X"%string; "Y"%string] [ELiteral EmptyTuple; ELiteral EmptyList; EVar "X"%string] (ELiteral EmptyMap)) -e> VLiteral EmptyMap.
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
  * simpl. apply eval_lit.
Qed.

Example tuple_eval : ([(inl "X"%string, VLiteral (Atom "asd"%string)); (inl "Y"%string, VLiteral EmptyTuple)], [], ETuple [ELiteral (Integer 5); EVar "X"%string; EVar "Y"%string]) -e> 
                      VTuple [VLiteral (Integer 5); VLiteral (Atom "asd"%string); VLiteral EmptyTuple].
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

Compute Core_Erlang_Environment.get_value (get_env_from_closure (inr ("Plus"%string, 2)) []).

Example apply_top_eval : ([(inr ("Plus"%string, 2), VClosure (inr ("Plus"%string, 2)) ["X"%string ; "Y"%string] (ELiteral (Integer 3)))], [], EApply (EFunSig ("Plus"%string, 2)) [ELiteral (Integer 2); ELiteral (Integer 3)]) -e> (VLiteral (Integer 3)).
Proof.
  apply eval_apply with (vals := [VLiteral (Integer 2) ; VLiteral (Integer 3)]) (var_list := ["X"%string; "Y"%string]) (body := ELiteral (Integer 3)) (ref := inr ("Plus"%string, 2)).
  * reflexivity.
  * apply eval_funsig.
  * simpl. intros. inversion H.
    - inversion H0. apply eval_lit.
    - inversion H0.
      + inversion H1. apply eval_lit.
      + inversion H1.
  * simpl. apply eval_lit.
Qed.

Example apply_eval : ([(inl "Minus"%string, VClosure (inl "Minus"%string) ["X"%string; "Y"%string] (ELiteral (Integer 42))) ; (inl "X"%string, VLiteral EmptyMap)], [], EApply (EVar "Minus"%string) [EVar "X"%string; EVar "X"%string]) -e> VLiteral (Integer 42).
Proof.
  apply eval_apply with (vals := [VLiteral EmptyMap; VLiteral EmptyMap]) (var_list := ["X"%string; "Y"%string]) (body := (ELiteral (Integer 42))) (ref := inl ("Minus"%string)).
  * reflexivity.
  * apply eval_var.
  * simpl. intros. inversion H.
    - inversion H0. apply eval_var.
    - inversion H0.
      + inversion H1. apply eval_var.
      + inversion H1.
  * simpl. apply eval_lit.
Qed.


Example list_eval : ([(inl "X"%string, VLiteral (Integer 5))], [], EList (EVar "X"%string) (ELiteral EmptyList)) -e> VList (VLiteral (Integer 5)) (VLiteral EmptyList).
Proof.
  apply eval_list.
  * apply eval_var.
  * apply eval_lit.
Qed.

Example let_eval_overwrite : ([], [], ELet ["X"%string] [EFun [] (ELiteral EmptyTuple)] (ELet ["X"%string] [ELiteral (Integer 5)] (EVar "X"%string))) -e> VLiteral (Integer 5).
Proof.
  apply eval_let with (vals := [VClosure (inl ""%string) [] (ELiteral EmptyTuple)]).
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

Example map_eval : ([(inl "X"%string, VLiteral (Integer 42))], [], EMap [ELiteral (Integer 5)] [EVar "X"%string]) -e> VMap [VLiteral (Integer 5)] [VLiteral (Integer 42)].
Proof.
  apply eval_map.
  1-3: reflexivity.
  * intros. inversion H.
    - inversion H0. apply eval_lit.
    - inversion H0.
  * intros. inversion H; inversion H0.
    - apply eval_var.
Qed.

(** Function parameter always overwrites everything *)
Example let_closure_apply_eval_without_overwrite :
([], [], ELet ["X"%string] [ELiteral (Integer 42)] (ELet ["Y"%string] [EFun ["X"%string] (EVar "X"%string)] (ELet ["X"%string] [ELiteral (Integer 5)] (EApply (EVar "Y"%string) [ELiteral (Integer 7)])))) -e> VLiteral (Integer 7).
Proof.
  apply eval_let with (vals := [VLiteral (Integer 42)]).
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. apply eval_lit.
    - inversion H0.
  * simpl. apply eval_let with (vals := [VClosure (inl ""%string) ["X"%string] (EVar "X"%string)]).
    - reflexivity.
    - simpl. intros. inversion H.
      + inversion H0. apply eval_fun.
      + inversion H0.
    - simpl. apply eval_let with (vals := [VLiteral (Integer 5)]).
      + reflexivity.
      + simpl. intros. inversion H.
        ** inversion H0. apply eval_lit.
        ** inversion H0.
      + simpl. apply eval_apply with (vals := [VLiteral (Integer 7)]) (ref := (inl "Y"%string)) (body := (EVar "X"%string)) (var_list := ["X"%string]).
        ** reflexivity.
        ** simpl. intros. apply eval_var.
        ** intros. inversion H.
          -- inversion H0. apply eval_lit.
          -- inversion H0.
        ** apply eval_var.
Qed.


(** Example to test that value overwriting does not affect the value in the closure *)
Example let_closure_apply_eval_without_overwrite2 :
([], [], ELet ["X"%string] [ELiteral (Integer 42)] (ELet ["Y"%string] [EFun [] (EVar "X"%string)] (ELet ["X"%string] [ELiteral (Integer 5)] (EApply (EVar "Y"%string) [])))) -e> VLiteral (Integer 42).
Proof.
  apply eval_let with (vals := [VLiteral (Integer 42)]).
  * reflexivity.
  * intros. inversion H; inversion H0.
    - apply eval_lit.
  * simpl. apply eval_let with (vals := [VClosure (inl ""%string) [] (EVar "X"%string)]).
    - reflexivity.
    - intros. inversion H; inversion H0.
      + apply eval_fun. 
    - apply eval_let with (vals := [VLiteral (Integer 5)]).
      + reflexivity.
      + intros. inversion H; inversion H0.
        ** apply eval_lit.
      + simpl. apply eval_apply with (vals := []) (var_list := []) (body := (EVar "X"%string)) (ref := (inl "Y"%string)).
        ** reflexivity.
        ** apply eval_var.
        ** intros. inversion H.
        ** apply eval_var.
Qed.

Example call_eval : ([(inl "X"%string, VLiteral (Integer 5))], [], ECall "plus"%string [EVar "X"%string ; ELiteral (Integer 2)]) -e> VLiteral (Integer 7).
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

Example mutliple_function_let : ([], [], ELet ["Z"%string] [ECall "plus"%string [ELiteral (Integer 2) ; ELiteral (Integer 2)] ] (ELet ["Y"%string] [EFun [] (EVar "Z"%string)] (ELet ["X"%string] [EFun [] (EApply (EVar "Y"%string) [])] (EApply (EVar "X"%string) [])))) -e> VLiteral (Integer 4).
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
  * simpl. apply eval_let with (vals := [VClosure (inl ""%string) [] (EVar "Z"%string)]).
    - reflexivity.
    - simpl. intros. inversion H.
      + inversion H0. apply eval_fun.
      + inversion H0.
    - simpl. apply eval_let with (vals := [VClosure (inl ""%string) [] (EApply (EVar "Y"%string) [])]).
      + reflexivity.
      + simpl. intros. inversion H.
        ** inversion H0. apply eval_fun.
        ** inversion H0.
      + simpl. apply eval_apply with (vals := []) (var_list := []) (body := (EApply (EVar "Y"%string) [])) (ref := inl "X"%string).
        ** reflexivity.
        ** simpl. apply eval_var.
        ** simpl. intros. inversion H.
        ** simpl. apply eval_apply with (vals := []) (var_list := []) (body := (EVar "Z"%string)) (ref := (inl "Y"%string)).
          -- reflexivity.
          -- apply eval_var.
          -- intros. inversion H.
          -- simpl. apply eval_var.
Qed.

Example case_eval : ([(inl "X"%string, VLiteral EmptyTuple)],[], ECase (EVar "X"%string) [
          CCons (PLiteral (Integer 5)) (ELiteral (Atom "true"%string)) (ELiteral (Integer 5)) ;
          CCons (PLiteral (Integer 6)) (ELiteral (Atom "true"%string)) (ELiteral (Integer 6)) ;
          CCons (PVar "Z"%string)      (ELiteral (Atom "true"%string)) (EVar "Z"%string)
          ]) -e> VLiteral EmptyTuple.
Proof.
  eapply eval_case with (i := 2).
  * exact ErrorExp.
  * apply eval_var.
  * simpl. reflexivity.
  * intros. inversion H.
    - subst. left. simpl. reflexivity.
    - inversion H1.
      + subst. simpl. left. reflexivity.
      + subst. inversion H3.
  * simpl. apply eval_lit.
  * simpl. apply eval_var.
Qed.


Example case_eval2 : ([(inl "X"%string, VLiteral EmptyTuple)],[], ECase (EVar "X"%string) [
          CCons (PLiteral (Integer 5)) (ELiteral (Atom "true"%string)) (ELiteral (Integer 5)) ;
          CCons (PLiteral (Integer 6)) (ELiteral (Atom "true"%string)) (ELiteral (Integer 6)) ;
          CCons (PVar "Z"%string)      (ELiteral (Atom "false"%string)) (EVar "Z"%string) ;
          CCons (PVar "Z"%string)      (ELiteral (Atom "true"%string)) (ELiteral EmptyMap)
          ]) -e> VLiteral EmptyMap.
Proof.
  eapply eval_case with (i := 3).
  * exact ErrorExp.
  * apply eval_var.
  * simpl. reflexivity.
  * intros. inversion H.
    - subst. right. simpl. intros. inversion H0. subst. apply eval_lit.
    - inversion H1.
      + subst. simpl. left. reflexivity.
      + inversion H3.
        ** subst. simpl. left. reflexivity.
        ** inversion H5.
  * apply eval_lit.
  * apply eval_lit.
Qed.

Example case_eval_fun : ([(inl "X"%string, VClosure (inl "X"%string) [] (EVar "Y"%string))], [(inl "X"%string, [(inl "Y"%string, tt)])], ECase (EVar "X"%string) [
          CCons (PLiteral (Integer 5)) (ELiteral (Atom "true"%string)) (ELiteral (Integer 5)) ;
          CCons (PLiteral (Integer 6)) (ELiteral (Atom "true"%string)) (ELiteral (Integer 6)) ;
          CCons (PVar "Z"%string)      (ELiteral (Atom "true"%string)) (EApply (EVar "Z"%string) [])
          ]) -e> tt.
Proof.
  eapply eval_case with (i := 2).
  * exact ErrorExp.
  * apply eval_var.
  * simpl. reflexivity.
  * intros. inversion H.
    - subst. right. simpl. intros. inversion H0.
    - inversion H1.
      + subst. simpl. left. reflexivity.
      + inversion H3.
  * apply eval_lit.
  * simpl. apply eval_apply with (vals := []) (var_list := []) (ref := (inl "X"%string)) (body := (EVar "Y"%string)).
   - reflexivity.
   - apply eval_var.
   - intros. inversion H.
   - simpl. apply eval_var.
Qed.


Example letrec_eval : ([(inr ("fun1"%string, 0), VClosure (inr ("fun1"%string, 0)) [] (ELiteral EmptyMap)) ; (inl "X"%string, VLiteral (Integer 42))], [], ELetrec [("fun2"%string, 0); ("fun1"%string, 1)] [ ([], (EVar "X"%string)) ; (["Z"%string], (EVar "Z"%string))] (EApply (EFunSig ("fun1"%string, 0)) [])) -e> VLiteral EmptyMap.
Proof.
  apply eval_letrec.
  * simpl. reflexivity.
  * simpl. apply eval_apply with (vals := []) (var_list := []) (body := (ELiteral EmptyMap)) (ref := (inr ("fun1"%string,0))).
    - simpl. reflexivity.
    - apply eval_funsig.
    - simpl. intros. inversion H.
    - simpl. apply eval_lit.
Qed.


Example unnamed_eval : ([(inl "X"%string, VLiteral (Integer 5))], [], EApply (EFun ["Y"%string] (EVar "Y"%string)) [EVar "X"%string]) -e> VLiteral (Integer 5).
Proof.
  apply eval_apply with (vals := [VLiteral (Integer 5)]) (var_list := ["Y"%string]) (body := (EVar "Y"%string)) (ref := inl ""%string).
  * reflexivity.
  * apply eval_fun.
  * intros. inversion H; inversion H0. apply eval_var.
  * simpl. apply eval_var.
Qed.


Section B_Core.

Definition B : ErlModule := ErlMod "b"%string [
  TopLevelFun ("fun1"%string, 0) ([], (ELiteral (Integer 6))) ;
  TopLevelFun ("fun2"%string, 0) ([], (ELet ["X"%string] [(EFun [] (ELiteral (Integer 5)))] (ELet ["X"%string] [(EFun [] (ELiteral (Integer 6)))] (EApply (EVar "X"%string) []))) )
].


Example fun2 : ([], [], ELet ["X"%string] [(EFun [] (ELiteral (Integer 5)))] (ELet ["X"%string] [(EFun [] (ELiteral (Integer 6)))] (EApply (EVar "X"%string) []))) -e> VLiteral (Integer 6).
Proof.
  apply eval_let with (vals := [VClosure (inl ""%string) [] (ELiteral (Integer 5))]).
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. apply eval_fun.
    - inversion H0.
  * simpl. apply eval_let with (vals := [VClosure (inl ""%string) [] (ELiteral (Integer 6))]).
    - reflexivity.
    - simpl. intros. inversion H.
      + inversion H0. apply eval_fun.
      + inversion H0.
    - simpl. apply eval_apply with (vals := []) (var_list := []) (body := (ELiteral (Integer 6))) (ref := (inl "X"%string)).
      + reflexivity.
      + apply eval_var.
      + intros. inversion H.
      + apply eval_lit.
Qed.

Compute initialize_proving B.

Compute initialize_proving_closures B.

End B_Core.

Section Documentation_Examples.

Example ex1 : ([], [], ELet ["X"%string] [ELiteral (Integer 5)] (EVar "X"%string)) -e> VLiteral (Integer 5).
Proof.
  apply eval_let with ([VLiteral (Integer 5)]).
  * reflexivity.
  * intros. inversion H.
    - inversion H0. subst. apply eval_lit.
    - inversion H0.
  * simpl. apply eval_var.
Qed.

Example ex2 : ([], [], ELet ["X"%string] [EFun [] (EApply (EVar "X"%string) [])] (EApply (EVar "X"%string) [])) -e> ErrorValue.
Proof.
  apply eval_let with ([VClosure (inl ""%string) [] (EApply ( EVar "X"%string) [])]).
  * reflexivity.
  * intros. inversion H.
    - inversion H0. subst. apply eval_fun.
    - inversion H0.
  * simpl. apply eval_apply with (vals := []) (var_list := []) (body := (EApply (EVar "X"%string) [])) (ref := (inl "X"%string)).
    - reflexivity.
    - apply eval_var.
    - intros. inversion H.
    - simpl. eapply eval_apply with (vals := []).
      + reflexivity.
      + admit. (* eapply eval_var.*)
      + intros. inversion H.
      + simpl. apply eval_lit.
  Unshelve.
  exact [].
  exact (inl ""%string).
Admitted.

Example ex3 :  ([], [], ELetrec [("X"%string, 0)] [([], (EApply (EFunSig ("X"%string, 0)) []))] (EApply (EFunSig ("X"%string, 0)) [])) -e> VLiteral EmptyTuple.
Proof.
  apply eval_letrec.
  * reflexivity.
  * simpl. eapply eval_apply with (vals := []) (var_list := []) (body := (EApply (EFunSig ("X"%string, 0)) [])) (ref := (inr ("X"%string, 0))).
    - reflexivity.
    - apply eval_funsig.
    - intros. inversion H.
    - simpl. eapply eval_apply with (vals := []) (var_list := []) (body := (EApply (EFunSig ("X"%string, 0)) [])) (ref := (inr ("X"%string, 0))).
      + reflexivity.
      + apply eval_funsig.
      + intros. inversion H.
      + simpl. eapply eval_apply with (vals := []) (var_list := []) (body := (EApply (EFunSig ("X"%string, 0)) [])) (ref := (inr ("X"%string, 0))).
        ** reflexivity.
        ** apply eval_funsig.
        ** intros. inversion H.
        ** simpl.
Admitted.

End Documentation_Examples.

End Core_Erlang_Examples.