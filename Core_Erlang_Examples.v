Load Core_Erlang_Semantics.

Module Core_Erlang_Examples.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.

Import Core_Erlang_Syntax.
Import Core_Erlang_Semantics.
Import Core_Erlang_Closures.
Import Core_Erlang_Helpers.

Ltac value_solver :=
  try(
    apply VJ_Literal
  );
  try(
    apply VJ_Function
  );
  try(
    apply VJ_List
  );
  try(
    apply VJ_Tuple
  );
  try(
    apply VJ_Map
  )
.

Ltac value_var_solver :=
  try(split); try((right; reflexivity) || (left; apply eval_var) ); try(value_solver); try(left)
.

(* This is an edless recursion *)
Example eval_letrec1 : ([], [], ELetrec [("fun1"%string, 1)] [FunDecl ["X"%string] (EApplyTopLevel ("fun1"%string, 1) [EVar "X"%string])] (EApplyTopLevel ("fun1"%string, 1) [ELiteral EmptyTuple])) -e> ErrorExp.
Proof.
  apply eval_letrec.
  * reflexivity.
  * simpl. split. 2: apply VJ_Literal. left. apply eval_apply_top with (exprs2 := [exist _ (ELiteral EmptyTuple) (VJ_Literal _)]).
    - reflexivity.
    - reflexivity.
    - simpl. intros. inversion H.
      + inversion H0. value_var_solver.
      + inversion H0.
    - split. 2: value_solver. left. apply eval_apply_top with (exprs2 := [exist _ (ELiteral EmptyTuple) (VJ_Literal _)]).
      + reflexivity.
      + reflexivity.
      + simpl. intros. inversion H.
        ** inversion H0. value_var_solver.
        ** inversion H0.
      + simpl. unfold get_fun_exp. simpl. split. 2: value_solver. left. apply eval_apply_top with (exprs2 := [exist _ (ELiteral EmptyTuple) (VJ_Literal _)]).
    reflexivity.
    reflexivity.
    simpl. intros. inversion H.
      inversion H0. left. apply eval_var.
      inversion H0. simpl. admit.
Admitted.

(* This cant be recursive, so we get an error *)
Example eval_letrec2 : ([], [], ELet ["F"%string] [EFunction (FunDecl ["X"%string] (EApply "F"%string [EVar "X"%string]))] (EApply "F"%string [ELiteral EmptyTuple])) -e> ErrorExp.
Proof.
  apply eval_let with (exprs2 := [exist _ (EFunction (FunDecl ["X"%string] (EApply "F"%string [EVar "X"%string]))) (VJ_Function _)]).
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. simpl. right. reflexivity.
    - inversion H0.
  * simpl. split. 2: value_solver. left. apply eval_apply with (exprs2 := [exist _ (ELiteral EmptyTuple) (VJ_Literal _)]).
    - reflexivity.
    - simpl. intros. inversion H.
      + inversion H0. simpl. right. reflexivity. 
      + inversion H0.
    - simpl. split. 2: value_var_solver. left. apply eval_apply with (exprs2 := [exist _ (ELiteral EmptyTuple) (VJ_Literal _)]).
      + reflexivity.
      + simpl. intros. inversion H.
        ** inversion H0. left. apply eval_var.
        ** inversion H0.
      + simpl. unfold get_fun_exp. simpl. split. 2: value_var_solver. right. reflexivity.
Qed.

(* Top level functions, and their closures must be added initially *)
Example multiple_top_level_funs : ([(inr ("fun1"%string, 0), exist _ (EFunction (FunDecl [] (EApplyTopLevel ("fun3"%string, 0) []))) (VJ_Function _)) ; 
                                    (inr ("fun2"%string, 0), exist _ (EFunction (FunDecl [] (ELiteral (Integer 42)))) (VJ_Function _)) ;
                                    (inr ("fun3"%string, 0), exist _ (EFunction (FunDecl [] (EApplyTopLevel ("fun2"%string, 0) []))) (VJ_Function _))]
                                    ,[
                                    (inr ("fun1"%string, 0), [(inr ("fun1"%string, 0), exist _ (EFunction (FunDecl [] (EApplyTopLevel ("fun3"%string, 0) []))) (VJ_Function _)) ; 
                                    (inr ("fun2"%string, 0), exist _ (EFunction (FunDecl [] (ELiteral (Integer 42)))) (VJ_Function _)) ;
                                    (inr ("fun3"%string, 0), exist _ (EFunction (FunDecl [] (EApplyTopLevel ("fun2"%string, 0) []))) (VJ_Function _))]) ;
                                    (inr ("fun2"%string, 0), [(inr ("fun1"%string, 0), exist _ (EFunction (FunDecl [] (EApplyTopLevel ("fun3"%string, 0) []))) (VJ_Function _)) ; 
                                    (inr ("fun2"%string, 0), exist _ (EFunction (FunDecl [] (ELiteral (Integer 42)))) (VJ_Function _)) ;
                                    (inr ("fun3"%string, 0), exist _ (EFunction (FunDecl [] (EApplyTopLevel ("fun2"%string, 0) []))) (VJ_Function _))]) ;
                                    (inr ("fun3"%string, 0), [(inr ("fun1"%string, 0), exist _ (EFunction (FunDecl [] (EApplyTopLevel ("fun3"%string, 0) []))) (VJ_Function _)) ; 
                                    (inr ("fun2"%string, 0), exist _ (EFunction (FunDecl [] (ELiteral (Integer 42)))) (VJ_Function _)) ;
                                    (inr ("fun3"%string, 0), exist _ (EFunction (FunDecl [] (EApplyTopLevel ("fun2"%string, 0) []))) (VJ_Function _))])
                                    ], EApplyTopLevel ("fun1"%string,0) []) -e> ELiteral (Integer 42).
Proof.
  apply eval_apply_top with (exprs2 := []).
  * reflexivity.
  * reflexivity.
  * simpl. intros. inversion H.
  * simpl. split. 2: value_var_solver. left. apply eval_apply_top with (exprs2 := []).
    - reflexivity.
    - reflexivity.
    - simpl. intros. inversion H.
    - simpl. split. 2 : value_var_solver. left. apply eval_apply_top with (exprs2 := []).
      + reflexivity.
      + reflexivity.
      + simpl. intros. inversion H.
      + simpl. unfold get_fun_exp. simpl. split. right. reflexivity. value_var_solver.
Qed.

Example top_overwrite : ([(inr ("fun1"%string, 0), EFunction (FunDecl [] (ELiteral (Integer 42))) p: (VJ_Function _))],
[(inr ("fun1"%string, 0), [(inr ("fun1"%string, 0), ELiteral (Integer 42) p: (VJ_Literal _))]) ],
  ELetrec [("fun1"%string, 0)] [FunDecl [] (ELiteral (Integer 40))] (EApplyTopLevel ("fun1"%string, 0) []) ) -e> ELiteral (Integer 40).
Proof.
  apply eval_letrec.
  * simpl. reflexivity.
  * simpl. split. 2: value_var_solver. left. apply eval_apply_top with (exprs2 := []).
    - reflexivity.
    - reflexivity.
    - simpl. intros. inversion H.
    - simpl. split. right. reflexivity. value_var_solver.
Qed.

Example top_no_overwrite : ([(inr ("fun1"%string, 0), EFunction (FunDecl [] (ELiteral (Integer 42))) p: VJ_Function _)]
                       ,[(inr ("fun1"%string, 0), [(inr ("fun1"%string, 0), ELiteral (Integer 42) p: VJ_Literal _)]) ]
                       , ELetrec [("fun1"%string, 1)] [FunDecl ["X"%string] (ELiteral (Integer 40))] (EApplyTopLevel ("fun1"%string, 0) []) ) -e> ELiteral (Integer 42).
Proof.
  apply eval_letrec.
  * simpl. reflexivity.
  * simpl. split. 2: value_solver. left. apply eval_apply_top with (exprs2 := []).
    - reflexivity.
    - reflexivity.
    - simpl. intros. inversion H.
    - simpl. split. right. reflexivity. value_var_solver.
Qed.

Example eval_let_func : ([(inl "X"%string, ELiteral (Integer 42) p: VJ_Literal _)], [], ELet ["X"%string; "X"%string] [EFunction (FunDecl [] (ELiteral EmptyList)); EFunction ( FunDecl [] (ELiteral EmptyMap))] (ELiteral EmptyMap)) -e> ELiteral EmptyMap.
Proof.
  apply eval_let with (exprs2 := [(EFunction (FunDecl [] (ELiteral EmptyList))) p: VJ_Function _ ; (EFunction (FunDecl [] (ELiteral EmptyMap))) p: VJ_Function _]).
  * simpl. reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. right. reflexivity.
    - inversion H0.
      + inversion H1. right. reflexivity.
      + inversion H1.
  * simpl. split. right. reflexivity. value_var_solver.
Qed.

Example eval_let_apply : ([(inl "X"%string, ELiteral (Integer 42) p: VJ_Literal _)], [], ELet ["Y"%string] [EFunction (FunDecl [] (EVar "X"%string))] (EApply "Y"%string [])) -e> ELiteral (Integer 42).
Proof.
  apply eval_let with (exprs2 := [EFunction (FunDecl [] (EVar "X"%string)) p: VJ_Function _]).
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. right. reflexivity.
    - inversion H0.
  * simpl. split. 2: value_solver. left. apply eval_apply with (exprs2 := []).
    - reflexivity.
    - simpl. intros. inversion H.
    - simpl. split. left. apply eval_var. value_var_solver.
Qed.

Example eval_muliple_let : ([], [], ELet ["X"%string] [ELiteral (Integer 1)] (ELet ["X"%string] [ELiteral (Integer 2)] (EVar "X"%string))) -e>  ELiteral (Integer 2).
Proof.
  apply eval_let with (exprs2 := [ELiteral (Integer 1) p: VJ_Literal _]).
  * reflexivity.
  * intros. simpl in *. inversion H.
    - inversion H0. right. reflexivity.
    - inversion H0.
  * simpl. split. 2: value_solver. left. apply eval_let with (exprs2 := [ELiteral (Integer 2) p: VJ_Literal _]).
    - reflexivity.
    - simpl. intros. inversion H.
      + inversion H0. right. reflexivity.
      + inversion H0.
    - split. left. apply eval_var. value_var_solver.
Qed.

Example let_eval_1 : ([], [], ELet ["X"%string] [ELiteral EmptyTuple] (ELiteral EmptyMap)) -e> ELiteral EmptyMap.
Proof.
  apply eval_let with (exprs2 := [ELiteral EmptyTuple p: VJ_Literal _]).
  * reflexivity.
  * intros. simpl in *. inversion H.
    - inversion H0. right. reflexivity.
    - inversion H0.
  * simpl. split. 2: value_solver. right. reflexivity.
Qed.

Example let_eval_2 : ([(inl "X"%string, ELiteral EmptyMap p: VJ_Literal _)], [], ELet ["X"%string] [ELiteral EmptyTuple] (ELiteral EmptyMap)) -e> ELiteral EmptyMap.
Proof.
  apply eval_let with (exprs2 := [ELiteral EmptyTuple p: VJ_Literal _]).
  * reflexivity.
  * intros. simpl in *. inversion H.
    - inversion H0. right. reflexivity.
    - inversion H0.
  * simpl. split. 2: value_solver. right. reflexivity.
Qed.

Example eval_let_3 : ([(inl "X"%string, ELiteral EmptyMap p: VJ_Literal _)], [], ELet ["X"%string; "X"%string; "Y"%string] [ELiteral EmptyTuple; ELiteral EmptyList; EVar "X"%string] (ELiteral EmptyMap)) -e> ELiteral EmptyMap.
Proof.
  apply eval_let with (exprs2 := [(ELiteral EmptyTuple) p: (VJ_Literal _) ; (ELiteral EmptyList) p: (VJ_Literal _); (ELiteral EmptyMap) p: (VJ_Literal _)]).
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. right. reflexivity.
    - inversion H0.
      + inversion H1. right. reflexivity.
      + inversion H1.
        ** inversion H2. left. apply eval_var.
        ** inversion H2.
  * simpl. split. 2: value_solver. right. reflexivity.
Qed.

Example tuple_eval : ([(inl "X"%string, ELiteral (Atom "asd"%string) p: VJ_Literal _); (inl "Y"%string, ELiteral EmptyTuple p: VJ_Literal _)], [], ETuple [ELiteral (Integer 5); EVar "X"%string; EVar "Y"%string]) -e> 
                      ETuple [ELiteral (Integer 5); ELiteral (Atom "asd"%string); ELiteral EmptyTuple].
Proof.
  apply eval_tuple.
  * reflexivity.
  * intros. inversion H.
    - inversion H0. value_var_solver.
    - inversion H0.
      + inversion H1. value_var_solver.
      + inversion H1.
        ** inversion H2. value_var_solver.
        ** inversion H2.
  * easy.
Qed.

Example apply_top_eval : ([(inr ("Plus"%string, 2), EFunction (FunDecl ["X"%string ; "Y"%string] (ELiteral (Integer 3))) p: VJ_Function _)], [], EApplyTopLevel ("Plus"%string, 2) [ELiteral (Integer 2); ELiteral (Integer 3)]) -e> (ELiteral (Integer 3)).
Proof.
  apply eval_apply_top with (exprs2 := [ELiteral (Integer 2) p: VJ_Literal _ ; ELiteral (Integer 3) p: VJ_Literal _]).
  * reflexivity.
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. value_var_solver.
    - inversion H0.
      + inversion H1. value_var_solver.
      + inversion H1.
  * simpl. value_var_solver.
Qed.

Example apply_eval : ([(inl "Minus"%string, EFunction (FunDecl ["X"%string; "Y"%string] (ELiteral (Integer 42))) p: VJ_Function _) ; (inl "X"%string, ELiteral EmptyMap p: VJ_Literal _)], [], EApply "Minus"%string [EVar "X"%string; EVar "X"%string]) -e> ELiteral (Integer 42).
Proof.
  apply eval_apply with (exprs2 := [ELiteral EmptyMap p: VJ_Literal _; ELiteral EmptyMap p: VJ_Literal _]).
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. value_var_solver.
    - inversion H0.
      + inversion H1. value_var_solver.
      + inversion H1.
  * simpl. value_var_solver.
Qed.


Example list_eval : ([(inl "X"%string, ELiteral (Integer 5) p: VJ_Literal _)], [], EList (EVar "X"%string) (ELiteral EmptyList)) -e> EList (ELiteral (Integer 5)) (ELiteral EmptyList).
Proof.
  apply eval_list; value_var_solver.
  easy.
Qed.

Example let_eval_overwrite : ([], [], ELet ["X"%string] [EFunction (FunDecl [] (ELiteral EmptyTuple))] (ELet ["X"%string] [ELiteral (Integer 5)] (EVar "X"%string))) -e> ELiteral (Integer 5).
Proof.
  apply eval_let with (exprs2 := [EFunction (FunDecl [] (ELiteral EmptyTuple)) p: VJ_Function _]).
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. value_var_solver.
    - inversion H0.
  * simpl. value_var_solver. apply eval_let with (exprs2 := [ELiteral (Integer 5) p: VJ_Literal _]).
    - reflexivity.
    - simpl. intros. inversion H.
      + inversion H0. value_var_solver.
      + inversion H0.
    - simpl. value_var_solver.
Qed.

Example map_eval : ([(inl "X"%string, ELiteral (Integer 42) p: VJ_Literal _)], [], EMap [ELiteral (Integer 5)] [EVar "X"%string]) -e> EMap [ELiteral (Integer 5)] [ELiteral (Integer 42)].
Proof.
  apply eval_map with (exprs2 := [ELiteral (Integer 42) p: VJ_Literal _]).
  * intros. inversion H.
    - rewrite <- H0. apply VJ_Literal.
    - inversion H0.
  * reflexivity.
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. value_var_solver.
    - inversion H0.
  * easy.
Qed.

(** Function parameter always overwrites everything *)
Example let_closure_apply_eval_without_overwrite :
([], [], ELet ["X"%string] [ELiteral (Integer 42)] (ELet ["Y"%string] [EFunction (FunDecl ["X"%string] (EVar "X"%string))] (ELet ["X"%string] [ELiteral (Integer 5)] (EApply "Y"%string [ELiteral (Integer 7)])))) -e> ELiteral (Integer 7).
Proof.
  apply eval_let with (exprs2 := [ELiteral (Integer 42) p: VJ_Literal _]).
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. value_var_solver.
    - inversion H0.
  * simpl. value_var_solver. apply eval_let with (exprs2 := [EFunction (FunDecl ["X"%string] (EVar "X"%string)) p: VJ_Function _]).
    - reflexivity.
    - simpl. intros. inversion H.
      + inversion H0. value_var_solver.
      + inversion H0.
    - simpl. value_var_solver. apply eval_let with (exprs2 := [ELiteral (Integer 5) p: VJ_Literal _]).
      + reflexivity.
      + simpl. intros. inversion H.
        ** inversion H0. value_var_solver.
        ** inversion H0.
      + simpl. split. 2: apply VJ_Literal. left. apply eval_apply with (exprs2 := [ELiteral (Integer 7) p: VJ_Literal _]).
        ** reflexivity.
        ** simpl. intros. inversion H.
          -- inversion H0. value_var_solver.
          -- inversion H0.
        ** simpl. split. left. apply eval_var. value_var_solver.
Qed.


(** Example to test that value overwriting does not affect the value in the closure *)
Example let_closure_apply_eval_without_overwrite2 :
([], [], ELet ["X"%string] [ELiteral (Integer 42)] (ELet ["Y"%string] [EFunction (FunDecl [] (EVar "X"%string))] (ELet ["X"%string] [ELiteral (Integer 5)] (EApply "Y"%string [])))) -e> ELiteral (Integer 42).
Proof.
  apply eval_let with (exprs2 := [ELiteral (Integer 42) p: VJ_Literal _]).
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. value_var_solver.
    - inversion H0.
  * simpl. split. 2: value_var_solver. left. apply eval_let with (exprs2 := [EFunction (FunDecl [] (EVar "X"%string)) p: VJ_Function _]).
    - reflexivity.
    - simpl. intros. inversion H.
      + inversion H0. value_var_solver.
      + inversion H0.
    - simpl. split. 2: value_var_solver. left. apply eval_let with (exprs2 := [ELiteral (Integer 5) p: VJ_Literal _]).
      + reflexivity.
      + simpl. intros. inversion H.
        ** inversion H0. value_var_solver.
        ** inversion H0.
      + simpl. split. 2: value_var_solver. left. apply eval_apply with (exprs2 := []).
        ** reflexivity.
        ** simpl. intros. inversion H.
        ** simpl. value_var_solver.
Qed.

Example call_eval : ([(inl "X"%string, ELiteral (Integer 5) p: VJ_Literal _)], [], ECall ("plus"%string, 2) [EVar "X"%string ; ELiteral (Integer 2)]) -e> ELiteral (Integer 7).
Proof.
  apply eval_call with (exprs2 := ([ELiteral (Integer 5) ; ELiteral (Integer 2)])).
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. value_var_solver.
    - inversion H0.
      + inversion H1. value_var_solver.
      + inversion H1.
  * simpl. split. reflexivity. value_solver.
Qed.

Example mutliple_function_let : ([], [], ELet ["Z"%string] [ECall ("plus"%string, 2) [ELiteral (Integer 2) ; ELiteral (Integer 2)] ] (ELet ["Y"%string] [EFunction (FunDecl [] (EVar "Z"%string))] (ELet ["X"%string] [EFunction (FunDecl [] (EApply "Y"%string []))] (EApply "X"%string [])))) -e> ELiteral (Integer 4).
Proof.
  apply eval_let with (exprs2 := [ELiteral (Integer 4) p: VJ_Literal _]).
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. value_var_solver. apply eval_call with (exprs2 := [ELiteral (Integer 2) ; ELiteral (Integer 2)]).
      + reflexivity.
      + simpl. intros. inversion H1.
        ** inversion H4. value_var_solver.
        ** inversion H4.
          -- inversion H5. value_var_solver.
          -- inversion H5.
      + simpl. value_var_solver. reflexivity.
    - inversion H0.
  * simpl. value_var_solver. apply eval_let with (exprs2 := [EFunction (FunDecl [] (EVar "Z"%string)) p: VJ_Function _]).
    - reflexivity.
    - simpl. intros. inversion H.
      + inversion H0. value_var_solver.
      + inversion H0.
    - simpl. value_var_solver. apply eval_let with (exprs2 := [EFunction (FunDecl [] (EApply "Y"%string [])) p: VJ_Function _]).
      + reflexivity.
      + simpl. intros. inversion H.
        ** inversion H0. value_var_solver.
        ** inversion H0.
      + simpl. value_var_solver. apply eval_apply with (exprs2 := []).
        ** reflexivity.
        ** simpl. intros. inversion H.
        ** simpl. value_var_solver. apply eval_apply with (exprs2 := []).
          -- reflexivity.
          -- simpl. intros. inversion H.
          -- simpl. value_var_solver.
Qed.

(* Example case_eval : ([(inl "X"%string, ELiteral EmptyTuple)],[], ECase (EVar "X"%string) [
          CConstructor (PLiteral (Integer 5)) (ELiteral (Atom "true"%string)) (ELiteral (Integer 5)) ;
          CConstructor (PLiteral (Integer 6)) (ELiteral (Atom "true"%string)) (ELiteral (Integer 6)) ;
          CConstructor (PVar "Z"%string)      (ELiteral (Atom "true"%string)) (EVar "Z"%string)
          ]) -e> ELiteral EmptyTuple.
Proof.
  eapply eval_case.
  * apply eval_var.
  * simpl. reflexivity.
  * simpl. apply eval_same.
  * simpl. apply eval_var.
Qed.*)

Example letrec_eval : ([(inr ("fun1"%string, 0), EFunction (FunDecl [] (ELiteral EmptyMap)) p: VJ_Function _) ; (inl "X"%string, ELiteral (Integer 42) p: VJ_Literal _)], [], ELetrec [("fun2"%string, 0); ("fun1"%string, 1)] [FunDecl [] (EVar "X"%string) ; FunDecl ["Z"%string] (EVar "Z"%string)] (EApplyTopLevel ("fun1"%string, 0) [])) -e> ELiteral EmptyMap.
Proof.
  apply eval_letrec.
  * simpl. reflexivity.
  * simpl. value_var_solver. apply eval_apply_top with (exprs2 := []).
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. intros. inversion H.
    - simpl. value_var_solver.
Qed.

Section B_Core.

Definition B : ErlModule := ErlMod "b"%string [
  TopLevelFun ("fun1"%string, 0) (FunDecl [] (ELiteral (Integer 6))) ;
  TopLevelFun ("fun2"%string, 0) (FunDecl [] (ELet ["X"%string] [(EFunction (FunDecl [] (ELiteral (Integer 5))))] (ELet ["X"%string] [(EFunction (FunDecl [] (ELiteral (Integer 6))))] (EApply "X"%string []))) )
].


Example fun2 : ([], [], ELet ["X"%string] [(EFunction (FunDecl [] (ELiteral (Integer 5))))] (ELet ["X"%string] [(EFunction (FunDecl [] (ELiteral (Integer 6))))] (EApply "X"%string []))) -e> ELiteral (Integer 6).
Proof.
  apply eval_let with (exprs2 := [EFunction (FunDecl [] (ELiteral (Integer 5))) p: VJ_Function _]).
  * reflexivity.
  * simpl. intros. inversion H.
    - inversion H0. value_var_solver.
    - inversion H0.
  * simpl. value_var_solver. apply eval_let with (exprs2 := [EFunction (FunDecl [] (ELiteral (Integer 6))) p: VJ_Function _]).
    - reflexivity.
    - simpl. intros. inversion H.
      + inversion H0. value_var_solver.
      + inversion H0.
    - simpl. value_var_solver. apply eval_apply with (exprs2 := []).
      + reflexivity.
      + simpl. intros. inversion H.
      + simpl. value_var_solver.
Qed.

Compute initialize_proving B.

Compute initialize_proving_closures B.

End B_Core.

Section Documentation_Examples.

Example ex1 : ([], [], ELet ["X"%string] [ELiteral (Integer 5)] (EVar "X"%string)) -e> ELiteral (Integer 5).
Proof.
  apply eval_let with ([ELiteral (Integer 5) p: VJ_Literal _]).
  * reflexivity.
  * intros. inversion H.
    - inversion H0. subst. right. reflexivity.
    - inversion H0.
  * simpl. split. 2: apply VJ_Literal. left. apply eval_var.
Qed.

Example ex2 : ([], [], ELet ["X"%string] [EFunction (FunDecl [] (EApply "X"%string []))] (EApply "X"%string [])) -e> ErrorExp.
Proof.
  apply eval_let with ([EFunction (FunDecl [] (EApply "X"%string [])) p: VJ_Function _]).
  * reflexivity.
  * intros. inversion H.
    - inversion H0. subst. simpl. right. reflexivity.
    - inversion H0.
  * simpl. value_var_solver. apply eval_apply with ([]).
    - reflexivity.
    - intros. inversion H.
    - simpl. value_var_solver. unfold get_fun_exp. simpl. apply eval_apply with [].
      + reflexivity.
      + intros. inversion H.
      + simpl. value_var_solver.
Qed.

Example ex3 :  ([], [], ELetrec [("X"%string, 0)] [FunDecl [] (EApplyTopLevel ("X"%string, 0) [])] (EApplyTopLevel ("X"%string, 0) [])) -e> ELiteral EmptyTuple.
Proof.
  apply eval_letrec.
  * reflexivity.
  * simpl. split. 2: apply VJ_Literal. left. apply eval_apply_top with [].
    - reflexivity.
    - reflexivity.
    - intros. inversion H.
    - simpl. split. 2: apply VJ_Literal. left. apply eval_apply_top with [].
      + reflexivity.
      + reflexivity.
      + intros. inversion H.
      + simpl. value_var_solver. simpl. apply eval_apply_top with [].
Admitted.

End Documentation_Examples.

End Core_Erlang_Examples.