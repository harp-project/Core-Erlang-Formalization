Require Core_Erlang_Semantics.

Module Tactics.

(**
  IMPORTANT NOTICE:
  To use the `solve` tactic, the abbreviations (e.g. `EEmptyTuple`)
  should not be used (use `ETuple []` instead).
*)

Import Core_Erlang_Semantics.Semantics.
Import ListNotations.

Section Helper_Theorems.

Theorem length_succ {B : Type} (a2 : B) (n : nat) (l2 : list B):
n = length l2
->
S n = length (a2 :: l2).
Proof.
  intros. simpl. rewrite H. auto.
Qed.

End Helper_Theorems.

(** Macro tactics *)
Ltac simpl_app :=
  repeat (rewrite app_assoc);
  repeat (rewrite app_nil_r).

Ltac simpl_app_H Hyp0 :=
  repeat (rewrite app_assoc in Hyp0);
  repeat (rewrite app_nil_r in Hyp0).

Ltac finishing_tactic :=
unfold nth_def; simpl;
match goal with
| |- | ?env, ?id, ENil, ?eff | -e> | ?id', ?res, ?eff'| => apply eval_nil
| |- | ?env, ?id, ELit ?lit, ?eff | -e> | ?id', ?res, ?eff'| => apply eval_lit
| |- | ?env, ?id, EVar ?v, ?eff | -e> | ?id', ?res, ?eff'| => apply eval_var; reflexivity
| |- | ?env, ?id, EFunId ?fid, ?eff | -e> | ?id', ?res, ?eff'| => apply eval_funid; reflexivity
| |- | ?env, ?id, EFun ?pl ?b, ?eff | -e> | ?id', ?res, ?eff'| => apply eval_fun
end
.

Ltac empty_list :=
simpl;
match goal with
| |- 0 = length ?l => apply eq_sym, length_zero_iff_nil; reflexivity
| |- length ?l = 0 => apply length_zero_iff_nil; reflexivity
end.

Ltac unfold_list :=
simpl; 
match goal with
| |- length ?l = _ => symmetry; repeat (eapply length_succ); empty_list
| |- _ = length ?l => repeat (eapply length_succ); empty_list
| _ => idtac
end.

(** Solver tactic *)
Ltac solve :=
unfold nth_def; simpl;
match goal with
| |- | ?env, ?id, ENil, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?id, ELit ?lit, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?id, EVar ?v, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?id, EFunId ?fid, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?id, EFun ?pl ?b, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?id, ETuple ?l, ?eff | -e> | ?id', ?res, ?eff'| =>
     (eapply eval_tuple;
     unfold_list2;
     unfold_elements;
     solve_inners;
     try(simpl;reflexivity);
     auto)
     + tuple_exception_solver 0
| |- | ?env, ?id, ECons _ _, ?eff | -e> | ?id', ?res, ?eff'| =>
     (eapply eval_cons; solve_inners)
     +
     (eapply eval_cons_tl_ex; solve_inners)
     +
     (eapply eval_cons_hd_ex; solve_inners)
| |- | ?env, ?id, ECase _ _, ?eff | -e> | ?id', ?res, ?eff'| =>
     case_solver 0
     +
     (eapply eval_case_pat_ex; solve_inners)
     +
     (eapply eval_case_clause_ex; unfold_elements; 
      match goal with
      | [H : match_clause _ _ _ = Some _ |- _] => inversion H
      | _ => idtac
      end;
      solve_inners)
| |- | ?env, ?id, ECall _ ?l, ?eff | -e> | ?id', ?res, ?eff'| =>
     (eapply eval_call;
     unfold_list2;
     solve_inners;
     unfold_elements;
     solve_inners;
     match goal with
     | |- eval _ _ _ = _ => tryif reflexivity then idtac else fail 1
     | _ => idtac
     end;
     auto)
     +
     (call_exception_solver 0)
| |- | ?env, ?id, EApp _ _, ?eff | -e> | ?id', ?res, ?eff'| => 
     (eapply eval_app;
     unfold_list2;
     unfold_elements;
     solve_inners;
     try(simpl;reflexivity);
     auto)
     +
     (eapply eval_app_closure_ex; solve_inners)
     +
     (app_param_exception_solver 0)
     +
     (eapply eval_app_badfun_ex;
      unfold_list2;
      unfold_elements;
      solve_inners;
      try(simpl;reflexivity);
      try(congruence)
     )
     +
     (eapply eval_app_badarity_ex;
      unfold_list2;
      unfold_elements;
      solve_inners;
      try(simpl;reflexivity);
      try(congruence)
     )
| |- | ?env, ?id, ELet _ _, ?eff | -e> | ?id', ?res, ?eff'| =>
     (eapply eval_let;
     unfold_list2;
     unfold_elements;
     solve_inners;
     try(simpl;reflexivity);
     auto)
     +
     (let_exception_solver 0)
| |- | ?env, ?id, ELetRec _ _, ?eff | -e> | ?id', ?res, ?eff'| =>
     eapply eval_letrec;
     solve_inners
| |- | ?env, ?id, EMap ?l, ?eff | -e> | ?id', ?res, ?eff'| =>
     (eapply eval_map;
     unfold_list2;
     unfold_elements;
     solve_inners;
     try(simpl;reflexivity);
     auto)
     +
     (map_key_exception_solver 0)
| |- | ?env, ?id, ETry _ _ _ _ _ _, ?eff | -e> | ?id', ?res, ?eff'| =>
     (eapply eval_try;
     unfold_list2;
     unfold_elements;
     solve_inners;
     try(simpl;reflexivity);
     auto)
     +
     catch_solver 0
end
with unfold_list2 :=
match goal with
| |- ?n = length ?l => unfold_list
| |- length ?l = ?n => unfold_list
| _ => idtac
end
with unfold_elements :=
intros; simpl length in *;
match goal with
| [H : S ?i <= 0 |-_ ] => inversion H
| [H : ?i < 0 |-_ ] => inversion H
| [H : S ?i <= ?n |-_ ] => inversion H; clear H; subst; unfold_elements
| [H : ?i < ?n |-_ ] => inversion H; clear H; subst; unfold_elements
| _ => idtac
end
with
solve_inners :=
match goal with
| |- | _, _, _, _ | -e> | _, _, _ | => tryif solve then idtac else fail 1
| _ => idtac
end
with
case_solver num :=
  tryif 
    eapply eval_case with (i := num);
    match goal with
    | |- _ < _ => tryif simpl; omega then idtac else fail 2
    | _ => idtac
    end;
    try(solve_inners);
    match goal with
     | |- match_clause _ _ _ = _ => tryif reflexivity then idtac else fail 1
     | _ => idtac
    end;
    match goal with
    | |- |_, _, _, _| -e> |_, inl ttrue, _| => tryif solve then idtac else fail 1
    | _ => idtac
    end;
    unfold_elements;
    match goal with
     | [H : match_clause _ _ _ = Some _ |- _] => inversion H
     | _ => idtac
    end;
    solve_inners;
    auto
  then idtac
  else
     case_solver (S num)
with
tuple_exception_solver num :=
  match goal with
  | |- |_, _, _, _| -e> | _, inl _, _ | => fail 1
  | _ =>
  tryif
    eapply eval_tuple_ex with (i := num);
    match goal with
    | |- _ < _ => tryif simpl; omega then idtac else fail 2
    | _ => idtac
    end;
    unfold_list2;
    unfold_elements;
    solve_inners
  then
    idtac
  else
    tuple_exception_solver (S num)
  end
with
catch_solver num :=
  tryif
    eapply eval_catch with (i := num);
    match goal with
    | |- _ < _ => tryif simpl; omega then idtac else fail 2
    | _ => idtac
    end;
    unfold_list2;
    unfold_elements;
    solve_inners
  then
    idtac
  else
    catch_solver (S num)
with
let_exception_solver num :=
  match goal with
  | |- |_, _, _, _| -e> | _, inl _, _ | => fail 1
  | _ =>
    tryif
      eapply eval_let_ex with (i := num);
      match goal with
      | |- _ < _ => tryif simpl; omega then idtac else fail 2
      | _ => idtac
      end;
      unfold_list2;
      unfold_elements;
      solve_inners
    then
      idtac
    else
      let_exception_solver (S num)
  end
with
app_param_exception_solver num :=
  match goal with
  | |- |_, _, _, _| -e> | _, inl _, _ | => fail 1
  | _ =>
    tryif
      eapply eval_app_param_ex with (i := num);
      match goal with
      | |- _ < _ => tryif simpl; omega then idtac else fail 2
      | _ => idtac
      end;
      unfold_list2;
      unfold_elements;
      solve_inners
    then
      idtac
    else
      app_param_exception_solver (S num)
  end
with
map_key_exception_solver num :=
  match goal with
  | |- |_, _, _, _| -e> | _, inl _, _ | => fail 1
  | _ =>
    tryif
      eapply eval_map_key_ex with (i := num);
      match goal with
      | |- _ < _ => tryif simpl; omega then idtac else fail 2
      | _ => idtac
      end;
      unfold_list2;
      unfold_elements;
      solve_inners
    then
      idtac
    else
      map_value_exception_solver num
  end
with
map_value_exception_solver num :=
  match goal with
  | |- |_, _, _, _| -e> | _, inl _, _ | => fail 1
  | _ =>
    tryif
      eapply eval_map_val_ex with (i := num);
      match goal with
      | |- _ < _ => tryif simpl; omega then idtac else fail 2
      | _ => idtac
      end;
      unfold_list2;
      unfold_elements;
      solve_inners
    then
      idtac
    else
      map_key_exception_solver (S num)
  end
with
call_exception_solver num :=
  match goal with
  | |- |_, _, _, _| -e> | _, inl _, _ | => fail 1
  | _ =>
    tryif
      eapply eval_call_ex with (i := num);
      match goal with
      | |- _ < _ => tryif simpl; omega then idtac else fail 2
      | _ => idtac
      end;
      unfold_list2;
      unfold_elements;
      solve_inners
    then
      idtac
    else
      call_exception_solver (S num)
  end
.

Definition exception_call : Expression := ECall "+" [ELit (Integer 5); ETuple []].

Definition exception_value : Value := VCons (VLit (Integer 5)) (VEmptyTuple).

Example map_eval_ex_val :
  |[], 0, EMap [(ErrorExp, EMap [(ErrorExp, ErrorExp); 
                (ErrorExp, exception_call);
                (ErrorExp, ErrorExp);
                (ErrorExp, ErrorExp)]); 
                (ErrorExp, exception_call);
                (ErrorExp, ErrorExp);
                (ErrorExp, ErrorExp)], []|
-e>
  |0, inr (badarith exception_value), []|.
Proof.
  unfold ErrorExp, exception_call.
  solve.
Qed.


















Reserved Notation "e --e-> v" (at level 50).
Inductive eval_to_result : Expression -> Value + Exception -> Prop :=
| eval_expr_intro e v : (exists n eff, | [], 0, e, [] | -e> |n, v, eff|) -> e --e-> v
where "e --e-> v" := (eval_to_result e v).

Goal
  exists v, ELet [("X"%string, ELit (Integer 5))] (EVar "X"%string)
  --e-> 
  v.
Proof.
  eexists.
  match goal with
  | |- ?a => assert a as Main
  end.
  * apply eval_expr_intro. eexists. eexists. solve.
  * simpl in *. Check Main.
    exact Main.
Qed.

Goal
  exists v,
  ELetRec [(("f"%string, 1), (["X"%string],
   ECase (EVar "X"%string)
          [(PLit (Integer 0), ELit (Atom "true"%string), ELit (Integer 5));
           (PLit (Integer 1), ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 0)]);
           (PVar "A"%string, ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 1)])]
   ))]
   (ELet [("X"%string, EFun ["F"%string]
       (ELetRec [(("f"%string, 1), (["X"%string], ELit (Integer 0)))] 
          (EApp (EVar "F"%string) [ELit (Integer 2)])
       ))
     ]
    (EApp (EVar "X"%string) [EFunId ("f"%string, 1)])
   )
   --e-> v.
Proof.
  eexists.
  match goal with
  | |- ?a => assert (a)
  end.
  * apply eval_expr_intro. eexists. eexists. solve.
  * Check H.
    exact H.
Qed.

Goal
  | [], 0, exception_call, [] | -e> |0, inr (badarith exception_value), []|.
Proof.
  unfold exception_call, exception_value.
  solve.
Qed.

Goal
  |[], 0, ECall "+"%string [ELit (Integer 5); exception_call], []|
-e>
  |0, inr (badarith exception_value), []|.
Proof.
  unfold exception_call, exception_value.
  solve.
Qed.











Goal
  |[], 0, ECons (EVar "Y"%string) (ErrorExp), []|
-e>
  | 0, inr (novar), []|.
Proof.
  unfold ErrorExp.
  solve.
Qed.

Goal
  |[], 0, ECons (ErrorExp) (ECons ((EVar "Y"%string)) (ENil)), []|
-e> 
  | 0, inr (novar), []|.
Proof.
  solve.
Qed.


Example case_eval2 :
  |[(inl "X"%string, VEmptyTuple)], 0,
   ECase (EVar "X"%string) 
         [(PLit (Integer 5), ELit (Atom "true"%string), ELit (Integer 5)); 
          (PLit (Integer 6), ELit (Atom "true"%string), ELit (Integer 6));
          (PVar "Z"%string, ELit (Atom "false"%string), EVar "Z"%string);
          (PVar "Z"%string, ELit (Atom "true"%string), EMap [])]

  , []|
-e> 
  | 0, inl (VMap []), []|.
Proof.
  solve.
Qed.

Goal
  |[], 0, ETry [(ETuple [], "X"%string)]
               (ELit (Atom "ok"%string)) 
               (ELit (Atom "error"%string)) 
               "Ex1"%string "Ex2"%string "Ex3"%string, []|
-e>
  |0, inl ok, []|
.
Proof.
  solve.
Qed.

End Tactics.