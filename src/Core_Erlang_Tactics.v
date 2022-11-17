Require Core_Erlang_Semantics.

Module Tactics.

(**
  IMPORTANT NOTICE:
  To use the `solve` tactic, the abbreviations (e.g. `EEmptyTuple`)
  should not be used (use `ETuple []` instead).
*)

Export Core_Erlang_Semantics.Semantics.
Export Core_Erlang_Helpers.Helpers.
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

(* Section Optimization.

Fixpoint is_literal_list (l : list Expression) : bool :=
match l with
| [] => true
| (ELit _)::xs => is_literal_list xs
| _ => false
end.

Fixpoint literal_list_to_value_list (l : list Expression) : list Value :=
match l with
| [] => []
| (ELit x)::xs => (VLit x)::(literal_list_to_value_list xs)
| _ => []
end.

Theorem eval_lit_list :
  forall l env id eff,
  is_literal_list l = true
->
  (forall i, i < length l -> |env, id, nth i l ErrorExp, eff| 
  -e> 
  |id, inl (nth i (literal_list_to_value_list l) ErrorValue), eff|).
Proof.
  induction l; intros.
  * inversion H0.
  * simpl in H0, H. destruct i.
    - simpl. destruct a; try (inversion H).
      + simpl. apply eval_lit.
    - simpl. destruct a; try (inversion H). simpl. apply IHl.
      + assumption.
      + lia.
Qed.

Fixpoint make_list {A : Type} (e : A) (n : nat) : list A :=
match n with
| 0 => []
| S n' => e::(make_list e n')
end.

Theorem length_lit_list :
  forall l, is_literal_list l = true -> 
  length l = length (literal_list_to_value_list l).
Proof.
  intros. induction l.
  * simpl. reflexivity.
  * simpl. destruct a; try (inversion H).
    - simpl. rewrite (IHl H1). auto.
Qed.

Theorem make_list_length :
  forall {A : Type} e n, length (@make_list A e n) = n.
Proof.
  intros. induction n.
  * simpl. reflexivity.
  * simpl. rewrite (IHn). auto.
Qed.

Theorem last_make_list :
  forall {A : Type} e n, last (@make_list A e n) e = e.
Proof.
  intros. induction n.
  * simpl. reflexivity.
  * simpl. rewrite (IHn). destruct (make_list e n); auto.
Qed.

Theorem nth_make_list :
  forall {A : Type} e def n i, i < n -> nth i (@make_list A e n) def = e.
Proof.
  induction n; intros.
  * inversion H.
  * simpl. destruct i; auto.
    - apply lt_S_n in H. apply IHn. auto.
Qed.

Theorem nth_def_make_list :
  forall {A : Type} e def n i, i < n -> nth_def (@make_list A e n) e def i = e.
Proof.
  intros. unfold nth_def. destruct i.
  * auto.
  * apply nth_make_list. lia.
Qed.

Theorem S_nth_def_make_list :
  forall {A : Type} e def n i, i < n -> nth_def (@make_list A e n) e def (S i) = e.
Proof.
  intros. unfold nth_def. apply nth_make_list. auto.
Qed.

Theorem quick_tuple_eval :
  forall l env id eff,
  is_literal_list l = true
->
  |env, id, ETuple l, eff| -e> |id, inl (VTuple (literal_list_to_value_list l)), eff |.
Proof.
  intros. eapply eval_tuple with (eff := make_list eff (length l)) (ids := make_list id (length l)).
  - apply length_lit_list. assumption.
  - rewrite make_list_length. auto.
  - rewrite make_list_length. auto.
  - intros. pose (eval_lit_list l env id eff H i H0).
    rewrite nth_def_make_list, nth_def_make_list, S_nth_def_make_list, S_nth_def_make_list. all: auto.
  - apply eq_sym, last_make_list.
  - apply eq_sym, last_make_list.
Qed.

Fixpoint check_lit_cons (e : Expression) : bool :=
match e with
| ENil => true
| ECons (ELit x) y => match y with
                      | ENil => true 
                      | ECons y' z => check_lit_cons y
                      | ELit y' => true
                      | _ => false
                      end
| _ => false
end.

Fixpoint exp_cons_to_val_cons (e : Expression) : Value :=
match e with
| ENil => VNil
| ECons (ELit x) y => match y with
                      | ENil => VCons (VLit x) VNil 
                      | ECons y' z => VCons (VLit x) (exp_cons_to_val_cons y)
                      | ELit y' => VCons (VLit x) (VLit y')
                      | _ => ErrorValue
                      end
| _ => ErrorValue
end.

Theorem quick_list_eval :
  forall e env id eff, check_lit_cons e = true
->
  | env, id, e, eff | -e> | id, inl (exp_cons_to_val_cons e), eff|.
Proof.
  induction e; intros; try (inversion H).
  * simpl. apply eval_nil.
  * simpl. destruct e4, e5; try (inversion H1).
    - eapply eval_cons. apply eval_nil. apply eval_lit.
    - eapply eval_cons; apply eval_lit.
    - eapply eval_cons. 2: apply eval_lit.
      + apply IHe2. assumption.
Qed.

End Optimization. *)

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
| |- | ?env, ?module, ?own_module, ?id, ENil, ?eff | -e> | ?id', ?res, ?eff'| => apply eval_nil
| |- | ?env, ?module, ?own_module, ?id, ELit ?lit, ?eff | -e> | ?id', ?res, ?eff'| => apply eval_lit
| |- | ?env, ?module, ?own_module, ?id, EVar ?v, ?eff | -e> | ?id', ?res, ?eff'| => apply eval_var; reflexivity
| |- | ?env, ?module, ?own_module, ?id, EFunId ?fid, ?eff | -e> | ?id', ?res, ?eff'| => (apply eval_funid; reflexivity) + (eapply eval_funid_module; reflexivity) 
| |- | ?env, ?module, ?own_module, ?id, EFun ?pl ?b, ?eff | -e> | ?id', ?res, ?eff'| => apply eval_fun
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
(* | |- | ?env, ?module, ?own_module, ?id, ESingle _, ?eff | -e> | ?id', ?res, ?eff'| => apply eval_single; solve *)
| |- | ?env, ?module, ?own_module, ?id, EValues _, ?eff | -e> | ?id', ?res, ?eff'| =>
     (eapply eval_values; 
     unfold_list2;
     unfold_elements;
     solve_inners;
     try(simpl;reflexivity);
     auto)
     +
     valuelist_exception_solver 0

| |- | ?env, ?module, ?own_module, ?id, ENil, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?module, ?own_module, ?id, ENil, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?module, ?own_module, ?id, ELit ?lit, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?module, ?own_module, ?id, EVar ?v, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?module, ?own_module, ?id, EFunId ?fid, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?module, ?own_module, ?id, EFun ?pl ?b, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?module, ?own_module, ?id, ETuple ?l, ?eff | -e> | ?id', ?res, ?eff'| =>
     (* (apply quick_tuple_eval; simpl; reflexivity)
     + *)
     (eapply eval_tuple;
     unfold_list2;
     unfold_elements;
     solve_inners;
     try(simpl;reflexivity);
     auto)
     + tuple_exception_solver 0
| |- | ?env, ?module, ?own_module, ?id, ECons _ _, ?eff | -e> | ?id', ?res, ?eff'| =>
     (* (apply quick_list_eval; simpl; reflexivity)
     + *)
     (eapply eval_cons; solve_inners)
     +
     (eapply eval_cons_tl_ex; solve_inners)
     +
     (eapply eval_cons_hd_ex; solve_inners)
| |- | ?env, ?module, ?own_module, ?id, ECase _ _, ?eff | -e> | ?id', ?res, ?eff'| =>
     case_solver 0
     +
     (eapply eval_case_pat_ex;
      solve_inners)
     +
     (eapply eval_case_clause_ex;
      (* unfold_list2;
      match goal with
      | |- forall i, i < length _ -> |_, _, _, _| -e> |_, _, _| =>
                                            unfold_elements;
                                            try(solve_inners)
      | _ => idtac
      end; *)
      solve_inners;
      intros;
      unfold_elements;
      match goal with
      
      | [H : match_clause _ _ _ = Some _ |- _] => inversion H
      | _ => idtac
      end;
      try(simpl;reflexivity);
      solve_inners)
| |- | ?env, ?module, ?own_module, ?id, ECall _ _ ?l, ?eff | -e> | ?id', ?res, ?eff'| =>  (* Need naother *)
     (eapply eval_call ;
     unfold_list2;
     solve_inners;
     unfold_elements;
     solve_inners;
     match goal with
     | |- eval _ _ _ _ = _ => tryif reflexivity then idtac else fail 1
     | _ => idtac
     end;
     auto)
     +
     (call_exception_solver 0)
| |- | ?env, ?module, ?own_module, ?id, EPrimOp _ _ ?l, ?eff | -e> | ?id', ?res, ?eff'| =>
     (eapply eval_call;
     unfold_list2;
     solve_inners;
     unfold_elements;
     solve_inners;
     match goal with
     | |- eval _ _ _ _ = _ => tryif reflexivity then idtac else fail 1
     | _ => idtac
     end;
     auto)
     +
     (primop_exception_solver 0)
| |- | ?env, ?module, ?own_module, ?id, EApp _ _, ?eff | -e> | ?id', ?res, ?eff'| => 
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
| |- | ?env, ?module, ?own_module, ?id, ELet _ _ _, ?eff | -e> | ?id', ?res, ?eff'| =>
     (eapply eval_let;
     solve_inners;
     try(simpl;reflexivity);
     auto)
     +
     (eapply eval_let_ex;
      solve_inners)
| |- | ?env, ?module, ?own_module, ?id, ESeq _ _, ?eff | -e> | ?id', ?res, ?eff'| =>
     (eapply eval_seq; solve_inners)
     +
     (eapply eval_seq_ex; solve_inners)
| |- | ?env, ?module, ?own_module, ?id, ELetRec _ _, ?eff | -e> | ?id', ?res, ?eff'| =>
     eapply eval_letrec;
     solve_inners
| |- | ?env, ?module, ?own_module, ?id, EMap ?l, ?eff | -e> | ?id', ?res, ?eff'| =>
     (eapply eval_map;
     unfold_list2;
     unfold_elements;
     solve_inners;
     try(simpl;reflexivity);
     auto)
     +
     (map_key_exception_solver 0)
| |- | ?env, ?module, ?own_module, ?id, ETry _ _ _ _ _, ?eff | -e> | ?id', ?res, ?eff'| =>
     (eapply eval_try;
      unfold_list2;
      solve_inners
      auto)
     +
     (
      eapply eval_catch;
      solve_inners
     )
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
| |- | _, _, _, _, _, _ | -e> | _, _, _ | => tryif solve then idtac else fail 1
| |- | _, _, _, _, _, _ | -e> | _, _, _ | => tryif solve then idtac else fail 1
| _ => idtac
end
with
case_solver num :=
  tryif 
    eapply eval_case with (i := num);
    match goal with
    | |- _ < _ => tryif simpl; lia then idtac else fail 2
    | _ => idtac
    end;
    try solve_inners;
    match goal with
     | |- match_clause _ _ _ = _ => tryif reflexivity then idtac else fail 1
     | _ => idtac
    end;
    match goal with
    | |- |_, _, _, _, _, _| -e> |_, inl ttrue, _| => tryif solve then idtac else fail 1
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
  | |- |_, _, _, _, _, _| -e> | _, inl _, _ | => fail 1
  | _ =>
  tryif
    eapply eval_tuple_ex with (i := num);
    match goal with
    | |- _ < _ => tryif simpl; lia then idtac else fail 2
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
valuelist_exception_solver num :=
  match goal with
  | |- |_, _, _, _, _, _| -e> | _, inl _, _ | => fail 1
  | _ =>
  tryif
    eapply eval_values_ex with (i := num);
    match goal with
    | |- _ < _ => tryif simpl; lia then idtac else fail 2
    | _ => idtac
    end;
    unfold_list2;
    unfold_elements;
    solve_inners
  then
    idtac
  else
    valuelist_exception_solver (S num)
  end
with
app_param_exception_solver num :=
  match goal with
  | |- |_, _, _, _, _, _ | -e> | _, inl _, _ | => fail 1
  | _ =>
    tryif
      eapply eval_app_param_ex with (i := num);
      match goal with
      | |- _ < _ => tryif simpl; lia then idtac else fail 2
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
  | |- |_, _, _, _, _, _| -e> | _, inl _, _ | => fail 1
  | _ =>
    tryif
      eapply eval_map_ex with (i := num);
      match goal with
      | |- _ < _ => tryif simpl; lia then idtac else fail 2
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
  | |- |_, _, _, _, _, _| -e> | _, inl _, _ | => fail 1
  | _ =>
    tryif
      eapply eval_call_ex with (i := num);
      match goal with
      | |- _ < _ => tryif simpl; lia then idtac else fail 2
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
with
primop_exception_solver num :=
  match goal with
  | |- |_, _, _, _, _, _| -e> | _, inl _, _ | => fail 1
  | _ =>
    tryif
      eapply eval_call_ex with (i := num);
      match goal with
      | |- _ < _ => tryif simpl; lia then idtac else fail 2
      | _ => idtac
      end;
      unfold_list2;
      unfold_elements;
      solve_inners
    then
      idtac
    else
      primop_exception_solver (S num)
  end
.

End Tactics.