Require Core_Erlang_Semantics.

Module Tactics.

(**
  IMPORTANT NOTE:
  To use the `solve` tactic, the abbreviations (e.g. `EEMptyTuple`)
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

(* Ltac simpl_concatn :=
  unfold concatn; simpl; simpl_app.

Ltac simpl_concatn_H Hyp0 :=
    unfold concatn in Hyp0; simpl in Hyp0; simpl_app_H Hyp0. *)

(* List unfolding tactics *)
(* Ltac unfold_list :=
match goal with
| [ H : Datatypes.length ?l = 0 |- _] => apply length_zero_iff_nil in H; subst
| [ H : 0 = Datatypes.length ?l |- _] => apply eq_sym, length_zero_iff_nil in H; subst
| [ H : Datatypes.length ?l = S ?n |- _] => symmetry in H; unfold_list
| [ H : S ?n = Datatypes.length ?l |- _] => 
   pose (element_exist _ _ _ H);
   match goal with
   | [H' : exists x l', _ = x::l' |- _] => 
     inversion H';
     match goal with
     | [H'' : exists l', _ = ?x::l' |- _] => inversion H''; subst; simpl in H; 
                                             inversion H; unfold_list
     end
   end
end
. *)

(* Ltac single_unfold_list :=
match goal with
| [ Hyp : Datatypes.length ?l = 0 |- _] => apply length_zero_iff_nil in Hyp; subst
| [ Hyp : 0 = Datatypes.length ?l |- _] => apply eq_sym, length_zero_iff_nil in Hyp; subst
| [ Hyp : Datatypes.length ?l = S ?n |- _] => symmetry in Hyp; unfold_list
| [ Hyp : S ?n = Datatypes.length ?l |- _] => 
   pose (element_exist _ _ _ Hyp);
   match goal with
   | [H' : exists x l', _ = x::l' |- _] => 
     inversion H';
     match goal with
     | [H'' : exists l', _ = ?x::l' |- _] => inversion H''; subst; simpl in Hyp; inversion Hyp
     end
   end
end
. *)

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
simpl; repeat (eapply length_succ); empty_list.

Ltac solve :=
unfold nth_def; simpl;
match goal with
| |- | ?env, ?id, ENil, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?id, ELit ?lit, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?id, EVar ?v, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?id, EFunId ?fid, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?id, EFun ?pl ?b, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?id, ETuple ?l, ?eff | -e> | ?id', ?res, ?eff'| =>
     eapply eval_tuple;
     unfold_list2;
     unfold_elements;
     solve_inners;
     try(simpl;reflexivity);
     auto
| |- | ?env, ?id, ECons _ _, ?eff | -e> | ?id', ?res, ?eff'| =>
     (eapply eval_cons; solve_inners)
     +
     (eapply eval_cons_ex_tl; solve_inners)
     +
     (eapply eval_cons_ex_hd; solve_inners)
| |- | ?env, ?id, ECase _ _, ?eff | -e> | ?id', ?res, ?eff'| =>
     case_solver 0
| |- | ?env, ?id, ECall _ ?l, ?eff | -e> | ?id', ?res, ?eff'| =>
     eapply eval_call;
     unfold_list2;
     solve_inners;
     unfold_elements;
     solve_inners;
     try(simpl;reflexivity);
     auto
| |- | ?env, ?id, EApp _ _, ?eff | -e> | ?id', ?res, ?eff'| => 
     eapply eval_app;
     unfold_list2;
     unfold_elements;
     solve_inners;
     try(simpl;reflexivity);
     auto
| |- | ?env, ?id, ELet _ _, ?eff | -e> | ?id', ?res, ?eff'| =>
     eapply eval_let;
     unfold_list2;
     unfold_elements;
     solve_inners;
     try(simpl;reflexivity);
     auto
| |- | ?env, ?id, ELetRec _ _, ?eff | -e> | ?id', ?res, ?eff'| =>
     eapply eval_letrec;
     solve_inners
| |- | ?env, ?id, EMap ?l, ?eff | -e> | ?id', ?res, ?eff'| =>
     eapply eval_map;
     unfold_list2;
     unfold_elements;
     solve_inners;
     try(simpl;reflexivity);
     auto
| |- | ?env, ?id, ETry _ _ _ _ _ _, ?eff | -e> | ?id', ?res, ?eff'| =>
     eapply eval_try;
     unfold_list2;
     unfold_elements;
     solve_inners;
     try(simpl;reflexivity);
     auto
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
  (eapply eval_case with (i := num);
    try(solve_inners);
    match goal with
     | |- match_clause _ _ _ = _ => tryif reflexivity then idtac else fail 1
         (* simpl; 
         match goal with
         | |- None = Some _ => fail
         | |- Some _ = Some _ => reflexivity
         | |- Some _ = None => fail
         | _ => idtac
         end *)
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
    auto) + case_solver (S num)
.

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