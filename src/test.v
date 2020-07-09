Require Import Core_Erlang_Semantics.

Import Core_Erlang_Environment.Environment.
Import Core_Erlang_Helpers.Helpers.
Import Core_Erlang_Syntax.Syntax.
Import Core_Erlang_Side_Effects.Side_Effects.
Import Core_Erlang_Semantics.Semantics.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.

Import Omega.

Set Ltac Backtrace.

Theorem alma {A B : Type} (a1 : A) (a2 : B) (l1 : list A) (l2 : list B):
length l1 = length l2
->
length (a1 :: l1) = length (a2 :: l2).
Proof.
  intros. simpl. rewrite H. auto.
Qed.

Theorem length_succ {B : Type} (a2 : B) (n : nat) (l2 : list B):
n = length l2
->
S n = length (a2 :: l2).
Proof.
  intros. simpl. rewrite H. auto.
Qed.

Ltac empty_list :=
simpl;
match goal with
| |- 0 = length ?l => instantiate (1 := []); auto
| |- length ?l = 0 => instantiate (1 := []); auto
end.

Ltac element_list := 
idtac
.

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

Ltac unfold_list :=
simpl; repeat (eapply length_succ); empty_list.

Ltac one_step_solver :=
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
| |- | _, _, _, _ | -e> | _, _, _ | => one_step_solver
| _ => idtac
end
.

(**
  Tactic thoughts:
  - first apply the matching derivation rule
  - unfold existential lists
  - solve subgoals recursively
  - cleanup with auto
*)

Goal
  | [], 0, ETuple [], [] | -e> |0, inl (VTuple []), [] |.
Proof.
  one_step_solver.
Qed.

Goal
  | [], 0, ETuple [ELit (Integer 1)], [] | -e> |0, inl (VTuple [VLit (Integer 1)]), [] |.
Proof.
  one_step_solver.
Qed.

Goal
  | [], 0, ETuple [ELit (Integer 1); ELit (Integer 2)], [] | 
-e> 
  |0, inl (VTuple [VLit (Integer 1); VLit (Integer 2)]), [] |.
Proof.
  one_step_solver.
Qed.

Goal
  | [], 0, ETuple [ELit (Integer 1); ELit (Integer 2); ELit (Integer 2); ELit (Integer 2)], [] | 
-e> 
  |0, inl (VTuple [VLit (Integer 1); VLit (Integer 2); VLit (Integer 2); VLit (Integer 2)]), [] |.
Proof.
  one_step_solver.
Qed.

Goal
  | [], 0, ETuple [ETuple [ELit (Integer 1); ELit (Integer 2); ELit (Integer 2); ELit (Integer 2)]; ELit (Integer 2); ELit (Integer 2); ELit (Integer 2)], [] | 
-e> 
  |0, inl (VTuple [VTuple [VLit (Integer 1); VLit (Integer 2); VLit (Integer 2); VLit (Integer 2)]; VLit (Integer 2); VLit (Integer 2); VLit (Integer 2)]), [] |.
Proof.
  one_step_solver.
Qed.


Goal
  | [], 0, ECall "plus"%string [ELit (Integer 1); ELit (Integer 2)], [] | -e> |0, inl (VLit (Integer 3)), [] |.
Proof.
  eapply eval_call; auto.
  * unfold_list.
  * unfold_list.
  * unfold_list.
  * intros. inversion H. 2: inversion H1.
    - finishing_tactic.
    - finishing_tactic.
    - inversion H3.
  * simpl. reflexivity.
  * auto.
Qed.

Goal 
  |[], 0,
   ELet [("X"%string, EFun [] (ELit (Integer 1))); 
         ("Y"%string, EFun [] (ELit (Integer 2))); 
         ("Z"%string, EFun [] (ELit (Integer 3)))]
     (EMap [(EVar "Z"%string, ELit (Integer 10)); 
            (EVar "X"%string, ELit (Integer 11));
            (EVar "Y"%string, ELit (Integer 12)); 
            (EVar "X"%string, ELit (Integer 13))])
  , []| 
-e> 
  | 3, inl (VMap [(VClos [] [] 0 [] (ELit (Integer 1)), VLit (Integer 13));
                  (VClos [] [] 1 [] (ELit (Integer 2)), VLit (Integer 12));
                  (VClos [] [] 2 [] (ELit (Integer 3)), VLit (Integer 10))])
  , []|.
Proof.
  eapply eval_let; auto.
  * unfold_list.
  * unfold_list.
  * unfold_list.
  * intros. inversion H. 2: inversion H1. 3: inversion H3. 4: inversion H5.
    all: simpl; apply eval_fun.
  * eapply eval_map; auto.
    - simpl. auto.
    - unfold_list.
    - unfold_list.
    - unfold_list.
    - unfold_list.
    - intros. inversion H. 2: inversion H1. 3: inversion H3. 4: inversion H5. 5: inversion H7.
      1-4: finishing_tactic.
    - intros. inversion H. 2: inversion H1. 3: inversion H3. 4: inversion H5. 5: inversion H7.
      1-4: finishing_tactic.
    - reflexivity.
    - reflexivity.
    - auto.
Qed.