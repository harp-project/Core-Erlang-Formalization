From CoreErlang.FrameStack Require Import SubstSemantics SubstSemanticsLemmas.
From CoreErlang.Interpreter Require Import StepFunctions Equivalences.
From CoreErlang.Symbolic Require Import SymbTheorems SymbTactics.

Import ListNotations.

(** This file gives some examples for the "solve_symbolically" tactic.
 *)

Definition fact_frameStack (e : Exp) : Exp :=
  ELetRec
    [(1, °ECase (˝VVar 1) [
      ([PLit 0%Z], ˝ttrue, (˝VLit 1%Z));
      ([PVar], ˝ttrue,
        °ELet 1 (EApp (˝VFunId (1, 1))
          [°ECall (˝VLit "erlang"%string) (˝VLit "-"%string) [˝VVar 0; ˝VLit 1%Z]])
          (°ECall (˝VLit "erlang"%string) (˝VLit "*"%string) [˝VVar 1; ˝VVar 0])
      )
    ])]
    (EApp (˝VFunId (0, 1)) [e])
.

(* Proving that fact_frameStack is equivalent to Coq's factorial.
   This requires some manual work for proving the postcondition in the inductive case.
 *)
Theorem fact_eval_ex:
  forall (z : Z), (0 <= z)%Z ->
  exists (y : Z),
  ⟨ [], (fact_frameStack (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ (y = Z.of_nat (Factorial.fact (Z.to_nat z))%Z).
Proof.
  solve_symbolically z.

  destruct PreCond0. subst.
  destruct H. subst. clear H.
  rewrite Z2Nat.inj_sub;[|lia].
  Search Z.to_nat Z.pos.
  assert (Z.to_nat 1%Z = 1). { lia. }
  rewrite H. clear H.
  rewrite Z2Nat.inj_pos.
  rewrite <- positive_nat_Z at 1.
  rewrite <- Nat2Z.inj_mul. f_equal.
  remember (Pos.to_nat p) as k.
  destruct k.
  * lia.
  * simpl. rewrite Nat.sub_0_r. reflexivity.
Qed.

Definition tailrec_fact (e d : Exp) : Exp :=
  ELetRec [
    (2, °ECase (˝VVar 1) [
        ([PLit (Integer 0%Z)], ˝ttrue, ˝VVar 2);
        ([PVar], ˝ttrue,
          (°EApp (˝VFunId (1, 2)) 
            [°ECall (˝erlang) (˝VLit "-"%string) [˝VVar 0; ˝VLit 1%Z];
             °ECall (˝erlang) (˝VLit "*"%string) [˝VVar 0; ˝VVar 3]
            ]))
      ]
    )
  ] (EApp (˝VFunId (0, 2)) [e; d]) 
.

(* Proving that tailrec_fact works equivalently to Coq's factorial.
   This also requires some manual work for the postcondition, and also when stating
   the theorem itself it needs to be proven for a general second argument.
 *)
Theorem fact_tailrec_eval_ex:
  forall (z : Z) (z' : Z), (0 <= z)%Z ->
  exists (y : Z),
  ⟨ [], (tailrec_fact (˝VLit z) (˝VLit z')) ⟩ -->* RValSeq [VLit y] /\ (y = Z.of_nat (Factorial.fact (Z.to_nat z)) * z')%Z.
Proof.
  solve_symbolically z z'.
  
  destruct PreCond0. subst.
  rewrite Z.mul_assoc. f_equal.
  rewrite <- positive_nat_Z.
  rewrite <- Nat2Z.inj_mul. f_equal.
  assert (1%Z = Z.of_nat (Z.to_nat 1%Z))%Z by lia. rewrite H0. clear H0.
  rewrite <- Nat2Z.inj_sub;[|lia].
  do 2 rewrite Nat2Z.id.
  remember (Pos.to_nat p) as k.
  pose proof Pos2Nat.is_pos p.
  destruct k; try lia.
  simpl.
  rewrite Nat.sub_0_r. lia. 
Qed.

Definition timestwo (e : Exp) : Exp :=
  ELetRec [
      (1, °ECall (˝erlang) (˝VLit "*"%string) [˝VVar 1; ˝VLit 2%Z]
      
      )
    ] (EApp (˝VFunId (0, 1)) [e]).

Definition timestwo' (e : Exp) : Exp :=
  °ECall (˝erlang) (˝VLit "*"%string) [e; ˝VLit 2%Z].

(* The tactic works with functions that are defined to be recursive, but actually are not. *)
Theorem timestwo_ex:
  forall (z : Z), True ->
  exists (y : Z),
  ⟨ [], (timestwo (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ (y = z * 2)%Z.
Proof.
  solve_symbolically z.
Qed.

(* The tactic works for non-recursive functions. *)
Theorem timestwo'_ex:
  forall (z : Z), True ->
  exists (y : Z),
  ⟨ [], (timestwo' (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ (y = z * 2)%Z.
Proof.
  solve_symbolically z.
Qed.

Definition times_two_simple (e : Exp) : Exp :=
  (EExp (ECall (VVal (VLit (Atom "erlang"%string))) (VVal (VLit (Atom "*"%string))) [e;(VVal (VLit (Integer (2))))])).

(* Multiplying by two, using 'erlang':'*' *)
Theorem times_two_simple_ex:
  forall (z : Z), True ->
  exists (y : Z),
  ⟨ [], (times_two_simple (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ (y = z * 2)%Z.
Proof.
  solve_symbolically z.
Qed.

Definition times_two_rec (e : Exp) : Exp := ELetRec [
(1, (EExp (ECase (VVal (VVar 1)) 
[
  ([(PLit (Integer (0)))], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Integer (0)))));
  ([PVar], (VVal (VLit (Atom "true"%string))), 
    (EExp (ELet 1 (EExp (ECall (VVal (VLit (Atom "erlang"%string))) (VVal (VLit (Atom "-"%string))) [(VVal (VVar 0));(VVal (VLit (Integer (1))))])) 
    (EExp (ECall (VVal (VLit (Atom "erlang"%string))) (VVal (VLit (Atom "+"%string))) [(EExp (EApp (VVal (VFunId (2, 1))) [(VVal (VVar 0))]));(VVal (VLit (Integer (2))))])))))])))] 

(EApp (VVal (VFunId (0, 1))) [e]).

(* Multiplying by two, using a recursive definition. (1 argument for the tactic) *)
Theorem times_two_rec_ex:
  forall (z : Z), (0 <= z)%Z ->
  exists (y : Z),
  ⟨ [], (times_two_rec (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ (y = z * 2)%Z.
Proof.
  solve_symbolically z.
Qed.

Definition plus_nums_simple (e f : Exp) : Exp :=
(EExp (ECall (VVal (VLit (Atom "erlang"%string))) (VVal (VLit (Atom "+"%string))) [e;f])).

(* Adding two numbers using 'erlang':'+'. *)
Theorem plus_nums_simple_ex:
  forall (z : Z) (z' : Z), True ->
  exists (y : Z),
  ⟨ [], (plus_nums_simple (˝VLit z) (˝VLit z')) ⟩ -->* RValSeq [VLit y] /\ (y = z + z')%Z.
Proof.
  solve_symbolically z.
Qed.

Definition plus_nums_rec (e f : Exp) := ELetRec [(2, (EExp (ECase (VVal (VVar 1)) [([(PLit (Integer (0)))], (VVal (VLit (Atom "true"%string))), (VVal (VVar 2)));([PVar], (VVal (VLit (Atom "true"%string))), (EExp (ELet 1 (EExp (ECall (VVal (VLit (Atom "erlang"%string))) (VVal (VLit (Atom "-"%string))) [(VVal (VVar 0));(VVal (VLit (Integer (1))))])) (EExp (ELet 1 (EExp (ECall (VVal (VLit (Atom "erlang"%string))) (VVal (VLit (Atom "+"%string))) [(VVal (VVar 4));(VVal (VLit (Integer (1))))])) (EExp (EApp (VVal (VFunId (3, 2))) [(VVal (VVar 1));(VVal (VVar 0))])))))))])))] (EApp (VVal (VFunId (0, 2))) [e;f]).

Theorem plus_nums_rec_ex:
  forall (z : Z),
  exists (y : Z),
  ⟨ [], (plus_nums_rec (˝VLit z) (˝VLit 0%Z)) ⟩ -->* RValSeq [VLit y] /\ (y = z)%Z.
Proof.
  (* This cannot be proven by induction, since the goal is too specific. *)
Abort.

(* Adding two numbers using a recursive definition. (2 arguments for the tactic) *)
Theorem plus_nums_rec_ex':
  forall (z : Z) (z' : Z), (z >= 0)%Z ->
  exists (y : Z),
  ⟨ [], (plus_nums_rec (˝VLit z) (˝VLit z')) ⟩ -->* RValSeq [VLit y] /\ (y = z + z')%Z.
Proof.
  solve_symbolically z z'.
Qed.

Definition isitzero_atom (e : Exp) : Exp :=
(EExp (ECase (e) [([(PLit (Integer (0)))], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Atom "true"%string))));([PVar], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Atom "false"%string))))])).

(* Theorem with atom in the postcondition instead of Z. This is just a case expression,
   not a function application. *)
Theorem isitzero_atom_ex:
  forall (z : Z), (z >= 0)%Z ->
  exists (y : string),
  ⟨ [], (isitzero_atom (˝VLit (Z.succ z))) ⟩ -->* RValSeq [VLit y] /\ (y = "false"%string)%Z.
Proof.
  solve_symbolically z.
Qed.

Definition isitzero_num (e : Exp) : Exp :=
(EExp (ECase (e) [([(PLit (Integer (0)))], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Integer (1)))));([PVar], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Integer (0)))))])).

Theorem isitzero_num_ex:
  forall (z : Z), True ->
  exists (y : Z),
  ⟨ [], (isitzero_num (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ ((y = 0)%Z \/ (y = 1)%Z).
Proof.
  solve_symbolically z.
Qed.

Definition isitzero_num_app (e : Exp) : Exp :=
EExp ( EApp ( EFun 1 (EExp (ECase (VVal (VVar 0)) [([(PLit (Integer (0)))], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Integer (1)))));([PVar], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Integer (0)))))]))) [e]).

Theorem isitzero_num_app_ex:
  forall (z : Z), True ->
  exists (y : Z),
  ⟨ [], (isitzero_num_app (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ ((y = 0)%Z \/ (y = 1)%Z).
Proof.
  solve_symbolically z.
Qed.

(* Theorem with atom in the postcondition instead of Z. *)
Definition isitzero_atom_app (e : Exp) : Exp :=
EExp ( EApp ( EFun 1(EExp (ECase (VVal (VVar 0)) [([(PLit (Integer (0)))], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Atom "true"%string))));([PVar], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Atom "false"%string))))]))) [e]).

Theorem isitzero_atom_app_ex:
  forall (z : Z), (z > 0)%Z ->
  exists (y : string),
  ⟨ [], (isitzero_atom_app (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ (y = "false"%string).
Proof.
  solve_symbolically z.
Qed.

Theorem timestwo_ex':
  forall (z : Z),
  exists (y : Z),
  ⟨ [], (times_two_simple (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ (y = z * 2)%Z.
Proof.
  solve_symbolically z.
Qed.

Definition times_two_simple_app (e : Exp) : Exp :=
  EExp (EApp (EExp (EFun 1 (EExp (ECall (VVal (VLit (Atom "erlang"%string))) (VVal (VLit (Atom "*"%string))) [(VVal (VVar 0));(VVal (VLit (Integer (2))))])))) [e]).

Theorem timestwo_ex'':
  forall (z : Z),
  exists (y : Z),
  ⟨ [], (times_two_simple_app (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ (y = z * 2)%Z.
Proof.
  solve_symbolically z.
Qed.

Theorem timestwo_ex''':
  forall (z : Z), (0 <= z)%Z ->
  exists (y : Z),
  ⟨ [], (times_two_rec (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ (y = z * 2)%Z.
Proof.
  solve_symbolically z.
Qed.
