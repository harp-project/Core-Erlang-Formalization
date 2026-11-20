(**
  This file contains tests about exceptions in the frame stack semantics: their
  creation, propagation through the different language constructs, and
  catching them.
*)
From CoreErlang.FrameStack Require Import SubstSemanticsAutoSolver.

Import ListNotations.
Open Scope string_scope.

(** `5 + {}` raises a `badarith` exception. *)
Definition plus_5_tuple : Exp :=
  °ECall (˝VLit "erlang") (˝VLit "+") [˝VLit 5%Z; °ETuple []].

Definition exception : Exception :=
  badarith (VTuple [VLit "+"; VLit 5%Z; VTuple []]).

(** Raising an exception *)
Goal ⟨[], plus_5_tuple⟩ -->* RExc exception.
Proof. star_step_solver. Qed.

Goal ⟨[], °ECall (˝VLit "erlang") (˝VLit "error") [˝VLit "my_reason"]⟩
   -->* RExc (Error, VLit "my_reason", VNil).
Proof. star_step_solver. Qed.

Goal ⟨[], °ECall (˝VLit "erlang") (˝VLit "throw") [˝VLit "ball"]⟩
   -->* RExc (Throw, VLit "ball", VNil).
Proof. star_step_solver. Qed.

(** Propagation through the language constructs *)
Goal ⟨[], °ECons plus_5_tuple (˝VLit "error")⟩ -->* RExc exception.
Proof. star_step_solver. Qed.

Goal ⟨[], °ECons (˝VLit "error") plus_5_tuple⟩ -->* RExc exception.
Proof. star_step_solver. Qed.

Goal ⟨[], °ETuple [˝VLit 1%Z; plus_5_tuple; ˝VLit 2%Z]⟩ -->* RExc exception.
Proof. star_step_solver. Qed.

Goal ⟨[], °EMap [(˝VLit 1%Z, plus_5_tuple)]⟩ -->* RExc exception.
Proof. star_step_solver. Qed.

Goal ⟨[], °ELet 1 plus_5_tuple (˝VVar 0)⟩ -->* RExc exception.
Proof. star_step_solver. Qed.

Goal ⟨[], °ECase plus_5_tuple [([PVar], ˝VLit "true", ˝VLit 1%Z)]⟩ -->* RExc exception.
Proof. star_step_solver. Qed.

(** The rest of a sequence is not evaluated *)
Goal ⟨[], °ESeq plus_5_tuple (˝VLit 1%Z)⟩ -->* RExc exception.
Proof. star_step_solver. Qed.

(** Catching exceptions: the handler binds the class, reason and details *)
Goal ⟨[], °ETry plus_5_tuple 1 (˝VVar 0) 3
                 (°ETuple [˝VVar 0; ˝VVar 1; ˝VVar 2])⟩
   -->* RValSeq [VTuple [VLit "error"; VLit "badarith"; VTuple [VLit "+"; VLit 5%Z; VTuple []]]].
Proof. star_step_solver. Qed.

(** Without an exception, the `of` branch is evaluated *)
Goal ⟨[], °ETry (˝VLit 1%Z) 1 (˝VVar 0) 3 (˝VLit "caught")⟩ -->* RValSeq [VLit 1%Z].
Proof. star_step_solver. Qed.

(** Re-raising a caught exception with the `raise` primop *)
Goal ⟨[], °ETry (°ETry plus_5_tuple 1 (˝VVar 0) 3 (°EPrimOp "raise" [˝VVar 2; ˝VVar 1]))
                 1 (˝VVar 0) 3 (˝VVar 1)⟩
   -->* RValSeq [VLit "badarith"].
Proof. star_step_solver. Qed.

(** Errors of application and calls *)
Goal ⟨[], °EApp (˝VLit 5%Z) []⟩ -->* RExc (badfun (VLit 5%Z)).
Proof. star_step_solver. Qed.

Goal ⟨[], °EApp (°EFun 1 (˝VVar 0)) []⟩ -->* RExc (badarity (VClos [] 0 1 (˝VVar 0)) VNil).
Proof. star_step_solver. Qed.

Goal ⟨[], °ECall (˝VLit 1%Z) (˝VLit "foo") []⟩
   -->* RExc (badarg (VTuple [VLit "apply"; VLit 1%Z; VLit "foo"; VNil])).
Proof. star_step_solver. Qed.
