From CoreErlang.Equivalence.BigStepToFrameStack Require Import EraseNames.
From CoreErlang.BigStep Require Import BigStep.
From CoreErlang.FrameStack Require Import SubstSemantics.



Import ListNotations.



Open Scope string_scope.



Goal erase_names_exp (fun _ => 0) (ELit (BigStep.Syntax.Integer 0)) = ˝VLit 0%Z.
Proof.
  cbn. reflexivity.
Qed.

Goal erase_names_exp (fun _ => 0) (BigStep.Syntax.ELet ["X"; "Y"] (BigStep.Syntax.EValues [ELit (BigStep.Syntax.Integer 0); ELit (BigStep.Syntax.Integer 1)]) (BigStep.Syntax.ETuple [EVar "X"; EVar "Y"])) =
  ELet 2 (EValues [˝VLit 0%Z; ˝VLit 1%Z]) (ETuple [˝VVar 0; ˝VVar 1]).
Proof.
  cbn. reflexivity.
Qed.

Goal erase_names_exp (fun _ => 0) (BigStep.Syntax.ELet ["X"] (BigStep.Syntax.EValues [ELit (BigStep.Syntax.Integer 0)]) (BigStep.Syntax.ETuple [EVar "X"])) =
  ELet 1 (EValues [˝VLit 0%Z]) (ETuple [˝VVar 0]).
Proof.
  cbn. reflexivity.
Qed.

Goal erase_names_exp (fun _ => 0) (BigStep.Syntax.ELet ["X"; "Y"; "Z"] (BigStep.Syntax.EValues [ELit (BigStep.Syntax.Integer 0); ELit (BigStep.Syntax.Integer 1); ELit (BigStep.Syntax.Integer 2)]) (BigStep.Syntax.ETuple [EVar "X"; EVar "Y"; EVar "Z"])) =
  ELet 3 (EValues [˝VLit 0%Z; ˝VLit 1%Z; ˝VLit 2%Z]) (ETuple [˝VVar 0; ˝VVar 1; ˝VVar 2]).
Proof.
  cbn. reflexivity.
Qed.

Goal erase_names_exp (fun _ => 0) (BigStep.Syntax.ELet ["X"; "Y"; "Z"] (BigStep.Syntax.EValues [ELit (BigStep.Syntax.Integer 0); ELit (BigStep.Syntax.Integer 1); ELit (BigStep.Syntax.Integer 2)]) (BigStep.Syntax.ETuple [EVar "X"; EVar "Z"; EVar "Y"])) =
  ELet 3 (EValues [˝VLit 0%Z; ˝VLit 1%Z; ˝VLit 2%Z]) (ETuple [˝VVar 0; ˝VVar 2; ˝VVar 1]).
Proof.
  cbn. reflexivity.
Qed.

Goal erase_names_exp (fun _ => 0) (BigStep.Syntax.ELet ["X"; "Y"] (BigStep.Syntax.EValues [ELit (BigStep.Syntax.Integer 0); ELit (BigStep.Syntax.Integer 1)]) (BigStep.Syntax.ETuple [EVar "X"; EVar "Y"; EVar "X"])) =
  ELet 2 (EValues [˝VLit 0%Z; ˝VLit 1%Z]) (ETuple [˝VVar 0; ˝VVar 1; ˝VVar 0]).
Proof.
  cbn. reflexivity.
Qed.

(*
Goal erase_names_exp (fun _ => 1) (BigStep.Syntax.ELet ["Y"] (BigStep.Syntax.EValues [ELit (BigStep.Syntax.Integer 1)]) (BigStep.Syntax.ETuple [EVar "X"; EVar "Y"; EVar "X"])) =
  ELet 1 (EValues [˝VLit 1%Z]) (ETuple [˝VVar 1; ˝VVar 0; ˝VVar 1]).
Proof.
  cbn. reflexivity.
Qed.
*)