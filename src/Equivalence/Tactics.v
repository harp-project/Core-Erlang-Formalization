From CoreErlang Require Export Basics.

(**
NOTES:  Maybe place this in CoreErlang/Tactics
*)



Ltac clear_refl
  :=
repeat match goal with
| H : ?x = ?x |- _ => clear H
end.

Ltac refold
  x
  :=
unfold x;
fold x.

Ltac invc
  H
  :=
inv H;
clear_refl.