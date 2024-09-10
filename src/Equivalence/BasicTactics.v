From CoreErlang Require Export Basics.






(* SECTION: Clear *)



Ltac clear_refl :=
  repeat match goal with
  | H : ?x = ?x |- _ => clear H
  end.






(* SECTION: Fold *)



Tactic Notation "refold" constr(d) :=
  unfold d;
  fold d.

Tactic Notation "refold" constr(d) "in" ident(H) :=
  unfold d in H;
  fold d in H.