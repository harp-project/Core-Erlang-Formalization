Require Import Coq.micromega.Lia.
Require Import stdpp.list.



(** DOCUMENTATION:

* rfl --> reflexivity
* asm --> assumption
* dis --> discriminate
* con --> congruence
* spl --> split
* lft --> left
* rgt --> right
* sbt --> subst
* trv --> trivial
* ato --> auto
* tau --> tauto
* itu --> intuition
* fro --> firstorder
* feq --> f_equal
* ceq --> case_eq
* adm --> admit.
* sli --> simpl; lia
* cli --> cbn; nia
* sni --> simpl; cia
* cni --> cbn; nia

UNSGHANGED:
* lia, nia, cut
*)






Ltac rfl := reflexivity.
Ltac asm := assumption.
Ltac dis := discriminate.
Ltac con := congruence.
Ltac spl := split.
Ltac lft := left.
Ltac rgt := right.
Ltac sbt := subst.
Ltac trv := trivial.
Ltac ato := auto.
Ltac tau := tauto.
Ltac itu := intuition.
Ltac fro := firstorder.
Ltac feq := f_equal.
Ltac ceq := case_eq.
Ltac adm := admit.



Ltac sli := simpl; lia.
Ltac cli := cbn; lia.

Ltac sni := simpl; nia.
Ltac cni := cbn; nia.