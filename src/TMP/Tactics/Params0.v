Require Import Coq.micromega.Lia.



(**
DOCUMENTATION:
* rfl - reflexivity
* asm - assumption
* dis - discriminate
* con - congruence
* spl - split
* lft - left
* rgt - right
* sbt - subst
* ato - auto
* itu - intuition
* cns - constructor
* ens - econstructor
* sli - simpl; lia
* cli - cbn; nia
* sni - simpl; cia
* cni - cbn; nia
*)






Ltac rfl := reflexivity.
Ltac asm := assumption.
Ltac dis := discriminate.
Ltac con := congruence.
Ltac spl := split.
Ltac lft := left.
Ltac rgt := right.
Ltac sbt := subst.
Ltac ato := auto.
Ltac itu := intuition.



Ltac cns := constructor.
Ltac ens := econstructor.

Ltac sli := simpl; lia.
Ltac cli := cbn; lia.

Ltac sni := simpl; nia.
Ltac cni := cbn; nia.