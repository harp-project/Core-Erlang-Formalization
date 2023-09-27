From CoreErlang Require Export Concurrent.NodeSemantics.
From CoreErlang Require Export CoList.

(** Refexive, transitive closure, with action logs: *)
Reserved Notation "n -[ l ]ₙ->* n'" (at level 50).
CoInductive closureNodeSem : Node -> Trace (Action * PID) -> Node -> Prop :=
| n_refl n (* n'  *): (* Permutation n n' -> *) n -[ []ₜ ]ₙ->* n (* ' *)
| n_trans n n' n'' l a ι:
  n -[a|ι]ₙ-> n' -> n' -[l]ₙ->* n''
->
  n -[(a,ι)::ₜ l]ₙ->* n''
where "n -[ l ]ₙ->* n'" := (closureNodeSem n l n').

Theorem closureNodeSem_trans :
  forall n n' l, n -[l]ₙ->* n' -> forall n'' l', n' -[l']ₙ->* n''
->
  n -[l ++ₜ l']ₙ->* n''.
Proof.
  cofix IHD1; intros n n' l D1; inv D1; intros; simpl.
  * rewrite trace_append_nil. exact H.
  * rewrite trace_append_cons.
    eapply n_trans. exact H.
    eapply (IHD1 _ _ _ H0) in H1. exact H1.
Qed.
