(**
  This file defines weak barbed bisimulation, and shows that strong barbed
  bisimulations are weak too.
*)

From CoreErlang Require Export Concurrent.StrongBisim.

Import ListNotations.

(** Silent actions: only `τ`. The process-local `ε` actions are not
    considered silent, since they are not confluent with signal arrival (see
    `Action` in `ProcessSemantics.v`). *)
Definition isSilent (a : Action) : Prop :=
match a with
 | τ => True
 | _ => False
end.

(** `A ~ʷ B observing O`: the nodes `A` and `B` are weakly bisimilar with the
    observed PIDs `O`. Every step of one of the nodes has to be matched by
    the same step of the other node, surrounded by silent steps, and the
    signals in transit to the observed PIDs (the barbs) have to be equal
    (`Signal_eq`) in the two nodes. Silent actions do not modify the ether,
    thus the barb condition does not need silent steps; it could be adjusted
    based on the equivalence we are interested in.

    NOTE: `τ` steps also have to be matched by at least one `τ` step (instead
    of possibly no steps), so this relation is finer than the standard (Milner
    style) weak bisimilarity. *)
CoInductive weakBisim (O : gset PID) : Node -> Node -> Prop :=
| is_weak_bisim (A B : Node) :
  (forall A' a ι,
      A -[a | ι]ₙ-> A' with O ->
        exists B' B'' B''' l₁ l₂,
             Forall (isSilent ∘ fst) l₁
          /\ Forall (isSilent ∘ fst) l₂
          /\ B -[l₁]ₙ->* B' with O
          /\ B' -[a | ι]ₙ-> B'' with O
          /\ B'' -[l₂]ₙ->* B''' with O
          /\ weakBisim O A' B''') ->
  (forall source dest,
      dest ∈ O ->
      option_list_biforall Signal_eq (A.1 !! (source, dest)) (B.1 !! (source, dest))) ->
  (forall B' a ι,
      B -[a | ι]ₙ-> B' with O ->
        exists A' A'' A''' l₁ l₂,
             Forall (isSilent ∘ fst) l₁
          /\ Forall (isSilent ∘ fst) l₂
          /\ A -[l₁]ₙ->* A' with O
          /\ A' -[a | ι]ₙ-> A'' with O
          /\ A'' -[l₂]ₙ->* A''' with O
          /\ weakBisim O A''' B') ->
  weakBisim O A B
.

Notation "A ~ʷ B 'observing' O" := (weakBisim O A B) (at level 70).

(** Strongly bisimilar nodes are weakly bisimilar. *)
Theorem strong_is_weak :
  forall O A B, A ~ˢ B observing O -> A ~ʷ B observing O.
Proof.
  cofix IH. intros.
  inv H; constructor; auto.
  * intros. apply H0 in H. destruct H as [B' H]. destruct_hyps.
    exists B, B', B', [], []. split_and!; try by constructor.
    exact H. by apply IH.
  * intros. apply H2 in H. destruct H as [A' H]. destruct_hyps.
    exists A, A', A', [], []. split_and!; try by constructor.
    exact H. by apply IH.
Qed.
