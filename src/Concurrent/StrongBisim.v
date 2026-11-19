(**
  This file defines strong barbed bisimulation of nodes, shows its
  reflexivity, and characterises it as the largest relation satisfying the
  bisimulation conditions (`is_strong_bisim_alt`).

  The helper definitions used by all bisimulations are elsewhere: signal
  equality (`Signal_eq`) is in `ProcessSemantics.v`, untaken PIDs and
  `preCompatibleNodes` are in `NodeSemanticsLemmas.v`, and `symClos` is in
  `Utilities.v`.
 *)
From CoreErlang Require Export Concurrent.NodeSemanticsLemmas
                               FrameStack.CTX.

Import ListNotations.

(** Signals related by the logical relation of values (in both directions,
    for all step indices); only used by experimental bisimulations. *)
Definition Srel (a b : Signal) :=
match a, b with
 | SMessage e, SMessage e' => forall n, Vrel n e e' /\ Vrel n e' e
 | SExit r b, SExit r' b' => b = b' /\ forall n, Vrel n r r' /\ Vrel n r' r
 | SLink, SLink => True
 | SUnlink, SUnlink => True
 | _, _ => False
end.

(** * Strong barbed bisimulation *)

(** `A ~ˢ B observing O`: the nodes `A` and `B` are strongly bisimilar with
    the observed PIDs `O`. Every step of one of the nodes has to be matched
    by the same step of the other node, and the signals in transit to the
    observed PIDs (the barbs) have to be equal (`Signal_eq`) in the two
    nodes. The barb condition could be adjusted based on the equivalence we
    are interested in; it does not need to be duplicated, since `Signal_eq`
    is symmetric. *)
CoInductive strongBisim (O : gset PID) : Node -> Node -> Prop :=
| is_strong_bisim (A B : Node) :
  (forall A' a ι,
      A -[a | ι]ₙ-> A' with O ->
        exists B',
          B -[a | ι]ₙ-> B' with O /\ strongBisim O A' B') ->
  (forall source dest,
      dest ∈ O ->
      option_list_biforall Signal_eq (A.1 !! (source, dest)) (B.1 !! (source, dest))) ->
  (forall B' a ι,
      B -[a | ι]ₙ-> B' with O ->
        exists A',
          A -[a | ι]ₙ-> A' with O /\ strongBisim O A' B') ->
  strongBisim O A B
.

Notation "A ~ˢ B 'observing' O" := (strongBisim O A B) (at level 70).

(** Strong bisimilarity is reflexive. *)
Theorem equality_is_strong_bisim :
  forall A O, A ~ˢ A observing O.
Proof.
  cofix IH. intros. constructor.
  * intros. exists A'. split. assumption. apply IH.
  * intros. apply option_biforall_refl. intros. apply Signal_eq_refl.
  * intros. exists B'. split. assumption. apply IH.
Qed.

(** * Bisimulations as relations *)

(** `R` is a strong bisimulation: related nodes satisfy the conditions of
    `strongBisim`, with `R` in place of `strongBisim`. *)
Definition is_strong_bisim_alt (R : Node -> Node -> Prop) (O : gset PID) :=
forall A B, R A B ->
(forall A' a ι,
      A -[a | ι]ₙ-> A' with O ->
        exists B',
          B -[a | ι]ₙ-> B' with O /\ R A' B') /\
  (forall source dest,
      dest ∈ O ->
      option_list_biforall Signal_eq (A.1 !! (source, dest)) (B.1 !! (source, dest))) /\
  (forall B' a ι,
      B -[a | ι]ₙ-> B' with O ->
        exists A',
          A -[a | ι]ₙ-> A' with O /\ R A' B').

(** Nodes related by a strong bisimulation are strongly bisimilar (the
    coinduction principle of `strongBisim`). *)
Theorem strong_alt_strong_1 :
  forall R O, is_strong_bisim_alt R O ->
    forall A B, R A B ->
      A ~ˢ B observing O.
Proof.
  cofix IH. intros.
  apply H in H0. destruct_hyps.
  constructor.
  * intros. apply H0 in H3. destruct_hyps.
    exists x. split. assumption. by eapply IH.
  * intros. by apply H1.
  * intros. apply H2 in H3. destruct_hyps.
    exists x. split. assumption. by eapply IH.
Qed.

(** Strong bisimilarity is a strong bisimulation. *)
Theorem strong_alt_strong_2 :
  forall O, is_strong_bisim_alt (strongBisim O) O.
Proof.
  intros. intros A B IH. by inv IH.
Qed.

(** Strongly bisimilar nodes are related by a strong bisimulation. *)
Corollary strong_alt_strong_corr :
  forall A B O, A ~ˢ B observing O ->
    exists R, is_strong_bisim_alt R O /\ R A B.
Proof.
  intros. exists (strongBisim O). split; auto.
  apply strong_alt_strong_2.
Qed.
