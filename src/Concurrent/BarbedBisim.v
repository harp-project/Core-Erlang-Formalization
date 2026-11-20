(**
  This file defines an even weaker variant of barbed bisimulation. We refer to
  this concept as bisimulation in this and every other file which is followed
  by this file in the compilation order.

  The file contains:
  - the definition of (barbed) bisimulation, and the facts that it is an
    equivalence relation which is coarser than weak bisimulation;
  - barbed expansion, and its properties;
  - bisimulation up to expansion, and its soundness
    (`barbedBisimUpTo_barbedBisim`);
  - the characterisation of bisimilarity as the largest bisimulation
    (`is_barbed_bisim_alt`);
  - the preservation of the barbs by reductions that do not send signals to
    observed PIDs.
*)

From CoreErlang Require Export Concurrent.WeakBisim.

Import ListNotations.

(** * Barbed bisimulation *)

(** `A ~ᵇ B observing O`: the nodes `A` and `B` are (barbed) bisimilar with
    the observed PIDs `O`. Every step of one of the nodes has to be matched
    by a reduction sequence (of any actions) of the other node. The signals
    in transit to an observed PID (the barbs) in one node have to be equal
    (`Signal_eq`) to the signals in transit to the same PID in a node
    reachable from the other node; the sources of these signals can differ.
    The barb conditions could be adjusted based on the equivalence we are
    interested in. *)
CoInductive barbedBisim (O : gset PID) : Node -> Node -> Prop :=
| is_bisim (A B : Node) :
  (forall A' a ι,
      A -[a | ι]ₙ-> A' with O ->
        exists B' l,
          B -[l]ₙ->* B' with O /\ barbedBisim O A' B') ->
  (forall source dest,
      dest ∈ O ->
      exists source' l B',
      B -[l]ₙ->* B' with O /\
      option_list_biforall Signal_eq (A.1 !! (source, dest)) (B'.1 !! (source', dest))) ->
  (forall B' a ι,
      B -[a | ι]ₙ-> B' with O ->
        exists A' l,
          A -[l]ₙ->* A' with O /\ barbedBisim O A' B') ->
  (forall source dest,
      dest ∈ O ->
      exists source' l A',
      A -[l]ₙ->* A' with O /\
      option_list_biforall Signal_eq (B.1 !! (source, dest)) (A'.1 !! (source', dest))) ->
  barbedBisim O A B
.

Notation "A ~ᵇ B 'observing' O" := (barbedBisim O A B) (at level 70).

(** Weakly bisimilar nodes are bisimilar. *)
Theorem weak_is_barbed :
  forall O A B, A ~ʷ B observing O -> A ~ᵇ B observing O.
Proof.
  cofix IH. intros. inv H; constructor; auto.
  * intros. apply H0 in H. destruct H as [B' [B'' [B''' [l1 [l2 ?]]]]].
    destruct_hyps. exists B''', (l1 ++ (a, ι) :: l2). split.
    - eapply closureNodeSem_trans. exact H4.
      econstructor. exact H5.
      exact H6.
    - by apply IH.
  * intros. apply (H1 source) in H.
    exists source, [], B. split. constructor. assumption.
  * intros. apply H2 in H. destruct H as [A' [A'' [A''' [l1 [l2 ?]]]]].
    destruct_hyps. exists A''', (l1 ++ (a, ι) :: l2). split.
    - eapply closureNodeSem_trans. exact H4.
      econstructor. exact H5.
      exact H6.
    - by apply IH.
  * intros. exists source, [], A. split_and!; try by constructor.
    specialize (H1 source _ H). clear-H1.
    destruct (A.1 !! _) eqn:P; destruct (B.1 !! _) eqn:P2; simpl in *.
    2-3: congruence. 2: trivial.
    clear -H1.
    apply biforall_length in H1 as HL.
    apply forall_biforall with (d1 := SLink) (d2 := SLink). by auto.
    intros.
    apply biforall_forall with (d1 := SLink) (d2 := SLink) (i := i) in H1.
    2: by lia.
    by apply Signal_eq_sym.
Qed.

(** Bisimilarity is reflexive. *)
Theorem barbedBisim_refl :
  forall O A, A ~ᵇ A observing O.
Proof.
  intros.
  apply weak_is_barbed, strong_is_weak, equality_is_strong_bisim.
Qed.

(** Bisimilarity is symmetric. *)
Corollary barbedBisim_sym :
  forall O A B, A ~ᵇ B observing O -> B ~ᵇ A observing O.
Proof.
  cofix IH; intros; constructor; inv H; auto.
  * intros. apply H2 in H. destruct_hyps.
    exists x, x0. split; try assumption.
    by apply IH.
  * intros. apply H0 in H. destruct_hyps.
    exists x, x0. split; try assumption.
    by apply IH.
Qed.

(** Reduction sequences of a node can be matched by reduction sequences of a
    bisimilar node. *)
Lemma barbedBisim_many :
  forall O A A' l, A -[l]ₙ->* A' with O ->
    forall B, A ~ᵇ B observing O ->
      exists B' l',
        B -[ l' ]ₙ->* B' with O /\ A' ~ᵇ B' observing O.
Proof.
  intros ???? H. induction H; intros.
  * rename n into A. exists B, []. split. constructor.
    by simpl.
  * rename n into A. rename n'' into A''.
    inv H1.
    apply H2 in H as H'. destruct H' as [B' [l' H']]. destruct_hyps.
    clear H2. apply IHclosureNodeSem in H6. destruct H6 as [B'' [l'' P]].
    destruct_hyps.
    exists B'', (l' ++ l''). split.
    eapply closureNodeSem_trans; eassumption. by simpl.
Qed.

(** The symmetric version of `barbedBisim_many`. NOTE: this theorem is needed
    separately to prove transitivity, because using symmetry in the proof for
    transitivity breaks the guardedness conditions! *)
Corollary barbedBisim_many_sym :
  forall O A A' l, A -[l]ₙ->* A' with O ->
    forall B, B ~ᵇ A observing O ->
      exists B' l',
        B -[ l' ]ₙ->* B' with O /\ B' ~ᵇ A' observing O.
Proof.
  intros.
  apply barbedBisim_sym in H0.
  pose proof (barbedBisim_many _ _ _ _ H _ H0).
  destruct_hyps. exists x, x0. (split; auto).
  now apply barbedBisim_sym.
Qed.

(** Bisimilarity is transitive. *)
Theorem barbedBisim_trans :
  forall O A B C,
    A ~ᵇ B observing O -> B ~ᵇ C observing O -> A ~ᵇ C observing O.
Proof.
  cofix IH. intros.
  pose proof (H) as AB. inv H. pose proof (H0) as BC. inv H0. constructor; auto.
  * clear H7. intros. apply H1 in H0 as H0'.
    destruct H0' as [B' [l [H0']]]. destruct_hyps.
    pose proof (barbedBisim_many _ _ _ _ H0' _ BC) as P.
    destruct P as [C' [l']]. destruct_hyps.
    specialize (IH _ _ _ _ H7 H9). exists C', l'.
    split. all: assumption.
  * intros.
    epose proof (H2 source dest H0) as P. destruct P as [sourceB [Bs [B' ?]]].
    destruct_hyps.
    pose proof (barbedBisim_many _ _ _ _ H8 _ BC) as [C' [Cs ?]]. destruct_hyps.
    pose proof H11 as B'C'. inv H11.
    specialize (H13 sourceB _ H0).
    destruct H13 as [sourceC [Cs' [C'' [sigsC ?]]]].
    destruct_hyps.
    exists sourceC, (Cs ++ Cs'), C''.
    split.
    - eapply closureNodeSem_trans; eassumption.
    - clear -H9 H11. (* transitivity is needed here! *)
      eapply option_biforall_trans; eauto.
      intros. eapply Signal_eq_trans; eassumption.
  * intros. rename B' into C'. apply H6 in H0 as H0'.
    destruct H0' as [B' [l [H0']]]. destruct_hyps.
    pose proof (barbedBisim_many_sym _ _ _ _ H0' _ AB) as P.
    destruct P as [A' [l']]. destruct_hyps.
    epose proof (IH _ _ _ _ H10 H8) as IH2. clear IH.
    exists A', l'.
    split. assumption. assumption.
  * intros.
    epose proof (H7 source dest H0) as P. destruct P as [sourceB [Bs [B' ?]]].
    destruct_hyps.
    assert (B ~ᵇ A observing O) as BA by now apply barbedBisim_sym.
    pose proof (barbedBisim_many _ _ _ _ H8 _ BA) as [A' [As ?]]. destruct_hyps.
    pose proof H11 as B'A'. inv H11.
    specialize (H13 sourceB _ H0).
    destruct H13 as [sourceA [As' [A'' [sigsA ?]]]].
    destruct_hyps.
    exists sourceA, (As ++ As'), A''.
    split.
    - eapply closureNodeSem_trans; eassumption.
    - clear -H11 H9. (* transitivity is needed here! *)
      eapply option_biforall_trans; eauto.
      intros. eapply Signal_eq_trans; eassumption.
Qed.

(** * Barbed expansion *)

(** `A ⪰ B observing O` (Definition 7 of the paper): `A` expands `B`, i.e.,
    `B` is a bisimilar, but more efficient version of `A` (`B ⪯ A` is the
    converse notation). Every step of `A` has to be matched by
    at most one step of `B`, and every step of `B` by at least one step of
    `A`. The barbs of `A` have to be present in `B` directly (with possibly
    different sources), while the barbs of `B` have to be reachable from
    `A`. *)
CoInductive barbedExpansion (O : gset PID) : Node -> Node -> Prop :=
| is_expansion A B:
  (forall A' a ι, A -[a | ι]ₙ-> A' with O -> exists B' l,
    length l <= 1 /\ B -[l]ₙ->* B' with O /\ barbedExpansion O A' B')
  ->
  (forall source dest,
      dest ∈ O ->
      exists source',
      option_list_biforall Signal_eq (A.1 !! (source, dest)) (B.1 !! (source', dest))) ->
  (forall B' a ι, B -[a | ι]ₙ-> B' with O -> exists A' l,
    length l >= 1 /\ A -[l]ₙ->* A' with O /\ barbedExpansion O A' B')
  ->
  (forall source dest,
    dest ∈ O ->
    exists source' l A',
    A -[l]ₙ->* A' with O /\
    option_list_biforall Signal_eq (B.1 !! (source, dest)) (A'.1 !! (source', dest)))
->
  barbedExpansion O A B.
Notation "A ⪰ B 'observing' O" := (barbedExpansion O A B) (at level 70).
Notation "A ⪯ B 'observing' O" := (barbedExpansion O B A) (at level 70).

(** Expansion implies bisimilarity. *)
Theorem barbedExpansion_implies_bisim :
  forall O A B, A ⪰ B observing O -> A ~ᵇ B observing O.
Proof.
  cofix IH. intros. inv H. constructor; auto.
  * intros. apply H0 in H. destruct H as [B' [l H]]. destruct_hyps.
    apply IH in H5. exists B', l. now auto.
  * intros. apply (H1 source dest) in H. destruct_hyps.
    exists x, [], B. split; auto. now constructor.
  * intros. apply H2 in H. destruct H as [A' [l H]]. destruct_hyps.
    apply IH in H5. exists A', l. now auto.
Qed.

(** * Bisimulation up to expansion *)

(** `A ~⪯~ B observing O` (Definition 8 of "Playing with bisimulation in Erlang"):
    `A` and `B` are bisimilar up to expansion: the derivatives of matched steps
    only have to be related up to expansion on both sides. The derivative of the
    stepping node expands the node which continues in the relation (`A' ⪰ A''`),
    while on the responding side, the node which continues in the relation
    expands the reached node (`B'' ⪰ B'`). Soundness is proved in
    `barbedBisimUpTo_barbedBisim`. *)
CoInductive barbedBisimUpTo (O : gset PID) : Node -> Node -> Prop :=
| is_bisim_up_to (A B : Node) :
  (forall A' a ι,
      A -[a | ι]ₙ-> A' with O ->
        exists B' A'' B'' l,
          B -[l]ₙ->* B' with O /\
          A' ⪰ A'' observing O /\ B'' ⪰ B' observing O /\ barbedBisimUpTo O A'' B'') ->
  (forall source dest,
      dest ∈ O ->
      exists source' l B',
      B -[l]ₙ->* B' with O /\
      option_list_biforall Signal_eq (A.1 !! (source, dest)) (B'.1 !! (source', dest))) ->
  (forall B' a ι,
      B -[a | ι]ₙ-> B' with O ->
        exists A' B'' A'' l,
          A -[l]ₙ->* A' with O /\
          A'' ⪰ A' observing O /\ B' ⪰ B'' observing O /\ barbedBisimUpTo O A'' B'') ->
  (forall source dest,
      dest ∈ O ->
      exists source' l A',
      A -[l]ₙ->* A' with O /\
      option_list_biforall Signal_eq (B.1 !! (source, dest)) (A'.1 !! (source', dest)))
->
  barbedBisimUpTo O A B.
Notation "A ~⪯~ B 'observing' O" := (barbedBisimUpTo O A B) (at level 70).

(** If `A ~ᵇ A'`, `B ~ᵇ B'` and `A' ~ᵇ B'`, then `A ~ᵇ B`. *)
Corollary diamond_trans :
  forall O A B A' B',
    A ~ᵇ A' observing O -> B ~ᵇ B' observing O -> A' ~ᵇ B' observing O ->
    A ~ᵇ B observing O.
Proof.
  intros ????? AA' BB' A'B'.
  eapply barbedBisim_trans. exact AA'.
  eapply barbedBisim_trans. exact A'B'.
  now apply barbedBisim_sym.
Qed.

(** Expansion is reflexive. *)
Lemma barbedExpansion_refl :
  forall O A, A ⪰ A observing O.
Proof.
  cofix H. intros.
  constructor.
  * intros. exists A', [(a, ι)]. split. 2: split.
    - slia.
    - econstructor. eassumption. constructor.
    - apply H.
  * intros. exists source.
    apply option_biforall_refl. intros. apply Signal_eq_refl.
  * intros. exists B', [(a, ι)]. split. 2: split.
    - slia.
    - econstructor. eassumption. constructor.
    - apply H.
  * intros. exists source, [], A.
    split. constructor.
    apply option_biforall_refl. intros. apply Signal_eq_refl.
Qed.

(** Expansion implies bisimilarity up to expansion. *)
Lemma barbedExpansion_is_expansion_up_to :
  forall O A B,
    A ⪰ B observing O -> A ~⪯~ B observing O.
Proof.
  cofix IH.
  intros. inv H. constructor; auto.
  * intros. apply H0 in H as H'. destruct H' as [B' [l H']]. destruct_hyps.
    exists B', A', B', l. do 2 (split; auto). 2: split.
    1-2: apply barbedExpansion_refl.
    now apply IH.
  * intros. apply (H1 source dest) in H. destruct H as [sourceB H].
    exists sourceB, [], B. split. constructor. assumption.
  * intros. apply H2 in H as H'. destruct H' as [A' [l H']]. destruct_hyps.
    exists A', B', A', l. do 2 (split; auto).
    2: split.
    1-2: apply barbedExpansion_refl.
    now apply IH.
Qed.

(** Reduction sequences of `A` can be matched by at most as long reduction
    sequences of a node `B` expanded by `A`. *)
Lemma barbedExpansion_many :
  forall O A A' l, A -[l]ₙ->* A' with O ->
    forall B, A ⪰ B observing O ->
      exists B' l',
        B -[ l' ]ₙ->* B' with O /\ A' ⪰ B' observing O /\ length l' <= length l.
Proof.
  intros O A A' l. revert A A'. induction l; intros; inv H.
  * exists B, []. split. 2: split.
    1,3: constructor.
    assumption.
  * rename A' into A''. rename n' into A'.
    inv H0. apply H in H4 as H'. destruct H' as [B' [l' H']]. destruct_hyps.
    eapply IHl in H7. 2: eassumption.
    destruct H7 as [B'' [l'' P]].
    destruct_hyps.
    exists B'', (l' ++ l''). split. 2: split.
    - eapply closureNodeSem_trans; eassumption.
    - assumption.
    - rewrite length_app. slia.
Qed.

(** Reduction sequences of `B` can be matched by at least as long reduction
    sequences of a node `A` expanding `B`. *)
Lemma barbedExpansion_many_sym :
  forall O B B' l', B -[l']ₙ->* B' with O ->
    forall A, A ⪰ B observing O ->
      exists A' l,
        A -[ l ]ₙ->* A' with O /\ A' ⪰ B' observing O /\ length l' <= length l.
Proof.
  intros O A A' l. revert A A'. induction l; intros; inv H.
  * exists A0, []. split. 2: split.
    1,3: constructor.
    assumption.
  * rename A' into A''. rename n' into A'.
    inv H0. apply H2 in H4 as H'. destruct H' as [B' [l' H']]. destruct_hyps.
    eapply IHl in H7. 2: eassumption.
    destruct H7 as [B'' [l'' P]].
    destruct_hyps.
    exists B'', (l' ++ l''). split. 2: split.
    - eapply closureNodeSem_trans; eassumption.
    - assumption.
    - rewrite length_app. slia.
Qed.

(** Expansion is transitive. *)
Lemma barbedExpansion_trans :
  forall O A B C,
    A ⪰ B observing O -> B ⪰ C observing O
    -> A ⪰ C observing O.
Proof.
  cofix IH. intros.
  constructor; auto.
  * intros. inv H. apply H2 in H1. destruct H1 as [B' [lB H1]].
    destruct_hyps.
    eapply barbedExpansion_many in H1. 2: eassumption.
    destruct H1 as [C' [lC H1]]. destruct_hyps.
    exists C', lC. split. 2: split.
    - lia.
    - assumption.
    - eapply IH; eassumption.
  * intros. inv H. inv H0.
    specialize (H3 source dest H1) as [sourceB ?].
    specialize (H6 sourceB dest H1) as [sourceC ?].
    eexists.
    eapply option_biforall_trans; eauto.
    intros. eapply Signal_eq_trans; eassumption.
  * intros. rename B' into C'.
    inv H0. apply H4 in H1. destruct H1 as [B' [lB H1]].
    destruct_hyps.
    eapply barbedExpansion_many_sym in H1. 2: eassumption.
    destruct H1 as [A' [lA H1]]. destruct_hyps.
    exists A', lA. split. 2: split.
    - lia.
    - assumption.
    - eapply IH; eassumption.
  * intros. pose proof H as AB. pose proof H0 as BC.
    inv H. inv H0.
    specialize (H8 source dest H1) as [sourceB [lB [B' ?]]]. destruct_hyps.
    eapply barbedExpansion_many_sym in H0. 2: exact AB.
    destruct H0 as [A' [lA H0]]. destruct_hyps.
    inv H9.
    specialize (H14 sourceB dest H1) as [sourceA [lA' [A'' H23]]]. destruct_hyps.
    do 3 eexists. split.
    - eapply closureNodeSem_trans; eassumption.
    - eapply option_biforall_trans; eauto.
      intros. eapply Signal_eq_trans; eassumption.
Qed.

(** * Bisimulations as relations *)

(** `R` is a (barbed) bisimulation: related nodes satisfy the conditions of
    `barbedBisim`, with `R` in place of `barbedBisim`. *)
Definition is_barbed_bisim_alt (R : Node -> Node -> Prop) (O : gset PID) :=
forall A B, R A B ->
(forall A' a ι,
      A -[a | ι]ₙ-> A' with O ->
        exists B' l,
          B -[l]ₙ->* B' with O /\ R A' B') /\
  (forall source dest,
      dest ∈ O ->
      exists source' l B',
      B -[l]ₙ->* B' with O /\
      option_list_biforall Signal_eq (A.1 !! (source, dest)) (B'.1 !! (source', dest))) /\
  (forall B' a ι,
      B -[a | ι]ₙ-> B' with O ->
        exists A' l,
          A -[l]ₙ->* A' with O /\ R A' B') /\
  (forall source dest,
      dest ∈ O ->
      exists source' l A',
      A -[l]ₙ->* A' with O /\
      option_list_biforall Signal_eq (B.1 !! (source, dest)) (A'.1 !! (source', dest))).

(** Nodes related by a bisimulation are bisimilar (the coinduction principle
    of `barbedBisim`). *)
Theorem barbed_alt_barbed_1 :
  forall R O, is_barbed_bisim_alt R O ->
    forall A B, R A B ->
      A ~ᵇ B observing O.
Proof.
  cofix IH. intros.
  apply H in H0. destruct_hyps.
  constructor.
  * intros. apply H0 in H4. destruct_hyps.
    exists x, x0. split. assumption. by eapply IH.
  * intros. by apply H1.
  * intros. apply H2 in H4. destruct_hyps.
    exists x, x0. split. assumption. by eapply IH.
  * intros. by apply H3.
Qed.

(** Bisimilarity is a bisimulation. *)
Theorem barbed_alt_barbed_2 :
  forall O, is_barbed_bisim_alt (barbedBisim O) O.
Proof.
  intros. intros A B IH. by inv IH.
Qed.

(** Bisimilar nodes are related by a bisimulation. *)
Corollary barbed_alt_barbed_corr :
  forall A B O, A ~ᵇ B observing O ->
    exists R, is_barbed_bisim_alt R O /\ R A B.
Proof.
  intros. exists (barbedBisim O). split; auto.
  apply barbed_alt_barbed_2.
Qed.

(** * Soundness of bisimulation up to expansion *)

(** Bisimilarity up to expansion is symmetric. *)
Lemma barbedBisimUpTo_sym :
  forall O A B, A ~⪯~ B observing O -> B ~⪯~ A observing O.
Proof.
  cofix IH. intros O A B H.
  inversion H as [? ? H1 H2 H3 H4]; subst.
  constructor.
  * intros B' a ι HB.
    destruct (H3 _ _ _ HB) as [A' [B'' [A'' [l [HA [HA''A' [HB'B'' HU]]]]]]].
    exists A', B'', A'', l. split_and!; try assumption. by apply IH.
  * exact H4.
  * intros A' a ι HA.
    destruct (H1 _ _ _ HA) as [B' [A'' [B'' [l [HB [HA'A'' [HB''B' HU]]]]]]].
    exists B', A'', B'', l. split_and!; try assumption. by apply IH.
  * exact H2.
Qed.

(** The auxiliary relation of the soundness proof: `A` expands `N`, `N` is
    bisimilar to `M` up to expansion, and `M` expands `B`. *)
Local Definition upToExpRel (O : gset PID) (A B : Node) : Prop :=
  exists N M, A ⪰ N observing O /\ N ~⪯~ M observing O /\ M ⪰ B observing O.

(** Reduction sequences of the left node of `upToExpRel` can be matched by
    reduction sequences of the right node (by strong induction on the length
    of the sequence; the expansions ensure that the sequence to be matched
    does not become longer). Since `~⪯~` is symmetric, this lemma also
    handles the converse direction (see `upToExp_bisim`). *)
Local Lemma upToExpRel_many :
  forall O (* n *) l, (* length l <= n -> *)
    forall A A', A -[l]ₙ->* A' with O ->
    forall B, upToExpRel O A B ->
      exists B' l', B -[l']ₙ->* B' with O /\ upToExpRel O A' B'.
Proof.
  intros O. induction l; intros A A' HA B [N [M [HAN [HNM HMB]]]].
  * inv HA. exists B, []. split. constructor. by exists N, M.
  * inversion HA as [|? A1 ? l0 a' ι HAstep HArest]; subst.
    inversion HAN as [? ? HAN1 HAN2 HAN3 HAN4]; subst.
    destruct (HAN1 _ _ _ HAstep) as [N1 [ln [Hln [HN HA1N1]]]].
    destruct ln as [|[b κ] [|]]; [| |simpl in Hln; lia].
    - inv HN. eapply IHl. exact HArest.
      by exists N1, M.
    - inversion HN as [|? Nm ? ? ? ? HNstep HNrest]; subst. inv HNrest.
      inversion HNM as [? ? HNM1 HNM2 HNM3 HNM4]; subst.
      destruct (HNM1 _ _ _ HNstep) as [M1 [N2 [M2 [lm [HM [HN1N2 [HM2M1 HN2M2]]]]]]].
      destruct (barbedExpansion_many _ _ _ _ HM _ HMB) as [B1 [lb [HB [HM1B1 _]]]].
      destruct (IHl _ _ HArest B1) as [B' [lb' [HB' HU]]].
      {
        exists N2, M2. split; [|split].
        - eapply barbedExpansion_trans; eassumption.
        - assumption.
        - eapply barbedExpansion_trans; eassumption.
      }
      exists B', (lb ++ lb'). split. 2: assumption.
      eapply closureNodeSem_trans; eassumption.
Qed.

(** The barbs of the left node of `upToExpRel` are reachable from the right
    node. *)
Local Lemma upToExpRel_barbs :
  forall O A B, upToExpRel O A B ->
    forall source dest, dest ∈ O ->
      exists source' l B', B -[l]ₙ->* B' with O /\
        option_list_biforall Signal_eq (A.1 !! (source, dest)) (B'.1 !! (source', dest)).
Proof.
  intros O A B [N [M [HAN [HNM HMB]]]] source dest Hdest.
  inversion HAN as [? ? _ HAN2 _ _]; subst.
  destruct (HAN2 source dest Hdest) as [s1 HANb].
  inversion HNM as [? ? _ HNM2 _ _]; subst.
  destruct (HNM2 s1 dest Hdest) as [s2 [lm [M1 [HM HNMb]]]].
  destruct (barbedExpansion_many _ _ _ _ HM _ HMB) as [B1 [lb [HB [HM1B1 _]]]].
  inversion HM1B1 as [? ? _ HM1B12 _ _]; subst.
  destruct (HM1B12 s2 dest Hdest) as [s3 HMBb].
  exists s3, lb, B1. split. 1: assumption.
  eapply option_biforall_trans. 1: intros; eapply Signal_eq_trans; eassumption.
  1: exact HANb.
  eapply option_biforall_trans. 1: intros; eapply Signal_eq_trans; eassumption.
  1: exact HNMb.
  exact HMBb.
Qed.

(** Bisimilarity composed with bisimilarity up to expansion on both sides is
    a bisimulation. The steps of both sides are matched with
    `upToExpRel_many`, using the symmetry of `~⪯~` for the right side. *)
Local Lemma upToExp_bisim :
  forall O, is_barbed_bisim_alt
    (fun A B => exists X Y, A ~ᵇ X observing O /\ X ~⪯~ Y observing O /\
                            Y ~ᵇ B observing O) O.
Proof.
  intros O A B [X [Y [HAX [HXY HYB]]]].
  assert (upToExpRel O X Y) as HU.
  { exists X, Y. split_and!; auto using barbedExpansion_refl. }
  assert (upToExpRel O Y X) as HU'.
  { exists Y, X. split_and!; auto using barbedExpansion_refl, barbedBisimUpTo_sym. }
  clear HXY.
  inversion HAX as [? ? HAX1 HAX2 HAX3 HAX4]; subst.
  inversion HYB as [? ? HYB1 HYB2 HYB3 HYB4]; subst.
  split; [|split; [|split]].
  * intros A' a ι HA.
    destruct (HAX1 _ _ _ HA) as [X' [lx [HX HA'X']]].
    destruct (upToExpRel_many O lx _ _ HX _ HU)
      as [Y' [ly [HY [N [M [HX'N [HNM HMY']]]]]]].
    destruct (barbedBisim_many _ _ _ _ HY _ HYB) as [B' [lb [HB HY'B']]].
    exists B', lb. split. 1: assumption.
    exists N, M. split; [|split].
    - eapply barbedBisim_trans. 1: exact HA'X'.
      by apply barbedExpansion_implies_bisim.
    - assumption.
    - eapply barbedBisim_trans. 2: exact HY'B'.
      by apply barbedExpansion_implies_bisim.
  * intros source dest Hdest.
    destruct (HAX2 source dest Hdest) as [s1 [lx [X1 [HX HAXb]]]].
    destruct (upToExpRel_many O lx _ _ HX _ HU)
      as [Y1 [ly [HY HU1]]].
    destruct (upToExpRel_barbs _ _ _ HU1 s1 dest Hdest)
      as [s2 [ly' [Y2 [HY' HXYb]]]].
    destruct (barbedBisim_many _ _ _ _ (closureNodeSem_trans _ _ _ _ HY _ _ HY') _ HYB)
      as [B2 [lb [HB HY2B2]]].
    inversion HY2B2 as [? ? _ HY2B22 _ _]; subst.
    destruct (HY2B22 s2 dest Hdest) as [s3 [lb' [B3 [HB' HYBb]]]].
    exists s3, (lb ++ lb'), B3. split.
    - eapply closureNodeSem_trans; eassumption.
    - eapply option_biforall_trans. 1: intros; eapply Signal_eq_trans; eassumption.
      1: exact HAXb.
      eapply option_biforall_trans. 1: intros; eapply Signal_eq_trans; eassumption.
      1: exact HXYb.
      exact HYBb.
  * intros B' a ι HB.
    destruct (HYB3 _ _ _ HB) as [Y' [ly [HY HY'B']]].
    destruct (upToExpRel_many O ly _ _ HY _ HU')
      as [X' [lx [HX [N [M [HY'N [HNM HMX']]]]]]].
    destruct (barbedBisim_many_sym _ _ _ _ HX _ HAX) as [A' [la [HA HA'X']]].
    exists A', la. split. 1: assumption.
    exists M, N. split; [|split].
    - eapply barbedBisim_trans. 1: exact HA'X'.
      by apply barbedBisim_sym, barbedExpansion_implies_bisim.
    - by apply barbedBisimUpTo_sym.
    - eapply barbedBisim_trans. 2: exact HY'B'.
      by apply barbedBisim_sym, barbedExpansion_implies_bisim.
  * intros source dest Hdest.
    destruct (HYB4 source dest Hdest) as [s1 [ly [Y1 [HY HBYb]]]].
    destruct (upToExpRel_many O ly _ _ HY _ HU')
      as [X1 [lx [HX HU1]]].
    destruct (upToExpRel_barbs _ _ _ HU1 s1 dest Hdest)
      as [s2 [lx' [X2 [HX' HYXb]]]].
    destruct (barbedBisim_many_sym _ _ _ _ (closureNodeSem_trans _ _ _ _ HX _ _ HX') _ HAX)
      as [A2 [la [HA HA2X2]]].
    inversion HA2X2 as [? ? _ _ _ HA2X24]; subst.
    destruct (HA2X24 s2 dest Hdest) as [s3 [la' [A3 [HA' HXAb]]]].
    exists s3, (la ++ la'), A3. split.
    - eapply closureNodeSem_trans; eassumption.
    - eapply option_biforall_trans. 1: intros; eapply Signal_eq_trans; eassumption.
      1: exact HBYb.
      eapply option_biforall_trans. 1: intros; eapply Signal_eq_trans; eassumption.
      1: exact HYXb.
      exact HXAb.
Qed.

(** Soundness of bisimulation up to expansion: nodes bisimilar up to
    expansion are bisimilar. *)
Theorem barbedBisimUpTo_barbedBisim :
  forall O A B, A ~⪯~ B observing O -> A ~ᵇ B observing O.
Proof.
  intros O A B H.
  eapply barbed_alt_barbed_1. 1: apply upToExp_bisim.
  exists A, B. split_and!; auto using barbedBisim_refl.
Qed.

(** * Barbs under reduction *)

(** Reductions that do not send signals to observed PIDs (which are not
    associated with processes) do not change the signals in transit to
    observed PIDs. *)
Lemma reductions_preserve_signals_targeting_O :
  forall O (n n' : Node) l, n -[l]ₙ->* n' with O ->
    O ## dom n.2 ->
    (forall ι, ι ∈ (PIDsOf sendPIDOf l) -> ι ∉ O) ->
    forall source : PID,
      forall dest, dest ∈ O ->
      option_list_biforall Signal_eq (n.1 !! (source, dest)) (n'.1 !! (source, dest)).
Proof.
  intros O n n' l H. induction H; intros Hdom H1 ? ? Hin.
  1: apply option_biforall_refl; intros; apply Signal_eq_refl.
  eapply option_biforall_trans.
    1: by apply Signal_eq_trans.
    2: apply IHclosureNodeSem. 3-4: set_solver.
    2: eapply reductions_preserve_O_dom; [|eassumption].
    2: eapply n_trans; [ exact H | apply n_refl ].
  inversion H; subst; simpl in *.
  3-4: apply option_biforall_refl; intros; apply Signal_eq_refl.
  * unfold etherAdd. destruct (decide ((ι, ι') = (source, dest))).
    - inv e. case_match; exfalso; apply H1 in Hin; try assumption; set_solver.
    - break_match_goal; setoid_rewrite lookup_insert_ne; try assumption; auto.
      all: apply option_biforall_refl; intros; apply Signal_eq_refl.
  * unfold etherPop in H2. destruct (decide ((ι1, ι) = (source, dest))).
    - inv e.
      case_match. 2: congruence. destruct l0; try congruence. inv H2.
      exfalso. clear -Hin Hdom. set_solver.
    - case_match; try congruence. destruct l0; try congruence. inv H2.
      setoid_rewrite lookup_insert_ne; auto.
      apply option_biforall_refl; intros; apply Signal_eq_refl.
Qed.
