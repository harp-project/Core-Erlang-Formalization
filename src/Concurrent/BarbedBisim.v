(**
  This file defines an even weaker variant of barbed bisimulation. We refer to
  this concept as bisimulation in this and every other file which is followed
  by this file in the compilation order.
*)

From CoreErlang Require Export Concurrent.PIDRenaming
                               Concurrent.WeakBisim.

Import ListNotations.

CoInductive barbedBisim (O : gset PID) : (* nat -> *) Node -> Node -> Prop :=
| is_bisim (A B : Node) :
  (forall A' a ι,
      A -[a | ι]ₙ-> A' with O ->
        exists B' l,
          B -[l]ₙ->* B' with O /\ barbedBisim O (* n *) A' B') ->
  (forall source dest,
      dest ∈ O ->
      exists source' l B',
      B -[l]ₙ->* B' with O /\
      option_list_biforall Signal_eq (A.1 !! (source, dest)) (B'.1 !! (source', dest))
      (* NOTE: this part could be adjusted based on the equivalence we are
               interested in *)) ->
  (forall B' a ι,
      B -[a | ι]ₙ-> B' with O ->
        exists A' l,
          A -[l]ₙ->* A' with O /\ barbedBisim O (* n *) A' B') ->
  (forall source dest,
      dest ∈ O ->
      exists source' l A',
      A -[l]ₙ->* A' with O /\
      option_list_biforall Signal_eq (B.1 !! (source, dest)) (A'.1 !! (source', dest))
      (* NOTE: this part could be adjusted based on the equivalence we are
               interested in *)) ->
  barbedBisim O (* (S n) *) A B
.

Notation "A ~ B 'observing' O" := (barbedBisim O (* n *) A B) (at level 70).

Theorem weak_is_barbed :
  forall O A B, A ~ʷ B observing O -> A ~ B observing O.
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

Theorem barbedBisim_refl :
  forall (* n *) O A, (* ether_wf A.1 -> *) A ~ A observing O.
Proof.
  intros.
  apply weak_is_barbed, strong_is_weak, equality_is_strong_bisim.
Qed.

Corollary barbedBisim_sym :
  forall O A B, A ~ B observing O -> B ~ A observing O.
Proof.
  cofix IH; intros; constructor; inv H; auto.
(*   * by apply symClos_sym. *)
  * intros. apply H2 in H. destruct_hyps.
    exists x, x0. split; try assumption.
    by apply IH.
  * intros. apply H0 in H. destruct_hyps.
    exists x, x0. split; try assumption.
    by apply IH.
Defined.

Lemma barbedBisim_many :
  forall O A A' l, A -[l]ₙ->* A' with O ->
    forall B, A ~ B observing O ->
      exists B' l',
        B -[ l' ]ₙ->* B' with O /\ A' ~ B' observing O.
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
Defined.


(** NOTE: this theorem is needed separately to prove transitivity, because
    using symmetry in the proof for transitivity breaks the guardedness
    conditions! *)
Corollary barbedBisim_many_sym :
  forall O A A' l, A -[l]ₙ->* A' with O ->
    forall B, B ~ A observing O ->
      exists B' l',
        B -[ l' ]ₙ->* B' with O /\ B' ~ A' observing O.
Proof.
  intros.
  apply barbedBisim_sym in H0.
  pose proof (barbedBisim_many _ _ _ _ H _ H0).
  destruct_hyps. exists x, x0. (split; auto).
  now apply barbedBisim_sym.
Defined.


Theorem barbedBisim_trans :
  forall O A B C,
    A ~ B observing O -> B ~ C observing O -> A ~ C observing O.
Proof.
  cofix IH. intros.
  pose proof (H) as AB. inv H. pose proof (H0) as BC. inv H0. constructor; auto.
(*   * clear -H1 H. destruct H1, H. split.
    1-2: eapply preCompatibleNodes_trans; eassumption. *)
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
    (* assert (B ~ A observing O) as BA by now apply barbedBisim_sym. *)
    pose proof (barbedBisim_many_sym _ _ _ _ H0' _ AB) as P.
    destruct P as [A' [l']]. destruct_hyps.
    (* apply barbedBisim_sym in H15. *)
    (* specialize (IH _ _ _ _ H15 H19). *)
    epose proof (IH _ _ _ _ H10 H8) as IH2. clear IH.
    exists A', l'.
    split. assumption. assumption.
  * intros.
    epose proof (H7 source dest H0) as P. destruct P as [sourceB [Bs [B' ?]]].
    destruct_hyps.
    assert (B ~ A observing O) as BA by now apply barbedBisim_sym.
    pose proof (barbedBisim_many _ _ _ _ H8 _ BA) as [A' [As ?]]. destruct_hyps.
    pose proof H11 as B'A'. inv H11.
    specialize (H13 sourceB _ H0).
    destruct H13 as [sourceA [As' [A'' [sigsA ?]]]].
    destruct_hyps.
    exists sourceA, (As ++ As'), A''.
    split.
    - eapply closureNodeSem_trans; eassumption.
    - (* rewrite <- H29. assumption. (* transitivity is needed here! *) *)
      clear -H11 H9.
      eapply option_biforall_trans; eauto.
      intros. eapply Signal_eq_trans; eassumption.
Defined.

CoInductive barbedExpansion (O : gset PID) : Node -> Node -> Prop :=
| is_expansion A B:
  (forall A' a ι, A -[a | ι]ₙ-> A' with O -> exists B' l, 
    length l <= 1 /\ B -[l]ₙ->* B' with O /\ barbedExpansion O A' B')
  ->
  (forall source dest,
      dest ∈ O ->
      exists source',
      option_list_biforall Signal_eq (A.1 !! (source, dest)) (B.1 !! (source', dest))
      (* NOTE: this part could be adjusted based on the equivalence we are
               interested in *)) ->
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
Notation "A ⪯ B 'observing' O" := (barbedExpansion O A B) (at level 70).

Theorem barbedExpansion_implies_bisim :
  forall O A B, A ⪯ B observing O -> A ~ B observing O.
Proof.
  cofix IH. intros. inv H. constructor; auto.
  * intros. apply H0 in H. destruct H as [B' [l H]]. destruct_hyps.
    apply IH in H5. exists B', l. now auto.
  * intros. apply (H1 source dest) in H. destruct_hyps.
    exists x, [], B. split; auto. now constructor.
  * intros. apply H2 in H. destruct H as [A' [l H]]. destruct_hyps.
    apply IH in H5. exists A', l. now auto.
Defined.

CoInductive barbedBisimUpTo (O : gset PID) : Node -> Node -> Prop :=
| is_bisim_up_to (A B : Node) :
  (forall A' a ι,
      A -[a | ι]ₙ-> A' with O ->
        exists B' A'' B'' l,
          B -[l]ₙ->* B' with O /\
          A'' ⪯ A' observing O /\ B' ⪯ B'' observing O /\ barbedBisimUpTo O (* n *) A'' B'') ->
  (forall source dest,
      dest ∈ O ->
      exists source' l B',
      B -[l]ₙ->* B' with O /\
      option_list_biforall Signal_eq (A.1 !! (source, dest)) (B'.1 !! (source', dest))
      (* NOTE: this part could be adjusted based on the equivalence we are
               interested in *)) ->
  (forall B' a ι,
      B -[a | ι]ₙ-> B' with O ->
        exists A' B'' A'' l,
          A -[l]ₙ->* A' with O /\
          A' ⪯ A'' observing O /\ B'' ⪯ B' observing O /\ barbedBisimUpTo O (* n *) A'' B'') ->
  (forall source dest,
      dest ∈ O ->
      exists source' l A',
      A -[l]ₙ->* A' with O /\
      option_list_biforall Signal_eq (B.1 !! (source, dest)) (A'.1 !! (source', dest))
      (* NOTE: this part could be adjusted based on the equivalence we are
               interested in *))
->
  barbedBisimUpTo O A B.
Notation "A ~⪯~ B 'observing' O" := (barbedBisimUpTo O A B) (at level 70).

Corollary diamond_trans :
  forall O A B A' B',
    A ~ A' observing O -> B ~ B' observing O -> A' ~ B' observing O ->
    A ~ B observing O.
Proof.
  intros ????? AA' BB' A'B'.
  eapply barbedBisim_trans. exact AA'.
  eapply barbedBisim_trans. exact A'B'.
  now apply barbedBisim_sym.
Defined.


Lemma barbedExpansion_refl :
  forall O A, (* ether_wf A.1 ->  *) A ⪯ A observing O.
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
Defined.

Lemma barbedExpansion_is_expansion_up_to :
  forall O A B,
    A ⪯ B observing O -> A ~⪯~ B observing O.
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
Defined.

Lemma barbedExpansion_many :
  forall O A A' l, A -[l]ₙ->* A' with O ->
    forall B, A ⪯ B observing O ->
      exists B' l',
        B -[ l' ]ₙ->* B' with O /\ A' ⪯ B' observing O /\ length l' <= length l.
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
    - rewrite app_length. slia.
Defined.

Lemma barbedExpansion_many_sym :
  forall O B B' l', B -[l']ₙ->* B' with O ->
    forall A, A ⪯ B observing O ->
      exists A' l,
        A -[ l ]ₙ->* A' with O /\ A' ⪯ B' observing O /\ length l' <= length l.
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
    - rewrite app_length. slia.
Defined.

Lemma barbedExpansion_trans :
  forall O A B C,
    A ⪯ B observing O -> B ⪯ C observing O
    -> A ⪯ C observing O.
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
Defined.

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

Theorem barbed_alt_barbed_1 :
  forall R O, is_barbed_bisim_alt R O ->
    forall A B, R A B ->
      A ~ B observing O.
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

Theorem barbed_alt_barbed_2 :
  forall O, is_barbed_bisim_alt (barbedBisim O) O.
Proof.
  intros. intros A B IH. by inv IH.
Qed.

Corollary barbed_alt_barbed_corr :
  forall A B O, A ~ B observing O ->
    exists R, is_barbed_bisim_alt R O /\ R A B.
Proof.
  intros. exists (barbedBisim O). split; auto.
  apply barbed_alt_barbed_2.
Qed.



Theorem barbedBisimUpTo_barbedBisim :
  forall O A B, A ~⪯~ B observing O -> A ~ B observing O.
Proof.
(*   cofix IH. intros. inv H. constructor; auto.
  * clear H4 H6 H5. intros. apply H3 in H as H'.
    destruct H' as [B' [A'' [B'' [l H']]]]. destruct_hyps.
    apply barbedExpansion_implies_bisim in H5, H6.
    (* apply IH in H9.
    exists B', l. do 3 (split; auto).
    eapply barbedBisim_trans. exact H7.
    eapply barbedBisim_trans. exact H9.
    now apply barbedBisim_sym. *)
    exists B', l. do 3 (split; auto). admit.
    (* eapply barbedBisimUpTo_barbedBisim_helper in H9. 2: eassumption.
    apply barbedBisim_sym in H8.
    eapply barbedBisimUpTo_barbedBisim_helper2 in H9. 2: eassumption.
    now apply IH. *)
    (* tricks needed to fix guardedness *)
    (* eapply diamond_trans; try eassumption.
    now apply IH. Guarded. *)
    (* inv H9. *)
  * admit. *)
Abort.

Lemma reductions_preserve_singals_targeting_O :
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
