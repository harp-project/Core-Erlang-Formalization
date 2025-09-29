(**
  This file defines strong barbed bisimulation, and shows its reflexivity.
 *)
From CoreErlang Require Export Concurrent.NodeSemanticsLemmas
                               FrameStack.CTX.

Import ListNotations.

Lemma isUntaken_comp :
  forall eth Π Π' ι, isUntaken ι (eth, Π ∪ Π') <->
    isUntaken ι (eth, Π) /\ isUntaken ι (eth, Π').
Proof.
  split.
  {
    intros. destruct H. unfold isUntaken. simpl in *.
    apply lookup_union_None in H. intuition.
  }
  {
    intros. destruct H, H, H0. simpl in *.
    split; auto.
    simpl. now apply lookup_union_None.
  }
Qed.

Definition Srel (a b : Signal) :=
match a, b with
 | SMessage e, SMessage e' => forall n, Vrel n e e' /\ Vrel n e' e
 | SExit r b, SExit r' b' => b = b' /\ forall n, Vrel n r r' /\ Vrel n r' r
 | SLink, SLink => True
 | SUnlink, SUnlink => True
 | _, _ => False
end.

Definition symClos {T : Type} (R : T -> T -> Prop) : T -> T -> Prop :=
  fun t1 t2 => R t1 t2 /\ R t2 t1.


Definition preCompatibleNodes (O : gset PID) (n1 n2 : Node) : Prop :=
  forall ι, ι ∈ O ->
    isUntaken ι n1 -> isUntaken ι n2.

Lemma preCompatibleNodes_trans :
  forall O n1 n2 n3, preCompatibleNodes O n1 n2 -> preCompatibleNodes O n2 n3 ->
    preCompatibleNodes O n1 n3.
Proof.
  unfold preCompatibleNodes. intros.
  apply H in H2; auto.
Defined.

Lemma preCompatibleNodes_refl :
  forall O n, preCompatibleNodes O n n.
Proof.
  intros. intros ???. assumption.
Defined.

Lemma reduction_produces_preCompatibleNodes :
  forall O n1 n2 l, n1 -[l]ₙ->* n2 with O ->
    preCompatibleNodes O n1 n2.
Proof.
  intros. induction H.
  * apply preCompatibleNodes_refl.
  * eapply preCompatibleNodes_trans. 2: eassumption.
    clear -H. inv H.
    - split; intros; destruct H1; simpl.
      + repeat processpool_destruct; try congruence.
      + now apply isTargetedEther_etherAdd.
    - split; intros; destruct H2; simpl.
      + repeat processpool_destruct; try congruence.
      + simpl in *.
        eapply isTargetedEther_etherPop in H0 as [|]; eauto.
        subst. now setoid_rewrite lookup_insert in H2.
    - split; intros; destruct H2; simpl.
      + repeat processpool_destruct; try congruence.
      + assumption.
    - split; intros; destruct H6; simpl in *.
      + repeat processpool_destruct; try congruence.
      + assumption.
Defined.

Definition Signal_eqb (s1 s2 : Signal) : bool :=
match s1,  s2 with
 | SMessage m, SMessage m' => m =ᵥ m'
 | SExit r b, SExit r' b' => Bool.eqb b b' && (r =ᵥ r')
 | SLink, SLink => true
 | SUnlink, SUnlink => true
 | _, _ => false
end.

Notation "s1 ==ₛ s2" := (Signal_eqb s1 s2) (at level 69, no associativity).

Definition Signal_eq (s1 s2 : Signal) : Prop := s1 ==ₛ s2 = true.

Arguments Signal_eq s1 s2 /.

Notation "s1 =ₛ s2" := (Signal_eq s1 s2) (at level 69, no associativity).

(* testing Arguments *)
Local Goal forall s1 s2, s1 ==ₛ s2 = true -> s1 =ₛ s2.
Proof.
  intros. simpl. assumption.
Abort.

Corollary Signal_eq_refl :
  forall s, s =ₛ s.
Proof.
  destruct s; cbn; try reflexivity.
  * cbn. unfold "=ₛ". simpl. apply Val_eqb_refl.
  * cbn. unfold "=ₛ". simpl. rewrite Val_eqb_refl.
    now destruct b.
Defined.

Corollary Signal_eq_sym :
  forall s s', s =ₛ s' -> s' =ₛ s.
Proof.
  destruct s eqn:ES1, s' eqn:ES2; unfold "=ₛ"; cbn; intro H; try reflexivity; try now inv H.
  * now rewrite Val_eqb_sym.
  * cbn. rewrite Val_eqb_sym.
    destruct b, b0; auto.
Defined.

Corollary Signal_eq_trans :
  forall s s' s'', s =ₛ s' -> s' =ₛ s'' -> s =ₛ s''.
Proof.
  destruct s eqn:ES1, s' eqn:ES2, s'' eqn:ES3;
    unfold "=ₛ"; cbn; intros H1 H2; try reflexivity; try now inv H1; try now inv H2.
  * erewrite Val_eqb_trans; eauto.
  * apply andb_true_iff in H1, H2. destruct_and!.
    rewrite (Val_eqb_trans _ _ _ H3 H0).
    now destruct b, b0, b1.
Defined.

Theorem symClos_sym : forall {T} (R : T -> T -> Prop) A B,
  symClos R A B -> symClos R B A.
Proof.
  intros. unfold symClos in *.
  destruct H; now split.
Defined.

Lemma Signal_eq_renamePID :
  forall s from to,
    s =ₛ renamePIDSignal from to s.
Proof.
  destruct s; intros; try reflexivity.
  all: unfold Signal_eq; simpl; rewrite renamePID_Val_eqb.
  2: rewrite eqb_reflx.
  all: reflexivity.
Qed.

Lemma reduction_produces_preCompatibleNodes_sym :
  forall O n1 n2 l, n1 -[l]ₙ->* n2 with O ->
    (forall ι, ι ∈ (PIDsOf sendPIDOf l) -> (* n2.2 !! ι <> None *) ι ∉ O) ->
    preCompatibleNodes O n2 n1.
Proof.
  intros. induction H.
  * apply preCompatibleNodes_refl.
  * eapply preCompatibleNodes_trans.
    1: {
      apply IHclosureNodeSem.
      intros. apply H0. unfold PIDsOf. simpl.
      apply elem_of_app. now right.
    }
    clear IHclosureNodeSem.
    inv H.
    - split; intros; destruct H3; simpl in *.
      + repeat processpool_destruct; try congruence.
      + eapply isTargetedEther_etherAdd_rev in H4.
        processpool_destruct. congruence.
        destruct (Nat.eq_dec ι' ι0). 2: assumption. subst.
        specialize (H0 ι0 ltac:(now left)).
        apply isTargetedEther_no_spawn with (ι := ι0) in H1 as P. 2: assumption.
        eapply no_spawn_included in P. 2: eassumption.
        simpl in P. destruct P as [P _].
        apply P in H3. congruence.
    - split; intros; destruct H4; simpl in *.
      + repeat processpool_destruct; try congruence.
      + eapply isTargetedEther_etherPop_rev in H2; eauto.
    - split; intros; destruct H4; simpl in *.
      + repeat processpool_destruct; try congruence.
      + assumption.
    - split; intros; destruct H8; simpl in *.
      + repeat processpool_destruct; try congruence.
      + assumption.
Defined.

CoInductive strongBisim (O : gset PID) : (* nat -> *) Node -> Node -> Prop :=
(* | is_bisim_0 (A B : Node) : barbedBisim O 0 A B *)
| is_strong_bisim (A B : Node) :
  (forall A' a ι,
      A -[a | ι]ₙ-> A' with O ->
        exists B',
          B -[a | ι]ₙ-> B' with O /\ strongBisim O (* n *) A' B') ->
  (forall source dest,
      dest ∈ O ->
      option_list_biforall Signal_eq (A.1 !! (source, dest)) (B.1 !! (source, dest))
      (* NOTE: this part could be adjusted based on the equivalence we are
               interested in *)) -> (*
         The condition above does not need to be duplicated since Signal_eq is
         symmetric.
               *)
  (forall B' a ι,
      B -[a | ι]ₙ-> B' with O ->
        exists A',
          A -[a | ι]ₙ-> A' with O /\ strongBisim O (* n *) A' B') ->
  strongBisim O (* (S n) *) A B
.

Notation "A ~ˢ B 'observing' O" := (strongBisim O A B) (at level 70).

Theorem equality_is_strong_bisim :
  forall A O, (* ether_wf A.1 -> *) A ~ˢ A observing O.
Proof.
  cofix IH. intros. constructor.
  * intros. exists A'. split. assumption. apply IH.
  * intros. apply option_biforall_refl. intros. apply Signal_eq_refl.
  * intros. exists B'. split. assumption. apply IH.
Qed.

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

Theorem strong_alt_strong_2 :
  forall O, is_strong_bisim_alt (strongBisim O) O.
Proof.
  intros. intros A B IH. by inv IH.
Qed.

Corollary strong_alt_strong_corr :
  forall A B O, A ~ˢ B observing O ->
    exists R, is_strong_bisim_alt R O /\ R A B.
Proof.
  intros. exists (strongBisim O). split; auto.
  apply strong_alt_strong_2.
Qed.

