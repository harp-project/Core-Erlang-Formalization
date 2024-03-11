From CoreErlang Require Export Concurrent.InductiveNodeSemantics
                               Concurrent.ProcessSemantics
                               Concurrent.PIDRenaming
                               Concurrent.WeakBisim.

Import ListNotations.


(*
Definition reductionPreCompatibility (n1 n2 : Node) l l' :=
  Forall (fun x => ~isUntaken x n2) (PIDsOf spawnPIDOf l) /\
  (forall ι, ι ∉ dom n1.2 ->
             In ι (PIDsOf sendPIDOf l) -> 
             ~In ι (PIDsOf spawnPIDOf l) ->
        ι ∉ dom n2.2 /\
        In ι (PIDsOf sendPIDOf l') /\
        ~In ι (PIDsOf spawnPIDOf l')).

Theorem reduction_preserves_preCompatibility :
  forall n1 n2, (* symClos *) preCompatibleNodes n1 n2 ->
    forall n1' n2' l l',
      n1 -[l]ₙ->* n1' ->
      n2 -[l']ₙ->* n2' ->
      (* Should not spawn incompatible processes: *)
      reductionPreCompatibility n1 n2 l l' ->
      reductionPreCompatibility n2 n1 l' l ->
        (* symClos *) preCompatibleNodes n1' n2'.
Proof.
  intros.
  unfold preCompatibleNodes in *. destruct H2 as [H2 H4], H3 as [H3 H5]. intros.
  eapply compatibility_of_reductions_rev in H0 as H0'. 2: eassumption.
  destruct H0'.
  * apply H in H7 as H7'.
    destruct (in_dec Nat.eq_dec ι (PIDsOf spawnPIDOf l')).
    - rewrite Forall_forall in H3. apply H3 in i. congruence.
    - eapply compatibility_of_reductions in H7' (* as [H7' | H7'] *).
      2: eassumption.
      assumption. (*  destruct_hyps. exfalso. now apply n. *)
  * destruct_hyps.
    destruct (in_dec Nat.eq_dec ι (PIDsOf spawnPIDOf l)).
    - eapply included_spawn in H0. 2: eassumption. now destruct H6.
    - apply not_elem_of_dom in H9.
      apply (H4 _ H9 H7) in n. destruct_hyps.
      apply not_elem_of_dom in H10.
      pose proof (appearsEther_after_send _ _ _ H1 _ H11 H12 H10).
      split; try assumption.
      apply -> no_spawn_included; eauto.
Defined.

Corollary reduction_preserves_compatibility :
  forall n1 n2, symClos preCompatibleNodes n1 n2 ->
    forall n1' n2' l l',
      n1 -[l]ₙ->* n1' ->
      n2 -[l']ₙ->* n2' ->
      reductionPreCompatibility n1 n2 l l' ->
      reductionPreCompatibility n2 n1 l' l ->
        symClos preCompatibleNodes n1' n2'.
Proof.
  intros. destruct H; split.
  * eapply reduction_preserves_preCompatibility.
    2-3: eassumption. all: eassumption.
  * eapply reduction_preserves_preCompatibility.
    2-3: eassumption. all: eassumption.
Defined.
*)

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
    - eapply closureNodeSem_trans. exact H5.
      econstructor. exact H6.
      exact H7.
    - by apply IH.
  * intros. apply (H1 source) in H as [B' [l ?]]. destruct_hyps.
    exists source, l, B'. split; assumption.
  * intros. apply H2 in H. destruct H as [A' [A'' [A''' [l1 [l2 ?]]]]].
    destruct_hyps. exists A''', (l1 ++ (a, ι) :: l2). split.
    - eapply closureNodeSem_trans. exact H5.
      econstructor. exact H6.
      exact H7.
    - by apply IH.
  * intros. apply (H3 source) in H as [A' [l ?]]. destruct_hyps.
    exists source, l, A'. split; assumption.
Qed.



(* Theorem reductionPreCompatibility_refl O A A' a ι:
  A -[ a | ι ]ₙ-> A' with O ->
  reductionPreCompatibility O A A [(a, ι)] [(a, ι)].
Proof.
  split; intros.
  * cbn. break_match_goal; auto. constructor; auto.
    intro. destruct H0. destruct a; inv Heqo. inv H.
    1: destruct H3 as [? | [? | ?]]; congruence.
    simpl in *. congruence.
  * cbn in H1. break_match_hyp; inv H1. 2: { inv H3. }
    destruct a; inv Heqo. split; auto. split; auto.
    now constructor.
Defined. *)


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

(* Lemma preCompatibleNodes_trans :
  forall A B C, preCompatibleNodes A B -> preCompatibleNodes B C ->
    preCompatibleNodes A C.
Proof.
  intros. intros ι Hi. apply H in Hi.
Defined. *)

(*
Lemma reductionPreCompatibility_app :
  forall As Bs A B,
    reductionPreCompatibility A B As Bs ->
    reductionPreCompatibility B A Bs As ->
    forall As' Bs' A' B' B'' (* B'' A'' *),
      A -[As]ₙ->* A' ->
      (* A' -[ys]ₙ->* A'' -> *)
      B -[Bs]ₙ->* B' ->
      B' -[Bs']ₙ->* B'' ->
      reductionPreCompatibility A' B' As' Bs' ->
      reductionPreCompatibility B' A' Bs' As' ->
      reductionPreCompatibility A B (As ++ As') (Bs ++ Bs').
Proof.
  intros As Bs A B C1 C2 As' Bs' A' B' B'' D1A D1 D2 C1' C2'.
  unfold reductionPreCompatibility in *.
  destruct C1 as [C1_1 C1_2]. destruct C2 as [C2_1 C2_2].
  destruct C1' as [C1_1' C1_2']. destruct C2' as [C2_1' C2_2'].
  split.
  * clear C2_2' C1_2' C1_2 C2_2.
    unfold PIDsOf. rewrite flat_map_app. fold (PIDsOf spawnPIDOf As).
    fold (PIDsOf spawnPIDOf As'). apply Forall_app; split; auto.
    (** Proof by contradiction :
        If ι ∈ (PIDsOf spawnPIDOf ys) 
        1) were used (isUsed ι B), then it couldn't be contained in
           this list (spawn could not happen on it).
        2) were assigned in B (B.2 ι = Some proc), then spawn could
           not happen on it
    *)
    rewrite Forall_forall in *. intros. apply C1_1' in H as H'. clear C1_1'.
    intro H0.
    eapply compatibility_of_reductions in H0 as H0'. 2: eassumption.
    congruence. (* 
    destruct H0'. (* congruence. *) destruct_hyps.
    destruct H0. pose proof (appearsEther_no_spawn _ _ _ D1 _ H3). *)
  * intros ι Ha Hin1 Hin2. unfold PIDsOf in Hin1, Hin2.
    rewrite flat_map_app in *.
    fold (PIDsOf spawnPIDOf As) in *. fold (PIDsOf spawnPIDOf As') in *.
    fold (PIDsOf sendPIDOf As) in Hin1. fold (PIDsOf sendPIDOf As') in Hin1.
    apply not_in_app in Hin2 as [Hin2_1 Hin2_2].
    apply in_app_or in Hin1 as [Hin1 | Hin1].
    - specialize (C1_2 _ Ha Hin1 Hin2_1) as [H8_1 [H8_2 H8_3]]. split; auto.
      split.
      + unfold PIDsOf. rewrite flat_map_app. eapply in_app_iff.
        now left.
      + unfold PIDsOf. rewrite flat_map_app.
        fold (PIDsOf spawnPIDOf Bs). fold (PIDsOf spawnPIDOf Bs').
        apply app_not_in; auto.
        eapply appearsEther_no_spawn. exact D2.
        eapply appearsEther_after_send; eauto.
        now apply not_elem_of_dom.
    - eapply no_spawn_included in Hin2_1. 2: eassumption.
      apply not_elem_of_dom in Ha.
      rewrite Hin2_1 in Ha.
      apply not_elem_of_dom in Ha.
      specialize (C1_2' _ Ha Hin1 Hin2_2) as [H8_1 [H8_2 H8_3]]. split.
      2: split.
      + apply not_elem_of_dom. eapply processes_dont_die_None; try eassumption.
        now apply not_elem_of_dom.
      + unfold PIDsOf. rewrite flat_map_app. eapply in_app_iff.
        now right.
      + unfold PIDsOf. rewrite flat_map_app.
        fold (PIDsOf spawnPIDOf Bs). fold (PIDsOf spawnPIDOf Bs').
        apply app_not_in; auto.
        eapply no_spawn_included_2. eassumption.
        apply not_elem_of_dom. assumption.
Defined.
*)

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

(* Theorem reductionPreCompatibility_trans :
  forall A C B As Bs Cs,
    reductionPreCompatibility A B As Bs ->
    reductionPreCompatibility B C Bs Cs ->
    reductionPreCompatibility A C As Cs.
Proof.
  intros. destruct H, H0. split.
  * rewrite Forall_forall in *. intros.
    apply H in H3 as H3'.
Defined. *)

(* Lemma Vrel_trans :
  forall n v1 v2, Vrel n v1 v2 -> forall v3, Vrel n v2 v3 -> Vrel n v1 v3.
Proof.
  intros n v1 v2 H.
  assert (VALCLOSED v1) by now apply Vrel_closed_l in H. revert H0.
  induction H using Vrel_ind; destruct v3; intros;
    try now (try rewrite Vrel_Fix_eq in H;
             try rewrite Vrel_Fix_eq in H1;
             simpl in *; destruct_hyps; auto).
  * rewrite Vrel_Fix_eq. simpl. split. 2: split.
    1: apply H0.
    1: now apply Vrel_closed_r in H.
    rewrite Vrel_Fix_eq in H. simpl in H. destruct_hyps. subst.
    split. 2: split. 1-2: auto.
Defined. *)

(* Corollary Srel_trans :
  forall s1 s2 s3, Srel s1 s2 -> Srel s2 s3 -> Srel s1 s3.
Proof.
  intros; destruct s1, s2, s3; simpl in *; try contradiction.
  * intros. split; apply CIU_Val_compat_closed_reverse.
    - specialize (H n) as [H _]. specialize (H0 n) as [H0 _].
      apply Erel_Val_compat_closed in H, H0.
      apply Rrel_exp_compat_closed in H, H0.
      apply CIU_iff_Rrel_closed in H, H0.
Defined. *)


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


(* Lemma barbedBisimUpTo_many :
  forall A A' l, A -[l]ₙ->* A' ->
    forall U B, A ~⪯~ B observing O ->
      exists B' A'' B'' l',
        reductionPreCompatibility A B l l' /\
        reductionPreCompatibility B A l' l /\
        B -[ l' ]ₙ->* B' /\ A' ⪯ A'' observing O /\ A'' ~⪯~ B'' observing O /\ B' ⪯ B'' observing O.
Proof.
  intros A A' l. revert A A'. induction l; intros; inv H.
Abort.

Lemma barbedBisimUpTo_barbedBisim_helper :
  forall U A B A' B',
    A ⪯ A' observing O -> A' ~⪯~ B' observing O -> B ⪯ B' observing O
    -> A ~⪯~ B observing O.
Proof.
  cofix IH. intros. pose proof H as AA'. pose proof H1 as BB'.
  constructor; auto.
  * inv H0. split.
    - eapply preCompatibleNodes_trans.
      inv H. apply H0. eapply preCompatibleNodes_trans.
      apply H2. inv H1. apply H0.
    - eapply preCompatibleNodes_trans.
      inv H1. apply H0. eapply preCompatibleNodes_trans.
      apply H2. inv H. apply H0.
  * now inv H.
  * now inv H1.
  * intros. rename A'0 into A0.
    inv H. apply H6 in H2 as [A'0 [l ?]]. destruct_hyps.
    clear H6 H7 H8 H9.
    eapply barbedBisimUpTo_many in H11. 2: eassumption.
    destruct H11 as [B'' [A''' [B''' [l'' H11]]]]. destruct_hyps.
    
Abort.

Lemma barbedBisimUpTo_trans :
  forall U A B C,
    A ~⪯~ B observing O -> B ~⪯~ C observing O
    -> A ~⪯~ C observing O.
Proof.
  cofix IH. intros.
  constructor; auto. 2-3: inv H; inv H0; auto.
  * inv H. inv H0. split.
    - eapply preCompatibleNodes_trans.
      inv H. apply H1. apply H.
    - eapply preCompatibleNodes_trans.
      inv H1. apply H. apply H1.
  * intros. inv H. apply H5 in H1. destruct H1 as [B' [A'' [B'' [lB H1]]]].
    destruct_hyps.
    eapply barbedBisimUpTo_many in H9. 2: eassumption.
    destruct H9 as [C' [B''0 [C'' [lC H9]]]]. destruct_hyps.
    exists C', A'', C'', lC. split. 2: split. 3: split.
    3: assumption.
    (* - clear -H H1 H9 H13 H2 H0.
      destruct H, H1, H9, H13. split.
      + rewrite Forall_forall in *.
        intros. apply H in H9. intro.
        apply H5 in H10; auto.
        
      + intros. apply H21 in H27; eauto.
        destruct_hyps. apply H23 in H27; eauto.
    - destruct H0', H7, H16, H17. split.
      + rewrite Forall_forall in *.
        intros. apply H17 in H25. intro.
        now apply H1 in H26.
      + intros. apply H24 in H27; eauto.
        destruct_hyps. apply H22 in H27; eauto. *)
    1-2: admit.
    split. 2: split. 1-3: try assumption.
    eapply IH. 2: eassumption.
    apply barbedExpansion_implies_bisim in H15.
Abort. *)

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

(*
Definition barbedCongr (U V : list PID) (A B : Node) : Prop :=
  forall C : ProcessPool,
    Forall (fun p => ~isUsedPool p C) V ->
      (A.1, A.2 ∪ C) ~ (B.1, B.2 ∪ C) observing O.


(* Lemma barbedBisimUpTo_many :
  forall A A' l, A -[l]ₙ->* A' ->
    forall U B A'' B'', A ⪯ A'' observing O -> A'' ~⪯~ B'' observing O -> B ⪯ B'' observing O ->
      exists B' A''' B''' l',
        reductionPreCompatibility A B l l' /\
        reductionPreCompatibility B A l' l /\
        B -[ l' ]ₙ->* B' /\ A' ⪯ A''' observing O /\ A''' ~⪯~ B''' observing O /\ B' ⪯ B''' observing O.
Proof.
  intros A A' l. revert A A'. induction l; intros; inv H.
  * exists B, A', B, []. split. 2: split. 3: split. 4: split. 5: split.
    3: constructor.
    1-2: split; constructor; auto.
    1-2: inv H3.
    2: { 
    1-2: apply barbedExpansion_refl; now inv H0.
  * rename A' into A''. rename n' into A'.
    inv H0. apply H3 in H4 as H'. destruct H' as [B' [A''0 [B'' [lB H']]]].
    destruct_hyps.
    clear H3 H5 H8 H7. eapply IHl in H6. Unshelve. 3: exact B'. 3: exact U.
    2: { clear -H6 H11 H12 H13.
    destruct H12 as [A'' [l'' H12]].
    destruct_hyps.
    exists A'', (l ++ l''). split. 2: split. 3: split. 4: split.
    4: assumption.
    3: eapply closureNodeSem_trans; eassumption.
    unfold symClos, preCompatibleNodes in H1.
    - replace (_ :: _) with ([(a0, ι)] ++ l') by reflexivity.
      eapply reductionPreCompatibility_app; try eassumption.
      econstructor. eassumption. constructor.
    - replace (_ :: _) with ([(a0, ι)] ++ l') by reflexivity.
      eapply reductionPreCompatibility_app; try eassumption.
      econstructor. eassumption. constructor.
    - rewrite app_length. slia.
Abort. *)

(* Lemma barbedBisimUpTo_barbedBisim_helper_asd :
  forall U A B C,
    A ⪯ B observing O -> B ~⪯~ C observing O
    -> A ~⪯~ C observing O.
Proof.
  cofix IH. intros.
  constructor; auto. 2-3: inv H; inv H0; auto.
  * inv H. inv H0. split.
    - eapply preCompatibleNodes_trans.
      inv H. apply H1. apply H.
    - eapply preCompatibleNodes_trans.
      inv H1. apply H. apply H1.
  * intros. inv H. apply H5 in H1. destruct H1 as [B' [lB H1]].
    destruct_hyps.
    eapply barbedBisimUpTo_many in H10. 2: eassumption.
    destruct H10 as [C' [B''0 [C'' [lC H10]]]]. destruct_hyps.
    exists C', A', C'', lC. split. 2: split. 3: split.
    3: assumption.
    1-2: shelve.
    split. 2: split. 2: assumption.
    apply barbedExpansion_refl. now inv H11.
    apply (barbedExpansion_trans _ _ _ _ H11) in H14.
    eapply IH; eassumption.
    Unshelve.
    - inv H0.
      clear -H H1 H10 H12 H2 H17.
      destruct H, H1, H10, H12. split.
      + rewrite Forall_forall in *.
        intros. apply H in H8. intro.
        now apply H17 in H9.
      + intros. apply H0 in H10; eauto.
        destruct_hyps. apply H5 in H12; eauto.
    - inv H0.
      clear -H H1 H10 H12 H2 H17.
      destruct H, H1, H10, H12. split.
      + rewrite Forall_forall in *.
        intros. apply H6 in H8. intro.
        now apply H2 in H9.
      + intros. apply H7 in H10; eauto.
        destruct_hyps. apply H3 in H12; eauto.
  * 
Defined. *)

Lemma barbedBisimUpTo_barbedBisim_helper :
  forall U A B C,
    A ~ B observing O -> B ~⪯~ C observing O
    -> A ~⪯~ C observing O.
Proof.
  cofix IH. intros. pose proof H as AB. inv H.
  pose proof H0 as BC. inv H0.
  constructor; auto.
  * split.
    - eapply preCompatibleNodes_trans.
      inv H. apply H1. apply H.
    - eapply preCompatibleNodes_trans.
      inv H1. apply H. apply H1.
  * intros.
    clear H5 H6 H7 H11 H12 H13.
    apply H4 in H0. destruct H0 as [B' [l H0]]. destruct_hyps.
   (*  pose proof (barbedBisim_expansion_many _ _ _ H6 _ _ BC).
    destruct H11 as [C' [l']]. destruct_hyps.
    specialize (IH _ _ _ _ H7 H14). exists C', l'.
    split. 2: split. 3: split; auto.
    - destruct H0, H5, H11, H12. split.
      + rewrite Forall_forall in *.
        intros. apply H0 in H19. intro.
        now apply H in H20.
      + intros. apply H15 in H21; eauto.
        destruct_hyps. apply H17 in H23; eauto.
    - destruct H0, H5, H11, H12. split.
      + rewrite Forall_forall in *.
        intros. apply H12 in H19. intro.
        now apply H1 in H20.
      + intros. apply H18 in H21; eauto.
        destruct_hyps. apply H16 in H23; eauto.
  * intros.
    epose proof (H5 source dest H0). destruct H14 as [sourceB [Bs [B' ?]]].
    destruct_hyps.
    pose proof (barbedBisim_expansion_many _ _ _ H14 _ _ BC) as [C' [Cs ?]]. destruct_hyps.
    pose proof H19 as B'C'. inv H19.
    specialize (H24 sourceB _ H0). destruct H24 as [sourceC [Cs' [C'' ?]]].
    destruct_hyps.
    exists sourceC, (Cs ++ Cs'), C''.
    split.
    - eapply closureNodeSem_trans; eassumption.
    - rewrite <- H24. assumption. (* transitivity is needed here! *)
  * 
  * *)
Abort.

Lemma barbedBisimUpTo_barbedBisim_helper2 :
  forall U A B C,
    A ~⪯~ B observing O -> B ~ C observing O
    -> A ~⪯~ C observing O.
Proof.
  
Abort. *)

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
