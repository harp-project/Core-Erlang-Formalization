From CoreErlang.Concurrent Require Import BarbedBisim.

Import ListNotations.

Lemma preCompatibleNodes_refl :
  forall n, preCompatibleNodes n n.
Proof.
  intros. split; now destruct H.
Qed.

Lemma reduction_produces_preCompatibleNodes :
  forall n1 n2 l, n1 -[l]ₙ->* n2 ->
    preCompatibleNodes n1 n2.
Proof.
  intros. induction H.
  * apply preCompatibleNodes_refl.
  * eapply preCompatibleNodes_trans. 2: eassumption.
    clear -H. inv H; split; simpl; destruct H; simpl in *; try assumption.
    all: try now unfold update in *; break_match_goal; congruence.
    - now apply isUsed_etherAdd.
    - eapply isUsed_etherPop in H0; eauto. destruct H0; auto.
      unfold update in H. subst. now rewrite Nat.eqb_refl in H.
    - clear H3 H0. unfold update in *.
      repeat break_match_goal; eqb_to_eq; try congruence.
Qed.

Lemma reduction_produces_preCompatibleNodes_sym :
  forall n1 n2 l, n1 -[l]ₙ->* n2 ->
    (forall ι, In ι (PIDsOf sendPIDOf l) ->
      n2.2 ι <> None) ->
    preCompatibleNodes n2 n1.
Proof.
  intros. induction H.
  * apply preCompatibleNodes_refl.
  * eapply preCompatibleNodes_trans.
    1: {
      apply IHclosureNodeSem.
      intros. apply H0. unfold PIDsOf. simpl.
      apply in_app_iff. now right.
    }
    clear -H H0 H1. inv H; split; simpl; destruct H; simpl in *; try assumption.
    all: try now unfold update in *; break_match_goal; congruence.
    - eapply isUsed_etherAdd_rev in H3. eassumption.
      unfold update in H. break_match_hyp. congruence. eqb_to_eq.
      destruct (Nat.eq_dec ι' ι0). 2: assumption. subst.
      specialize (H0 ι0 ltac:(now left)).
      apply isUsed_no_spawn with (ι := ι0) in H1 as H1'. 2: assumption.
      eapply no_spawn_included in H1'. 2: eassumption.
      simpl in H1'. destruct H1' as [H1' _].
      unfold update in H1'. break_match_hyp. eqb_to_eq. congruence.
      apply H1' in H. congruence.
    - eapply isUsed_etherPop_rev in H2; eauto.
    - clear H3 H0. unfold update in *.
      repeat break_match_hyp; eqb_to_eq; try congruence.
Qed.

(* InductiveNodeSemantics.v *)
Lemma ether_is_not_affected :
  forall n n' l, n -[l]ₙ->* n' ->
    (forall ι, In ι (PIDsOf sendPIDOf l) -> n'.2 ι <> None) ->
    forall source dest,
      n'.2 dest = None ->
      n.1 source dest = [] ->
      n'.1 source dest = [].
Proof.
  intros n n' l H. induction H; intros.
  assumption.
  apply IHclosureNodeSem.
  { intros. apply H1. unfold PIDsOf. simpl. apply in_app_iff. now right. }
  { assumption. }
  inv H; simpl in *; try assumption.
  * unfold etherAdd, update. repeat break_match_goal; eqb_to_eq; subst; auto.
    apply H1 in H2. 2: now left. contradiction.
  * unfold etherPop in H4. break_match_hyp. congruence.
    inv H4. unfold update. repeat break_match_goal; eqb_to_eq; subst; auto.
    rewrite H3 in Heql0. congruence.
Qed.

Theorem normalisation :
  forall n n' l,
    ether_wf n.1 ->
    (forall ι, In ι (PIDsOf sendPIDOf l) ->
      n'.2 ι <> None) -> (* Signals shouldn't be sent to the "world" *)
    (* (forall ι source dest s, In (AArrive source dest s, ι) l ->
                             n'.2 ι <> None) -> (* Signals should not
                                                   arrive to the "world" *) *)
    (forall ι ι', n.2 ι' = None -> n.1 ι ι' = []) ->
    n -[l]ₙ->* n' ->
    n ~ n' using (PIDsOf spawnPIDOf l).
Proof.
  intros. apply barbedExpansion_implies_bisim.
  generalize dependent n. generalize dependent n'. revert l. cofix IH. intros.
  constructor; auto.
  1: split; [ now eapply reduction_produces_preCompatibleNodes; eassumption
            | now eapply reduction_produces_preCompatibleNodes_sym; eassumption].
  1: now apply ether_wf_preserved in H2.
  * intros. exists n', [].
    split. 2: split. 3: split. 4: split. all: simpl.
    - split.
      + cbn. destruct a; simpl; try now constructor.
        constructor. 2: constructor.
        admit.
      + intros. admit.
    - admit.
    - lia.
    - admit.
    - admit.
  * intros. exists B', (l ++ [(a, ι)]).
    split. 2: split. 3: split. 4: split. all: simpl.
    - split.
      + cbn. destruct a; simpl; constructor; auto.
        intro. destruct H4.
        eapply isUsed_no_spawn. 2: exact H5.
        eapply closureNodeSem_trans. exact H2. econstructor 2. exact H3. constructor.
        unfold PIDsOf. rewrite flat_map_app, in_app_iff. right. cbn. now left.
      + intros.
        eapply no_spawn_included_2 in H2 as H2'. 2: exact H4.
        pose proof (no_spawn_included l n n' H2 _ H2').
        split.
        ** now apply H7.
        ** split; unfold PIDsOf; rewrite flat_map_app, in_app_iff.
           -- now right.
           -- intro. firstorder.
    - split.
      + unfold PIDsOf. rewrite flat_map_app. cbn. fold (PIDsOf spawnPIDOf l).
        rewrite app_nil_r. apply Forall_app. split.
        ** rewrite Forall_forall. intros. intro. destruct H5.
           eapply no_spawn_included_2 in H2. 2: eassumption. congruence.
        ** destruct a; simpl; constructor; auto.
           intro. destruct H4.
           inv H3. 1: clear-H7; intuition; congruence.
           simpl in *. congruence.
      + intros.
        unfold PIDsOf in H5, H6. rewrite flat_map_app in H5, H6. cbn in H5, H6.
        fold (PIDsOf spawnPIDOf l) in H6. fold (PIDsOf sendPIDOf l) in H5.
        rewrite app_nil_r in *. apply not_in_app in H6 as [H6_1 H6_2].
        eapply no_spawn_included in H2 as H2'. 2: eassumption.
        split.
        ** now apply H2'.
        ** split. 2: cbn; now rewrite app_nil_r.
           clear H6_1 H6_2.
           apply in_app_iff in H5 as [? | ?]. 2: cbn; now rewrite app_nil_r in *.
           exfalso. apply H0 in H5.
           now apply H2' in H4.
    - rewrite app_length. slia.
    - eapply closureNodeSem_trans. eassumption. econstructor. eassumption. constructor.
    - apply barbedExpansion_refl.
      eapply ether_wf_preserved. 2: eassumption.
      eapply closureNodeSem_trans. eassumption. econstructor. eassumption. constructor.
  * intros. exists source.
    eapply no_spawn_included in H3. 2: eassumption. apply H3 in H4 as H4'.
    split. assumption.
    apply (H1 source) in H4.
    eapply ether_is_not_affected in H2. 2-4: eassumption.
    rewrite H2. assumption.
  * intros. exists source, l, n'. split; auto.
Abort.


