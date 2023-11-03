From CoreErlang.Concurrent Require Import BarbedBisim.

Import ListNotations.

(* BarbedBisim.v *)
Lemma preCompatibleNodes_refl :
  forall n, preCompatibleNodes n n.
Proof.
  intros. split; now destruct H.
Qed.

(* BarbedBisim.v *)
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

(* BarbedBisim.v *)
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

(* BarbedBisim.v *)
Lemma isUntaken_comp :
  forall eth Π Π' ι, isUntaken ι (eth, Π ∥∥ Π') <->
    isUntaken ι (eth, Π) /\ isUntaken ι (eth, Π').
Proof.
  split.
  {
    intros. destruct H. unfold isUntaken. simpl in *.
    unfold comp_pool in H. break_match_hyp. congruence.
    rewrite H. now easy.
  }
  {
    intros. destruct H, H, H0. simpl in *.
    split; auto.
    simpl. unfold comp_pool. now rewrite H, H0.
  }
Qed.

(* InductiveNodeSemantics.v *)
Lemma step_in_comp :
  forall eth eth' Π Π2 Π' a ι,
    (eth, Π ∥∥ Π2) -[ a | ι ]ₙ-> (eth', Π') ->
    (exists n'', (eth, Π) -[ a | ι ]ₙ-> (eth', n'') /\ (Π' = n'' ∥∥ Π2)) \/
    (exists n'', (eth, Π2) -[ a | ι ]ₙ-> (eth', n'') /\ (Π' = Π ∥∥ n'')).
Proof.
  intros. inv H.
  * apply equal_f with ι in H2 as H2'. unfold update, comp_pool in H2'.
    rewrite Nat.eqb_refl in H2'. break_match_hyp.
    - inv H2'. left. exists (ι ↦ p' ∥ Π).
      replace Π with (ι ↦ p0 ∥ Π) at 1. 2: {
        extensionality ι''.
        unfold update in *.
        break_match_goal; eqb_to_eq; try congruence.
      }
      split. now apply n_send.
      unfold update, comp_pool in *. extensionality ι''.
      apply equal_f with ι'' in H2. break_match_goal; auto.
    - right. exists (ι ↦ p' ∥ Π2).
      replace Π2 with (ι ↦ p ∥ Π2) at 1. 2: {
        extensionality ι''.
        unfold update in *.
        break_match_goal; eqb_to_eq; try congruence.
      }
      split. 1: now apply n_send.
      unfold update, comp_pool in *. extensionality ι''.
      apply equal_f with ι'' in H2. break_match_goal; eqb_to_eq; subst; auto.
      now rewrite Heqo.
  * apply equal_f with ι in H1 as H1'. unfold update, comp_pool in H1'.
    rewrite Nat.eqb_refl in H1'. break_match_hyp.
    - inv H1'. left. exists (ι ↦ p' ∥ Π).
      replace Π with (ι ↦ p0 ∥ Π) at 1. 2: {
        extensionality ι''.
        unfold update in *.
        break_match_goal; eqb_to_eq; try congruence.
      }
      split. now apply n_arrive.
      unfold update, comp_pool in *. extensionality ι''.
      apply equal_f with ι'' in H1. break_match_goal; auto.
    - right. exists (ι ↦ p' ∥ Π2).
      replace Π2 with (ι ↦ p ∥ Π2) at 1. 2: {
        extensionality ι''.
        unfold update in *.
        break_match_goal; eqb_to_eq; try congruence.
      }
      split. 1: now apply n_arrive.
      unfold update, comp_pool in *. extensionality ι''.
      apply equal_f with ι'' in H1. break_match_goal; eqb_to_eq; subst; auto.
      now rewrite Heqo.
  * apply equal_f with ι in H1 as H1'. unfold update, comp_pool in H1'.
    rewrite Nat.eqb_refl in H1'. break_match_hyp.
    - inv H1'. left. exists (ι ↦ p' ∥ Π).
      replace Π with (ι ↦ p0 ∥ Π) at 1. 2: {
        extensionality ι''.
        unfold update in *.
        break_match_goal; eqb_to_eq; try congruence.
      }
      split. now apply n_other.
      unfold update, comp_pool in *. extensionality ι''.
      apply equal_f with ι'' in H1. break_match_goal; auto.
    - right. exists (ι ↦ p' ∥ Π2).
      replace Π2 with (ι ↦ p ∥ Π2) at 1. 2: {
        extensionality ι''.
        unfold update in *.
        break_match_goal; eqb_to_eq; try congruence.
      }
      split. 1: now apply n_other.
      unfold update, comp_pool in *. extensionality ι''.
      apply equal_f with ι'' in H1. break_match_goal; eqb_to_eq; subst; auto.
      now rewrite Heqo.
  * apply equal_f with ι in H1 as H1'. unfold update, comp_pool in H1'.
    rewrite Nat.eqb_refl in H1'. break_match_hyp.
    - inv H1'. left. eexists.
      replace Π with (ι ↦ p0 ∥ Π) at 1. 2: {
        extensionality ι''.
        unfold update in *.
        break_match_goal; eqb_to_eq; try congruence.
      }
      split.
      + eapply n_spawn; eauto.
        unfold update in *. apply equal_f with ι' in H1.
        break_match_goal; eqb_to_eq; subst; try congruence.
        rewrite H5 in H1. unfold comp_pool in H1.
        break_match_hyp; congruence.
      + unfold update, comp_pool in *. extensionality ι''.
        apply equal_f with ι'' in H1. repeat break_match_goal; auto.
    - right. eexists.
      replace Π2 with (ι ↦ p ∥ Π2) at 1. 2: {
        extensionality ι''.
        unfold update in *.
        break_match_goal; eqb_to_eq; subst; try congruence.
      }
      split.
      + eapply n_spawn; eauto.
        unfold update in *. apply equal_f with ι' in H1.
        break_match_goal; eqb_to_eq; subst; try congruence.
        rewrite H5 in H1. unfold comp_pool in H1.
        break_match_hyp; congruence.
      + unfold update, comp_pool in *. extensionality ι''.
        apply equal_f with ι'' in H1.
        repeat break_match_goal; eqb_to_eq; subst; auto; try congruence.
Qed.

Lemma bisim_congr :
  forall U Π Π' eth eth', (eth, Π) ~ (eth', Π') using U ->
    forall Π2, (eth, Π ∥∥ Π2) ~ (eth', Π' ∥∥ Π2) using U.
Proof.
  cofix IH. intros. inv H. constructor; auto; simpl in *.
  * clear -H0. destruct H0. split; unfold preCompatibleNodes in *; intros.
    - apply isUntaken_comp in H1 as [H1_1 H1_2].
      apply H in H1_1.
      assert (isUntaken ι (eth', Π2)). {
        destruct H1_1, H1_2. split; auto.
      }
      now apply isUntaken_comp.
    - apply isUntaken_comp in H1 as [H1_1 H1_2].
      apply H0 in H1_1.
      assert (isUntaken ι (eth, Π2)). {
        destruct H1_1, H1_2. split; auto.
      }
      now apply isUntaken_comp.
  * clear H4 H5 H6. intros. destruct A'.
    apply step_in_comp in H as [[Π1' [? ?]] | [Π2' [? ?]]].
    - subst. apply H3 in H. destruct_hyps. destruct x as [e' Π1''].
      (* At this point, we need renamings :( - or to know what PIDs are
         spawned by Π *)
      exists (e', Π1'' ∥∥ Π2), x0. split. 2: split. 3: split.
      3: apply reductions_are_preserved_by_comp; auto.
Qed.
















Theorem action_chainable:
  forall l n n', n -[l]ₙ->* n' ->
    (* (forall ι : PID, In ι (PIDsOf sendPIDOf l) -> n'.2 ι <> None) -> *)
    (* (forall ι ι' : PID, n.2 ι' = None -> n.1 ι ι' = []) -> *)
    forall a ι n'', n -[a | ι]ₙ-> n'' ->
      In (a, ι) l \/ 
      exists n''' a' ι', n' -[a' | ι']ₙ-> n''' /\
               reductionPreCompatibility n n' [(a, ι)] [(a', ι')] /\
               reductionPreCompatibility n' n [(a', ι')] [(a, ι)].
Proof.
  induction l using list_length_ind; intros.
  
  (* induction l using list_length_ind; intros.
  destruct (length l) eqn:Hl.
  * apply length_zero_iff_nil in Hl. subst.
    inv H0. right. exists n'', a, ι.
    split; auto.
    split; eapply reductionPreCompatibility_refl; eassumption.
  * simpl in Hl. apply eq_sym, last_element_exists in Hl as Hl'.
    destruct Hl' as [l' [[a' ι'] EQ]]. subst.
    apply split_reduction in H0 as [n'0 [D1 D2]].
    rewrite app_length in Hl. simpl in Hl.
    specialize (H l' ltac:(lia) _ _ D1 _ _ _ H1). destruct H.
    - left. apply in_app_iff. now left.
    - rename n'0 into A. rename n' into B.
      destruct_hyps. inv D2. inv H9. *)
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
  * intros. Print reductionPreCompatibility. Print Action.
    
  
  (* exists n', [].
    split. 2: split. 3: split. 4: split. all: simpl.
    - split.
      + cbn. destruct a; simpl; try now constructor.
        constructor. 2: constructor.
        admit.
      + intros. admit.
    - admit.
    - lia.
    - admit.
    - admit. *)
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


