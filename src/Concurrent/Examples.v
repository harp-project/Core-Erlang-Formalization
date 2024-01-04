From CoreErlang.Concurrent Require Import BarbedBisim.

Import ListNotations.

(* InductiveNodeSemantics.v *)
(* Lemma ether_is_not_affected :
  forall n n' l, n -[l]ₙ->* n' ->
    (forall ι, In ι (PIDsOf sendPIDOf l) -> n'.2 !! ι <> None) ->
    forall source dest,
      n'.2 !! dest = None ->
      n.1 !! (source, dest) = [] ->
      n'.1 !! (source, dest) = []. *)
Lemma ether_is_not_affected :
  forall n n' l, n -[l]ₙ->* n' ->
    (forall ι, In ι (PIDsOf sendPIDOf l) -> n'.2 !! ι <> None) ->
    forall source dest,
      n'.2 !! dest = None ->
      n.1 !! (source, dest) = n'.1 !! (source, dest).
Proof.
  intros n n' l H. induction H; intros; try reflexivity.
  setoid_rewrite <- IHclosureNodeSem.
  2: { intros. apply H1. unfold PIDsOf. simpl. apply in_app_iff. now right. }
  2: { assumption. }
  inversion H; subst; simpl in *; try reflexivity.
  * unfold etherAdd. destruct (decide ((ι, ι') = (source, dest))).
    - inv e. exfalso. eapply H1. left. reflexivity. assumption.
    - break_match_goal; setoid_rewrite lookup_insert_ne; try assumption; auto.
  * unfold etherPop in H3. destruct (decide ((ι1, ι) = (source, dest))).
    - inv e. exfalso. eapply processes_dont_die_Some in H0.
      2: { setoid_rewrite lookup_insert. reflexivity. }
      inv H0. congruence.
    - break_match_hyp; try congruence. destruct l0; try congruence. inv H3.
      setoid_rewrite lookup_insert_ne; auto.
Qed.

(* BarbedBisim.v *)
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

Lemma insert_of_union :
  forall ι p Π Π2 prs,
  ι ↦ p ∥ prs = Π ∪ Π2 ->
  Π = ι ↦ p ∥ Π \/ (ι ∉ dom Π /\ Π2 = ι ↦ p ∥ Π2).
Proof.
  intros.
  put (lookup ι : ProcessPool -> _) on H as H'. simpl in H'.
  setoid_rewrite lookup_insert in H'.
  symmetry in H'. apply lookup_union_Some_raw in H'. destruct H' as [H' | [H_1 H_2]].
  * left. apply map_eq. intros.
    destruct (decide (i = ι)); subst.
    - now setoid_rewrite lookup_insert.
    - now setoid_rewrite lookup_insert_ne.
  * right. split. now apply not_elem_of_dom.
    apply map_eq. intros.
    destruct (decide (i = ι)); subst.
    - now setoid_rewrite lookup_insert.
    - now setoid_rewrite lookup_insert_ne.
Qed.

(* InductiveNodeSemantics.v *)
Lemma step_in_comp :
  forall eth eth' Π Π2 Π' a ι,
    (eth, Π ∪ Π2) -[ a | ι ]ₙ-> (eth', Π') ->
    (exists n'', (eth, Π) -[ a | ι ]ₙ-> (eth', n'') /\ (Π' = n'' ∪ Π2)) \/
    (exists n'', (eth, Π2) -[ a | ι ]ₙ-> (eth', n'') /\ (Π' = Π ∪ n'')).
Proof.
  intros. inv H.
  * apply insert_of_union in H2 as H2'. destruct_or!.
    - setoid_rewrite H2'. left. exists (ι ↦ p' ∥ Π).
      split. now apply n_send.
      apply map_eq. intros. put (lookup i : ProcessPool -> _) on H2 as H2''.
      simpl in *. rewrite par_comp_assoc_pool.
      repeat processpool_destruct; try congruence.
    - inv H2'. setoid_rewrite H0. right. exists (ι ↦ p' ∥ Π2).
      split. 1: now apply n_send.
      apply map_eq. intros. put (lookup i : ProcessPool -> _) on H2 as H2''.
      simpl in *. setoid_rewrite <- insert_union_r. 2: now apply not_elem_of_dom.
      repeat processpool_destruct; try congruence.
  * apply insert_of_union in H1 as H1'. destruct_or!.
    - setoid_rewrite H1'. left. exists (ι ↦ p' ∥ Π).
      split. apply n_arrive; auto.
      apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as H1''.
      simpl in *. rewrite par_comp_assoc_pool.
      repeat processpool_destruct; try congruence.
    - inv H1'. setoid_rewrite H0. right. exists (ι ↦ p' ∥ Π2).
      split. 1: now apply n_arrive.
      apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as H1''.
      simpl in *. setoid_rewrite <- insert_union_r. 2: now apply not_elem_of_dom.
      repeat processpool_destruct; try congruence.
  * apply insert_of_union in H1 as H1'. destruct H1'.
    - setoid_rewrite H. left. exists (ι ↦ p' ∥ Π).
      split. apply n_other; auto.
      apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as H1''.
      simpl in *. rewrite par_comp_assoc_pool.
      repeat processpool_destruct; try congruence.
    - inv H. setoid_rewrite H2. right. exists (ι ↦ p' ∥ Π2).
      split. 1: now apply n_other.
      apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as H1''.
      simpl in *. setoid_rewrite <- insert_union_r. 2: now apply not_elem_of_dom.
      repeat processpool_destruct; try congruence.
  * apply insert_of_union in H1 as H1'. destruct_or!.
    - setoid_rewrite H1'. left.
      exists (ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π).
      split. eapply n_spawn; eauto.
      1: put (dom : ProcessPool -> _) on H1 as P; simpl in *; clear -P H5 H6; set_solver.
      apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as H1''.
      simpl in *. do 2 rewrite par_comp_assoc_pool.
      repeat processpool_destruct; try congruence.
    - inv H1'. setoid_rewrite H0. right. exists (ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π2).
      split. 1: eapply n_spawn; eauto.
      1: put (dom : ProcessPool -> _) on H1 as P; simpl in *; clear -P H5 H6; set_solver.
      apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as H1''.
      simpl in *. repeat setoid_rewrite <- insert_union_r.
      2: now apply not_elem_of_dom.
      2: put (dom : ProcessPool -> _) on H1 as P; simpl in *; apply not_elem_of_dom; set_solver.
      repeat processpool_destruct; try congruence.
Qed.

(* InductiveNodeSemantics.v *)
(* Corollary isNotUsed_renamePID_ether :
  forall eth from to, ¬isUsedEther from eth ->
                      ¬isUsedEther to eth -> renamePIDEther from to eth = eth.
Proof.
  intros. unfold renamePIDEther. apply map_eq_iff. intros.
  destruct (eth !! i) eqn:P; setoid_rewrite P.
  * apply lookup_kmap_Some; auto. admit.
  * apply lookup_kmap_None; auto. intros. destruct i, i0. simpl in H1.
    inv H1. rewrite lookup_fmap. unfold renamePIDPID_sym in P.
    unfold isUsedEther in *. repeat case_match; eqb_to_eq; subst.
    - assert (forall ι' x l, eth !! (ι', from) <> Some (x :: l)) by firstorder.
Admitted. *)

(* InductiveNodeSemantics.v *)
(* Corollary double_renamePID_ether :
  forall eth from to, ¬isUsedEther to eth  -> renamePIDEther to from (renamePIDEther from to eth) = eth.
Proof.
  intros. unfold renamePIDEther.
  intros. unfold renamePIDEther. apply map_eq_iff. intros.
  unfold isUsedEther in H.
  assert (forall ι', eth !! (ι', to) = None). {
    intros. apply eq_None_ne_Some. intros ? ?.
    apply H. do 2 eexists. eassumption.
  }
  destruct i as [ιs ιd]. destruct (decide (to = ιd)); subst.
  * rewrite H0. apply lookup_kmap_None; auto. intros.
    destruct i; inv H1. unfold renamePIDPID_sym in H4.
    rewrite lookup_fmap. apply fmap_None.
    apply lookup_kmap_None; auto. intros.
    destruct i; inv H1. unfold renamePIDPID_sym in H5.
    rewrite lookup_fmap. apply fmap_None.
    repeat case_match; eqb_to_eq; subst; try apply H0; congruence.
  * admit.
Admitted. *)


(* Corollary isNotUsed_renamePID_pool :
  forall Π from to, ¬isUsedPool from Π -> renamePIDPool from to Π = Π.
Proof.
  intros.
Admitted. *)

(* Corollary double_renamePID_pool :
  forall Π from to, ¬isUsedPool to Π  -> renamePIDPool to from (renamePIDPool from to Π) = Π.
Proof.

Admitted. *)

Lemma rename_preCompatible :
  forall eth Π p p',
  ¬isUsedPool p' Π ->
  p' ∉ dom Π ->
  ¬isUsedEther p' eth ->
  p ∈ dom Π -> (* <- renaming only makes sense for existing process
    NOTE, that this could be weakened to `¬isUntaken p (eth, Π)`. This theorem
    would not make sense for such a `p`, that is reserved for the outside
   *)
  preCompatibleNodes (eth, Π)
    (renamePIDEther p p' eth, renamePIDPool p p' Π).
Proof.
  split; simpl.
  * apply lookup_kmap_None; auto. intros.
    destruct H3. unfold renamePIDPID_sym in H4. repeat case_match; eqb_to_eq; subst.
    - simpl in *. congruence.
    - rewrite lookup_fmap. apply not_elem_of_dom in H0. now setoid_rewrite H0.
    - rewrite lookup_fmap. simpl in *. now setoid_rewrite H3.
  * destruct H3. simpl in *.
    assert (ι ≠ p'). {
      intro. subst. congruence.
    }
    assert (ι ≠ p). {
      intro. subst. now apply not_elem_of_dom in H3.
    }
    now apply isUsedEther_rename_same_neq.
Qed.


Corollary rename_preCompatible_sym :
  forall eth Π p p',
  ¬isUsedPool p' Π ->
  p' ∉ dom Π ->
  ¬isUsedEther p' eth ->
  p ∈ dom Π ->
  symClos preCompatibleNodes (eth, Π)
    (renamePIDEther p p' eth, renamePIDPool p p' Π).
Proof.
  intros. split.
  * apply rename_preCompatible; auto.
  * admit.
Admitted.

Lemma SIGCLOSED_rename :
  forall s p p', SIGCLOSED s <-> SIGCLOSED (renamePIDSignal p p' s).
Proof.
  intros. destruct s; simpl; auto.
  all: split; intro; try by apply renamePID_preserves_scope.
  1-2: admit. (* corresponding lemma needs to be expressed with <-> *)
Admitted.

Lemma Signal_eq_renamePID :
  forall s from to,
    s =ₛ renamePIDSignal from to s.
Proof.
  destruct s; intros; try reflexivity.
  all: unfold Signal_eq; simpl; rewrite renamePID_Val_eqb.
  2: rewrite eqb_reflx.
  all: reflexivity.
Qed.

Lemma ether_wf_rename :
  forall eth p p',
    ether_wf eth <-> ether_wf (renamePIDEther p p' eth).
Proof.
  split; intro; unfold ether_wf, renamePIDEther in *; intros.
  * apply lookup_kmap_Some in H0. 2: auto. destruct H0 as [[s d] [Eq H0]].
    simpl in Eq. inv Eq. rewrite lookup_fmap in H0.
    destruct (eth !! (s, d)) eqn:P; setoid_rewrite P in H0. 2: inv H0.
    apply H in P. inv H0.
    apply Forall_forall. intros. rewrite Forall_forall in P.
    apply in_map_iff in H0 as [? [? ?]]. apply P in H1.
    subst x. now apply SIGCLOSED_rename.
  * (* case separation needed for ι = p/p' *)
    assert ((map (renamePIDSignal p p') <$> eth) !! (ι, ι') = map (renamePIDSignal p p') <$> Some l). {
      rewrite lookup_fmap. by setoid_rewrite H0.
    }
    simpl in H1.
    pose proof (lookup_kmap (prod_map (renamePIDPID_sym p p') (renamePIDPID_sym p p')) (map (renamePIDSignal p p') <$> eth) (ι, ι')).
    setoid_rewrite <- H2 in H1. apply H in H1.
    clear -H1. apply map_Forall in H1; auto.
    intros. by apply SIGCLOSED_rename in H.
Qed.

Lemma rename_reduction_compatible_1 :
  forall eth Π p p' l,
  ¬ isUsedPool p' Π ->
  ¬ isUsedEther p' eth ->
  ¬In p' (flat_map (fun '(a, ι) => ι::usedPIDsAct a) l) ->
  reductionPreCompatibility (eth, Π) (eth .[ p ⇔ p' ]ₑ, Π .[ p ⇔ p' ]ₚₚ)
                   l (map (prod_map (renamePIDAct p p') (renamePIDPID_sym p p')) l).
Proof.
  intros. split.
  * apply Forall_forall. intros. intro.
    destruct H3; simpl in *. unfold renamePIDPool in H3.
    assert (x <> p'). {
      admit. (* Because H2 + H1 *)
    }
    destruct (decide (x = p)).
    - subst. admit. (* H4 and H0 are contradictory *)
    - admit. (* additional hypothesis needed: (eth,Π) -[l]ₙ->* (eth',Π')
                1. renamePIDPID_sym p p' x = x in this case
                2. then -> isUsedEther x eth
                3. however, x is a spawn PID, and it is used -> contradiction *)
  * simpl. intros. split. 2: split.
    - 
    -
    -
Qed.

Lemma rename_reduction_compatible_2 :
  forall eth Π p p' l,
  reductionPreCompatibility (eth .[ p ⇔ p' ]ₑ, Π .[ p ⇔ p' ]ₚₚ) (eth, Π)
                   (map (prod_map (renamePIDAct p p') (renamePIDPID_sym p p')) l) l.
Proof.
  
Qed.


Theorem rename_bisim :
  forall eth Π p p',
    ether_wf eth ->
    ¬isUsedEther p' eth ->
    p' ∉ dom Π ->
    p ∈ dom Π ->
    ¬isUsedPool p' Π ->
    (eth, Π) ~ (renamePIDEther p p' eth, renamePIDPool p p' Π) using [].
Proof.
  cofix IH.
  intros. constructor; auto.
  * apply rename_preCompatible_sym; assumption.
  * simpl. by apply ether_wf_rename.
  * intros. destruct A' as [eth' Π'].
    destruct (in_dec Nat.eq_dec p' (usedPIDsAct a)).
    {
      assert (exists v1 v2, a = ASpawn p' v1 v2). {
        admit. (* only spawn could obtain a fresh action PID *)
      }
      assert (exists p'', p'' ∉ dom Π /\ p'' ∉ dom Π' /\ ¬isUsedEther p'' eth /\ ¬isUsedEther p'' eth'). {
        unfold isUsedEther.
        admit. (* use `fresh` function *)
      }
      destruct_hyps. subst.
      (* inversion H4; subst.
      1: clear -H16; exfalso; destruct_or!; congruence. *)
      
      
      
      exists (renamePIDEther p p' (renamePIDEther p' x eth'), renamePIDPool p p' (renamePIDPool p' x Π')),
             [(renamePIDAct p p' (renamePIDAct p' x (ASpawn p' x0 x1)), renamePIDPID_sym p p' (renamePIDPID_sym p' x ι))].
      split. 2: split. 3: split.
      - admit.
      - admit.
      - replace eth with (eth .[p'⇔x]ₑ).
        replace Π with (Π .[p'⇔x]ₚₚ). 2-3: admit. (* neither p' nor x is used anywhere *)
        econstructor. 2: constructor.
        apply renamePID_is_preserved_node_semantics.
        apply renamePID_is_preserved_node_semantics. assumption.
        all: try assumption.
        all: admit.
      - eapply barbedBisim_trans. apply IH. 6: apply IH.
        Guarded.
      admit. (* and additional renaming is needed for the spawned process *)
    }
    {
      exists (renamePIDEther p p' eth', renamePIDPool p p' Π'),
             [(renamePIDAct p p' a, renamePIDPID_sym p p' ι)].
      split. 2: split. 3: split.
      - admit. (* helper needed *)
      - admit. (* helper needed *)
      - econstructor. apply renamePID_is_preserved_node_semantics. exact H4.
        2-3: assumption.
        2: constructor.
        assumption.
      - apply IH.
        + eapply n_trans with (l := []) in H4. 2: constructor.
          by apply ether_wf_preserved in H4.
        + eapply not_isUsedEther_step in H4; eassumption.
        + eapply not_isUsedPool_step in H4; try eassumption.
          unfold isUsedPool in H4. apply not_elem_of_dom. clear -H4.
          apply eq_None_ne_Some_2. intros ??. apply H4. left. intro.
          setoid_rewrite H in H0. congruence.
        + admit. (* helper needed *)
        + eapply not_isUsedPool_step in H4; try eassumption.
    }
    (*
  
  
    admit. (* TODO steps are preserved by renaming *) *)
  * simpl. intros.
    exists (renamePIDPID_sym p p' source), []. eexists.
    exists (map (renamePIDSignal p p') sigsA). split. 2: split. 3: split.
    {
      apply n_refl.
    }
    {
      simpl.
      apply not_elem_of_dom. apply not_elem_of_dom in H5.
      unfold renamePIDPool. apply lookup_kmap_None; auto.
      intros. unfold isUsedPool in H3.
      unfold renamePIDPID_sym in H7. repeat case_match; eqb_to_eq; subst.
      * exfalso. apply H0. do 2 eexists. eassumption.
      * by apply not_elem_of_dom in H5.
      * rewrite lookup_fmap. by setoid_rewrite H5.
    }
    {
      simpl. replace dest with (renamePIDPID_sym p p' dest).
      2: {
        unfold renamePIDPID_sym. repeat case_match; eqb_to_eq; try reflexivity; subst.
        * congruence.
        * assert (forall ι l, eth !! (ι, p') <> Some l) by (clear-H0; firstorder).
          by apply H8 in H6.
      }
      replace (_,_) with (prod_map (renamePIDPID_sym p p') (renamePIDPID_sym p p') (source,dest)) by reflexivity.
      unfold renamePIDEther. setoid_rewrite lookup_kmap; auto.
      rewrite lookup_fmap. setoid_rewrite H6. reflexivity.
    }
    {
      eapply forall_biforall with (d1 := SUnlink) (d2 := SUnlink).
      1: by rewrite map_length.
      intros. rewrite map_nth with (d:= SUnlink).
      by apply Signal_eq_renamePID.
    }
  * admit.
  *
Qed.

Lemma bisim_congr :
  forall U Π Π' eth eth', (eth, Π) ~ (eth', Π') using U ->
    forall Π2, (eth, Π ∪ Π2) ~ (eth', Π' ∪ Π2) using U.
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
    apply step_in_comp in H as H'. destruct H' as [[Π1' [? ?]] | [Π2' [? ?]]].
    - subst. apply H3 in H4 as H4'. destruct_hyps. destruct x as [e' Π1''].
      (* (* At this point, we need renamings :( - or to know what PIDs are
         spawned by Π *)
      Print reductionPreCompatibility.
      (* spawns in x0 should be distinct from:
         - syntactically used PIDs in Π2 - for goal 3
         - ι0 -> if a = send(ι, ι0 <- destination, msg)
         - We also need a proof that (eth, Π) ~ (eth[x|->y], Π[x|->y])
      *)
      exists (e', Π1'' ∪ Π2), x0. split. 2: split. 3: split.
      4: { apply IH. assumption. }
      3: apply reductions_are_preserved_by_comp; auto.
      3: {
        intros. destruct H6 as [H6 _]. rewrite Forall_forall in H6.
        apply H6 in H9. unfold isUntaken in H9. simpl in *.
      } *)
      admit.
    - subst. exists (e, Π' ∪ Π2'), [(a, ι)]. split_and!.
      + split.
        ** destruct a; auto. simpl. constructor; auto. intro.
           eapply (no_spawn_unTaken (eth, Π ∪ Π2)). eapply n_trans. eassumption.
           apply n_refl. 2: cbn; left; reflexivity.
           apply isUntaken_comp in H5 as [? ?]. apply H0 in H5.
           apply isUntaken_comp; split; auto.
           (* ι0 should be Untaken wrt. eth *)
           destruct H5, H6. split; simpl in *; auto.
        ** intros; simpl in *; destruct a; auto; simpl in *.
           destruct_or!; auto. split. 2: split; auto.
           subst.
           (* ISSUE: we do not know, whether Π' uses ι0 *)
           (* is it okay to assume, that Π2 does not communicate to 
              PIDs in the domain of Π/Π' -> NO!

              is it okay to assume, that Π2 does not communicate to
              PIDs in ((dom Π ∪ dom Π') \ (dom Π ∩ dom Π')). Probably not.
            *)
           admit.
      + split.
        ** destruct a; auto. simpl. constructor; auto. intro.
           eapply (no_spawn_unTaken (eth, Π ∪ Π2)). eapply n_trans. eassumption.
           apply n_refl. 2: cbn; left; reflexivity.
           apply isUntaken_comp in H5 as [? ?].
           apply isUntaken_comp; split; auto.
        ** intros; simpl in *; destruct a; auto; simpl in *.
           destruct_or!; auto. split. 2: split; auto.
           subst.
           (* ISSUE: we do not know, whether Π uses ι0
              BOTTOMLINE: we should specify where can Π2 send messages?
            *)
           admit.
      + econstructor.
        apply reduction_is_preserved_by_comp_r. (* eassumption. *) admit. admit. admit. admit.
      + admit.
(*     - subst. exists (e, Π ∪ Π2'), [(a, ι)]. split_and!.
      split.
      + destruct a; auto. simpl. constructor; auto. intro.
        eapply (no_spawn_unTaken (eth, Π ∪ Π2)). eapply n_trans. eassumption.
        apply n_refl. 2: cbn; left; reflexivity.
        apply isUntaken_comp in H5 as [? ?]. apply H0 in H5.
        apply isUntaken_comp; split; auto.
        (* ι0 should be Untaken wrt. eth *)
        destruct H5, H6. split; simpl in *; auto.
      + intros; simpl in *; destruct a; auto; simpl in *.
        destruct_or!; auto. split. 2: split; auto.
        subst.
        (* ISSUE: we do not know, whether Π' uses ι0 *)
        admit.
      4: { apply IH. apply barbedBisim_refl. } *)
Abort.
















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
Abort.

(* Theorem normalisation :
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
  * intros. Print reductionPreCompatibility. Print Action. *)
    
  
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
(*   * intros. exists B', (l ++ [(a, ι)]).
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
 *)

