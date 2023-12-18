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
    - repeat processpool_destruct; try congruence.
    - now apply isUsedEther_etherAdd.
    - repeat processpool_destruct; try congruence.
    - eapply isUsedEther_etherPop in H0; eauto. destruct H0.
      + assumption.
      + subst. now setoid_rewrite lookup_insert in H.
    - repeat processpool_destruct; try congruence.
    - clear H4 H0. repeat processpool_destruct; try congruence.
Qed.

(* BarbedBisim.v *)
Lemma reduction_produces_preCompatibleNodes_sym :
  forall n1 n2 l, n1 -[l]ₙ->* n2 ->
    (forall ι, In ι (PIDsOf sendPIDOf l) ->
      n2.2 !! ι <> None) ->
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
    - repeat processpool_destruct; try congruence.
    - eapply isUsedEther_etherAdd_rev in H3.
      processpool_destruct. congruence.
      destruct (Nat.eq_dec ι' ι0). 2: assumption. subst.
      specialize (H0 ι0 ltac:(now left)).
      apply isUsedEther_no_spawn with (ι := ι0) in H1 as H1'. 2: assumption.
      eapply no_spawn_included in H1'. 2: eassumption.
      simpl in H1'. destruct H1' as [H1' _].
      repeat processpool_destruct; try congruence.
      setoid_rewrite lookup_insert_ne in H1'. 2: assumption.
      apply H1' in H. congruence.
    - repeat processpool_destruct; try congruence.
    - eapply isUsedEther_etherPop_rev in H2; eauto.
    - repeat processpool_destruct; try congruence.
    - repeat processpool_destruct; try congruence.
Qed.

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

Definition renamePIDSignal (p p' : PID) (s : Signal) : Signal :=
match s with
 | SMessage e => SMessage (renamePIDVal p p' e)
 | SExit r b => SExit (renamePIDVal p p' r) b
 | SLink => s
 | SUnlink => s
end.

Definition renamePIDPID (p p' : PID) := fun s => if s =? p
                                                 then p'
                                                 else if s =? p'
                                                      (* This part is needed
                                                         for Inj eq eq *)
                                                      then p
                                                      else s.

Instance renamePIDPID_Inj p p' : Inj eq eq (renamePIDPID p p').
Proof.
  unfold Inj. intros. unfold renamePIDPID in H.
  repeat case_match; eqb_to_eq; subst; auto; try congruence.
Defined.

Hint Resolve renamePIDPID_Inj : core.
Hint Resolve prod_map_inj : core.
Hint Resolve id_inj : core.

Definition renamePIDEther (p p' : PID) (eth : Ether) : Ether :=
  kmap (prod_map (renamePIDPID p p') (renamePIDPID p p'))
    ((map (renamePIDSignal p p')) <$> eth).

Check ( <[(1,1) := [SMessage (VPid 0)]]>empty) : Ether.
Compute (( <[(1,1) := [SMessage (VPid 0)]]>empty) : Ether) !! (1,1).
Compute (( <[(2,1) := [SMessage (VPid 1)]]>(<[(1,1) := [SMessage (VPid 2)]]>empty)) : Ether) !! (1,1).
Compute ( renamePIDEther 1 3 (( <[(2,1) := [SMessage (VPid 1)]]>(<[(1,1) := [SMessage (VPid 2)]]>empty)) : Ether))!! (3,3).

Definition renamePIDProc (p p' : PID) (pr : Process) : Process :=
match pr with
| inl (fs, r, (mb1, mb2), links, flag) =>
  inl (renamePIDStack p p' fs, renamePIDRed p p' r,
       (map (renamePIDVal p p') mb1, map (renamePIDVal p p') mb2),
       map (renamePIDPID p p') links, flag)
| inr dpr => inr (map (fun '(d, v) => (renamePIDPID p p' d, renamePIDVal p p' v)) dpr)
end.

Definition renamePIDPool (p p' : PID) (Π : ProcessPool) : ProcessPool :=
  kmap (renamePIDPID p p') (renamePIDProc p p' <$> Π).

Lemma isUsedEther_rename_same_new :
  forall p p' eth, isUsedEther p eth <-> isUsedEther p' (renamePIDEther p p' eth).
Proof.
  intros. split; intros.
  * unfold renamePIDEther, isUsedEther.
    destruct H as [ιs [H1 H2]].
    exists (renamePIDPID p p' ιs). split.
    - intro. apply lookup_kmap_Some in H; auto. destruct H as [? [? ?]].
      destruct x. inv H.
      assert (ιs = n) by apply (renamePIDPID_Inj _ _ _ _ H4). subst.
      unfold renamePIDPID in H5.
      repeat case_match; eqb_to_eq; subst.
      + rewrite lookup_fmap in H0. destruct (eth !! (n, p)) eqn:P; auto.
        setoid_rewrite P in H0. cbn in H0. inv H0. apply map_eq_nil in H3. now subst.
      + rewrite lookup_fmap in H0. destruct (eth !! (n, p)) eqn:P; auto.
      + congruence.
    - intro.
      eapply lookup_kmap_None with (i := (ιs, p) ) in H; auto.
      2: cbn; f_equal; unfold renamePIDPID; now rewrite Nat.eqb_refl.
      rewrite lookup_fmap in H. destruct (eth !! (ιs, p)) eqn:P.
      + setoid_rewrite P in H. cbn in H. congruence.
      + congruence.
  * unfold renamePIDEther, isUsedEther.
    destruct H as [ιs [H1 H2]].
    assert (exists x l, renamePIDEther p p' eth !! (ιs, p') = Some (x::l)). {
      apply not_eq_None_Some in H2. destruct H2. destruct x; try congruence.
      do 2 eexists. eassumption.
    }
    clear H1 H2. destruct H as [x [l ?]].
    apply lookup_kmap_Some in H. 2: auto. destruct H as [[n n0] [H1 H2]].
    simpl in *. inv H1. rewrite lookup_fmap in H2.
    destruct (eth !! (n, n0)) eqn:P; setoid_rewrite P in H2; cbn in H2; inv H2.
    destruct l0; inv H0.
    unfold renamePIDPID in H3. repeat case_match; eqb_to_eq; subst.
    - exists n; setoid_rewrite P; split; congruence.
    - exists n; setoid_rewrite P; split; congruence.
    - congruence.
Qed.

Lemma isUsedEther_rename_same_old :
  forall p p' eth, isUsedEther p' eth <-> isUsedEther p (renamePIDEther p p' eth).
Proof.
  intros. split; intros.
  * unfold renamePIDEther, isUsedEther.
    destruct H as [ιs [H1 H2]].
    exists (renamePIDPID p p' ιs). split.
    - intro. apply lookup_kmap_Some in H; auto. destruct H as [? [? ?]].
      destruct x. inv H.
      assert (ιs = n) by apply (renamePIDPID_Inj _ _ _ _ H4). subst.
      unfold renamePIDPID in H5.
      repeat case_match; eqb_to_eq; subst.
      + rewrite lookup_fmap in H0. destruct (eth !! (n, p')) eqn:P; auto.
        setoid_rewrite P in H0. cbn in H0. inv H0. apply map_eq_nil in H3. now subst.
      + rewrite lookup_fmap in H0. destruct (eth !! (n, p')) eqn:P; auto.
        setoid_rewrite P in H0. cbn in H0. destruct l; inv H0. apply H1.
        assumption.
      + congruence.
    - intro. destruct (decide (p = p')).
      {
        subst. assert (renamePIDPID p' p' = id). {
             extensionality x. unfold renamePIDPID. cbn.
             case_match; eqb_to_eq; now subst.
          }
        rewrite H0 in *. cbn in *.
        eapply lookup_kmap_None with (i := (ιs, p') ) in H; auto.
        rewrite lookup_fmap in H. destruct (eth !! (ιs, p')) eqn:P;
          setoid_rewrite P in H; simpl in *; congruence.
      }
      {
        eapply lookup_kmap_None with (i := (ιs, p') ) in H; auto.
        2: cbn; f_equal; unfold renamePIDPID; rewrite Nat.eqb_refl.
        2: apply Nat.eqb_neq in n; now rewrite Nat.eqb_sym, n.
        rewrite lookup_fmap in H. destruct (eth !! (ιs, p')) eqn:P.
        + setoid_rewrite P in H. cbn in H. congruence.
        + congruence.
      }
  * unfold renamePIDEther, isUsedEther.
    destruct H as [ιs [H1 H2]].
    assert (exists x l, renamePIDEther p p' eth !! (ιs, p) = Some (x::l)). {
      apply not_eq_None_Some in H2. destruct H2. destruct x; try congruence.
      do 2 eexists. eassumption.
    }
    clear H1 H2. destruct H as [x [l ?]].
    apply lookup_kmap_Some in H. 2: auto. destruct H as [[n n0] [H1 H2]].
    simpl in *. inv H1. rewrite lookup_fmap in H2.
    destruct (eth !! (n, n0)) eqn:P; setoid_rewrite P in H2; cbn in H2; inv H2.
    destruct l0; inv H0.
    unfold renamePIDPID in H3. repeat case_match; eqb_to_eq; subst.
    - exists n; setoid_rewrite P; split; congruence.
    - exists n; setoid_rewrite P; split; congruence.
    - congruence.
Qed.

Lemma rename_bisim :
  forall eth Π p p',
    ether_wf eth ->
    ¬isUsedEther p' eth ->
    p' ∉ dom Π ->
    ¬isUsedPool p' Π ->
    (eth, Π) ~ (renamePIDEther p p' eth, renamePIDPool p p' Π) using [].
Proof.
  cofix IH.
  intros. constructor; auto.
  * split.
    - split; simpl.
      + apply lookup_kmap_None; auto. intros.
        unfold renamePIDPID in H4. repeat case_match; eqb_to_eq; subst.
        ** destruct H3. simpl in *. congruence.
        ** rewrite lookup_fmap. apply not_elem_of_dom in H1. now setoid_rewrite H1.
        ** rewrite lookup_fmap. destruct H3. simpl in *. now setoid_rewrite H3.
      + admit.
    - split; simpl.
      + destruct H3. simpl in *.
        destruct (decide (ι = p')). 2: destruct (decide (ι = p)).
        ** apply not_elem_of_dom. now subst.
        ** subst. apply lookup_kmap_None with (i := p') in H3; auto.
           2: { unfold renamePIDPID. rewrite Nat.eqb_refl.
                apply Nat.eqb_neq in n. rewrite Nat.eqb_sym in n. now rewrite n.
              }
           rewrite lookup_fmap in H3. destruct (Π !! p') eqn:P.
           -- apply not_elem_of_dom in H1. setoid_rewrite H1 in P. congruence.
           -- now pose proof (proj2 (isUsedEther_rename_same_old p p' eth) H4).
        ** subst. apply lookup_kmap_None with (i := ι) in H3; auto.
           2: {
                unfold renamePIDPID.
                apply Nat.eqb_neq in n, n0. now rewrite n, n0.
           }
           rewrite lookup_fmap in H3. destruct (Π !! ι) eqn:P;auto.
           now setoid_rewrite P in H3.
      + admit.
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

