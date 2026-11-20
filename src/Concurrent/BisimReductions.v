(**
  This file proves that certain reductions and modifications of nodes result
  in bisimilar nodes:
  - τ and `self` steps, and their sequences (`silent_steps_bisim`);
  - adding a terminated process without links (`terminated_process_bisim`);
  - updating the signals in transit between dead processes
    (`ether_update_terminated`);
  - adding an empty list of signals to the ether
    (`ether_empty_update_bisim`);
  - adding a finished process, which is not targeted by signals
    (`almost_terminated_bisim`).
  The last four theorems are proved without `cofix`, as instances of
  bisimulation up to fresh renaming (`bisim_up_to_renaming(_opt)`): it
  suffices to give a relation of nodes (`DeadExt`, `EthUpd`, `EthEmpty`,
  `AlmostExt`), and check that single steps and the barbs are preserved by
  it.
*)

From CoreErlang.Concurrent Require Export BisimUpToRenaming.

Import ListNotations.
Import Notations.

(** A step of a node does not associate observed PIDs with processes. *)
Theorem difference_O :
  forall O n n' a ι,
    dom n.2 ## O ->
    n -[a | ι]ₙ-> n' with O ->
    dom n'.2 ## O.
Proof.
  intros. inv H0; simpl in *; setoid_rewrite dom_insert_L; setoid_rewrite dom_insert_L in H.
  1-3: set_solver.
  setoid_rewrite dom_insert_L. set_solver.
Qed.

(** * Silent steps *)

(** A τ step results in a bisimilar node (the result is even expanded by the
    original node). *)
Theorem normalisation_τ_bisim :
  forall O (n n' : Node) ι,
    n -[τ | ι]ₙ-> n' with O ->
    n ~ᵇ n' observing O.
Proof.
  intros. apply barbedExpansion_implies_bisim.
  generalize dependent n. generalize dependent n'. revert ι. cofix IH. intros.
  constructor; auto.
  * intros.
    rename n into A, A' into B, n' into C.
    destruct (decide (ι = ι0)).
    {
      subst. eapply internal_det in H0 as H0'. 2: exact H.
      destruct H0'; destruct_hyps.
      * subst. exists C, []. split_and!.
        - slia.
        - constructor.
        - apply barbedExpansion_refl.
      * subst. destruct H3.
        { (* confluence *)
          do 2 eexists. split_and!.
          2: {
            eapply n_trans. exact H2. apply n_refl.
          }
          slia.
          eapply IH. exact H1.
        }
        { (* termination *)
          subst. exists x1. eexists.
          split_and!.
          2: {
            eapply n_trans. exact H2. apply n_refl.
          }
          slia.
          apply barbedExpansion_refl.
        }
    }
    { (* ι ≠ ι0 *)
      epose proof confluence _ _ _ _ _ H _ _ _ _ H0 n.
      Unshelve. 2: by simpl.
      destruct_hyps.
      exists x, [(a, ι0)]. split_and!.
      - slia.
      - econstructor. eassumption. constructor.
      - eapply IH. exact H2.
    }
  * clear IH. intros. exists source.
    eapply n_trans in H as HD. 2: eapply n_refl.
    inv HD. inv H6. inv H7. apply option_biforall_refl. intros. apply Signal_eq_refl.
  * clear IH. intros. exists B', [(τ, ι); (a, ι0)].
    split. 2: split. all: simpl.
    - slia.
    - econstructor. eassumption. econstructor. eassumption. constructor.
    - apply barbedExpansion_refl.
  * clear IH. intros. exists source, [(τ, ι)], n'. split; auto.
    econstructor. eassumption. constructor.
    apply option_biforall_refl. intros. by apply Signal_eq_refl.
Qed.

(** A sequence of τ steps results in a bisimilar node. *)
Theorem normalisation_τ_many_bisim :
  forall l O (n n' : Node),
    Forall (fun x => x.1 = τ) l ->
    n -[l]ₙ->* n' with O ->
    n ~ᵇ n' observing O.
Proof.
  induction l; intros.
  * inv H0. apply barbedBisim_refl.
  * inv H0. inv H. simpl in *. subst.
    eapply barbedBisim_trans.
    eapply normalisation_τ_bisim; eauto.
    apply IHl; try assumption.
Qed.

(** * Terminated processes *)

(** Terminated processes without links cannot take steps. *)
Lemma no_step_dead_empty :
  forall a p', ¬ (inr ∅ -⌈a⌉-> p').
Proof.
  intros a p' H. inv H.
Qed.

(** If two pools with an insertion at the same PID are equal, then the
    inserted processes are equal. *)
Lemma pool_insert_same :
  forall (Π Π' : ProcessPool) ι p p', ι ↦ p ∥ Π = ι ↦ p' ∥ Π' -> p = p'.
Proof.
  intros Π Π' ι p p' H.
  put (lookup ι : ProcessPool -> _) on H as HL.
  setoid_rewrite lookup_insert_eq in HL. by inv HL.
Qed.

(** If two pools with insertions at different PIDs are equal, the process
    inserted at `ι0` is in the other pool, and the equality is preserved by
    replacing this process. *)
Lemma pool_insert_split :
  forall (Π prs : ProcessPool) ι ι0 q x, ι0 ≠ ι ->
    ι0 ↦ q ∥ prs = ι ↦ x ∥ Π ->
    Π !! ι0 = Some q /\ (forall q', ι0 ↦ q' ∥ prs = ι ↦ x ∥ ι0 ↦ q' ∥ Π).
Proof.
  intros Π prs ι ι0 q x Hneq H. split.
  * put (lookup ι0 : ProcessPool -> _) on H as HL.
    setoid_rewrite lookup_insert_eq in HL.
    setoid_rewrite lookup_insert_ne in HL; [|congruence]. by symmetry.
  * intros q'. transitivity (ι0 ↦ q' ∥ ι0 ↦ q ∥ prs).
    1: by setoid_rewrite insert_insert_eq.
    setoid_rewrite H.
    setoid_rewrite (insert_insert_ne _ ι0 ι); [|congruence]. reflexivity.
Qed.

(** `B` is `A` extended with a terminated process without links at `ι`. *)
Definition DeadExt (ι : PID) (A B : Node) : Prop :=
  A.2 !! ι = None /\ B = (A.1, ι ↦ inr ∅ ∥ A.2).

(** Steps of a node are matched by the node extended with a terminated
    process without links. *)
Lemma DeadExt_StepSim :
  forall O ι, StepSim O (DeadExt ι).
Proof.
  intros O ι [eth Π] B [eth' Π'] a ι0 [Hι HB] D Hfresh. subst B. simpl in *.
  assert (ι0 ≠ ι) as Hneq.
  { intro. subst. inv D; setoid_rewrite lookup_insert_eq in Hι; congruence. }
  inv D; simpl in *.
  all: setoid_rewrite lookup_insert_ne in Hι; [|congruence].
  all: setoid_rewrite (insert_insert_ne _ ι ι0); [|congruence].
  * eexists. split. 1: by apply n_send.
    split; simpl.
    - setoid_rewrite lookup_insert_ne; [|congruence]. assumption.
    - f_equal. setoid_rewrite (insert_insert_ne _ ι ι0); [|congruence]. reflexivity.
  * eexists. split. 1: by eapply n_arrive.
    split; simpl.
    - setoid_rewrite lookup_insert_ne; [|congruence]. assumption.
    - f_equal. setoid_rewrite (insert_insert_ne _ ι ι0); [|congruence]. reflexivity.
  * eexists. split. 1: by eapply n_other.
    split; simpl.
    - setoid_rewrite lookup_insert_ne; [|congruence]. assumption.
    - f_equal. setoid_rewrite (insert_insert_ne _ ι ι0); [|congruence]. reflexivity.
  * destruct (Hfresh ι' eq_refl) as [Hu Ha].
    setoid_rewrite (insert_insert_ne _ ι ι0) in Hu; [|congruence].
    assert (ι' ≠ ι) as Hι'. {
      intro. subst. apply Hu. left.
      setoid_rewrite lookup_insert_ne; [|congruence].
      by setoid_rewrite lookup_insert_eq.
    }
    eexists. split. 1: by eapply n_spawn.
    split; simpl.
    - setoid_rewrite lookup_insert_ne; [|congruence].
      setoid_rewrite lookup_insert_ne; [|congruence]. assumption.
    - f_equal. setoid_rewrite (insert_insert_ne _ ι0 ι); [|congruence].
      setoid_rewrite (insert_insert_ne _ ι' ι); [|congruence]. reflexivity.
Qed.

(** Steps of a node extended with a terminated process without links are
    matched by the original node. *)
Lemma DeadExt_StepSim_rev :
  forall O ι, StepSim O (fun B A => DeadExt ι A B).
Proof.
  intros O ι B [eth Π] B' a ι0 [Hι HB] D Hfresh. subst B. simpl in *.
  remember (ι ↦ inr ∅ ∥ Π) as BΠ eqn:HBΠ.
  revert HBΠ. inv D; intro HBΠ.
  all: destruct (decide (ι0 = ι)) as [Heq | Hneq];
    [subst; apply pool_insert_same in HBΠ; subst; exfalso;
     eapply no_step_dead_empty; eassumption|].
  all: destruct (pool_insert_split _ _ _ _ _ _ Hneq HBΠ) as [HΠ Hprs].
  all: pose proof (insert_id Π ι0 _ HΠ) as HidΠ.
  all: rewrite <- HidΠ.
  * eexists. split. 1: by apply n_send.
    split; simpl.
    - setoid_rewrite lookup_insert_ne; [|congruence]. assumption.
    - by rewrite Hprs.
  * eexists. split. 1: by eapply n_arrive.
    split; simpl.
    - setoid_rewrite lookup_insert_ne; [|congruence]. assumption.
    - by rewrite Hprs.
  * eexists. split. 1: by eapply n_other.
    split; simpl.
    - setoid_rewrite lookup_insert_ne; [|congruence]. assumption.
    - by rewrite Hprs.
  * destruct (Hfresh ι' eq_refl) as [Hu Ha].
    assert (ι' ≠ ι) as Hι'. {
      intro. subst.
      assert (isUsedPool ι (ι0 ↦ p ∥ Π0)) as Hc. {
        setoid_rewrite HBΠ. left. by setoid_rewrite lookup_insert_eq.
      }
      contradiction.
    }
    eexists. split.
    1: { eapply n_spawn; try eassumption. by setoid_rewrite HidΠ. }
    split; simpl.
    - setoid_rewrite lookup_insert_ne; [|congruence].
      setoid_rewrite lookup_insert_ne; [|congruence]. assumption.
    - f_equal. rewrite Hprs.
      setoid_rewrite (insert_insert_ne _ ι' ι); [|congruence]. reflexivity.
Qed.

(** `DeadExt` preserves the signals in transit. *)
Lemma DeadExt_BarbSim :
  forall O ι, BarbSim O (DeadExt ι).
Proof.
  intros O ι A B [_ ->] s d _. exists s. simpl.
  apply option_biforall_refl. intros. apply Signal_eq_refl.
Qed.

(** `DeadExt` preserves the signals in transit (in the other direction). *)
Lemma DeadExt_BarbSim_rev :
  forall O ι, BarbSim O (fun B A => DeadExt ι A B).
Proof.
  intros O ι B A [_ ->] s d _. exists s. simpl.
  apply option_biforall_refl. intros. apply Signal_eq_refl.
Qed.

(** Adding a terminated process without links to the pool with an unobserved
    PID not associated with a process results in a bisimilar node. *)
Theorem terminated_process_bisim :
  forall O A ι,
    (ι ∉ O) ->
    (ι ∉ dom A.2) ->
    A ~ᵇ (A.1, ι ↦ inr ∅ ∥ A.2) observing O.
Proof.
  intros O A ι _ Hdom.
  apply (bisim_up_to_renaming O (DeadExt ι)).
  1: apply DeadExt_StepSim.
  1: apply DeadExt_StepSim_rev.
  1: apply DeadExt_BarbSim.
  1: apply DeadExt_BarbSim_rev.
  split. 2: reflexivity.
  by apply not_elem_of_dom.
Qed.

(** * Updating the ether between dead processes *)

(** `optional_send a ιs ιd` is the singleton list of the signal sent by `a`,
    if `a` sends from `ιs` to `ιd`; otherwise, it is the empty list. *)
Definition optional_send (a : Action) (ιs ιd : PID) : list Signal :=
match a with
| ASend from to t => match (decide ((ιs, ιd) = (from, to))) with
                     | left _  => [t]
                     | right _ => []
                     end
| _ => []
end.

(** `optional_send_deleted a ιs ιd e` sets the signals in transit from `ιs` to
    `ιd` in `e` to the signal sent by `a`, if `a` sends from `ιs` to `ιd`;
    otherwise, it is `e`. *)
Definition optional_send_deleted (a : Action) (ιs ιd : PID) (e : Ether) : Ether :=
match a with
| ASend from to t => match (decide ((ιs, ιd) = (from, to))) with
                     | left _  => <[(ιs,ιd):=[t]]>e
                     | right _ => e
                     end
| _ => e
end.

(** If `ιs` and `ιd` are dead processes, then a step is preserved by setting
    the signals in transit from `ιs` to `ιd` to any list `l` (the signal
    sent by the step from `ιs` to `ιd` is appended to `l`), or by removing
    them (the signal sent by the step becomes the only one in transit),
    provided that the spawned PID (if any) does not appear in `l`. *)
Lemma ether_update_reduction :
  forall O Aeth AΠ Beth BΠ ιs ιd l a ι links links',
    AΠ !! ιd = Some (inr links) ->
    AΠ !! ιs = Some (inr links') ->
    (Aeth, AΠ) -[a | ι]ₙ-> (Beth, BΠ) with O ->
    (forall ιspawn, Some ιspawn = spawnPIDOf a -> (ιspawn ∉ flat_union usedPIDsSignal l)) ->
    (<[(ιs, ιd):=l]> Aeth, AΠ) -[ a | ι ]ₙ-> (<[(ιs, ιd):=l ++ optional_send a ιs ιd]>Beth, BΠ) with O /\
    (delete (ιs, ιd) Aeth, AΠ) -[ a | ι ]ₙ-> (optional_send_deleted a ιs ιd (delete (ιs, ιd) Beth), BΠ) with O.
Proof.
  intros * Hdead Hdead2 HD Hspawn. inv HD.
  * assert (<[(ιs, ιd):=l ++ optional_send (ASend ι ι' t) ιs ιd]> (etherAdd ι ι' t Aeth) = etherAdd ι ι' t (<[(ιs, ιd):=l]>Aeth) /\
            optional_send_deleted (ASend ι ι' t) ιs ιd (etherAdd ι ι' t Aeth -- (ιs, ιd)) =
            etherAdd ι ι' t (delete (ιs, ιd) Aeth)). {
    unfold etherAdd. simpl.
    destruct (decide ((ιs, ιd) = (ι, ι'))).
    * inv e. setoid_rewrite lookup_insert. destruct_decide_eq. case_match.
      all: setoid_rewrite insert_insert; destruct_decide_eq; split; f_equal.
      all: setoid_rewrite lookup_delete; destruct_decide_eq.
      all: setoid_rewrite delete_insert_eq.
      all: by setoid_rewrite insert_delete_eq.
    * setoid_rewrite lookup_insert_ne; auto.
      setoid_rewrite lookup_delete_ne; auto.
      case_match.
      ** setoid_rewrite H.
         setoid_rewrite insert_insert at 1; auto. destruct_decide_eq.
         rewrite app_nil_r.
         setoid_rewrite delete_insert_ne; by auto.
      ** setoid_rewrite H. setoid_rewrite insert_insert at 1; auto. destruct_decide_eq.
         setoid_rewrite delete_insert_ne; auto.
         by rewrite app_nil_r.
    }
    destruct H as [Hf Hs]. setoid_rewrite Hf. setoid_rewrite Hs.
    split; apply n_send; exact H3.
  * unfold etherPop in H4. repeat case_match; try congruence.
    inv H4.
    assert (ιd <> ι). {
      intro. subst. setoid_rewrite lookup_insert in Hdead. destruct_decide_eq. inv Hdead.
      inv H6.
    }
    split.
    - apply n_arrive with (ι0 := ι1).
      unfold etherPop.
      setoid_rewrite lookup_insert_ne. 2: intro X; inv X; lia.
      setoid_rewrite H. simpl. rewrite app_nil_r.
      setoid_rewrite insert_insert at 1. destruct_decide_eq. reflexivity.
      assumption.
    - apply n_arrive with (ι0 := ι1).
      unfold etherPop.
      setoid_rewrite lookup_delete_ne. 2: intro X; inv X; lia.
      setoid_rewrite H. simpl.
      setoid_rewrite delete_insert_ne at 1. reflexivity.
      intro X; inv X; lia.
      assumption.
  * assert (ιd <> ι). {
      intro. subst. setoid_rewrite lookup_insert in Hdead. destruct_decide_eq.
      inv Hdead. inv H4.
      destruct_or! H6; congruence.
    }
    destruct_or! H6; subst; simpl; rewrite app_nil_r.
    all: split; apply n_other; try assumption.
    all: set_solver.
  * assert (ιd <> ι). {
      intro. subst. setoid_rewrite lookup_insert in Hdead. destruct_decide_eq.
      inv Hdead. inv H10.
    }
    (* tricky, spawnPID freshness assumption is probably needed *)
    simpl. rewrite app_nil_r.
    split.
    - eapply n_spawn; try eassumption.
      {
        specialize (Hspawn _ eq_refl).
        intro. apply H8. destruct H0. 2: destruct H0.
        * destruct H0, H0.
          destruct (decide ((x, ι') = (ιs, ιd))).
          - inv e. setoid_rewrite lookup_insert in H0. inv H0.
            exfalso. apply H5. left.
            setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in Hdead; auto.
            by setoid_rewrite Hdead.
          - setoid_rewrite lookup_insert_ne in H0; auto.
            left. by exists x, x0.
        * destruct_hyps.
          destruct (decide ((ι', x) = (ιs, ιd))).
          - inv e.
            exfalso. apply H5. left.
            assert (ιs <> ι). {
              intro. subst. apply H5. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
            }
            setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in Hdead2; auto.
            by setoid_rewrite Hdead2.
          - setoid_rewrite lookup_insert_ne in H0; auto.
            right. left. by exists x.
        * destruct_hyps.
          destruct (decide ((x, x0) = (ιs, ιd))).
          - inv e. setoid_rewrite lookup_insert in H0. destruct_decide_eq.
          - setoid_rewrite lookup_insert_ne in H0; auto.
            right. right. do 3 eexists. split; eassumption.
      }
    - eapply n_spawn; try eassumption.
      {
        specialize (Hspawn _ eq_refl).
        intro. apply H8. destruct H0. 2: destruct H0.
        * destruct H0, H0.
          destruct (decide ((x, ι') = (ιs, ιd))).
          - inv e. setoid_rewrite lookup_delete in H0. destruct_decide_eq.
          - setoid_rewrite lookup_delete_ne in H0; auto.
            left. by exists x, x0.
        * destruct_hyps.
          destruct (decide ((ι', x) = (ιs, ιd))).
          - inv e.
            exfalso. apply H5. left.
            assert (ιs <> ι). {
              intro. subst. apply H5. left. by setoid_rewrite lookup_insert; destruct_decide_eq.
            }
            setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in Hdead2; auto.
            by setoid_rewrite Hdead2.
          - setoid_rewrite lookup_delete_ne in H0; auto.
            right. left. by exists x.
        * destruct_hyps.
          destruct (decide ((x, x0) = (ιs, ιd))).
          - inv e. setoid_rewrite lookup_delete in H0. destruct_decide_eq.
          - setoid_rewrite lookup_delete_ne in H0; auto.
            right. right. do 3 eexists. split; eassumption.
      }
Qed.

(** `general_insert ιs ιd l e` sets the signals in transit from `ιs` to `ιd`
    in `e` to `l`, or removes them if `l` is `None`. *)
Definition general_insert (ιs ιd : PID) (l : option (list Signal)) (e : Ether)  : Ether :=
match l with
| None => e -- (ιs, ιd)
| Some l' => <[(ιs, ιd) := l']>e
end.

(** The signals in transit from `s` to `d` after adding a signal. *)
Lemma lookup_etherAdd_eq :
  forall s d m (E : Ether),
    etherAdd s d m E !! (s, d) = Some (default [] (E !! (s, d)) ++ [m]).
Proof.
  intros. unfold etherAdd. destruct (E !! (s, d)); by setoid_rewrite lookup_insert_eq.
Qed.

(** Adding a signal does not change the signals in transit between other
    PIDs. *)
Lemma lookup_etherAdd_ne :
  forall s d m (E : Ether) k, k ≠ (s, d) -> etherAdd s d m E !! k = E !! k.
Proof.
  intros s d m E k Hk. unfold etherAdd.
  destruct (E !! (s, d)); apply lookup_insert_ne; congruence.
Qed.

(** `offKey k0 E1 E2`: the ethers `E1` and `E2` agree, except possibly at the
    key `k0`. *)
Definition offKey (k0 : PID * PID) (E1 E2 : Ether) : Prop :=
  forall k, k ≠ k0 -> E1 !! k = E2 !! k.

(** `offKey` is symmetric. *)
Lemma offKey_sym :
  forall k0 E1 E2, offKey k0 E1 E2 -> offKey k0 E2 E1.
Proof.
  intros k0 E1 E2 H k Hk. symmetry. by apply H.
Qed.

(** Adding the same signal to ethers preserves `offKey`. *)
Lemma offKey_etherAdd :
  forall k0 E1 E2, offKey k0 E1 E2 ->
    forall s d m, offKey k0 (etherAdd s d m E1) (etherAdd s d m E2).
Proof.
  intros k0 E1 E2 H s d m k Hk.
  destruct (decide (k = (s, d))) as [-> | Hne].
  * rewrite !lookup_etherAdd_eq. by rewrite (H _ Hk).
  * rewrite !lookup_etherAdd_ne; try assumption. by apply H.
Qed.

(** Popping a signal from an entry other than `k0` preserves `offKey`, and
    does not change the entry `k0`. *)
Lemma offKey_etherPop :
  forall k0 E1 E2 E1' s d t, offKey k0 E1 E2 -> (s, d) ≠ k0 ->
    etherPop s d E1 = Some (t, E1') ->
    exists E2', etherPop s d E2 = Some (t, E2') /\ offKey k0 E1' E2' /\
      E1' !! k0 = E1 !! k0 /\ E2' !! k0 = E2 !! k0.
Proof.
  intros k0 E1 E2 E1' s d t H Hk Hpop. unfold etherPop in *.
  pose proof (H (s, d) Hk) as Hsd. setoid_rewrite <- Hsd.
  destruct (E1 !! (s, d)) as [[|x xs]|]; inv Hpop.
  eexists. split. 1: reflexivity.
  split_and!.
  * intros k Hk'. destruct (decide (k = (s, d))) as [-> | Hne].
    - transitivity (Some xs).
      1: apply lookup_insert_eq.
      symmetry. apply lookup_insert_eq.
    - transitivity (E1 !! k). 1: apply lookup_insert_ne; congruence.
      transitivity (E2 !! k). 1: by apply H.
      symmetry. apply lookup_insert_ne; congruence.
  * apply lookup_insert_ne; congruence.
  * apply lookup_insert_ne; congruence.
Qed.

(** A dead process cannot receive signals. *)
Lemma no_arrive_dead :
  forall d s r t p', ¬ (inr d -⌈AArrive s r t⌉-> p').
Proof.
  intros d s r t p' H. inv H.
Qed.

(** The relation of `ether_update_terminated`: the pools are the same, `ιd`
    is a dead process, and the ethers agree except at `(ιs, ιd)`. *)
Definition EthUpd (ιs ιd : PID) (A B : Node) : Prop :=
  A.2 = B.2 /\ (exists dx, A.2 !! ιd = Some (inr dx)) /\ offKey (ιs, ιd) A.1 B.1.

(** `EthUpd` is symmetric. *)
Lemma EthUpd_sym :
  forall ιs ιd A B, EthUpd ιs ιd A B -> EthUpd ιs ιd B A.
Proof.
  intros ιs ιd A B [H1 [[dx H2] H3]]. split_and!.
  * by symmetry.
  * exists dx. by rewrite <- H1.
  * by apply offKey_sym.
Qed.

(** Steps are preserved by `EthUpd`. *)
Lemma EthUpd_StepSim :
  forall O ιs ιd, StepSim O (EthUpd ιs ιd).
Proof.
  intros O ιs ιd [eth Π] [eth2 Π2] A' a ι0 [HΠ [[dx Hdx] Hoff]] D Hfresh.
  simpl in *. subst Π2.
  pose proof (dead_processes_stay_dead _ _ _ _ _ D _ _ Hdx) as Hdead.
  inv D; simpl in *.
  * eexists. split. 1: by apply n_send.
    split_and!. 1: reflexivity. 1: by eexists.
    by apply offKey_etherAdd.
  * assert ((ι1, ι0) ≠ (ιs, ιd)) as Hk. {
      intro Heq. inv Heq.
      setoid_rewrite lookup_insert_eq in Hdx. inv Hdx.
      eapply no_arrive_dead. eassumption.
    }
    edestruct offKey_etherPop as [E2' [Hpop2 [Hoff' _]]];
      [exact Hoff | exact Hk | eassumption |].
    eexists. split. 1: by eapply n_arrive.
    split_and!. 1: reflexivity. 1: by eexists.
    assumption.
  * eexists. split. 1: by eapply n_other.
    split_and!. 1: reflexivity. 1: by eexists.
    assumption.
  * destruct (Hfresh ι' eq_refl) as [Hu Ha].
    eexists. split. 1: by eapply n_spawn.
    split_and!. 1: reflexivity. 1: by eexists.
    assumption.
Qed.

(** Steps are preserved by `EthUpd` (in the other direction). *)
Lemma EthUpd_StepSim_rev :
  forall O ιs ιd, StepSim O (fun B A => EthUpd ιs ιd A B).
Proof.
  intros O ιs ιd B A B' a ι HR D Hfresh.
  destruct (EthUpd_StepSim O ιs ιd B A B' a ι (EthUpd_sym _ _ _ _ HR) D Hfresh)
    as [A' [HA HR']].
  exists A'. split. 1: assumption.
  by apply EthUpd_sym.
Qed.

(** `EthUpd` preserves the signals in transit to observed PIDs, if `ιd` is
    not observed. *)
Lemma EthUpd_BarbSim :
  forall O ιs ιd, ιd ∉ O -> BarbSim O (EthUpd ιs ιd).
Proof.
  intros O ιs ιd Hd A B [_ [_ Hoff]] s d HdO. exists s.
  rewrite (Hoff (s, d)). 2: { intro Heq. inv Heq. contradiction. }
  apply option_biforall_refl. intros. apply Signal_eq_refl.
Qed.

(** `EthUpd` preserves the signals in transit to observed PIDs (in the other
    direction), if `ιd` is not observed. *)
Lemma EthUpd_BarbSim_rev :
  forall O ιs ιd, ιd ∉ O -> BarbSim O (fun B A => EthUpd ιs ιd A B).
Proof.
  intros O ιs ιd Hd B A HR.
  apply (EthUpd_BarbSim O ιs ιd Hd B A (EthUpd_sym _ _ _ _ HR)).
Qed.

(** Updating (or removing) the signals in transit from a dead process to a
    dead, unobserved process results in a bisimilar node. *)
Theorem ether_update_terminated :
  forall O A ιs ιd l dx,
    A.2 !! ιd = Some (inr dx) ->
    (ιd ∉ O) ->
    A ~ᵇ (general_insert ιs ιd l A.1, A.2) observing O.
Proof.
  intros O A ιs ιd l dx Hdx Hd.
  apply (bisim_up_to_renaming O (EthUpd ιs ιd)).
  1: apply EthUpd_StepSim.
  1: apply EthUpd_StepSim_rev.
  1: by apply EthUpd_BarbSim.
  1: by apply EthUpd_BarbSim_rev.
  split_and!. 1: reflexivity. 1: by exists dx.
  intros k Hk. symmetry. destruct l; simpl.
  * apply lookup_insert_ne. congruence.
  * apply lookup_delete_ne. congruence.
Qed.

(*
  This definition expresses that there are no exits sent with the
  same source and destination with 'normal' reason.
 *)
(* Definition no_self_exits_via_link (e : Ether) :=
  forall ι l, e !! (ι, ι) = Some l ->
    Forall (fun s => forall b, s <> SExit normal b) l.

Theorem normalisation_2 :
  forall O A B ι a,
  (* Sends should not be included in chainability!
     A send can happen before termination that potentially causes difference
     in the two systems (in the other one, this send never happened). *)
    ether_wf A.1 -> (* message sending requires VALCLOSED - needed for dead processes *)
    no_self_exits_via_link A.1 ->
    isChainable2 a ->
    dom A.2 ## O ->
    A -[a |ι]ₙ-> B with O ->
    A ~ᵇ B observing O. *)

(** * Self steps *)

(** A `self` step results in a bisimilar node (the result is even expanded by
    the original node). *)
Theorem normalisation_self_bisim :
  forall O (n n' : Node) ι,
    n -[ASelf ι | ι]ₙ-> n' with O ->
    n ~ᵇ n' observing O.
Proof.
  intros. apply barbedExpansion_implies_bisim.
  generalize dependent n. generalize dependent n'. revert ι. cofix IH. intros.
  constructor; auto.
  * intros.
    rename n into A, A' into B, n' into C.
    destruct (decide (ι = ι0)).
    {
      subst.
      inv H. clear H2. inv H1. simpl in *. inv H0.
      * put (lookup ι0 : ProcessPool -> _) on H2 as D.
        setoid_rewrite lookup_insert in D. destruct_decide_eq. inv D. inv H5.
      * put (lookup ι0 : ProcessPool -> _) on H1 as D.
        setoid_rewrite lookup_insert in D. destruct_decide_eq. inv D. inv H6.
        (* TODO: boiler plate, there is minimal difference in 5 of the
          following 6 cases (the case for terminated exit is different!) *)
        { (* message *)
          do 2 eexists. split_and!. 2: {
            eapply n_trans. apply n_arrive. eassumption.
            constructor. apply n_refl.
          }
          1: slia.
          apply IH with (ι := ι0); clear IH.
          * replace (ι0 ↦ inl (fs, RValSeq [VPid ι0], mailboxPush mb v, links, flag) ∥ Π) with
              (ι0 ↦ inl (fs, RValSeq [VPid ι0], mailboxPush mb v, links, flag) ∥ prs).
            2: {
              apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as D.
              destruct (decide (i = ι0)).
              * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
              * setoid_rewrite lookup_insert_ne in D; auto.
                by setoid_rewrite lookup_insert_ne.
            }
            apply n_other. constructor. set_solver.
        }
        { (* dropped exit *)
          do 2 eexists. split_and!. 2: {
            eapply n_trans. apply n_arrive. eassumption.
            constructor. assumption. apply n_refl.
          }
          1: slia.
          apply IH with (ι := ι0); clear IH.
          * replace (ι0 ↦ inl (fs, RValSeq [VPid ι0], mb, links, flag) ∥ Π) with
              (ι0 ↦ inl (fs, RValSeq [VPid ι0], mb, links, flag) ∥ prs).
            2: {
              apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as D.
              destruct (decide (i = ι0)).
              * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
              * setoid_rewrite lookup_insert_ne in D; auto.
                by setoid_rewrite lookup_insert_ne.
            }
            apply n_other. constructor. set_solver.
        }
        { (* terminated exit *)
          do 2 eexists. split_and!. 2: {
            eapply n_trans. apply n_arrive. eassumption.
            apply p_exit_terminate. eassumption. apply n_refl.
          }
          1: slia.
          replace (ι0 ↦ inr (gset_to_gmap reason' links) ∥ Π) with
              (ι0 ↦ inr (gset_to_gmap reason' links) ∥ prs).
          2: {
            apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as D.
            destruct (decide (i = ι0)).
            * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
            * setoid_rewrite lookup_insert_ne in D; auto.
              by setoid_rewrite lookup_insert_ne.
          }
          apply barbedExpansion_refl.
        }
        { (* converted exit *)
          do 2 eexists. split_and!. 2: {
            eapply n_trans. apply n_arrive. eassumption.
            apply p_exit_convert. assumption. apply n_refl.
          }
          1: slia.
          apply IH with (ι := ι0); clear IH.
          * replace (ι0 ↦ inl (fs, RValSeq [VPid ι0], mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ι1; reason]), links, true) ∥ Π) with
              (ι0 ↦ inl (fs, RValSeq [VPid ι0], mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ι1; reason]), links, true) ∥ prs).
            2: {
              apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as D.
              destruct (decide (i = ι0)).
              * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
              * setoid_rewrite lookup_insert_ne in D; auto.
                by setoid_rewrite lookup_insert_ne.
            }
            apply n_other. constructor. set_solver.
        }
        { (* link *)
          do 2 eexists. split_and!. 2: {
            eapply n_trans. apply n_arrive. eassumption.
            constructor. apply n_refl.
          }
          1: slia.
          apply IH with (ι := ι0); clear IH.
          * replace (ι0 ↦ inl (fs, RValSeq [VPid ι0], mb, {[ι1]} ∪ links, flag) ∥ Π) with
              (ι0 ↦ inl (fs, RValSeq [VPid ι0], mb, {[ι1]} ∪ links, flag) ∥ prs).
            2: {
              apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as D.
              destruct (decide (i = ι0)).
              * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
              * setoid_rewrite lookup_insert_ne in D; auto.
                by setoid_rewrite lookup_insert_ne.
            }
            apply n_other. constructor. set_solver.
        }
        { (* unlink *)
          do 2 eexists. split_and!. 2: {
            eapply n_trans. apply n_arrive. eassumption.
            constructor. apply n_refl.
          }
          1: slia.
          apply IH with (ι := ι0); clear IH.
          * replace (ι0 ↦ inl (fs, RValSeq [VPid ι0], mb, links ∖ {[ι1]}, flag) ∥ Π) with
              (ι0 ↦ inl (fs, RValSeq [VPid ι0], mb, links ∖ {[ι1]}, flag) ∥ prs).
            2: {
              apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as D.
              destruct (decide (i = ι0)).
              * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
              * setoid_rewrite lookup_insert_ne in D; auto.
                by setoid_rewrite lookup_insert_ne.
            }
            apply n_other. constructor. set_solver.
        }
      * put (lookup ι0 : ProcessPool -> _) on H1 as D.
        setoid_rewrite lookup_insert in D. destruct_decide_eq. inv D. destruct_or! H6.
        - subst. inv H2. inv H7.
        - subst. inv H2.
          eexists. exists []. split. slia. split. apply n_refl.
          replace (ι0 ↦ inl (fs, RValSeq [VPid ι0], mb, links, flag) ∥ Π0) with
             (ι0 ↦ inl (fs, RValSeq [VPid ι0], mb, links, flag) ∥ Π).
          2: {
            apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as D.
            destruct (decide (i = ι0)).
            * subst. by setoid_rewrite lookup_insert; destruct_decide_eq.
            * setoid_rewrite lookup_insert_ne in D; auto.
              by setoid_rewrite lookup_insert_ne.
          }
          apply barbedExpansion_refl.
        - subst. inv H2.
      * put (lookup ι0 : ProcessPool -> _) on H1 as D.
        setoid_rewrite lookup_insert in D. destruct_decide_eq. inv D. inv H10.
    }
    { (* ι ≠ ι0 *)
      epose proof confluence _ _ _ _ _ H _ _ _ _ H0 n.
      Unshelve. 2: by simpl.
      destruct_hyps.
      exists x, [(a, ι0)]. split_and!.
      - slia.
      - econstructor. eassumption. constructor.
      - eapply IH. exact H2.
    }
  * clear IH. intros. exists source.
    eapply n_trans in H as HD. 2: eapply n_refl.
    inv HD. inv H6. inv H7.
    apply option_biforall_refl. intros. by apply Signal_eq_refl.
  * clear IH. intros. exists B', [(ASelf ι, ι); (a, ι0)].
    split. 2: split. all: simpl.
    - slia.
    - econstructor. eassumption. econstructor. eassumption. constructor.
    - apply barbedExpansion_refl.
  * clear IH. intros. exists source, [(ASelf ι, ι)], n'. split; auto.
    econstructor. eassumption. constructor.
    apply option_biforall_refl. intros. by apply Signal_eq_refl.
Qed.

(** A sequence of τ and `self` steps results in a bisimilar node. *)
Theorem silent_steps_bisim :
  forall l O (n n' : Node),
    Forall (fun x => x.1 = τ \/ exists ι, x.1 = ASelf ι) l ->
    n -[l]ₙ->* n' with O ->
    n ~ᵇ n' observing O.
Proof.
  induction l; intros.
  * inv H0. apply barbedBisim_refl.
  * inv H0. inv H. simpl in *. destruct H2; subst.
    - eapply barbedBisim_trans.
      eapply normalisation_τ_bisim; eauto.
      apply IHl; try assumption.
    - destruct H. subst. eapply barbedBisim_trans.
      assert (ι = x). {
        inv H4. destruct_or! H0; try congruence.
      }
      subst.
      eapply normalisation_self_bisim; eauto.
      eapply IHl; try eassumption.
Qed.

(** * Empty ether entries *)

(** Popping a signal from the ether removes the first signal in transit
    between the given PIDs. *)
Lemma etherPop_some_inv :
  forall s d (E E' : Ether) t, etherPop s d E = Some (t, E') ->
    exists xs, E !! (s, d) = Some (t :: xs) /\ E' = <[(s, d):=xs]> E.
Proof.
  intros s d E E' t H. unfold etherPop in H.
  destruct (E !! (s, d)) as [[|x xs]|]; inv H. by exists xs.
Qed.

(** An entry of the ether is empty, if it is missing or the empty list. *)
Definition emptyEntry (o : option (list Signal)) : Prop :=
  o = None \/ o = Some [].

(** The signals of an empty entry. *)
Lemma emptyEntry_default :
  forall o, emptyEntry o -> default [] o = [].
Proof.
  intros o [-> | ->]; reflexivity.
Qed.

(** The relation of `ether_empty_update_bisim`: the pools are the same, and
    the ethers agree except at `(ιs, ιd)`, where they are either equal, or
    both empty. *)
Definition EthEmpty (ιs ιd : PID) (A B : Node) : Prop :=
  A.2 = B.2 /\ offKey (ιs, ιd) A.1 B.1 /\
  (A.1 !! (ιs, ιd) = B.1 !! (ιs, ιd) \/
   (emptyEntry (A.1 !! (ιs, ιd)) /\ emptyEntry (B.1 !! (ιs, ιd)))).

(** `EthEmpty` is symmetric. *)
Lemma EthEmpty_sym :
  forall ιs ιd A B, EthEmpty ιs ιd A B -> EthEmpty ιs ιd B A.
Proof.
  intros ιs ιd A B [H1 [H2 [H3 | [H3 H4]]]]; split_and!.
  1,4: by symmetry.
  1,3: by apply offKey_sym.
  * left. by symmetry.
  * right. by split.
Qed.

(** Steps are preserved by `EthEmpty`. *)
Lemma EthEmpty_StepSim :
  forall O ιs ιd, StepSim O (EthEmpty ιs ιd).
Proof.
  intros O ιs ιd [eth Π] [eth2 Π2] A' a ι0 [HΠ [Hoff Hk0]] D Hfresh.
  simpl in *. subst Π2.
  inv D; simpl in *.
  * eexists. split. 1: by apply n_send.
    split_and!. 1: reflexivity. 1: by apply offKey_etherAdd.
    destruct (decide ((ιs, ιd) = (ι0, ι'))) as [Heq | Hne].
    - injection Heq as Heq1 Heq2. subst ιs ιd.
      left. simpl. rewrite !lookup_etherAdd_eq.
      destruct Hk0 as [-> | [H1 H2]]. 1: reflexivity.
      by rewrite (emptyEntry_default _ H1), (emptyEntry_default _ H2).
    - simpl. rewrite !lookup_etherAdd_ne; try assumption.
  * edestruct etherPop_some_inv as [xs [Hxs HE']]; [eassumption|].
    subst ether'.
    destruct (decide ((ι1, ι0) = (ιs, ιd))) as [Heq | Hne].
    - injection Heq as Heq1 Heq2. subst ι1 ι0.
      assert (eth2 !! (ιs, ιd) = Some (t :: xs)) as Hxs2. {
        destruct Hk0 as [Hk0 | [[Hk0 | Hk0] _]].
        1: by rewrite <- Hk0.
        all: rewrite Hxs in Hk0; congruence.
      }
      eexists. split.
      1: { eapply n_arrive. 2: eassumption. unfold etherPop. by rewrite Hxs2. }
      split_and!. 1: reflexivity.
      + intros k Hk.
        transitivity (eth !! k). 1: apply lookup_insert_ne; congruence.
        transitivity (eth2 !! k). 1: by apply Hoff.
        symmetry. apply lookup_insert_ne; congruence.
      + left. transitivity (Some xs). 1: apply lookup_insert_eq.
        symmetry. apply lookup_insert_eq.
    - edestruct offKey_etherPop as [E2' [Hpop2 [Hoff' [HE1 HE2]]]];
        [exact Hoff | exact Hne | eassumption |].
      eexists. split. 1: by eapply n_arrive.
      split_and!. 1: reflexivity. 1: assumption.
      simpl. by rewrite HE1, HE2.
  * eexists. split. 1: by eapply n_other.
    split_and!; try reflexivity; assumption.
  * destruct (Hfresh ι' eq_refl) as [Hu Ha].
    eexists. split. 1: by eapply n_spawn.
    split_and!; try reflexivity; assumption.
Qed.

(** Steps are preserved by `EthEmpty` (in the other direction). *)
Lemma EthEmpty_StepSim_rev :
  forall O ιs ιd, StepSim O (fun B A => EthEmpty ιs ιd A B).
Proof.
  intros O ιs ιd B A B' a ι HR D Hfresh.
  destruct (EthEmpty_StepSim O ιs ιd B A B' a ι (EthEmpty_sym _ _ _ _ HR) D Hfresh)
    as [A' [HA HR']].
  exists A'. split. 1: assumption.
  by apply EthEmpty_sym.
Qed.

(** `EthEmpty` preserves the signals in transit to observed PIDs, if `ιd` is
    not observed. *)
Lemma EthEmpty_BarbSim :
  forall O ιs ιd, ιd ∉ O -> BarbSim O (EthEmpty ιs ιd).
Proof.
  intros O ιs ιd Hd A B [_ [Hoff _]] s d HdO. exists s.
  rewrite (Hoff (s, d)). 2: { intro Heq. inv Heq. contradiction. }
  apply option_biforall_refl. intros. apply Signal_eq_refl.
Qed.

(** `EthEmpty` preserves the signals in transit to observed PIDs (in the
    other direction), if `ιd` is not observed. *)
Lemma EthEmpty_BarbSim_rev :
  forall O ιs ιd, ιd ∉ O -> BarbSim O (fun B A => EthEmpty ιs ιd A B).
Proof.
  intros O ιs ιd Hd B A HR.
  apply (EthEmpty_BarbSim O ιs ιd Hd B A (EthEmpty_sym _ _ _ _ HR)).
Qed.

(** Setting a missing or empty entry of the ether with an unobserved target
    to the empty list results in a bisimilar node. *)
Theorem ether_empty_update_bisim :
  forall ιs ιd A O,
    ιd ∉ O ->
    (A.1 !! (ιs, ιd) = None \/ A.1 !! (ιs, ιd) = Some []) ->
    A ~ᵇ (<[(ιs, ιd):=[]]>A.1, A.2) observing O.
Proof.
  intros ιs ιd A O Hd Hemp.
  apply (bisim_up_to_renaming O (EthEmpty ιs ιd)).
  1: apply EthEmpty_StepSim.
  1: apply EthEmpty_StepSim_rev.
  1: by apply EthEmpty_BarbSim.
  1: by apply EthEmpty_BarbSim_rev.
  split_and!. 1: reflexivity.
  * intros k Hk. symmetry. apply lookup_insert_ne. congruence.
  * right. split. 1: exact Hemp.
    right. apply lookup_insert_eq.
Qed.

(** * Finished processes *)

(** `ι` appears only as the source of signals in the ether `eth`: no signals
    are in transit to `ι`, `ι` does not appear inside the signals in transit,
    and the signals sent by `ι` are neither links nor exit signals. *)
Definition appearsOnlyAsSourceAndNoLink (ι : PID) (eth : Ether) : Prop :=
  ¬isTargetedEther ι eth /\
  (forall (ιs ιd : PID) (t : list Signal),
         eth !! (ιs, ιd) = Some t -> ι ∉ flat_union usedPIDsSignal t) /\
  (forall ιd l, eth !! (ι, ιd) = Some l -> (SLink ∉ l) /\ forall r b, SExit r b ∉ l).

(** If `ιs` appears only as a source in the ether, and it is not used in the
    pool, then this is preserved by the steps that do not spawn `ιs`. *)
Theorem appearsOnlyAsSource_preserved :
  forall A B ι a O,
    A -[a | ι]ₙ-> B with O ->
    forall ιs, appearsOnlyAsSourceAndNoLink ιs A.1 ->
      ¬ isUsedPool ιs A.2 ->
      Some ιs ≠ spawnPIDOf a ->
      appearsOnlyAsSourceAndNoLink ιs B.1 /\ ¬isUsedPool ιs B.2.
Proof.
  intros. inv H; simpl in *.
  * clear H2. destruct H0.
    split. split. 2: split.
    - intro. apply H. apply isTargetedEther_etherAdd_rev in H2. assumption.
      intro. subst. apply H1. right. exists ι, p. split. auto; by setoid_rewrite lookup_insert_eq.
      inv H3; simpl in *.
      1-4: set_solver.
      apply elem_of_union_list. exists ({[ιs]} ∪ usedPIDsVal reason).
      split. 2: set_solver.
      apply elem_of_elements, elem_of_map_to_set. do 2 eexists. split. 2: reflexivity.
      assumption.
    - intros. apply etherAdd_lookup in H2 as H2'. destruct H2'.
      + by apply H0 in H4.
      + destruct_hyps; subst.
        intro.
        assert (ιs ∈ usedPIDsSignal t). {
          unfold etherAdd in H2. case_match; setoid_rewrite lookup_insert_eq in H2.
          ** inv H2. apply app_inv_tail in H8. subst.
             apply H0 in H5. rewrite flat_union_app in H4. simpl in H4.
             set_solver.
          ** inv H2. destruct x; inv H8. 2: { destruct x; inv H9. }
             set_solver.
        }
        apply H1. right. exists ι, p. split. auto; by setoid_rewrite lookup_insert_eq.
        inv H3; simpl in *.
        1-4: set_solver.
        apply elem_of_union_list. exists ({[ι']} ∪ usedPIDsVal reason).
        split. 2: set_solver.
        apply elem_of_elements, elem_of_map_to_set. do 2 eexists. split. 2: reflexivity.
        assumption.
    - destruct H0. intros. apply etherAdd_lookup in H4 as H4'.
      destruct H4'.
      + by apply H2 in H5.
      + destruct_hyps; subst.
        assert (SLink ≠ t /\ forall r b, SExit r b <> t). {
          inv H3; auto; exfalso;
          apply H1; left; by setoid_rewrite lookup_insert_eq.
        }
        unfold etherAdd in H4. case_match; setoid_rewrite lookup_insert_eq in H4.
        ** inv H4. apply app_inv_tail in H8. subst.
           apply H2 in H6. set_solver.
        ** inv H4. destruct x; inv H8. 2: { destruct x; inv H9. }
           set_solver.
    - intro. apply H1. apply isUsedPool_insert_1 in H2.
      apply isUsedPool_insert_2. intuition.
      inv H3; simpl in *.
      1-4: do 2 right; set_solver.
      apply elem_of_union_list in H2. destruct_hyps.
      apply elem_of_elements, elem_of_map_to_set in H0; destruct_hyps. subst.
      apply lookup_delete_Some in H0 as [? ?].
      do 2 right. apply elem_of_union_list. exists ({[x0]} ∪ usedPIDsVal x1). split.
      2: assumption.
      apply elem_of_elements, elem_of_map_to_set. do 2 eexists. split. 2: reflexivity.
      assumption.
  * destruct H0. split. split. 2: split.
    - intro. apply H. eapply isTargetedEther_etherPop_rev; eassumption.
    - intros. unfold etherPop in H3. repeat case_match; try congruence. inv H3.
      apply H0 in H6. simpl in H6.
      destruct (decide ((ι1, ι) = (ιs0, ιd))).
      + inv e. setoid_rewrite lookup_insert_eq in H5. inv H5.
        set_solver.
      + setoid_rewrite lookup_insert_ne in H5; auto.
        by apply H0 in H5.
    - intros. unfold etherPop in H3. repeat case_match; try congruence. inv H3.
      destruct H0 as [_ H0].
      destruct (decide ((ι1, ι) = (ιs, ιd))).
      + inv e. setoid_rewrite lookup_insert_eq in H5. inv H5.
        apply H0 in H6. set_solver.
      + setoid_rewrite lookup_insert_ne in H5; auto.
        by apply H0 in H5.
    - intro. apply H1. apply isUsedPool_insert_1 in H5.
      apply isUsedPool_insert_2. destruct H5. 1: intuition. destruct H5. 1: intuition.
      unfold etherPop in H3. repeat case_match; try congruence. inv H3.
      destruct H0.
      specialize (H0 _ _ _ H6).
      simpl in H0.
      inv H4; simpl in *; do 2 right.
      + rewrite flat_union_app in H5. set_solver.
      (* the following 3 cases can't happen, but only 2 would cause
         issues (exit convert, link) since those add the source of the
         signal to the usedPIDsProc *)
      + set_solver.
      + apply elem_of_union_list in H5; destruct_hyps.
        apply elem_of_elements, elem_of_map_to_set in H4; destruct_hyps.
        subst. apply lookup_gset_to_gmap_Some in H4 as [? ?]. subst.
        apply elem_of_union in H5 as [|].
        ** set_solver.
        ** destruct_or! H12; destruct_hyps; subst; simpl in H5.
           all: set_solver.
      + rewrite flat_union_app in H5. simpl in H5.
        assert (ιs <> ι1). {
          intro. subst. apply H3 in H6 as [_ ?]. set_solver.
        }
        set_solver.
      + assert (ιs <> ι1). {
          intro. subst. apply H3 in H6. set_solver.
        }
        set_solver.
      + set_solver.
  * split. 1: assumption.
    eapply not_isUsedPool_step with (O := O) (eth := ether). eassumption.
    2: { eapply n_other. exact H3. assumption. }
    destruct_or! H4; subst; simpl. 1,3: set_solver.
    intro. apply H1. apply elem_of_singleton in H. subst. left; by setoid_rewrite lookup_insert_eq.
  * split. 1: assumption.
    eapply not_isUsedPool_step with (O := O) (eth := ether).
    eassumption. 2: eapply n_spawn; try eassumption.
    assert (ιs <> ι') by congruence.
    assert (ιs ∉ usedPIDsVal v1 ∪ usedPIDsVal v2). {
      intro. apply H1. right. exists ι, p. split. auto; by setoid_rewrite lookup_insert_eq.
      inv H8; simpl; simpl in H9; set_solver.
    }
    set_solver.
Qed.

(** If two pools with an insertion at the same PID are equal, then they are
    also equal after replacing the inserted process. *)
Lemma pool_insert_same_replace :
  forall (Π Π' : ProcessPool) ι p p', ι ↦ p ∥ Π = ι ↦ p' ∥ Π' ->
    forall q, ι ↦ q ∥ Π = ι ↦ q ∥ Π'.
Proof.
  intros Π Π' ι p p' H q.
  transitivity (ι ↦ q ∥ ι ↦ p ∥ Π). 1: by setoid_rewrite insert_insert_eq.
  setoid_rewrite H. by setoid_rewrite insert_insert_eq.
Qed.

(** A PID that is not used in a pool is not associated with a process. *)
Lemma not_isUsedPool_lookup :
  forall ι Π, ¬isUsedPool ι Π -> Π !! ι = None.
Proof.
  intros ι Π HU. destruct (Π !! ι) eqn:E. 2: reflexivity.
  exfalso. apply HU. left. intro Hc. congruence.
Qed.

(** The PID spawned by a step is not used in the pool before the step. *)
Lemma spawned_not_used :
  forall O eth Π B' a ι ι', (eth, Π) -[a | ι]ₙ-> B' with O ->
    spawnPIDOf a = Some ι' -> ¬isUsedPool ι' Π.
Proof.
  intros O eth Π B' a ι ι' D Hsp. inv D; simpl in Hsp; try congruence.
  destruct_or!; subst; simpl in Hsp; congruence.
Qed.

(** A step of a node can also be taken after adding a process to the pool at
    a PID `ι` without a process, if the spawned PID (if any) is fresh in the
    extended pool. *)
Lemma pool_ext_step :
  forall O eth Π eth' Π' a ι0 ι q,
    Π !! ι = None ->
    (eth, Π) -[a | ι0]ₙ-> (eth', Π') with O ->
    (forall p, spawnPIDOf a = Some p -> ¬isUsedPool p (ι ↦ q ∥ Π) /\ ¬appearsEther p eth) ->
    (eth, ι ↦ q ∥ Π) -[a | ι0]ₙ-> (eth', ι ↦ q ∥ Π') with O /\ Π' !! ι = None.
Proof.
  intros O eth Π eth' Π' a ι0 ι q Hι D Hfresh.
  enough (exists Π'', (eth, ι ↦ q ∥ Π) -[a | ι0]ₙ-> (eth', Π'') with O /\
            Π'' = ι ↦ q ∥ Π' /\ Π' !! ι = None) as [Π'' [D' [<- HΠ']]].
  1: by split.
  assert (ι0 ≠ ι) as Hneq.
  { intro. subst. inv D; setoid_rewrite lookup_insert_eq in Hι; congruence. }
  inv D; simpl in *.
  all: apply lookup_insert_None in Hι as [Hι _].
  all: setoid_rewrite (insert_insert_ne _ ι ι0); [|congruence..].
  * eexists. split. 1: by apply n_send.
    split. 1: reflexivity.
    apply lookup_insert_None. split; [assumption|congruence].
  * eexists. split. 1: by eapply n_arrive.
    split. 1: reflexivity.
    apply lookup_insert_None. split; [assumption|congruence].
  * eexists. split. 1: by eapply n_other.
    split. 1: reflexivity.
    apply lookup_insert_None. split; [assumption|congruence].
  * destruct (Hfresh ι' eq_refl) as [Hu Ha].
    setoid_rewrite (insert_insert_ne _ ι ι0) in Hu; [|congruence].
    assert (ι' ≠ ι) as Hι'. {
      intro. subst. apply Hu. left.
      setoid_rewrite lookup_insert_ne; [|congruence].
      by setoid_rewrite lookup_insert_eq.
    }
    eexists. split. 1: by eapply n_spawn.
    split.
    - setoid_rewrite (insert_insert_ne _ ι0 ι); [|congruence..].
      setoid_rewrite (insert_insert_ne _ ι' ι); [|congruence..]. reflexivity.
    - apply lookup_insert_None. split; [|congruence].
      apply lookup_insert_None. split; [assumption|congruence].
Qed.

(** The converse of `pool_ext_step`: a step of a process other than `ι` in
    the extended pool can also be taken in the original pool, if the spawned
    PID (if any) is fresh in the original node. *)
Lemma pool_ext_step_rev :
  forall O eth Π B' a ι0 ι q, ι0 ≠ ι -> Π !! ι = None ->
    (eth, ι ↦ q ∥ Π) -[a | ι0]ₙ-> B' with O ->
    (forall p, spawnPIDOf a = Some p -> ¬isUsedPool p Π /\ ¬appearsEther p eth) ->
    exists A', (eth, Π) -[a | ι0]ₙ-> A' with O /\
      A'.2 !! ι = None /\ B' = (A'.1, ι ↦ q ∥ A'.2).
Proof.
  intros O eth Π B' a ι0 ι q Hneq Hι D Hfresh.
  remember (ι ↦ q ∥ Π) as BΠ eqn:HBΠ.
  revert HBΠ. inv D; intro HBΠ.
  all: destruct (pool_insert_split _ _ _ _ _ _ Hneq HBΠ) as [HΠ Hprs].
  all: pose proof (insert_id Π ι0 _ HΠ) as HidΠ.
  all: rewrite <- HidΠ.
  * eexists. split. 1: by apply n_send.
    split; simpl.
    - setoid_rewrite lookup_insert_ne; [|congruence]. assumption.
    - by rewrite Hprs.
  * eexists. split. 1: by eapply n_arrive.
    split; simpl.
    - setoid_rewrite lookup_insert_ne; [|congruence]. assumption.
    - by rewrite Hprs.
  * eexists. split. 1: by eapply n_other.
    split; simpl.
    - setoid_rewrite lookup_insert_ne; [|congruence]. assumption.
    - by rewrite Hprs.
  * destruct (Hfresh ι' eq_refl) as [Hu Ha].
    assert (ι' ≠ ι) as Hι'. {
      intro. subst.
      assert (isUsedPool ι (ι0 ↦ p ∥ Π0)) as Hc. {
        setoid_rewrite HBΠ. left. by setoid_rewrite lookup_insert_eq.
      }
      contradiction.
    }
    eexists. split.
    1: { eapply n_spawn; try eassumption. by setoid_rewrite HidΠ. }
    split; simpl.
    - setoid_rewrite lookup_insert_ne; [|congruence].
      setoid_rewrite lookup_insert_ne; [|congruence]. assumption.
    - f_equal. rewrite Hprs.
      setoid_rewrite (insert_insert_ne _ ι' ι); [|congruence]. reflexivity.
Qed.

(** A process that has finished its evaluation can only receive signals, or
    terminate. *)
Lemma finished_process_step :
  forall vs mb links flag a p',
    inl ([], RValSeq vs, mb, links, flag) -⌈a⌉-> p' ->
    (exists s d t, a = AArrive s d t) \/ (a = ε /\ p' = inr (gset_to_gmap normal links)).
Proof.
  intros vs mb links flag a p' H. inv H.
  all: try by left; do 3 eexists.
  all: try by right.
  exfalso. eapply value_nostep; [|eassumption]. constructor.
Qed.

(** `B` is `A` extended with a finished process without links at `ι`, where
    `ι` is not used in the pool of `A`, and appears only as a source in the
    ether of `A`. *)
Definition LiveExt (ι : PID) (vs : list Val) (mb : Mailbox) (flag : ProcessFlag)
  (A B : Node) : Prop :=
  appearsOnlyAsSourceAndNoLink ι A.1 /\ ¬isUsedPool ι A.2 /\
  B = (A.1, ι ↦ inl ([], RValSeq vs, mb, ∅, flag) ∥ A.2).

(** The relation of `almost_terminated_bisim`: the finished process at `ι`
    is still there (`LiveExt`), or it has already terminated (`DeadExt`). *)
Definition AlmostExt (ι : PID) (vs : list Val) (mb : Mailbox) (flag : ProcessFlag)
  (A B : Node) : Prop :=
  LiveExt ι vs mb flag A B \/ DeadExt ι A B.

(** Steps of a node are matched by the node extended with the finished
    process (or the terminated process). *)
Lemma AlmostExt_StepSim :
  forall O ι vs mb flag, StepSimOpt O (AlmostExt ι vs mb flag).
Proof.
  intros O ι vs mb flag [eth Π] B [eth' Π'] a ι0 [[Haoas [HU HB]] | HD] D Hfresh.
  * subst B. simpl in *.
    destruct (pool_ext_step O eth Π eth' Π' a ι0 ι _ (not_isUsedPool_lookup _ _ HU) D Hfresh)
      as [D' _].
    assert (Some ι ≠ spawnPIDOf a) as Hsp. {
      intro Hsp. symmetry in Hsp. destruct (Hfresh ι Hsp) as [Hu _].
      apply Hu. left. by setoid_rewrite lookup_insert_eq.
    }
    pose proof (appearsOnlyAsSource_preserved _ _ _ _ _ D ι Haoas HU Hsp) as [Ha' Hu'].
    eexists. split. 1: left; exact D'.
    left. by split_and!.
  * destruct (DeadExt_StepSim O ι _ _ _ _ _ HD D Hfresh) as [B' [HB' HR']].
    exists B'. split. 1: by left. by right.
Qed.

(** Steps of a node extended with the finished process (or the terminated
    process) are matched by the original node. The termination of the
    finished process is matched by not taking a step. *)
Lemma AlmostExt_StepSim_rev :
  forall O ι vs mb flag, StepSimOpt O (fun B A => AlmostExt ι vs mb flag A B).
Proof.
  intros O ι vs mb flag B [eth Π] B' a ι0 [[Haoas [HU HB]] | HD] D Hfresh.
  * subst B. simpl in *.
    pose proof (not_isUsedPool_lookup _ _ HU) as Hι.
    destruct (decide (ι0 = ι)) as [-> | Hneq].
    - (* the finished process can only terminate *)
      remember (ι ↦ inl ([], RValSeq vs, mb, ∅, flag) ∥ Π) as BΠ eqn:HBΠ.
      revert HBΠ. inv D; intro HBΠ.
      all: pose proof (pool_insert_same _ _ _ _ _ HBΠ) as Hp; subst p.
      all: pose proof (pool_insert_same_replace _ _ _ _ _ HBΠ) as Hrepl.
      all: edestruct finished_process_step as [[s0 [d0 [t0 Ha]]] | [Ha Hp']];
        [eassumption| |]; try congruence.
      + (* arrivals: no signals are sent to ι *)
        exfalso. destruct Haoas as [HT _]. apply HT.
        edestruct etherPop_some_inv as [xs [Hxs _]]; [eassumption|].
        by exists ι1, (t :: xs).
      + destruct_or!; congruence.
      + (* termination: the other node does not take a step *)
        subst p'. exists (eth, Π). split. 1: by right.
        right. split. 1: assumption.
        simpl. setoid_rewrite gset_to_gmap_empty. by rewrite Hrepl.
    - destruct (pool_ext_step_rev O eth Π B' a ι0 ι _ Hneq Hι D Hfresh)
        as [A' [D' [_ ->]]].
      assert (Some ι ≠ spawnPIDOf a) as Hsp. {
        intro Hsp. symmetry in Hsp.
        apply (spawned_not_used _ _ _ _ _ _ _ D) in Hsp. apply Hsp.
        left. by setoid_rewrite lookup_insert_eq.
      }
      pose proof (appearsOnlyAsSource_preserved _ _ _ _ _ D' ι Haoas HU Hsp) as [Ha' Hu'].
      exists A'. split. 1: by left.
      left. by split_and!.
  * destruct (DeadExt_StepSim_rev O ι _ _ _ _ _ HD D Hfresh) as [A' [HA' HR']].
    exists A'. split. 1: by left. by right.
Qed.

(** `AlmostExt` preserves the signals in transit. *)
Lemma AlmostExt_BarbSim :
  forall O ι vs mb flag, BarbSim O (AlmostExt ι vs mb flag).
Proof.
  intros O ι vs mb flag A B [[_ [_ ->]] | [_ ->]] s d _.
  all: exists s; simpl; apply option_biforall_refl; intros; apply Signal_eq_refl.
Qed.

(** `AlmostExt` preserves the signals in transit (in the other direction). *)
Lemma AlmostExt_BarbSim_rev :
  forall O ι vs mb flag, BarbSim O (fun B A => AlmostExt ι vs mb flag A B).
Proof.
  intros O ι vs mb flag B A [[_ [_ ->]] | [_ ->]] s d _.
  all: exists s; simpl; apply option_biforall_refl; intros; apply Signal_eq_refl.
Qed.

(** Adding a finished process without links at a PID `ι`, which is not used
    in the pool, and appears only as a source in the ether, results in a
    bisimilar node. The hypothesis `ι ∉ O` is not used in the proof. *)
Theorem almost_terminated_bisim :
  forall O A mb flag ι vs,
    appearsOnlyAsSourceAndNoLink ι A.1 ->
    ¬isUsedPool ι A.2 ->
    ι ∉ O ->
    A ~ᵇ (A.1, ι ↦ inl ([], RValSeq vs, mb, ∅, flag) ∥ A.2) observing O.
Proof.
  intros O A mb flag ι vs Haoas HU _.
  apply (bisim_up_to_renaming_opt O (AlmostExt ι vs mb flag)).
  1: apply AlmostExt_StepSim.
  1: apply AlmostExt_StepSim_rev.
  1: apply AlmostExt_BarbSim.
  1: apply AlmostExt_BarbSim_rev.
  left. by split_and!.
Qed.
