From CoreErlang.Concurrent Require Import BisimReductions.
From CoreErlang.FrameStack Require Import SubstSemantics Examples.

Import ListNotations.

(*

This does not work this way. We have to either remove the side conditions, 
or add more.

Unset Guard Checking.
Theorem almost_terminated_bisim :
  forall O A mb flag ι vs,
    ¬isTargetedEther ι A.1 ->
    ¬isUsedPool ι A.2 ->
    ι ∉ O ->
    A ~ (A.1, ι ↦ inl ([], RValSeq vs, mb, ∅, flag) ∥ A.2) observing O.
Proof with left; by setoid_rewrite lookup_insert.
  cofix IH. intros * Heth HΠ HO. constructor; intros.
  2,4: exists source; do 2 eexists; split; [apply n_refl|]; simpl; apply option_biforall_refl; intros; apply Signal_eq_refl.
  * inv H; simpl in *.
    - do 2 eexists. split.
      + setoid_rewrite insert_commute. 2: apply not_isUsedPool_insert_1 in HΠ; set_solver.
        eapply n_trans. 2: apply n_refl. by apply n_send.
      + setoid_rewrite insert_commute. 2: apply not_isUsedPool_insert_1 in HΠ; set_solver.
        apply IH; try assumption.
        ** intro. simpl in *. apply isTargetedEther_etherAdd_rev in H. congruence.
           intro. subst. apply HΠ. right. exists ι0, p. split.
           by setoid_rewrite lookup_insert.
           inv H0; simpl. 1-4: set_solver.
           apply elem_of_union_list. exists ({[ι]} ∪ usedPIDsVal reason).
           split. 2: set_solver.
           apply elem_of_elements, elem_of_map_to_set. exists ι, reason.
           by split.
        ** simpl. intro. apply HΠ. apply isUsedPool_insert_1 in H.
           apply isUsedPool_insert_2. intuition.
           right. right.
           inv H0; simpl in *. 1-4: set_solver.
           apply elem_of_union_list in H; destruct_hyps.
           apply elem_of_elements, elem_of_map_to_set in H. destruct_hyps.
           apply lookup_delete_Some in H. destruct_hyps.
           apply elem_of_union_list. exists ({[x0]} ∪ usedPIDsVal x1). split.
           2: set_solver.
           apply elem_of_elements, elem_of_map_to_set.
           exists x0, x1. by split.
    - do 2 eexists. split.
      + setoid_rewrite insert_commute. 2: apply not_isUsedPool_insert_1 in HΠ; set_solver.
        eapply n_trans. 2: apply n_refl. by apply n_arrive.
      + setoid_rewrite insert_commute. 2: apply not_isUsedPool_insert_1 in HΠ; set_solver.
        apply IH; try assumption.
        ** intro. eapply isTargetedEther_etherPop_rev in H. 2: eassumption.
           congruence.
        ** simpl. intro. apply HΠ. apply isUsedPool_insert_1 in H.
           apply isUsedPool_insert_2. intuition.
           right. right.
           inv H1; simpl in *.
           1-4: set_solver.
           apply elem_of_union_list in H; destruct_hyps.
           apply elem_of_elements, elem_of_map_to_set in H. destruct_hyps.
           apply lookup_delete_Some in H. destruct_hyps.
           apply elem_of_union_list. exists ({[x0]} ∪ usedPIDsVal x1). split.
           2: set_solver.
           apply elem_of_elements, elem_of_map_to_set.
           exists x0, x1. by split.
    - do 2 eexists. split.
      + setoid_rewrite insert_commute. 2: set_solver.
        eapply n_trans. 2: apply n_refl. by apply n_other.
      + setoid_rewrite insert_commute. 2: set_solver.
        apply IH; try assumption. set_solver.
    - assert (exists fresh, ¬isUsedPool fresh (ι0 ↦ p ∥ Π)
                         /\ ¬appearsEther fresh ether
                         /\ fresh <> ι'
                         /\ fresh ∉ O
                         /\ fresh ∉ usedPIDsAct (ASpawn ι' v1 v2 link_flag)
                         /\ ¬isUsedPool fresh (ι ↦ inl ([], RValSeq vs, mb, ∅, flag) ∥ ι0 ↦ p ∥ Π)
                         /\ ¬ isUsedPool fresh
         (ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι0]} else ∅, false) ∥ ι0 ↦ p' ∥ Π)) as [fresh Hf]. {
        (* freshness *)
        admit.
      }
      destruct_hyps.
      assert (fresh <> ι0) as Hf2. {
        intro. subst. apply H1...
      }
      assert (ι' <> ι0) as Hneq. {
        intro. subst. apply H4...
      }
      assert (fresh <> ι) as Hf. {
          intro. subst. apply H12...
        }
        assert (ι' ∉ usedPIDsVal v1 ∪ usedPIDsVal v2 ∪ usedPIDsProc p). {
          intro. apply H4.
          right. exists ι0, p. split. by setoid_rewrite lookup_insert.
          inv H7; simpl in *; set_solver.
        }
        assert (renamePIDProc ι' fresh 
                 (inl ([], r, emptyBox, if link_flag then {[ι0]} else ∅, false)) =
                 (inl ([], r, emptyBox, if link_flag then {[ι0]} else ∅, false))) as Hp.
        {
          cbn. replace (set_map (renamePIDPID ι' fresh) (if link_flag then {[ι0]} else ∅)) with
                       (if link_flag then {[ι0]} else ∅ : gset PID). 2: {
            case_match; auto. setoid_rewrite set_map_singleton_L.
            clear -Hf2 Hneq. by renamePIDPID_case_match.
          }
          repeat f_equal.
          rewrite isNotUsed_renamePID_red. reflexivity.
          destruct v1; inv H6; cbn.
          1-8: set_solver.
          case_match; inv H16. 2: set_solver.
          simpl. intro. apply subst_usedPIDs in H15; simpl in *.
          destruct H15; destruct_hyps. set_solver.
          apply list_subst_idsubst_inl in H15.
          apply elem_of_app in H15 as [|].
          * apply elem_of_map_iff in H15; destruct_hyps. destruct x1, p0. subst.
            simpl in H16. apply elem_of_union in H16 as [|]. 2: set_solver.
            assert (ι' ∈ flat_union (λ x : nat * nat * Exp, usedPIDsExp x.2) ext). {
              apply elem_of_flat_union. eexists; split; eassumption.
            }
            set_solver.
          * eapply mk_list_usedPIDs in H2.
            assert (ι' ∈ flat_union usedPIDsVal l). {
              apply elem_of_flat_union. eexists; split; eassumption.
            }
            set_solver.
        }
        assert (
         ι0 ↦ renamePIDProc ι' fresh p' 
         ∥ fresh
           ↦ (inl ([], r, emptyBox, if link_flag then {[ι0]} else ∅, false)) ∥ Π .[ ι' ⇔ fresh ]ₚₚ = ι0 ↦ renamePIDProc ι' fresh p' 
         ∥ fresh
           ↦ (inl ([], r, emptyBox, if link_flag then {[ι0]} else ∅, false)) ∥ Π
        ) as HΠ.
        {
          apply map_eq. intros.
          destruct (decide (ι0 = i)).
          - subst. by setoid_rewrite lookup_insert.
          - setoid_rewrite lookup_insert_ne; auto.
            destruct (decide (fresh = i)).
            + subst. by setoid_rewrite lookup_insert.
            + setoid_rewrite lookup_insert_ne; auto.
              admit. (* TODO: later *)
        }
      exists (renamePIDEther ι' fresh ether, ι ↦ inl ([], RValSeq vs, mb, ∅, flag) ∥ renamePIDPool ι' fresh (
      ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι0]} else ∅, false) ∥ ι0 ↦ p' ∥ Π)), [(renamePIDAct ι' fresh (ASpawn ι' v1 v2 link_flag), ι0)].
      split.
      + setoid_rewrite (insert_commute _ ι ι0). 2: set_solver.
        setoid_rewrite (insert_commute _ ι' ι0). 2: set_solver.
        repeat rewrite pool_insert_renamePID.
        replace (renamePIDPID_sym ι' fresh ι0) with ι0.
        replace (renamePIDPID_sym ι' fresh ι') with fresh.
        2: {
          renamePIDPID_sym_case_match.
        }
        2: {
          clear -H9 H4 H12. renamePIDPID_sym_case_match.
          all: exfalso.
          * apply H4...
          * apply H12. left.
            destruct (decide (fresh = ι)).
            - subst. by setoid_rewrite lookup_insert.
            - setoid_rewrite lookup_insert_ne; auto. by setoid_rewrite lookup_insert.
        }
        simpl renamePIDAct.
        rewrite Hp, HΠ.
        replace (renamePIDPID ι' fresh ι') with fresh by renamePIDPID_case_match.
        rewrite isNotUsed_renamePID_val, isNotUsed_renamePID_val.
        2-3: set_solver.
        eapply n_trans. eapply n_spawn; try eassumption.
        ** setoid_rewrite insert_commute. assumption. set_solver.
        ** eapply renamePID_is_preserved_local with (from := ι') (to := fresh) in H7.
           simpl in H7.
           rewrite isNotUsed_renamePID_val, isNotUsed_renamePID_val in H7.
           replace (renamePIDPID ι' fresh ι') with fresh in H7 by renamePIDPID_case_match.
           rewrite isNotUsed_renamePID_proc in H7.
           exact H7.
           1,3-5: set_solver.
           all: intro; apply H12; right; exists ι0, p; split; [|assumption].
           all: setoid_rewrite lookup_insert_ne; auto; try by setoid_rewrite lookup_insert.
           all: set_solver.
        ** rewrite does_not_appear_renamePID_ether; auto.
           assert (fresh <> ι0). {
             intro. subst. apply H1...
           }
           setoid_rewrite (insert_commute _ ι ι0). 2: set_solver.
           setoid_rewrite (insert_commute _ fresh ι0). 2: set_solver.
           setoid_rewrite (insert_commute _ fresh ι). 2: set_solver.
           apply n_refl.
      + eapply barbedBisim_trans.
        eapply (rename_bisim O _ _ [(ι', fresh)]). cbn. set_solver.
        simpl. apply IH; simpl. 2: assumption.
        repeat rewrite pool_insert_renamePID.
        replace (renamePIDPID_sym ι' fresh ι0) with ι0.
        replace (renamePIDPID_sym ι' fresh ι') with fresh.
        2: {
          renamePIDPID_sym_case_match.
        }
        2: {
          clear -H9 H4 H12. renamePIDPID_sym_case_match.
          all: exfalso.
          * apply H4...
          * apply H12. left.
            destruct (decide (fresh = ι)).
            - subst. by setoid_rewrite lookup_insert.
            - setoid_rewrite lookup_insert_ne; auto. by setoid_rewrite lookup_insert.
        }
        rewrite Hp. setoid_rewrite (insert_commute _ fresh ι0); auto.
        setoid_rewrite HΠ.
        repeat setoid_rewrite dom_insert_L.
        set_solver.
  * destruct (decide (ι0 = ι)).
    {
      subst. inv H1.
      * put (lookup ι : ProcessPool -> _) on H4 as D.
        setoid_rewrite lookup_insert in D. inv D. inv H7.
      * put (lookup ι : ProcessPool -> _) on H3 as D.
        setoid_rewrite lookup_insert in D. inv D. inv H8.
        - do 2 eexists. split. apply n_refl.
          admit.
        - admit.
        - admit.
        - admit.
        - admit.
        - admit.
      * admit.
      * put (lookup ι : ProcessPool -> _) on H3 as D.
        setoid_rewrite lookup_insert in D. inv D. inv H12.
    }
    {
      destruct A. simpl in *. destruct B'.
      inv H1.
      - assert (p = ι0 ↦ p1 ∥ p) as Eq1. {
          apply map_eq.
          intro. put (lookup i : ProcessPool -> _) on H4 as HD.
          destruct (decide (i = ι0)).
          * subst. setoid_rewrite lookup_insert.
            setoid_rewrite lookup_insert in HD.
            setoid_rewrite lookup_insert_ne in HD; auto.
          * by setoid_rewrite lookup_insert_ne.
        }
        rewrite Eq1.
        do 2 eexists. split.
        + eapply n_trans. 2: apply n_refl. by apply n_send.
        + replace (ι0 ↦ p' ∥ prs) with
            (ι ↦ inl ([], RValSeq vs, mb, ∅, flag) ∥ ι0 ↦ p' ∥ p). 2: {
            apply map_eq. intros.
            put (lookup i : ProcessPool -> _) on H4 as HD.
            destruct (decide (i = ι)).
            * subst. setoid_rewrite lookup_insert.
              setoid_rewrite lookup_insert_ne; auto.
              setoid_rewrite lookup_insert in HD.
              setoid_rewrite lookup_insert_ne in HD; auto.
            * destruct (decide (i = ι0)).
              - subst. setoid_rewrite lookup_insert.
                setoid_rewrite lookup_insert_ne; auto.
                by setoid_rewrite lookup_insert.
              - setoid_rewrite lookup_insert_ne in HD; auto.
                repeat setoid_rewrite lookup_insert_ne; auto.
          }
          apply IH; try assumption. set_solver.
      - assert (p = ι0 ↦ p1 ∥ p) as Eq1. {
          apply map_eq.
          intro. put (lookup i : ProcessPool -> _) on H3 as HD.
          destruct (decide (i = ι0)).
          * subst. setoid_rewrite lookup_insert.
            setoid_rewrite lookup_insert in HD.
            setoid_rewrite lookup_insert_ne in HD; auto.
          * by setoid_rewrite lookup_insert_ne.
        }
        rewrite Eq1.
        do 2 eexists. split.
        + eapply n_trans. 2: apply n_refl. by apply n_arrive.
        + replace (ι0 ↦ p' ∥ prs) with
            (ι ↦ inl ([], RValSeq vs, mb, ∅, flag) ∥ ι0 ↦ p' ∥ p). 2: {
            apply map_eq. intros.
            put (lookup i : ProcessPool -> _) on H3 as HD.
            destruct (decide (i = ι)).
            * subst. setoid_rewrite lookup_insert.
              setoid_rewrite lookup_insert_ne; auto.
              setoid_rewrite lookup_insert in HD.
              setoid_rewrite lookup_insert_ne in HD; auto.
            * destruct (decide (i = ι0)).
              - subst. setoid_rewrite lookup_insert.
                setoid_rewrite lookup_insert_ne; auto.
                by setoid_rewrite lookup_insert.
              - setoid_rewrite lookup_insert_ne in HD; auto.
                repeat setoid_rewrite lookup_insert_ne; auto.
          }
          apply IH; try assumption. set_solver.
      - assert (p = ι0 ↦ p1 ∥ p) as Eq1. {
          apply map_eq.
          intro. put (lookup i : ProcessPool -> _) on H3 as HD.
          destruct (decide (i = ι0)).
          * subst. setoid_rewrite lookup_insert.
            setoid_rewrite lookup_insert in HD.
            setoid_rewrite lookup_insert_ne in HD; auto.
          * by setoid_rewrite lookup_insert_ne.
        }
        rewrite Eq1.
        do 2 eexists. split.
        + eapply n_trans. 2: apply n_refl. by apply n_other.
        + replace (ι0 ↦ p' ∥ Π) with
            (ι ↦ inl ([], RValSeq vs, mb, ∅, flag) ∥ ι0 ↦ p' ∥ p). 2: {
            apply map_eq. intros.
            put (lookup i : ProcessPool -> _) on H3 as HD.
            destruct (decide (i = ι)).
            * subst. setoid_rewrite lookup_insert.
              setoid_rewrite lookup_insert_ne; auto.
              setoid_rewrite lookup_insert in HD.
              setoid_rewrite lookup_insert_ne in HD; auto.
            * destruct (decide (i = ι0)).
              - subst. setoid_rewrite lookup_insert.
                setoid_rewrite lookup_insert_ne; auto.
                by setoid_rewrite lookup_insert.
              - setoid_rewrite lookup_insert_ne in HD; auto.
                repeat setoid_rewrite lookup_insert_ne; auto.
          }
          apply IH; try assumption. set_solver.
      - assert (p = ι0 ↦ p1 ∥ p) as Eq1. {
          apply map_eq.
          intro. put (lookup i : ProcessPool -> _) on H3 as HD.
          destruct (decide (i = ι0)).
          * subst. setoid_rewrite lookup_insert.
            setoid_rewrite lookup_insert in HD.
            setoid_rewrite lookup_insert_ne in HD; auto.
          * by setoid_rewrite lookup_insert_ne.
        }
        rewrite Eq1.
        assert (ι' <> ι0) as Hneq1. {
          intro. subst. apply H8...
        }
        assert (ι' <> ι) as Hneq2. {
          intro. subst. rewrite H3 in H8. apply H8...
        }
        do 2 eexists. split.
        + eapply n_trans. 2: apply n_refl. eapply n_spawn; try eassumption.
          rewrite H3, Eq1 in H8.
          intro. apply H8.
          destruct H1.
          ** left. setoid_rewrite lookup_insert_ne; auto.
          ** destruct_hyps. right.
             exists x, x0. split. 2: assumption.
             destruct (decide (x = ι0)).
             ++ subst. setoid_rewrite lookup_insert_ne; auto.
             ++ setoid_rewrite lookup_insert_ne. assumption.
                intro. subst.
                apply elem_of_dom_2 in H1.
                apply H. set_solver.
        + replace (ι0 ↦ p' ∥ Π) with
            (ι ↦ inl ([], RValSeq vs, mb, ∅, flag) ∥ ι0 ↦ p' ∥ p). 2: {
            apply map_eq. intros.
            put (lookup i : ProcessPool -> _) on H3 as HD.
            destruct (decide (i = ι)).
            * subst. setoid_rewrite lookup_insert.
              setoid_rewrite lookup_insert_ne; auto.
              setoid_rewrite lookup_insert in HD.
              setoid_rewrite lookup_insert_ne in HD; auto.
            * destruct (decide (i = ι0)).
              - subst. setoid_rewrite lookup_insert.
                setoid_rewrite lookup_insert_ne; auto.
                by setoid_rewrite lookup_insert.
              - setoid_rewrite lookup_insert_ne in HD; auto.
                repeat setoid_rewrite lookup_insert_ne; auto.
          }
          setoid_rewrite (insert_commute _ ι' ι); auto.
          apply IH; try assumption. set_solver.
    }
Admitted.
Set Guard Checking. *)

Theorem sequential_to_node :
  forall k fs e fs' e', ⟨fs, e⟩ -[k]-> ⟨fs', e'⟩ ->
    forall O ι eth Π mb links flag,
      (eth, ι ↦ inl (fs, e, mb, links, flag) ∥ Π) -[repeat (τ, ι) k]ₙ->*
      (eth, ι ↦ inl (fs', e', mb, links, flag) ∥ Π) with O.
Proof.
  intros *. intro H. induction H; intros.
  * constructor.
  * simpl. econstructor.
    constructor. constructor. eassumption.
    by left.
    apply IHstep_rt.
Qed.

(* Everything which falls under the n_other category can be lifted to
   inter-process level *)
Theorem process_local_to_node :
  forall p p' l ι, p -⌈l⌉->* p' ->
    Forall (fun a => a = τ \/ a = ε \/ a = ASelf ι) l ->
    forall O eth Π,
      (eth, ι ↦ p ∥ Π) -[map (fun a => (a, ι)) l]ₙ->*
      (eth, ι ↦ p' ∥ Π) with O.
Proof.
  intros *. intro H. induction H; intros.
  * constructor.
  * simpl. inv H1. specialize (IHLabelStar H5 O eth Π). econstructor.
    2: exact IHLabelStar.
    clear H5 H0 IHLabelStar. destruct_or! H4; subst.
    - constructor; auto.
    - constructor; auto.
    - constructor; auto.
Qed.

(* Lemma meta_to_cons_mk_list :
  forall l l',
    meta_to_cons l = l' <-> mk_list l' = Some l.
Proof.
  split; revert l'; induction l; intros; simpl in H; subst.
  * by simpl.
  * simpl. 
Qed. *)

Lemma meta_to_cons_mk_list : forall l, mk_list (meta_to_cons l) = Some l.
Proof.
  induction l.
  by simpl.
  simpl. by rewrite IHl.
Qed.

Lemma mk_list_meta_to_cons : forall l l', mk_list l = Some l' ->
  meta_to_cons l' = l.
Proof.
  induction l; intros; inv H.
  * by simpl.
  * case_match. 2: congruence.
    inv H1. simpl. f_equal.
    by apply IHl2.
Qed.

Lemma eval_split_correct :
  forall l l' idx,
  mk_list l = Some l' ->
  idx < length l' ->
  eval_split (VLit (Z.of_nat idx)) l = RValSeq [VTuple [meta_to_cons (take idx l'); meta_to_cons (drop idx l')]].
Proof.
  intros. simpl.
  case_match.
  * apply Z.ltb_lt in H1. lia.
  * rewrite Nat2Z.id.
    clear H1. revert l l' H0 H. induction idx; intros.
    - simpl. rewrite drop_0. by erewrite mk_list_meta_to_cons.
    - simpl. destruct l; inv H. simpl in H0. lia.
      case_match. 2: congruence. inv H2. simpl in H0.
      specialize (IHidx l2 l ltac:(lia) H). case_match. 2: congruence.
      destruct p. simpl.
      by inv IHidx.
Qed.

Lemma mk_list_closed :
  forall l l' Γ,
    VAL Γ ⊢ l ->
    mk_list l = Some l' -> Forall (ValScoped Γ) l'.
Proof.
  induction l; intros; inv H0. by constructor.
  case_match; try congruence.
  inv H2. constructor. by inv H.
  apply IHl2; by destruct_scopes.
Qed.

Lemma meta_to_cons_closed :
  forall l Γ,
    Forall (ValScoped Γ) l ->
    VAL Γ ⊢ meta_to_cons l.
Proof.
  induction l; intros; inv H; simpl; by scope_solver.
Qed.

Lemma EReceive_scope :
  forall l time r Γ,
  Forall (fun '(pl, g, e) => EXP PatListScope pl + (3 + Γ) ⊢ g /\ EXP PatListScope pl + (3 + Γ) ⊢ e) l ->
  EXP 3 + Γ ⊢ time ->
  EXP 4 + Γ ⊢ r ->
  EXP Γ ⊢ EReceive l time r.
Proof.
  intros. do 6 scope_solver_step.
  1: scope_solver.
  2: lia.
  do 2 scope_solver_step. scope_solver.
  1: scope_solver.
  do 2 scope_solver_step.
  1: scope_solver.
  do 2 scope_solver_step.
  scope_solver_step.
  1: scope_solver.
  all: intros; simpl in *; rewrite app_length, map_length in H2; simpl in H2;
  assert (i < length l \/ i = length l) by lia; destruct H3.
  {
    rewrite indexed_to_forall with (def := ([], ˝VNil, ˝VNil)) in H.
    apply H in H3 as H'.
    repeat rewrite map_app. repeat rewrite map_map. simpl.
    rewrite app_nth1. 2: by rewrite map_length.
    rewrite app_nth1. 2: by rewrite map_length.
    rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
    setoid_rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
    destruct nth, p. cbn. apply H'.
  }
  {
    rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
    setoid_rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
    subst. erewrite <- map_length. rewrite nth_middle. cbn. scope_solver.
  }
  {
    rewrite indexed_to_forall with (def := ([], ˝VNil, ˝VNil)) in H.
    apply H in H3 as H'.
    repeat rewrite map_app. repeat rewrite map_map. simpl.
    rewrite app_nth1. 2: by rewrite map_length.
    rewrite app_nth1. 2: by rewrite map_length.
    setoid_rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
    extract_map_fun F.
    assert (° ESeq (° EPrimOp "remove_message" []) (˝VNil) = F ([], ˝VNil, ˝VNil)). {
      by subst F.
    }
    erewrite (nth_indep (map F l) _ (° ESeq (° EPrimOp "remove_message" []) (˝ VNil))).
    rewrite H4. rewrite map_nth. subst F.
    destruct nth, p. cbn.
    do 2 scope_solver_step.
    1: scope_solver.
    1: apply H'.
    by rewrite map_length.
  }
  {
    rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
    setoid_rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
    subst. erewrite <- map_length. rewrite nth_middle. cbn. scope_solver.
  }
Qed.

Lemma eval_append_correct :
  forall l l',
    eval_append (meta_to_cons l) (meta_to_cons l') = RValSeq [meta_to_cons (l ++ l')].
Proof.
  induction l; simpl; intros.
  * reflexivity.
  * by rewrite IHl.
Qed.

Section seq_map_eval.

Context {l : Val}
        {l' : list Val}
        {ident : nat}
        {f : Val -> Val}
        {f_clos : Val}
        {f_clos_closed : VALCLOSED f_clos}.

Hypothesis f_simulates :
  forall v : Val, create_result (IApp f_clos) [v] [] = Some (RValSeq [f v], []).
Hypothesis l_is_proper : mk_list l = Some l'.
Hypothesis f_closed : forall v, VALCLOSED v -> VALCLOSED (f v).
Hypothesis l_closed : VALCLOSED l.

Definition map_body : Exp :=
  ECase (˝VVar 2) [
      ([PNil], ˝ttrue, ˝VNil);
      ([PCons PVar PVar], ˝ttrue, °ECons (EApp (˝VVar 3) [˝VVar 0])
                                        (EApp (˝VVar 2) [˝VVar 3;˝VVar 1])
      )
    ].

Definition map_clos : Val :=
  VClos [(ident, 2, map_body)] ident 2 map_body.

Lemma map_clos_closed :
  VALCLOSED map_clos.
Proof.
  scope_solver.
Qed.

Hint Resolve map_clos_closed : examples.

Open Scope string_scope.

Ltac do_step := econstructor; [constructor;auto with examples| simpl].

Theorem map_clos_eval :
  ⟨[], EApp (˝map_clos) [˝f_clos; ˝l]⟩ -->* RValSeq [meta_to_cons (map f l')].
Proof.
  generalize dependent l'. clear l_is_proper l'.
  induction l; intros; simpl in *; inv l_is_proper.
  * simpl.
    eexists. split. repeat constructor.
    do 7 do_step.
    econstructor. econstructor; auto. cbn.
    do 6 do_step.
    constructor.
  * case_match. 2: congruence. destruct l'; inv H0. clear IHv1.
    inv l_closed.
    specialize (IHv2 H4 _ eq_refl). destruct IHv2 as [clock [IHv2 IHD]].
    eexists. split.
    {
      inv IHv2. inv H1. clear H4.
      simpl. constructor. constructor; auto.
    }
    do 7 do_step.
    econstructor. econstructor; auto. cbn.
    do 2 do_step.
    econstructor. apply eval_step_case_not_match. reflexivity.
    do 4 do_step.
    eapply transitive_eval.
    rewrite <- app_nil_l at 1. apply frame_indep_nil.
    {
      repeat rewrite vclosed_ignores_ren; auto.
      rewrite vclosed_ignores_sub; auto.
      exact IHD.
    }
    repeat rewrite vclosed_ignores_ren; auto.
    rewrite vclosed_ignores_sub; auto.
    do 6 do_step.
    econstructor. econstructor; auto. simpl. by rewrite f_simulates.
    econstructor. constructor; auto. simpl.
    constructor.
Qed.


End seq_map_eval.

Hint Resolve map_clos_closed : examples.



Section map_pmap.

Context {l : Val}
        {l' : list Val}
        {ident : nat}
        {f : Val -> Val}
        {f_clos : Val}
        {f_clos_closed : VALCLOSED f_clos}
        {ι : PID} (* This PID will be observed *).

Hypothesis f_simulates :
  forall v : Val, create_result (IApp f_clos) [v] [] = Some (RValSeq [f v], []).
Hypothesis l_is_proper : mk_list l = Some l'.
Hypothesis f_closed : forall v, VALCLOSED v -> VALCLOSED (f v).
Hypothesis l_closed : VALCLOSED l.
Hypothesis (l_is_free_of_PIDs : usedPIDsVal (meta_to_cons l') = ∅).

Open Scope string_scope.

(* Definition map_body : Exp :=
  ECase (˝VVar 2) [
      ([PNil], ˝ttrue, ˝VNil);
      ([PCons PVar PVar], ˝ttrue, °ECons (EApp (˝VVar 3) [˝VVar 0])
                                        (EApp (˝VVar 2) [˝VVar 3;˝VVar 1])
      )
    ].

Definition map_clos : Val :=
  VClos [(ident, 2, map_body)] ident 2 map_body.

Lemma map_clos_closed :
  VALCLOSED map_clos.
Proof.
  scope_solver.
Qed.

Hint Resolve map_clos_closed : examples.

Open Scope string_scope.

Ltac do_step := econstructor; [constructor;auto with examples| simpl].

Theorem map_clos_eval :
  ⟨[], EApp (˝map_clos) [˝f_clos; ˝l]⟩ -->* RValSeq [meta_to_cons (map f l')].
Proof.
  generalize dependent l'. clear l_is_proper l'.
  induction l; intros; simpl in *; inv l_is_proper.
  * simpl.
    eexists. split. repeat constructor.
    do 7 do_step.
    econstructor. econstructor; auto. cbn.
    do 6 do_step.
    constructor.
  * case_match. 2: congruence. destruct l'; inv H0. clear IHv1.
    inv l_closed.
    specialize (IHv2 H4 _ eq_refl). destruct IHv2 as [clock [IHv2 IHD]].
    eexists. split.
    {
      inv IHv2. inv H1. clear H4.
      simpl. constructor. constructor; auto.
    }
    do 7 do_step.
    econstructor. econstructor; auto. cbn.
    do 2 do_step.
    econstructor. apply eval_step_case_not_match. reflexivity.
    do 4 do_step.
    eapply transitive_eval.
    rewrite <- app_nil_l at 1. apply frame_indep_nil.
    {
      repeat rewrite vclosed_ignores_ren; auto.
      rewrite vclosed_ignores_sub; auto.
      exact IHD.
    }
    repeat rewrite vclosed_ignores_ren; auto.
    rewrite vclosed_ignores_sub; auto.
    do 6 do_step.
    econstructor. econstructor; auto. simpl. by rewrite f_simulates.
    econstructor. constructor; auto. simpl.
    constructor.
Qed.
 *)
(*
  Alternative suggestion:
  1. Have a server with a number of PIDs that compute a map of some list and function
  sequentially.
  2. Prove the equivalence.
  3. Any pmap function should build up the structure of that server first (with spawns).
*)


Context (idx : nat)
        (Hidx : idx < length l').

(*
pmap(F, L) ->
  {L1, L2} = lists:split(Idx, L),
  spawn(fun(L, Addr) -> Addr ! map(F, L), [L1, self()]),
  Mapped = map(F, L2),
  receive
    L1 -> L1 ++ L2
  end
*)
Definition receive : Exp :=
(EReceive [
               ([PVar], ˝ttrue, 
                 °ECall (˝erlang) (˝send)
                   [
                    ˝VPid ι;
                    (* NOTE: the nameless approach makes it harder to guess
                       the variable used outside the given clauses in a receive
                                                               |
                                                               v
                    *)
                    °ECall (˝erlang) (˝VLit "++") [˝VVar 0; ˝VVar 4]
                   ])
             ] (˝infinity) (˝VNil)).

Definition seq_sec : Exp :=
  ELet 1 (°EApp (˝@map_clos ident) [˝f_clos; ˝VVar 2])
             receive.

Print EReceive.
Lemma receive_closed :
  EXP 1 ⊢ receive.
Proof.
  repeat constructor; simpl. 2: lia.
  destruct i. 2: lia.
  simpl. intros. do 4 scope_solver_step.
  1, 2: scope_solver.
  1-2: destruct i; intros.
  2, 4: destruct i; try lia.
  all: simpl. 1-2: scope_solver.
  all: do 3 scope_solver_step.
  1: scope_solver.
  1: scope_solver_step.
  1: scope_solver.
  all: try destruct i; intros.
  1, 3, 5, 7: simpl. 1-3:scope_solver.
  1: do 10 scope_solver_step.
  all: do 8 scope_solver_step.
  all: intros; destruct i; try destruct i; try destruct i.
  all: do 2 scope_solver_step. lia.
  all: intros; destruct i; try destruct i; try destruct i.
  all: scope_solver.
Qed.

Hint Resolve receive_closed : examples.

Definition send_body : Exp :=
  (°ECall (˝erlang) (˝send) [˝VVar 0; °EApp (˝@map_clos ident) [˝f_clos; ˝VVar 1]]).

Definition par_map : Redex :=
  ECase (ECall (˝VLit "lists") (˝VLit "split") [˝VLit (Z.of_nat idx); ˝l])
    [
      ([PTuple [PVar; PVar]], ˝ttrue,
        °ELet 1 (°ECall (˝erlang) (˝self) [])
          (°ESeq 
            (°ECall (˝erlang) (˝spawn) [
             °EFun 2 send_body;
             °ECons (˝VVar 0) (°ECons (˝VVar 1) (˝VNil))])
          (
            seq_sec
          )
        )
      )
    ].

Lemma take_helper1 :
  VALCLOSED (meta_to_cons (take idx l')).
Proof.
  apply meta_to_cons_closed.
  apply mk_list_closed with (Γ := 0) in l_is_proper. 2: assumption.
  by apply Forall_take.
Qed.

Lemma take_helper2 :
  VALCLOSED (meta_to_cons (map f (take idx l'))).
Proof.
  apply meta_to_cons_closed.
  apply mk_list_closed with (Γ := 0) in l_is_proper. 2: assumption.
  apply list.Forall_forall. intros. apply elem_of_map_iff in H.
  destruct_hyps. subst.
  apply f_closed. rewrite list.Forall_forall in l_is_proper.
  apply l_is_proper. clear-H0.
  pose proof subseteq_take idx l'. set_solver.
Qed.

Lemma drop_helper1 :
  VALCLOSED (meta_to_cons (drop idx l')).
Proof.
  apply meta_to_cons_closed.
  apply mk_list_closed with (Γ := 0) in l_is_proper. 2: assumption.
  by apply Forall_drop.
Qed.

Lemma drop_helper2 :
  VALCLOSED (meta_to_cons (map f (drop idx l'))).
Proof.
  apply meta_to_cons_closed.
  apply mk_list_closed with (Γ := 0) in l_is_proper. 2: assumption.
  apply list.Forall_forall. intros. apply elem_of_map_iff in H.
  destruct_hyps. subst.
  apply f_closed. rewrite list.Forall_forall in l_is_proper.
  apply l_is_proper. clear-H0.
  pose proof subseteq_drop idx l'. set_solver.
Qed.

Lemma bisim_helper : forall ι_base, ι_base <> ι -> (∅,
 ι_base
 ↦ inl
     ([FParams (IPrimOp "recv_peek_message") [] [];
       FLet 2
         (° ECase (˝ VVar 0)
              [([PLit "true"], ˝ VLit "true",
                ° ECase (˝ VVar 1)
                    [([PVar], ˝ VLit "true",
                      ° ESeq (° EPrimOp "remove_message" [])
                          (° ECall (˝ VLit "erlang") (˝ VLit "!")
                               [˝ VPid ι;
                                ° ECall (˝ VLit "erlang") (˝ VLit "++")
                                    [˝ VVar 0; ˝ meta_to_cons (map f (drop idx l'))]]));
                     ([PVar], ˝ VLit "true",
                      ° ESeq (° EPrimOp "recv_next" [])
                          (° EApp
                               (˝ VClos
                                    [(0, 0,
                                      ° ELet 2 (° EPrimOp "recv_peek_message" [])
                                          (° ECase (˝ VVar 0)
                                               [([PLit "true"], ˝ 
                                                 VLit "true",
                                                 ° ECase (˝ VVar 1)
                                                     [([PVar], ˝ 
                                                       VLit "true",
                                                       ° ESeq
                                                           (° EPrimOp "remove_message" [])
                                                           (° 
                                                            ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                      ([PVar], ˝ 
                                                       VLit "true",
                                                       ° ESeq 
                                                           (° EPrimOp "recv_next" [])
                                                           (° EApp (˝ VFunId (3, 0)) []))]);
                                                ([PLit "false"], ˝ 
                                                 VLit "true",
                                                 ° ELet 1
                                                     (° EPrimOp "recv_wait_timeout"
                                                          [˝ VLit "infinity"])
                                                     (° ECase 
                                                          (˝ VVar 0)
                                                          [([PLit "true"], ˝ 
                                                            VLit "true", ˝ VNil);
                                                           ([PLit "false"], ˝ 
                                                            VLit "true",
                                                            ° 
                                                            EApp (˝ VFunId (3, 0)) [])]))]))]
                                    0 0
                                    (° ELet 2 (° EPrimOp "recv_peek_message" [])
                                         (° ECase (˝ VVar 0)
                                              [([PLit "true"], ˝ 
                                                VLit "true",
                                                ° ECase (˝ VVar 1)
                                                    [([PVar], ˝ 
                                                      VLit "true",
                                                      ° ESeq
                                                          (° EPrimOp "remove_message" [])
                                                          (° ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                     ([PVar], ˝ 
                                                      VLit "true",
                                                      ° ESeq (° EPrimOp "recv_next" [])
                                                          (° EApp (˝ VFunId (3, 0)) []))]);
                                               ([PLit "false"], ˝ 
                                                VLit "true",
                                                ° ELet 1
                                                    (° EPrimOp "recv_wait_timeout"
                                                         [˝ VLit "infinity"])
                                                    (° ECase (˝ VVar 0)
                                                         [([PLit "true"], ˝ 
                                                           VLit "true", ˝ VNil);
                                                          ([PLit "false"], ˝ 
                                                           VLit "true",
                                                           ° EApp (˝ VFunId (3, 0)) [])]))])))
                               []))]);
               ([PLit "false"], ˝ VLit "true",
                ° ELet 1 (° EPrimOp "recv_wait_timeout" [˝ VLit "infinity"])
                    (° ECase (˝ VVar 0)
                         [([PLit "true"], ˝ VLit "true", ˝ VNil);
                          ([PLit "false"], ˝ VLit "true",
                           ° EApp
                               (˝ VClos
                                    [(0, 0,
                                      ° ELet 2 (° EPrimOp "recv_peek_message" [])
                                          (° ECase (˝ VVar 0)
                                               [([PLit "true"], ˝ 
                                                 VLit "true",
                                                 ° ECase (˝ VVar 1)
                                                     [([PVar], ˝ 
                                                       VLit "true",
                                                       ° ESeq
                                                           (° EPrimOp "remove_message" [])
                                                           (° 
                                                            ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                      ([PVar], ˝ 
                                                       VLit "true",
                                                       ° ESeq 
                                                           (° EPrimOp "recv_next" [])
                                                           (° EApp (˝ VFunId (3, 0)) []))]);
                                                ([PLit "false"], ˝ 
                                                 VLit "true",
                                                 ° ELet 1
                                                     (° EPrimOp "recv_wait_timeout"
                                                          [˝ VLit "infinity"])
                                                     (° ECase 
                                                          (˝ VVar 0)
                                                          [([PLit "true"], ˝ 
                                                            VLit "true", ˝ VNil);
                                                           ([PLit "false"], ˝ 
                                                            VLit "true",
                                                            ° 
                                                            EApp (˝ VFunId (3, 0)) [])]))]))]
                                    0 0
                                    (° ELet 2 (° EPrimOp "recv_peek_message" [])
                                         (° ECase (˝ VVar 0)
                                              [([PLit "true"], ˝ 
                                                VLit "true",
                                                ° ECase (˝ VVar 1)
                                                    [([PVar], ˝ 
                                                      VLit "true",
                                                      ° ESeq
                                                          (° EPrimOp "remove_message" [])
                                                          (° ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                     ([PVar], ˝ 
                                                      VLit "true",
                                                      ° ESeq (° EPrimOp "recv_next" [])
                                                          (° EApp (˝ VFunId (3, 0)) []))]);
                                               ([PLit "false"], ˝ 
                                                VLit "true",
                                                ° ELet 1
                                                    (° EPrimOp "recv_wait_timeout"
                                                         [˝ VLit "infinity"])
                                                    (° ECase (˝ VVar 0)
                                                         [([PLit "true"], ˝ 
                                                           VLit "true", ˝ VNil);
                                                          ([PLit "false"], ˝ 
                                                           VLit "true",
                                                           ° EApp (˝ VFunId (3, 0)) [])]))])))
                               [])]))])], RBox,
      ([], [meta_to_cons (map f (take idx l'))]), ∅, false) ∥ ∅) ~
(∅,
 ι_base
 ↦ inl
     ([FParams (ICall (VLit "erlang") (VLit "!")) [VPid ι] []], RValSeq [
      meta_to_cons (map f l')], emptyBox, ∅, false) ∥ ∅) observing {[ι]}.
Proof.

Admitted.

Lemma eval_helper_peek_message :
  inl
  ([FParams (IPrimOp "recv_peek_message") [] [];
    FLet 2
      (° ECase (˝ VVar 0)
           [([PLit "true"], ˝ VLit "true",
             ° ECase (˝ VVar 1)
                 [([PVar], ˝ VLit "true",
                   ° ESeq (° EPrimOp "remove_message" [])
                       (° ECall (˝ VLit "erlang") (˝ VLit "!")
                            [˝ VPid ι;
                             ° ECall (˝ VLit "erlang") (˝ VLit "++")
                                 [˝ VVar 0; ˝ meta_to_cons (map f (drop idx l'))]]));
                  ([PVar], ˝ VLit "true",
                   ° ESeq (° EPrimOp "recv_next" [])
                       (° EApp
                            (˝ VClos
                                 [(0, 0,
                                   ° ELet 2 (° EPrimOp "recv_peek_message" [])
                                       (° ECase (˝ VVar 0)
                                            [([PLit "true"], ˝ 
                                              VLit "true",
                                              ° ECase (˝ VVar 1)
                                                  [([PVar], ˝ 
                                                    VLit "true",
                                                    ° ESeq (° EPrimOp "remove_message" [])
                                                        (° ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [
                                                             ˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                   ([PVar], ˝ 
                                                    VLit "true",
                                                    ° ESeq (° EPrimOp "recv_next" [])
                                                        (° EApp (˝ VFunId (3, 0)) []))]);
                                             ([PLit "false"], ˝ 
                                              VLit "true",
                                              ° ELet 1
                                                  (° EPrimOp "recv_wait_timeout"
                                                       [˝ VLit "infinity"])
                                                  (° ECase (˝ VVar 0)
                                                       [([PLit "true"], ˝ 
                                                         VLit "true", ˝ VNil);
                                                        ([PLit "false"], ˝ 
                                                         VLit "true",
                                                         ° EApp (˝ VFunId (3, 0)) [])]))]))]
                                 0 0
                                 (° ELet 2 (° EPrimOp "recv_peek_message" [])
                                      (° ECase (˝ VVar 0)
                                           [([PLit "true"], ˝ 
                                             VLit "true",
                                             ° ECase (˝ VVar 1)
                                                 [([PVar], ˝ VLit "true",
                                                   ° ESeq (° EPrimOp "remove_message" [])
                                                       (° ECall 
                                                            (˝ VLit "erlang") 
                                                            (˝ VLit "!")
                                                            [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                  ([PVar], ˝ VLit "true",
                                                   ° ESeq (° EPrimOp "recv_next" [])
                                                       (° EApp (˝ VFunId (3, 0)) []))]);
                                            ([PLit "false"], ˝ 
                                             VLit "true",
                                             ° ELet 1
                                                 (° EPrimOp "recv_wait_timeout"
                                                      [˝ VLit "infinity"])
                                                 (° ECase (˝ VVar 0)
                                                      [([PLit "true"], ˝ 
                                                        VLit "true", ˝ VNil);
                                                       ([PLit "false"], ˝ 
                                                        VLit "true",
                                                        ° EApp (˝ VFunId (3, 0)) [])]))])))
                            []))]);
            ([PLit "false"], ˝ VLit "true",
             ° ELet 1 (° EPrimOp "recv_wait_timeout" [˝ VLit "infinity"])
                 (° ECase (˝ VVar 0)
                      [([PLit "true"], ˝ VLit "true", ˝ VNil);
                       ([PLit "false"], ˝ VLit "true",
                        ° EApp
                            (˝ VClos
                                 [(0, 0,
                                   ° ELet 2 (° EPrimOp "recv_peek_message" [])
                                       (° ECase (˝ VVar 0)
                                            [([PLit "true"], ˝ 
                                              VLit "true",
                                              ° ECase (˝ VVar 1)
                                                  [([PVar], ˝ 
                                                    VLit "true",
                                                    ° ESeq (° EPrimOp "remove_message" [])
                                                        (° ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [
                                                             ˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                   ([PVar], ˝ 
                                                    VLit "true",
                                                    ° ESeq (° EPrimOp "recv_next" [])
                                                        (° EApp (˝ VFunId (3, 0)) []))]);
                                             ([PLit "false"], ˝ 
                                              VLit "true",
                                              ° ELet 1
                                                  (° EPrimOp "recv_wait_timeout"
                                                       [˝ VLit "infinity"])
                                                  (° ECase (˝ VVar 0)
                                                       [([PLit "true"], ˝ 
                                                         VLit "true", ˝ VNil);
                                                        ([PLit "false"], ˝ 
                                                         VLit "true",
                                                         ° EApp (˝ VFunId (3, 0)) [])]))]))]
                                 0 0
                                 (° ELet 2 (° EPrimOp "recv_peek_message" [])
                                      (° ECase (˝ VVar 0)
                                           [([PLit "true"], ˝ 
                                             VLit "true",
                                             ° ECase (˝ VVar 1)
                                                 [([PVar], ˝ VLit "true",
                                                   ° ESeq (° EPrimOp "remove_message" [])
                                                       (° ECall 
                                                            (˝ VLit "erlang") 
                                                            (˝ VLit "!")
                                                            [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                  ([PVar], ˝ VLit "true",
                                                   ° ESeq (° EPrimOp "recv_next" [])
                                                       (° EApp (˝ VFunId (3, 0)) []))]);
                                            ([PLit "false"], ˝ 
                                             VLit "true",
                                             ° ELet 1
                                                 (° EPrimOp "recv_wait_timeout"
                                                      [˝ VLit "infinity"])
                                                 (° ECase (˝ VVar 0)
                                                      [([PLit "true"], ˝ 
                                                        VLit "true", ˝ VNil);
                                                       ([PLit "false"], ˝ 
                                                        VLit "true",
                                                        ° EApp (˝ VFunId (3, 0)) [])]))])))
                            [])]))])], RBox, ([], [meta_to_cons (map f (take idx l'))]),
   ∅, false) -⌈ repeat τ 34 ⌉->* inl
     ([FParams (ICall (VLit "erlang") (VLit "!")) [VPid ι] []], RValSeq [
      meta_to_cons (map f l')], emptyBox, ∅, false).
Proof.
  eapply lsstep. apply p_recv_peek_message_ok. reflexivity.
  eapply lsstep. apply p_local. constructor. reflexivity.
  simpl.
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. constructor. scope_solver.
  eapply lsstep. apply p_local. apply eval_step_case_match. reflexivity.
  eapply lsstep. apply p_local. constructor. scope_solver.
  eapply lsstep. apply p_local. apply eval_step_case_true. simpl.
  rewrite idsubst_is_id_val. simpl.
  repeat rewrite vclosed_ignores_ren; try apply drop_helper2.
  repeat rewrite vclosed_ignores_sub; try apply drop_helper2.
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. constructor.
  1: { apply take_helper2. }
  eapply lsstep. apply p_local. apply eval_step_case_match. reflexivity.
  eapply lsstep. apply p_local. constructor. scope_solver.
  eapply lsstep. apply p_local. apply eval_step_case_true. simpl.
  (* remove message from the mailbox *)
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_remove_message. by cbn.
  eapply lsstep. apply p_local. constructor.
  repeat rewrite vclosed_ignores_sub; try apply drop_helper2.
  (* Reading configurations is easier from here *)
  (* evaluate send *)
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. constructor. scope_solver.
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. constructor. scope_solver.
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. constructor. congruence.
  eapply lsstep. apply p_local. constructor. scope_solver.
  eapply lsstep. apply p_local. constructor.
  (* evaluate append *)
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. constructor. scope_solver.
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. constructor. scope_solver.
  eapply lsstep. apply p_local. constructor. simpl.
  eapply lsstep. apply p_local. constructor. congruence.
  eapply lsstep. apply p_local. constructor.
  1: apply take_helper2.
  eapply lsstep. apply p_local. constructor. simpl.
  repeat rewrite vclosed_ignores_sub; try apply drop_helper2.
  eapply lsstep. apply p_local. constructor. apply drop_helper2.
  eapply lsstep. apply p_local. econstructor.
  { (* evaluate the meta-theoretical simulated append *)
    simpl. cbn.
    rewrite eval_append_correct.
    rewrite <- map_app, take_drop. reflexivity.
  }
  apply lsrefl.
Qed.


(* Implicit assumptions with this definition:
   - Only the child communicates, there are no other messages awaiting to
     be processed by the parent process!!!
   - If the equivalence is based on the empty ether, errors are rules out!!!
*)

Context (ι_base : PID)
        (Hbase : ι_base <> ι).

Opaque eval_split.
Opaque seq_sec.
Opaque map_clos.
Theorem split_eval O :
  exists l,
    (∅, ι_base ↦ inl ([], par_map, emptyBox, ∅, false) ∥ ∅) -[l]ₙ->* 
    (∅, ι_base ↦ inl ([FParams (ICall erlang spawn) [VClos [] 0 2 send_body] [];FSeq seq_sec.[up_subst
                (meta_to_cons (take idx l') .: meta_to_cons (drop idx l') .: idsubst)].[
     VPid ι_base/] ], RValSeq [VCons (VPid ι_base) (VCons (meta_to_cons (take idx l')) VNil)], emptyBox, ∅, false) ∥ ∅) with O /\
    Forall (fun x => x.1 = τ \/ exists ι, x.1 = ASelf ι) l.
Proof.
  eexists. split.
  {
    eapply closureNodeSem_trans.
    * apply sequential_to_node.
      do 10 do_step.
      econstructor 2. econstructor. reflexivity. simpl.
      unfold eval_transform_list. simpl.
      erewrite eval_split_correct. 2-3: eassumption.
      do 9 do_step.
      rewrite vclosed_ignores_sub; auto with examples.
      rewrite vclosed_ignores_sub; auto with examples.
      constructor.
    * eapply n_trans. apply n_other with (ι := ι_base) (a := ASelf ι_base).
      2: set_solver.
      constructor.
      apply sequential_to_node.
      do 11 do_step.
      rewrite vclosed_ignores_sub; auto with examples.
      rewrite vclosed_ignores_sub; auto with examples.
      rewrite vclosed_ignores_ren; auto with examples.
      2: {
        apply meta_to_cons_closed.
        apply mk_list_closed with (Γ := 0) in l_is_proper. 2: assumption.
        by apply Forall_take.
      }
      rewrite vclosed_ignores_sub; auto with examples.
      2: {
        apply meta_to_cons_closed.
        apply mk_list_closed with (Γ := 0) in l_is_proper. 2: assumption.
        by apply Forall_take.
      }
      do 4 do_step.
      {
        apply meta_to_cons_closed.
        apply mk_list_closed with (Γ := 0) in l_is_proper. 2: assumption.
        by apply Forall_take.
      }
      do 4 do_step.
      constructor.
  }
  {
    apply Forall_app. split. 2: constructor.
    1, 3: by apply Forall_repeat; left.
    right. by eexists.
  }
Qed.
Transparent eval_split.
Transparent seq_sec.


Definition map_seq_send :Exp :=
  °ECall (˝erlang) (˝send)
       [
        ˝VPid ι;
        °EApp (˝@map_clos ident) [˝f_clos; ˝l]
       ].

Opaque receive.
(* NOTE: coercions start to tangle up here for parsing *)
Theorem map_pmap_bisim_empty_ether :
  (∅, ι_base ↦ inl ([], RExp (map_seq_send), emptyBox, ∅, false) ∥ ∅) ~
  (∅, ι_base ↦ inl ([], par_map, emptyBox, ∅, false) ∥ ∅) observing {[ι]}.
Proof.
  opose proof* (@map_clos_eval l l' ident f f_clos).
  all:try assumption. destruct H as [mapₖ [Hres HD]].
  pose proof split_eval {[ι]}. destruct H as [pmapₗ [HD2 Hₗ]].
  eapply barbedBisim_trans.
  eapply normalisation_τ_many_bisim.
  2: set_solver.
  2: {
    apply sequential_to_node.
    do 8 do_step.
    eapply frame_indep_core in HD.
    exact HD.
  }
  1: by apply Forall_repeat.
  simpl.
  eapply barbedBisim_trans.
  2: {
    apply barbedBisim_sym. eapply normalisation_τ_self_many_bisim.
    3: exact HD2.
    1: assumption.
    set_solver.
  }
  constructor.
  2,4: intros; exists source, []; eexists; simpl; split; try by constructor.
  { (* sequential process gets a signal (which can only be a send)
       In this case, the entire concurrent map has to be evaluated!
     *)
    intros. assert (ι0 = ι_base). {
      destruct A'.
      apply deconstruct_reduction in H. destruct_hyps.
      put (lookup ι0 : ProcessPool -> _) on H as H'.
      setoid_rewrite lookup_insert in H'. destruct (decide (ι0 = ι_base)).
      assumption.
      setoid_rewrite lookup_insert_ne in H'; auto. set_solver.
    }
    subst.
    assert (a = ASend ι_base ι (SMessage (meta_to_cons (map f l')))). {
      inv H.
      * put (lookup ι_base : ProcessPool -> _) on H2 as P.
        setoid_rewrite lookup_insert in P. inv P. by inv H5.
      * unfold etherPop in H2. repeat case_match; try congruence.
        set_solver.
      * put (lookup ι_base : ProcessPool -> _) on H1 as P.
        setoid_rewrite lookup_insert in P. inv P.
        destruct_or! H6; inv H2; try inv H9; cbn in *; try congruence.
      * put (lookup ι_base : ProcessPool -> _) on H1 as P.
        setoid_rewrite lookup_insert in P. inv P.
        inv H2. inv H10.
    }
    subst. inv H. 2: { destruct_or! H6; congruence. } clear H1.
    put (lookup ι_base : ProcessPool -> _) on H2 as P.
    setoid_rewrite lookup_insert in P. inv P. inv H7. 
    (* prs = ∅ *)
    assert (forall p, ι_base ↦ p ∥ prs = ι_base ↦ p ∥ ∅) as X. {
      intros.
      apply map_eq. intros. put (lookup i : ProcessPool -> _) on H2 as D.
      destruct (decide (i = ι_base)).
      * subst. by setoid_rewrite lookup_insert.
      * setoid_rewrite lookup_insert_ne in D; auto.
        by setoid_rewrite lookup_insert_ne.
    }
    clear H2.
    (* To be able to use eexists, we need to pose map evaluation first! *)
    opose proof* (@map_clos_eval (meta_to_cons (take idx l')) (take idx l') ident f f_clos) as InitEval.
    all: try eassumption.
    1: apply meta_to_cons_mk_list.
    1: { apply take_helper1. }
    opose proof* (@map_clos_eval (meta_to_cons (drop idx l')) (drop idx l') ident f f_clos) as TailEval.
    all: try eassumption.
    1: apply meta_to_cons_mk_list.
    1: { apply drop_helper1. }
    destruct InitEval as [Initₖ [InitRes InitEval]].
    destruct TailEval as [Tailₖ [TailRes TailEval]].
    (**)
    do 2 eexists. split.
    {
      (* reductions *)
      eapply n_trans.
      (* spawning the new process *)
      pose proof (infinite_is_fresh (ι :: ι_base :: elements (usedPIDsVal f_clos))) as HF.
      eapply n_spawn with (ι := ι_base) (ι' := fresh (app [ι; ι_base] (elements (usedPIDsVal f_clos)))).
      2: { clear-HF. set_solver. }
      2: {
         (* revise fresh generation on the ether + pool! that will 
                  also be future proof for general ethers *)
          intro. apply isUsedPool_insert_1 in H. destruct_or!.
          * setoid_rewrite delete_empty in H.
            destruct H. set_solver. destruct_hyps. set_solver.
          * pose proof (infinite_is_fresh (ι :: ι_base :: elements (usedPIDsVal f_clos))). set_solver.
          * unfold usedPIDsProc in H. cbn in H.
            rewrite vclosed_ignores_sub in H; auto with examples.
            rewrite vclosed_ignores_sub in H; auto with examples.
Transparent receive.
Transparent map_clos.
            unfold map_clos, map_body in H. simpl in *.
            rewrite vclosed_ignores_sub in H; auto with examples.
            rewrite vclosed_ignores_sub in H; auto with examples.
            rewrite vclosed_ignores_ren in H; auto with examples.
            rewrite vclosed_ignores_sub in H; auto with examples.
            2-3: apply drop_helper1.
            assert (usedPIDsVal (meta_to_cons (take idx l')) = ∅). {
              clear -l_is_free_of_PIDs. revert l' l_is_free_of_PIDs.
              induction idx; intros; destruct l'; simpl.
              1-3: set_solver.
              cbn in *. set_solver.
            }
            assert (usedPIDsVal (meta_to_cons (drop idx l')) = ∅). {
              clear -l_is_free_of_PIDs. revert l' l_is_free_of_PIDs.
              induction idx; intros; destruct l'; simpl.
              1-3: set_solver.
              cbn in *. set_solver.
            }
            rewrite H0, H1 in H.
            clear-H.
            pose proof (infinite_is_fresh (ι :: ι_base :: elements (usedPIDsVal f_clos))).
            set_solver.
Opaque receive.
Opaque map_clos.
      }
      2: {
        (* revise fresh generation on the ether + pool! that will 
                  also be future proof for general ethers *)
        clear. intro. destruct H. 2: destruct H.
        * destruct H, H. set_solver.
        * destruct H. set_solver.
        * destruct_hyps. set_solver.
      }
      3: {
        constructor. reflexivity.
      }
      1: {
        simpl. reflexivity.
      }
      1: {
        simpl. reflexivity.
      }
      rewrite vclosed_ignores_sub; auto with examples.
      rewrite vclosed_ignores_sub; auto with examples.
      (* map is evaluated in the spawned process *)
      eapply closureNodeSem_trans.
      {
        apply sequential_to_node.
        do 8 do_step.
        eapply frame_indep_core in InitEval.
        exact InitEval.
      }
      simpl.
      repeat rewrite (vclosed_ignores_sub map_clos); auto with examples.
      repeat rewrite (vclosed_ignores_sub f_clos); auto with examples.
      repeat rewrite vclosed_ignores_ren; auto.
      2: { apply drop_helper1. }
      (* map is sent back to the parent *)
      eapply n_trans. eapply n_send. constructor.
      { apply take_helper2. }
      (* map arrives to the parent *)
      setoid_rewrite insert_commute.
      2: {
        pose proof (infinite_is_fresh (ι :: ι_base :: elements (usedPIDsVal f_clos))).
        set_solver.
      }
      eapply n_trans. apply n_arrive with (ι0 := fresh (ι :: ι_base :: elements (usedPIDsVal f_clos))).
      {
        unfold etherAdd, etherPop.
        setoid_rewrite lookup_empty.
        setoid_rewrite lookup_insert.
        setoid_rewrite lookup_empty.
        setoid_rewrite insert_insert.
        reflexivity.
      }
      {
        constructor.
      }
      (* parent evaluates the map *)
      eapply closureNodeSem_trans.
      {
        apply sequential_to_node.
        do 2 do_step.
        rewrite vclosed_ignores_sub.
        2: { apply drop_helper1. }
        eapply frame_indep_core in TailEval.
        eapply transitive_eval. exact TailEval.
        simpl. do_step.
        constructor.
      }
      (* parent receives the first part of the map
        This is painful :(
      *)
      eapply closureNodeSem_trans.
      {
        eapply process_local_to_node.
        {
  Transparent receive.
          unfold receive, EReceive. simpl.
          repeat rewrite vclosed_ignores_ren; try apply drop_helper2.
          eapply lsstep. constructor. constructor. cbn. reflexivity.
          cbn.
          eapply lsstep. do 2 constructor.
          eapply lsstep. do 2 constructor.
          1: {
            opose proof* (EReceive_scope ([([PVar], ˝ VLit "true",
                                  ° ECall (˝ VLit "erlang") (˝ VLit "!")
                                      [˝ VPid ι;
                                       ° ECall (˝ VLit "erlang") 
                                           (˝ VLit "++")
                                           [˝ VVar 0; ˝ meta_to_cons (map f (drop idx l'))]])]) (˝VLit "infinity"%string) (˝VNil) 0).
            2-3: scope_solver.
            {
              constructor; auto. split. scope_solver.
              do 6 scope_solver_step.
              all: intros; destruct i; try destruct i; try destruct i.
              1,3-5,7-9,11-12: scope_solver.
              1: scope_solver_step; eapply loosen_scope_val; try apply drop_helper2; lia.
              all: do 6 scope_solver_step.
            }
            inv H. inv H2. constructor; auto.
            intros. simpl in *.
            specialize (H3 0 ltac:(lia)). simpl in H3. apply H3.
          }
          eapply lsstep. do 2 constructor.
          eapply lsstep. apply p_local. econstructor. congruence. reflexivity.
          simpl.
          eapply lsstep. apply p_local. constructor.
          eapply lsstep. apply p_local. constructor.
          repeat rewrite vclosed_ignores_ren; try apply drop_helper2.
          repeat rewrite vclosed_ignores_sub; try apply drop_helper2.
          apply eval_helper_peek_message.
        }
        {
          repeat constructor.
        }
      }
      (* parent sends the result *)
      eapply n_trans. apply n_send. constructor. assumption.
      (* the child process should be terminated for the equivalence *)
      setoid_rewrite insert_commute.
      2: {
        clear. pose proof (infinite_is_fresh (ι :: ι_base :: elements (usedPIDsVal f_clos))).
        set_solver.
      }
      eapply n_trans. apply n_other. apply p_terminate. by clear; set_solver.
      setoid_rewrite gset_to_gmap_empty.
      apply n_refl.
    }
    { (* equivalence - we need two helpers about dead processes and ether inserts *)
      rewrite X.
      eapply barbedBisim_trans.
      apply dead_process_bisim with (ι := fresh (ι :: ι_base :: elements (usedPIDsVal f_clos))).
      1: clear; pose proof (infinite_is_fresh (ι :: ι_base :: elements (usedPIDsVal f_clos))); set_solver.
      1: clear; pose proof (infinite_is_fresh (ι :: ι_base :: elements (usedPIDsVal f_clos))); set_solver.
      simpl. (* now the pools are equal, we have to do the same for the ethers *)
      unfold etherAdd. setoid_rewrite lookup_empty.
      setoid_rewrite lookup_insert_ne.
      2: clear; pose proof (infinite_is_fresh (ι :: ι_base :: elements (usedPIDsVal f_clos))); set_solver.
      setoid_rewrite lookup_empty.
      setoid_rewrite insert_commute at 2.
      2: clear; pose proof (infinite_is_fresh (ι :: ι_base :: elements (usedPIDsVal f_clos))); set_solver.
      remember (_ ↦ _ ∥ _ ↦ _ ∥ ∅) as P.
      setoid_rewrite <- HeqP.
      remember (insert (ι_base, ι) _ ∅) as E.
      apply ether_empty_update_bisim.
      clear-Hbase. set_solver.
      simpl. subst E. left.
      setoid_rewrite lookup_insert_ne. set_solver.
      set_solver.
    }
  }
  {
    Opaque receive.
    opose proof* (@map_clos_eval (meta_to_cons (take idx l')) (take idx l') ident f f_clos) as InitEval.
    all: try eassumption.
    1: apply meta_to_cons_mk_list.
    1: { apply take_helper1. }
    opose proof* (@map_clos_eval (meta_to_cons (drop idx l')) (drop idx l') ident f f_clos) as TailEval.
    all: try eassumption.
    1: apply meta_to_cons_mk_list.
    1: { apply drop_helper1. }
    destruct InitEval as [Initₖ [InitRes InitEval]].
    destruct TailEval as [Tailₖ [TailRes TailEval]].

    intros. eexists. exists []. split. eapply n_refl.
    intros. assert (ι0 = ι_base). {
      destruct B'.
      apply deconstruct_reduction in H. destruct_hyps.
      put (lookup ι0 : ProcessPool -> _) on H as H'.
      setoid_rewrite lookup_insert in H'. destruct (decide (ι0 = ι_base)).
      assumption.
      setoid_rewrite lookup_insert_ne in H'; auto. set_solver.
    }
    subst.
    assert (exists ι_new, a = ASpawn ι_new (VClos [] 0 2 send_body) (VCons (VPid ι_base) (VCons (meta_to_cons (take idx l')) VNil)) false). {
      inv H.
      * put (lookup ι_base : ProcessPool -> _) on H2 as P.
        setoid_rewrite lookup_insert in P. inv P. by inv H5.
      * unfold etherPop in H2. repeat case_match; try congruence.
        set_solver.
      * put (lookup ι_base : ProcessPool -> _) on H1 as P.
        setoid_rewrite lookup_insert in P. inv P.
        destruct_or! H6; inv H2; try inv H9; cbn in *; try congruence.
      * put (lookup ι_base : ProcessPool -> _) on H1 as P.
        setoid_rewrite lookup_insert in P. inv P.
        inv H2. inv H10. by eexists.
    }
    destruct H0; subst. inv H. destruct_or! H6; congruence.
    put (lookup ι_base : ProcessPool -> _) on H1 as HX.
    setoid_rewrite lookup_insert in HX. inv HX. simpl in *. inv H6.
    simpl in H12. inv H12.
    assert (forall p, ι_base ↦ p ∥ Π = ι_base ↦ p ∥ ∅) as X. {
      intros. apply map_eq. intros.
      put (lookup i : ProcessPool -> _) on H1 as X.
        destruct (decide (i = ι_base)).
        - subst. by setoid_rewrite lookup_insert.
        - setoid_rewrite lookup_insert_ne; auto.
          by setoid_rewrite lookup_insert_ne in X.
    }
    rewrite X. rewrite X in H10.
    inv H13. clear H15.
    clear H1. clear HD2.
    assert (x ≠ ι_base) as Heqx. {
      intro. subst. apply H10.
      left. by setoid_rewrite lookup_insert.
    }
    eapply barbedBisim_trans.
    2: {
      apply barbedBisim_sym.
      eapply normalisation_τ_many_bisim.
      2 :{
        repeat setoid_rewrite dom_insert_L. set_solver.
      }
      1: shelve.
      eapply closureNodeSem_trans.
      { (* parent map *)
        eapply sequential_to_node.
        repeat rewrite (vclosed_ignores_sub); auto with examples.
        do 8 do_step.
        eapply frame_indep_core in InitEval as InitEval'.
        simpl. apply InitEval'.
      }
      { (* child map *)
        setoid_rewrite insert_commute; auto.
        eapply sequential_to_node.
        repeat rewrite (vclosed_ignores_sub); auto with examples.
        2: repeat rewrite vclosed_ignores_ren; auto. 2-3: apply drop_helper1.
        do 2 do_step.
        repeat rewrite vclosed_ignores_ren; auto. 2: apply drop_helper1.
        eapply frame_indep_core in TailEval as TailEval'.
        eapply transitive_eval.
        apply TailEval'.
        simpl. do 4 do_step.
        1: {
            repeat rewrite (vclosed_ignores_ren); auto with examples.
            all: try apply drop_helper2.
            opose proof* (EReceive_scope ([([PVar], ˝ VLit "true",
                                  ° ECall (˝ VLit "erlang") (˝ VLit "!")
                                      [˝ VPid ι;
                                       ° ECall (˝ VLit "erlang") 
                                           (˝ VLit "++")
                                           [˝ VVar 0; ˝ meta_to_cons (map f (drop idx l'))]])]) (˝VLit "infinity"%string) (˝VNil) 0).
            2-3: scope_solver.
            {
              constructor; auto. split. scope_solver.
              do 6 scope_solver_step.
              all: intros; destruct i; try destruct i; try destruct i.
              1,3-5,7-9,11-12: scope_solver.
              1: scope_solver_step; eapply loosen_scope_val; try apply drop_helper2; lia.
              all: do 6 scope_solver_step.
            }
            inv H. inv H2. constructor; auto.
            intros. simpl in *.
            specialize (H3 0 ltac:(lia)). simpl in H3. simpl. apply H3.
        }
        do_step.
        repeat rewrite (vclosed_ignores_sub); auto with examples.
        econstructor 2. econstructor. congruence. reflexivity.
        repeat rewrite (vclosed_ignores_sub); auto with examples.
        repeat rewrite (vclosed_ignores_ren); auto with examples.
        all: try apply drop_helper2. simpl.
        do_step.
        repeat rewrite (vclosed_ignores_sub); auto with examples.
        repeat rewrite (vclosed_ignores_ren); auto with examples.
        all: try apply drop_helper2. simpl.
        do_step. constructor 1.
      }
    }
    (* child send - we have to reason about this with the definition of bisim.
       it would be simpler to use simulation equivalence, since again we have to
       prove both directions
     *)
    rewrite (vclosed_ignores_sub) in H10; auto with examples.
    rewrite (vclosed_ignores_sub) in H10; auto with examples.
    rewrite (vclosed_ignores_sub) in H10; auto with examples.
    rewrite (vclosed_ignores_sub) in H10; auto with examples.
    rewrite (vclosed_ignores_ren) in H10; auto with examples.
    rewrite (vclosed_ignores_sub) in H10; auto with examples.
    2-3: apply drop_helper1.
    constructor.
    2,4: intros; exists source, []; eexists; simpl; split; try by constructor.
    * (* -> direction, we have already proved this *)
      intros. assert (ι0 = ι_base). {
        destruct A'.
        apply deconstruct_reduction in H. destruct_hyps.
        put (lookup ι0 : ProcessPool -> _) on H as H'.
        setoid_rewrite lookup_insert in H'. destruct (decide (ι0 = ι_base)).
        assumption.
        setoid_rewrite lookup_insert_ne in H'; auto. set_solver.
      }
      subst.
      assert (a = ASend ι_base ι (SMessage (meta_to_cons (map f l')))). {
        inv H.
        * put (lookup ι_base : ProcessPool -> _) on H2 as P.
          setoid_rewrite lookup_insert in P. inv P. by inv H5.
        * clear-H2. unfold etherPop in H2. repeat case_match; try congruence.
          set_solver.
        * put (lookup ι_base : ProcessPool -> _) on H1 as P.
          setoid_rewrite lookup_insert in P. inv P.
          destruct_or! H6; inv H2; try inv H12; cbn in *; try congruence.
        * put (lookup ι_base : ProcessPool -> _) on H1 as P.
          setoid_rewrite lookup_insert in P. inv P.
          inv H2. inv H13.
      }
      subst. inv H. 2: { destruct_or! H6; congruence. } clear H1.
      put (lookup ι_base : ProcessPool -> _) on H2 as P.
      setoid_rewrite lookup_insert in P. inv P. inv H8.
      clear X.
      (* prs = ∅ *)
      assert (forall p, ι_base ↦ p ∥ prs = ι_base ↦ p ∥ ∅) as X. {
        intros.
        apply map_eq. intros. put (lookup i : ProcessPool -> _) on H2 as D.
        destruct (decide (i = ι_base)).
        * subst. by setoid_rewrite lookup_insert.
        * setoid_rewrite lookup_insert_ne in D; auto.
          by setoid_rewrite lookup_insert_ne.
      }
      clear H2.
      (**)
      do 2 eexists. split.
      {
        (* reductions *)
        (* map is sent back to the parent *)
        setoid_rewrite insert_commute; auto.
        eapply n_trans. eapply n_send. constructor.
        { apply take_helper2. }
        (* map arrives to the parent *)
        setoid_rewrite insert_commute.
        2: {
          pose proof (infinite_is_fresh [ι; ι_base]).
          set_solver.
        }
        eapply n_trans. apply n_arrive with (ι0 := x).
        {
          unfold etherAdd, etherPop.
          setoid_rewrite lookup_empty.
          setoid_rewrite lookup_insert.
          setoid_rewrite lookup_empty.
          setoid_rewrite insert_insert.
          reflexivity.
        }
        {
          constructor.
        }
        (* parent message peek
        *)
        eapply closureNodeSem_trans.
        {
          eapply process_local_to_node.
          {
            apply eval_helper_peek_message.
          }
          {
            repeat constructor.
          }
        }
        (* parent sends the result *)
        eapply n_trans. apply n_send. constructor. assumption.
        (* the child process should be terminated for the equivalence *)
        setoid_rewrite insert_commute.
        2: {
          set_solver.
        }
        eapply n_trans. apply n_other. apply p_terminate. by clear; set_solver.
        setoid_rewrite gset_to_gmap_empty.
        apply n_refl.
      }
      { (* equivalence - we need two helpers about dead processes and ether inserts *)
        rewrite X.
        eapply barbedBisim_trans.
        apply dead_process_bisim with (ι := x).
        1-2: set_solver.
        simpl. (* now the pools are equal, we have to do the same for the ethers *)
        unfold etherAdd. setoid_rewrite lookup_empty.
        setoid_rewrite lookup_insert_ne.
        2: set_solver.
        setoid_rewrite lookup_empty.
        setoid_rewrite insert_commute at 2.
        2: set_solver.
        remember (_ ↦ _ ∥ _ ↦ _ ∥ ∅) as P.
        setoid_rewrite <- HeqP.
        remember (insert (ι_base, ι) _ ∅) as E.
        apply ether_empty_update_bisim.
        clear-Hbase. set_solver.
        simpl. subst E. left.
        setoid_rewrite lookup_insert_ne. set_solver.
        set_solver.
      }




    * intros. simpl in *.
      (* parent could potentially peek the message queue, but the child can also
         do the message send - in both cases, we have to do the same reductions
         to finish the evaluation
       *)
      inv H.
      - (* send happens in the child *)
        put (lookup ι0 : ProcessPool -> _) on H2 as HX2.
        assert (ι0 <> ι_base). {
          intro. subst. setoid_rewrite lookup_insert in HX2. inv HX2. inv H5.
        }
        setoid_rewrite lookup_insert in HX2.
        setoid_rewrite lookup_insert_ne in HX2; auto.
        symmetry in HX2. apply lookup_insert_Some in HX2. destruct HX2 as [HX2 | HX2].
        2: { clear-HX2. set_solver. }
        destruct HX2 as [EQ1 EQ2]. inv EQ2. clear H0.
        remember (inl (_, _, _, _, _)) as recp in H2 at 2.
        assert (forall p, ι0 ↦ p ∥ prs = ι0 ↦ p ∥ ι_base ↦ recp ∥ ∅) as XX. {
          intros. apply map_eq. intros.
          destruct (decide (i = ι0)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            put (lookup i : ProcessPool -> _) on H2 as HX2.
            destruct (decide (i = ι_base)).
            - subst. setoid_rewrite lookup_insert in HX2.
              setoid_rewrite lookup_insert_ne in HX2; auto.
              setoid_rewrite lookup_insert. assumption.
            - setoid_rewrite lookup_insert_ne in HX2; auto.
              setoid_rewrite lookup_insert_ne in HX2; auto.
              setoid_rewrite lookup_insert_ne; auto.
        }
        rewrite XX in *. inv H5. clear XX H2.
        (* starting here, the same chain of thought has to be applied in the
           failing peek_message case too! *)
        eexists. exists []. split. apply n_refl.
        apply barbedBisim_sym.
        
        (* child terminates - TODO - this is wrong - create a helper to it  *)
        eapply barbedBisim_trans.
        {
          (* eapply normalisation_τ_many_bisim.
          1: shelve.
          1:{
            repeat setoid_rewrite dom_insert_L. set_solver.
          }
          apply process_local_to_node. 2: shelve.
          eapply lsstep. apply p_terminate. setoid_rewrite gset_to_gmap_empty.
          apply lsrefl. *)
          apply barbedBisim_sym.
          pose proof (almost_terminated_bisim {[ι]} (etherAdd ι0 ι' (SMessage (meta_to_cons (map f (take idx l')))) ∅, ι'
   ↦ inl
       ([FParams (IPrimOp "recv_peek_message") [] [];
         FLet 2
           (° ECase (˝ VVar 0)
                [([PLit "true"], ˝ VLit "true",
                  ° ECase (˝ VVar 1)
                      [([PVar], ˝ VLit "true",
                        ° ESeq (° EPrimOp "remove_message" [])
                            (° ECall (˝ VLit "erlang") (˝ VLit "!")
                                 [˝ VPid ι;
                                  ° ECall (˝ VLit "erlang") (˝ VLit "++")
                                      [˝ VVar 0; ˝ meta_to_cons (map f (drop idx l'))]]));
                       ([PVar], ˝ VLit "true",
                        ° ESeq (° EPrimOp "recv_next" [])
                            (° EApp
                                 (˝ VClos
                                      [(0, 0,
                                        ° ELet 2 (° EPrimOp "recv_peek_message" [])
                                            (° ECase (˝ VVar 0)
                                                 [([PLit "true"], ˝ 
                                                   VLit "true",
                                                   ° ECase (˝ VVar 1)
                                                       [([PVar], ˝ 
                                                         VLit "true",
                                                         ° ESeq
                                                             (° 
                                                             EPrimOp "remove_message" [])
                                                             (° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                        ([PVar], ˝ 
                                                         VLit "true",
                                                         ° ESeq 
                                                             (° EPrimOp "recv_next" [])
                                                             (° EApp (˝ VFunId (3, 0)) []))]);
                                                  ([PLit "false"], ˝ 
                                                   VLit "true",
                                                   ° ELet 1
                                                       (° EPrimOp "recv_wait_timeout"
                                                            [˝ 
                                                            VLit "infinity"])
                                                       (° ECase 
                                                            (˝ VVar 0)
                                                            [(
                                                             [
                                                             PLit "true"], ˝ 
                                                             VLit "true", ˝ VNil);
                                                             (
                                                             [
                                                             PLit "false"], ˝ 
                                                             VLit "true",
                                                             ° 
                                                             EApp (˝ VFunId (3, 0)) [])]))]))]
                                      0 0
                                      (° ELet 2 (° EPrimOp "recv_peek_message" [])
                                           (° ECase (˝ VVar 0)
                                                [([PLit "true"], ˝ 
                                                  VLit "true",
                                                  ° ECase (˝ VVar 1)
                                                      [([PVar], ˝ 
                                                        VLit "true",
                                                        ° ESeq
                                                            (° 
                                                             EPrimOp "remove_message" [])
                                                            (° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                       ([PVar], ˝ 
                                                        VLit "true",
                                                        ° ESeq 
                                                            (° EPrimOp "recv_next" [])
                                                            (° EApp (˝ VFunId (3, 0)) []))]);
                                                 ([PLit "false"], ˝ 
                                                  VLit "true",
                                                  ° ELet 1
                                                      (° EPrimOp "recv_wait_timeout"
                                                           [˝ 
                                                           VLit "infinity"])
                                                      (° ECase 
                                                           (˝ VVar 0)
                                                           [([
                                                             PLit "true"], ˝ 
                                                             VLit "true", ˝ VNil);
                                                            ([
                                                             PLit "false"], ˝ 
                                                             VLit "true",
                                                             ° 
                                                             EApp (˝ VFunId (3, 0)) [])]))])))
                                 []))]);
                 ([PLit "false"], ˝ VLit "true",
                  ° ELet 1 (° EPrimOp "recv_wait_timeout" [˝ VLit "infinity"])
                      (° ECase (˝ VVar 0)
                           [([PLit "true"], ˝ VLit "true", ˝ VNil);
                            ([PLit "false"], ˝ VLit "true",
                             ° EApp
                                 (˝ VClos
                                      [(0, 0,
                                        ° ELet 2 (° EPrimOp "recv_peek_message" [])
                                            (° ECase (˝ VVar 0)
                                                 [([PLit "true"], ˝ 
                                                   VLit "true",
                                                   ° ECase (˝ VVar 1)
                                                       [([PVar], ˝ 
                                                         VLit "true",
                                                         ° ESeq
                                                             (° 
                                                             EPrimOp "remove_message" [])
                                                             (° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                        ([PVar], ˝ 
                                                         VLit "true",
                                                         ° ESeq 
                                                             (° EPrimOp "recv_next" [])
                                                             (° EApp (˝ VFunId (3, 0)) []))]);
                                                  ([PLit "false"], ˝ 
                                                   VLit "true",
                                                   ° ELet 1
                                                       (° EPrimOp "recv_wait_timeout"
                                                            [˝ 
                                                            VLit "infinity"])
                                                       (° ECase 
                                                            (˝ VVar 0)
                                                            [(
                                                             [
                                                             PLit "true"], ˝ 
                                                             VLit "true", ˝ VNil);
                                                             (
                                                             [
                                                             PLit "false"], ˝ 
                                                             VLit "true",
                                                             ° 
                                                             EApp (˝ VFunId (3, 0)) [])]))]))]
                                      0 0
                                      (° ELet 2 (° EPrimOp "recv_peek_message" [])
                                           (° ECase (˝ VVar 0)
                                                [([PLit "true"], ˝ 
                                                  VLit "true",
                                                  ° ECase (˝ VVar 1)
                                                      [([PVar], ˝ 
                                                        VLit "true",
                                                        ° ESeq
                                                            (° 
                                                             EPrimOp "remove_message" [])
                                                            (° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                       ([PVar], ˝ 
                                                        VLit "true",
                                                        ° ESeq 
                                                            (° EPrimOp "recv_next" [])
                                                            (° EApp (˝ VFunId (3, 0)) []))]);
                                                 ([PLit "false"], ˝ 
                                                  VLit "true",
                                                  ° ELet 1
                                                      (° EPrimOp "recv_wait_timeout"
                                                           [˝ 
                                                           VLit "infinity"])
                                                      (° ECase 
                                                           (˝ VVar 0)
                                                           [([
                                                             PLit "true"], ˝ 
                                                             VLit "true", ˝ VNil);
                                                            ([
                                                             PLit "false"], ˝ 
                                                             VLit "true",
                                                             ° 
                                                             EApp (˝ VFunId (3, 0)) [])]))])))
                                 [])]))])], RBox, emptyBox, ∅, false) ∥ ∅)) as HH.
          apply HH; clear HH.                    (* TODO: bug? Direct 
                                                   apply does not work here*)
          - simpl; setoid_rewrite dom_insert_L. set_solver.
          - simpl. set_solver.
        }
      (* parent receives *)
      constructor.
      2,4: intros; exists source, []; eexists; simpl; split; try by constructor.
      (* etherAdd needs special care in this case *)
      2: {
        unfold etherAdd. simpl. setoid_rewrite lookup_empty.
        setoid_rewrite lookup_insert_ne. by setoid_rewrite lookup_empty.
        intro Y. inv Y. set_solver.
      }
      2: {
        unfold etherAdd. simpl. setoid_rewrite lookup_empty.
        setoid_rewrite lookup_insert_ne. by setoid_rewrite lookup_empty.
        intro Y. inv Y. set_solver.
      }
      (***)
      2: { (* Proved it already - to some extent *)
        intros. assert (ι1 = ι'). {
          destruct B'.
          apply deconstruct_reduction in H0. destruct_hyps.
          put (lookup ι1 : ProcessPool -> _) on H0 as H'.
          setoid_rewrite lookup_insert in H'. destruct (decide (ι1 = ι')).
          assumption.
          setoid_rewrite lookup_insert_ne in H'; auto. set_solver.
        }
        subst.
        assert (a = ASend ι' ι (SMessage (meta_to_cons (map f l')))). {
          inv H0.
          * put (lookup ι' : ProcessPool -> _) on H3 as P.
            setoid_rewrite lookup_insert in P. inv P. by inv H6.
          * clear-H3. unfold etherPop in H3. repeat case_match; try congruence.
            set_solver.
          * put (lookup ι' : ProcessPool -> _) on H2 as P.
            setoid_rewrite lookup_insert in P. inv P.
            destruct_or! H8; inv H3; try inv H13; cbn in *; try congruence.
          * put (lookup ι' : ProcessPool -> _) on H2 as P.
            setoid_rewrite lookup_insert in P. inv P.
            inv H3. inv H14.
        }
        subst. inv H0. 2: { destruct_or! H8; congruence. } clear H2.
        put (lookup ι' : ProcessPool -> _) on H3 as P.
        setoid_rewrite lookup_insert in P. inv P. inv H9.
        clear X.
        (* prs = ∅ *)
        assert (forall p, ι' ↦ p ∥ prs0 = ι' ↦ p ∥ ∅) as X. {
          intros.
          apply map_eq. intros. put (lookup i : ProcessPool -> _) on H3 as D.
          destruct (decide (i = ι')).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne in D; auto.
            by setoid_rewrite lookup_insert_ne.
        }
        clear H3. rewrite X in *.
        (**)
        do 2 eexists. split.
        {
          (* reductions *)
          (* map arrives to the parent *)
          eapply n_trans. apply n_arrive with (ι0 := ι0).
          {
            unfold etherAdd, etherPop.
            setoid_rewrite lookup_empty.
            setoid_rewrite lookup_insert.
            setoid_rewrite lookup_empty.
            setoid_rewrite insert_insert.
            reflexivity.
          }
          {
            constructor.
          }
          (* parent message peek
          *)
          eapply closureNodeSem_trans.
          {
            eapply process_local_to_node.
            {
              apply eval_helper_peek_message.
            }
            {
              repeat constructor.
            }
          }
          (* parent sends the result *)
          eapply n_trans. apply n_send. constructor. assumption.
          apply n_refl.
        }
        { (* equivalence - we need two helpers about dead processes and ether inserts *)
          simpl. (* now the pools are equal, we have to do the same for the ethers *)
          unfold etherAdd. setoid_rewrite lookup_empty.
          setoid_rewrite lookup_insert_ne.
          2: set_solver.
          setoid_rewrite lookup_empty.
          remember (insert (ι', ι) _ ∅) as E.
          setoid_rewrite insert_commute. 2: intro Y; inv Y; lia.
          apply barbedBisim_sym.
          setoid_rewrite HeqE.
          apply ether_empty_update_bisim.
          clear-Hbase. set_solver.
          simpl. subst E. left.
          setoid_rewrite lookup_insert_ne. set_solver.
          set_solver.
        }
      }
      
      {
        intros.
        inv H0.
        * put (lookup ι1 : ProcessPool -> _) on H3 as XX.
          setoid_rewrite lookup_insert in XX.
          destruct (decide (ι' = ι1)).
          - subst. setoid_rewrite lookup_insert in XX. inv XX.
            inv H6.
          - by setoid_rewrite lookup_insert_ne in XX.
        (* arrive *)
        * unfold etherPop, etherAdd in H3.
          setoid_rewrite lookup_empty in H3.
          destruct (decide ((ι0, ι') = (ι3, ι1))).
          2: {
            setoid_rewrite lookup_insert_ne in H3; auto.
            by setoid_rewrite lookup_empty in H3.
          }
          inv e. setoid_rewrite lookup_insert in H3.
          setoid_rewrite lookup_empty in H3.
          setoid_rewrite insert_insert in H3. inv H3.
          put (lookup ι1 : ProcessPool -> _) on H2 as HX1.
          setoid_rewrite lookup_insert in HX1. inv HX1.
          assert (forall p, ι1 ↦ p ∥ prs0 = ι1 ↦ p ∥ ∅) as XX. {
            intros. apply map_eq. intros.
            put (lookup i : ProcessPool -> _) on H2 as HX2.
            destruct (decide (i = ι1)).
            * subst. by setoid_rewrite lookup_insert.
            * setoid_rewrite lookup_insert_ne in HX2; auto.
              by setoid_rewrite lookup_insert_ne.
          }
          rewrite XX in *. clear XX H2.
          inv H8.
          eexists. exists []. split. apply n_refl.
          (* receive finished *)
          (* cleanup of empty ether update: *)
          eapply barbedBisim_trans.
          apply barbedBisim_sym.
          epose proof (ether_empty_update_bisim {[ι]} _ (∅,
ι1
 ↦ inl
     ([FParams (IPrimOp "recv_peek_message") [] [];
       FLet 2
         (° ECase (˝ VVar 0)
              [([PLit "true"], ˝ VLit "true",
                ° ECase (˝ VVar 1)
                    [([PVar], ˝ VLit "true",
                      ° ESeq (° EPrimOp "remove_message" [])
                          (° ECall (˝ VLit "erlang") (˝ VLit "!")
                               [˝ VPid ι;
                                ° ECall (˝ VLit "erlang") (˝ VLit "++")
                                    [˝ VVar 0; ˝ meta_to_cons (map f (drop idx l'))]]));
                     ([PVar], ˝ VLit "true",
                      ° ESeq (° EPrimOp "recv_next" [])
                          (° EApp
                               (˝ VClos
                                    [(0, 0,
                                      ° ELet 2 (° EPrimOp "recv_peek_message" [])
                                          (° ECase (˝ VVar 0)
                                               [([PLit "true"], ˝ 
                                                 VLit "true",
                                                 ° ECase (˝ VVar 1)
                                                     [([PVar], ˝ 
                                                       VLit "true",
                                                       ° ESeq
                                                           (° EPrimOp "remove_message" [])
                                                           (° 
                                                            ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                      ([PVar], ˝ 
                                                       VLit "true",
                                                       ° ESeq 
                                                           (° EPrimOp "recv_next" [])
                                                           (° EApp (˝ VFunId (3, 0)) []))]);
                                                ([PLit "false"], ˝ 
                                                 VLit "true",
                                                 ° ELet 1
                                                     (° EPrimOp "recv_wait_timeout"
                                                          [˝ VLit "infinity"])
                                                     (° ECase 
                                                          (˝ VVar 0)
                                                          [([PLit "true"], ˝ 
                                                            VLit "true", ˝ VNil);
                                                           ([PLit "false"], ˝ 
                                                            VLit "true",
                                                            ° 
                                                            EApp (˝ VFunId (3, 0)) [])]))]))]
                                    0 0
                                    (° ELet 2 (° EPrimOp "recv_peek_message" [])
                                         (° ECase (˝ VVar 0)
                                              [([PLit "true"], ˝ 
                                                VLit "true",
                                                ° ECase (˝ VVar 1)
                                                    [([PVar], ˝ 
                                                      VLit "true",
                                                      ° ESeq
                                                          (° EPrimOp "remove_message" [])
                                                          (° ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                     ([PVar], ˝ 
                                                      VLit "true",
                                                      ° ESeq (° EPrimOp "recv_next" [])
                                                          (° EApp (˝ VFunId (3, 0)) []))]);
                                               ([PLit "false"], ˝ 
                                                VLit "true",
                                                ° ELet 1
                                                    (° EPrimOp "recv_wait_timeout"
                                                         [˝ VLit "infinity"])
                                                    (° ECase (˝ VVar 0)
                                                         [([PLit "true"], ˝ 
                                                           VLit "true", ˝ VNil);
                                                          ([PLit "false"], ˝ 
                                                           VLit "true",
                                                           ° EApp (˝ VFunId (3, 0)) [])]))])))
                               []))]);
               ([PLit "false"], ˝ VLit "true",
                ° ELet 1 (° EPrimOp "recv_wait_timeout" [˝ VLit "infinity"])
                    (° ECase (˝ VVar 0)
                         [([PLit "true"], ˝ VLit "true", ˝ VNil);
                          ([PLit "false"], ˝ VLit "true",
                           ° EApp
                               (˝ VClos
                                    [(0, 0,
                                      ° ELet 2 (° EPrimOp "recv_peek_message" [])
                                          (° ECase (˝ VVar 0)
                                               [([PLit "true"], ˝ 
                                                 VLit "true",
                                                 ° ECase (˝ VVar 1)
                                                     [([PVar], ˝ 
                                                       VLit "true",
                                                       ° ESeq
                                                           (° EPrimOp "remove_message" [])
                                                           (° 
                                                            ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                      ([PVar], ˝ 
                                                       VLit "true",
                                                       ° ESeq 
                                                           (° EPrimOp "recv_next" [])
                                                           (° EApp (˝ VFunId (3, 0)) []))]);
                                                ([PLit "false"], ˝ 
                                                 VLit "true",
                                                 ° ELet 1
                                                     (° EPrimOp "recv_wait_timeout"
                                                          [˝ VLit "infinity"])
                                                     (° ECase 
                                                          (˝ VVar 0)
                                                          [([PLit "true"], ˝ 
                                                            VLit "true", ˝ VNil);
                                                           ([PLit "false"], ˝ 
                                                            VLit "true",
                                                            ° 
                                                            EApp (˝ VFunId (3, 0)) [])]))]))]
                                    0 0
                                    (° ELet 2 (° EPrimOp "recv_peek_message" [])
                                         (° ECase (˝ VVar 0)
                                              [([PLit "true"], ˝ 
                                                VLit "true",
                                                ° ECase (˝ VVar 1)
                                                    [([PVar], ˝ 
                                                      VLit "true",
                                                      ° ESeq
                                                          (° EPrimOp "remove_message" [])
                                                          (° ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                     ([PVar], ˝ 
                                                      VLit "true",
                                                      ° ESeq (° EPrimOp "recv_next" [])
                                                          (° EApp (˝ VFunId (3, 0)) []))]);
                                               ([PLit "false"], ˝ 
                                                VLit "true",
                                                ° ELet 1
                                                    (° EPrimOp "recv_wait_timeout"
                                                         [˝ VLit "infinity"])
                                                    (° ECase (˝ VVar 0)
                                                         [([PLit "true"], ˝ 
                                                           VLit "true", ˝ VNil);
                                                          ([PLit "false"], ˝ 
                                                           VLit "true",
                                                           ° EApp (˝ VFunId (3, 0)) [])]))])))
                               [])]))])], RBox,
      mailboxPush emptyBox (meta_to_cons (map f (take idx l'))), ∅, false) ∥ ∅)) as Heth. simpl in Heth. eapply Heth.
          1-2: set_solver.
          (* same state *)
          by apply bisim_helper.
        * put (lookup ι1 : ProcessPool -> _) on H2 as XX.
          setoid_rewrite lookup_insert in XX.
          destruct (decide (ι' = ι1)).
          2: {
            setoid_rewrite lookup_insert_ne in XX; auto. set_solver.
          }
          subst. setoid_rewrite lookup_insert in XX. inv XX.
          destruct_or!; subst; inv H3. inv H9. inv H8.
          by cbn in H8.
          (* peeking can be done again, before receiving unfortunately :( *)
          (* technical steps are needed from below - labelled as
                    (* failing peek_message *) 
           *)
          assert (forall p, ι1 ↦ p ∥ Π0 = ι1 ↦ p ∥ ∅) as XX. {
            intros. apply map_eq. intros.
            destruct (decide (i = ι1)).
            * subst. by setoid_rewrite lookup_insert.
            * setoid_rewrite lookup_insert_ne; auto.
              put (lookup i : ProcessPool -> _) on H2 as HX2.
              setoid_rewrite lookup_insert_ne in HX2; auto.
          }
          rewrite XX in *. clear H2.
          eexists. exists []. split. 1: apply n_refl.
          eapply barbedBisim_trans.
          {
            eapply normalisation_τ_many_bisim.
            1: shelve.
            1:{
              repeat setoid_rewrite dom_insert_L. set_solver.
            }
            apply process_local_to_node.
            2: shelve.
            eapply lsstep. eapply p_local. constructor. reflexivity. simpl.
            repeat rewrite (vclosed_ignores_sub); auto with examples.
            2-3: apply drop_helper2.
            eapply lsstep. eapply p_local. constructor.
            eapply lsstep. eapply p_local. constructor. scope_solver.
            eapply lsstep. eapply p_local. apply eval_step_case_not_match. reflexivity.
            eapply lsstep. eapply p_local. apply eval_step_case_match. reflexivity.
            simpl.
            repeat rewrite (vclosed_ignores_sub); auto with examples.
            2: apply drop_helper2.
            eapply lsstep. eapply p_local. constructor. scope_solver.
            eapply lsstep. eapply p_local. constructor.
            eapply lsstep. eapply p_local. constructor.
            eapply lsstep. eapply p_local. constructor.
            eapply lsstep. eapply p_local. constructor. congruence.
            eapply lsstep. eapply p_local. constructor. scope_solver.
            (* infinity timeout can only be reached, if something is in the mailbox *)
            apply lsrefl.
          }
          simpl.

          (* parent receives *)
          constructor.
          2,4: intros; exists source, []; eexists; simpl; split; try by constructor.
          (* etherAdd needs special care in this case *)
          2: {
            unfold etherAdd. simpl. setoid_rewrite lookup_empty.
            setoid_rewrite lookup_insert_ne. by setoid_rewrite lookup_empty.
            intro Y. inv Y. set_solver.
          }
          2: {
            unfold etherAdd. simpl. setoid_rewrite lookup_empty.
            setoid_rewrite lookup_insert_ne. by setoid_rewrite lookup_empty.
            intro Y. inv Y. set_solver.
          }
          (***)
          2: {
            (* Proved it already - to some extent *)
            intros. assert (ι1 = ι2). {
              destruct B'.
              apply deconstruct_reduction in H0. destruct_hyps.
              put (lookup ι2 : ProcessPool -> _) on H0 as H'.
              setoid_rewrite lookup_insert in H'. destruct (decide (ι1 = ι2)).
              assumption.
              setoid_rewrite lookup_insert_ne in H'; auto. set_solver.
            }
            subst.
            assert (a = ASend ι2 ι (SMessage (meta_to_cons (map f l')))). {
              inv H0.
              * put (lookup ι2 : ProcessPool -> _) on H3 as P.
                setoid_rewrite lookup_insert in P. inv P. by inv H6.
              * clear-H3. unfold etherPop in H3. repeat case_match; try congruence.
                set_solver.
              * put (lookup ι2 : ProcessPool -> _) on H2 as P.
                setoid_rewrite lookup_insert in P. inv P.
                destruct_or! H9; inv H3; try inv H14; cbn in *; try congruence.
              * put (lookup ι2 : ProcessPool -> _) on H2 as P.
                setoid_rewrite lookup_insert in P. inv P.
                inv H3. inv H16.
            }
            subst. inv H0. 2: { destruct_or! H9; congruence. } clear H2.
            put (lookup ι2 : ProcessPool -> _) on H3 as P.
            setoid_rewrite lookup_insert in P. inv P. inv H12.
            clear X.
            (* prs = ∅ *)
            assert (forall p, ι2 ↦ p ∥ prs0 = ι2 ↦ p ∥ ∅) as X. {
              intros.
              apply map_eq. intros. put (lookup i : ProcessPool -> _) on H3 as D.
              destruct (decide (i = ι2)).
              * subst. by setoid_rewrite lookup_insert.
              * setoid_rewrite lookup_insert_ne in D; auto.
                by setoid_rewrite lookup_insert_ne.
            }
            clear H3. rewrite X in *.
            (**)
            do 2 eexists. split.
            {
              (* reductions *)
              (* map arrives to the parent *)
              eapply n_trans. apply n_arrive with (ι0 := ι0).
              {
                unfold etherAdd, etherPop.
                setoid_rewrite lookup_empty.
                setoid_rewrite lookup_insert.
                setoid_rewrite lookup_empty.
                setoid_rewrite insert_insert.
                reflexivity.
              }
              {
                constructor.
              }
              (* parent recv_timeout then message peek
              *)
              eapply closureNodeSem_trans.
              {
                eapply process_local_to_node.
                {
                  (* recv_timeout *)
                  eapply lsstep. apply p_recv_wait_timeout_new_message.
                  eapply lsstep. apply p_local. constructor. reflexivity.
                  simpl. eapply lsstep. apply p_local. constructor.
                  repeat rewrite (vclosed_ignores_sub); auto with examples.
                  2: apply drop_helper2.
                  simpl. eapply lsstep. apply p_local. constructor. scope_solver.
                  eapply lsstep. apply p_local. apply eval_step_case_not_match. reflexivity.
                  eapply lsstep. apply p_local. apply eval_step_case_match. reflexivity.
                  eapply lsstep. apply p_local. constructor. scope_solver.
                  eapply lsstep. apply p_local. constructor.
                  simpl. repeat rewrite (vclosed_ignores_sub); auto with examples.
                  2: apply drop_helper2.
                  eapply lsstep. apply p_local. constructor.
                  eapply lsstep. apply p_local. constructor.
                  1: {
                    repeat rewrite (vclosed_ignores_ren); auto with examples.
                    repeat rewrite (vclosed_ignores_sub); auto with examples.
                    all: try apply drop_helper2.
                    opose proof* (EReceive_scope ([([PVar], ˝ VLit "true",
                                          ° ECall (˝ VLit "erlang") (˝ VLit "!")
                                              [˝ VPid ι;
                                               ° ECall (˝ VLit "erlang") 
                                                   (˝ VLit "++")
                                                   [˝ VVar 0; ˝ meta_to_cons (map f (drop idx l'))]])]) (˝VLit "infinity"%string) (˝VNil) 0).
                    2-3: scope_solver.
                    {
                      constructor; auto. split. scope_solver.
                      do 6 scope_solver_step.
                      all: intros; destruct i; try destruct i; try destruct i.
                      1,3-5,7-9,11-12: scope_solver.
                      1: scope_solver_step; eapply loosen_scope_val; try apply drop_helper2; lia.
                      all: do 6 scope_solver_step.
                    }
                    inv H0. inv H3. constructor; auto.
                    intros. simpl in *.
                    specialize (H4 0 ltac:(lia)). simpl in H4. simpl. apply H4.
                  }
                  eapply lsstep. apply p_local. constructor.
                  eapply lsstep. apply p_local. econstructor. congruence. simpl. reflexivity.
                  simpl. repeat rewrite (vclosed_ignores_sub); auto with examples.
                  repeat rewrite (vclosed_ignores_ren); auto with examples.
                  all: try apply drop_helper2.
                  eapply lsstep. apply p_local. constructor.
                  eapply lsstep. apply p_local. constructor.
                  (* message_peek *)
                  apply eval_helper_peek_message.
                }
                {
                  constructor. 2: repeat constructor.
                  by right; left.
                }
              }
              (* parent sends the result *)
              eapply n_trans. apply n_send. constructor. assumption.
              apply n_refl.
            }
            { (* equivalence - we need two helpers about dead processes and ether inserts *)
              simpl. (* now the pools are equal, we have to do the same for the ethers *)
              unfold etherAdd. setoid_rewrite lookup_empty.
              setoid_rewrite lookup_insert_ne.
              2: set_solver.
              setoid_rewrite lookup_empty.
              remember (insert (ι2, ι) _ ∅) as E.
              setoid_rewrite insert_commute. 2: intro Y; inv Y; lia.
              apply barbedBisim_sym.
              setoid_rewrite HeqE.
              apply ether_empty_update_bisim.
              clear-Hbase. set_solver.
              simpl. subst E. left.
              setoid_rewrite lookup_insert_ne. set_solver.
              set_solver.
            }
          }
          
          
          
          {
            clear XX. intros.
            inv H0.
            * put (lookup ι2 : ProcessPool -> _) on H3 as XX.
              setoid_rewrite lookup_insert in XX.
              destruct (decide (ι1 = ι2)).
              - subst. setoid_rewrite lookup_insert in XX. inv XX.
                inv H6.
              - by setoid_rewrite lookup_insert_ne in XX.
            (* arrive *)
            * unfold etherPop, etherAdd in H3.
              setoid_rewrite lookup_empty in H3.
              destruct (decide ((ι0, ι1) = (ι4, ι2))).
              2: {
                setoid_rewrite lookup_insert_ne in H3; auto.
                by setoid_rewrite lookup_empty in H3.
              }
              inv e. setoid_rewrite lookup_insert in H3.
              setoid_rewrite lookup_empty in H3.
              setoid_rewrite insert_insert in H3. inv H3.
              put (lookup ι2 : ProcessPool -> _) on H2 as HX1.
              setoid_rewrite lookup_insert in HX1. inv HX1.
              assert (forall p, ι2 ↦ p ∥ prs0 = ι2 ↦ p ∥ ∅) as XX. {
                intros. apply map_eq. intros.
                put (lookup i : ProcessPool -> _) on H2 as HX2.
                destruct (decide (i = ι2)).
                * subst. by setoid_rewrite lookup_insert.
                * setoid_rewrite lookup_insert_ne in HX2; auto.
                  by setoid_rewrite lookup_insert_ne.
              }
              rewrite XX in *. clear XX H2.
              inv H9.
              eexists. exists []. split. apply n_refl.
              (* receive finished *)
              (* cleanup of empty ether update: *)
              eapply barbedBisim_trans.
              apply barbedBisim_sym.
              epose proof (ether_empty_update_bisim {[ι]} _ (∅,
 ι2
 ↦ inl
     ([FParams (IPrimOp "recv_wait_timeout") [] [];
       FLet 1
         (° ECase (˝ VVar 0)
              [([PLit "true"], ˝ VLit "true", ˝ VNil);
               ([PLit "false"], ˝ VLit "true",
                ° EApp
                    (˝ VClos
                         [(0, 0,
                           ° ELet 2 (° EPrimOp "recv_peek_message" [])
                               (° ECase (˝ VVar 0)
                                    [([PLit "true"], ˝ VLit "true",
                                      ° ECase (˝ VVar 1)
                                          [([PVar], ˝ VLit "true",
                                            ° ESeq (° EPrimOp "remove_message" [])
                                                (° ECall (˝ VLit "erlang") 
                                                     (˝ VLit "!")
                                                     [˝ VPid ι;
                                                      ° ECall 
                                                          (˝ VLit "erlang") 
                                                          (˝ VLit "++")
                                                          [˝ VVar 0;
                                                           ˝ meta_to_cons
                                                             (map f (drop idx l'))]]));
                                           ([PVar], ˝ VLit "true",
                                            ° ESeq (° EPrimOp "recv_next" [])
                                                (° EApp (˝ VFunId (3, 0)) []))]);
                                     ([PLit "false"], ˝ VLit "true",
                                      ° ELet 1
                                          (° EPrimOp "recv_wait_timeout"
                                               [˝ VLit "infinity"])
                                          (° ECase (˝ VVar 0)
                                               [([PLit "true"], ˝ VLit "true", ˝ VNil);
                                                ([PLit "false"], ˝ 
                                                 VLit "true", ° 
                                                 EApp (˝ VFunId (3, 0)) [])]))]))] 0 0
                         (° ELet 2 (° EPrimOp "recv_peek_message" [])
                              (° ECase (˝ VVar 0)
                                   [([PLit "true"], ˝ VLit "true",
                                     ° ECase (˝ VVar 1)
                                         [([PVar], ˝ VLit "true",
                                           ° ESeq (° EPrimOp "remove_message" [])
                                               (° ECall (˝ VLit "erlang") 
                                                    (˝ VLit "!")
                                                    [˝ VPid ι;
                                                     ° ECall (˝ VLit "erlang")
                                                         (˝ VLit "++")
                                                         [˝ VVar 0;
                                                          ˝ meta_to_cons
                                                             (map f (drop idx l'))]]));
                                          ([PVar], ˝ VLit "true",
                                           ° ESeq (° EPrimOp "recv_next" [])
                                               (° EApp (˝ VFunId (3, 0)) []))]);
                                    ([PLit "false"], ˝ VLit "true",
                                     ° ELet 1
                                         (° EPrimOp "recv_wait_timeout"
                                              [˝ VLit "infinity"])
                                         (° ECase (˝ VVar 0)
                                              [([PLit "true"], ˝ VLit "true", ˝ VNil);
                                               ([PLit "false"], ˝ 
                                                VLit "true", ° 
                                                EApp (˝ VFunId (3, 0)) [])]))]))) [])])],
      RValSeq [VLit "infinity"], mailboxPush emptyBox (meta_to_cons (map f (take idx l'))), ∅,
      false) ∥ ∅)) as Heth. simpl in Heth. eapply Heth.
              1-2: set_solver.
              { (* next: wait timeout succeeds - again low level reasoning needed *)
                constructor.
                2,4: intros; exists source, []; eexists; simpl; split; try by constructor.
                2: { (* again, we proved this already to some extent *)
                    intros. assert (ι0 = ι2). {
                    destruct B'.
                    apply deconstruct_reduction in H0. destruct_hyps.
                    put (lookup ι0 : ProcessPool -> _) on H0 as H'.
                    setoid_rewrite lookup_insert in H'. destruct (decide (ι0 = ι2)).
                    assumption.
                    setoid_rewrite lookup_insert_ne in H'; auto. set_solver.
                  }
                  subst.
                  assert (a = ASend ι2 ι (SMessage (meta_to_cons (map f l')))). {
                    inv H0.
                    * put (lookup ι2 : ProcessPool -> _) on H3 as P.
                      setoid_rewrite lookup_insert in P. inv P. by inv H6.
                    * clear-H3. unfold etherPop in H3. repeat case_match; try congruence.
                      set_solver.
                    * put (lookup ι2 : ProcessPool -> _) on H2 as P.
                      setoid_rewrite lookup_insert in P. inv P.
                      destruct_or! H9; inv H3; try inv H14; cbn in *; try congruence.
                    * put (lookup ι2 : ProcessPool -> _) on H2 as P.
                      setoid_rewrite lookup_insert in P. inv P.
                      inv H3. inv H16.
                  }
                  subst. inv H0. 2: { destruct_or! H9; congruence. } clear H2.
                  put (lookup ι2 : ProcessPool -> _) on H3 as P.
                  setoid_rewrite lookup_insert in P. inv P. inv H12.
                  clear X.
                  (* prs = ∅ *)
                  assert (forall p, ι2 ↦ p ∥ prs1 = ι2 ↦ p ∥ ∅) as X. {
                    intros.
                    apply map_eq. intros. put (lookup i : ProcessPool -> _) on H3 as D.
                    destruct (decide (i = ι2)).
                    * subst. by setoid_rewrite lookup_insert.
                    * setoid_rewrite lookup_insert_ne in D; auto.
                      by setoid_rewrite lookup_insert_ne.
                  }
                  clear H3. rewrite X in *.
                  (**)
                  do 2 eexists. split.
                  {
                    (* reductions *)
                    (* parent recv_timeout then message peek
                    *)
                    eapply closureNodeSem_trans.
                    {
                      eapply process_local_to_node.
                      {
                        (* recv_timeout *)
                        eapply lsstep. apply p_recv_wait_timeout_new_message.
                        eapply lsstep. apply p_local. constructor. reflexivity.
                        simpl. eapply lsstep. apply p_local. constructor.
                        repeat rewrite (vclosed_ignores_sub); auto with examples.
                        2: apply drop_helper2.
                        simpl. eapply lsstep. apply p_local. constructor. scope_solver.
                        eapply lsstep. apply p_local. apply eval_step_case_not_match. reflexivity.
                        eapply lsstep. apply p_local. apply eval_step_case_match. reflexivity.
                        eapply lsstep. apply p_local. constructor. scope_solver.
                        eapply lsstep. apply p_local. constructor.
                        simpl. repeat rewrite (vclosed_ignores_sub); auto with examples.
                        2: apply drop_helper2.
                        eapply lsstep. apply p_local. constructor.
                        eapply lsstep. apply p_local. constructor.
                        1: {
                          repeat rewrite (vclosed_ignores_ren); auto with examples.
                          repeat rewrite (vclosed_ignores_sub); auto with examples.
                          all: try apply drop_helper2.
                          opose proof* (EReceive_scope ([([PVar], ˝ VLit "true",
                                                ° ECall (˝ VLit "erlang") (˝ VLit "!")
                                                    [˝ VPid ι;
                                                     ° ECall (˝ VLit "erlang") 
                                                         (˝ VLit "++")
                                                         [˝ VVar 0; ˝ meta_to_cons (map f (drop idx l'))]])]) (˝VLit "infinity"%string) (˝VNil) 0).
                          2-3: scope_solver.
                          {
                            constructor; auto. split. scope_solver.
                            do 6 scope_solver_step.
                            all: intros; destruct i; try destruct i; try destruct i.
                            1,3-5,7-9,11-12: scope_solver.
                            1: scope_solver_step; eapply loosen_scope_val; try apply drop_helper2; lia.
                            all: do 6 scope_solver_step.
                          }
                          inv H0. inv H3. constructor; auto.
                          intros. simpl in *.
                          specialize (H4 0 ltac:(lia)). simpl in H4. simpl. apply H4.
                        }
                        eapply lsstep. apply p_local. constructor.
                        eapply lsstep. apply p_local. econstructor. congruence. simpl. reflexivity.
                        simpl. repeat rewrite (vclosed_ignores_sub); auto with examples.
                        repeat rewrite (vclosed_ignores_ren); auto with examples.
                        all: try apply drop_helper2.
                        eapply lsstep. apply p_local. constructor.
                        eapply lsstep. apply p_local. constructor.
                        (* message_peek *)
                        apply eval_helper_peek_message.
                      }
                      {
                        constructor. 2: repeat constructor.
                        by right; left.
                      }
                    }
                    (* parent sends the result *)
                    eapply n_trans. apply n_send. constructor. assumption.
                    apply n_refl.
                  }
                  { (* equivalence - we need two helpers about dead processes and ether inserts *)
                    simpl. (* now the pools are equal, we have to do the same for the ethers *)
                    unfold etherAdd. setoid_rewrite lookup_empty.
                    apply barbedBisim_refl.
                  }
                }
                intros. inv H0.
                * put (lookup ι0 : ProcessPool -> _) on H3 as XX.
                  setoid_rewrite lookup_insert in XX.
                  destruct (decide (ι0 = ι2)).
                  - subst. setoid_rewrite lookup_insert in XX. inv XX.
                    inv H6.
                  - by setoid_rewrite lookup_insert_ne in XX; auto.
                * clear -H3. unfold etherPop in H3. by setoid_rewrite lookup_empty in H3.
                * put (lookup ι0 : ProcessPool -> _) on H2 as XX.
                  setoid_rewrite lookup_insert in XX.
                  destruct (decide (ι0 = ι2)).
                  2: by setoid_rewrite lookup_insert_ne in XX; auto.
                  subst. setoid_rewrite lookup_insert in XX. inv XX.
                  destruct_or! H9; subst; inv H3.
                  1: inv H12; inv H9.
                  congruence.
                  assert (forall p, ι2 ↦ p ∥ Π1 = ι2 ↦ p ∥ ∅) as XXX. {
                    intros. apply map_eq. intros.
                    destruct (decide (i = ι2)).
                    * subst. by setoid_rewrite lookup_insert.
                    * setoid_rewrite lookup_insert_ne; auto.
                      put (lookup i : ProcessPool -> _) on H2 as HX2.
                      by setoid_rewrite lookup_insert_ne in HX2; auto.
                  }
                  rewrite XXX in *. clear H2 XXX.
                  eexists. exists []. split. apply n_refl.
                  eapply barbedBisim_trans.
                  {
                    eapply normalisation_τ_many_bisim.
                    1: shelve.
                    1: set_solver.
                    apply sequential_to_node.
                    do 9 do_step.
                    1: {
                        repeat rewrite (vclosed_ignores_ren); auto with examples.
                        repeat rewrite (vclosed_ignores_sub); auto with examples.
                        all: try apply drop_helper2.
                        opose proof* (EReceive_scope ([([PVar], ˝ VLit "true",
                                              ° ECall (˝ VLit "erlang") (˝ VLit "!")
                                                  [˝ VPid ι;
                                                   ° ECall (˝ VLit "erlang") 
                                                       (˝ VLit "++")
                                                       [˝ VVar 0; ˝ meta_to_cons (map f (drop idx l'))]])]) (˝VLit "infinity"%string) (˝VNil) 0).
                        2-3: scope_solver.
                        {
                          constructor; auto. split. scope_solver.
                          do 6 scope_solver_step.
                          all: intros; destruct i; try destruct i; try destruct i.
                          1,3-5,7-9,11-12: scope_solver.
                          1: scope_solver_step; eapply loosen_scope_val; try apply drop_helper2; lia.
                          all: do 6 scope_solver_step.
                        }
                        inv H0. inv H3. constructor; auto.
                        intros. simpl in *.
                        specialize (H4 0 ltac:(lia)). simpl in H4. simpl. apply H4.
                    }
                    repeat rewrite (vclosed_ignores_sub); auto with examples.
                    2-4: apply drop_helper2.
                    do_step. econstructor 2. econstructor. congruence. simpl. reflexivity.
                    repeat rewrite (vclosed_ignores_sub); auto with examples.
                    repeat rewrite (vclosed_ignores_ren); auto with examples.
                    all: try apply drop_helper2.
                    do 2 do_step.
                    constructor 1.
                  }
                  (* peek_message succeeds - this was done previously *)
                  by apply bisim_helper.
                * put (lookup ι0 : ProcessPool -> _) on H2 as XX.
                    setoid_rewrite lookup_insert in XX.
                    destruct (decide (ι0 = ι2)).
                    - subst. setoid_rewrite lookup_insert in XX. inv XX.
                      inv H16.
                    - by setoid_rewrite lookup_insert_ne in XX.
                  }
             * put (lookup ι2 : ProcessPool -> _) on H2 as XX.
               setoid_rewrite lookup_insert in XX.
               destruct (decide (ι2 = ι1)).
               - subst. setoid_rewrite lookup_insert in XX. inv XX.
                 destruct_or! H9; subst; inv H3.
                 1: inv H12; inv H9.
                 congruence.
               - by setoid_rewrite lookup_insert_ne in XX.
             * put (lookup ι2 : ProcessPool -> _) on H2 as XX.
               setoid_rewrite lookup_insert in XX.
               destruct (decide (ι2 = ι1)).
               - subst. setoid_rewrite lookup_insert in XX. inv XX.
                 inv H16.
               - by setoid_rewrite lookup_insert_ne in XX.
          }
        * put (lookup ι1 : ProcessPool -> _) on H2 as XX.
          setoid_rewrite lookup_insert in XX.
          destruct (decide (ι' = ι1)).
          - subst. setoid_rewrite lookup_insert in XX. inv XX.
            inv H14.
          - by setoid_rewrite lookup_insert_ne in XX.
        }




      - clear-H2. unfold etherPop in H2. by setoid_rewrite lookup_empty in H2.
      - (* failing peek_message *)
        put (lookup ι0 : ProcessPool -> _) on H1 as HX1.
        setoid_rewrite lookup_insert in HX1.
        destruct (decide (ι0 = ι_base)).
        2: {
          setoid_rewrite lookup_insert_ne in HX1; auto.
          setoid_rewrite lookup_insert_ne in HX1; auto. set_solver.
          intro. subst.
          setoid_rewrite lookup_insert in HX1. inv HX1.
          destruct_or! H6; subst; inv H2. inv H8. inv H6.
        }
        subst. setoid_rewrite lookup_insert in HX1. inv HX1.
        assert (forall p, ι_base ↦ p ∥ Π0 = ι_base ↦ p ∥ x ↦ inl
              ([FParams (ICall (VLit "erlang") (VLit "!")) [VPid ι_base] []],
               RValSeq [meta_to_cons (map f (take idx l'))], emptyBox, ∅, false) ∥ ∅) as XX. {
          intros. apply map_eq. intros.
          destruct (decide (i = ι_base)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            put (lookup i : ProcessPool -> _) on H1 as HX2.
            setoid_rewrite lookup_insert_ne in HX2; auto.
        }
        rewrite XX. clear H1.
        destruct_or! H6; subst; inv H2.
        1: inv H6; inv H5.
        1: inv H5.
        eexists. exists []. split. 1: apply n_refl.
        apply barbedBisim_sym. eapply barbedBisim_trans.
        {
          eapply normalisation_τ_many_bisim.
          1: shelve.
          1:{
            repeat setoid_rewrite dom_insert_L. set_solver.
          }
          apply process_local_to_node.
          2: shelve.
          eapply lsstep. eapply p_local. constructor. reflexivity. simpl.
          repeat rewrite (vclosed_ignores_sub); auto with examples.
          2-3: apply drop_helper2.
          eapply lsstep. eapply p_local. constructor.
          eapply lsstep. eapply p_local. constructor. scope_solver.
          eapply lsstep. eapply p_local. apply eval_step_case_not_match. reflexivity.
          eapply lsstep. eapply p_local. apply eval_step_case_match. reflexivity.
          simpl.
          repeat rewrite (vclosed_ignores_sub); auto with examples.
          2: apply drop_helper2.
          eapply lsstep. eapply p_local. constructor. scope_solver.
          eapply lsstep. eapply p_local. constructor.
          eapply lsstep. eapply p_local. constructor.
          eapply lsstep. eapply p_local. constructor.
          eapply lsstep. eapply p_local. constructor. congruence.
          eapply lsstep. eapply p_local. constructor. scope_solver.
          (* infinity timeout can only be reached, if something is in the mailbox *)
          apply lsrefl.
        }
        simpl.
        (* send happens in the child *)
        constructor.
        2,4: intros; exists source, []; eexists; simpl; split; try by constructor.
        2: {
          (* Proved it already - to some extent *)
          intros. assert (ι_base = ι0). {
            destruct B'.
            apply deconstruct_reduction in H. destruct_hyps.
            put (lookup ι0 : ProcessPool -> _) on H as H'.
            setoid_rewrite lookup_insert in H'. destruct (decide (ι_base = ι0)).
            assumption.
            setoid_rewrite lookup_insert_ne in H'; auto. set_solver.
          }
          subst.
          assert (a = ASend ι0 ι (SMessage (meta_to_cons (map f l')))). {
            inv H.
            * put (lookup ι0 : ProcessPool -> _) on H2 as P.
              setoid_rewrite lookup_insert in P. inv P. by inv H6.
            * clear-H2. unfold etherPop in H2. repeat case_match; try congruence.
              set_solver.
            * put (lookup ι0 : ProcessPool -> _) on H1 as P.
              setoid_rewrite lookup_insert in P. inv P.
              destruct_or! H8; inv H2; try inv H13; cbn in *; try congruence.
            * put (lookup ι0 : ProcessPool -> _) on H1 as P.
              setoid_rewrite lookup_insert in P. inv P.
              inv H2. inv H14.
          }
          subst. inv H. 2: { destruct_or! H8; congruence. } clear H1.
          put (lookup ι0 : ProcessPool -> _) on H2 as P.
          setoid_rewrite lookup_insert in P. inv P. inv H9.
          clear X.
          (* prs = ∅ *)
          assert (forall p, ι0 ↦ p ∥ prs = ι0 ↦ p ∥ ∅) as X. {
            intros.
            apply map_eq. intros. put (lookup i : ProcessPool -> _) on H2 as D.
            destruct (decide (i = ι0)).
            * subst. by setoid_rewrite lookup_insert.
            * setoid_rewrite lookup_insert_ne in D; auto.
              by setoid_rewrite lookup_insert_ne.
          }
          clear H2. rewrite X in *.
          (**)
          do 2 eexists. split.
          {
            (* reductions *)
            (* map is sent back to the parent *)
            setoid_rewrite insert_commute; auto.
            eapply n_trans. eapply n_send. constructor.
            { apply take_helper2. }
            (* map arrives to the parent *)
            setoid_rewrite insert_commute; auto.
            (* parent receive message recv_timeout then message peek
            *)
            eapply n_trans. apply n_arrive with (ι0 := x).
            {
              unfold etherAdd, etherPop.
              setoid_rewrite lookup_empty.
              setoid_rewrite lookup_insert.
              setoid_rewrite lookup_empty.
              setoid_rewrite insert_insert.
              reflexivity.
            }
            {
              constructor.
            }
            eapply closureNodeSem_trans.
            {
              eapply process_local_to_node.
              {
                (* recv_timeout *)
                eapply lsstep. apply p_recv_wait_timeout_new_message.
                eapply lsstep. apply p_local. constructor. reflexivity.
                simpl. eapply lsstep. apply p_local. constructor.
                repeat rewrite (vclosed_ignores_sub); auto with examples.
                2: apply drop_helper2.
                simpl. eapply lsstep. apply p_local. constructor. scope_solver.
                eapply lsstep. apply p_local. apply eval_step_case_not_match. reflexivity.
                eapply lsstep. apply p_local. apply eval_step_case_match. reflexivity.
                eapply lsstep. apply p_local. constructor. scope_solver.
                eapply lsstep. apply p_local. constructor.
                simpl. repeat rewrite (vclosed_ignores_sub); auto with examples.
                2: apply drop_helper2.
                eapply lsstep. apply p_local. constructor.
                eapply lsstep. apply p_local. constructor.
                1: {
                  repeat rewrite (vclosed_ignores_ren); auto with examples.
                  repeat rewrite (vclosed_ignores_sub); auto with examples.
                  all: try apply drop_helper2.
                  opose proof* (EReceive_scope ([([PVar], ˝ VLit "true",
                                        ° ECall (˝ VLit "erlang") (˝ VLit "!")
                                            [˝ VPid ι;
                                             ° ECall (˝ VLit "erlang") 
                                                 (˝ VLit "++")
                                                 [˝ VVar 0; ˝ meta_to_cons (map f (drop idx l'))]])]) (˝VLit "infinity"%string) (˝VNil) 0).
                  2-3: scope_solver.
                  {
                    constructor; auto. split. scope_solver.
                    do 6 scope_solver_step.
                    all: intros; destruct i; try destruct i; try destruct i.
                    1,3-5,7-9,11-12: scope_solver.
                    1: scope_solver_step; eapply loosen_scope_val; try apply drop_helper2; lia.
                    all: do 6 scope_solver_step.
                  }
                  inv H. inv H2. constructor; auto.
                  intros. simpl in *.
                  specialize (H3 0 ltac:(lia)). simpl in H3. simpl. apply H3.
                }
                eapply lsstep. apply p_local. constructor.
                eapply lsstep. apply p_local. econstructor. congruence. simpl. reflexivity.
                simpl. repeat rewrite (vclosed_ignores_sub); auto with examples.
                repeat rewrite (vclosed_ignores_ren); auto with examples.
                all: try apply drop_helper2.
                eapply lsstep. apply p_local. constructor.
                eapply lsstep. apply p_local. constructor.
                (* message_peek *)
                apply eval_helper_peek_message.
              }
              {
                constructor. 2: repeat constructor.
                by right; left.
              }
            }
            (* parent sends the result *)
            eapply n_trans. apply n_send. constructor. assumption.
            (* child process should be terminated *)
            setoid_rewrite insert_commute.
            2: {
              set_solver.
            }
            eapply n_trans. apply n_other. apply p_terminate. by clear; set_solver.
            setoid_rewrite gset_to_gmap_empty.
            apply n_refl.
          }
          { (* equivalence - we need two helpers about dead processes and ether inserts *)
            eapply barbedBisim_trans.
            apply barbedBisim_sym.
            pose proof (dead_process_bisim {[ι]} (etherAdd ι0 ι (SMessage (meta_to_cons (map f l'))) (<[(x, ι0):=[]]> ∅), <[ι0:=inl ([], RValSeq [meta_to_cons (map f l')], emptyBox, ∅, false)]> ∅)) as XXX. (* again, direct apply won't work for some reason *)
            apply XXX.
            1: set_solver.
            1: set_solver.
            simpl. (* now the pools are equal, we have to do the same for the ethers *)
            unfold etherAdd. setoid_rewrite lookup_empty.
            setoid_rewrite lookup_insert_ne.
            2: set_solver.
            setoid_rewrite lookup_empty.
            setoid_rewrite insert_commute.
            2: set_solver.
            remember (insert (ι0, ι) _ ∅) as E.
            apply barbedBisim_sym.
            apply ether_empty_update_bisim.
            clear-Hbase. set_solver.
            simpl. subst E. left.
            setoid_rewrite lookup_insert_ne. set_solver.
            set_solver.
          }
        }
        intros. inv H.
        + put (lookup ι0 : ProcessPool -> _) on H2 as HX2.
          assert (ι0 <> ι_base). {
            intro. subst. setoid_rewrite lookup_insert in HX2. inv HX2. inv H6.
          }
          setoid_rewrite lookup_insert in HX2.
          setoid_rewrite lookup_insert_ne in HX2; auto.
          symmetry in HX2. apply lookup_insert_Some in HX2. destruct HX2 as [HX2 | HX2].
          2: { clear-HX2. set_solver. }
          destruct HX2 as [EQ1 EQ2]. inv EQ2. clear H0.
          remember (inl _) as recp in H2 at 2.
          assert (forall p, ι0 ↦ p ∥ prs = ι0 ↦ p ∥ ι_base ↦ recp ∥ ∅) as XXX. {
            intros. apply map_eq. intros.
            destruct (decide (i = ι0)).
            * subst. by setoid_rewrite lookup_insert.
            * setoid_rewrite lookup_insert_ne; auto.
              put (lookup i : ProcessPool -> _) on H2 as HX2.
              destruct (decide (i = ι_base)).
              - subst. setoid_rewrite lookup_insert in HX2.
                setoid_rewrite lookup_insert_ne in HX2; auto.
                setoid_rewrite lookup_insert. assumption.
              - setoid_rewrite lookup_insert_ne in HX2; auto.
                setoid_rewrite lookup_insert_ne in HX2; auto.
                setoid_rewrite lookup_insert_ne; auto.
          }
          rewrite XXX in *. clear H2. inv H6.
          eexists. exists []. split. apply n_refl.
          (* child terminates *)
          eapply barbedBisim_trans.
          {
            apply barbedBisim_sym.
            pose proof (almost_terminated_bisim {[ι]} (etherAdd ι0 ι' (SMessage (meta_to_cons (map f (take idx l')))) ∅, ι'
   ↦ inl
       ([FParams (IPrimOp "recv_wait_timeout") [] [];
         FLet 1
           (° ECase (˝ VVar 0)
                [([PLit "true"], ˝ VLit "true", ˝ VNil);
                 ([PLit "false"], ˝ VLit "true",
                  ° EApp
                      (˝ VClos
                           [(0, 0,
                             ° ELet 2 (° EPrimOp "recv_peek_message" [])
                                 (° ECase (˝ VVar 0)
                                      [([PLit "true"], ˝ VLit "true",
                                        ° ECase (˝ VVar 1)
                                            [([PVar], ˝ VLit "true",
                                              ° ESeq (° EPrimOp "remove_message" [])
                                                  (° ECall (˝ VLit "erlang") 
                                                       (˝ VLit "!")
                                                       [˝ VPid ι;
                                                        ° ECall 
                                                            (˝ VLit "erlang")
                                                            (˝ VLit "++")
                                                            [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                             ([PVar], ˝ VLit "true",
                                              ° ESeq (° EPrimOp "recv_next" [])
                                                  (° EApp (˝ VFunId (3, 0)) []))]);
                                       ([PLit "false"], ˝ VLit "true",
                                        ° ELet 1
                                            (° EPrimOp "recv_wait_timeout"
                                                 [˝ VLit "infinity"])
                                            (° ECase (˝ VVar 0)
                                                 [([PLit "true"], ˝ VLit "true", ˝ VNil);
                                                  ([PLit "false"], ˝ 
                                                   VLit "true",
                                                   ° EApp (˝ VFunId (3, 0)) [])]))]))] 0 0
                           (° ELet 2 (° EPrimOp "recv_peek_message" [])
                                (° ECase (˝ VVar 0)
                                     [([PLit "true"], ˝ VLit "true",
                                       ° ECase (˝ VVar 1)
                                           [([PVar], ˝ VLit "true",
                                             ° ESeq (° EPrimOp "remove_message" [])
                                                 (° ECall (˝ VLit "erlang") 
                                                      (˝ VLit "!")
                                                      [˝ VPid ι;
                                                       ° ECall 
                                                           (˝ VLit "erlang") 
                                                           (˝ VLit "++")
                                                           [˝ 
                                                            VVar 0;
                                                            ˝ 
                                                            meta_to_cons
                                                             (map f (drop idx l'))]]));
                                            ([PVar], ˝ VLit "true",
                                             ° ESeq (° EPrimOp "recv_next" [])
                                                 (° EApp (˝ VFunId (3, 0)) []))]);
                                      ([PLit "false"], ˝ VLit "true",
                                       ° ELet 1
                                           (° EPrimOp "recv_wait_timeout"
                                                [˝ VLit "infinity"])
                                           (° ECase (˝ VVar 0)
                                                [([PLit "true"], ˝ VLit "true", ˝ VNil);
                                                 ([PLit "false"], ˝ 
                                                  VLit "true", ° 
                                                  EApp (˝ VFunId (3, 0)) [])]))]))) [])])],
        RValSeq [VLit "infinity"], emptyBox, ∅, false) ∥ ∅)) as HH.
            apply HH; clear HH.
            - setoid_rewrite dom_insert_L. set_solver.
            - set_solver.
          }
          (* parent receives *)
          constructor.
          (* etherAdd needs special care in this case *)
          2,4: intros; exists source, []; eexists; simpl; split; try by constructor.
          2: {
            unfold etherAdd. simpl. setoid_rewrite lookup_empty.
            setoid_rewrite lookup_insert_ne. by setoid_rewrite lookup_empty.
            intro Y. inv Y. set_solver.
          }
          2: {
            unfold etherAdd. simpl. setoid_rewrite lookup_empty.
            setoid_rewrite lookup_insert_ne. by setoid_rewrite lookup_empty.
            intro Y. inv Y. set_solver.
          }
          (***)
          2: {
            (* again, we proved this already to some extent *)
            intros. assert (ι' = ι1). {
              destruct B'.
              apply deconstruct_reduction in H0. destruct_hyps.
              put (lookup ι1 : ProcessPool -> _) on H0 as H'.
              setoid_rewrite lookup_insert in H'. destruct (decide (ι' = ι1)).
              assumption.
              setoid_rewrite lookup_insert_ne in H'; auto. set_solver.
            }
            subst.
            assert (a = ASend ι1 ι (SMessage (meta_to_cons (map f l')))). {
              inv H0.
              * put (lookup ι1 : ProcessPool -> _) on H3 as P.
                setoid_rewrite lookup_insert in P. inv P. by inv H8.
              * clear-H3. unfold etherPop in H3. repeat case_match; try congruence.
                set_solver.
              * put (lookup ι1 : ProcessPool -> _) on H2 as P.
                setoid_rewrite lookup_insert in P. inv P.
                destruct_or! H9; inv H3; try inv H14; cbn in *; try congruence.
              * put (lookup ι1 : ProcessPool -> _) on H2 as P.
                setoid_rewrite lookup_insert in P. inv P.
                inv H3. inv H16.
            }
            subst. inv H0. 2: { destruct_or! H9; congruence. } clear H2.
            put (lookup ι1 : ProcessPool -> _) on H3 as P.
            setoid_rewrite lookup_insert in P. inv P. inv H12.
            clear X.
            (* prs = ∅ *)
            assert (forall p, ι1 ↦ p ∥ prs0 = ι1 ↦ p ∥ ∅) as X. {
              intros.
              apply map_eq. intros. put (lookup i : ProcessPool -> _) on H3 as D.
              destruct (decide (i = ι1)).
              * subst. by setoid_rewrite lookup_insert.
              * setoid_rewrite lookup_insert_ne in D; auto.
                by setoid_rewrite lookup_insert_ne.
            }
            clear H3. rewrite X in *.
            (**)
            do 2 eexists. split.
            {
              (* reductions *)
              (* parent receive message recv_timeout then message peek
              *)
              eapply n_trans. apply n_arrive with (ι0 := ι0).
              {
                unfold etherAdd, etherPop.
                setoid_rewrite lookup_empty.
                setoid_rewrite lookup_insert.
                setoid_rewrite lookup_empty.
                setoid_rewrite insert_insert.
                reflexivity.
              }
              {
                constructor.
              }
              eapply closureNodeSem_trans.
              {
                eapply process_local_to_node.
                {
                  (* recv_timeout *)
                  eapply lsstep. apply p_recv_wait_timeout_new_message.
                  eapply lsstep. apply p_local. constructor. reflexivity.
                  simpl. eapply lsstep. apply p_local. constructor.
                  repeat rewrite (vclosed_ignores_sub); auto with examples.
                  2: apply drop_helper2.
                  simpl. eapply lsstep. apply p_local. constructor. scope_solver.
                  eapply lsstep. apply p_local. apply eval_step_case_not_match. reflexivity.
                  eapply lsstep. apply p_local. apply eval_step_case_match. reflexivity.
                  eapply lsstep. apply p_local. constructor. scope_solver.
                  eapply lsstep. apply p_local. constructor.
                  simpl. repeat rewrite (vclosed_ignores_sub); auto with examples.
                  2: apply drop_helper2.
                  eapply lsstep. apply p_local. constructor.
                  eapply lsstep. apply p_local. constructor.
                  1: {
                    repeat rewrite (vclosed_ignores_ren); auto with examples.
                    repeat rewrite (vclosed_ignores_sub); auto with examples.
                    all: try apply drop_helper2.
                    opose proof* (EReceive_scope ([([PVar], ˝ VLit "true",
                                          ° ECall (˝ VLit "erlang") (˝ VLit "!")
                                              [˝ VPid ι;
                                               ° ECall (˝ VLit "erlang") 
                                                   (˝ VLit "++")
                                                   [˝ VVar 0; ˝ meta_to_cons (map f (drop idx l'))]])]) (˝VLit "infinity"%string) (˝VNil) 0).
                    2-3: scope_solver.
                    {
                      constructor; auto. split. scope_solver.
                      do 6 scope_solver_step.
                      all: intros; destruct i; try destruct i; try destruct i.
                      1,3-5,7-9,11-12: scope_solver.
                      1: scope_solver_step; eapply loosen_scope_val; try apply drop_helper2; lia.
                      all: do 6 scope_solver_step.
                    }
                    inv H0. inv H3. constructor; auto.
                    intros. simpl in *.
                    specialize (H4 0 ltac:(lia)). simpl in H4. simpl. apply H4.
                  }
                  eapply lsstep. apply p_local. constructor.
                  eapply lsstep. apply p_local. econstructor. congruence. simpl. reflexivity.
                  simpl. repeat rewrite (vclosed_ignores_sub); auto with examples.
                  repeat rewrite (vclosed_ignores_ren); auto with examples.
                  all: try apply drop_helper2.
                  eapply lsstep. apply p_local. constructor.
                  eapply lsstep. apply p_local. constructor.
                  (* message_peek *)
                  apply eval_helper_peek_message.
                }
                {
                  constructor. 2: repeat constructor.
                  by right; left.
                }
              }
              (* parent sends the result *)
              eapply n_trans. apply n_send. constructor. assumption.
              apply n_refl.
            }
            { (* equivalence - we need two helpers about dead processes and ether inserts *)
              simpl. (* now the pools are equal, we have to do the same for the ethers *)
              unfold etherAdd. setoid_rewrite lookup_empty.
              setoid_rewrite lookup_insert_ne.
              2: set_solver.
              setoid_rewrite lookup_empty.
              remember (insert (ι1, ι) _ ∅) as E.
              setoid_rewrite insert_commute. 2: intro Y; inv Y; lia.
              apply barbedBisim_sym.
              setoid_rewrite HeqE.
              apply ether_empty_update_bisim.
              clear-Hbase. set_solver.
              simpl. subst E. left.
              setoid_rewrite lookup_insert_ne. set_solver.
              set_solver.
            }
          }
          {
            clear XX XXX. intros.
            inv H0.
            * put (lookup ι1 : ProcessPool -> _) on H3 as XX.
              setoid_rewrite lookup_insert in XX.
              destruct (decide (ι' = ι1)).
              - subst. setoid_rewrite lookup_insert in XX. inv XX.
                inv H8.
              - by setoid_rewrite lookup_insert_ne in XX.
            (* arrive *)
            * unfold etherPop, etherAdd in H3.
              setoid_rewrite lookup_empty in H3.
              destruct (decide ((ι0, ι') = (ι3, ι1))).
              2: {
                setoid_rewrite lookup_insert_ne in H3; auto.
                by setoid_rewrite lookup_empty in H3.
              }
              inv e. setoid_rewrite lookup_insert in H3.
              setoid_rewrite lookup_empty in H3.
              setoid_rewrite insert_insert in H3. inv H3.
              put (lookup ι1 : ProcessPool -> _) on H2 as HX1.
              setoid_rewrite lookup_insert in HX1. inv HX1.
              assert (forall p, ι1 ↦ p ∥ prs0 = ι1 ↦ p ∥ ∅) as XX. {
                intros. apply map_eq. intros.
                put (lookup i : ProcessPool -> _) on H2 as HX2.
                destruct (decide (i = ι1)).
                * subst. by setoid_rewrite lookup_insert.
                * setoid_rewrite lookup_insert_ne in HX2; auto.
                  by setoid_rewrite lookup_insert_ne.
              }
              rewrite XX in *. clear XX H2.
              inv H9.
              eexists. exists []. split. apply n_refl.
              (* receive finished *)
              (* cleanup of empty ether update: *)
              eapply barbedBisim_trans.
              apply barbedBisim_sym.
              epose proof (ether_empty_update_bisim {[ι]} _ (∅,
 ι1
 ↦ inl
     ([FParams (IPrimOp "recv_wait_timeout") [] [];
       FLet 1
         (° ECase (˝ VVar 0)
              [([PLit "true"], ˝ VLit "true", ˝ VNil);
               ([PLit "false"], ˝ VLit "true",
                ° EApp
                    (˝ VClos
                         [(0, 0,
                           ° ELet 2 (° EPrimOp "recv_peek_message" [])
                               (° ECase (˝ VVar 0)
                                    [([PLit "true"], ˝ VLit "true",
                                      ° ECase (˝ VVar 1)
                                          [([PVar], ˝ VLit "true",
                                            ° ESeq (° EPrimOp "remove_message" [])
                                                (° ECall (˝ VLit "erlang") 
                                                     (˝ VLit "!")
                                                     [˝ VPid ι;
                                                      ° ECall 
                                                          (˝ VLit "erlang") 
                                                          (˝ VLit "++")
                                                          [˝ VVar 0;
                                                           ˝ meta_to_cons
                                                             (map f (drop idx l'))]]));
                                           ([PVar], ˝ VLit "true",
                                            ° ESeq (° EPrimOp "recv_next" [])
                                                (° EApp (˝ VFunId (3, 0)) []))]);
                                     ([PLit "false"], ˝ VLit "true",
                                      ° ELet 1
                                          (° EPrimOp "recv_wait_timeout"
                                               [˝ VLit "infinity"])
                                          (° ECase (˝ VVar 0)
                                               [([PLit "true"], ˝ VLit "true", ˝ VNil);
                                                ([PLit "false"], ˝ 
                                                 VLit "true", ° 
                                                 EApp (˝ VFunId (3, 0)) [])]))]))] 0 0
                         (° ELet 2 (° EPrimOp "recv_peek_message" [])
                              (° ECase (˝ VVar 0)
                                   [([PLit "true"], ˝ VLit "true",
                                     ° ECase (˝ VVar 1)
                                         [([PVar], ˝ VLit "true",
                                           ° ESeq (° EPrimOp "remove_message" [])
                                               (° ECall (˝ VLit "erlang") 
                                                    (˝ VLit "!")
                                                    [˝ VPid ι;
                                                     ° ECall (˝ VLit "erlang")
                                                         (˝ VLit "++")
                                                         [˝ VVar 0;
                                                          ˝ meta_to_cons
                                                             (map f (drop idx l'))]]));
                                          ([PVar], ˝ VLit "true",
                                           ° ESeq (° EPrimOp "recv_next" [])
                                               (° EApp (˝ VFunId (3, 0)) []))]);
                                    ([PLit "false"], ˝ VLit "true",
                                     ° ELet 1
                                         (° EPrimOp "recv_wait_timeout"
                                              [˝ VLit "infinity"])
                                         (° ECase (˝ VVar 0)
                                              [([PLit "true"], ˝ VLit "true", ˝ VNil);
                                               ([PLit "false"], ˝ 
                                                VLit "true", ° 
                                                EApp (˝ VFunId (3, 0)) [])]))]))) [])])],
      RValSeq [VLit "infinity"], mailboxPush emptyBox (meta_to_cons (map f (take idx l'))), ∅,
      false) ∥ ∅)) as Heth. simpl in Heth. eapply Heth.
              1-2: set_solver.
              { (* next: wait timeout succeeds - again low level reasoning needed *)
                constructor.
                2,4: intros; exists source, []; eexists; simpl; split; try by constructor.
                2: {
                  (* again, we proved this already to some extent *)
                  intros. assert (ι0 = ι1). {
                    destruct B'.
                    apply deconstruct_reduction in H0. destruct_hyps.
                    put (lookup ι0 : ProcessPool -> _) on H0 as H'.
                    setoid_rewrite lookup_insert in H'. destruct (decide (ι0 = ι1)).
                    assumption.
                    setoid_rewrite lookup_insert_ne in H'; auto. set_solver.
                  }
                  subst.
                  assert (a = ASend ι1 ι (SMessage (meta_to_cons (map f l')))). {
                    inv H0.
                    * put (lookup ι1 : ProcessPool -> _) on H3 as P.
                      setoid_rewrite lookup_insert in P. inv P. by inv H8.
                    * clear-H3. unfold etherPop in H3. repeat case_match; try congruence.
                      set_solver.
                    * put (lookup ι1 : ProcessPool -> _) on H2 as P.
                      setoid_rewrite lookup_insert in P. inv P.
                      destruct_or! H9; inv H3; try inv H14; cbn in *; try congruence.
                    * put (lookup ι1 : ProcessPool -> _) on H2 as P.
                      setoid_rewrite lookup_insert in P. inv P.
                      inv H3. inv H16.
                  }
                  subst. inv H0. 2: { destruct_or! H9; congruence. } clear H2.
                  put (lookup ι1 : ProcessPool -> _) on H3 as P.
                  setoid_rewrite lookup_insert in P. inv P. inv H12.
                  clear X.
                  (* prs = ∅ *)
                  assert (forall p, ι1 ↦ p ∥ prs1 = ι1 ↦ p ∥ ∅) as X. {
                    intros.
                    apply map_eq. intros. put (lookup i : ProcessPool -> _) on H3 as D.
                    destruct (decide (i = ι1)).
                    * subst. by setoid_rewrite lookup_insert.
                    * setoid_rewrite lookup_insert_ne in D; auto.
                      by setoid_rewrite lookup_insert_ne.
                  }
                  clear H3. rewrite X in *.
                  (**)
                  do 2 eexists. split.
                  {
                    (* reductions *)
                    (* parent recv_timeout then message peek
                    *)
                    eapply closureNodeSem_trans.
                    {
                      eapply process_local_to_node.
                      {
                        (* recv_timeout *)
                        eapply lsstep. apply p_recv_wait_timeout_new_message.
                        eapply lsstep. apply p_local. constructor. reflexivity.
                        simpl. eapply lsstep. apply p_local. constructor.
                        repeat rewrite (vclosed_ignores_sub); auto with examples.
                        2: apply drop_helper2.
                        simpl. eapply lsstep. apply p_local. constructor. scope_solver.
                        eapply lsstep. apply p_local. apply eval_step_case_not_match. reflexivity.
                        eapply lsstep. apply p_local. apply eval_step_case_match. reflexivity.
                        eapply lsstep. apply p_local. constructor. scope_solver.
                        eapply lsstep. apply p_local. constructor.
                        simpl. repeat rewrite (vclosed_ignores_sub); auto with examples.
                        2: apply drop_helper2.
                        eapply lsstep. apply p_local. constructor.
                        eapply lsstep. apply p_local. constructor.
                        1: {
                          repeat rewrite (vclosed_ignores_ren); auto with examples.
                          repeat rewrite (vclosed_ignores_sub); auto with examples.
                          all: try apply drop_helper2.
                          opose proof* (EReceive_scope ([([PVar], ˝ VLit "true",
                                                ° ECall (˝ VLit "erlang") (˝ VLit "!")
                                                    [˝ VPid ι;
                                                     ° ECall (˝ VLit "erlang") 
                                                         (˝ VLit "++")
                                                         [˝ VVar 0; ˝ meta_to_cons (map f (drop idx l'))]])]) (˝VLit "infinity"%string) (˝VNil) 0).
                          2-3: scope_solver.
                          {
                            constructor; auto. split. scope_solver.
                            do 6 scope_solver_step.
                            all: intros; destruct i; try destruct i; try destruct i.
                            1,3-5,7-9,11-12: scope_solver.
                            1: scope_solver_step; eapply loosen_scope_val; try apply drop_helper2; lia.
                            all: do 6 scope_solver_step.
                          }
                          inv H0. inv H3. constructor; auto.
                          intros. simpl in *.
                          specialize (H4 0 ltac:(lia)). simpl in H4. simpl. apply H4.
                        }
                        eapply lsstep. apply p_local. constructor.
                        eapply lsstep. apply p_local. econstructor. congruence. simpl. reflexivity.
                        simpl. repeat rewrite (vclosed_ignores_sub); auto with examples.
                        repeat rewrite (vclosed_ignores_ren); auto with examples.
                        all: try apply drop_helper2.
                        eapply lsstep. apply p_local. constructor.
                        eapply lsstep. apply p_local. constructor.
                        (* message_peek *)
                        apply eval_helper_peek_message.
                      }
                      {
                        constructor. 2: repeat constructor.
                        by right; left.
                      }
                    }
                    (* parent sends the result *)
                    eapply n_trans. apply n_send. constructor. assumption.
                    apply n_refl.
                  }
                  { (* equivalence - we need two helpers about dead processes and ether inserts *)
                    simpl. (* now the pools are equal, we have to do the same for the ethers *)
                    unfold etherAdd. setoid_rewrite lookup_empty.
                    apply barbedBisim_refl.
                  }
                }
                intros. inv H0.
                * put (lookup ι0 : ProcessPool -> _) on H3 as XX.
                  setoid_rewrite lookup_insert in XX.
                  destruct (decide (ι0 = ι1)).
                  - subst. setoid_rewrite lookup_insert in XX. inv XX.
                    inv H8.
                  - by setoid_rewrite lookup_insert_ne in XX; auto.
                * clear -H3. unfold etherPop in H3. by setoid_rewrite lookup_empty in H3.
                * put (lookup ι0 : ProcessPool -> _) on H2 as XX.
                  setoid_rewrite lookup_insert in XX.
                  destruct (decide (ι0 = ι1)).
                  2: by setoid_rewrite lookup_insert_ne in XX; auto.
                  subst. setoid_rewrite lookup_insert in XX. inv XX.
                  destruct_or! H9; subst; inv H3.
                  1: inv H12; inv H9.
                  congruence.
                  assert (forall p, ι1 ↦ p ∥ Π1 = ι1 ↦ p ∥ ∅) as XXX. {
                    intros. apply map_eq. intros.
                    destruct (decide (i = ι1)).
                    * subst. by setoid_rewrite lookup_insert.
                    * setoid_rewrite lookup_insert_ne; auto.
                      put (lookup i : ProcessPool -> _) on H2 as HX2.
                      by setoid_rewrite lookup_insert_ne in HX2; auto.
                  }
                  rewrite XXX in *. clear H2 XXX.
                  eexists. exists []. split. apply n_refl.
                  eapply barbedBisim_trans.
                  {
                    eapply normalisation_τ_many_bisim.
                    1: shelve.
                    1: set_solver.
                    apply sequential_to_node.
                    do 9 do_step.

                    1: {
                        repeat rewrite (vclosed_ignores_ren); auto with examples.
                        repeat rewrite (vclosed_ignores_sub); auto with examples.
                        all: try apply drop_helper2.
                        opose proof* (EReceive_scope ([([PVar], ˝ VLit "true",
                                              ° ECall (˝ VLit "erlang") (˝ VLit "!")
                                                  [˝ VPid ι;
                                                   ° ECall (˝ VLit "erlang") 
                                                       (˝ VLit "++")
                                                       [˝ VVar 0; ˝ meta_to_cons (map f (drop idx l'))]])]) (˝VLit "infinity"%string) (˝VNil) 0).
                        2-3: scope_solver.
                        {
                          constructor; auto. split. scope_solver.
                          do 6 scope_solver_step.
                          all: intros; destruct i; try destruct i; try destruct i.
                          1,3-5,7-9,11-12: scope_solver.
                          1: scope_solver_step; eapply loosen_scope_val; try apply drop_helper2; lia.
                          all: do 6 scope_solver_step.
                        }
                        inv H0. inv H3. constructor; auto.
                        intros. simpl in *.
                        specialize (H4 0 ltac:(lia)). simpl in H4. simpl. apply H4.
                    }

                    repeat rewrite (vclosed_ignores_sub); auto with examples.
                    2-4: apply drop_helper2.
                    do_step. econstructor 2. econstructor. congruence. simpl. reflexivity.
                    repeat rewrite (vclosed_ignores_sub); auto with examples.
                    repeat rewrite (vclosed_ignores_ren); auto with examples.
                    all: try apply drop_helper2.
                    do 2 do_step.
                    constructor 1.
                  }
                  (* peek_message succeeds - this was done previously *)
                  by apply bisim_helper.
                * put (lookup ι0 : ProcessPool -> _) on H2 as XX.
                  setoid_rewrite lookup_insert in XX.
                  destruct (decide (ι0 = ι1)).
                  - subst. setoid_rewrite lookup_insert in XX. inv XX.
                    inv H16.
                  - by setoid_rewrite lookup_insert_ne in XX; auto.
              }
            * put (lookup ι1 : ProcessPool -> _) on H2 as XX.
              setoid_rewrite lookup_insert in XX.
              destruct (decide (ι' = ι1)).
              - subst. setoid_rewrite lookup_insert in XX. inv XX.
                destruct_or!; subst; inv H3. inv H12. inv H9.
                congruence.
              - by setoid_rewrite lookup_insert_ne in XX.
            * put (lookup ι1 : ProcessPool -> _) on H2 as XX.
              setoid_rewrite lookup_insert in XX.
              destruct (decide (ι' = ι1)).
              - subst. setoid_rewrite lookup_insert in XX. inv XX.
                inv H16.
              - by setoid_rewrite lookup_insert_ne in XX.
          }
        + clear-H2. unfold etherPop in H2. by setoid_rewrite lookup_empty in H2.
        + put (lookup ι0 : ProcessPool -> _) on H1 as HX1.
          setoid_rewrite lookup_insert in HX1.
          destruct (decide (ι0 = ι_base)).
          ** subst. setoid_rewrite lookup_insert in HX1. inv HX1.
             destruct_or! H8; subst; inv H2. inv H9. inv H8.
             congruence.
          ** setoid_rewrite lookup_insert_ne in HX1; auto.
             destruct (decide (ι0 = x)).
             -- subst. setoid_rewrite lookup_insert in HX1. inv HX1.
                destruct_or! H8; subst; inv H2. inv H9. inv H8.
             -- setoid_rewrite lookup_insert_ne in HX1; auto. clear-HX1. set_solver.
        + put (lookup ι0 : ProcessPool -> _) on H1 as HX1.
          setoid_rewrite lookup_insert in HX1.
          destruct (decide (ι0 = ι_base)).
          ** subst. setoid_rewrite lookup_insert in HX1. inv HX1. inv H14.
          ** setoid_rewrite lookup_insert_ne in HX1; auto.
             destruct (decide (ι0 = x)).
             -- subst. setoid_rewrite lookup_insert in HX1. inv HX1. inv H14.
             -- setoid_rewrite lookup_insert_ne in HX1; auto. clear-HX1. set_solver.
      - put (lookup ι0 : ProcessPool -> _) on H1 as HX1.
        setoid_rewrite lookup_insert in HX1.
        destruct (decide (ι0 = ι_base)).
        + subst. setoid_rewrite lookup_insert in HX1. inv HX1. inv H13.
        + setoid_rewrite lookup_insert_ne in HX1; auto.
          destruct (decide (ι0 = x)).
          ** subst. setoid_rewrite lookup_insert in HX1. inv HX1. inv H13.
          ** setoid_rewrite lookup_insert_ne in HX1; auto. clear-HX1. set_solver.
  }
Unshelve.
  apply Forall_app; split.
  all: try by apply Forall_repeat.
  all: try by repeat constructor.
Qed. (* This takes an awful lot time (obviously) ~ 2-3 minutes*)
Transparent map_clos.

End map_pmap.
