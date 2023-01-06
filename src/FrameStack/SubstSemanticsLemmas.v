From CoreErlang.FrameStack Require Export SubstSemantics Termination.
From Coq Require Export Logic.ProofIrrelevance Program.Equality.
Import ListNotations.

(** Properties of the semantics *)
Theorem step_determinism {e e' fs fs'} :
  ⟨ fs, e ⟩ --> ⟨fs', e'⟩ ->
  (forall fs'' e'', ⟨fs, e⟩ --> ⟨fs'', e''⟩ -> fs'' = fs' /\ e'' = e').
Proof.
  intro H. dependent induction H; intros;
  match goal with
  | [H : ⟨ _, _ ⟩ --> ⟨_, _⟩ |- _] => inversion H; subst; auto
  end.
  (* case: *)
  * rewrite H in H9. inversion H9; now subst.
  * rewrite H in H9; congruence.
  * rewrite H in H9; congruence.
  * rewrite H in H8. inversion H8; now subst.
  (* exceptions: *)
  * specialize (H5 vl1 e2 3 e3). congruence.
  * specialize (H vl1 e2 3 e3). congruence.
Qed.

Theorem value_nostep v :
  is_result v ->
  forall fs' v', ⟨ [], v ⟩ --> ⟨fs' , v'⟩ -> False.
Proof.
  intros H fs' v' HD. inversion H; subst; inversion HD.
Qed.

Theorem step_rt_determinism {e v fs fs' k} :
  ⟨fs, e⟩ -[k]-> ⟨fs', v⟩
->
  (forall fs'' v', ⟨fs, e⟩ -[k]-> ⟨fs'', v'⟩ -> fs' = fs'' /\ v' = v).
Proof.
  intro. dependent induction H; intros.
  * inversion H; subst; auto.
  * inversion H1; subst. apply IHstep_rt; auto. eapply step_determinism in H; eauto. destruct H. subst. auto.
Qed.

Ltac destruct_scope :=
  match goal with
  | [H : RED _ ⊢ (RExp _) |- _] => inversion H; subst; clear H
  | [H : RED _ ⊢ (RValSeq _) |- _] => inversion H; subst; clear H
  | [H : RED _ ⊢ (RExc _) |- _] => inversion H; subst; clear H
  | [H : RED _ ⊢ RBox |- _] => clear H
  | [H : FSCLOSED (_ :: _) |- _] => inversion H; subst; clear H
  | [H : FSCLOSED [] |- _] => clear H
  | [H : EXP _ ⊢ VVal _ |- _] => inversion H; subst; clear H
  | [H : EXP _ ⊢ EExp _ |- _] => inversion H; subst; clear H
  | [H : VAL _ ⊢ VNil |- _] => clear H
  | [H : VAL _ ⊢ VLit _ |- _] => clear H
  | [H : VAL _ ⊢ VCons _ _ |- _] => inversion H; subst; clear H
  | [H : VAL _ ⊢ VTuple _ |- _] => inversion H; subst; clear H
  | [H : VAL _ ⊢ VMap _ |- _] => inversion H; subst; clear H
  | [H : VAL _ ⊢ VVar _ |- _] => inversion H; subst; clear H
  | [H : VAL _ ⊢ VFunId _ |- _] => inversion H; subst; clear H
  | [H : VAL _ ⊢ VClos _ _ _ _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ EFun _ _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ EValues _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ ECons _ _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ ETuple _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ EMap _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ ECall _ _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ EPrimOp _ _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ EApp _ _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ ECase _ _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ ELet _ _ _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ ESeq _ _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ ELetRec _ _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ ETry _ _ _ _ _ |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FCons1 _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FCons2 _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FParams _ _ _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FApp1 _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FCase1 _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FCase2 _ _ _ _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FLet _ _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FSeq _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FTry _ _ _ _) |- _] => inversion H; subst; clear H
  end.

Ltac destruct_scopes := repeat destruct_scope.

#[global]
Hint Constructors RedexScope : core. 

(* Maps.v *)
Lemma deflatten_keeps_prop {A} (P : A -> Prop) :
  forall (l : list A),
    Forall P l ->
    Forall (fun '(x, y) => P x /\ P y) (deflatten_list l).
Proof.
  induction l using list_length_ind.
  intro HF.
  destruct l. 2: destruct l.
  * constructor.
  * cbn. constructor.
  * cbn. inversion HF. inversion H3. subst.
    clear HF H3. constructor; auto.
    apply H; simpl; auto.
Qed.

(* Maps.v *)
Lemma map_insert_prop :
  forall (P : Val * Val -> Prop) l k v,
    P (k, v) ->
    Forall P l ->
    Forall P (map_insert k v l).
Proof.
  induction l; intros k v HP HF.
  * constructor; auto.
  * simpl. destruct a as [k' v'].
    destruct_foralls.
    break_match_goal. 2: break_match_goal.
    - constructor. 2: constructor. all: auto.
    - constructor; auto.
    - constructor; auto.
Qed.

(* Maps.v *)
Lemma make_val_map_keeps_prop (P : Val * Val -> Prop) :
  forall l,
    Forall P l ->
    Forall P (make_val_map l).
Proof.
  induction l; intro H.
  * constructor.
  * cbn. destruct a. inversion H. subst. clear H.
    apply IHl in H3. clear IHl.
    now apply map_insert_prop.
Qed.

(* Maps.v *)
Lemma flatten_keeps_prop {A} (P : A -> Prop) :
  forall (l : list (A * A)),
    Forall (fun '(x, y) => P x /\ P y) l ->
    Forall P (flatten_list l).
Proof.
  induction l; intros; simpl in *; auto.
  destruct a.
  destruct_foralls. destruct H2. constructor; auto.
Qed.

Add Search Blacklist "_ind2"
                 "coped_ind"
                 "coped_sind"
                 "FCLOSED_ind"
                 "FCLOSED_sind"
                 "Unnamed_thm".

Lemma closlist_scope Γ ext :
  (forall i : nat,
  i < length ext ->
  EXP length ext + nth i (map (snd ∘ fst) ext) 0 + Γ
  ⊢ nth i (map snd ext) (` VNil))
  ->
  Forall (fun v : Val => VAL Γ ⊢ v) (convert_to_closlist ext).
Proof.
  intros. rewrite indexed_to_forall. Unshelve. 2: exact VNil.
  intros.
  unfold convert_to_closlist in *.
  rewrite map_length in H0. apply H in H0 as H0'.
  replace 0 with ((snd ∘ fst) (0, 0, `VNil)) in H0' by auto.
  replace (`VNil) with (snd (0, 0, `VNil)) in H0' by auto.
  do 2 rewrite map_nth in H0'. simpl in H0'.
  rewrite nth_indep with (d' := VClos ext 0 0 (`VNil)).
  2: now rewrite map_length.
  remember (fun '(y, e) => let '(id, vc) := y in VClos ext id vc e) as F.
  replace (VClos ext 0 0 (`VNil)) with (F (0, 0, `VNil)) by (subst;auto).
  rewrite map_nth. subst.
  destruct (nth i ext (0, 0, ` VNil)). destruct p; cbn in *.
  constructor; auto.
Qed.

#[global]
Hint Constructors ValScoped : core.
#[global]
Hint Constructors ExpScoped : core.
#[global]
Hint Constructors NonValScoped : core.
#[global]
Hint Constructors ICLOSED : core.


(* Auxiliaries.v *)
Lemma subtract_elem_closed Γ:
  forall v1 v2, VAL Γ ⊢ v1 -> VAL Γ ⊢ v2 ->
  VAL Γ ⊢ (subtract_elem v1 v2).
Proof.
  induction v1; intros; cbn; try constructor.
  repeat break_match_goal; destruct_scopes; auto.
Qed.

(* Auxiliaries.v *)
Theorem closed_eval : forall m f vl eff,
  Forall (fun v => VALCLOSED v) vl ->
  REDCLOSED (fst (eval m f vl eff)).
Proof.
  intros. unfold eval.
  break_match_goal; unfold eval_arith, eval_logical, eval_equality,
  eval_transform_list, eval_list_tuple, eval_cmp, eval_io,
  eval_hd_tl, eval_elem_tuple, eval_check, eval_error; try rewrite Heqb.
  all: try destruct vl; try destruct vl.
  all: simpl; try (now (constructor; constructor)).
  all: repeat break_match_goal.
  all: try (constructor; constructor); auto.
  all: try now constructor; auto.
  all: destruct_foralls; destruct_scopes; auto.
  all: try (apply indexed_to_forall; repeat constructor; auto).
  * constructor. apply indexed_to_forall. repeat constructor. auto.
  * clear Heqb eff m f. induction v; cbn.
    all: try (do 2 constructor; apply indexed_to_forall; do 2 constructor; now auto).
    - now do 2 constructor.
    - destruct_scopes. apply IHv1 in H4 as H4'. break_match_goal.
      2: break_match_goal. 3: break_match_goal.
      all: try (do 2 constructor; apply indexed_to_forall; now repeat constructor).
      do 3 constructor; subst; auto.
      apply IHv2 in H5. destruct_scopes. now destruct_foralls.
  * clear Heqb eff m f. generalize dependent v. induction v0; intros; cbn; break_match_goal; try destruct v.
    all: try (do 2 constructor; apply indexed_to_forall; do 2 constructor; now auto).
    1-3: destruct_scopes; do 3 constructor; auto.
    destruct_scopes. destruct v0_2; cbn in *.
    3: {
      apply IHv0_2; auto.
      repeat break_match_goal; auto.
      constructor; auto.
      now apply subtract_elem_closed.
    }
    all: repeat break_match_goal; auto.
    all: constructor; constructor; auto.
    all: try apply subtract_elem_closed; auto.
    all: constructor; auto; now apply subtract_elem_closed.
  * clear Heqb eff m f. induction v; cbn.
    all: destruct_scopes; try (do 2 constructor; apply indexed_to_forall; now repeat constructor).
    do 2 constructor; auto. induction l; constructor.
    - apply (H1 0). simpl. lia.
    - apply IHl. intros. apply (H1 (S i)). simpl. lia.
  * clear Heqb eff m f. generalize dependent v. induction l; cbn; intros.
    - constructor. simpl. lia.
    - destruct v; cbn in Heqs; try congruence.
      destruct_scopes. 
      repeat break_match_hyp; inversion Heqs; subst.
      constructor. apply indexed_to_forall. constructor; auto.
      apply IHl in Heqs0; auto.
      constructor. apply indexed_to_forall. constructor; auto.
      inversion Heqs0. now rewrite <- indexed_to_forall in H1.
  * clear Heqb eff m f. generalize dependent e. induction v; cbn; intros.
    all: try congruence.
    all: try inversion Heqs; subst; clear Heqs.
    all: try (do 2 constructor; apply indexed_to_forall; do 2 constructor; now auto).
    destruct (transform_list v2) eqn:Eq.
    - destruct v2; try congruence; inversion H0; subst.
      all: try (do 2 constructor; apply indexed_to_forall; do 2 constructor; now auto).
    - destruct v2; try congruence; inversion H0; subst.
      all: try (do 2 constructor; apply indexed_to_forall; do 2 constructor; now auto).
      apply IHv2; auto. destruct_scopes. auto.
  * epose proof (proj1 (nth_error_Some l0 (Init.Nat.pred (Pos.to_nat p))) _).
    Unshelve. 2: { intro. rewrite H in Heqo. congruence. }
    eapply nth_error_nth with (d := VNil) in Heqo. subst. now apply H2.
  * remember (Init.Nat.pred (Pos.to_nat p)) as k. clear Heqk Heqb m f p eff.
    generalize dependent l2. revert k. induction l0; intros; simpl in *.
    - destruct k; congruence.
    - destruct k.
      + inversion Heqo. subst. constructor.
        intros. destruct i; simpl in *.
        auto.
        apply (H2 (S i)). lia.
      + break_match_hyp. 2: congruence.
        inversion Heqo; subst; clear Heqo. constructor. simpl.
        intros. destruct i.
        apply (H2 0). lia.
        apply IHl0 in Heqo0. inversion Heqo0. apply (H4 i). lia.
        intros. apply (H2 (S i0)). lia.
  * apply indexed_to_forall in H1. destruct_foralls. now constructor.
  * apply indexed_to_forall in H1. destruct_foralls. now constructor. 
Qed.




Theorem create_result_closed :
  forall vl ident,
    Forall (fun v => VALCLOSED v) vl ->
    ICLOSED ident ->
    REDCLOSED (create_result ident vl).
Proof.
  intros vl ident Hall Hi.
  destruct ident; simpl.
  1-3: constructor; auto.
  1-2: do 2 constructor; auto.
  * now apply (indexed_to_forall _ (fun v => VALCLOSED v) VNil).
  * apply deflatten_keeps_prop in Hall.
    apply make_val_map_keeps_prop in Hall.
    rewrite indexed_to_forall in Hall. Unshelve. 2: exact (VNil, VNil).
    intros. specialize (Hall i H).
    replace VNil with (fst (VNil, VNil)) by auto. rewrite map_nth.
    destruct nth. apply Hall.
  * apply deflatten_keeps_prop in Hall.
    apply make_val_map_keeps_prop in Hall.
    rewrite indexed_to_forall in Hall. Unshelve. 2: exact (VNil, VNil).
    intros. specialize (Hall i H).
    replace VNil with (snd (VNil, VNil)) by auto. rewrite map_nth.
    destruct nth. apply Hall.
  * now apply closed_eval.
  * now apply closed_eval.
  * inversion Hi; subst; clear Hi. destruct v; unfold badfun.
    1-7: constructor; auto; constructor.
    break_match_goal.
    - constructor. destruct_scope.
      apply -> subst_preserves_scope_exp. exact H6.
      apply Nat.eqb_eq in Heqb. rewrite Heqb.
      replace (Datatypes.length ext + Datatypes.length vl + 0) with
              (length (convert_to_closlist ext ++ vl)).
      2: { unfold convert_to_closlist.
           rewrite app_length, map_length. lia.
      }
      apply scoped_list_idsubst. apply Forall_app; split; auto.
      now apply closlist_scope.
    - unfold badarity. constructor. constructor. auto.
Qed.

Lemma Forall_pair {A B} (P1 : A -> Prop) (P2 : B -> Prop) l : forall d1 d2,
  (forall i : nat,
  i < Datatypes.length l -> P1 (nth i (map fst l) d1)) ->
  (forall i : nat,
    i < Datatypes.length l -> P2 (nth i (map snd l) d2)) ->
  Forall (fun '(x, y) => P1 x /\ P2 y) l.
Proof.
  induction l; intros; constructor.
  * destruct a. split. apply (H 0). simpl. lia. apply (H0 0). simpl. lia.
  * eapply IHl; intros.
    apply (H (S i)). simpl. lia.
    apply (H0 (S i)). simpl. lia.
Qed.

(* Matching.v *)
Lemma match_pattern_list_sublist vs :
  forall lp vs', match_pattern_list lp vs = Some vs' ->
    incl vs' vs.
Proof.
  (* Does not hold! One pattern can contain any number of 
     variables. *)
Abort.

(* Matching.v *)
Lemma match_pattern_length :
  forall p v l, match_pattern p v = Some l ->
    PatScope p = length l.
Proof.
  induction p using Pat_ind2 with
    (Q := Forall (fun p => forall v l, match_pattern p v = Some l ->
    PatScope p = length l))
    (R := Forall (fun '(p1, p2) => (forall v l, match_pattern p1 v = Some l ->
    PatScope p1 = length l) /\
    (forall v l, match_pattern p2 v = Some l ->
    PatScope p2 = length l))); simpl; intros.
  * destruct v; now inv H.
  * destruct v; inv H. break_match_hyp; now inv H1.
  * now inv H.
  * destruct_all_hyps. inv H. rewrite app_length. firstorder.
  * destruct_all_hyps. generalize dependent l0. revert l1.
    induction l; intros.
    - destruct_all_hyps. now inv H.
    - destruct_all_hyps. inv H. inv IHp. rewrite app_length.
      apply IHl in Heqo0; auto. cbn. erewrite Heqo0, H1.
      reflexivity. eassumption.
  * destruct_all_hyps. generalize dependent l0. revert l1.
    induction l; intros.
    - destruct_all_hyps. now inv H.
    - destruct_all_hyps. inv H. inv IHp. do 2 rewrite app_length.
      apply IHl in Heqo1; auto. cbn. erewrite Heqo1.
      destruct H1. erewrite H, H0. rewrite Nat.add_assoc. reflexivity.
      all: eassumption.
  * firstorder.
  * firstorder.
  * firstorder.
  * firstorder.
Qed.

(* Matching.v *)
Lemma match_pattern_list_length vs :
  forall lp vs', match_pattern_list lp vs = Some vs' ->
    PatListScope lp = length vs'.
Proof.
  induction vs; destruct lp; intros vs' H; inversion H.
  * reflexivity.
  * repeat break_match_hyp; try congruence.
    inv H1. apply IHvs in Heqo0. cbn. rewrite app_length.
    rewrite <- Heqo0. erewrite match_pattern_length. reflexivity.
    eassumption.
Qed.

(* Matching.v *)
Lemma match_pattern_scope Γ p :
  forall v l, match_pattern p v = Some l ->
    VAL Γ ⊢ v ->
    Forall (fun v => VAL Γ ⊢ v) l.
Proof.
  induction p using Pat_ind2 with
    (Q := Forall (fun p => forall v l, match_pattern p v = Some l ->
    VAL Γ ⊢ v ->
    Forall (fun v => VAL Γ ⊢ v) l))
    (R := Forall (fun '(p1, p2) => (forall v l, match_pattern p1 v = Some l ->
    VAL Γ ⊢ v ->
    Forall (fun v => VAL Γ ⊢ v) l) /\
    (forall v l, match_pattern p2 v = Some l ->
    VAL Γ ⊢ v ->
    Forall (fun v => VAL Γ ⊢ v) l))); simpl; intros.
    * destruct v; now inv H.
    * destruct v; inv H. break_match_hyp; now inv H2.
    * inv H. auto.
    * destruct_all_hyps. destruct_scopes. inv H. apply Forall_app; split.
      - eapply IHp1; eassumption.
      - eapply IHp2; eassumption.
    * destruct_all_hyps. destruct_scopes.
      apply indexed_to_forall in H3.
      generalize dependent l0. generalize dependent l1.
      induction l; intros.
      - destruct_all_hyps. now inv H.
      - destruct_all_hyps. inv H. inv IHp.
        destruct_foralls.
        apply IHl in Heqo0; auto. apply Forall_app; split; auto.
        eapply H1; eassumption.
    * destruct_all_hyps. destruct_scopes.
      generalize dependent l0. generalize dependent l1.
      induction l; intros.
      - destruct_all_hyps. now inv H.
      - destruct_all_hyps. inv H. inv IHp.
        destruct_foralls.
        destruct H1 as [H1f H1s].
        apply IHl in Heqo1; auto.
        2: { intros. apply (H2 (S i)). simpl. lia. }
        2: { intros. apply (H4 (S i)). simpl. lia. }
        apply Forall_app; split; auto.
        2: apply Forall_app; split; auto.
        eapply H1f. exact Heqo. apply (H2 0 ltac:(slia)).
        eapply H1s. exact Heqo0. apply (H4 0 ltac:(slia)).
    * firstorder.
    * firstorder.
    * firstorder.
    * firstorder.
Qed.

(* Matching.v *)
Lemma match_pattern_list_scope Γ vs :
  forall lp vs', match_pattern_list lp vs = Some vs' ->
    Forall (fun v => VAL Γ ⊢ v) vs ->
    Forall (fun v => VAL Γ ⊢ v) vs'.
Proof.
  induction vs; destruct lp; intros vs' H Hall; inv H.
  * auto.
  * inv Hall. destruct_all_hyps. inv H1. apply IHvs in Heqo0; auto.
    apply Forall_app; split; auto.
    eapply match_pattern_scope; eassumption.
Qed.

Theorem step_closedness : forall F e F' e',
   ⟨ F, e ⟩ --> ⟨ F', e' ⟩ -> FSCLOSED F -> REDCLOSED e
->
  FSCLOSED F' /\ REDCLOSED e'.
Proof.
  intros F e F' e' IH. induction IH; intros Hcl1 Hcl2;
  destruct_scopes; destruct_foralls; split; auto.
  all: cbn; try (repeat constructor; now auto).
  all: try now (apply indexed_to_forall in H1; do 2 (constructor; auto)).
  * constructor; auto. constructor; auto.
    apply Forall_app; auto.
    intros. apply H8 in H.
    inv H. simpl in H0. exists x.
    rewrite app_length. simpl. lia.
  * now apply create_result_closed.
  * apply create_result_closed; auto. apply Forall_app; auto.
  * do 2 (constructor; auto).
    epose proof (Forall_pair _ _ _ _ _ H0 H3).
    destruct_foralls. inv H4. constructor; auto.
    now apply flatten_keeps_prop.
    intros. simpl. rewrite length_flatten_list.
    exists (length el). nia.
  * constructor. apply (H0 0). slia.
  * do 2 (constructor; auto).
    now apply indexed_to_forall in H4.
  * constructor. apply -> subst_preserves_scope_exp.
    eassumption.
    now apply scoped_list_idsubst.
  * constructor; auto. constructor.
    now rewrite Nat.add_0_r in H5.
  * setoid_rewrite Nat.add_0_r in H4.
    setoid_rewrite Nat.add_0_r in H5.
    do 2 (constructor; auto).
  * do 2 (constructor; auto).
    - apply (H5 0). simpl. lia.
    - eexists; eassumption.
    - intros. apply (H2 (S i)). simpl. lia.
    - intros. apply (H5 (S i)). simpl. lia.
  * constructor. apply -> subst_preserves_scope_exp.
    apply (H2 0 ltac:(slia)).
    erewrite match_pattern_list_length. 2: exact H.
    apply scoped_list_idsubst.
    eapply match_pattern_list_scope; eassumption.
  * do 2 (constructor; auto).
    - intros. apply (H2 (S i)). simpl. lia.
    - intros. apply (H5 (S i)). simpl. lia.
  * constructor. apply -> subst_preserves_scope_exp. exact H8.
    erewrite match_pattern_list_length. 2: exact H.
    apply scoped_list_idsubst.
    eapply match_pattern_list_scope; eassumption.
  * constructor. apply -> subst_preserves_scope_exp.
    eassumption.
    rewrite Nat.add_0_r.
    replace (length l) with
            (length (convert_to_closlist (map (fun '(x, y) => (0, x, y)) l))).
    2: {
      unfold convert_to_closlist. now do 2 rewrite map_length.
    }
    apply scoped_list_idsubst.
    apply closlist_scope. rewrite map_length. intros.
    specialize (H3 i H). rewrite Nat.add_0_r in *.
    do 2 rewrite map_map.
    remember (fun x : nat * Exp => (snd ∘ fst) (let '(x0, y) := x in (0, x0, y)))
    as F.
    remember (fun x : nat * Exp => snd (let '(x0, y) := x in (0, x0, y)))
    as G.
    replace 0 with (F (0, `VNil)) by (subst;auto).
    replace (`VNil) with (G (0, `VNil)) by (subst;auto).
    do 2 rewrite map_nth.
    replace 0 with (fst (0, `VNil)) in H3 by (subst;auto).
    replace (`VNil) with (snd (0, `VNil)) in H3 by (subst;auto).
    do 2 rewrite map_nth in H3.
    subst; cbn in *. destruct (nth i l (0, ` VNil)). auto.
  * constructor. apply -> subst_preserves_scope_exp.
    eassumption.
    now apply scoped_list_idsubst.
  * constructor. apply -> subst_preserves_scope_exp.
    eassumption.
    repeat apply cons_scope; auto. destruct class; constructor.
  * rewrite Nat.add_0_r in *. do 2 (constructor; auto).
Qed.

Corollary step_any_closedness : forall Fs Fs' e v k,
   ⟨ Fs, e ⟩ -[k]-> ⟨Fs', v⟩ -> FSCLOSED Fs -> REDCLOSED e
->
  REDCLOSED v /\ FSCLOSED Fs'.
Proof.
  intros. induction H; auto.
  * apply step_closedness in H; auto. firstorder.
Qed.

Theorem transitive_eval : forall {n Fs Fs' e e'},
  ⟨ Fs, e ⟩ -[n]-> ⟨ Fs', e' ⟩ -> forall {n' Fs'' e''}, ⟨ Fs', e' ⟩ -[n']-> ⟨ Fs'', e'' ⟩
->
  ⟨ Fs, e ⟩ -[n + n']-> ⟨ Fs'', e''⟩.
Proof.
  intros n Fs F' e e' IH. induction IH; intros; auto.
  simpl. econstructor. exact H. now apply IHIH.
Qed.


Lemma terminates_in_k_step :
  forall fs e fs' e' k, ⟨ fs, e ⟩ --> ⟨ fs', e' ⟩ ->
  | fs', e' | k ↓ ->
  | fs, e | S k ↓.
Proof.
  intros fs e fs' e' k H H0. induction H.
  all: try (now constructor).
  * eapply cool_params_0; eassumption.
  * eapply cool_params; eassumption.
  * eapply step_case_match; eassumption.
  * eapply step_case_true; eassumption.
  * eapply heat_letrec; eassumption.
Qed.

Theorem terminates_in_k_eq_terminates_in_k_sem :
  forall k e fs, terminates_in_k_sem fs e k <-> | fs, e | k ↓.
Proof.
  split.
  {
    revert e fs. induction k; intros e fs H.
    * destruct H as [res [Hres HD]].
      inversion HD; subst. now constructor.
    * destruct H as [res [Hres HD]].
      inversion HD; subst.
      assert (terminates_in_k_sem fs' e' k). {
        eexists. split; eassumption.
      }
      apply IHk in H.
      eapply terminates_in_k_step; eassumption.
  }
  {
    intros. induction H.
    all: try destruct IHterminates_in_k as [res0 [Hres0 HD]].
    all: try (now eexists; split;
                  [eassumption | econstructor;
                      [constructor | assumption]]).
    * eexists. split.
      - eassumption.
      - econstructor. constructor; eassumption.
        eassumption.
    * eexists. split.
      - exact Hres0.
      - econstructor. constructor; eassumption.
        eassumption.
    * eexists. split.
      - eassumption.
      - econstructor. constructor; eassumption.
        eassumption.
    * eexists. split.
      - eassumption.
      - econstructor. constructor; eassumption.
        eassumption.
    * eexists. split.
      - eassumption.
      - econstructor. constructor; eassumption.
        eassumption.
    * eexists. split.
      - eassumption.
      - constructor.
  }
Qed.

Theorem terminates_step :
  forall n fs e, | fs, e | n ↓ -> forall fs' e', ⟨fs, e⟩ --> ⟨fs', e'⟩
->
  | fs', e' | n - 1↓.
Proof.
  intros. apply terminates_in_k_eq_terminates_in_k_sem in H. destruct H. destruct n.
  * destruct H. inv H.
    - subst. inversion H1; subst. inversion H0.
    - subst. inversion H1; subst. inversion H0.
  * destruct H.
    inv H1. subst. apply (step_determinism H0) in H3. inv H3.
    assert (exists y, is_result y /\ ⟨ fs', e' ⟩ -[ n ]-> ⟨ [], y ⟩). { 
      eexists. eauto. }
    apply ex_intro in H6. apply terminates_in_k_eq_terminates_in_k_sem in H1.
    now rewrite Nat.sub_1_r.
Qed.

Corollary term_step_term :
  forall k n fs e, | fs, e | n ↓ -> forall fs' e', ⟨fs, e⟩ -[k]-> ⟨fs', e'⟩
->
  | fs', e' | n - k ↓.
Proof.
  induction k; intros; inversion H0; subst; auto.
  * rewrite Nat.sub_0_r. auto.
  * apply terminates_step with (n := n) in H2; auto.
    eapply IHk in H5; auto. 2: exact H2. now replace (n - S k) with ((n - 1) - k) by lia.
Qed.

Corollary step_term_term :
  forall k n fs e fs' e',
  ⟨fs, e⟩ -[k]-> ⟨fs', e'⟩ -> | fs', e' | n - k ↓ -> n >= k 
->
  | fs, e | n ↓.
Proof.
  intros. apply terminates_in_k_eq_terminates_in_k_sem.
  apply terminates_in_k_eq_terminates_in_k_sem in H0. destruct H0, H0.
  pose proof (transitive_eval H H2). replace (k+(n-k)) with n in H3 by lia.
  eexists. eauto.
Qed.

Corollary step_term_term_plus :
  forall k k2 fs e fs' e', 
  ⟨fs, e⟩ -[k]-> ⟨fs', e'⟩ -> | fs', e' | k2 ↓
->
  | fs, e | k + k2 ↓.
Proof.
  intros. apply terminates_in_k_eq_terminates_in_k_sem.
  apply terminates_in_k_eq_terminates_in_k_sem in H0. destruct H0, H0.
  pose proof (transitive_eval H H1).
  eexists. eauto.
Qed.

Theorem transitive_eval_rev : forall Fs Fs' e e' k1,
  ⟨ Fs, e ⟩ -[k1]-> ⟨ Fs', e' ⟩-> 
  forall Fs'' e'' k2,
  ⟨ Fs, e ⟩ -[k1 + k2]-> ⟨ Fs'', e'' ⟩
->
  ⟨ Fs', e' ⟩ -[k2]-> ⟨ Fs'', e'' ⟩.
Proof.
  intros Fs Fs' e e' k1 IH. induction IH; intros.
  * simpl in H. auto.
  * simpl in H0. inversion H0; subst. eapply step_determinism in H.
    2: exact H2. destruct H; subst.
    apply IHIH in H5. auto.
Qed.

Theorem frame_indep_step : forall e F F' Fs e',
  ⟨ F :: Fs, e ⟩ --> ⟨ F' :: Fs, e' ⟩
->
  forall Fs', ⟨ F :: Fs', e ⟩ --> ⟨ F' :: Fs', e' ⟩.
Proof.
  intros. revert Fs'. dependent induction H; intros.
  all: try constructor; auto.
  all: try (apply cons_neq in x; contradiction).
  all: symmetry in x; try (apply cons_neq in x; contradiction).
Qed.

Theorem frame_indep_red : forall e F Fs e',
  ⟨ F :: Fs, e ⟩ --> ⟨ Fs, e' ⟩
->
  forall Fs', ⟨ F :: Fs', e ⟩ --> ⟨ Fs', e' ⟩.
Proof.
  intros. revert Fs'. dependent induction H; intros.
  all: try constructor; auto.
  all: try (apply cons_neq in x; contradiction).
  all: symmetry in x; try (apply cons_cons_neq in x; contradiction).
Qed.

Theorem frame_indep_core : forall k e Fs Fs' v,
  ⟨ Fs, e ⟩ -[k]-> ⟨ Fs', v ⟩
->
  forall Fs'', ⟨ Fs ++ Fs'', e ⟩ -[k]-> ⟨ Fs' ++ Fs'', v ⟩.
Proof.
  induction k; intros.
  * inversion H. subst. constructor.
  * inv H. inv H1.
    all: try now (simpl; econstructor; try constructor; auto).
    all: try (eapply IHk in H4; simpl in *; econstructor; [constructor | exact H4]); auto.
Qed.

Theorem frame_indep_nil : forall k e Fs v,
  ⟨ Fs, e ⟩ -[k]-> ⟨ [], v ⟩
->
  forall Fs', ⟨ Fs ++ Fs', e ⟩ -[k]-> ⟨ Fs', v ⟩.
Proof.
  intros. eapply frame_indep_core in H. exact H.
Qed.

#[global]
Hint Constructors is_result : core.


Lemma params_eval :
  forall vals ident vl exps e Fs (v : Val),
  ⟨ FParams ident vl ((map VVal vals) ++ e :: exps) :: Fs, RValSeq [v]⟩ -[1 + 2 * length vals]->
  ⟨ FParams ident (vl ++ v :: vals) exps :: Fs, e⟩.
Proof.
  induction vals; simpl; intros.
  * econstructor. constructor. constructor.
  * specialize (IHvals ident (vl ++ [v]) exps e Fs a).
    econstructor. constructor.
    econstructor. constructor.
    rewrite <- app_assoc in IHvals.
    replace (length vals + S (length vals + 0)) with
            (1 + 2*length vals) by lia. exact IHvals.
Qed.

Lemma params_eval_create :
  forall vals ident vl Fs (v : Val),
  ⟨ FParams ident vl (map VVal vals) :: Fs, RValSeq [v]⟩ -[1 + 2 * length vals]->
  ⟨ Fs, create_result ident (vl ++ v :: vals)⟩.
Proof.
  induction vals; simpl; intros.
  * econstructor. constructor. reflexivity. constructor.
  * specialize (IHvals ident (vl ++ [v]) Fs a).
    econstructor. constructor.
    econstructor. constructor.
    rewrite <- app_assoc in IHvals.
    replace (length vals + S (length vals + 0)) with
            (1 + 2*length vals) by lia. exact IHvals.
Qed.

(* Auxiliaries.v *)
Lemma eval_is_result :
  forall f m vl eff, is_result (fst (eval m f vl eff)).
Proof.
  intros. unfold eval.
  break_match_goal; unfold eval_arith, eval_logical, eval_equality,
  eval_transform_list, eval_list_tuple, eval_cmp, eval_io,
  eval_hd_tl, eval_elem_tuple, eval_check, eval_error; try rewrite Heqb.
  all: repeat break_match_goal.
  all: simpl; try (now (constructor; constructor)).
  all: subst; clear Heqb m f eff.
  * induction v; simpl; auto.
    repeat break_match_goal; auto.
  * revert v. induction v0; destruct v; cbn; auto.
    1-3, 5-9: repeat break_match_goal; auto.
    repeat (break_match_goal; auto; subst); simpl.
  * induction v; simpl; auto.
  * induction vl; simpl; auto.
    repeat break_match_goal; auto.
  * induction vl; simpl; auto.
    repeat break_match_goal; auto.
Qed.

Lemma create_result_is_not_box :
  forall ident vl,
  is_result (create_result ident vl) \/
  (exists e, (create_result ident vl) = RExp e).
Proof.
  destruct ident; intro; simpl; auto.
  1-2: left; apply eval_is_result.
  destruct v; auto.
  break_match_goal; auto.
  right. eexists. reflexivity.
Qed.

Lemma Private_params_exp_eval :
  forall exps ident vl Fs (e : Exp) n,
  | FParams ident vl exps :: Fs, e | n ↓ ->
  (forall m : nat,
  m < S n ->
  forall (Fs : FrameStack) (e : Exp),
  | Fs, e | m ↓ ->
  exists (res : Redex) (k : nat),
    is_result res /\ ⟨ [], e ⟩ -[ k ]-> ⟨ [], res ⟩ /\ k <= m) ->
  exists res k, is_result res /\
  ⟨ FParams ident vl exps :: Fs, e⟩ -[k]->
  ⟨ Fs, res ⟩ /\ k <= n.
Proof.
  induction exps; intros.
  * apply H0 in H as H'. 2: lia.
    destruct H' as [res [k [Hres [Hd Hlt]]]].
    eapply frame_indep_nil in Hd.
    eapply term_step_term in H. 2: exact Hd. simpl in *.
    inv Hres.
    - do 2 eexists. split. 2: split.
      2: {
        eapply transitive_eval. exact Hd.
        eapply step_trans. constructor. congruence. apply step_refl.
      }
      auto.
      inv H. lia.
    - destruct vs. 2: destruct vs. 1, 3: inv H. (* vs is a singleton *)
      inv H. destruct (create_result_is_not_box ident (vl ++ [v])).
      + do 2 eexists. split. 2: split.
        2: {
          eapply transitive_eval. exact Hd.
          eapply step_trans. constructor. reflexivity. apply step_refl.
        }
        auto.
        lia.
      (* if create_result was a function application: *)
      + inv H. rewrite H1 in *. apply H0 in H7 as H7'.
        destruct H7' as [res2 [k2 [Hres2 [Hd2 Hlt2]]]]. 2: lia.
        eapply frame_indep_nil in Hd2.
        eapply term_step_term in H7. 2: exact Hd2.
        do 2 eexists. split. 2: split.
        2: {
          eapply transitive_eval. exact Hd.
          eapply step_trans. constructor. reflexivity. rewrite H1.
          exact Hd2.
        }
        auto.
        lia.
  * (* same as above *)
    apply H0 in H as H'. 2: lia.
    destruct H' as [res [k [Hres [Hd Hlt]]]].
    eapply frame_indep_nil in Hd.
    eapply term_step_term in H. 2: exact Hd. simpl in *.
    inv Hres.
    - do 2 eexists. split. 2: split.
      2: {
        eapply transitive_eval. exact Hd.
        eapply step_trans. constructor. congruence. apply step_refl.
      }
      auto.
      inv H. lia.
    (* up to this point*)
    - destruct vs. 2: destruct vs. 1, 3: inv H.
      inv H. apply IHexps in H2 as [res2 [k2 [Hres2 [Hd2 Hlt2]]]].
      2: {
        intros. eapply H0. lia. eassumption.
      }
      do 2 eexists. split. 2: split.
      2: {
        eapply transitive_eval. exact Hd.
        eapply step_trans. constructor. exact Hd2.
      }
      auto.
      lia.
Qed.

Lemma Private_params_exp_eval_empty :
  forall exps ident vl Fs (e : Exp) n,
  | FParams ident vl exps :: Fs, e | n ↓ ->
  (forall m : nat,
  m < S n ->
  forall (Fs : FrameStack) (e : Exp),
  | Fs, e | m ↓ ->
  exists (res : Redex) (k : nat),
    is_result res /\ ⟨ [], e ⟩ -[ k ]-> ⟨ [], res ⟩ /\ k <= m) ->
  exists res k, is_result res /\
  ⟨ [FParams ident vl exps], e⟩ -[k]->
  ⟨ [], res ⟩ /\ k <= n.
Proof.
  induction exps; intros.
  * apply H0 in H as H'. 2: lia.
    destruct H' as [res [k [Hres [Hd Hlt]]]].
    eapply frame_indep_nil in Hd as Hlia.
    eapply frame_indep_nil in Hd.
    eapply term_step_term in H as Hlia2. 2: exact Hlia. simpl in *.
    inv Hres.
    - do 2 eexists. split. 2: split.
      2: {
        eapply transitive_eval. exact Hd.
        eapply step_trans. constructor. congruence. apply step_refl.
      }
      auto.
      inv Hlia2. lia.
    - destruct vs. 2: destruct vs. 1, 3: inv Hlia2. (* vs is a singleton *)
      inv Hlia2. destruct (create_result_is_not_box ident (vl ++ [v])).
      + do 2 eexists. split. 2: split.
        2: {
          eapply transitive_eval. exact Hd.
          eapply step_trans. constructor. reflexivity. apply step_refl.
        }
        auto.
        lia.
      (* if create_result was a function application: *)
      + inv H1. rewrite H2 in *. apply H0 in H7 as H7'. 2: lia.
        destruct H7' as [res2 [k2 [Hres2 [Hd2 Hlt2]]]].
        eapply frame_indep_nil in Hd2 as Hlia3.
        eapply frame_indep_nil in Hd2.
        eapply term_step_term in H7. 2: exact Hlia3.
        do 2 eexists. split. 2: split.
        2: {
          eapply transitive_eval. exact Hd.
          eapply step_trans. constructor. reflexivity. rewrite H2.
          exact Hd2.
        }
        auto.
        lia.
  * (* same as above *)
    apply H0 in H as H'. 2: lia.
    destruct H' as [res [k [Hres [Hd Hlt]]]].
    eapply frame_indep_nil in Hd as Hlia.
    eapply frame_indep_nil in Hd.
    eapply term_step_term in H as Hlia2. 2: exact Hlia. simpl in *.
    inv Hres.
    - do 2 eexists. split. 2: split.
      2: {
        eapply transitive_eval. exact Hd.
        eapply step_trans. constructor. congruence. apply step_refl.
      }
      auto.
      inv Hlia2. lia.
    (* up to this point*)
    - destruct vs. 2: destruct vs. 1, 3: inv Hlia2.
      inv Hlia2. apply IHexps in H2 as [res2 [k2 [Hres2 [Hd2 Hlt2]]]].
      2: {
        intros. eapply H0. lia. eassumption.
      }
      do 2 eexists. split. 2: split.
      2: {
        eapply transitive_eval. exact Hd.
        eapply step_trans. constructor. exact Hd2.
      }
      auto.
      lia.
Qed.

Lemma term_empty : forall x Fs (e : Exp),
  | Fs, e | x ↓ ->
  exists k, | [], e | k ↓ /\ k <= x.
Proof.
  induction x using Wf_nat.lt_wf_ind; intros; inv H0.
  * eexists. split. do 2 constructor. auto. lia.
  * destruct el. (* tricks to avoid RBox *)
    - eexists. split. constructor. eapply cool_params_0.
      congruence. reflexivity. do 2 constructor. inv H3. lia.
    - inv H3.
      eapply Private_params_exp_eval_empty in H8 as HH2.
      2: {
        intros. specialize (H m ltac:(slia) Fs0 e0 H1) as [j [HD Hj]].
        apply terminates_in_k_eq_terminates_in_k_sem in HD as [res [Hres Hr]].
        do 2 eexists. split. 2: split. all: eassumption.
      }
      destruct HH2 as [res [k [Hres [Hd Hlt]]]].
      eexists. split. do 2 constructor. congruence.
      eapply terminates_in_k_eq_terminates_in_k_sem. eexists.
      split. 2: exact Hd. auto. nia.
  * destruct el. (* proof is same as above, tricks to avoid RBox *)
    - eexists. split. constructor. eapply cool_params_0.
      congruence. reflexivity. do 2 constructor. inv H3. lia.
    - inv H3.
      eapply Private_params_exp_eval_empty in H8 as HH2.
      2: {
        intros. specialize (H m ltac:(slia) Fs0 e0 H1) as [j [HD Hj]].
        apply terminates_in_k_eq_terminates_in_k_sem in HD as [res [Hres Hr]].
        do 2 eexists. split. 2: split. all: eassumption.
      }
      destruct HH2 as [res [k [Hres [Hd Hlt]]]].
      eexists. split. do 2 constructor. congruence.
      eapply terminates_in_k_eq_terminates_in_k_sem. eexists.
      split. 2: exact Hd. auto. nia.
  * eexists. split. do 2 constructor. auto. nia.
  * eapply Private_params_exp_eval_empty in H3 as HH2.
    2: {
      intros. specialize (H m ltac:(slia) Fs0 e H1) as [j [HD Hj]].
      apply terminates_in_k_eq_terminates_in_k_sem in HD as [res [Hres Hr]].
      do 2 eexists. split. 2: split. all: eassumption.
    }
    destruct HH2 as [res [k0 [Hres [Hd Hlt]]]].
    eexists. split. constructor.
    eapply terminates_in_k_eq_terminates_in_k_sem. eexists.
    split. 2: exact Hd. auto. nia.
  * destruct el. (* tricks to avoid RBox *)
    - eexists. split. constructor. eapply cool_params_0.
      congruence. reflexivity.
      (* here is this different from the previous *)
      simpl. constructor. apply eval_is_result.
      (***)
      inv H3. lia.
    - inv H3.
      eapply Private_params_exp_eval_empty in H8 as HH2.
      2: {
        intros. specialize (H m ltac:(slia) Fs0 e0 H1) as [j [HD Hj]].
        apply terminates_in_k_eq_terminates_in_k_sem in HD as [res [Hres Hr]].
        do 2 eexists. split. 2: split. all: eassumption.
      }
      destruct HH2 as [res [k [Hres [Hd Hlt]]]].
      eexists. split. do 2 constructor. congruence.
      eapply terminates_in_k_eq_terminates_in_k_sem. eexists.
      split. 2: exact Hd. auto. nia.
  * destruct el. (* tricks to avoid RBox *)
  - eexists. split. constructor. eapply cool_params_0.
    congruence. reflexivity.
    (* here is this different from the previous *)
    simpl. constructor. apply eval_is_result.
    (***)
    inv H3. lia.
  - inv H3.
    eapply Private_params_exp_eval_empty in H8 as HH2.
    2: {
      intros. specialize (H m ltac:(slia) Fs0 e0 H1) as [j [HD Hj]].
      apply terminates_in_k_eq_terminates_in_k_sem in HD as [res [Hres Hr]].
      do 2 eexists. split. 2: split. all: eassumption.
    }
    destruct HH2 as [res [k [Hres [Hd Hlt]]]].
    eexists. split. do 2 constructor. congruence.
    eapply terminates_in_k_eq_terminates_in_k_sem. eexists.
    split. 2: exact Hd. auto. nia.
  (* application is harder, because first, the function parameter needs
     to be evaluated, then we do a case separation, whether l = [].
     Everytime an exception occurs, that needs to be propagated -> hence
     the number of case separations. *)
  * apply H in H3 as H3'. destruct H3' as [j [Hj Hlt1]]. 2: nia.
    apply terminates_in_k_eq_terminates_in_k_sem in Hj as [res [Hres Hr]].
    eapply frame_indep_nil in Hr as Hlia1.
    eapply frame_indep_nil in Hr. eapply term_step_term in H3.
    2: exact Hlia1. simpl in *.
    destruct l. (* tricks to avoid RBox *)
    - inv Hres. (* exception result? *)
      + exists (2 + j). split. constructor.
        eapply step_term_term. exact Hr. 2: nia.
        replace (S j - j) with 1 by nia.
        constructor. congruence. constructor. auto.
        inv H3. nia.
      + inv H3. inv H1. destruct (create_result_is_not_box (IApp v) []).
        ** exists (3 + j). split. constructor.
           eapply step_term_term. exact Hr. 2: nia.
           replace (S (S j) - j) with 2 by nia.
           constructor. econstructor. congruence. reflexivity.
           now constructor.
           lia.
        ** inv H0. rewrite H1 in *. apply H in H8 as H8'. 2: nia.
           destruct H8' as [i [Hd2 Hlt2]].
           exists (1 + (j + 2 + i)). split. constructor.
           eapply step_term_term. exact Hr. 2: nia.
           replace (j + 2 + i - j) with (2 + i) by nia.
           constructor. econstructor. congruence. reflexivity.
           now rewrite H1. nia.
    - inv Hres.
      + exists (2 + j). split. constructor.
        eapply step_term_term. exact Hr. 2: nia.
        replace (S j - j) with 1 by nia.
        constructor. congruence. constructor. auto.
        inv H3. nia.
      + inv H3. inv H1.
        eapply Private_params_exp_eval_empty in H9 as HH2.
        2: {
          intros. specialize (H m ltac:(slia) Fs0 e1 H1) as [i [Hd2 Hi]].
          apply terminates_in_k_eq_terminates_in_k_sem in Hd2
             as [res2 [Hres2 Hr2]].
          do 2 eexists. split. 2: split. all: eassumption.
        }
        destruct HH2 as [res2 [i [Hres2 [Hd2 Hlt2]]]].
        assert (⟨ [FApp1 (e :: l)], RValSeq [v]⟩ -[2]-> ⟨ [FParams (IApp v) [] l], e ⟩). {
          repeat econstructor. congruence.
        }
        eapply (transitive_eval Hr) in H0.
        eapply (transitive_eval H0) in Hd2.
        eexists. split.
        constructor. apply terminates_in_k_eq_terminates_in_k_sem.
        eexists. split. 2: exact Hd2. assumption. nia.
  * apply H in H3 as HH. 2: nia.
    destruct HH as [i [Hi Hlt]].
    apply terminates_in_k_eq_terminates_in_k_sem in Hi as [res [Hres Hr]].
    eapply frame_indep_nil in Hr as Hlia1.
    eapply frame_indep_nil in Hr.
    eapply term_step_term in H3. 2: exact Hlia1.
    inv Hres. (* tail exception or not *)
    - exists (S i + 1).
      split. 2: inv H3; nia.
      simpl. constructor. apply terminates_in_k_eq_terminates_in_k_sem.
      exists ex. split; auto. eapply transitive_eval.
      exact Hr. do 2 econstructor. congruence.
    - inv H3. apply H in H1 as HH. 2: nia.
      destruct HH as [j [Hj Hltj]].
      simpl in *. apply terminates_in_k_eq_terminates_in_k_sem in Hj as [hdres [Hr2 Hd2]].
      eapply frame_indep_nil in Hd2 as Hlia2.
      eapply frame_indep_nil in Hd2.
      eapply term_step_term in H1. 2: exact Hlia2.
      assert (⟨ [FCons1 hd], RValSeq [tl0] ⟩ -[1]-> ⟨[FCons2 tl0], hd⟩). {
        repeat econstructor.
      }
      eapply (transitive_eval Hr) in H0.
      eapply (transitive_eval H0) in Hd2.
      inv Hr2. (* head exception or not *)
      + exists (1 + (i + (1 + (j + 1) ))). split.
        simpl. constructor. eapply step_term_term.
        exact Hd2.
        replace (i + S (j + 1) - (i + 1 + j)) with 1 by nia.
        constructor. congruence. now constructor.
        nia.
        inv H1. nia.
      + exists (1 + (i + (1 + (j + 1) ))). split.
        simpl. constructor. eapply step_term_term.
        exact Hd2. inv H1.
        replace (i + S (j + 1) - (i + 1 + j)) with 1 by nia.
        constructor. now constructor.
        nia.
        inv H1. nia.
  * apply H in H3 as HH. 2: nia.
    destruct HH as [i [Hi Hlt]].
    apply terminates_in_k_eq_terminates_in_k_sem in Hi as [res [Hres Hr]].
    eapply frame_indep_nil in Hr as Hlia1.
    eapply frame_indep_nil in Hr.
    eapply term_step_term in H3. 2: exact Hlia1.
    inv Hres. (* tail exception or not *)
    - exists (S i + 1).
      split. 2: inv H3; nia.
      simpl. constructor. apply terminates_in_k_eq_terminates_in_k_sem.
      exists ex. split; auto. eapply transitive_eval.
      exact Hr. do 2 econstructor. congruence.
    - inv H3. apply H in H7 as HH. 2: nia.
      destruct HH as [j [Hj Hltj]].
      simpl in *. apply terminates_in_k_eq_terminates_in_k_sem in Hj as [hdres [Hr2 Hd2]].
      eapply frame_indep_nil in Hd2 as Hlia2.
      eapply term_step_term in H7. 2: exact Hlia2.
      assert (⟨ [FLet (Datatypes.length vs) e2], vs ⟩ -[1]-> 
      ⟨ [], e2.[list_subst vs idsubst] ⟩). {
        repeat econstructor.
      }
      eapply (transitive_eval Hr) in H0.
      eapply (transitive_eval H0) in Hd2.
      exists (1 + (i + (1 + j))). split. 2: inv Hr2; inv H7; nia.
      constructor. eapply step_term_term. exact Hd2.
      replace (i + (1 + j) - (i + 1 + j)) with 0 by nia.
      now constructor.
      nia.
  (* Sequencing is basically same as let *)
  * apply H in H3 as HH. 2: nia.
    destruct HH as [i [Hi Hlt]].
    apply terminates_in_k_eq_terminates_in_k_sem in Hi as [res [Hres Hr]].
    eapply frame_indep_nil in Hr as Hlia1.
    eapply frame_indep_nil in Hr.
    eapply term_step_term in H3. 2: exact Hlia1.
    inv Hres. (* tail exception or not *)
    - exists (S i + 1).
      split. 2: inv H3; nia.
      simpl. constructor. apply terminates_in_k_eq_terminates_in_k_sem.
      exists ex. split; auto. eapply transitive_eval.
      exact Hr. do 2 econstructor. congruence.
    - inv H3. apply H in H1 as HH. 2: nia.
      destruct HH as [j [Hj Hltj]].
      simpl in *. apply terminates_in_k_eq_terminates_in_k_sem in Hj as [hdres [Hr2 Hd2]].
      eapply frame_indep_nil in Hd2 as Hlia2.
      eapply term_step_term in H1. 2: exact Hlia2.
      assert (⟨ [FSeq e2], RValSeq [v] ⟩ -[1]-> 
      ⟨ [], e2 ⟩). {
        repeat econstructor.
      }
      eapply (transitive_eval Hr) in H0.
      eapply (transitive_eval H0) in Hd2.
      exists (1 + (i + (1 + j))). split. 2: inv Hr2; inv H1; nia.
      constructor. eapply step_term_term. exact Hd2.
      replace (i + (1 + j) - (i + 1 + j)) with 0 by nia.
      now constructor.
      nia.
  * eexists. split. constructor. now constructor. nia.
  * apply H in H3 as HH. 2: nia. destruct HH as [k1 [Hd1 Hlt1]].
    apply terminates_in_k_eq_terminates_in_k_sem in Hd1 as [r1 [Hr Hd]].
    eapply frame_indep_nil in Hd as Hlia1.
    eapply frame_indep_nil in Hd.
    eapply term_step_term in H3. 2: exact Hlia1.
    simpl in *.
    inv Hr. (* exception? *)
    - exists (1 + k1 + 1). split. 2: inv H3; nia.
      simpl. constructor. eapply step_term_term. exact Hd.
      replace (k1 + 1 - k1) with 1 by nia.
      constructor. congruence. now constructor. nia.
    - (* list_length_ind on H3 (or structural could also be enough) *)
      admit.
  * apply H in H4 as [i [Hd Hlt]].
    eexists. split. econstructor. reflexivity. exact Hd. nia. nia.
  * apply H in H3 as HH. 2: nia.
    destruct HH as [i [Hd Hlt]].
    apply terminates_in_k_eq_terminates_in_k_sem in Hd as [r [Hres Hd]].
    eapply frame_indep_nil in Hd as Hlia.
    eapply frame_indep_nil in Hd.
    eapply term_step_term in H3. 2: exact Hlia.
    simpl in *.
    inv Hres. (* exception or not *)
    - inv H3. 2: congruence.
      apply H in H1 as [j [Hd2 Hlt2]]. 2: nia.
      exists (1 + (i + (1 + j))). split. 2: nia.
      constructor. eapply step_term_term. exact Hd. 2: nia.
      replace (i + (1 + j) - i) with (S j) by nia.
      now constructor.
    - inv H3.
      apply H in H9 as [j [Hd2 Hlt2]]. 2: nia.
      exists (1 + (i + (1 + j))). split. 2: nia.
      constructor. eapply step_term_term. exact Hd. 2: nia.
      replace (i + (1 + j) - i) with (S j) by nia.
      now constructor.
  * eexists. split. now constructor. nia.
Admitted.

(* NOTE: This is not a duplicate! Do not remove! *)
(* sufficient to prove it for Exp, since value sequences and
   exceptions terminate in 0/1 step by definition in the
   empty stack (and RBox does not terminate!). *)
Corollary term_eval_empty : forall x Fs (e : Exp),
  | Fs, e | x ↓ ->
  exists res k, is_result res /\ ⟨ [], e ⟩ -[k]-> ⟨ [], res ⟩ /\ k <= x.
Proof.
  intros. apply term_empty in H. destruct H as [k [H Hlt]].
  apply terminates_in_k_eq_terminates_in_k_sem in H as [r [Hr H]].
  do 2 eexists; eauto.
Qed.

Corollary term_eval : forall x Fs (e : Exp), | Fs, e | x ↓ ->
  exists v k, is_result v /\ ⟨ Fs, e ⟩ -[k]-> ⟨ Fs, v ⟩ /\ k <= x.
Proof.
  intros.
  apply term_eval_empty in H as [r [k [Hr [Hd Hlt]]]].
  exists r, k. intuition.
  eapply frame_indep_nil in Hd. exact Hd.
Qed.

Corollary term_eval_both : forall x Fs (e : Exp), | Fs, e | x ↓ ->
  exists v k, is_result v /\
  ⟨ [], e ⟩ -[k]-> ⟨ [], v ⟩ /\
  ⟨ Fs, e ⟩ -[k]-> ⟨ Fs, v ⟩ /\ k <= x.
Proof.
  intros. apply term_eval_empty in H as [r [k [Hr [Hd Hlt]]]].
  exists r, k. intuition.
  eapply frame_indep_nil in Hd. exact Hd.
Qed.

Theorem put_back : forall F e Fs (P : EXPCLOSED e) (P2 : FCLOSED F),
  | F :: Fs, e | ↓ -> | Fs, plug_f F e | ↓.
Proof.
  destruct F; intros; simpl.
  all: try now (inv H; exists (S x); constructor; auto).
  * inv H. exists (3 + x). now do 3 constructor.
  * inv H. destruct ident; simpl.
  (* These build on the same idea, however, application and maps are a bit different: *)
  1-2, 4-5: destruct vl; simpl; [
    eexists; do 2 constructor; [congruence | eassumption]
    |
    exists (4 + ((2 * length vl) + x)); do 2 constructor;
    try congruence; constructor;
    eapply step_term_term;
    [
      apply params_eval
      |
      simpl app;
      now replace (S (2 * Datatypes.length vl + x) - (1 + 2 * Datatypes.length vl)) with x by lia
      |
      lia
    ]
  ].
    - destruct_scopes. specialize (H6 eq_refl).
      inv H6. destruct vl.
      + simpl. destruct el.
        ** simpl in H. congruence.
        ** eexists. constructor.
           erewrite deflatten_flatten. eassumption.
           simpl in H. instantiate (1 := x0). lia.
      + simpl. destruct vl; simpl.
        ** eexists. do 3 constructor. simpl.
           erewrite deflatten_flatten. eassumption.
           simpl in H. instantiate (1 := x0). lia.
        ** exists (5 + ((2 * length vl) + x)). do 4 constructor.
           erewrite deflatten_flatten.
           2: { rewrite app_length, map_length. simpl in *.
                instantiate (1 := x0). lia. }
           eapply step_term_term.
           apply params_eval. simpl app. 2: lia.
           now replace (S (2 * Datatypes.length vl + x) - (1 + 2 * Datatypes.length vl)) with x by lia.
    - destruct vl; simpl.
      + eexists. do 4 constructor. congruence. eassumption.
      + exists (6 + ((2 * length vl) + x)). do 4 constructor. congruence.
        constructor.
        eapply step_term_term.
        apply params_eval. simpl app. 2: lia.
        now replace (S (2 * Datatypes.length vl + x) - (1 + 2 * Datatypes.length vl)) with x by lia.
  * inv H. destruct lv. (* RBox is not handled by params_eval_create! *)
    - eexists.
      do 2 constructor. cbn. eapply cool_params_0.
      congruence.
      reflexivity.
      destruct_scopes. inv H6.
      econstructor. exact H.
      rewrite eclosed_ignores_sub; auto. exact H0.
    - exists (6 + ((2 * length lv) + x)). do 2 constructor.
      simpl. constructor. congruence. constructor.
      eapply step_term_term.
      apply params_eval_create. 2: lia.
      replace (S (S (Datatypes.length lv + (Datatypes.length lv + 0) + x)) -
      (1 + 2 * Datatypes.length lv)) with (S x) by lia.
      simpl. destruct_scopes. inv H6.
      econstructor. eassumption. rewrite eclosed_ignores_sub; auto.
Qed.

Ltac inv_term :=
  match goal with
  | [H : | _, _ | _ ↓ |- _] => inv H
  end.

Theorem put_back_rev : forall F e Fs (P : EXPCLOSED e), FCLOSED F ->
  | Fs, plug_f F e | ↓ -> | F :: Fs, e | ↓.
Proof.
  destruct F; intros; simpl.
  all: try now (inv H0; cbn in *; inv_term; [eexists;eassumption | inv H0]).
  * inv H0. cbn in *. inv H1. inv H5. inv H2. eexists. eassumption. inv H0.
  * cbn. inv H0. destruct ident; simpl in H1.
    1-2, 4-5:
      inv_term; [
        destruct vl; inv_term;
         [eexists; eassumption
         |inv H8; eapply term_step_term in H2;[|apply params_eval]];
         eexists; eassumption
        |inv H0
      ].
    (* again, map and apply need special care: *)
    - destruct_scopes. specialize (H7 eq_refl). inv H7. destruct vl.
      + destruct el.
        ** simpl in H. congruence.
        ** inv H1. 2: inv H0. erewrite deflatten_flatten in H9.
           2: { instantiate (1 := x0). simpl in H. lia. }
           eexists. eassumption.
      + destruct vl; simpl in *.
        ** inv H1. 2: inv H0. erewrite deflatten_flatten in H9.
           2: { instantiate (1 := x0). simpl in H. lia. }
           do 2 inv_term. eexists. eassumption.
        ** inv_term. 2: inv H0. erewrite deflatten_flatten in H9.
           2: { instantiate (1 := x0). simpl in H.
             rewrite app_length, map_length. slia. }
           do 3 inv_term.
           eapply term_step_term in H2;[|apply params_eval].
           eexists; eassumption.
    - inv_term. 2: inv H0. inv_term. destruct vl; inv_term.
      + inv_term. eexists. eassumption.
      + do 2 inv_term. eapply term_step_term in H2;[|apply params_eval].
        eexists. eassumption.
  * inv H0. cbn in *. inv H1. 2: inv H0.
    inv H5. destruct lv.
    - inv H2. destruct_scopes. inv H8.
      inv H7. 2: congruence. rewrite eclosed_ignores_sub in H14; auto.
      eexists. eassumption.
    - destruct_scopes. inv H7. inv H2. inv H12.
      eapply term_step_term in H2.
      2: apply params_eval_create.
      simpl in H2. inv H2. 2: congruence.
      rewrite eclosed_ignores_sub in H14; auto.
      eexists. eassumption.
Qed.
