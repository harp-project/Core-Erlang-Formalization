(**
  This file contains numerous semantic properties about the frame stack semantics
  (labelled version) of Core Erlang.
 *)
From CoreErlang.FrameStack Require Export SubstSemanticsLabeled.
From stdpp Require Export list option.
Import ListNotations.

Corollary side_effect_ac_value : forall fs r fs' r' l0,
  ⟨ fs, r ⟩ -⌊ Some ((AtomCreation, l0):SideEffect) ⌋-> ⟨ fs', r' ⟩ ->
  exists av, l0 = [VLit (Atom av)].
Proof.
  intros. inversion H;
  unfold SubstSemanticsLabeled.create_result in *; simpl in *; subst.
  - destruct ident; try discriminate.
    + destruct m; try discriminate.
      destruct l; try discriminate.
      destruct f; try discriminate.
      destruct l; try discriminate.
      unfold eval in H1.
      destruct (convert_string_to_code (s, s0)); try discriminate.
      1-2: inversion H1; unfold eval_io in H3;
           destruct (convert_string_to_code (s, s0)); try discriminate;
           repeat (destruct vl; simpl in H3; try discriminate).
      2-4: destruct (eval_error s s0 vl); try discriminate.
      {
        inversion H1. unfold eval_list_atom in H3.
        destruct (convert_string_to_code (s, s0)); try discriminate.
        repeat (destruct vl; simpl in H3; try discriminate).
        destruct (mk_ascii_list v); try discriminate.
        inversion H3. exists (string_of_list_ascii l).
        reflexivity.
      }
      all: destruct (eval_concurrent s s0 vl); try discriminate.
    + unfold primop_eval in H1.
      destruct (convert_primop_to_code f); try discriminate.
      all: destruct (eval_primop_error f vl); try discriminate.
    + destruct v; try discriminate.
      destruct (params =? (length vl))%nat; try discriminate.
  - destruct ident; try discriminate.
    + destruct m; try discriminate.
      destruct l; try discriminate.
      destruct f; try discriminate.
      destruct l; try discriminate.
      unfold eval in H0.
      destruct (convert_string_to_code (s, s0)); try discriminate.
      1-2: inversion H0; unfold eval_io in H2;
           destruct (convert_string_to_code (s, s0)); try discriminate;
           repeat (destruct vl; simpl in H2; try discriminate).
      {
        inversion H0. unfold eval_list_atom in H2.
        destruct (convert_string_to_code (s, s0)); try discriminate.
        repeat (destruct vl; simpl in H2; try discriminate).
        destruct (mk_ascii_list v); try discriminate.
        inversion H2. exists (string_of_list_ascii l).
        reflexivity.
      }
      1-3: destruct (eval_error s s0 (vl ++ [v])); try discriminate.
      all: destruct (eval_concurrent s s0 (vl ++ [v])); try discriminate.
    + unfold primop_eval in H0.
      destruct (convert_primop_to_code f); try discriminate.
      all: destruct (eval_primop_error f (vl ++ [v])); try discriminate.
    + destruct v0; try discriminate.
      destruct (params =? (length (vl ++ [v])))%nat; try discriminate.
Qed.

Theorem transitive_eval :
  forall {n e e' l fs fs'}, ⟨ fs, e ⟩ -[ n, l ]-> ⟨ fs', e' ⟩ ->
  forall {n' e'' l' fs''},  ⟨ fs', e' ⟩ -[ n', l' ]-> ⟨ fs'', e'' ⟩
->
  ⟨ fs, e ⟩ -[ n + n', l ++ l' ]-> ⟨ fs'', e'' ⟩.
Proof.
  intros n Fs Fs' l e e' IH.
  induction IH; intros; auto using app_nil_l.
  simpl. econstructor. exact H. apply IHIH. exact H1.
  destruct s; rewrite H0; auto.
Qed.

Theorem transitive_any_eval :
  forall {e e' l fs fs'}, ⟨ fs, e ⟩ -[ l ]->* ⟨ fs', e' ⟩ ->
  forall {e'' l' fs''},  ⟨ fs', e' ⟩ -[ l' ]->* ⟨ fs'', e'' ⟩
->
  ⟨ fs, e ⟩ -[ l ++ l' ]->* ⟨ fs'', e'' ⟩.
Proof.
  intros. destruct H, H0. pose proof (transitive_eval H H0).
  unfold step_any_non_terminal. eexists. exact H1.
Qed.

Theorem step_determenism {e e' l fs fs'} :
  ⟨ fs, e ⟩ -⌊ l ⌋-> ⟨ fs', e' ⟩ ->
  (forall l' fs'' e'', ⟨ fs, e ⟩ -⌊ l' ⌋-> ⟨ fs'', e'' ⟩
  -> l = l' /\ fs'' = fs' /\ e'' = e').
Proof.
  intro H. inv H; intros; inv H; auto.
  - rewrite <- H1 in H9. now inv H9.
  - rewrite <- H0 in H8. now inv H8.
Qed.

Theorem value_nostep v :
  is_result v ->
  forall fs' v' l, ⟨[], v⟩ -⌊l⌋-> ⟨fs' , v'⟩ -> False.
Proof.
  intros H fs' v' l' HD. inversion H; subst; inversion HD.
Qed.

Theorem step_rt_determinism {e v fs fs' l} :
  ⟨fs, e⟩ -⌊l⌋-> ⟨fs', v⟩
->
  (forall fs'' v', ⟨fs, e⟩ -⌊l⌋-> ⟨fs'', v'⟩ -> fs' = fs'' /\ v' = v).
Proof.
  intro. induction H; intros; try inv H; try inv H0; subst; auto.
  * inv H1. rewrite <- H3 in H9. now inv H9.
  * rewrite <- H2 in H8. now inv H8.
Qed.

Theorem create_result_closed :
  forall vl ident r eff,
    Forall (fun v => VALCLOSED v) vl ->
    ICLOSED ident ->
    Some (r, eff) = (create_result ident vl) ->
    REDCLOSED r.
Proof.
  intros vl ident r eff Hall Hi Heq.
  destruct ident; simpl in *; try invSome.
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
  * destruct m, f; try destruct l; try destruct l0; try invSome.
    all: inv Hi; try econstructor; auto; scope_solver.
    eapply closed_eval; try eassumption. eauto.
  * destruct (primop_eval f vl) eqn: p.
    - inv Heq.
      eapply (closed_primop_eval f vl r eff Hall).
      assumption.
    - inv Heq.
  * inversion Hi; subst; clear Hi. destruct v; unfold badfun; try invSome.
    1-8: constructor; auto; constructor.
    break_match_hyp; invSome.
    - constructor. destruct_scopes.
      apply -> subst_preserves_scope_exp. exact H6.
      apply Nat.eqb_eq in Heqb. rewrite Heqb.
      replace (Datatypes.length ext + Datatypes.length vl + 0) with
              (length (convert_to_closlist ext ++ vl)).
      2: { unfold convert_to_closlist.
           rewrite length_app, length_map. lia.
      }
      apply scoped_list_idsubst. apply Forall_app; split; auto.
      now apply closlist_scope.
    - unfold badarity. constructor. constructor. auto.
Qed.

Theorem step_closedness : forall F e F' e' l,
   ⟨ F, e ⟩ -⌊l⌋-> ⟨ F', e' ⟩ -> FSCLOSED F -> REDCLOSED e 
->
  FSCLOSED F' /\ REDCLOSED e' (* /\ list_fmap (fun s => Forall (ValScoped 0) (snd s)) l *).
Proof.
  intros F e F' e' l IH. induction IH; intros Hcl1 Hcl2;
  destruct_scopes; destruct_foralls; split; auto.
  all: cbn; try (repeat constructor; now auto).
  all: try now (apply indexed_to_forall in H1; do 2 (constructor; auto)).
  * do 2 (constructor; auto).
    apply Forall_app; auto.
    intro. apply H7 in H. inv H. exists x. rewrite length_app. simpl.
    simpl in H0. lia.
  * eapply create_result_closed; eauto.
  * eapply create_result_closed. 3: eassumption. apply Forall_app; auto. auto.
  * do 2 (constructor; auto).
    epose proof (Forall_pair _ _ _ _ _ H0 H3).
    destruct_foralls. inv H4. constructor; auto.
    now apply flatten_keeps_prop.
    intros. simpl. rewrite length_flatten_list.
    exists (length el). lia.
  * constructor. apply (H0 0). slia.
  * do 2 (constructor; auto).
    now apply indexed_to_forall in H4.
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
    now apply clause_scope.
  * do 2 (constructor; auto).
    apply -> subst_preserves_scope_exp. apply H5.
    eapply match_pattern_list_scope in H as Hmatch. 2: eassumption.
    apply match_pattern_list_length in H. rewrite H.
    now apply scoped_list_idsubst.
  * constructor. apply -> subst_preserves_scope_exp. apply H5.
    erewrite match_pattern_list_length. 2: exact H.
    apply scoped_list_idsubst.
    eapply match_pattern_list_scope; eassumption.
  * constructor. apply -> subst_preserves_scope_exp.
    eassumption.
    rewrite Nat.add_0_r.
    replace (length l) with
            (length (convert_to_closlist (map (fun '(x, y) => (0, x, y)) l))).
    2: {
      unfold convert_to_closlist. now do 2 rewrite length_map.
    }
    apply scoped_list_idsubst.
    apply closlist_scope. rewrite length_map. intros.
    specialize (H3 i H). rewrite Nat.add_0_r in *.
    do 2 rewrite map_map.
    remember (fun x : nat * Exp => (snd ∘ fst) (let '(x0, y) := x in (0, x0, y)))
    as F.
    remember (fun x : nat * Exp => snd (let '(x0, y) := x in (0, x0, y)))
    as G.
    replace 0 with (F (0, ˝VNil)) by (subst;auto).
    replace (˝VNil) with (G (0, ˝VNil)) by (subst;auto).
    do 2 rewrite map_nth.
    replace 0 with (fst (0, ˝VNil)) in H3 by (subst;auto).
    replace (˝VNil) with (snd (0, ˝VNil)) in H3 by (subst;auto).
    do 2 rewrite map_nth in H3.
    subst; cbn in *. destruct (nth i l (0, ˝ VNil)). auto.
  * constructor. apply -> subst_preserves_scope_exp.
    eassumption.
    now apply scoped_list_idsubst.
  * constructor. apply -> subst_preserves_scope_exp.
    eassumption.
    repeat apply cons_scope; auto. destruct class; constructor.
  * rewrite Nat.add_0_r in *. do 2 (constructor; auto).
Qed.

Corollary step_any_closedness : forall Fs Fs' e v k l,
   ⟨ Fs, e ⟩ -[k , l]-> ⟨Fs', v⟩ -> FSCLOSED Fs -> REDCLOSED e
->
  REDCLOSED v /\ FSCLOSED Fs'.
Proof.
  intros. induction H; auto. apply step_closedness in H. destruct H.
  apply (IHstep_rt ). all: auto.
Qed.

Theorem step_any_non_terminal_closedness : forall F e l F' e',
   ⟨ F, e ⟩ -[ l ]->* ⟨ F', e' ⟩ -> FSCLOSED F -> REDCLOSED e
-> REDCLOSED e' /\ FSCLOSED F'.
Proof.
  intros F e l F' e' H. induction H; intros. destruct H. auto.
  apply step_closedness in H. inv H.
  apply (step_any_closedness _ _ _ _ _ _ H2 H4 H5). all: assumption.
Qed.

Theorem transitive_eval_rev : forall Fs Fs' e e' k1 l1,
  ⟨ Fs, e ⟩ -[k1 , l1]-> ⟨ Fs', e' ⟩->
  forall Fs'' e'' k2 l2,
  ⟨ Fs, e ⟩ -[k1 + k2 , l1 ++ l2]-> ⟨ Fs'', e'' ⟩
->
  ⟨ Fs', e' ⟩ -[k2 , l2]-> ⟨ Fs'', e'' ⟩.
Proof.
  intros Fs Fs' e e' k1 l1 H. induction H.
  - intros Fs'' e'' k2 l2 H. simpl in H. apply H.
  - intros Fs'' e''' k2 l2 H2. rewrite Nat.add_succ_l in H2.
    destruct s; subst.
    + inv H2. destruct s0.
      * inv H7. eapply IHstep_rt.
        destruct (step_determenism H _ _  _ H3).
        destruct H2. subst. assumption.
      * inv H7.
        destruct (step_determenism H _ _  _ H3).
        inv H2.
    + inv H2. destruct s.
      * inv H7.
        destruct (step_determenism H _ _  _ H3).
        inv H1.
      * inv H7. eapply IHstep_rt.
        destruct (step_determenism H _ _  _ H3).
        destruct H2. subst. assumption.
Qed.

Theorem frame_indep_step : forall e F F' Fs e' l,
  ⟨ F :: Fs, e ⟩ -⌊l⌋-> ⟨ F' :: Fs, e' ⟩
->
  forall Fs', ⟨ F :: Fs', e ⟩ -⌊l⌋-> ⟨ F' :: Fs', e' ⟩.
Proof.
  intros. revert Fs'. inv H; intros.
  all: try constructor; auto; subst.
  all: try (apply cons_neq in H4; contradiction).
  all: try (symmetry in H1; apply cons_neq in H1; contradiction).
  all: try (symmetry in H4; apply cons_neq in H4; contradiction).
  all: try (symmetry in H5; apply cons_neq in H5; contradiction).
  all: try (apply cons_neq in H5; contradiction).
Qed.

Theorem frame_indep_red : forall e F Fs e' l,
  ⟨ F :: Fs, e ⟩ -⌊l⌋-> ⟨ Fs, e' ⟩
->
  forall Fs', ⟨ F :: Fs', e ⟩ -⌊l⌋-> ⟨ Fs', e' ⟩.
Proof.
  intros. revert Fs'. inv H; intros.
  all: try constructor; auto.
  all: try (apply cons_neq in H3; contradiction).
  all: try (apply cons_neq in H4; contradiction).
  all: put (@length Frame : FrameStack -> nat) on H3 as H3L; simpl in H3L; lia.
Qed.

Theorem frame_indep_core : forall k e Fs Fs' v l,
  ⟨ Fs, e ⟩ -[k , l]-> ⟨ Fs', v ⟩
->
  forall Fs'', ⟨ Fs ++ Fs'', e ⟩ -[k , l]-> ⟨ Fs' ++ Fs'', v ⟩.
Proof.
  induction k; intros.
  * inversion H. subst. constructor.
  * inv H; inv H1.
    all: try now (simpl; econstructor; try constructor; auto).
    20: { eapply IHk in H2; simpl in *. econstructor. apply eval_step_case_not_match. auto. eassumption. reflexivity. }
    all: try (eapply IHk in H2; simpl in *; econstructor).
    all: try constructor.
    all: try apply H2; auto.
Qed.

Theorem frame_indep_nil : forall k e Fs v l,
  ⟨ Fs, e ⟩ -[k , l]-> ⟨ [], v ⟩
->
  forall Fs', ⟨ Fs ++ Fs', e ⟩ -[k , l]-> ⟨ Fs', v ⟩.
Proof.
  intros. eapply frame_indep_core in H. exact H.
Qed.

Lemma params_eval :
  forall vals ident vl exps e Fs (v : Val),
  Forall (fun v => VALCLOSED v) vals ->
  ⟨ FParams ident vl ((map VVal vals) ++ e :: exps) :: Fs, RValSeq [v]⟩ -[1 + 2 * length vals , []]->
  ⟨ FParams ident (vl ++ v :: vals) exps :: Fs, e⟩.
Proof.
  induction vals; simpl; intros.
  * econstructor. econstructor. constructor. simpl. auto.
  * specialize (IHvals ident (vl ++ [v]) exps e Fs a).
    econstructor. constructor.
    econstructor. constructor.
    rewrite <- app_assoc in IHvals. now inv H.
    replace (length vals + S (length vals + 0)) with
            (1 + 2*length vals) by lia. rewrite <- app_assoc in IHvals. apply IHvals.
    now inv H.
    all: simpl; auto.
Qed.

(**
  Equivalence between labeled and unlabeled semantics
  *)

From CoreErlang.FrameStack Require Export SubstSemanticsLemmas.

Theorem step_unlabeled_to_labeled:
  forall Fs e Fs' v,
  ⟨ Fs, e ⟩ --> ⟨Fs', v⟩ ->
  exists l, ⟨ Fs, e ⟩ -⌊l⌋-> ⟨Fs', v⟩.
Proof.
  intros Fs e Fs' v H.
  inv H; eexists; constructor; try destruct ident; try apply H0; try assumption; try apply H1; reflexivity.
Qed.

Theorem step_labeled_to_unlabeled:
  forall Fs e Fs' v l,
  ⟨ Fs, e ⟩ -⌊l⌋-> ⟨Fs', v⟩ ->
  ⟨ Fs, e ⟩ --> ⟨Fs', v⟩.
Proof.
  intros Fs e Fs' v l H.
  inv H; econstructor; try destruct ident; try apply H1; try apply H0; try assumption; reflexivity.
Qed.

Theorem step_unlabeled_labeled_determinsm_one_step :
  forall Fs e Fs' v l Fs'' v',
  ⟨ Fs, e ⟩ --> ⟨Fs', v⟩ ->
  ⟨ Fs, e ⟩ -⌊l⌋-> ⟨Fs'', v'⟩ -> Fs' = Fs'' /\ v = v'.
Proof.
  intros Fs e Fs' v l Fs'' v' H H0.
  apply (step_determenism H0 l Fs' v).
  inv H; inv H0; constructor; try apply H1; try reflexivity.
  * unfold create_result in H2. destruct ident.
    1-3: inv H2; rewrite <- H9; destruct vl; destruct v'; try inv H9; reflexivity.
    all: rewrite <- H9; inv H9; rewrite <- H2 in H0; inv H0; try reflexivity.
  * unfold create_result in H1. induction ident.
    1-3: inv H1; rewrite <- H8; destruct vl; destruct v'; try inv H8; reflexivity.
    all: rewrite <- H8; inv H8; rewrite <- H1 in H0; inv H1.
    all: reflexivity.
Qed.

Theorem step_unlabeled_labeled_determinsm_all_step :
  forall k 
         Fs e Fs' v l Fs'' v',
  ⟨ Fs, e ⟩ -[k]-> ⟨Fs', v⟩ ->
  ⟨ Fs, e ⟩ -[k , l]-> ⟨Fs'', v'⟩ -> Fs' = Fs'' /\ v = v'.
Proof.
  intros k. induction k; intros Fs e Fs' v l Fs'' v' H H1; inv H; try now inv H1.
  inv H1. destruct (step_unlabeled_labeled_determinsm_one_step _ _ _ _ _ _ _ H2 H0).
  subst.
  apply (IHk _ _ _ _ _ _ _ H5 H3).
Qed.
