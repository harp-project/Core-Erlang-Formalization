(**
  This file contains numerous semantic properties about the frame stack semantics
  (labelled version) of Core Erlang.
 *)
From CoreErlang.FrameStack Require Export 
    SubstSemanticsLabeled.
From stdpp Require Export list option.
Import ListNotations.

Corollary side_effect_ac_value : forall fs r fs' r' l0,
  ⟨ fs, r ⟩ -⌊ Some ((AtomCreation, l0):SideEffect) ⌋->ₗ ⟨ fs', r' ⟩ ->
  exists av, l0 = [VLit (Atom av)].
Proof.
  intros. inversion H;
  unfold create_result in *; simpl in *; subst.
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
  forall {n e e' l fs fs'}, ⟨ fs, e ⟩ -[ n, l ]->ₗ ⟨ fs', e' ⟩ ->
  forall {n' e'' l' fs''},  ⟨ fs', e' ⟩ -[ n', l' ]->ₗ ⟨ fs'', e'' ⟩
->
  ⟨ fs, e ⟩ -[ n + n', l ++ l' ]->ₗ ⟨ fs'', e'' ⟩.
Proof.
  intros n Fs Fs' l e e' IH.
  induction IH; intros; auto using app_nil_l.
  simpl. econstructor. exact H. apply IHIH. exact H1.
  destruct s; rewrite H0; auto.
Qed.

Theorem transitive_any_eval :
  forall {e e' l fs fs'}, ⟨ fs, e ⟩ -[ l ]->ₗ* ⟨ fs', e' ⟩ ->
  forall {e'' l' fs''},  ⟨ fs', e' ⟩ -[ l' ]->ₗ* ⟨ fs'', e'' ⟩
->
  ⟨ fs, e ⟩ -[ l ++ l' ]->ₗ* ⟨ fs'', e'' ⟩.
Proof.
  intros. destruct H, H0. pose proof (transitive_eval H H0).
  unfold step_any_non_terminal. eexists. exact H1.
Qed.

Theorem step_determinism {e e' l fs fs'} :
  ⟨ fs, e ⟩ -⌊ l ⌋->ₗ ⟨ fs', e' ⟩ ->
  (forall {l' fs'' e''}, ⟨ fs, e ⟩ -⌊ l' ⌋->ₗ ⟨ fs'', e'' ⟩
  -> l = l' /\ fs'' = fs' /\ e'' = e').
Proof.
  intro H. inv H; intros; inv H; auto.
  - rewrite <- H1 in H9. now inv H9.
  - rewrite <- H0 in H8. now inv H8.
Qed.

Theorem value_nostep v :
  is_result v ->
  forall fs' v' l, ⟨[], v⟩ -⌊l⌋->ₗ ⟨fs' , v'⟩ -> False.
Proof.
  intros H fs' v' l' HD. inversion H; subst; inversion HD.
Qed.

Theorem step_rt_determinism {r r' fs fs' l k} :
  ⟨fs, r⟩ -[k, l]->ₗ ⟨fs', r'⟩
->
  (forall {fs'' r'' l''}, ⟨fs, r⟩ -[k, l'']->ₗ ⟨fs'', r''⟩ -> l = l'' /\ fs' = fs'' /\ r' = r'').
Proof.
  intro. induction H; intros.
  * inv H. firstorder.
  * inv H2.
    pose proof (step_determinism H H4) as [? [? ?]]. subst.
    specialize (IHstep_rt _ _ _ H5) as [? [? ?]]. subst.
    firstorder.
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
   ⟨ F, e ⟩ -⌊l⌋->ₗ ⟨ F', e' ⟩ -> FSCLOSED F -> REDCLOSED e
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
   ⟨ Fs, e ⟩ -[k , l]->ₗ ⟨Fs', v⟩ -> FSCLOSED Fs -> REDCLOSED e
->
  REDCLOSED v /\ FSCLOSED Fs'.
Proof.
  intros. induction H; auto. apply step_closedness in H. destruct H.
  apply (IHstep_rt ). all: auto.
Qed.

Theorem step_any_non_terminal_closedness : forall F e l F' e',
   ⟨ F, e ⟩ -[ l ]->ₗ* ⟨ F', e' ⟩ -> FSCLOSED F -> REDCLOSED e
-> REDCLOSED e' /\ FSCLOSED F'.
Proof.
  intros F e l F' e' H. induction H; intros. destruct H. auto.
  apply step_closedness in H. inv H.
  apply (step_any_closedness _ _ _ _ _ _ H2 H4 H5). all: assumption.
Qed.

Theorem transitive_eval_rev : forall Fs Fs' e e' k1 l1,
  ⟨ Fs, e ⟩ -[k1 , l1]->ₗ ⟨ Fs', e' ⟩->
  forall Fs'' e'' k2 l2,
  ⟨ Fs, e ⟩ -[k1 + k2 , l1 ++ l2]->ₗ ⟨ Fs'', e'' ⟩
->
  ⟨ Fs', e' ⟩ -[k2 , l2]->ₗ ⟨ Fs'', e'' ⟩.
Proof.
  intros Fs Fs' e e' k1 l1 H. induction H.
  - intros Fs'' e'' k2 l2 H. simpl in H. apply H.
  - intros Fs'' e''' k2 l2 H2. rewrite Nat.add_succ_l in H2.
    destruct s; subst.
    + inv H2. destruct s0.
      * inv H7. eapply IHstep_rt.
        destruct (step_determinism H H3).
        destruct H2. subst. assumption.
      * inv H7.
        destruct (step_determinism H H3).
        inv H2.
    + inv H2. destruct s.
      * inv H7.
        destruct (step_determinism H H3).
        inv H1.
      * inv H7. eapply IHstep_rt.
        destruct (step_determinism H H3).
        destruct H2. subst. assumption.
Qed.

Theorem frame_indep_step : forall e F F' Fs e' l,
  ⟨ F :: Fs, e ⟩ -⌊l⌋->ₗ ⟨ F' :: Fs, e' ⟩
->
  forall Fs', ⟨ F :: Fs', e ⟩ -⌊l⌋->ₗ ⟨ F' :: Fs', e' ⟩.
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
  ⟨ F :: Fs, e ⟩ -⌊l⌋->ₗ ⟨ Fs, e' ⟩
->
  forall Fs', ⟨ F :: Fs', e ⟩ -⌊l⌋->ₗ ⟨ Fs', e' ⟩.
Proof.
  intros. revert Fs'. inv H; intros.
  all: try constructor; auto.
  all: try (apply cons_neq in H3; contradiction).
  all: try (apply cons_neq in H4; contradiction).
  all: put (@length Frame : FrameStack -> nat) on H3 as H3L; simpl in H3L; lia.
Qed.

Theorem frame_indep_core : forall k e Fs Fs' v l,
  ⟨ Fs, e ⟩ -[k , l]->ₗ ⟨ Fs', v ⟩
->
  forall Fs'', ⟨ Fs ++ Fs'', e ⟩ -[k , l]->ₗ ⟨ Fs' ++ Fs'', v ⟩.
Proof.
  induction k; intros.
  * inversion H. subst. constructor.
  * inv H; inv H1.
    all: try now (simpl; econstructor; try constructor; auto).
    20: { eapply IHk in H2; simpl in *. econstructor.
      apply eval_step_case_not_match. auto. eassumption. reflexivity. }
    all: try (eapply IHk in H2; simpl in *; econstructor).
    all: try constructor.
    all: try apply H2; auto.
Qed.

Theorem frame_indep_nil : forall k e Fs v l,
  ⟨ Fs, e ⟩ -[k , l]->ₗ ⟨ [], v ⟩
->
  forall Fs', ⟨ Fs ++ Fs', e ⟩ -[k , l]->ₗ ⟨ Fs', v ⟩.
Proof.
  intros. eapply frame_indep_core in H. exact H.
Qed.

Lemma params_eval :
  forall vals ident vl exps e Fs (v : Val),
  Forall (fun v => VALCLOSED v) vals ->
  ⟨ FParams ident vl ((map VVal vals) ++ e :: exps) :: Fs, RValSeq [v]⟩ -[1 + 2 * length vals , []]->ₗ
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

Lemma params_eval_create :
  forall vals ident vl Fs (v : Val) r eff',
  Forall (fun v => VALCLOSED v) vals ->
  Some (r, eff') = create_result ident (vl ++ v :: vals) ->
  ⟨ FParams ident vl (map VVal vals) :: Fs, RValSeq [v]⟩ -[1 + 2 * length vals, match eff' with
              | None => []
              | Some x => [x]
              end ]->ₗ
  ⟨ Fs, r ⟩.
Proof.
  induction vals; simpl; intros.
  * econstructor. econstructor. exact H0. constructor.
    reflexivity.
  * specialize (IHvals ident (vl ++ [v]) Fs a). inv H.
    econstructor. constructor.
    econstructor. constructor; auto.
    rewrite <- app_assoc in IHvals.
    replace (length vals + S (length vals + 0)) with
            (1 + 2*length vals) by lia. eapply IHvals; eauto.
    reflexivity. reflexivity.
Qed.

(**
*)

From CoreErlang.FrameStack Require Export
  LabeledTermination.

Lemma terminates_in_k_step :
  forall fs e fs' e' k sl l, ⟨ fs, e ⟩ -⌊ l ⌋->ₗ ⟨ fs', e' ⟩ ->
  | fs', e' | sl – k ↓ ->
  | fs, e | (option_cons l sl) – S k ↓.
Proof.
  intros fs e fs' e' k sl l H. induction H.
  all: econstructor; eassumption.
Qed.

Theorem semantic_iff_termination :
  forall k e fs l, terminates_in_k_l_sem fs e k l <-> | fs, e | l – k ↓.
Proof.
  split.
  {
    revert e fs l. induction k; intros e fs l H.
    * destruct H as [res [Hres HD]].
      inversion HD; subst. now constructor.
    * destruct H as [res [Hres HD]].
      inversion HD; subst.
      assert (terminates_in_k_l_sem fs' e' k l0). {
        eexists. split; eassumption.
      }
      unfold terminates_in_k_l_sem in H.
      apply IHk in H.
      eapply terminates_in_k_step.
      apply H0. apply H.
  }
  {
    intros. induction H.
    all: try destruct IHterminates_in_k as [res0 [Hres0 HD]].
    all: try (now eexists; split;
                  [eassumption | econstructor;
                      [now constructor | eassumption | reflexivity]]).
    * eexists. split.
      - eassumption.
      - econstructor. econstructor; try eassumption.
        eassumption.
        destruct l; reflexivity.
    * eexists. split.
      - exact Hres0.
      - econstructor. econstructor; eassumption.
        eassumption.
        destruct l; reflexivity.
    * eexists. split.
      - eassumption.
      - econstructor. constructor; eassumption.
        eassumption.
        reflexivity.
    * eexists. split.
      - eassumption.
      - econstructor. constructor; eassumption.
        eassumption.
        reflexivity.
    * eexists. split.
      - eassumption.
      - constructor.
  }
Qed.

(* option tail function *)
Definition option_tail {A} (l : option A) (sl : list A) 
  : list A :=
  match l with
  | Some s => tail sl
  | None => sl
  end.

Theorem terminates_step :
  forall n fs e l, | fs, e | l – n ↓ -> forall fs' e' l', ⟨fs, e⟩ -⌊l'⌋->ₗ ⟨fs', e'⟩
->
  | fs', e' | (option_tail l' l) – n - 1↓.
Proof.
  intros. apply semantic_iff_termination in H. destruct H. destruct n.
  * destruct H. inv H.
    - subst. inversion H1; subst. inversion H0.
    - subst. inversion H1; subst. inversion H0.
  * destruct H.
    inv H1. apply (step_determinism H0) in H3.
    inv H3. inv H2.
    assert (exists y, is_result y /\ ⟨ fs', e' ⟩ -[ n , l0 ]->ₗ ⟨ [], y ⟩). { 
      eexists. eauto. }
    apply ex_intro in H4. apply semantic_iff_termination in H1.
    destruct s; simpl; rewrite Nat.sub_0_r; assumption.
Qed.

Corollary term_step_term :
  forall k n fs e l1 l2, | fs, e | l1 ++ l2 – n ↓ 
  -> forall fs' e' , ⟨fs, e⟩ -[k , l1]->ₗ ⟨fs', e'⟩
->
  | fs', e' | l2 – n - k ↓.
Proof.
  induction k; intros; inversion H0; subst; auto.
  * rewrite Nat.sub_0_r. auto.
  * replace (n - S k) with ((n - 1) - k) by lia. destruct s.
    - eapply terminates_step with (n := n) (l' := Some s) in H2.
      2: exact H.
      eapply IHk in H3. exact H3. exact H2.
    - eapply terminates_step with (n := n) (l' := None) in H2.
      2: exact H.
      eapply IHk in H3. exact H3. exact H2.
Qed.

Corollary term_step_term_2 :
  forall k n fs e l l1, | fs, e | l – n ↓ 
  -> forall fs' e' , ⟨fs, e⟩ -[k , l1]->ₗ ⟨fs', e'⟩
->
  | fs', e' | skipn (length l1) l – n - k ↓.
Proof.
  induction k; intros; inversion H0; subst; auto.
  * rewrite Nat.sub_0_r. auto.
  * replace (n - S k) with ((n - 1) - k) by lia. destruct s.
    - eapply terminates_step with (n := n) (l' := Some s) in H2.
      2: exact H.
      eapply IHk in H3. 2: exact H2. destruct l eqn:l'; simpl in *.
      + rewrite drop_nil in H3. exact H3.
      + exact H3.
    - eapply terminates_step with (n := n) (l' := None) in H2.
      2: exact H.
      eapply IHk in H3. exact H3. exact H2.
Qed.

Corollary step_term_term :
  forall k n fs e fs' e' l1 l2,
  ⟨fs, e⟩ -[k , l1]->ₗ ⟨fs', e'⟩ -> | fs', e' | l2 – n - k ↓ -> n >= k 
->
  | fs, e | l1 ++ l2 – n ↓.
Proof.
  intros. apply semantic_iff_termination.
  apply semantic_iff_termination in H0. destruct H0, H0.
  pose proof (transitive_eval H H2). replace (k+(n-k)) with n in H3 by lia.
  eexists. eauto.
Qed.

Corollary step_term_term_plus :
  forall k k2 fs e fs' e' l1 l2, 
  ⟨fs, e⟩ -[k , l1]->ₗ ⟨fs', e'⟩ -> | fs', e' | l2 – k2 ↓
->
  | fs, e | l1 ++ l2 – k + k2 ↓.
Proof.
  intros. apply semantic_iff_termination.
  apply semantic_iff_termination in H0. destruct H0, H0.
  pose proof (transitive_eval H H1).
  eexists. eauto.
Qed.

Lemma create_result_is_not_box :
  forall ident vl r eff',
  ICLOSED ident ->
  Forall (fun v => VALCLOSED v) vl ->
  Some (r, eff') = create_result ident vl ->
  is_result r \/
  (exists e, r = RExp e).
Proof.
  destruct ident; intros; simpl in *; try invSome; auto.
  1: left; do 2 constructor; auto; constructor; now apply indexed_to_forall.
  1: left; do 2 constructor. constructor; auto.
  (* map *)
  1-2: erewrite <- length_map; apply indexed_to_forall.
  1-2: eapply List.Forall_map; apply make_val_map_keeps_prop.
  1-2: eapply Forall_impl; [|eapply deflatten_keeps_prop; eassumption].
  1-2: intros; destruct a; apply H1.
  (****)
  1: auto.
  1: left; destruct m, f; try destruct l; try destruct l0; try invSome; try constructor; inv H; scope_solver.
  1: symmetry in H1; eapply eval_is_result in H1; auto.
  * left. destruct (primop_eval f vl) eqn: pe.
    - inv H1. eapply primop_eval_is_result; eassumption.
    - inv H1.
  * inv H. destruct v; try invSome; try now (left; constructor; auto).
    break_match_hyp; invSome; auto.
    right. eexists. reflexivity.
    left. constructor; auto.
Qed.

From CoreErlang.FrameStack Require Export
  SubstSemanticsLabeled.

Lemma Private_params_exp_eval :
  forall exps ident vl Fs (e : Exp) n (Hid : ICLOSED ident) (l : SideEffectList) (Hvl : Forall (fun v => VALCLOSED v) vl),
  | FParams ident vl exps :: Fs, e | l – n ↓ ->
  (forall m : nat,
  m < S n ->
  forall (Fs : FrameStack) (e : Exp) (ll : SideEffectList),
  | Fs, e | ll – m ↓ ->
  exists (res : Redex) (k : nat) (l : SideEffectList),
    is_result res /\ ⟨ [], e ⟩ -[ k , l ]->ₗ ⟨ [], res ⟩ /\ k <= m) ->
  exists res k l, is_result res /\
  ⟨ FParams ident vl exps :: Fs, e⟩ -[k , l]->ₗ
  ⟨ Fs, res ⟩ /\ k <= n.
Proof.
  induction exps; intros.
  * apply H0 in H as H'. 2: lia.
    destruct H' as [res [k [ll [Hres [Hd Hlt]]]]].
    eapply frame_indep_nil in Hd.
(*    specialize (H1 _ _ _ _ _ Hd).
    eapply H1 in H. *)
    eapply term_step_term_2 in H. 2: exact Hd. simpl in *.
    inv Hres.
    - do 3 eexists. split. 2: split.
      2: {
        eapply transitive_eval. exact Hd.
        eapply step_trans. constructor. reflexivity. apply step_refl.
        reflexivity.
      }
      auto.
      inv H. lia.
    - destruct vs. 2: destruct vs. 1, 3: inv H. (* vs is a singleton *)
      inv H. destruct (create_result_is_not_box ident (vl ++ [v]) res l0); auto.
      + now apply Forall_app.
      + do 3 eexists. split. 2: split.
        2: {
          eapply transitive_eval. exact Hd.
          eapply step_trans. econstructor. eassumption. apply step_refl.
          reflexivity.
        }
        auto.
        lia.
      (* if create_result was a function application: *)
      + inv H. apply H0 in H9 as H9'.
        destruct H9' as [res2 [k2 [l2 [Hres2 [Hd2 Hlt2]]]]]. 2: lia.
        eapply frame_indep_nil in Hd2.
        eapply term_step_term_2 in H9. 2: exact Hd2.
        do 3 eexists. split. 2: split.
        2: {
          eapply transitive_eval. exact Hd.
          eapply step_trans. econstructor. eassumption.
          exact Hd2. reflexivity.
        }
        auto.
        lia.
  * (* same as above *)
    apply H0 in H as H'. 2: lia.
    destruct H' as [res [k [ll [Hres [Hd Hlt]]]]].
    eapply frame_indep_nil in Hd.
    eapply term_step_term_2 in H. 2: exact Hd. simpl in *.
    inv Hres.
    - do 3 eexists. split. 2: split.
      2: {
        eapply transitive_eval. exact Hd.
        eapply step_trans. constructor. reflexivity. apply step_refl.
        reflexivity.
      }
      auto.
      inv H. lia.
    (* up to this point*)
    - destruct vs. 2: destruct vs. 1, 3: inv H.
      inv H. apply IHexps in H9 as [res2 [k2 [l2 [Hres2 [Hd2 Hlt2]]]]].
      4: {
        intros. eapply H0. lia. eassumption.
      }
      do 3 eexists. split. 2: split.
      2: {
        eapply transitive_eval. exact Hd.
        eapply step_trans. constructor. exact Hd2.
        reflexivity.
      }
      auto.
      lia.
      auto.
      now apply Forall_app.
Qed.

Theorem prefix_drop : forall {A} (l0 l1 : list A) ,
            l0 `prefix_of` l1 -> 
            forall l2,
              l2 = drop (length l0) l1 ->
              l1 = l0 ++ l2 .
Proof.
  induction l0; intros; subst.
  - simpl. rewrite drop_0. reflexivity.
  - inv H. simpl. rewrite drop_app_length.
    reflexivity.
Qed.

Lemma Private_params_exp_eval_empty :
  forall exps ident vl Fs (e : Exp) n l (Hid : ICLOSED ident) (Hvl : Forall (fun v => VALCLOSED v) vl) (Hcle : EXPCLOSED e) (Hexps : Forall (fun e => EXPCLOSED e) exps),
  | FParams ident vl exps :: Fs, e | l – n ↓ ->
  (forall m : nat,
  m < S n ->
  forall (Fs : FrameStack) (e : Exp) (l : SideEffectList),
  | Fs, e | l – m ↓ -> EXPCLOSED e ->
  exists (res : Redex) (k : nat) (l' : SideEffectList),
    is_result res /\ ⟨ [], e ⟩ -[ k , l' ]->ₗ ⟨ [], res ⟩ /\ k <= m /\ l' `prefix_of` l) ->
  exists res k l', is_result res /\
  ⟨ [FParams ident vl exps], e⟩ -[k , l']->ₗ
  ⟨ [], res ⟩ /\ k <= n /\ l' `prefix_of` l.
Proof.
  induction exps; intros.
  * apply H0 in H as H'. 2: lia. 2: assumption.
    destruct H' as [res [k [l' [Hres [Hd [Hlt Hpref]]]]]].
    eapply frame_indep_nil in Hd as Hlia.
    eapply frame_indep_nil in Hd.
    eapply term_step_term_2 in H as Hlia2. 2: exact Hlia. simpl in *.
    inv Hres.
    - do 3 eexists. split. 2: split. 3: split.
      2: {
        eapply transitive_eval. exact Hd.
        eapply step_trans. constructor. reflexivity. apply step_refl.
        reflexivity.
      }
      auto.
      inv Hlia2. lia.
      rewrite app_nil_r. assumption.
    - destruct vs. 2: destruct vs. 1, 3: inv Hlia2. (* vs is a singleton *)
      inv Hlia2. destruct (create_result_is_not_box ident (vl ++ [v]) res l0).
      + auto.
      + now apply Forall_app.
      + eassumption.
      + do 3 eexists. split. 2: split. 3: split.
        2: {
          eapply transitive_eval. exact Hd.
          eapply step_trans. econstructor. eassumption. apply step_refl.
          reflexivity.
        }
        auto.
        lia.
        unfold option_cons in *.
        destruct l0. 2: rewrite app_nil_r; assumption.
        rewrite (prefix_drop _ _ Hpref _ H7).
        rewrite (cons_middle s l' ls). rewrite app_assoc.
        apply prefix_app_r. auto.
      (* if create_result was a function application: *)
      + inv H2. apply H0 in H9 as H9'. 2: lia.
        destruct H9' as [res2 [k2 [l2 [Hres2 [Hd2 [Hlt2 Hpref2]]]]]].
        eapply frame_indep_nil in Hd2 as Hlia3.
        eapply frame_indep_nil in Hd2.
        eapply term_step_term_2 in H9. 2: exact Hlia3.
        do 3 eexists. split. 2: split. 3: split.
        2: {
          eapply transitive_eval. exact Hd.
          eapply step_trans. econstructor. eassumption.
          exact Hd2. reflexivity.
        }
        auto.
        lia. subst.
        2: { 
          pose proof (create_result_closed
                            (vl ++ [v])
                            ident
                            x
                            l0
                            ltac:(apply Forall_app; auto)
                            Hid
                            H4).
          by inversion H2.
        }
        unfold option_cons in *.
        destruct l0; rewrite (prefix_drop _ _ Hpref _ H7).
        ** do 2 rewrite cons_middle.
           apply prefix_app.
           apply prefix_app.
           assumption.
        ** apply prefix_app.
           assumption.
  * (* same as above *)
    apply H0 in H as H'. 2: lia.
    destruct H' as [res [k [l' [Hres [Hd Hlt]]]]].
    eapply frame_indep_nil in Hd as Hlia.
    eapply frame_indep_nil in Hd.
    eapply term_step_term_2 in H as Hlia2. 2: exact Hlia. simpl in *.
    inv Hres.
    - do 3 eexists. split. 2: split. 3: split.
      2: {
        eapply transitive_eval. exact Hd.
        eapply step_trans. constructor. reflexivity. apply step_refl.
        reflexivity.
      }
      auto.
      inv Hlia2. lia.
      destruct Hlt.
      rewrite app_nil_r.
      assumption.
    (* up to this point*)
    - destruct vs. 2: destruct vs. 1, 3: inv Hlia2.
      inv Hlia2. inv H1. inv Hexps.
      apply IHexps in H9 as [res2 [k2 [l2 [Hres2 [Hd2 Hlt2]]]]]; auto.
      3: {
        intros. eapply H0. lia. eassumption. eassumption.
      }
      do 3 eexists. split. 2: split. 3: split.
      2: {
        eapply transitive_eval. exact Hd.
        eapply step_trans. constructor.
        exact Hd2.
        reflexivity.
      }
      auto.
      lia.
      auto.
      destruct Hlt2. destruct Hlt.
      inv H8. apply prefix_app.
      rewrite drop_app_length in H2.
      assumption.
      apply Forall_app. split; auto.
    - auto.
Qed.

(**
  so far
*)

Lemma term_empty : forall x Fs (e : Exp) (He : EXPCLOSED e) (l : SideEffectList),
  | Fs, e | l – x ↓ ->
  exists k l', | [], e | l' – k ↓ /\ k <= x /\ l' `prefix_of` l.
Proof.
  induction x using Wf_nat.lt_wf_ind; intros; inv H0.
  * do 2 eexists. split. constructor; auto. constructor. auto. split.
    lia. apply prefix_nil.
  * destruct el. (* tricks to avoid RBox *)
    - do 2 eexists. split. constructor.
      epose proof (cool_params_0_l [] IValues [] _ None []). simpl in H0.
      eapply H0.
      congruence. reflexivity. do 2 constructor. auto. inv H3. split. lia.
      apply prefix_nil.
    - inv H3. destruct_scopes.
      eapply Private_params_exp_eval_empty in H9 as HH2; auto.
      2-3: rewrite <- indexed_to_forall in H3; now inv H3.
      2: {
        intros. epose proof (H m ltac:(slia) Fs0 e0 _ _ H1) as [j [l' [HD [Hj Hpref]]]].
        apply semantic_iff_termination in HD as [res [Hres Hr]].
        do 3 eexists. split. 2: split. 3: split. all: eassumption.
      }
      destruct HH2 as [res [k [l' [Hres [Hd [Hlt Hpref]]]]]].
      do 2 eexists. split. do 2 constructor. congruence.
      eapply semantic_iff_termination. eexists.
      split. 2: exact Hd. auto. split. lia. assumption.
  * destruct el. (* proof is same as above, tricks to avoid RBox *)
    - do 2 eexists. split. constructor.
      epose proof (cool_params_0_l [] ITuple [] _ None []). simpl in H0.
      eapply H0.
      congruence. reflexivity. do 4 constructor; auto. intros. inv H1. inv H3.
      split. lia. apply prefix_nil.
    - inv H3. destruct_scopes.
      eapply Private_params_exp_eval_empty in H9 as HH2; auto.
      2-3: rewrite <- indexed_to_forall in H3; now inv H3.
      2: {
        intros. epose proof (H m ltac:(slia) Fs0 e0 _ _ H1) as [j [l' [HD [Hj Hpref]]]].
        apply semantic_iff_termination in HD as [res [Hres Hr]].
        do 3 eexists. split. 2: split. 3: split. all: eassumption.
      }
      destruct HH2 as [res [k [l' [Hres [Hd [Hlt Hpref]]]]]].
      do 2 eexists. split. do 2 constructor. congruence.
      eapply semantic_iff_termination. eexists.
      split. 2: exact Hd. auto. split. lia. assumption.
  * do 2 eexists. split. do 5 constructor; slia. split. lia. apply prefix_nil.
  * destruct_scopes.
    eapply Private_params_exp_eval_empty in H3 as HH2; auto.
    2: apply (H1 0); slia.
    2: { constructor. apply (H5 0); slia. apply flatten_keeps_prop.
         rewrite indexed_to_forall with (def := (˝VNil, ˝VNil)). intros.
         specialize (H1 (S i) ltac:(slia)). specialize (H5 (S i) ltac:(slia)).
         simpl in *. rewrite map_nth with (d := (˝VNil, ˝VNil)) in H1, H5.
         destruct nth; now split.
       }
    2: {
      intros. epose proof (H m ltac:(slia) Fs0 e _ _ H2) as [j [l' [HD [Hj Hpref]]]].
      apply semantic_iff_termination in HD as [res [Hres Hr]].
      do 3 eexists. split. 2: split. 3: split. all: eassumption.
    }
    destruct HH2 as [res [k0 [l' [Hres [Hd [Hlt Hpref]]]]]].
    do 2 eexists. split. constructor.
    eapply semantic_iff_termination. eexists.
    split. 2: exact Hd. auto. split. lia. assumption.
  * (* Call is trickier, because first the module, then the function
       expression has to be evaluated *)
    destruct_scopes. apply H in H3 as HD1; auto.
    destruct HD1 as [k1 [l1 [D1 [Hlia1 Hpref]]]].
    apply semantic_iff_termination in D1 as [res1 [Hres1 Hr1]].
    eapply frame_indep_nil in Hr1 as Hr1'.
    eapply frame_indep_nil in Hr1.
    eapply term_step_term_2 in H3.
    2: exact Hr1. simpl in *.
    inv Hres1.
    (* moduleexp Exception *)
    - inv H3. do 2 eexists. split. constructor.
      eapply step_term_term_plus. exact Hr1'. constructor.
      congruence. constructor. constructor; auto. split. lia.
      rewrite app_nil_r. assumption.
    (* moduleexp Value *)
    - inv H3. inv H0. (* clear H5. *)
      apply H in H10 as HD2; auto. 2: lia.
      destruct HD2 as [k2 [l2 [D2 [Hlia2 Hpref2]]]].
      apply semantic_iff_termination in D2 as [res2 [Hres2 Hr2]].
      eapply frame_indep_nil in Hr2 as Hr2'.
      eapply frame_indep_nil in Hr2.
      eapply term_step_term_2 in H10.
      2: exact Hr2. simpl in *.
      inv Hres2.
      (* funexp exception *)
      + inv H10. do 2 eexists. split. constructor.
        eapply step_term_term_plus. exact Hr1'. constructor.
        eapply step_term_term_plus. exact Hr2'. constructor.
        congruence. constructor. constructor; auto. split. lia.
        rewrite app_nil_r. destruct Hpref2. symmetry in H2.
        epose proof (prefix_drop l1 l Hpref (l2 ++ x) H2).
        rewrite H5. Search (_ ++ _ `prefix_of` _ ++ _).
        apply prefix_app. rewrite <- app_nil_r at 1. apply prefix_app.
        apply prefix_nil.
      (* moduleexp value *)
      + inv H10. destruct el. (* tricks to avoid RBox *)
        ** inv H13. do 2 eexists. split.
           constructor.
           eapply step_term_term_plus. exact Hr1'. constructor.
           eapply step_term_term_plus. exact Hr2'. constructor.
           epose proof (cool_params_0_l [] (ICall v f0) [] _ l0 []). simpl in H1.
           apply H1.
           congruence. exact H12. clear H1.
           (* here is this different from the previous *)
           simpl in H12. destruct_foralls.
           destruct v, f0; try destruct l; try destruct l0; try destruct l3; try invSome; try constructor; auto.
           all: try (constructor; constructor; apply indexed_to_forall);
             try (constructor; [|constructor]; auto).
           -- destruct l4.
              ++ eapply (eval_is_result ); eauto.
              ++ inv H12.
           -- destruct l4 eqn: a.
              ++ eapply (eval_is_result ); eauto.
              ++ inv H12. unfold badfun.
                 eapply exception_is_result. auto. scope_solver.
           -- destruct l4.
              ++ eapply (eval_is_result ); eauto.
              ++ inv H12.
           -- destruct l4.
              ++ eapply (eval_is_result ); eauto.
              ++ inv H12.
                 eapply exception_is_result. auto. scope_solver.
           -- split. lia. destruct l0; simpl in H9; simpl.
              ++ destruct Hpref2. rewrite H1 in H9.
                 symmetry in H1.
                 epose proof (prefix_drop _ _ Hpref _ H1). rewrite H2.
                 apply prefix_app. apply prefix_app. rewrite drop_app_length in H9.
                 rewrite <- H9.
                 assert (s :: ls = [s] ++ ls). {
                   simpl. reflexivity.
                 } rewrite H5.
                 rewrite <- app_nil_r at 1. apply prefix_app. apply prefix_nil.
              ++ destruct Hpref2. rewrite H1 in H9.
                 symmetry in H1.
                 epose proof (prefix_drop _ _ Hpref _ H1). rewrite H2.
                 apply prefix_app. apply prefix_app. apply prefix_nil.
        ** inv H13. inv H0.
           eapply Private_params_exp_eval_empty in H17 as HD3; auto.
           2: {
             apply (H6 0). slia.
           }
           2: {
             apply indexed_to_forall in H6. now inv H6.
           }
           2: {
             intros. epose proof (H m0 ltac:(slia) Fs0 e0 _ _ H1) as [j [ls [HD [Hj Hpref3]]]].
             apply semantic_iff_termination in HD as [res [Hres Hr]].
             do 3 eexists. split. 2: split. 3: split. all: eassumption.
           }
           destruct HD3 as [res3 [k3 [l3 [Hres3 [Hd3 [Hlt3 Hpref3]]]]]].
           do 2 eexists. split. 2: split.
           constructor.
           eapply step_term_term_plus. exact Hr1'. constructor.
           eapply step_term_term_plus. exact Hr2'. constructor.
           constructor. congruence.
           eapply semantic_iff_termination. eexists.
           split. 2: exact Hd3. auto. lia.
           destruct Hpref. subst.
           apply prefix_app. rewrite drop_app_length in *.
           destruct Hpref2. subst.
           apply prefix_app. rewrite drop_app_length in *.
           destruct Hpref3. subst.
           rewrite app_nil_end_deprecated at 1.
           apply prefix_app. apply prefix_nil.
  * destruct el. (* tricks to avoid RBox *)
    - inv H3. do 2 eexists. split. constructor. eapply cool_params_0_l.
      congruence. eassumption.
      (* here is this different from the previous *)
      simpl. constructor. 2: split. 2: lia. cbn in H5.
      destruct (primop_eval f []) eqn: pe. 2: invSome.
      destruct p. inv H5. eapply primop_eval_is_result with (f:=f); eauto.
      destruct l0; simpl.
      + assert (s :: ls = [s] ++ ls). {
                simpl. reflexivity.
               }
        rewrite H0.
        rewrite app_nil_end_deprecated at 1.
        apply prefix_app. apply prefix_nil.
      + apply prefix_nil.
    - inv H3. destruct_scopes.
      eapply Private_params_exp_eval_empty in H9 as HH2; auto.
      2-3: rewrite <- indexed_to_forall in H3; now inv H3.
      2: {
        intros. epose proof (H m ltac:(slia) Fs0 e0 _ _ H1) as [j [l1 [HD [Hj Hpref]]]].
        apply semantic_iff_termination in HD as [res [Hres Hr]].
        do 3 eexists. split. 2: split. 3: split. all: eassumption.
      }
      destruct HH2 as [res [k [l1 [Hres [Hd [Hlt Hpref]]]]]].
      do 2 eexists. split. do 2 constructor. congruence.
      eapply semantic_iff_termination. eexists.
      split. 2: exact Hd. auto. split. lia. assumption.
  (* application is harder, because first, the function parameter needs
     to be evaluated, then we do a case separation, whether l = [].
     Everytime an exception occurs, that needs to be propagated -> hence
     the number of case separations. *)
  * apply H in H3 as H3'. destruct H3' as [j [l1 [Hj [Hlt1 Hpref]]]]. 2: lia.
    apply semantic_iff_termination in Hj as [res [Hres Hr]].
    eapply frame_indep_nil in Hr as Hlia1.
    eapply frame_indep_nil in Hr. eapply term_step_term_2 in H3.
    2: exact Hlia1. simpl in *.
    destruct l. (* tricks to avoid RBox *)
    - inv Hres. (* exception result? *)
      + exists (2 + j). eexists. split. constructor.
        eapply step_term_term. simpl. exact Hr. 2: lia.
        replace (S j - j) with 1 by lia.
        constructor. reflexivity. constructor. auto.
        inv H3. split. lia.
        rewrite app_nil_r. assumption.
      + do 2 eexists.
        split. 2: split. 3: exact Hpref. constructor. inv H3. inv H6.
        
        
        all: admit.
        (**
         destruct (create_result_is_not_box (IApp v) [] res l1).
        ** inv H0; now constructor.
        ** auto.
        ** assumption.
        ** exists (3 + j). split. constructor.
           eapply step_term_term. exact Hr. 2: lia.
           replace (S (S j) - j) with 2 by lia.
           constructor. econstructor. congruence. eassumption.
           now constructor.
           lia.
        ** inv H1. apply H in H9 as H9'. 2: lia.
           destruct H9' as [i [Hd2 Hlt2]].
           exists (1 + (j + 2 + i)). split. constructor.
           eapply step_term_term. exact Hr. 2: lia.
           replace (j + 2 + i - j) with (2 + i) by lia.
           constructor. econstructor. congruence. eassumption.
           assumption. lia.
           inv H0.
           pose proof (create_result_closed [] (IApp v) x l ltac:(auto) ltac:(now constructor) H7). now inv H0. *)
    - inv Hres.
      + exists (2 + j). eexists. split. constructor.
        eapply step_term_term. exact Hr. 2: lia.
        replace (S j - j) with 1 by lia.
        constructor. reflexivity. constructor. auto.
        inv H3. split. lia. rewrite app_nil_r. assumption.
      + inv H3. admit.
      
        (**
        inv H2. destruct_scopes.
        eapply Private_params_exp_eval_empty in H10 as HH2; auto.
        3-4: rewrite <- indexed_to_forall in H7; now inv H7.
        2: { inv H0; now constructor. }
        2: {
          intros. epose proof (H m ltac:(slia) Fs0 e1 _ H2) as [i [Hd2 Hi]].
          apply semantic_iff_termination in Hd2
             as [res2 [Hres2 Hr2]].
          do 2 eexists. split. 2: split. all: eassumption.
        }
        destruct HH2 as [res2 [i [Hres2 [Hd2 Hlt2]]]].
        assert (⟨ [FApp1 (e :: l)], RValSeq [v]⟩ -[2]-> ⟨ [FParams (IApp v) [] l], e ⟩). {
          repeat econstructor. congruence.
        }
        eapply (transitive_eval Hr) in H1.
        eapply (transitive_eval H1) in Hd2.
        eexists. split.
        constructor. apply semantic_iff_termination.
        eexists. split. 2: exact Hd2. assumption. lia.
        *)
    - now destruct_scopes.
  * apply H in H3 as HH. 2: lia.
    destruct HH as [i [li [Hi [Hlt Hprefi]]]].
    apply semantic_iff_termination in Hi as [res [Hres Hr]].
    eapply frame_indep_nil in Hr as Hlia1.
    eapply frame_indep_nil in Hr.
    eapply term_step_term_2 in H3. 2: exact Hlia1.
    inv Hres. (* tail exception or not *)
    - exists (S i + 1). eexists.
      split. 2: split. 2: inv H3; lia.
      simpl. constructor. apply semantic_iff_termination.
      exists (RExc (cl, v1, v2)). split; auto. eapply transitive_eval.
      exact Hr. do 2 econstructor. reflexivity.
      rewrite app_nil_r. assumption.
    - inv H3. apply H in H6 as HH. 2: lia.
      destruct HH as [j [lj [Hj [Hltj Hprefj]]]].
      simpl in *. apply semantic_iff_termination in Hj as [hdres [Hr2 Hd2]].
      eapply frame_indep_nil in Hd2 as Hlia2.
      eapply frame_indep_nil in Hd2.
      eapply term_step_term_2 in H6. 2: exact Hlia2.
      assert (⟨ [FCons1 hd], RValSeq [tl0] ⟩ -[1 , []]->ₗ ⟨[FCons2 tl0], hd⟩). {
        repeat econstructor.
      }
      eapply (transitive_eval Hr) in H1.
      eapply (transitive_eval H1) in Hd2.
      inv Hr2. (* head exception or not *)
      + exists (1 + (i + (1 + (j + 1) ))). eexists. split.
        simpl. constructor. eapply step_term_term.
        exact Hd2.
        replace (i + S (j + 1) - (i + 1 + j)) with 1 by lia.
        constructor. reflexivity. do 2 constructor; auto.
        lia. split.
        inv H6. simpl. lia.
        repeat (rewrite app_nil_r).
        destruct Hprefi. rewrite H4 in *. apply prefix_app.
        destruct Hprefj. rewrite drop_app_length in H5. rewrite H5.
        rewrite <- app_nil_r at 1. apply prefix_app. apply prefix_nil.
      + exists (1 + (i + (1 + (j + 1) ))). eexists. split.
        simpl. constructor. eapply step_term_term.
        exact Hd2. inv H1.
        replace (i + S (j + 1) - (i + 1 + j)) with 1 by lia.
        
        
        
        all: admit.
        (**
        constructor. do 4 constructor; inv H0; now inv H3.
        lia.
        inv H2. lia.
        *)
      + now destruct_scopes.
    - now destruct_scopes.
  * apply H in H3 as HH. 2: lia.
    destruct HH as [i [li [Hi [Hlt Hprefi]]]].
    apply semantic_iff_termination in Hi as [res [Hres Hr]].
    eapply frame_indep_nil in Hr as Hlia1.
    eapply frame_indep_nil in Hr.
    eapply term_step_term_2 in H3. 2: exact Hlia1.
    inv Hres. (* tail exception or not *)
    - exists (S i + 1). eexists.
      split. 2: split. 2: inv H3; lia.
      simpl. constructor. apply semantic_iff_termination.
      exists (RExc (cl, v1, v2)). split; auto. eapply transitive_eval.
      exact Hr. do 2 econstructor. reflexivity.
      rewrite app_nil_r. assumption.
    - inv H3. apply H in H9 as HH. 2: lia.
      destruct HH as [j [lj [Hj [Hltj Hprefj]]]].
      simpl in *. apply semantic_iff_termination in Hj as [hdres [Hr2 Hd2]].
      eapply frame_indep_nil in Hd2 as Hlia2.
      eapply term_step_term_2 in H9. 2: exact Hlia2.
      assert (⟨ [FLet (Datatypes.length vs) e2], RValSeq vs ⟩ -[1, []]->ₗ 
      ⟨ [], e2.[list_subst vs idsubst] ⟩). {
        repeat econstructor.
      }
      eapply (transitive_eval Hr) in H1.
      eapply (transitive_eval H1) in Hd2.
      exists (1 + (i + (1 + j))). eexists. split. 2: split. 2: inv Hr2; inv H1; lia.
      constructor. eapply step_term_term. exact Hd2.
      replace (i + (1 + j) - (i + 1 + j)) with 0 by lia.
      now constructor.
      lia.
      repeat (rewrite app_nil_r).
      destruct Hprefi. rewrite H2 in *. apply prefix_app.
      destruct Hprefj. rewrite drop_app_length in H3. rewrite H3.
      rewrite <- app_nil_r at 1. apply prefix_app. apply prefix_nil.
      destruct_scopes. apply -> subst_preserves_scope_exp; eauto.
      rewrite Nat.add_0_r. now apply scoped_list_idsubst.
    - now destruct_scopes.
  (* Sequencing is basically same as let *)
  * apply H in H3 as HH. 2: lia.
    destruct HH as [i [li [Hi [Hlt Hprefi]]]].
    apply semantic_iff_termination in Hi as [res [Hres Hr]].
    eapply frame_indep_nil in Hr as Hlia1.
    eapply frame_indep_nil in Hr.
    eapply term_step_term_2 in H3. 2: exact Hlia1.
    inv Hres. (* tail exception or not *)
    - exists (S i + 1). eexists.
      split. 2: split. 2: inv H3; lia.
      simpl. constructor. apply semantic_iff_termination.
      exists (RExc (cl, v1, v2)). split; auto. eapply transitive_eval.
      exact Hr. do 2 econstructor. reflexivity.
      rewrite app_nil_r. assumption.
    - inv H3. apply H in H6 as HH. 2: lia.
      destruct HH as [j [lj [Hj [Hltj Hprefj]]]].
      simpl in *. apply semantic_iff_termination in Hj as [hdres [Hr2 Hd2]].
      eapply frame_indep_nil in Hd2 as Hlia2.
      eapply term_step_term_2 in H6. 2: exact Hlia2.
      assert (⟨ [FSeq e2], RValSeq [v] ⟩ -[1 , []]->ₗ
      ⟨ [], e2 ⟩). {
        repeat econstructor.
      }
      eapply (transitive_eval Hr) in H1.
      eapply (transitive_eval H1) in Hd2.
      exists (1 + (i + (1 + j))). eexists. split. 2: split. 2: inv Hr2; inv H1; lia.
      constructor. eapply step_term_term. exact Hd2.
      replace (i + (1 + j) - (i + 1 + j)) with 0 by lia.
      now constructor.
      lia.
      repeat (rewrite app_nil_r).
      destruct Hprefi. rewrite H2 in *. apply prefix_app.
      destruct Hprefj. rewrite drop_app_length in H3. rewrite H3.
      rewrite <- app_nil_r at 1. apply prefix_app. apply prefix_nil.
      now destruct_scopes.
    - now destruct_scopes.
  * do 2 eexists. split. constructor. do 3 constructor; auto.
    destruct_scopes. constructor; intros. inv H0. auto. split. lia.
    apply prefix_nil.
  (* for case: list_length_ind on H3 (or structural could also be enough) *)
  * apply H in H3 as HH. 2: lia. destruct HH as [k1 [l1 [Hd1 [Hlt1 Hpref1]]]].
    apply semantic_iff_termination in Hd1 as [r1 [Hr Hd]].
    eapply frame_indep_nil in Hd as Hlia1.
    eapply frame_indep_nil in Hd.
    eapply term_step_term_2 in H3. 2: exact Hlia1.
    simpl in *.
    inv Hr. (* exception? *)
    + exists (1 + k1 + 1). eexists. split. 2: split. 2: inv H3; lia.
      simpl. constructor. eapply step_term_term. exact Hd.
      replace (k1 + 1 - k1) with 1 by lia.
      constructor. reflexivity. do 2 constructor; auto. lia.
      rewrite app_nil_r. assumption.
      (**
        so far
      *)
    + epose proof (Private_term_empty_case l Fs vs (k - k1) _ _ _ H3) as
        [res [k2 [Hres [Hd2 Hlt2]]]].
      Unshelve. 10: {
        intros. eapply H. lia. 2: eassumption. auto.
      }
      pose proof (transitive_eval Hd Hd2).
      exists (S (k1 + k2)). split. 2: lia.
      constructor.
      apply semantic_iff_termination. exists res. now split.
      all: auto.
      destruct_scopes. rewrite indexed_to_forall with (def := ([], ˝VNil, ˝VNil)).
      intros. apply H7 in H1 as H1'. apply H8 in H1. clear H7 H8.
      rewrite map_nth with (d := ([], ˝VNil, ˝VNil)) in H1, H1'.
      extract_map_fun F. replace (˝VNil) with (F ([], ˝VNil, ˝VNil)) in H1' at 3 by now subst F. subst F. rewrite map_nth in H1'.
      extract_map_fun F. replace [] with (F ([], ˝VNil, ˝VNil)) in H1 by now subst F. subst F. rewrite map_nth in H1.
      destruct nth, p; split; cbn in *; rewrite Nat.add_0_r in *. apply H1'. apply H1.
    + now destruct_scopes.
  * apply H in H4 as [i [Hd Hlt]].
    eexists. split. econstructor. reflexivity. exact Hd. lia. lia.
    apply -> subst_preserves_scope_exp. destruct_scopes. apply H6.
    apply scoped_list_subscoped_eq. unfold convert_to_closlist. now do 2 rewrite length_map. 2: auto.
    apply closlist_scope. rewrite length_map, map_map; intros. destruct_scopes.
    apply H6 in H0. clear -H0. rewrite map_map.
    do 2 rewrite map_nth with (d := (0, ˝VNil)) in H0.
    do 2 rewrite map_nth with (d := (0, ˝VNil)). destruct nth. now cbn in *.
  * apply H in H3 as HH. 2: lia.
    destruct HH as [i [Hd Hlt]].
    apply semantic_iff_termination in Hd as [r [Hres Hd]].
    eapply frame_indep_nil in Hd as Hlia.
    eapply frame_indep_nil in Hd.
    eapply term_step_term in H3. 2: exact Hlia.
    simpl in *.
    inv Hres. (* exception or not *)
    - inv H3. (* 2: { inv H7. } *)
      apply H in H4 as [j [Hd2 Hlt2]]. 2: lia.
      exists (1 + (i + (1 + j))). split. 2: lia.
      constructor. eapply step_term_term. exact Hd. 2: lia.
      replace (i + (1 + j) - i) with (S j) by lia.
      now constructor.
      destruct_scopes. apply -> subst_preserves_scope_exp; eauto.
      apply cons_scope. destruct cl; simpl; auto.
      apply cons_scope. auto.
      apply cons_scope. auto.
      auto.
    - inv H3.
      apply H in H10 as [j [Hd2 Hlt2]]. 2: lia.
      exists (1 + (i + (1 + j))). split. 2: lia.
      constructor. eapply step_term_term. exact Hd. 2: lia.
      replace (i + (1 + j) - i) with (S j) by lia.
      now constructor.
      destruct_scopes. apply -> subst_preserves_scope_exp. eauto.
      rewrite Nat.add_0_r. now apply scoped_list_idsubst.
    - now destruct_scopes.
  * eexists. split. now constructor. lia.
Unshelve.
  all: auto.
Qed.

(* NOTE: This is not a duplicate! Do not remove! *)
(* sufficient to prove it for Exp, since value sequences and
   exceptions terminate in 0/1 step by definition in the
   empty stack (and RBox does not terminate!). *)
Corollary term_eval_empty : forall x Fs (e : Exp) (He : EXPCLOSED e),
  | Fs, e | x ↓ ->
  exists res k, is_result res /\ ⟨ [], e ⟩ -[k]-> ⟨ [], res ⟩ /\ k <= x.
Proof.
  intros. apply term_empty in H; auto. destruct H as [k [H Hlt]].
  apply semantic_iff_termination in H as [r [Hr H]].
  do 2 eexists; eauto.
Qed.

Corollary term_eval : forall x Fs (e : Exp) (He : EXPCLOSED e), | Fs, e | x ↓ ->
  exists v k, is_result v /\ ⟨ Fs, e ⟩ -[k]-> ⟨ Fs, v ⟩ /\ k <= x.
Proof.
  intros.
  apply term_eval_empty in H as [r [k [Hr [Hd Hlt]]]].
  exists r, k. intuition.
  eapply frame_indep_nil in Hd. exact Hd. auto.
Qed.

Corollary term_eval_both : forall x Fs (e : Exp) (He : EXPCLOSED e), | Fs, e | x ↓ ->
  exists v k, is_result v /\
  ⟨ [], e ⟩ -[k]-> ⟨ [], v ⟩ /\
  ⟨ Fs, e ⟩ -[k]-> ⟨ Fs, v ⟩ /\ k <= x.
Proof.
  intros. apply term_eval_empty in H as [r [k [Hr [Hd Hlt]]]].
  exists r, k. intuition.
  eapply frame_indep_nil in Hd. exact Hd.
  assumption.
Qed.

Theorem put_back : forall F e Fs (P : EXPCLOSED e) (P2 : FCLOSED F),
  | F :: Fs, e | ↓ -> | Fs, plug_f F e | ↓.
Proof.
  destruct F; intros; simpl.
  all: try now (inv H; exists (S x); constructor; auto).
  * inv H. exists (3 + x). do 2 constructor. now inv P2.
    now constructor.
  * inv H. destruct ident; simpl; destruct_scopes.
  (* These build on the same idea, however, calls, applications and maps are a bit different: *)
  1-2, 5: destruct vl; destruct_foralls; simpl; [
    eexists; do 2 constructor; [congruence | eassumption]
    |
    exists (4 + ((2 * length vl) + x)); do 2 constructor;
    try congruence; constructor; auto;
    eapply step_term_term;
    [
      apply params_eval
      |
      simpl app;
      now replace (S (2 * Datatypes.length vl + x) - (1 + 2 * Datatypes.length vl)) with x by lia
      |
      lia
    ]
  ]; auto.
    - destruct_scopes. specialize (H6 eq_refl).
      inv H6. destruct vl.
      + simpl. destruct el.
        ** simpl in H. congruence.
        ** eexists. constructor.
           erewrite deflatten_flatten. eassumption.
           simpl in H. instantiate (1 := x0). lia.
      + simpl. destruct vl; simpl.
        ** eexists. do 2 constructor. now inv H4. constructor. simpl.
           erewrite deflatten_flatten. eassumption.
           simpl in H. instantiate (1 := x0). lia.
        ** exists (5 + ((2 * length vl) + x)). do 2 constructor.
           now inv H4. do 2 constructor. now destruct_foralls.
           erewrite deflatten_flatten.
           2: { rewrite length_app, length_map. simpl in *.
                instantiate (1 := x0). lia. }
           eapply step_term_term.
           apply params_eval. now destruct_foralls. simpl app. 2: lia.
           now replace (S (2 * Datatypes.length vl + x) - (1 + 2 * Datatypes.length vl)) with x by lia.
    - destruct vl; simpl.
      + eexists. do 2 constructor. now inv H3. do 2 constructor. now inv H3.
        do 2 constructor. congruence. eassumption.
      + exists (8 + ((2 * length vl) + x)). do 2 constructor.
        now inv H3. do 2 constructor. now inv H3.
        do 2 constructor. congruence.
        constructor. now inv H4.
        eapply step_term_term.
        apply params_eval. now inv H4. simpl app. 2: lia.
        now replace (S (2 * Datatypes.length vl + x) - (1 + 2 * Datatypes.length vl)) with x by lia.
    - destruct vl; simpl.
      + eexists. do 2 constructor. now inv H3. do 2 constructor. congruence. eassumption.
      + exists (6 + ((2 * length vl) + x)). do 2 constructor.
        now inv H3. do 2 constructor. congruence.
        constructor. now inv H4.
        eapply step_term_term.
        apply params_eval. now inv H4. simpl app. 2: lia.
        now replace (S (2 * Datatypes.length vl + x) - (1 + 2 * Datatypes.length vl)) with x by lia.
  * destruct H as [k D]. eexists. do 2 constructor. now inv P2. constructor.
    eassumption.
  * inv H. apply term_eval_both in H0 as H'. destruct H' as [res [l [Hres [D0 [D1 Hlt]]]]]. 2: assumption.
    eapply term_step_term in H0. 2: eassumption.
    clear D1. inv Hres.
    - inv H0.
      eexists. do 3 econstructor. congruence. reflexivity.
      econstructor. reflexivity. cbn. eapply frame_indep_nil in D0.
      do 2 rewrite idsubst_is_id_exp.
      eapply step_term_term_plus. eassumption. constructor. reflexivity.
      eassumption.
    - inv H0.
      + eexists. do 3 econstructor. congruence. reflexivity.
        econstructor. reflexivity. do 2 rewrite idsubst_is_id_exp.
        eapply frame_indep_nil in D0. eapply step_term_term_plus.
        eassumption. econstructor. eassumption.
      + eexists (4 + (l + (7 + 2 * length lv + k))). simpl. do 3 econstructor. congruence. reflexivity.
        econstructor. reflexivity. do 2 rewrite idsubst_is_id_exp.
        eapply frame_indep_nil in D0. eapply step_term_term_plus.
        eassumption. constructor. econstructor.
        reflexivity. cbn. do 2 constructor.
        replace (map
       (fun '(p, x0, y) =>
        (p, x0.[upn (PatListScope p) idsubst],
         y.[upn (PatListScope p) idsubst])) le) with le.
        replace (map (fun x0 : Exp => x0.[idsubst]) (map VVal lv)) with (map VVal lv).
        2: {
          clear. induction lv; auto. simpl. rewrite idsubst_is_id_val.
          now rewrite IHlv at 1.
        }
        2: {
          clear. induction le; auto. simpl. destruct a, p.
          rewrite idsubst_upn, <-IHle.
          now do 2 rewrite idsubst_is_id_exp.
        }
        clear D0. do 2 econstructor.
        destruct lv.
        ** econstructor. congruence. reflexivity. simpl. eassumption.
        ** simpl. constructor. congruence.
           econstructor. inv P2. now inv H4.
           change clock to (1 + 2 * length lv + k).
           eapply step_term_term_plus.
           eapply params_eval_create. inv P2. now inv H4. reflexivity.
           cbn. eassumption.
(*   * deriv. apply term_eval in H0 as H0'.
    repeat destruct_hyps. eapply term_step_term in H0. 2: eassumption. 2: assumption.
    inv H.
    - inv H0. inv H8.
    - inv H0.
  * deriv. apply term_eval in H0 as H0'.
    repeat destruct_hyps. eapply term_step_term in H0. 2: eassumption. 2: assumption.
    inv H.
    - inv H0. inv H8.
    - inv H0. *)
Qed.

Theorem put_back_rev : forall F e Fs (P : EXPCLOSED e), FCLOSED F ->
  | Fs, plug_f F e | ↓ -> | F :: Fs, e | ↓.
Proof.
  destruct F; intros; simpl.
  all: try now (inv H0; cbn in *; inv_term; [eexists;eassumption | inv H0]).
  * inv H0. cbn in *. inv H1. inv H5. inv H3. eexists. eassumption. inv H0.
  * cbn. inv H0. destruct ident; simpl in H1.
    1-2, 5:
      inv_term; [
        destruct vl; inv_term;
         [eexists; eassumption
         |inv H8; eapply term_step_term in H3;[|apply params_eval]]; inv H; destruct_foralls; auto;
         eexists; eassumption
        |inv H0
      ].
    (* again, map, call and apply need special care: *)
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
             rewrite length_app, length_map. slia. }
           do 3 inv_term.
           eapply term_step_term in H7;[|apply params_eval].
           eexists; eassumption.
           now destruct_foralls.
    - inv_term. 2: inv H0. do 3 inv_term. destruct vl; inv_term.
      + inv_term. eexists. eassumption.
      + do 2 inv_term. eapply term_step_term in H5;[|apply params_eval].
        eexists. eassumption.
        inv H. now destruct_foralls.
    - inv_term. 2: inv H0. inv_term. destruct vl; inv_term.
      + inv_term. eexists. eassumption.
      + do 2 inv_term. eapply term_step_term in H4;[|apply params_eval].
        eexists. eassumption.
        inv H. now destruct_foralls.
  * simpl in *. inv H. destruct H0 as [k D]. inv_term. 2: { inv H. }
    do 2 inv_term. eexists. eassumption.
  * inv H0. cbn in *. inv H1. 2: inv H0. inv H5. inv H2. cbn in H7.
    inv H7; cbn in *; try invSome; invSome. simpl in H11; do 2 rewrite idsubst_is_id_exp in H11.
    rename H11 into H5.
    apply term_eval_both in H5 as T. destruct T as [res [l [Hres [D0 [D1 Hlia]]]]].
    eapply term_step_term in H5. 2: eassumption. 2: auto.
    clear D1. inv Hres.
    - inv H5. eexists. eapply frame_indep_nil in D0. eapply step_term_term_plus.
      eassumption. constructor. reflexivity. eassumption.
    - inv H5.
      + eapply frame_indep_nil in D0. eexists.
        eapply step_term_term_plus. eassumption.
        cbn in *. clear D0. eapply step_case_true. eassumption.
      + inv H2; inv H11. simpl in H12. inv H12. inv H5. inv H10. 2: inv_val.
        replace (map
       (fun '(p, x0, y) =>
        (p, x0.[upn (PatListScope p) idsubst],
         y.[upn (PatListScope p) idsubst])) le) with le in H7.
        replace (map (fun x0 : Exp => x0.[idsubst]) (map VVal lv)) with (map VVal lv) in H7.
        2: {
          clear. induction lv; auto. simpl. rewrite idsubst_is_id_val.
          now rewrite IHlv at 1.
        }
        2: {
          clear. induction le; auto. simpl. destruct a, p.
          rewrite idsubst_upn, <-IHle.
          now do 2 rewrite idsubst_is_id_exp.
        }
        destruct lv.
        ** inv H7. inv H5. cbn in H11. cbn in H8. invSome.
           eapply frame_indep_nil in D0. eexists.
           eapply step_term_term_plus. eassumption.
           eapply step_case_false. eassumption.
        ** inv H7. inv H5. inv H12. eapply term_step_term in H6.
           2: eapply params_eval_create. 2: { inv H. now inv H8. }
           2: { reflexivity. }
           simpl in H6.
           eapply frame_indep_nil in D0. eexists.
           eapply step_term_term_plus. eassumption.
           eapply step_case_false. eassumption.
(*   * simpl in H0. repeat deriv. (* receive is not evaluated at this level *)
  * simpl in H0. repeat deriv. (* receive is not evaluated at this level *) *)
Qed.
*)
