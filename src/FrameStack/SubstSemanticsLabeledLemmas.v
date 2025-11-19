(**
  This file contains numerous semantic properties about the frame stack semantics
  (labelled version) of Core Erlang.
*)
From CoreErlang.FrameStack Require Export
    LabeledTermination
    SubstSemanticsLabeled.
From stdpp Require Export list option.
Import ListNotations.

Lemma side_effect_ac_value : forall fs r fs' r' l0,
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
      {
        inversion H1. unfold eval_convert in H3.
        destruct (convert_string_to_code (s, s0)); try discriminate.
        * repeat (destruct vl; simpl in H3; try discriminate).
          destruct (mk_ascii_list v); try discriminate.
          inversion H3. exists (string_of_list_ascii l).
          reflexivity.
        * repeat (destruct vl; simpl in H3; try discriminate).
          destruct v; try discriminate.
          destruct l; discriminate.
      }
      {
        inversion H1. unfold eval_convert in H3.
        destruct (convert_string_to_code (s, s0)); try discriminate.
        * repeat (destruct vl; simpl in H3; try discriminate).
          destruct (mk_ascii_list v); try discriminate.
          inversion H3. exists (string_of_list_ascii l).
          reflexivity.
        * repeat (destruct vl; simpl in H3; try discriminate).
          destruct v; try discriminate.
          destruct l; discriminate.
      }
      1-3: destruct (eval_error s s0 vl); try discriminate.
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
        inversion H0. unfold eval_convert in H2.
        destruct (convert_string_to_code (s, s0)); try discriminate.
        - repeat (destruct vl; simpl in H2; try discriminate).
          destruct (mk_ascii_list v); try discriminate.
          inversion H2. exists (string_of_list_ascii l).
          reflexivity.
        - repeat (destruct vl; simpl in H2; try discriminate).
          destruct v; try discriminate.
          destruct l; discriminate.
      }
      {
        inversion H0. unfold eval_convert in H2.
        destruct (convert_string_to_code (s, s0)); try discriminate.
        - repeat (destruct vl; simpl in H2; try discriminate).
          destruct (mk_ascii_list v); try discriminate.
          inversion H2. exists (string_of_list_ascii l).
          reflexivity.
        - repeat (destruct vl; simpl in H2; try discriminate).
          destruct v; try discriminate.
          destruct l; discriminate.
      }
      1-3: destruct (eval_error s s0 (vl ++ [v])); try discriminate.
      all: destruct (eval_concurrent s s0 (vl ++ [v])); try discriminate.
    + unfold primop_eval in H0.
      destruct (convert_primop_to_code f); try discriminate.
      all: destruct (eval_primop_error f (vl ++ [v])); try discriminate.
    + destruct v0; try discriminate.
      destruct (params =? (length (vl ++ [v])))%nat; try discriminate.
Qed.

Theorem transitive_eval_labeled :
  forall {n e e'} l {fs fs'}, ⟨ fs, e ⟩ -[ n, l ]->ₗ ⟨ fs', e' ⟩ ->
  forall {n' e''} l' {fs''},  ⟨ fs', e' ⟩ -[ n', l' ]->ₗ ⟨ fs'', e'' ⟩
->
  ⟨ fs, e ⟩ -[ n + n', l ++ l' ]->ₗ ⟨ fs'', e'' ⟩.
Proof.
  intros n Fs Fs' l e e' IH.
  induction IH; intros; auto using app_nil_l.
  simpl. econstructor. exact H. apply IHIH. exact H1.
  destruct s; rewrite H0; auto.
Qed.

Corollary transitive_any_eval_labeled :
  forall {e e'} l {fs fs'}, ⟨ fs, e ⟩ -[ l ]->ₗ* ⟨ fs', e' ⟩ ->
  forall {e''} l' {fs''},  ⟨ fs', e' ⟩ -[ l' ]->ₗ* ⟨ fs'', e'' ⟩
->
  ⟨ fs, e ⟩ -[ l ++ l' ]->ₗ* ⟨ fs'', e'' ⟩.
Proof.
  intros. destruct H, H0. pose proof (transitive_eval_labeled _ H _ H0).
  unfold step_any_non_terminal. eexists. exact H1.
Qed.

Theorem step_determinism_labeled {e e' l fs fs'} :
  ⟨ fs, e ⟩ -⌊ l ⌋->ₗ ⟨ fs', e' ⟩ ->
  (forall {l' fs'' e''}, ⟨ fs, e ⟩ -⌊ l' ⌋->ₗ ⟨ fs'', e'' ⟩
  -> l = l' /\ fs'' = fs' /\ e'' = e').
Proof.
  intro H. inv H; intros; inv H; auto.
  - rewrite <- H1 in H9. now inv H9.
  - rewrite <- H0 in H8. now inv H8.
Qed.

Lemma value_nostep_labeled v :
  is_result v ->
  forall fs' v' l, ⟨[], v⟩ -⌊l⌋->ₗ ⟨fs' , v'⟩ -> False.
Proof.
  intros H fs' v' l' HD. inversion H; subst; inversion HD.
Qed.

Theorem step_rt_determinism_labeled {r r' fs fs' l k} :
  ⟨fs, r⟩ -[k, l]->ₗ ⟨fs', r'⟩
->
  (forall {fs'' r'' l''}, ⟨fs, r⟩ -[k, l'']->ₗ ⟨fs'', r''⟩ -> l = l'' /\ fs' = fs'' /\ r' = r'').
Proof.
  intro. induction H; intros.
  * inv H. firstorder.
  * inv H2.
    pose proof (step_determinism_labeled H H4) as [? [? ?]]. subst.
    specialize (IHstep_rt _ _ _ H5) as [? [? ?]]. subst.
    firstorder.
Qed.

Lemma create_result_closed :
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
    eapply eval_is_closed_result; try eassumption. eauto.
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

Theorem step_closedness_labeled : forall F e F' e' l,
   ⟨ F, e ⟩ -⌊l⌋->ₗ ⟨ F', e' ⟩ -> FSCLOSED F -> REDCLOSED e
->
  FSCLOSED F' /\ REDCLOSED e'.
Proof.
  intros F e F' e' l IH. induction IH; intros Hcl1 Hcl2;
  destruct_scopes; destruct_foralls; split; auto.
  all: cbn; try (repeat constructor; now auto).
  all: try now (apply indexed_to_forall in H1; do 2 (constructor; auto)).
  * do 2 (constructor; auto).
    apply Forall_app; auto.
  * eapply create_result_closed; eauto.
  * eapply create_result_closed. 3: eassumption. apply Forall_app; auto. auto.
  * do 2 (constructor; auto).
    epose proof (Forall_pair _ _ _ _ _ H0 H3).
    destruct_foralls. inv H4. constructor; auto.
    now apply flatten_keeps_prop.
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

Theorem step_any_closedness_labeled : forall Fs Fs' e v k l,
   ⟨ Fs, e ⟩ -[k , l]->ₗ ⟨Fs', v⟩ -> FSCLOSED Fs -> REDCLOSED e
->
  REDCLOSED v /\ FSCLOSED Fs'.
Proof.
  intros. induction H; auto. apply step_closedness_labeled in H. destruct H.
  apply (IHstep_rt ). all: auto.
Qed.

Corollary step_any_non_terminal_closedness : forall F e l F' e',
   ⟨ F, e ⟩ -[ l ]->ₗ* ⟨ F', e' ⟩ -> FSCLOSED F -> REDCLOSED e
-> REDCLOSED e' /\ FSCLOSED F'.
Proof.
  intros F e l F' e' H. induction H; intros. destruct H. auto.
  apply step_closedness_labeled in H. inv H.
  apply (step_any_closedness_labeled _ _ _ _ _ _ H2 H4 H5). all: assumption.
Qed.

Lemma transitive_eval_rev_labeled : forall Fs Fs' e e' k1 l1,
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
        destruct (step_determinism_labeled H H3).
        destruct H2. subst. assumption.
      * inv H7.
        destruct (step_determinism_labeled H H3).
        inv H2.
    + inv H2. destruct s.
      * inv H7.
        destruct (step_determinism_labeled H H3).
        inv H1.
      * inv H7. eapply IHstep_rt.
        destruct (step_determinism_labeled H H3).
        destruct H2. subst. assumption.
Qed.

Lemma frame_indep_step_labeled : forall e F F' Fs e' l,
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

Lemma frame_indep_red_labeled : forall e F Fs e' l,
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

Theorem frame_indep_core_labeled : forall k e Fs Fs' v l,
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

Corollary frame_indep_nil_labeled : forall k e Fs v l,
  ⟨ Fs, e ⟩ -[k , l]->ₗ ⟨ [], v ⟩
->
  forall Fs', ⟨ Fs ++ Fs', e ⟩ -[k , l]->ₗ ⟨ Fs', v ⟩.
Proof.
  intros. eapply frame_indep_core_labeled in H. exact H.
Qed.

Lemma params_eval_labeled :
  forall vals ident vl exps e Fs (v : Val),
  ⟨ FParams ident vl ((map VVal vals) ++ e :: exps) :: Fs, RValSeq [v]⟩ -[1 + 2 * length vals , []]->ₗ
  ⟨ FParams ident (vl ++ v :: vals) exps :: Fs, e⟩.
Proof.
  induction vals; simpl; intros.
  * econstructor. econstructor. constructor. simpl. auto.
  * specialize (IHvals ident (vl ++ [v]) exps e Fs a).
    econstructor. constructor.
    econstructor. constructor.
    rewrite <- app_assoc in IHvals.
    replace (length vals + S (length vals + 0)) with
            (1 + 2*length vals) by lia. apply IHvals.
    all: simpl; auto.
Qed.

Lemma params_eval_create :
  forall vals ident vl Fs (v : Val) r eff',
  Some (r, eff') = create_result ident (vl ++ v :: vals) ->
  ⟨ FParams ident vl (map VVal vals) :: Fs, RValSeq [v]⟩ -[1 + 2 * length vals, match eff' with
              | None => []
              | Some x => [x]
              end ]->ₗ
  ⟨ Fs, r ⟩.
Proof.
  induction vals; simpl; intros.
  * econstructor. econstructor. exact H. constructor.
    reflexivity.
  * specialize (IHvals ident (vl ++ [v]) Fs a). inv H.
    econstructor. constructor.
    econstructor. constructor; auto.
    rewrite <- app_assoc in IHvals.
    replace (length vals + S (length vals + 0)) with
            (1 + 2*length vals) by lia. eapply IHvals; eauto.
    reflexivity. reflexivity.
Qed.

Lemma terminates_in_k_step :
  forall fs e fs' e' k sl l, ⟨ fs, e ⟩ -⌊ l ⌋->ₗ ⟨ fs', e' ⟩ ->
  | fs', e' | sl – k ↓ ->
  | fs, e | (option_cons l sl) – S k ↓.
Proof.
  intros fs e fs' e' k sl l H. induction H.
  all: econstructor; eassumption.
Qed.

Theorem semantic_iff_termination :
  forall k e fs l, terminates_in_k_sem_labeled fs e k l <-> | fs, e | l – k ↓.
Proof.
  split.
  {
    revert e fs l. induction k; intros e fs l H.
    * destruct H as [res [Hres HD]].
      inversion HD; subst. now constructor.
    * destruct H as [res [Hres HD]].
      inversion HD; subst.
      assert (terminates_in_k_sem_labeled fs' e' k l0). {
        eexists. split; eassumption.
      }
      unfold terminates_in_k_sem_labeled in H.
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

Lemma terminates_step :
  forall n fs e l, | fs, e | l – n ↓ -> forall fs' e' l', ⟨fs, e⟩ -⌊l'⌋->ₗ ⟨fs', e'⟩
->
  | fs', e' | (option_tail l' l) – n - 1↓.
Proof.
  intros. apply semantic_iff_termination in H. destruct H. destruct n.
  * destruct H. inv H.
    - subst. inversion H1; subst. inversion H0.
    - subst. inversion H1; subst. inversion H0.
  * destruct H.
    inv H1. apply (step_determinism_labeled H0) in H3.
    inv H3. inv H2.
    assert (exists y, is_result y /\ ⟨ fs', e' ⟩ -[ n , l0 ]->ₗ ⟨ [], y ⟩). { 
      eexists. eauto. }
    apply ex_intro in H4. apply semantic_iff_termination in H1.
    destruct s; simpl; rewrite Nat.sub_0_r; assumption.
Qed.

Lemma term_step_term_no_skip :
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

Lemma term_step_term_labeled :
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

Lemma step_term_term_labeled :
  forall k n fs e fs' e' l1 l2,
  ⟨fs, e⟩ -[k , l1]->ₗ ⟨fs', e'⟩ -> | fs', e' | l2 – n - k ↓ -> n >= k 
->
  | fs, e | l1 ++ l2 – n ↓.
Proof.
  intros. apply semantic_iff_termination.
  apply semantic_iff_termination in H0. destruct H0, H0.
  pose proof (transitive_eval_labeled _ H _ H2). replace (k+(n-k)) with n in H3 by lia.
  eexists. eauto.
Qed.

Lemma step_term_term_plus_labeled :
  forall k k2 fs e fs' e' l1 l2, 
  ⟨fs, e⟩ -[k , l1]->ₗ ⟨fs', e'⟩ -> | fs', e' | l2 – k2 ↓
->
  | fs, e | l1 ++ l2 – k + k2 ↓.
Proof.
  intros. apply semantic_iff_termination.
  apply semantic_iff_termination in H0. destruct H0, H0.
  pose proof (transitive_eval_labeled _ H _ H1).
  eexists. eauto.
Qed.

Lemma create_result_is_not_box_closed :
  forall ident vl r eff',
  ICLOSED ident ->
  Forall (fun v => VALCLOSED v) vl ->
  Some (r, eff') = create_result ident vl ->
  REDCLOSED r.
Proof.
  destruct ident; intros; simpl in *; try invSome; auto.
  1: do 3 constructor. by apply indexed_to_forall.
  (* map *)
  1: do 3 constructor.
  1-2: erewrite <- length_map; apply indexed_to_forall.
  1-2: eapply List.Forall_map; apply make_val_map_keeps_prop.
  1-2: eapply Forall_impl; [|eapply deflatten_keeps_prop; eassumption].
  1-2: intros; destruct a; apply H1.
  (****)
  1: destruct m, f; try destruct l; try destruct l0; try invSome; try constructor; inv H; scope_solver.
  1: symmetry in H1; eapply eval_is_closed_result in H1; auto.
  * destruct (primop_eval f vl) eqn: pe.
    - inv H1. eapply primop_eval_is_closed_result; eassumption.
    - inv H1.
  * inv H. destruct v; try invSome; try now (constructor; auto).
    break_match_hyp; invSome; auto.
    all: constructor; auto.
    inv H3.
    apply -> subst_preserves_scope_exp; try eassumption.
    apply scoped_list_subscoped_eq. 3: auto.
    rewrite length_app.
    unfold convert_to_closlist. apply Nat.eqb_eq in Heqb. rewrite length_map. lia.
    {
      apply Forall_app.
      split; auto.
      now apply closlist_scope.
    }
Qed.

Lemma create_result_is_not_box :
  forall ident vl r eff',
  Some (r, eff') = create_result ident vl ->
  is_result r \/
  (exists e, r = RExp e).
Proof.
  destruct ident; intros; simpl in *; try invSome; auto.
  1: destruct m, f; try destruct l; try destruct l0; try invSome.
  all: try now (do 2 constructor).
  1: symmetry in H; eapply eval_is_result in H; auto.
  * symmetry in H. apply primop_eval_is_exception in H as [? ?].
    subst. left. destruct x as [[? ?] ?]; auto.
  * inv H. destruct v; try invSome; try now (do 2 constructor).
    break_match_hyp; invSome.
    - right. eexists. reflexivity.
    - left. constructor.
Qed.

Lemma Private_params_exp_eval :
  forall exps ident vl Fs (e : Exp) n (l : SideEffectList),
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
    eapply frame_indep_nil_labeled in Hd.
(*    specialize (H1 _ _ _ _ _ Hd).
    eapply H1 in H. *)
    eapply term_step_term_labeled in H. 2: exact Hd. simpl in *.
    inv Hres.
    - do 3 eexists. split. 2: split.
      2: {
        eapply transitive_eval_labeled. exact Hd.
        eapply step_trans. constructor. reflexivity. apply step_refl.
        reflexivity.
      }
      auto.
      inv H. lia.
    - destruct vs. 2: destruct vs. 1, 3: inv H. (* vs is a singleton *)
      inv H. destruct (create_result_is_not_box ident (vl ++ [v]) res l0); auto.
      + do 3 eexists. split. 2: split.
        2: {
          eapply transitive_eval_labeled. exact Hd.
          eapply step_trans. econstructor. eassumption. apply step_refl.
          reflexivity.
        }
        auto.
        lia.
      (* if create_result was a function application: *)
      + inv H. apply H0 in H8 as H8'.
        destruct H8' as [res2 [k2 [l2 [Hres2 [Hd2 Hlt2]]]]]. 2: lia.
        eapply frame_indep_nil_labeled in Hd2.
        eapply term_step_term_labeled in H8. 2: exact Hd2.
        do 3 eexists. split. 2: split.
        2: {
          eapply transitive_eval_labeled. exact Hd.
          eapply step_trans. econstructor. eassumption.
          exact Hd2. reflexivity.
        }
        auto.
        lia.
  * (* same as above *)
    apply H0 in H as H'. 2: lia.
    destruct H' as [res [k [ll [Hres [Hd Hlt]]]]].
    eapply frame_indep_nil_labeled in Hd.
    eapply term_step_term_labeled in H. 2: exact Hd. simpl in *.
    inv Hres.
    - do 3 eexists. split. 2: split.
      2: {
        eapply transitive_eval_labeled. exact Hd.
        eapply step_trans. constructor. reflexivity. apply step_refl.
        reflexivity.
      }
      auto.
      inv H. lia.
    (* up to this point*)
    - destruct vs. 2: destruct vs. 1, 3: inv H.
      inv H. apply IHexps in H8 as [res2 [k2 [l2 [Hres2 [Hd2 Hlt2]]]]].
      2: {
        intros. eapply H0. lia. eassumption.
      }
      do 3 eexists. split. 2: split.
      2: {
        eapply transitive_eval_labeled. exact Hd.
        eapply step_trans. constructor. exact Hd2.
        reflexivity.
      }
      auto.
      lia.
Qed.

(* TODO: move this to Basics.v *)
Proposition prefix_drop : forall {A} (l0 l1 : list A) ,
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
  forall exps ident vl Fs (e : Exp) n l,
  | FParams ident vl exps :: Fs, e | l – n ↓ ->
  (forall m : nat,
  m < S n ->
  forall (Fs : FrameStack) (e : Exp) (l : SideEffectList),
  | Fs, e | l – m ↓ ->
  exists (res : Redex) (k : nat) (l' : SideEffectList),
    is_result res /\ ⟨ [], e ⟩ -[ k , l' ]->ₗ ⟨ [], res ⟩ /\ k <= m /\ l' `prefix_of` l) ->
  exists res k l', is_result res /\
  ⟨ [FParams ident vl exps], e⟩ -[k , l']->ₗ
  ⟨ [], res ⟩ /\ k <= n /\ l' `prefix_of` l.
Proof.
  induction exps; intros.
  * apply H0 in H as H'. 2: lia.
    destruct H' as [res [k [l' [Hres [Hd [Hlt Hpref]]]]]].
    eapply frame_indep_nil_labeled in Hd as Hlia.
    eapply frame_indep_nil_labeled in Hd.
    eapply term_step_term_labeled in H as Hlia2. 2: exact Hlia. simpl in *.
    inv Hres.
    - do 3 eexists. split. 2: split. 3: split.
      2: {
        eapply transitive_eval_labeled. exact Hd.
        eapply step_trans. constructor. reflexivity. apply step_refl.
        reflexivity.
      }
      auto.
      inv Hlia2. lia.
      rewrite app_nil_r. assumption.
    - destruct vs. 2: destruct vs. 1, 3: inv Hlia2. (* vs is a singleton *)
      inv Hlia2. destruct (create_result_is_not_box ident (vl ++ [v]) res l0).
      + auto.
      + do 3 eexists. split. 2: split. 3: split.
        2: {
          eapply transitive_eval_labeled. exact Hd.
          eapply step_trans. econstructor. eassumption. apply step_refl.
          reflexivity.
        }
        auto.
        lia.
        unfold option_cons in *.
        destruct l0. 2: rewrite app_nil_r; assumption.
        rewrite (prefix_drop _ _ Hpref _ H6).
        rewrite (cons_middle s l' ls). rewrite app_assoc.
        apply prefix_app_r. auto.
      (* if create_result was a function application: *)
      + inv H1. apply H0 in H8 as H8'. 2: lia.
        destruct H8' as [res2 [k2 [l2 [Hres2 [Hd2 [Hlt2 Hpref2]]]]]].
        eapply frame_indep_nil_labeled in Hd2 as Hlia3.
        eapply frame_indep_nil_labeled in Hd2.
        eapply term_step_term_labeled in H8. 2: exact Hlia3.
        do 3 eexists. split. 2: split. 3: split.
        2: {
          eapply transitive_eval_labeled. exact Hd.
          eapply step_trans. econstructor. eassumption.
          exact Hd2. reflexivity.
        }
        auto.
        lia. subst.
        unfold option_cons in *.
        destruct l0; rewrite (prefix_drop _ _ Hpref _ H6).
        ** do 2 rewrite cons_middle.
           apply prefix_app.
           apply prefix_app.
           assumption.
        ** apply prefix_app.
           assumption.
  * (* same as above *)
    apply H0 in H as H'. 2: lia.
    destruct H' as [res [k [l' [Hres [Hd Hlt]]]]].
    eapply frame_indep_nil_labeled in Hd as Hlia.
    eapply frame_indep_nil_labeled in Hd.
    eapply term_step_term_labeled in H as Hlia2. 2: exact Hlia. simpl in *.
    inv Hres.
    - do 3 eexists. split. 2: split. 3: split.
      2: {
        eapply transitive_eval_labeled. exact Hd.
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
      inv Hlia2.
      apply IHexps in H8 as [res2 [k2 [l2 [Hres2 [Hd2 Hlt2]]]]]; auto.
      2: {
        intros. eapply H0. lia. eassumption.
      }
      do 3 eexists. split. 2: split. 3: split.
      2: {
        eapply transitive_eval_labeled. exact Hd.
        eapply step_trans. constructor.
        exact Hd2.
        reflexivity.
      }
      auto.
      lia.
      auto.
      destruct Hlt2. destruct Hlt.
      rewrite (prefix_drop _ _ H4 _ eq_refl).
      apply prefix_app.
      rewrite (prefix_drop _ _ H2 _ eq_refl).
      apply prefix_app_r.
      by auto.
Qed.

Lemma Private_term_empty_case l:
  forall Fs (vs : ValSeq) n (ls : SideEffectList),
  (forall (m : nat) ,
  m < n ->
  forall (Fs : FrameStack) (e : Exp) (lss : SideEffectList),
  | Fs, e | lss – m ↓ -> exists (k : nat) (lsss : SideEffectList) , (| [], e | lsss – k ↓) /\ k <= m 
      /\ lsss `prefix_of` lss )-> 
  | FCase1 l :: Fs, vs | ls – n ↓ -> (* this has to be value sequence, because 
                                   in case of not matching patterns, only
                                   this is usable *)
  exists res k l1, is_result res /\
  ⟨ [FCase1 l ], vs⟩ -[k , l1]->ₗ
  ⟨ [], res ⟩ /\ k <= n /\
  l1 `prefix_of` ls.
Proof.
  induction l; intros Fs vs n ls IH HD.
  * (* empty case *) inv HD. eexists. exists 1. eexists.
    split. 2: split. 2: econstructor; constructor.
    constructor; constructor. split. lia. apply prefix_nil.
  * inv HD.
    - (* matching first pattern *)
      apply IH in H6 as HH. 2: lia. destruct HH as [i [li [Hdgr [Hlt Hprefi]]]].
      apply semantic_iff_termination in Hdgr as [gr [Hgr Hdgr]]. (* guard result *)
      eapply frame_indep_nil_labeled in Hdgr as Hlia.
      eapply frame_indep_nil_labeled in Hdgr.
      eapply term_step_term_labeled in H6.
      2: exact Hlia. simpl in *. inv Hgr.
      + (* guard is an exception *) inv H6.
        exists (RExc (cl, v1, v2)), (1 + (i + 1)). eexists. split; auto. split.
        2: split. 2: lia.
        econstructor. constructor. exact H5. eapply transitive_eval_labeled.
        exact Hdgr. econstructor. constructor. congruence. constructor.
        1-2: reflexivity. rewrite <- app_nil_r. do 2 rewrite app_nil_r. assumption.
      + inv H6.
        ** (* guard is true *)
           apply IH in H7 as HH. 2: lia.
           destruct HH as [j [lj [Hdcl [Hlt2 Hprefj]]]].
           apply semantic_iff_termination in Hdcl as [clr [Hclr Hdcl]]. (* clause result *)
           eapply frame_indep_nil_labeled in Hdcl. simpl in *.
           assert (⟨ [FCase2 vs e2.[list_subst vs' idsubst] l], RValSeq [VLit "true"%string] ⟩ -[1 , []]->ₗ
           ⟨ [], e2.[list_subst vs' idsubst] ⟩). {
             econstructor. constructor. constructor.
             reflexivity.
           }
           epose proof (transitive_eval_labeled _ Hdgr _ H).
           epose proof (transitive_eval_labeled _ H0 _ Hdcl).
           exists clr, (1 + (i + 1 + j)). eexists. split; auto.
           split. 2: split. 2: lia.
           econstructor. apply eval_step_case_match; eassumption.
           eassumption. reflexivity. rewrite app_nil_r. destruct Hprefi. subst.
           apply prefix_app. rewrite drop_app_length in Hprefj. assumption.
        ** (* guard is false *)
           apply IHl in H7 as [res [j [ls2 [Hres [HD [Htl Hpref]]]]]]; auto.
           2: {
             intros. eapply IH. lia. eassumption.
           }
           exists res, (1 + (i + S j)). eexists. split. 2: split. auto. 2: split. 2: lia.
           econstructor. apply eval_step_case_match. eassumption.
           eapply transitive_eval_labeled. exact Hdgr.
           econstructor. constructor. exact HD. reflexivity. reflexivity.
           destruct Hprefi. subst.
           apply prefix_app. rewrite drop_app_length in Hpref. assumption.
    - (* not matching first pattern *)
      apply IHl in H6 as [res [j [Hres [HD [Htl [Hlt Hpref]]]]]]; auto.
      2: {
        intros. eapply IH. lia. exact H0.
      }
      exists res, (1 + j). eexists. split. 2: split. auto. 2: split. 2: lia.
      econstructor. now apply eval_step_case_not_match. exact Htl.
      reflexivity. assumption.
Qed.

Theorem term_empty_labeled : forall x Fs (e : Exp) (l : SideEffectList),
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
      2: {
        intros. epose proof (H m ltac:(slia) Fs0 e0 _ H1) as [j [l' [HD [Hj Hpref]]]].
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
      congruence. reflexivity. do 4 constructor; auto. intros. inv H3.
      split. lia. apply prefix_nil.
    - inv H3. destruct_scopes.
      eapply Private_params_exp_eval_empty in H9 as HH2; auto.
      2: {
        intros. epose proof (H m ltac:(slia) Fs0 e0 _ H1) as [j [l' [HD [Hj Hpref]]]].
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
    2: {
      intros. epose proof (H m ltac:(slia) Fs0 e _ H1) as [j [l' [HD [Hj Hpref]]]].
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
    eapply frame_indep_nil_labeled in Hr1 as Hr1'.
    eapply frame_indep_nil_labeled in Hr1.
    eapply term_step_term_labeled in H3.
    2: exact Hr1. simpl in *.
    inv Hres1.
    (* moduleexp Exception *)
    - inv H3. do 2 eexists. split. constructor.
      eapply step_term_term_plus_labeled. exact Hr1'. constructor.
      congruence. constructor. constructor; auto. split. lia.
      rewrite app_nil_r. assumption.
    (* moduleexp Value *)
    - inv H3.
      apply H in H6 as HD2; auto. 2: lia.
      destruct HD2 as [k2 [l2 [D2 [Hlia2 Hpref2]]]].
      apply semantic_iff_termination in D2 as [res2 [Hres2 Hr2]].
      eapply frame_indep_nil_labeled in Hr2 as Hr2'.
      eapply frame_indep_nil_labeled in Hr2.
      eapply term_step_term_labeled in H6.
      2: exact Hr2. simpl in *.
      inv Hres2.
      (* funexp exception *)
      + inv H6. do 2 eexists. split. constructor.
        eapply step_term_term_plus_labeled. exact Hr1'. constructor.
        eapply step_term_term_plus_labeled. exact Hr2'. constructor.
        congruence. constructor. constructor; auto. split. lia.
        rewrite app_nil_r. destruct Hpref2. symmetry in H0.
        epose proof (prefix_drop l1 l Hpref (l2 ++ x) H0).
        rewrite H1. apply prefix_app. rewrite <- app_nil_r at 1.
        apply prefix_app. apply prefix_nil.
      (* moduleexp value *)
      + inv H6. destruct el. (* tricks to avoid RBox *)
        ** inv H5. do 2 eexists. split.
           constructor.
           eapply step_term_term_plus_labeled. exact Hr1'. constructor.
           eapply step_term_term_plus_labeled. exact Hr2'. constructor.
           epose proof (cool_params_0_l [] (ICall v f0) [] _ l0 []). simpl in H0.
           apply H0.
           congruence. exact H6.
           (* here is this different from the previous *)
           simpl in H6.
           destruct v, f0; try destruct l; try destruct l0; try destruct l3; try invSome; try constructor; auto.
           all: try (constructor; constructor; apply indexed_to_forall);
             try (constructor; [|constructor]; auto).
           -- destruct l4.
              ++ eapply eval_is_result; eauto.
              ++ invSome.
           -- destruct l4 eqn: a.
              ++ eapply eval_is_result; eauto.
              ++ invSome. unfold badfun.
                 eapply exception_is_result.
           -- destruct l4.
              ++ eapply eval_is_result; eauto.
              ++ invSome.
           -- destruct l4.
              ++ eapply eval_is_result; eauto.
              ++ invSome.
                 eapply exception_is_result.
           -- split. lia. destruct l0; simpl in H3; simpl.
              ++ destruct Hpref2. rewrite H0 in H3.
                 symmetry in H0.
                 epose proof (prefix_drop _ _ Hpref _ H0). rewrite H1.
                 apply prefix_app. apply prefix_app.
                 rewrite drop_app_length in H3.
                 rewrite <- H3.
                 apply prefix_cons. apply prefix_nil.
              ++ destruct Hpref2. rewrite H0 in H3.
                 symmetry in H0.
                 epose proof (prefix_drop _ _ Hpref _ H0). rewrite H1.
                 apply prefix_app. apply prefix_app. apply prefix_nil.
        ** inv H5.
           eapply Private_params_exp_eval_empty in H11 as HD3; auto.
           2: {
             intros. epose proof (H m0 ltac:(slia) Fs0 e0 _ H1) as [j [ls [HD [Hj Hpref3]]]].
             apply semantic_iff_termination in HD as [res [Hres Hr]].
             do 3 eexists. split. 2: split. 3: split. all: eassumption.
           }
           destruct HD3 as [res3 [k3 [l3 [Hres3 [Hd3 [Hlt3 Hpref3]]]]]].
           do 2 eexists. split. 2: split.
           constructor.
           eapply step_term_term_plus_labeled. exact Hr1'. constructor.
           eapply step_term_term_plus_labeled. exact Hr2'. constructor.
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
      destruct p. inv H5. eapply primop_eval_is_exception with (f:=f) in pe as []. subst. destruct x as [[] ?]. eauto.
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
      2: {
        intros. epose proof (H m ltac:(slia) Fs0 e0 _ H1) as [j [l1 [HD [Hj Hpref]]]].
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
    eapply frame_indep_nil_labeled in Hr as Hlia1.
    eapply frame_indep_nil_labeled in Hr. eapply term_step_term_labeled in H3.
    2: exact Hlia1. simpl in *.
    destruct l0. (* tricks to avoid RBox *)
    - inv Hres. (* exception result? *)
      + exists (2 + j). eexists. split. constructor.
        eapply step_term_term_labeled. simpl. exact Hr. 2: lia.
        replace (S j - j) with 1 by lia.
        constructor. reflexivity. constructor. auto.
        inv H3. split. lia.
        rewrite app_nil_r. assumption.
      + 
        inv H3. inv H5.
        destruct (create_result_is_not_box (IApp v) [] res l0).
        ** assumption.
        ** exists (3 + j). eexists. split. constructor.
           eapply step_term_term_labeled. exact Hr. 2: lia.
           replace (S (S j) - j) with 2 by lia.
           constructor. econstructor. congruence. eassumption.
           now constructor.
           split. lia.
           destruct Hpref. subst. apply prefix_app.
           rewrite drop_app_length in H3. rewrite <- H3.
           destruct l0; simpl.
           assert (s :: ls = [s] ++ ls). {
             simpl. reflexivity.
           } rewrite H1. rewrite <- app_nil_r at 1.
           apply prefix_app. apply prefix_nil.
           apply prefix_nil.
        ** inv H0. apply H in H9 as H9'. 2: lia.
           destruct H9' as [i [l2 [Hd2 [Hlt2 Hpref2]]]].
           exists (1 + (j + 2 + i)). eexists. split. constructor.
           eapply step_term_term_labeled. exact Hr. 2: lia.
           replace (j + 2 + i - j) with (2 + i) by lia.
           constructor. econstructor. congruence. eassumption. exact Hd2.
           split. lia. destruct Hpref. subst. rewrite drop_app_length in H3.
           apply prefix_app. destruct Hpref2. destruct l0; simpl in *.
           assert (s :: l2 = [s] ++ l2). {
             simpl. reflexivity.
           } rewrite <- H3. rewrite H0. rewrite app_comm_cons. repeat rewrite H1.
           rewrite <- app_nil_r at 1. apply prefix_app. apply prefix_nil.
           rewrite <- H3. rewrite H0.
           rewrite <- app_nil_r at 1. apply prefix_app. apply prefix_nil.
    - inv Hres.
      + exists (2 + j). eexists. split. constructor.
        eapply step_term_term_labeled. exact Hr. 2: lia.
        replace (S j - j) with 1 by lia.
        constructor. reflexivity. constructor. auto.
        inv H3. split. lia. rewrite app_nil_r. assumption.
      + inv H3. inv H5. destruct_scopes.
        eapply Private_params_exp_eval_empty in H10 as HH2; auto.
        2: {
          intros. epose proof (H m ltac:(slia) Fs0 e1 _ H1) 
            as [i [l3 [Hd2 [Hi Hpref2]]]].
          apply semantic_iff_termination in Hd2
             as [res2 [Hres2 Hr2]].
          do 3 eexists. split. 2: split. 3: split. all: eassumption.
        }
        destruct HH2 as [res2 [i [l2 [Hres2 [Hd2 [Hlt2 Hpref2]]]]]].
        assert (⟨ [FApp1 (e :: l0)], RValSeq [v]⟩ -[2 , []]->ₗ ⟨ [FParams (IApp v) [] l0], e ⟩). {
          repeat econstructor. congruence.
        }
        eapply (transitive_eval_labeled _ Hr) in H0.
        eapply (transitive_eval_labeled _ H0) in Hd2.
        do 2 eexists. split.
        constructor. apply semantic_iff_termination.
        eexists. split. 2: exact Hd2. assumption. split. lia.
        rewrite app_nil_r in *.
        destruct Hpref. subst. apply prefix_app.
        rewrite drop_app_length in Hpref2. assumption.
  * apply H in H3 as HH. 2: lia.
    destruct HH as [i [li [Hi [Hlt Hprefi]]]].
    apply semantic_iff_termination in Hi as [res [Hres Hr]].
    eapply frame_indep_nil_labeled in Hr as Hlia1.
    eapply frame_indep_nil_labeled in Hr.
    eapply term_step_term_labeled in H3. 2: exact Hlia1.
    inv Hres. (* tail exception or not *)
    - exists (S i + 1). eexists.
      split. 2: split. 2: inv H3; lia.
      simpl. constructor. apply semantic_iff_termination.
      exists (RExc (cl, v1, v2)). split; auto. eapply transitive_eval_labeled.
      exact Hr. do 2 econstructor. reflexivity.
      rewrite app_nil_r. assumption.
    - inv H3. apply H in H5 as HH. 2: lia.
      destruct HH as [j [lj [Hj [Hltj Hprefj]]]].
      simpl in *. apply semantic_iff_termination in Hj as [hdres [Hr2 Hd2]].
      eapply frame_indep_nil_labeled in Hd2 as Hlia2.
      eapply frame_indep_nil_labeled in Hd2.
      eapply term_step_term_labeled in H5. 2: exact Hlia2.
      assert (⟨ [FCons1 hd], RValSeq [tl0] ⟩ -[1 , []]->ₗ ⟨[FCons2 tl0], hd⟩). {
        repeat econstructor.
      }
      eapply (transitive_eval_labeled _ Hr) in H0.
      eapply (transitive_eval_labeled _ H0) in Hd2.
      inv Hr2. (* head exception or not *)
      + exists (1 + (i + (1 + (j + 1) ))). eexists. split.
        simpl. constructor. eapply step_term_term_labeled.
        exact Hd2.
        replace (i + S (j + 1) - (i + 1 + j)) with 1 by lia.
        constructor. reflexivity. do 2 constructor; auto.
        lia. split.
        inv H5. simpl. lia.
        repeat (rewrite app_nil_r).
        destruct Hprefi. rewrite H1 in *. apply prefix_app.
        destruct Hprefj. rewrite drop_app_length in H2. rewrite H2.
        rewrite <- app_nil_r at 1. apply prefix_app. apply prefix_nil.
      + exists (1 + (i + (1 + (j + 1) ))). eexists. split.
        simpl. constructor. eapply step_term_term_labeled.
        exact Hd2. inv H5.
        replace (i + S (j + 1) - (i + 1 + j)) with 1 by lia.
        destruct_foralls.
        constructor. do 4 constructor.
        lia. split. inv H5. lia. do 2 rewrite app_nil_r.
        destruct Hprefi. subst. apply prefix_app. rewrite drop_app_length in Hprefj.
        assumption.
  * apply H in H3 as HH. 2: lia.
    destruct HH as [i [li [Hi [Hlt Hprefi]]]].
    apply semantic_iff_termination in Hi as [res [Hres Hr]].
    eapply frame_indep_nil_labeled in Hr as Hlia1.
    eapply frame_indep_nil_labeled in Hr.
    eapply term_step_term_labeled in H3. 2: exact Hlia1.
    inv Hres. (* tail exception or not *)
    - exists (S i + 1). eexists.
      split. 2: split. 2: inv H3; lia.
      simpl. constructor. apply semantic_iff_termination.
      exists (RExc (cl, v1, v2)). split; auto. eapply transitive_eval_labeled.
      exact Hr. do 2 econstructor. reflexivity.
      rewrite app_nil_r. assumption.
    - inv H3. apply H in H8 as HH. 2: lia.
      destruct HH as [j [lj [Hj [Hltj Hprefj]]]].
      simpl in *. apply semantic_iff_termination in Hj as [hdres [Hr2 Hd2]].
      eapply frame_indep_nil_labeled in Hd2 as Hlia2.
      eapply term_step_term_labeled in H8. 2: exact Hlia2.
      assert (⟨ [FLet (Datatypes.length vs) e2], RValSeq vs ⟩ -[1, []]->ₗ 
      ⟨ [], e2.[list_subst vs idsubst] ⟩). {
        repeat econstructor.
      }
      eapply (transitive_eval_labeled _ Hr) in H0.
      eapply (transitive_eval_labeled _ H0) in Hd2.
      exists (1 + (i + (1 + j))). eexists. split. 2: split. 2: inv Hr2; inv H0; lia.
      constructor. eapply step_term_term_labeled. exact Hd2.
      replace (i + (1 + j) - (i + 1 + j)) with 0 by lia.
      now constructor.
      lia.
      repeat (rewrite app_nil_r).
      destruct Hprefi. rewrite H1 in *. apply prefix_app.
      destruct Hprefj. rewrite drop_app_length in H2. rewrite H2.
      rewrite <- app_nil_r at 1. apply prefix_app. apply prefix_nil.
  (* Sequencing is basically same as let *)
  * apply H in H3 as HH. 2: lia.
    destruct HH as [i [li [Hi [Hlt Hprefi]]]].
    apply semantic_iff_termination in Hi as [res [Hres Hr]].
    eapply frame_indep_nil_labeled in Hr as Hlia1.
    eapply frame_indep_nil_labeled in Hr.
    eapply term_step_term_labeled in H3. 2: exact Hlia1.
    inv Hres. (* tail exception or not *)
    - exists (S i + 1). eexists.
      split. 2: split. 2: inv H3; lia.
      simpl. constructor. apply semantic_iff_termination.
      exists (RExc (cl, v1, v2)). split; auto. eapply transitive_eval_labeled.
      exact Hr. do 2 econstructor. reflexivity.
      rewrite app_nil_r. assumption.
    - inv H3. apply H in H5 as HH. 2: lia.
      destruct HH as [j [lj [Hj [Hltj Hprefj]]]].
      simpl in *. apply semantic_iff_termination in Hj as [hdres [Hr2 Hd2]].
      eapply frame_indep_nil_labeled in Hd2 as Hlia2.
      eapply term_step_term_labeled in H5. 2: exact Hlia2.
      assert (⟨ [FSeq e2], RValSeq [v] ⟩ -[1 , []]->ₗ
      ⟨ [], e2 ⟩). {
        repeat econstructor.
      }
      eapply (transitive_eval_labeled _ Hr) in H0.
      eapply (transitive_eval_labeled _ H0) in Hd2.
      exists (1 + (i + (1 + j))). eexists. split. 2: split. 2: inv Hr2; inv H0; lia.
      constructor. eapply step_term_term_labeled. exact Hd2.
      replace (i + (1 + j) - (i + 1 + j)) with 0 by lia.
      now constructor.
      lia.
      repeat (rewrite app_nil_r).
      destruct Hprefi. rewrite H1 in *. apply prefix_app.
      destruct Hprefj. rewrite drop_app_length in H2. rewrite H2.
      rewrite <- app_nil_r at 1. apply prefix_app. apply prefix_nil.
  * do 2 eexists. split. constructor. do 3 constructor; auto.
    destruct_scopes. constructor; intros. lia.
    apply prefix_nil.
  (* for case: list_length_ind on H3 (or structural could also be enough) *)
  * apply H in H3 as HH. 2: lia. destruct HH as [k1 [l1 [Hd1 [Hlt1 Hpref1]]]].
    apply semantic_iff_termination in Hd1 as [r1 [Hr Hd]].
    eapply frame_indep_nil_labeled in Hd as Hlia1.
    eapply frame_indep_nil_labeled in Hd.
    eapply term_step_term_labeled in H3. 2: exact Hlia1.
    simpl in *.
    inv Hr. (* exception? *)
    + exists (1 + k1 + 1). eexists. split. 2: split. 2: inv H3; lia.
      simpl. constructor. eapply step_term_term_labeled. exact Hd.
      replace (k1 + 1 - k1) with 1 by lia.
      constructor. reflexivity. do 2 constructor; auto. lia.
      rewrite app_nil_r. assumption.
    + epose proof (Private_term_empty_case _ _ _ _ _ _ H3) as
        [res [k2 [l2 [Hres [Hd2 [Hlt2 Hpref2]]]]]].
      Unshelve. 2: {
        intros. eapply H. lia. eassumption.
      }
      pose proof (transitive_eval_labeled _ Hd _ Hd2).
      exists (S (k1 + k2)). eexists. split. 2: split. 2: lia.
      constructor.
      apply semantic_iff_termination. exists res. split. 2: exact H0.
      all: auto.
      destruct Hpref1. subst. apply prefix_app. rewrite drop_app_length in *. assumption.
  * apply H in H4 as [i [li [Hd [Hlt Hpref]]]].
    do 2 eexists. split. econstructor. reflexivity. exact Hd. split. lia. assumption. lia.
  * apply H in H3 as HH. 2: lia.
    destruct HH as [i [li [Hd [Hlt Hpref]]]].
    apply semantic_iff_termination in Hd as [r [Hres Hd]].
    eapply frame_indep_nil_labeled in Hd as Hlia.
    eapply frame_indep_nil_labeled in Hd.
    eapply term_step_term_labeled in H3. 2: exact Hlia.
    simpl in *.
    inv Hres. (* exception or not *)
    - inv H3. (* 2: { inv H7. } *)
      apply H in H10 as [j [l2 [Hd2 [Hlt2 Hpref2]]]]. 2: lia.
      exists (1 + (i + (1 + j))). eexists. split. 2: split. 2: lia.
      constructor. eapply step_term_term_labeled. exact Hd. 2: lia.
      replace (i + (1 + j) - i) with (S j) by lia.
      2: { destruct Hpref. subst. rewrite drop_app_length in Hpref2.
           apply prefix_app. exact Hpref2.
      }
      now constructor.
    - inv H3.
      apply H in H10 as [j [l2 [Hd2 [Hlt2 Hpref2]]]]. 2: lia.
      exists (1 + (i + (1 + j))). eexists. split. 2: split. 2: lia.
      constructor. eapply step_term_term_labeled. exact Hd. 2: lia.
      replace (i + (1 + j) - i) with (S j) by lia.
      2: { destruct Hpref. subst. rewrite drop_app_length in Hpref2.
           apply prefix_app. exact Hpref2.
      }
      now constructor.
  * do 2 eexists. split. now constructor. split. lia. apply prefix_nil.
Qed.

(* NOTE: This is not a duplicate! Do not remove! *)
(* sufficient to prove it for Exp, since value sequences and
   exceptions terminate in 0/1 step by definition in the
   empty stack (and RBox does not terminate!). *)
Corollary term_eval_empty_labeled : forall x Fs (e : Exp) (ls : SideEffectList) ,
  | Fs, e | ls – x ↓ ->
  exists res k lss ,
    is_result res /\
    ⟨ [], e ⟩ -[k , lss]->ₗ ⟨ [], res ⟩ /\
    k <= x /\
    lss `prefix_of` ls.
Proof.
  intros. apply term_empty_labeled in H; auto. destruct H as [k [lss [H Hlt]]].
  apply semantic_iff_termination in H as [r [Hr H]].
  do 3 eexists; eauto.
Qed.

Corollary term_eval_labeled : forall x Fs (e : Exp) (ls : SideEffectList) ,
  | Fs, e | ls – x ↓ ->
  exists v k lss,
    is_result v /\
    ⟨ Fs, e ⟩ -[k , lss]->ₗ ⟨ Fs, v ⟩ /\
    k <= x /\
    lss `prefix_of` ls
    .
Proof.
  intros.
  apply term_eval_empty_labeled in H as [r [k [lss [Hr [Hd Hlt]]]]].
  exists r, k, lss. intuition.
  eapply frame_indep_nil_labeled in Hd. exact Hd.
Qed.

Corollary term_eval_both_labeled :
  forall x Fs (e : Exp) (l : SideEffectList) , 
  | Fs, e | l – x ↓ ->
  exists v k ls, is_result v /\
  ⟨ [], e ⟩ -[k , ls]->ₗ ⟨ [], v ⟩ /\
  ⟨ Fs, e ⟩ -[k , ls]->ₗ ⟨ Fs, v ⟩ /\
  k <= x /\
  ls `prefix_of` l.
Proof.
  intros. apply term_eval_empty_labeled in H as [r [k [ls [Hr [Hd [Hlt Hpref]]]]]].
  exists r, k, ls. intuition.
  eapply frame_indep_nil_labeled in Hd. exact Hd.
Qed.

Lemma to_Exp_eval_labeled :
  forall (vals : list Val) (exp : Exp) (exps : list Exp) ident Fs,
   (ident = IMap -> exists n, length exps + length vals = 1 + 2*n) -> (* invariant for maps *)
   exists k, ⟨Fs, to_Exp ident (map VVal vals ++ exp :: exps)⟩ -[k, []]->ₗ ⟨ FParams ident vals exps :: Fs, exp ⟩.
Proof.
  (* these subproofs are the same almost for most lang. elements
     except for the number of initialisation steps *)
  intros. destruct ident.
  * destruct vals; simpl.
    - eexists. econstructor. constructor.
      econstructor. constructor. congruence.
      constructor.
      all: reflexivity.
    - eexists. econstructor. constructor.
      econstructor. constructor. congruence.
      econstructor. constructor.
      apply params_eval_labeled.
      all: reflexivity.
  * destruct vals; simpl.
    - eexists. econstructor. constructor.
      econstructor. constructor. congruence.
      constructor.
      all: reflexivity.
    - eexists. econstructor. constructor.
      econstructor. constructor. congruence.
      econstructor. constructor.
      apply params_eval_labeled.
      all: reflexivity.
  (* maps require special attention *)
  * destruct vals; simpl.
    - destruct exps.
      + specialize (H eq_refl) as [n H]. simpl in H. lia.
      + specialize (H eq_refl) as [n H]. simpl in H.
        eexists. econstructor. constructor.
        rewrite deflatten_flatten with (n := n). 2: lia.
        constructor.
        all: reflexivity.
    - destruct vals.
      + simpl. specialize (H eq_refl) as [n H].
        eexists. econstructor. constructor.
        econstructor. constructor.
        econstructor. constructor.
        simpl in H.
        rewrite deflatten_flatten with (n := n). 2: lia.
        constructor.
        all: reflexivity.
      + simpl. specialize (H eq_refl) as [n H].
        eexists. econstructor. constructor.
        econstructor. constructor.
        econstructor. constructor.
        econstructor. constructor.
        simpl in H.
        rewrite deflatten_flatten with (n := n).
        2: rewrite length_app, length_map; slia.
        apply params_eval_labeled.
        all: reflexivity.
  (***)
  * destruct vals; simpl.
    - eexists. econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor. congruence.
      constructor.
      all: reflexivity.
    - eexists. econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor. congruence.
      econstructor. constructor.
      apply params_eval_labeled.
      all: reflexivity.
  * destruct vals; simpl.
    - eexists. econstructor. constructor.
      econstructor. constructor. congruence.
      constructor.
      all: reflexivity.
    - eexists. econstructor. constructor.
      econstructor. constructor. congruence.
      econstructor. constructor.
      apply params_eval_labeled.
      all: reflexivity.
  * destruct vals; simpl.
    - eexists. econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor. congruence.
      constructor.
      all: reflexivity.
    - eexists. econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor. congruence.
      econstructor. constructor.
      apply params_eval_labeled.
      all: reflexivity.
Qed.

Corollary params_eval_VValues_labeled :
 forall (vals : list Val) (Fs : list Frame),
 ⟨ Fs, °EValues (map VVal vals)⟩ -[
   2 + 2 * base.length vals, [] ]->ₗ ⟨ Fs, RValSeq vals ⟩.
Proof.
  intros. destruct vals.
  * simpl. econstructor. constructor.
    econstructor. econstructor. congruence. reflexivity.
    constructor. all: reflexivity.
  * simpl. econstructor. constructor.
    econstructor. constructor. congruence.
    econstructor. constructor.
    pose proof params_eval_create vals IValues [] Fs v (RValSeq (v::vals)) None eq_refl.
    replace (length vals + S (length vals + 0)) with
            (1 + 2 * length vals) by lia.
    simpl in *.
    eassumption.
    all: reflexivity.
Qed.


Theorem put_back_labeled :
  forall F Fs (e : Exp) r k l,
    FrameWf F -> (* required by map frames *)
    is_result r -> (* required by special case frames *)
    ⟨F :: Fs, e⟩ -[k, l]->ₗ ⟨[], r⟩
  ->
    exists j, ⟨Fs, plug_f F e⟩ -[j, l]->ₗ ⟨[], r⟩.
Proof.
  destruct F; intros; simpl.
  all: try by (eexists; econstructor; [ constructor | eassumption | reflexivity]).
  * eexists. econstructor. constructor.
    econstructor. constructor.
    econstructor. constructor. eassumption.
    all: reflexivity.
  (* parameter list frames: *)
  * pose proof (to_Exp_eval_labeled vl e el ident Fs H) as [k0 X].
    eexists.
    eapply transitive_eval_labeled with (l := []). exact X.
    exact H1.
  (***)
  * eexists.
    econstructor. constructor.
    econstructor. constructor.
    econstructor. constructor. eassumption.
    all: reflexivity.
  (* Special "case" frame: *)
  * (* independent evaluation of e *)
    assert (terminates_in_k_sem_labeled (FCase2 lv ex le :: Fs) e k l) as X. {
      exists r. split; eassumption.
    }
    apply semantic_iff_termination in X.
    apply term_empty_labeled in X as [k0 [newl [X [Hk0 Hpref]]]].
    eapply term_eval_empty_labeled in X as [res [i [newl2 [Hres [X [Hi Hpref2]]]]]].
    eapply frame_indep_nil_labeled in X as X'.
    replace k with (i+(k-i)) in H1 by lia.
    pose proof (prefix_drop _ _ Hpref2 _ eq_refl) as HX.
    pose proof (prefix_drop _ _ Hpref _ eq_refl) as HX2.
    rewrite HX2, HX in H1. rewrite <- app_assoc in H1.
    epose proof (transitive_eval_rev_labeled _ _ _ _ _ _ X' _ _ _ _ H1) as XX.
    inv XX. clear X'.
    inv Hres; inv H3.
    (* exception result and vseq (true and false guard) result
       can have different number of steps *)
    (* exception *)
    - eexists.
      econstructor. constructor.
      econstructor. constructor.
      econstructor. econstructor. congruence. reflexivity.
      econstructor. constructor. reflexivity.
      simpl. do 2 rewrite idsubst_is_id_exp.
      eapply frame_indep_nil_labeled in X as X'. eapply transitive_eval_labeled.
      exact X'. clear X'. econstructor. constructor. reflexivity.
      eapply frame_indep_nil_labeled in X.
      replace k with (i+(k-i)) in H1 by lia.
      epose proof (transitive_eval_rev_labeled _ _ _ _ _ _ X _ _ _ _ H1) as XX.
      inv XX. inv H5. assert (k2 = k1) by lia. subst. exact H6.
      all: try reflexivity.
      simpl.
      by rewrite <-HX, app_assoc, <-HX.
    (* true guard *)
    - eexists.
      econstructor. constructor.
      econstructor. constructor.
      econstructor. econstructor. congruence. reflexivity.
      econstructor. constructor. reflexivity.
      simpl. do 2 rewrite idsubst_is_id_exp.
      eapply frame_indep_nil_labeled in X. eapply transitive_eval_labeled.
      exact X. clear X. econstructor. constructor.
      eassumption.
      all: try reflexivity.
      simpl.
      by rewrite <-HX, app_assoc, <-HX.
    (* false guard *)
    - eexists.
      econstructor. constructor.
      econstructor. constructor.
      econstructor. econstructor. congruence. reflexivity.
      econstructor. constructor. reflexivity.
      simpl. do 2 rewrite idsubst_is_id_exp.
      eapply frame_indep_nil_labeled in X. eapply transitive_eval_labeled.
      exact X. clear X. econstructor. constructor.
      econstructor. constructor. reflexivity. cbn.
      rewrite map_ext with (g := id). 2: {
        intros. by rewrite idsubst_is_id_exp.
      }
      rewrite map_id.
      rewrite map_ext with (g := id). 2: {
        intros. destruct a as [[pl g] b].
        rewrite idsubst_upn.
        by do 2 rewrite idsubst_is_id_exp.
      }
      rewrite map_id.
      econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor.
      eapply transitive_eval_labeled.
      apply params_eval_VValues_labeled. eassumption.
      all: try reflexivity. simpl.
      by rewrite <-HX, app_assoc, <-HX.
Qed.

Corollary put_back_term_labeled : forall F (e : Exp) Fs l, FrameWf F ->
  | F :: Fs, e |ₗ l ↓ -> | Fs, plug_f F e |ₗ l ↓.
Proof.
  intros.
  destruct H0. apply semantic_iff_termination in H0.
  destruct H0 as [res [Hres H0]].
  apply put_back_labeled in H0; try assumption.
  destruct H0. exists x0.
  apply semantic_iff_termination. eexists. split; eassumption.
Qed.

Corollary transitive_eval_rev_lt_labeled :
  forall {Fs r Fs' r' k1} l1, ⟨Fs, r⟩ -[k1, l1]->ₗ ⟨Fs', r'⟩ ->
    forall {Fs'' r'' k2} l2, k2 <= k1 -> l2 `prefix_of` l1
      -> ⟨Fs, r⟩ -[k2, l2]->ₗ ⟨Fs'', r''⟩ ->
      ⟨Fs'', r''⟩ -[k1 - k2, drop (length l2) l1]->ₗ ⟨Fs', r'⟩.
Proof.
  intros.
  replace k1 with (k2 + (k1 - k2)) in H by lia.
  replace l1 with (l2 ++ drop (length l2) l1) in H. 2: {
    eapply prefix_drop in H1. 2: reflexivity. by rewrite H1 at 2.
  }
  eapply transitive_eval_rev_labeled in H. 2: eassumption. assumption.
Qed.

Ltac inv_term_labeled :=
  match goal with
  | [H : | _, _ | _ – _ ↓ |- _] => inv H
  end.

Lemma transitive_contradiction_labeled :
  forall k1 fs r fs' r' k2 l1 l2 r'', is_result r'' ->
    ⟨fs, r⟩ -[k1, l1]->ₗ ⟨fs', r'⟩ ->
    ⟨fs, r⟩ -[k2, l2]->ₗ ⟨[], r''⟩ ->
    k2 < k1 ->
    False.
Proof.
  induction k1; intros.
  * lia.
  * inv H0. inv H1.
    - by apply value_nostep_labeled in H4.
    - eapply IHk1.
      + eassumption.
      + eassumption.
      + eapply step_determinism_labeled in H0. 2: exact H4.
        destruct_and!. subst. eassumption.
      + lia.
Qed.

Theorem put_back_rev_labeled :
  forall F Fs (e : Exp) r k l,
    FrameWf F -> (* required by map frames *)
    is_result r -> (* required by special case frames *)
    ⟨Fs, plug_f F e⟩ -[k, l]->ₗ ⟨[], r⟩
  ->
    exists j, ⟨F :: Fs, e⟩ -[j, l]->ₗ ⟨[], r⟩.
Proof.
  destruct F; intros; simpl in *.
  all: try by (inv H1; try inv_result; inv H2;
    eexists; eassumption).
  * inv H1; try inv_result. inv H2.
    inv H3. inv H1.
    inv H2. inv H1.
    eexists; eassumption.
  (* parameter list frame: *)
  * pose proof (to_Exp_eval_labeled vl e el ident Fs H) as [k0 X].
    assert (k0 <= k \/ k0 > k) as [Hlt | Hlt] by lia.
    - opose proof (transitive_eval_rev_lt_labeled _ H1 _ Hlt _ X).
      apply prefix_nil.
      eexists. eassumption.
    (* k0 > k cannot happen: *)
    - by eapply transitive_contradiction_labeled in H1.
  * inv H1; try inv_result. inv H2.
    inv H3. inv H1.
    inv H2. inv H1.
    eexists; eassumption.
  (* special "case" frame *)
  * inv H1. inv_result. inv H2.
    inv H3. inv H1.
    inv H2. inv H1. simpl in H10. invSome.
    inv H3. inv H1. simpl in *. invSome.
    simpl in *.
    do 2 rewrite idsubst_is_id_exp in H2.
    (* extract independent evaluation of e: *)
    assert (terminates_in_k_sem_labeled (FCase2 [] ex
      [([], ˝ VLit "true"%string,
        ° ECase (° EValues (map VVal lv)) le)] :: Fs) e k l) as X. {
      exists r. split; eassumption.
    }
    apply semantic_iff_termination in X.
    eapply term_eval_empty_labeled in X as [res [i [newl [Hres [X [Hi Hpref]]]]]].
    (***)
    eapply frame_indep_nil_labeled in X as X'.
    pose proof (transitive_eval_rev_lt_labeled _ H2 _ Hi Hpref X') as XX.
    clear X' H2.
    (* check what's the guard result: exception, false, or true *)
    inv XX. inv Hres; inv H2.
    (* exception *)
    - eexists.
      eapply frame_indep_nil_labeled in X.
      pose proof (prefix_drop _ _ Hpref _ eq_refl). rewrite H2.
      eapply transitive_eval_labeled.
      exact X. econstructor. constructor. reflexivity.
      eassumption.
      reflexivity.
    (* true - proof is the same as in the previous case *)
    - eexists.
      eapply frame_indep_nil_labeled in X.
      pose proof (prefix_drop _ _ Hpref _ eq_refl). rewrite H2.
      eapply transitive_eval_labeled.
      exact X. econstructor. constructor.
      eassumption.
      reflexivity.
    (* false *)
    - inv H3. inv H2.
      simpl in H15. invSome. simpl in *.
      rewrite map_ext with (g := id) in H4. 2: {
        intros. by rewrite idsubst_is_id_exp.
      }
      rewrite map_id in H4.
      rewrite map_ext with (g := id) in H4. 2: {
        intros. destruct a as [[pl g] b].
        rewrite idsubst_upn.
        by do 2 rewrite idsubst_is_id_exp.
      }
      rewrite map_id in H4. inv H4. inv H2.
      inv H3. inv H2.
      inv H4. inv_result. inv H2.
      pose proof (params_eval_VValues_labeled lv (FCase1 le :: fs')).
      assert (k0 >= 2 + 2 * base.length lv \/ k0 < 2 + 2 * base.length lv) as [Hlt | Hlt] by lia.
      + opose proof (transitive_eval_rev_lt_labeled _ H3 _ Hlt _ H2) as XX.
        apply prefix_nil.
        eexists.
        eapply frame_indep_nil_labeled in X.
        pose proof (prefix_drop _ _ Hpref _ eq_refl). rewrite H4.
        eapply transitive_eval_labeled. exact X.
        econstructor. constructor.
        exact XX.
        simpl. by rewrite drop_0.
      (* k0 should be greater; therefore, this is a contradiction *)
      + by eapply transitive_contradiction_labeled in H2.
Qed.


Theorem put_back_rev_term_labeled : forall F e Fs l, FrameWf F ->
  | Fs, plug_f F e |ₗ l ↓ -> | F :: Fs, e |ₗ l ↓.
Proof.
  intros.
  destruct H0. apply semantic_iff_termination in H0.
  destruct H0 as [res [Hres H0]].
  apply put_back_rev_labeled in H0; try assumption.
  destruct H0. exists x0.
  apply semantic_iff_termination. eexists. split; eassumption.
Qed.
