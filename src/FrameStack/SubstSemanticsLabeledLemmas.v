(**
  This file contains numerous semantic properties about the frame stack semantics
  (labelled version) of Core Erlang.
 *)
From CoreErlang.FrameStack Require Export SubstSemanticsLabeled.
From stdpp Require Export list option.
Import ListNotations.

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
  * inv H1. split. reflexivity. rewrite <- H3 in H9. inv H9. reflexivity.
  * split. reflexivity. rewrite <- H2 in H8. inv H8. reflexivity.
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

Print SideEffect.

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
  intros F e l F' e' H. induction H. intros. destruct H. auto.
  apply step_closedness in H. inv H.
  apply (step_any_closedness _ _ _ _ _ _ H2 H4 H5). all: assumption.
Qed.