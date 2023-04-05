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
  * now apply closed_primop_eval.
  * inversion Hi; subst; clear Hi. destruct v; unfold badfun.
    1-7: constructor; auto; constructor.
    break_match_goal.
    - constructor. destruct_scopes.
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
    intros. apply H7 in H.
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
    - apply (H4 0). simpl. lia.
    - eexists; eassumption.
    - intros. apply (H1 (S i)). simpl. lia.
    - intros. apply (H4 (S i)). simpl. lia.
  * constructor. apply -> subst_preserves_scope_exp.
    apply (H1 0 ltac:(slia)).
    erewrite match_pattern_list_length. 2: exact H.
    apply scoped_list_idsubst.
    eapply match_pattern_list_scope; eassumption.
  * do 2 (constructor; auto).
    - intros. apply (H1 (S i)). simpl. lia.
    - intros. apply (H4 (S i)). simpl. lia.
  * constructor. apply -> subst_preserves_scope_exp. exact H7.
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

Lemma create_result_is_not_box :
  forall ident vl,
  is_result (create_result ident vl) \/
  (exists e, (create_result ident vl) = RExp e).
Proof.
  destruct ident; intro; simpl; auto.
  1: left; apply eval_is_result.
  1: left; apply primop_eval_is_result.
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

Lemma Private_term_empty_case l: forall Fs (vs : ValSeq) n,
  (forall m : nat,
  m < n ->
  forall (Fs : FrameStack) (e : Exp),
  | Fs, e | m ↓ -> exists k : nat, (| [], e | k ↓) /\ k <= m) ->
  | FCase1 l :: Fs, vs | n ↓ -> (* this has to be value sequence, because 
                                   in case of not matching patterns, only
                                   this is usable *)
  exists res k, is_result res /\
  ⟨ [FCase1 l ], vs⟩ -[k]->
  ⟨ [], res ⟩ /\ k <= n.
Proof.
  induction l; intros Fs vs n IH HD.
  * (* empty case *) inv HD. eexists. exists 1.
    split. 2: split. 2: econstructor; constructor.
    auto. nia.
  * inv HD.
    - (* matching first pattern *)
      apply IH in H5 as HH. 2: nia. destruct HH as [i [Hdgr Hlt]].
      apply terminates_in_k_eq_terminates_in_k_sem in Hdgr as [gr [Hgr Hdgr]]. (* guard result *)
      eapply frame_indep_nil in Hdgr as Hlia.
      eapply frame_indep_nil in Hdgr.
      eapply term_step_term in H5.
      2: exact Hlia. simpl in *. inv Hgr.
      + (* guard is an exception *) inv H5.
        exists ex, (1 + (i + 1)). split; auto. split; [|nia].
        econstructor. constructor. exact H4. eapply transitive_eval.
        exact Hdgr. econstructor. constructor. congruence. constructor.
      + destruct vs0. 2: destruct vs0. all: inv H5.
        ** (* guard is true *)
           apply IH in H9 as HH. 2: nia. destruct HH as [j [Hdcl Hlt2]].
           apply terminates_in_k_eq_terminates_in_k_sem in Hdcl as [clr [Hclr Hdcl]]. (* clause result *)
           eapply frame_indep_nil in Hdcl. simpl in *.
           assert (⟨ [FCase2 vs lp e2 l], RValSeq [VLit "true"%string] ⟩ -[1]->
           ⟨ [], e2.[list_subst vs'0 idsubst] ⟩). {
             econstructor. constructor. eassumption. constructor.
           }
           epose proof (transitive_eval Hdgr H).
           epose proof (transitive_eval H0 Hdcl).
           exists clr, (1 + (i + 1 + j)). split; auto.
           split. 2: nia.
           econstructor. apply eval_step_case_match. exact H1.
           rewrite H4 in H1. inv H1.
           exact H2.
        ** (* guard is false *)
           apply IHl in H0 as [res [j [Hres [HD Htl]]]].
           2: {
             intros. eapply IH. nia. exact H1.
           }
           exists res, (1 + (i + S j)). split. 2: split. auto. 2: nia.
           econstructor. apply eval_step_case_match. eassumption.
           eapply transitive_eval. exact Hdgr.
           econstructor. constructor. assumption.
    - (* not matching first pattern *)
      apply IHl in H5 as [res [j [Hres [HD Htl]]]].
      2: {
        intros. eapply IH. nia. exact H0.
      }
      exists res, (1 + j). split. 2: split. auto. 2: nia.
      econstructor. now apply eval_step_case_not_match. assumption.
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
        intros. specialize (H m0 ltac:(slia) Fs0 e0 H1) as [j [HD Hj]].
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
    simpl. constructor. apply primop_eval_is_result.
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
  (* for case: list_length_ind on H3 (or structural could also be enough) *)
  * apply H in H3 as HH. 2: nia. destruct HH as [k1 [Hd1 Hlt1]].
    apply terminates_in_k_eq_terminates_in_k_sem in Hd1 as [r1 [Hr Hd]].
    eapply frame_indep_nil in Hd as Hlia1.
    eapply frame_indep_nil in Hd.
    eapply term_step_term in H3. 2: exact Hlia1.
    simpl in *.
    inv Hr. (* exception? *)
    + exists (1 + k1 + 1). split. 2: inv H3; nia.
      simpl. constructor. eapply step_term_term. exact Hd.
      replace (k1 + 1 - k1) with 1 by nia.
      constructor. congruence. now constructor. nia.
    + epose proof (Private_term_empty_case l Fs vs (k - k1) _ H3) as
        [res [k2 [Hres [Hd2 Hlt2]]]].
      Unshelve. 2: {
        intros. eapply H. nia. eassumption.
      }
      pose proof (transitive_eval Hd Hd2).
      exists (S (k1 + k2)). split. 2: nia.
      constructor.
      apply terminates_in_k_eq_terminates_in_k_sem. exists res. now split.
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
Qed.

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
