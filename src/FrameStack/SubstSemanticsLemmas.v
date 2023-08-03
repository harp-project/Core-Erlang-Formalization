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
  * now specialize (H5 _ _ _ _ eq_refl).
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
  * destruct m, f; try destruct l; try destruct l0; try now apply closed_eval.
    all: inv Hi; constructor; auto; scope_solver.
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
  * do 2 (constructor; auto).
    - specialize (H4 0 ltac:(slia)). cbn in H4.
      apply -> subst_preserves_scope_exp. eassumption.
      eapply match_pattern_list_scope in H as Hmatch. 2: eassumption.
      apply match_pattern_list_length in H. unfold PatListScope in H.
      rewrite H. now apply scoped_list_idsubst.
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
  (* * constructor. apply -> subst_preserves_scope_exp. exact H4.
    erewrite match_pattern_list_length. 2: exact H.
    apply scoped_list_idsubst.
    eapply match_pattern_list_scope; eassumption. *)
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
      - econstructor. constructor; try eassumption.
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
      - econstructor.
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
  Forall (fun v => VALCLOSED v) vals ->
  ⟨ FParams ident vl ((map VVal vals) ++ e :: exps) :: Fs, RValSeq [v]⟩ -[1 + 2 * length vals]->
  ⟨ FParams ident (vl ++ v :: vals) exps :: Fs, e⟩.
Proof.
  induction vals; simpl; intros.
  * econstructor. constructor. constructor.
  * specialize (IHvals ident (vl ++ [v]) exps e Fs a).
    econstructor. constructor.
    econstructor. constructor.
    rewrite <- app_assoc in IHvals. now inv H.
    replace (length vals + S (length vals + 0)) with
            (1 + 2*length vals) by lia. rewrite <- app_assoc in IHvals. apply IHvals.
    now inv H.
Qed.

Lemma params_eval_create :
  forall vals ident vl Fs (v : Val),
  Forall (fun v => VALCLOSED v) vals ->
  ⟨ FParams ident vl (map VVal vals) :: Fs, RValSeq [v]⟩ -[1 + 2 * length vals]->
  ⟨ Fs, create_result ident (vl ++ v :: vals)⟩.
Proof.
  induction vals; simpl; intros.
  * econstructor. constructor. reflexivity. constructor.
  * specialize (IHvals ident (vl ++ [v]) Fs a). inv H.
    econstructor. constructor.
    econstructor. constructor; auto.
    rewrite <- app_assoc in IHvals.
    replace (length vals + S (length vals + 0)) with
            (1 + 2*length vals) by lia. now apply IHvals.
Qed.

Lemma create_result_is_not_box :
  forall ident vl,
  ICLOSED ident ->
  Forall (fun v => VALCLOSED v) vl ->
  is_result (create_result ident vl) \/
  (exists e, (create_result ident vl) = RExp e).
Proof.
  destruct ident; intros; simpl; auto.
  1: left; do 2 constructor. constructor. now apply indexed_to_forall.
  1: auto.
  1: left; do 2 constructor. constructor.
  (* map *)
  1-2: erewrite <- map_length; apply indexed_to_forall.
  1-2: eapply List.Forall_map; apply make_val_map_keeps_prop.
  1-2: eapply Forall_impl; [|eapply deflatten_keeps_prop; eassumption].
  1-2: intros; destruct a; apply H1.
  (****)
  1: auto.
  1: left; destruct m, f; try destruct l; try destruct l0; try apply eval_is_result; auto; constructor; inv H; scope_solver.
  1: left; apply primop_eval_is_result; auto.
  inv H. destruct v; try now (left; constructor; auto).
  break_match_goal; auto.
  right. eexists. reflexivity.
  left. constructor; auto.
Qed.

Lemma Private_params_exp_eval :
  forall exps ident vl Fs (e : Exp) n (Hid : ICLOSED ident) (Hvl : Forall (fun v => VALCLOSED v) vl),
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
      inv H. destruct (create_result_is_not_box ident (vl ++ [v])); auto.
      + now apply Forall_app.
      + do 2 eexists. split. 2: split.
        2: {
          eapply transitive_eval. exact Hd.
          eapply step_trans. constructor. reflexivity. apply step_refl.
        }
        auto.
        lia.
      (* if create_result was a function application: *)
      + inv H. rewrite H2 in *. apply H0 in H8 as H8'.
        destruct H8' as [res2 [k2 [Hres2 [Hd2 Hlt2]]]]. 2: lia.
        eapply frame_indep_nil in Hd2.
        eapply term_step_term in H8. 2: exact Hd2.
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
      inv H. apply IHexps in H3 as [res2 [k2 [Hres2 [Hd2 Hlt2]]]].
      4: {
        intros. eapply H0. lia. eassumption.
      }
      do 2 eexists. split. 2: split.
      2: {
        eapply transitive_eval. exact Hd.
        eapply step_trans. constructor. exact Hd2.
      }
      auto.
      lia.
      auto.
      now apply Forall_app.
Qed.

Lemma Private_params_exp_eval_empty :
  forall exps ident vl Fs (e : Exp) n (Hid : ICLOSED ident) (Hvl : Forall (fun v => VALCLOSED v) vl) (Hcle : EXPCLOSED e) (Hexps : Forall (fun e => EXPCLOSED e) exps),
  | FParams ident vl exps :: Fs, e | n ↓ ->
  (forall m : nat,
  m < S n ->
  forall (Fs : FrameStack) (e : Exp),
  | Fs, e | m ↓ -> EXPCLOSED e ->
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
      + auto.
      + now apply Forall_app.
      + do 2 eexists. split. 2: split.
        2: {
          eapply transitive_eval. exact Hd.
          eapply step_trans. constructor. reflexivity. apply step_refl.
        }
        auto.
        lia.
      (* if create_result was a function application: *)
      + inv H2. rewrite H3 in *. apply H0 in H8 as H8'. 2: lia.
        destruct H8' as [res2 [k2 [Hres2 [Hd2 Hlt2]]]].
        eapply frame_indep_nil in Hd2 as Hlia3.
        eapply frame_indep_nil in Hd2.
        eapply term_step_term in H8. 2: exact Hlia3.
        do 2 eexists. split. 2: split.
        2: {
          eapply transitive_eval. exact Hd.
          eapply step_trans. constructor. reflexivity. rewrite H3.
          exact Hd2.
        }
        auto.
        lia.
        pose proof (create_result_closed (vl ++ [v]) ident ltac:(apply Forall_app; auto) Hid). rewrite H3 in H2. now inv H2.
    - auto.
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
      inv Hlia2. inv H1. inv Hexps.
      apply IHexps in H3 as [res2 [k2 [Hres2 [Hd2 Hlt2]]]]; auto.
      3: {
        intros. eapply H0. lia. eassumption. eassumption.
      }
      do 2 eexists. split. 2: split.
      2: {
        eapply transitive_eval. exact Hd.
        eapply step_trans. constructor. exact Hd2.
      }
      auto.
      lia.
      auto.
      apply Forall_app. split; auto.
    - auto.
Qed.

Lemma Private_term_empty_case l: forall Fs (vs : ValSeq) n
  (Hcl : Forall (fun '(p, g, e) => EXP PatListScope p ⊢ g /\ EXP PatListScope p ⊢ e) l)
  (Hvl : Forall (fun v => VALCLOSED v) vs),
  (forall m : nat,
  m < n ->
  forall (Fs : FrameStack) (e : Exp), EXPCLOSED e ->
  | Fs, e | m ↓ -> exists k : nat, (| [], e | k ↓) /\ k <= m) ->
  | FCase1 l :: Fs, vs | n ↓ -> (* this has to be value sequence, because 
                                   in case of not matching patterns, only
                                   this is usable *)
  exists res k, is_result res /\
  ⟨ [FCase1 l ], vs⟩ -[k]->
  ⟨ [], res ⟩ /\ k <= n.
Proof.
  induction l; intros Fs vs n Hcl Hvl IH HD.
  * (* empty case *) inv HD. eexists. exists 1.
    split. 2: split. 2: econstructor; constructor.
    constructor; constructor. lia.
  * inv HD.
    - (* matching first pattern *)
      apply IH in H5 as HH. 2: lia. destruct HH as [i [Hdgr Hlt]].
      apply terminates_in_k_eq_terminates_in_k_sem in Hdgr as [gr [Hgr Hdgr]]. (* guard result *)
      eapply frame_indep_nil in Hdgr as Hlia.
      eapply frame_indep_nil in Hdgr.
      eapply term_step_term in H5.
      2: exact Hlia. simpl in *. inv Hgr.
      + (* guard is an exception *) inv H5.
        exists (RExc (cl, v1, v2)), (1 + (i + 1)). split; auto. split; [|lia].
        econstructor. constructor. exact H4. eapply transitive_eval.
        exact Hdgr. econstructor. constructor. congruence. constructor.
      + inv H5.
        ** (* guard is true *)
           apply IH in H1 as HH. 2: lia.
           2: {
             apply -> subst_preserves_scope_exp.
             inv Hcl. apply H3.
             apply match_pattern_list_length in H4 as H4'. rewrite H4'.
             apply scoped_list_idsubst.
             eapply match_pattern_list_scope; eauto.
           }
           destruct HH as [j [Hdcl Hlt2]].
           apply terminates_in_k_eq_terminates_in_k_sem in Hdcl as [clr [Hclr Hdcl]]. (* clause result *)
           eapply frame_indep_nil in Hdcl. simpl in *.
           assert (⟨ [FCase2 vs e2.[list_subst vs' idsubst] l], RValSeq [VLit "true"%string] ⟩ -[1]->
           ⟨ [], e2.[list_subst vs' idsubst] ⟩). {
             econstructor. constructor. constructor.
           }
           epose proof (transitive_eval Hdgr H0).
           epose proof (transitive_eval H2 Hdcl).
           exists clr, (1 + (i + 1 + j)). split; auto.
           split. 2: lia.
           econstructor. apply eval_step_case_match; eassumption.
           eassumption.
        ** (* guard is false *)
           inv Hcl.
           apply IHl in H1 as [res [j [Hres [HD Htl]]]]; auto.
           2: {
             intros. eapply IH. lia. exact H2. eassumption.
           }
           exists res, (1 + (i + S j)). split. 2: split. auto. 2: lia.
           econstructor. apply eval_step_case_match. eassumption.
           eapply transitive_eval. exact Hdgr.
           econstructor. constructor. assumption.
      + apply -> subst_preserves_scope_exp. inv Hcl. apply H1.
        apply match_pattern_list_length in H4 as H4'. rewrite H4'.
        apply scoped_list_idsubst.
        eapply match_pattern_list_scope; eauto.
    - (* not matching first pattern *)
      inv Hcl.
      apply IHl in H5 as [res [j [Hres [HD Htl]]]]; auto.
      2: {
        intros. eapply IH. lia. exact H0. eassumption.
      }
      exists res, (1 + j). split. 2: split. auto. 2: lia.
      econstructor. now apply eval_step_case_not_match. assumption.
Qed.


Lemma term_empty : forall x Fs (e : Exp) (He : EXPCLOSED e),
  | Fs, e | x ↓ ->
  exists k, | [], e | k ↓ /\ k <= x.
Proof.
  induction x using Wf_nat.lt_wf_ind; intros; inv H0.
  * eexists. split. constructor; auto. do 3 constructor; auto. lia.
  * destruct el. (* tricks to avoid RBox *)
    - eexists. split. constructor. eapply cool_params_0.
      congruence. reflexivity. do 2 constructor. auto. inv H3. lia.
    - inv H3. destruct_scopes.
      eapply Private_params_exp_eval_empty in H8 as HH2; auto.
      2-3: rewrite <- indexed_to_forall in H3; now inv H3.
      2: {
        intros. epose proof (H m ltac:(slia) Fs0 e0 _ H1) as [j [HD Hj]].
        apply terminates_in_k_eq_terminates_in_k_sem in HD as [res [Hres Hr]].
        do 2 eexists. split. 2: split. all: eassumption.
      }
      destruct HH2 as [res [k [Hres [Hd Hlt]]]].
      eexists. split. do 2 constructor. congruence.
      eapply terminates_in_k_eq_terminates_in_k_sem. eexists.
      split. 2: exact Hd. auto. lia.
  * destruct el. (* proof is same as above, tricks to avoid RBox *)
    - eexists. split. constructor. eapply cool_params_0.
      congruence. reflexivity. do 4 constructor; auto. intros. inv H0. inv H3. lia.
    - inv H3. destruct_scopes.
      eapply Private_params_exp_eval_empty in H8 as HH2; auto.
      2-3: rewrite <- indexed_to_forall in H3; now inv H3.
      2: {
        intros. epose proof (H m ltac:(slia) Fs0 e0 _ H1) as [j [HD Hj]].
        apply terminates_in_k_eq_terminates_in_k_sem in HD as [res [Hres Hr]].
        do 2 eexists. split. 2: split. all: eassumption.
      }
      destruct HH2 as [res [k [Hres [Hd Hlt]]]].
      eexists. split. do 2 constructor. congruence.
      eapply terminates_in_k_eq_terminates_in_k_sem. eexists.
      split. 2: exact Hd. auto. lia.
  * eexists. split. do 5 constructor; slia. lia.
  * destruct_scopes.
    eapply Private_params_exp_eval_empty in H3 as HH2; auto.
    2: apply (H1 0); slia.
    2: { constructor. apply (H5 0); slia. apply flatten_keeps_prop.
         rewrite indexed_to_forall with (def := (`VNil, `VNil)). intros.
         specialize (H1 (S i) ltac:(slia)). specialize (H5 (S i) ltac:(slia)).
         simpl in *. rewrite map_nth with (d := (`VNil, `VNil)) in H1, H5.
         destruct nth; now split.
       }
    2: {
      intros. epose proof (H m ltac:(slia) Fs0 e _ H2) as [j [HD Hj]].
      apply terminates_in_k_eq_terminates_in_k_sem in HD as [res [Hres Hr]].
      do 2 eexists. split. 2: split. all: eassumption.
    }
    destruct HH2 as [res [k0 [Hres [Hd Hlt]]]].
    eexists. split. constructor.
    eapply terminates_in_k_eq_terminates_in_k_sem. eexists.
    split. 2: exact Hd. auto. lia.
  * (* Call is trickier, because first the module, then the function
       expression has to be evaluated *)
    destruct_scopes. apply H in H3 as HD1; auto.
    destruct HD1 as [k1 [D1 Hlia1]].
    apply terminates_in_k_eq_terminates_in_k_sem in D1 as [res1 [Hres1 Hr1]].
    eapply frame_indep_nil in Hr1 as Hr1'.
    eapply frame_indep_nil in Hr1.
    eapply term_step_term in H3.
    2: exact Hr1. simpl in *.
    inv Hres1.
    (* moduleexp Exception *)
    - inv H3. eexists. split. constructor.
      eapply step_term_term_plus. exact Hr1'. constructor.
      congruence. constructor. constructor; auto. lia.
    (* moduleexp Value *)
    - inv H3. inv H0. clear H5.
      apply H in H2 as HD2; auto. 2: lia.
      destruct HD2 as [k2 [D2 Hlia2]].
      apply terminates_in_k_eq_terminates_in_k_sem in D2 as [res2 [Hres2 Hr2]].
      eapply frame_indep_nil in Hr2 as Hr2'.
      eapply frame_indep_nil in Hr2.
      eapply term_step_term in H2.
      2: exact Hr2. simpl in *.
      inv Hres2.
      (* funexp exception *)
      + inv H2. eexists. split. constructor.
        eapply step_term_term_plus. exact Hr1'. constructor.
        eapply step_term_term_plus. exact Hr2'. constructor.
        congruence. constructor. constructor; auto. lia.
      (* moduleexp value *)
      + inv H2. destruct el. (* tricks to avoid RBox *)
        ** eexists. split. 
           constructor.
           eapply step_term_term_plus. exact Hr1'. constructor.
           eapply step_term_term_plus. exact Hr2'. constructor.
           eapply cool_params_0.
           congruence. reflexivity.
           (* here is this different from the previous *)
           simpl. constructor.
           destruct v, f0; try destruct l; try destruct l0; try constructor; auto.
           122: inv H3; lia.
           14: apply eval_is_result; auto.
           all: clear -H0 H4; inv H0; constructor; intros; destruct i; try destruct i; simpl in *; try lia; auto.
           (***)
        ** inv H3. inv H0.
           eapply Private_params_exp_eval_empty in H15 as HD3; auto.
           2: {
             apply (H6 0). slia.
           }
           2: {
             apply indexed_to_forall in H6. now inv H6.
           }
           2: {
             intros. epose proof (H m0 ltac:(slia) Fs0 e0 _ H1) as [j [HD Hj]].
             apply terminates_in_k_eq_terminates_in_k_sem in HD as [res [Hres Hr]].
             do 2 eexists. split. 2: split. all: eassumption.
           }
           destruct HD3 as [res3 [k3 [Hres3 [Hd3 Hlt3]]]].
           eexists. split.
           constructor.
           eapply step_term_term_plus. exact Hr1'. constructor.
           eapply step_term_term_plus. exact Hr2'. constructor.
           constructor. congruence.
           eapply terminates_in_k_eq_terminates_in_k_sem. eexists.
           split. 2: exact Hd3. auto. lia.
  * destruct el. (* tricks to avoid RBox *)
    - eexists. split. constructor. eapply cool_params_0.
      congruence. reflexivity.
      (* here is this different from the previous *)
      simpl. constructor. apply primop_eval_is_result; auto.
      (***)
      inv H3. lia.
    - inv H3. destruct_scopes.
      eapply Private_params_exp_eval_empty in H8 as HH2; auto.
      2-3: rewrite <- indexed_to_forall in H3; now inv H3.
      2: {
        intros. epose proof (H m ltac:(slia) Fs0 e0 _ H1) as [j [HD Hj]].
        apply terminates_in_k_eq_terminates_in_k_sem in HD as [res [Hres Hr]].
        do 2 eexists. split. 2: split. all: eassumption.
      }
      destruct HH2 as [res [k [Hres [Hd Hlt]]]].
      eexists. split. do 2 constructor. congruence.
      eapply terminates_in_k_eq_terminates_in_k_sem. eexists.
      split. 2: exact Hd. auto. lia.
  (* application is harder, because first, the function parameter needs
     to be evaluated, then we do a case separation, whether l = [].
     Everytime an exception occurs, that needs to be propagated -> hence
     the number of case separations. *)
  * apply H in H3 as H3'. destruct H3' as [j [Hj Hlt1]]. 2: lia.
    apply terminates_in_k_eq_terminates_in_k_sem in Hj as [res [Hres Hr]].
    eapply frame_indep_nil in Hr as Hlia1.
    eapply frame_indep_nil in Hr. eapply term_step_term in H3.
    2: exact Hlia1. simpl in *.
    destruct l. (* tricks to avoid RBox *)
    - inv Hres. (* exception result? *)
      + exists (2 + j). split. constructor.
        eapply step_term_term. exact Hr. 2: lia.
        replace (S j - j) with 1 by lia.
        constructor. congruence. constructor. auto.
        inv H3. lia.
      + inv H3. inv H2. destruct (create_result_is_not_box (IApp v) []).
        ** inv H0; now constructor.
        ** auto.
        ** exists (3 + j). split. constructor.
           eapply step_term_term. exact Hr. 2: lia.
           replace (S (S j) - j) with 2 by lia.
           constructor. econstructor. congruence. reflexivity.
           now constructor.
           lia.
        ** inv H1. rewrite H2 in *. apply H in H9 as H9'. 2: lia.
           destruct H9' as [i [Hd2 Hlt2]].
           exists (1 + (j + 2 + i)). split. constructor.
           eapply step_term_term. exact Hr. 2: lia.
           replace (j + 2 + i - j) with (2 + i) by lia.
           constructor. econstructor. congruence. reflexivity.
           now rewrite H2. lia.
           inv H0.
           pose proof (create_result_closed [] (IApp v) ltac:(auto) ltac:(now constructor)). rewrite H2 in H0. now inv H0.
    - inv Hres.
      + exists (2 + j). split. constructor.
        eapply step_term_term. exact Hr. 2: lia.
        replace (S j - j) with 1 by lia.
        constructor. congruence. constructor. auto.
        inv H3. lia.
      + inv H3. inv H2. destruct_scopes.
        eapply Private_params_exp_eval_empty in H10 as HH2; auto.
        3-4: rewrite <- indexed_to_forall in H7; now inv H7.
        2: { inv H0; now constructor. }
        2: {
          intros. epose proof (H m ltac:(slia) Fs0 e1 _ H2) as [i [Hd2 Hi]].
          apply terminates_in_k_eq_terminates_in_k_sem in Hd2
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
        constructor. apply terminates_in_k_eq_terminates_in_k_sem.
        eexists. split. 2: exact Hd2. assumption. lia.
    - now destruct_scopes.
  * apply H in H3 as HH. 2: lia.
    destruct HH as [i [Hi Hlt]].
    apply terminates_in_k_eq_terminates_in_k_sem in Hi as [res [Hres Hr]].
    eapply frame_indep_nil in Hr as Hlia1.
    eapply frame_indep_nil in Hr.
    eapply term_step_term in H3. 2: exact Hlia1.
    inv Hres. (* tail exception or not *)
    - exists (S i + 1).
      split. 2: inv H3; lia.
      simpl. constructor. apply terminates_in_k_eq_terminates_in_k_sem.
      exists (RExc (cl, v1, v2)). split; auto. eapply transitive_eval.
      exact Hr. do 2 econstructor. congruence.
    - inv H3. apply H in H2 as HH. 2: lia.
      destruct HH as [j [Hj Hltj]].
      simpl in *. apply terminates_in_k_eq_terminates_in_k_sem in Hj as [hdres [Hr2 Hd2]].
      eapply frame_indep_nil in Hd2 as Hlia2.
      eapply frame_indep_nil in Hd2.
      eapply term_step_term in H2. 2: exact Hlia2.
      assert (⟨ [FCons1 hd], RValSeq [tl0] ⟩ -[1]-> ⟨[FCons2 tl0], hd⟩). {
        repeat econstructor.
      }
      eapply (transitive_eval Hr) in H1.
      eapply (transitive_eval H1) in Hd2.
      inv Hr2. (* head exception or not *)
      + exists (1 + (i + (1 + (j + 1) ))). split.
        simpl. constructor. eapply step_term_term.
        exact Hd2.
        replace (i + S (j + 1) - (i + 1 + j)) with 1 by lia.
        constructor. congruence. do 2 constructor; auto.
        lia.
        inv H2. lia.
      + exists (1 + (i + (1 + (j + 1) ))). split.
        simpl. constructor. eapply step_term_term.
        exact Hd2. inv H2.
        replace (i + S (j + 1) - (i + 1 + j)) with 1 by lia.
        constructor. do 4 constructor; inv H0; now inv H3.
        lia.
        inv H2. lia.
      + now destruct_scopes.
    - now destruct_scopes.
  * apply H in H3 as HH. 2: lia.
    destruct HH as [i [Hi Hlt]].
    apply terminates_in_k_eq_terminates_in_k_sem in Hi as [res [Hres Hr]].
    eapply frame_indep_nil in Hr as Hlia1.
    eapply frame_indep_nil in Hr.
    eapply term_step_term in H3. 2: exact Hlia1.
    inv Hres. (* tail exception or not *)
    - exists (S i + 1).
      split. 2: inv H3; lia.
      simpl. constructor. apply terminates_in_k_eq_terminates_in_k_sem.
      exists (RExc (cl, v1, v2)). split; auto. eapply transitive_eval.
      exact Hr. do 2 econstructor. congruence.
    - inv H3. apply H in H8 as HH. 2: lia.
      destruct HH as [j [Hj Hltj]].
      simpl in *. apply terminates_in_k_eq_terminates_in_k_sem in Hj as [hdres [Hr2 Hd2]].
      eapply frame_indep_nil in Hd2 as Hlia2.
      eapply term_step_term in H8. 2: exact Hlia2.
      assert (⟨ [FLet (Datatypes.length vs) e2], RValSeq vs ⟩ -[1]-> 
      ⟨ [], e2.[list_subst vs idsubst] ⟩). {
        repeat econstructor.
      }
      eapply (transitive_eval Hr) in H1.
      eapply (transitive_eval H1) in Hd2.
      exists (1 + (i + (1 + j))). split. 2: inv Hr2; inv H7; lia.
      constructor. eapply step_term_term. exact Hd2.
      replace (i + (1 + j) - (i + 1 + j)) with 0 by lia.
      now constructor.
      lia.
      destruct_scopes. apply -> subst_preserves_scope_exp; eauto.
      rewrite Nat.add_0_r. now apply scoped_list_idsubst.
    - now destruct_scopes.
  (* Sequencing is basically same as let *)
  * apply H in H3 as HH. 2: lia.
    destruct HH as [i [Hi Hlt]].
    apply terminates_in_k_eq_terminates_in_k_sem in Hi as [res [Hres Hr]].
    eapply frame_indep_nil in Hr as Hlia1.
    eapply frame_indep_nil in Hr.
    eapply term_step_term in H3. 2: exact Hlia1.
    inv Hres. (* tail exception or not *)
    - exists (S i + 1).
      split. 2: inv H3; lia.
      simpl. constructor. apply terminates_in_k_eq_terminates_in_k_sem.
      exists (RExc (cl, v1, v2)). split; auto. eapply transitive_eval.
      exact Hr. do 2 econstructor. congruence.
    - inv H3. apply H in H2 as HH. 2: lia.
      destruct HH as [j [Hj Hltj]].
      simpl in *. apply terminates_in_k_eq_terminates_in_k_sem in Hj as [hdres [Hr2 Hd2]].
      eapply frame_indep_nil in Hd2 as Hlia2.
      eapply term_step_term in H2. 2: exact Hlia2.
      assert (⟨ [FSeq e2], RValSeq [v] ⟩ -[1]-> 
      ⟨ [], e2 ⟩). {
        repeat econstructor.
      }
      eapply (transitive_eval Hr) in H1.
      eapply (transitive_eval H1) in Hd2.
      exists (1 + (i + (1 + j))). split. 2: inv Hr2; inv H1; lia.
      constructor. eapply step_term_term. exact Hd2.
      replace (i + (1 + j) - (i + 1 + j)) with 0 by lia.
      now constructor.
      lia.
      now destruct_scopes.
    - now destruct_scopes.
  * eexists. split. constructor. do 3 constructor; auto.
    destruct_scopes. constructor; intros. inv H0. auto. lia.
  (* for case: list_length_ind on H3 (or structural could also be enough) *)
  * apply H in H3 as HH. 2: lia. destruct HH as [k1 [Hd1 Hlt1]].
    apply terminates_in_k_eq_terminates_in_k_sem in Hd1 as [r1 [Hr Hd]].
    eapply frame_indep_nil in Hd as Hlia1.
    eapply frame_indep_nil in Hd.
    eapply term_step_term in H3. 2: exact Hlia1.
    simpl in *.
    inv Hr. (* exception? *)
    + exists (1 + k1 + 1). split. 2: inv H3; lia.
      simpl. constructor. eapply step_term_term. exact Hd.
      replace (k1 + 1 - k1) with 1 by lia.
      constructor. congruence. do 2 constructor; auto. lia.
    + epose proof (Private_term_empty_case l Fs vs (k - k1) _ _ _ H3) as
        [res [k2 [Hres [Hd2 Hlt2]]]].
      Unshelve. 10: {
        intros. eapply H. lia. 2: eassumption. auto.
      }
      pose proof (transitive_eval Hd Hd2).
      exists (S (k1 + k2)). split. 2: lia.
      constructor.
      apply terminates_in_k_eq_terminates_in_k_sem. exists res. now split.
      1-6: shelve.
      2: auto.
      destruct_scopes. rewrite indexed_to_forall with (def := ([], `VNil, `VNil)).
      intros. apply H7 in H1 as H1'. apply H8 in H1. clear H7 H8.
      rewrite map_nth with (d := ([], `VNil, `VNil)) in H1, H1'.
      extract_map_fun F. replace (`VNil) with (F ([], `VNil, `VNil)) in H1' at 3 by now subst F. subst F. rewrite map_nth in H1'.
      extract_map_fun F. replace [] with (F ([], `VNil, `VNil)) in H1 by now subst F. subst F. rewrite map_nth in H1.
      destruct nth, p; split; cbn in *; rewrite Nat.add_0_r in *. apply H1'. apply H1.
    + now destruct_scopes.
  * apply H in H4 as [i [Hd Hlt]].
    eexists. split. econstructor. reflexivity. exact Hd. lia. lia.
    apply -> subst_preserves_scope_exp. destruct_scopes. apply H6.
    apply scoped_list_subscoped_eq. unfold convert_to_closlist. now do 2 rewrite map_length. 2: auto.
    apply closlist_scope. rewrite map_length, map_map; intros. destruct_scopes.
    apply H6 in H0. clear -H0. rewrite map_map.
    do 2 rewrite map_nth with (d := (0, `VNil)) in H0.
    do 2 rewrite map_nth with (d := (0, `VNil)). destruct nth. now cbn in *.
  * apply H in H3 as HH. 2: lia.
    destruct HH as [i [Hd Hlt]].
    apply terminates_in_k_eq_terminates_in_k_sem in Hd as [r [Hres Hd]].
    eapply frame_indep_nil in Hd as Hlia.
    eapply frame_indep_nil in Hd.
    eapply term_step_term in H3. 2: exact Hlia.
    simpl in *.
    inv Hres. (* exception or not *)
    - inv H3. 2: congruence.
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
  apply terminates_in_k_eq_terminates_in_k_sem in H as [r [Hr H]].
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
           2: { rewrite app_length, map_length. simpl in *.
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
      eapply step_term_term_plus. eassumption. constructor. congruence.
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
           apply params_eval_create. inv P2. now inv H4.
           cbn. eassumption.
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
             rewrite app_length, map_length. slia. }
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
    inv H7; inv H9. simpl in H10; do 2 rewrite idsubst_is_id_exp in H10.
    rename H10 into H5.
    apply term_eval_both in H5 as T. destruct T as [res [l [Hres [D0 [D1 Hlia]]]]].
    eapply term_step_term in H5. 2: eassumption. 2: auto.
    clear D1. inv Hres.
    - inv H5. eexists. eapply frame_indep_nil in D0. eapply step_term_term_plus.
      eassumption. constructor. congruence. eassumption.
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
        ** inv H7. inv H5. cbn in H11.
           eapply frame_indep_nil in D0. eexists.
           eapply step_term_term_plus. eassumption.
           eapply step_case_false. eassumption.
        ** inv H7. inv H5. inv H12. eapply term_step_term in H6.
           2: apply params_eval_create. 2: { inv H. now inv H8. }
           simpl in H6.
           eapply frame_indep_nil in D0. eexists.
           eapply step_term_term_plus. eassumption.
           eapply step_case_false. eassumption.
Qed.
