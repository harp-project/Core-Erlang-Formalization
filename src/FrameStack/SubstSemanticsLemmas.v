(**
  This file contains numerous semantic properties about the frame stack semantics
  and the termination relation of Core Erlang.
 *)
From CoreErlang.FrameStack Require Export
  SubstSemantics
  SubstSemanticsLabeledLemmas
  Termination.
Import ListNotations.

(**
  Equivalence between labeled and unlabeled semantics
  *)
Theorem step_unlabeled_to_labeled:
  forall Fs r Fs' r',
  ⟨ Fs, r ⟩ --> ⟨Fs', r'⟩ ->
  exists l, ⟨ Fs, r ⟩ -⌊l⌋->ₗ ⟨Fs', r'⟩.
Proof.
  intros Fs e Fs' v H.
  inv H; eexists; constructor; try destruct ident; try apply H0; try assumption; try apply H1; reflexivity.
Qed.

Theorem step_labeled_to_unlabeled:
  forall Fs r Fs' r' l,
  ⟨ Fs, r ⟩ -⌊l⌋->ₗ ⟨Fs', r'⟩ ->
  ⟨ Fs, r ⟩ --> ⟨Fs', r'⟩.
Proof.
  intros Fs e Fs' v l H.
  inv H; econstructor; try destruct ident; try apply H1; try apply H0; try assumption; reflexivity.
Qed.

Corollary step_rt_unlabeled_to_labeled :
  forall Fs r Fs' r' k,
    ⟨Fs, r⟩ -[k]-> ⟨Fs', r'⟩ ->
      exists l, ⟨Fs, r⟩ -[k, l]->ₗ ⟨Fs', r'⟩.
Proof.
  intros. induction H.
  * exists []. constructor.
  * destruct IHstep_rt as [ls D2].
    apply step_unlabeled_to_labeled in H as [l1 D1].
    exists (match l1 with
            | None => ls
            | Some x => x :: ls
            end).
    econstructor; try eassumption.
    reflexivity.
Qed.

Corollary step_rt_labeled_to_unlabeled :
  forall Fs r Fs' r' k l,
    ⟨Fs, r⟩ -[k, l]->ₗ ⟨Fs', r'⟩ ->
      ⟨Fs, r⟩ -[k]-> ⟨Fs', r'⟩.
Proof.
  intros. induction H.
  * constructor.
  * apply step_labeled_to_unlabeled in H.
    econstructor; eassumption.
Qed.

Theorem step_unlabeled_labeled_determinism_one_step :
  forall Fs e Fs' v l Fs'' v',
  ⟨ Fs, e ⟩ --> ⟨Fs', v⟩ ->
  ⟨ Fs, e ⟩ -⌊l⌋->ₗ ⟨Fs'', v'⟩ -> Fs' = Fs'' /\ v = v'.
Proof.
  intros Fs e Fs' v l Fs'' v' H H0.
  apply step_unlabeled_to_labeled in H as [l0 H].
  pose proof (step_determinism H H0) as [? ?].
  firstorder.
Qed.

Theorem step_unlabeled_labeled_determinism_all_step :
  forall k 
         Fs e Fs' v l Fs'' v',
  ⟨ Fs, e ⟩ -[k]-> ⟨Fs', v⟩ ->
  ⟨ Fs, e ⟩ -[k , l]->ₗ ⟨Fs'', v'⟩ -> Fs' = Fs'' /\ v = v'.
Proof.
  intros.
  apply step_rt_unlabeled_to_labeled in H as [l0 H].
  epose proof (step_rt_determinism H H0). firstorder.
Qed.

Ltac translate_to_labeled :=
repeat match goal with
| [H : ⟨ _, _ ⟩ --> ⟨_, _⟩ |- _] => apply step_unlabeled_to_labeled in H as [? ?]
| [H : ⟨ _, _ ⟩ -[_]-> ⟨_, _⟩ |- _] => apply step_rt_unlabeled_to_labeled in H as [? ?]
end.

(** Properties of the semantics *)
Theorem step_determinism {e e' fs fs'} :
  ⟨ fs, e ⟩ --> ⟨fs', e'⟩ ->
  (forall fs'' e'', ⟨fs, e⟩ --> ⟨fs'', e''⟩ -> fs'' = fs' /\ e'' = e').
Proof.
  intros.
  translate_to_labeled.
  pose proof (step_determinism H H0).
  firstorder.
Qed.

Theorem value_nostep v :
  is_result v ->
  forall fs' v', ⟨ [], v ⟩ --> ⟨fs' , v'⟩ -> False.
Proof.
  intros H fs' v' HD.
  translate_to_labeled.
  by apply value_nostep in H0.
Qed.

Theorem step_rt_determinism {e v fs fs' k} :
  ⟨fs, e⟩ -[k]-> ⟨fs', v⟩
->
  (forall fs'' v', ⟨fs, e⟩ -[k]-> ⟨fs'', v'⟩ -> fs' = fs'' /\ v' = v).
Proof.
  intros.
  translate_to_labeled.
  pose proof (step_rt_determinism H H0).
  firstorder.
Qed.

Theorem step_closedness : forall F e F' e',
   ⟨ F, e ⟩ --> ⟨ F', e' ⟩ -> FSCLOSED F -> REDCLOSED e
->
  FSCLOSED F' /\ REDCLOSED e'.
Proof.
  intros.
  translate_to_labeled.
  apply step_closedness in H; by eauto.
Qed.

Corollary step_any_closedness : forall Fs Fs' e v k,
   ⟨ Fs, e ⟩ -[k]-> ⟨Fs', v⟩ -> FSCLOSED Fs -> REDCLOSED e
->
  REDCLOSED v /\ FSCLOSED Fs'.
Proof.
  intros.
  translate_to_labeled.
  apply step_any_closedness in H; by eauto.
Qed.

Theorem transitive_eval : forall {n Fs Fs' e e'},
  ⟨ Fs, e ⟩ -[n]-> ⟨ Fs', e' ⟩ -> forall {n' Fs'' e''}, ⟨ Fs', e' ⟩ -[n']-> ⟨ Fs'', e'' ⟩
->
  ⟨ Fs, e ⟩ -[n + n']-> ⟨ Fs'', e''⟩.
Proof.
  intros.
  translate_to_labeled.
  pose proof transitive_eval H H0 as D.
  by apply step_rt_labeled_to_unlabeled in D.
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

Theorem semantic_iff_termination :
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
      - econstructor. econstructor; try eassumption.
        eassumption.
    * eexists. split.
      - exact Hres0.
      - econstructor. econstructor; eassumption.
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
  intros. apply semantic_iff_termination in H. destruct H. destruct n.
  * destruct H. inv H.
    - subst. inversion H1; subst. inversion H0.
    - subst. inversion H1; subst. inversion H0.
  * destruct H.
    inv H1. subst. apply (step_determinism H0) in H3. inv H3.
    assert (exists y, is_result y /\ ⟨ fs', e' ⟩ -[ n ]-> ⟨ [], y ⟩). { 
      eexists. eauto. }
    apply ex_intro in H6. apply semantic_iff_termination in H1.
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
  intros. apply semantic_iff_termination.
  apply semantic_iff_termination in H0. destruct H0, H0.
  pose proof (transitive_eval H H2). replace (k+(n-k)) with n in H3 by lia.
  eexists. eauto.
Qed.

Corollary step_term_term_plus :
  forall k k2 fs e fs' e', 
  ⟨fs, e⟩ -[k]-> ⟨fs', e'⟩ -> | fs', e' | k2 ↓
->
  | fs, e | k + k2 ↓.
Proof.
  intros. apply semantic_iff_termination.
  apply semantic_iff_termination in H0. destruct H0, H0.
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
  (* this theorem is not simply a consequence of equivalence between labeled and unlabeled semantics *)
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
  intros.
  translate_to_labeled.
  eapply frame_indep_step in H.
  by apply step_labeled_to_unlabeled in H.
Qed.

Theorem frame_indep_red : forall e F Fs e',
  ⟨ F :: Fs, e ⟩ --> ⟨ Fs, e' ⟩
->
  forall Fs', ⟨ F :: Fs', e ⟩ --> ⟨ Fs', e' ⟩.
Proof.
  intros.
  translate_to_labeled.
  eapply frame_indep_red in H.
  by apply step_labeled_to_unlabeled in H.
Qed.

Theorem frame_indep_core : forall k e Fs Fs' v,
  ⟨ Fs, e ⟩ -[k]-> ⟨ Fs', v ⟩
->
  forall Fs'', ⟨ Fs ++ Fs'', e ⟩ -[k]-> ⟨ Fs' ++ Fs'', v ⟩.
Proof.
  intros.
  translate_to_labeled.
  eapply frame_indep_core in H.
  by eapply step_rt_labeled_to_unlabeled in H.
Qed.

Theorem frame_indep_nil : forall k e Fs v,
  ⟨ Fs, e ⟩ -[k]-> ⟨ [], v ⟩
->
  forall Fs', ⟨ Fs ++ Fs', e ⟩ -[k]-> ⟨ Fs', v ⟩.
Proof.
  intros.
  translate_to_labeled.
  eapply frame_indep_nil in H.
  by eapply step_rt_labeled_to_unlabeled in H.
Qed.

Lemma params_eval :
  forall vals ident vl exps e Fs (v : Val),
  ⟨ FParams ident vl ((map VVal vals) ++ e :: exps) :: Fs, RValSeq [v]⟩ -[1 + 2 * length vals]->
  ⟨ FParams ident (vl ++ v :: vals) exps :: Fs, e⟩.
Proof.
  intros.
  apply step_rt_labeled_to_unlabeled with (l := []).
  by apply params_eval.
Qed.

Lemma params_eval_create :
  forall vals ident vl Fs (v : Val) r eff',
  Some (r, eff') = create_result ident (vl ++ v :: vals) -> (* TODO: side effects *)
  ⟨ FParams ident vl (map VVal vals) :: Fs, RValSeq [v]⟩ -[1 + 2 * length vals]->
  ⟨ Fs, r ⟩.
Proof.
  intros.
  eapply step_rt_labeled_to_unlabeled.
  by apply params_eval_create.
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

Lemma Private_params_exp_eval_empty :
  forall exps ident vl Fs (e : Exp) n ,
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
    pose proof (Hd' := Hd).
    eapply frame_indep_nil in Hd.
    eapply term_step_term in H. 2: exact Hd. simpl in *.
    inv Hres.
    - do 2 eexists. split. 2: split.
      2: {
        eapply transitive_eval.
        eapply frame_indep_nil in Hd'. exact Hd'.
        eapply step_trans. econstructor. reflexivity.
        apply step_refl.
      }
      constructor.
      inv H. lia.
    - destruct vs. 2: destruct vs. 1, 3: inv H. (* vs is a singleton *)
      inv H. pose proof (create_result_is_not_box ident (vl ++ [v]) res l H3).
      destruct H as [H|[e' ?]]; subst. inv H.
      + (* create_result is an exception *)
        do 2 eexists. split. 2: split.
        2: {
          eapply transitive_eval.
          eapply frame_indep_nil in Hd'. exact Hd'.
          eapply step_trans.
          eapply eval_cool_params; try eassumption.
          apply step_refl.
        }
        constructor. lia.
      + (* create_result is a valseq *)
        do 2 eexists. split. 2: split.
        2: {
          eapply transitive_eval.
          eapply frame_indep_nil in Hd'. exact Hd'.
          eapply step_trans.
          eapply eval_cool_params; try eassumption.
          apply step_refl.
        }
        constructor. lia.
      (* if create_result was a function application: *)
      + apply H0 in H7 as H7'.
        destruct H7' as [res2 [k2 [Hres2 [Hd2 Hlt2]]]]. 2: lia.
        pose proof (Hd2' := Hd2).
        eapply frame_indep_nil in Hd2.
        eapply term_step_term in H7. 2: exact Hd2.
        do 2 eexists. split. 2: split.
        2: {
          eapply transitive_eval.
          eapply frame_indep_nil in Hd'. exact Hd'.
          eapply step_trans. econstructor. eassumption.
          exact Hd2'.
        }
        auto.
        lia.
  * apply H0 in H as H'. 2: lia.
    destruct H' as [res [k [Hres [Hd Hlt]]]].
    pose proof (Hd' := Hd).
    eapply frame_indep_nil in Hd.
    eapply term_step_term in H. 2: exact Hd. simpl in *.
    inv Hres.
    - inv H. do 2 eexists. split. 2: split.
      2: {
        eapply transitive_eval.
        eapply frame_indep_nil in Hd'. exact Hd'.
        eapply step_trans. econstructor. reflexivity.
        apply step_refl.
      }
      constructor.
      lia.
    - destruct vs. 2: destruct vs. 1, 3: inv H.
      inv H. apply IHexps in H2 as [res2 [k2 [Hres2 [Hd2 Hlt2]]]].
      2: {
        intros. eapply H0. lia. eassumption.
      }
      do 2 eexists. split. 2: split.
      2: {
        eapply transitive_eval.
        eapply frame_indep_nil in Hd'. exact Hd'.
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
    constructor. lia.
  * inv HD.
    - (* matching first pattern *)
      apply IH in H5 as HH. 2: lia. destruct HH as [i [Hdgr Hlt]].
      apply semantic_iff_termination in Hdgr as [gr [Hgr Hdgr]]. (* guard result *)
      eapply frame_indep_nil in Hdgr as Hlia.
      eapply frame_indep_nil in Hdgr.
      eapply term_step_term in H5.
      2: exact Hlia. simpl in *. inv Hgr.
      + (* guard is an exception *) inv H5.
        exists (RExc (cl, v1, v2)), (1 + (i + 1)). split; auto.
        split. 2: lia.
        econstructor. constructor. exact H4. eapply transitive_eval.
          exact Hdgr. econstructor. constructor. congruence. constructor.
      + inv H5.
        ** (* guard is true *)
           apply IH in H0 as HH. 2: lia.
           destruct HH as [j [Hdcl Hlt2]].
           apply semantic_iff_termination in Hdcl as [clr [Hclr Hdcl]]. (* clause result *)
           eapply frame_indep_nil in Hdcl. simpl in *.
           assert (⟨ [FCase2 vs e2.[list_subst vs' idsubst] l], RValSeq [VLit "true"%string] ⟩ -[1]->
           ⟨ [], e2.[list_subst vs' idsubst] ⟩). {
             econstructor. constructor. constructor.
           }
           epose proof (transitive_eval Hdgr H).
           epose proof (transitive_eval H1 Hdcl).
           exists clr, (1 + (i + 1 + j)). split; auto.
           split. 2: lia.
           econstructor. apply eval_step_case_match; eassumption.
           eassumption.
        ** (* guard is false *)
           apply IHl in H0 as [res [j [Hres [HD Htl]]]]; auto.
           2: {
             intros. eapply IH. lia. exact H1.
           }
           exists res, (1 + (i + S j)). split. 2: split. auto. 2: lia.
           econstructor. apply eval_step_case_match. eassumption.
           eapply transitive_eval. exact Hdgr.
           econstructor. constructor. assumption.
    - (* not matching first pattern *)
      apply IHl in H5 as [res [j [Hres [HD Htl]]]]; auto.
      2: {
        intros. eapply IH. lia. exact H0.
      }
      exists res, (1 + j). split. 2: split. auto. 2: lia.
      econstructor. now apply eval_step_case_not_match. assumption.
Qed.


Lemma term_empty : forall x Fs (e : Exp),
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
      2: {
        intros. epose proof (H m ltac:(slia) Fs0 e0 H1) as [j [HD Hj]].
        apply semantic_iff_termination in HD as [res [Hres Hr]].
        do 2 eexists. split. 2: split. all: eassumption.
      }
      destruct HH2 as [res [k [Hres [Hd Hlt]]]].
      eexists. split. do 2 constructor. congruence.
      eapply semantic_iff_termination. eexists.
      split. 2: exact Hd. auto. lia.
  * destruct el. (* proof is same as above, tricks to avoid RBox *)
    - eexists. split. constructor. eapply cool_params_0.
      congruence. reflexivity. do 4 constructor; auto. intros.
      inv H3. lia.
    - inv H3. destruct_scopes.
      eapply Private_params_exp_eval_empty in H8 as HH2; auto.
      2: {
        intros. epose proof (H m ltac:(slia) Fs0 e0 H1) as [j [HD Hj]].
        apply semantic_iff_termination in HD as [res [Hres Hr]].
        do 2 eexists. split. 2: split. all: eassumption.
      }
      destruct HH2 as [res [k [Hres [Hd Hlt]]]].
      eexists. split. do 2 constructor. congruence.
      eapply semantic_iff_termination. eexists.
      split. 2: exact Hd. auto. lia.
  * eexists. split. do 5 constructor; slia. lia.
  * destruct_scopes.
    eapply Private_params_exp_eval_empty in H3 as HH2; auto.
    2: {
      intros. epose proof (H m ltac:(slia) Fs0 e H1) as [j [HD Hj]].
      apply semantic_iff_termination in HD as [res [Hres Hr]].
      do 2 eexists. split. 2: split. all: eassumption.
    }
    destruct HH2 as [res [k0 [Hres [Hd Hlt]]]].
    eexists. split. constructor.
    eapply semantic_iff_termination. eexists.
    split. 2: exact Hd. auto. lia.
  * (* Call is trickier, because first the module, then the function
       expression has to be evaluated *)
    destruct_scopes. apply H in H3 as HD1; auto.
    destruct HD1 as [k1 [D1 Hlia1]].
    apply semantic_iff_termination in D1 as [res1 [Hres1 Hr1]].
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
    - inv H3.
      apply H in H1 as HD2; auto. 2: lia.
      destruct HD2 as [k2 [D2 Hlia2]].
      apply semantic_iff_termination in D2 as [res2 [Hres2 Hr2]].
      eapply frame_indep_nil in Hr2 as Hr2'.
      eapply frame_indep_nil in Hr2.
      eapply term_step_term in H1.
      2: exact Hr2. simpl in *.
      inv Hres2.
      (* funexp exception *)
      + inv H1. eexists. split. constructor.
        eapply step_term_term_plus. exact Hr1'. constructor.
        eapply step_term_term_plus. exact Hr2'. constructor.
        congruence. constructor. constructor; auto. lia.
      (* moduleexp value *)
      + inv H1. destruct el. (* tricks to avoid RBox *)
        ** inv H2. eexists. split. 
           constructor.
           eapply step_term_term_plus. exact Hr1'. constructor.
           eapply step_term_term_plus. exact Hr2'. constructor.
           eapply cool_params_0.
           congruence. eassumption.
           (* here is this different from the previous *)
           simpl in H5.
           destruct v, f0; try destruct l; try destruct l0; try invSome; try now do 2 constructor; auto.
           -- destruct l1.
              ++ eapply eq_sym, (eval_is_result) in H5; eauto.
                 now constructor.
              ++ inv H5.
           -- destruct l1 eqn: a.
              ++ eapply eq_sym, (eval_is_result) in H5; eauto.
                 now constructor.
              ++ inv H5. unfold badfun.
                 do 2 constructor.
           -- lia.
        ** inv H2.
           eapply Private_params_exp_eval_empty in H10 as HD3; auto.
           2: {
             intros. epose proof (H m0 ltac:(slia) Fs0 e0 H1) as [j [HD Hj]].
             apply semantic_iff_termination in HD as [res [Hres Hr]].
             do 2 eexists. split. 2: split. all: eassumption.
           }
           destruct HD3 as [res3 [k3 [Hres3 [Hd3 Hlt3]]]].
           eexists. split.
           constructor.
           eapply step_term_term_plus. exact Hr1'. constructor.
           eapply step_term_term_plus. exact Hr2'. constructor.
           constructor. congruence.
           eapply semantic_iff_termination. eexists.
           split. 2: exact Hd3. auto. lia.
  * destruct el. (* tricks to avoid RBox *)
    - inv H3. eexists. split. constructor. eapply cool_params_0.
      congruence. eassumption.
      (* here is this different from the previous *)
      simpl. constructor. 2: lia. cbn in H5. 
      destruct (primop_eval f []) eqn: pe. 2: invSome.
      destruct p. inv H5. eapply primop_eval_is_exception with (f:=f) in pe as [? ?]. subst.
      destruct x as [[? ?] ?]. constructor.
    - inv H3. destruct_scopes.
      eapply Private_params_exp_eval_empty in H8 as HH2; auto.
      2: {
        intros. epose proof (H m ltac:(slia) Fs0 e0 H1) as [j [HD Hj]].
        apply semantic_iff_termination in HD as [res [Hres Hr]].
        do 2 eexists. split. 2: split. all: eassumption.
      }
      destruct HH2 as [res [k [Hres [Hd Hlt]]]].
      eexists. split. do 2 constructor. congruence.
      eapply semantic_iff_termination. eexists.
      split. 2: exact Hd. auto. lia.
  (* application is harder, because first, the function parameter needs
     to be evaluated, then we do a case separation, whether l = [].
     Everytime an exception occurs, that needs to be propagated -> hence
     the number of case separations. *)
  * apply H in H3 as H3'. destruct H3' as [j [Hj Hlt1]]. 2: lia.
    apply semantic_iff_termination in Hj as [res [Hres Hr]].
    eapply frame_indep_nil in Hr as Hlia1.
    eapply frame_indep_nil in Hr. eapply term_step_term in H3.
    2: exact Hlia1. simpl in *.
    destruct l. (* tricks to avoid RBox *)
    - inv Hres. (* exception result? *)
      + exists (2 + j). split. constructor.
        eapply step_term_term. exact Hr. 2: lia.
        replace (S j - j) with 1 by lia.
        constructor. reflexivity. constructor. auto.
        inv H3. lia.
      + inv H3. inv H1. destruct (create_result_is_not_box (IApp v) [] res l).
        ** assumption.
        ** exists (3 + j). split. constructor.
           eapply step_term_term. exact Hr. 2: lia.
           replace (S (S j) - j) with 2 by lia.
           constructor. econstructor. congruence. eassumption.
           now constructor.
           lia.
        ** inv H0. apply H in H8 as H8'. 2: lia.
           destruct H8' as [i [Hd2 Hlt2]].
           exists (1 + (j + 2 + i)). split. constructor.
           eapply step_term_term. exact Hr. 2: lia.
           replace (j + 2 + i - j) with (2 + i) by lia.
           constructor. econstructor. congruence. eassumption.
           assumption. lia.
    - inv Hres.
      + exists (2 + j). split. constructor.
        eapply step_term_term. exact Hr. 2: lia.
        replace (S j - j) with 1 by lia.
        constructor. reflexivity. constructor. auto.
        inv H3. lia.
      + inv H3. inv H1. destruct_scopes.
        eapply Private_params_exp_eval_empty in H9 as HH2; auto.
        2: {
          intros. epose proof (H m ltac:(slia) Fs0 e1 H1) as [i [Hd2 Hi]].
          apply semantic_iff_termination in Hd2
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
        constructor. apply semantic_iff_termination.
        eexists. split. 2: exact Hd2. assumption. lia.
  * apply H in H3 as HH. 2: lia.
    destruct HH as [i [Hi Hlt]].
    apply semantic_iff_termination in Hi as [res [Hres Hr]].
    eapply frame_indep_nil in Hr as Hlia1.
    eapply frame_indep_nil in Hr.
    eapply term_step_term in H3. 2: exact Hlia1.
    inv Hres. (* tail exception or not *)
    - exists (S i + 1).
      split. 2: inv H3; lia.
      simpl. constructor. apply semantic_iff_termination.
      exists (RExc (cl, v1, v2)). split; auto. eapply transitive_eval.
      exact Hr. do 2 econstructor. reflexivity.
    - inv H3. apply H in H1 as HH. 2: lia.
      destruct HH as [j [Hj Hltj]].
      simpl in *. apply semantic_iff_termination in Hj as [hdres [Hr2 Hd2]].
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
        replace (i + S (j + 1) - (i + 1 + j)) with 1 by lia.
        constructor. reflexivity. do 2 constructor; auto.
        lia.
        inv H1. lia.
      + exists (1 + (i + (1 + (j + 1) ))). split.
        simpl. constructor. eapply step_term_term.
        exact Hd2. inv H1.
        replace (i + S (j + 1) - (i + 1 + j)) with 1 by lia.
        constructor. do 4 constructor; inv H0; now inv H3.
        lia.
        inv H1. lia.
  * apply H in H3 as HH. 2: lia.
    destruct HH as [i [Hi Hlt]].
    apply semantic_iff_termination in Hi as [res [Hres Hr]].
    eapply frame_indep_nil in Hr as Hlia1.
    eapply frame_indep_nil in Hr.
    eapply term_step_term in H3. 2: exact Hlia1.
    inv Hres. (* tail exception or not *)
    - exists (S i + 1).
      split. 2: inv H3; lia.
      simpl. constructor. apply semantic_iff_termination.
      exists (RExc (cl, v1, v2)). split; auto. eapply transitive_eval.
      exact Hr. do 2 econstructor. reflexivity.
    - inv H3. apply H in H7 as HH. 2: lia.
      destruct HH as [j [Hj Hltj]].
      simpl in *. apply semantic_iff_termination in Hj as [hdres [Hr2 Hd2]].
      eapply frame_indep_nil in Hd2 as Hlia2.
      eapply term_step_term in H7. 2: exact Hlia2.
      assert (⟨ [FLet (Datatypes.length vs) e2], RValSeq vs ⟩ -[1]-> 
      ⟨ [], e2.[list_subst vs idsubst] ⟩). {
        repeat econstructor.
      }
      eapply (transitive_eval Hr) in H0.
      eapply (transitive_eval H0) in Hd2.
      exists (1 + (i + (1 + j))). split. 2: inv Hr2; inv H7; lia.
      constructor. eapply step_term_term. exact Hd2.
      replace (i + (1 + j) - (i + 1 + j)) with 0 by lia.
      now constructor.
      lia.
  (* Sequencing is basically same as let *)
  * apply H in H3 as HH. 2: lia.
    destruct HH as [i [Hi Hlt]].
    apply semantic_iff_termination in Hi as [res [Hres Hr]].
    eapply frame_indep_nil in Hr as Hlia1.
    eapply frame_indep_nil in Hr.
    eapply term_step_term in H3. 2: exact Hlia1.
    inv Hres. (* tail exception or not *)
    - exists (S i + 1).
      split. 2: inv H3; lia.
      simpl. constructor. apply semantic_iff_termination.
      exists (RExc (cl, v1, v2)). split; auto. eapply transitive_eval.
      exact Hr. do 2 econstructor. reflexivity.
    - inv H3. apply H in H1 as HH. 2: lia.
      destruct HH as [j [Hj Hltj]].
      simpl in *. apply semantic_iff_termination in Hj as [hdres [Hr2 Hd2]].
      eapply frame_indep_nil in Hd2 as Hlia2.
      eapply term_step_term in H1. 2: exact Hlia2.
      assert (⟨ [FSeq e2], RValSeq [v] ⟩ -[1]-> 
      ⟨ [], e2 ⟩). {
        repeat econstructor.
      }
      eapply (transitive_eval Hr) in H0.
      eapply (transitive_eval H0) in Hd2.
      exists (1 + (i + (1 + j))). split. 2: inv Hr2; inv H1; lia.
      constructor. eapply step_term_term. exact Hd2.
      replace (i + (1 + j) - (i + 1 + j)) with 0 by lia.
      now constructor.
      lia.
  * eexists. split. constructor. do 3 constructor; auto.
    lia.
  (* for case: list_length_ind on H3 (or structural could also be enough) *)
  * apply H in H3 as HH. 2: lia. destruct HH as [k1 [Hd1 Hlt1]].
    apply semantic_iff_termination in Hd1 as [r1 [Hr Hd]].
    eapply frame_indep_nil in Hd as Hlia1.
    eapply frame_indep_nil in Hd.
    eapply term_step_term in H3. 2: exact Hlia1.
    simpl in *.
    inv Hr. (* exception? *)
    + exists (1 + k1 + 1). split. 2: inv H3; lia.
      simpl. constructor. eapply step_term_term. exact Hd.
      replace (k1 + 1 - k1) with 1 by lia.
      constructor. reflexivity. do 2 constructor; auto. lia.
    + epose proof (Private_term_empty_case l Fs vs (k - k1) _ H3) as
        [res [k2 [Hres [Hd2 Hlt2]]]].
      Unshelve. 2: {
        intros. eapply H. lia. eassumption.
      }
      pose proof (transitive_eval Hd Hd2).
      exists (S (k1 + k2)). split. 2: lia.
      constructor.
      apply semantic_iff_termination. exists res. now split.
      all: auto.
  * apply H in H4 as [i [Hd Hlt]].
    eexists. split. econstructor. reflexivity. exact Hd. lia. lia.
  * apply H in H3 as HH. 2: lia.
    destruct HH as [i [Hd Hlt]].
    apply semantic_iff_termination in Hd as [r [Hres Hd]].
    eapply frame_indep_nil in Hd as Hlia.
    eapply frame_indep_nil in Hd.
    eapply term_step_term in H3. 2: exact Hlia.
    simpl in *.
    inv Hres. (* exception or not *)
    - inv H3. (* 2: { inv H7. } *)
      apply H in H1 as [j [Hd2 Hlt2]]. 2: lia.
      exists (1 + (i + (1 + j))). split. 2: lia.
      constructor. eapply step_term_term. exact Hd. 2: lia.
      replace (i + (1 + j) - i) with (S j) by lia.
      now constructor.
    - inv H3.
      apply H in H9 as [j [Hd2 Hlt2]]. 2: lia.
      exists (1 + (i + (1 + j))). split. 2: lia.
      constructor. eapply step_term_term. exact Hd. 2: lia.
      replace (i + (1 + j) - i) with (S j) by lia.
      now constructor.
  * eexists. split. now constructor. lia.
Qed.

(* NOTE: This is not a duplicate! Do not remove! *)
(* sufficient to prove it for Exp, since value sequences and
   exceptions terminate in 0/1 step by definition in the
   empty stack (and RBox does not terminate!). *)
Corollary term_eval_empty : forall x Fs (e : Exp),
  | Fs, e | x ↓ ->
  exists res k, is_result res /\ ⟨ [], e ⟩ -[k]-> ⟨ [], res ⟩ /\ k <= x.
Proof.
  intros. apply term_empty in H; auto. destruct H as [k [H Hlt]].
  apply semantic_iff_termination in H as [r [Hr H]].
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

(* H1 : ⟨ FParams ident vl el :: Fs, e ⟩ -[ k ]-> ⟨ [], r ⟩
______________________________________(1/1)
∃ j : nat,
  ⟨ Fs, to_Exp ident (map VVal vl ++ e :: el) ⟩ -[ j ]-> ⟨ [], r ⟩ *)

Lemma to_Exp_eval :
  forall (vals : list Val) (exp : Exp) (exps : list Exp) ident Fs,
   (ident = IMap -> exists n, length exps + length vals = 1 + 2*n) -> (* invariant for maps *)
   exists k, ⟨Fs, to_Exp ident (map VVal vals ++ exp :: exps)⟩ -[k]-> ⟨ FParams ident vals exps :: Fs, exp ⟩.
Proof.
  (* these subproofs are the same almost for most lang. elements
     except for the number of initialisation steps *)
  intros. destruct ident.
  * destruct vals; simpl.
    - eexists. econstructor. constructor.
      econstructor. constructor. congruence.
      constructor.
    - eexists. econstructor. constructor.
      econstructor. constructor. congruence.
      econstructor. constructor.
      apply params_eval.
  * destruct vals; simpl.
    - eexists. econstructor. constructor.
      econstructor. constructor. congruence.
      constructor.
    - eexists. econstructor. constructor.
      econstructor. constructor. congruence.
      econstructor. constructor.
      apply params_eval.
  (* maps require special attention *)
  * destruct vals; simpl.
    - destruct exps.
      + specialize (H eq_refl) as [n H]. simpl in H. lia.
      + specialize (H eq_refl) as [n H]. simpl in H.
        eexists. econstructor. constructor.
        rewrite deflatten_flatten with (n := n). 2: lia.
        constructor.
    - destruct vals.
      + simpl. specialize (H eq_refl) as [n H].
        eexists. econstructor. constructor.
        econstructor. constructor.
        econstructor. constructor.
        simpl in H.
        rewrite deflatten_flatten with (n := n). 2: lia.
        constructor.
      + simpl. specialize (H eq_refl) as [n H].
        eexists. econstructor. constructor.
        econstructor. constructor.
        econstructor. constructor.
        econstructor. constructor.
        simpl in H.
        rewrite deflatten_flatten with (n := n).
        2: rewrite length_app, length_map; slia.
        apply params_eval.
  (***)
  * destruct vals; simpl.
    - eexists. econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor. congruence.
      constructor.
    - eexists. econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor. congruence.
      econstructor. constructor.
      apply params_eval.
  * destruct vals; simpl.
    - eexists. econstructor. constructor.
      econstructor. constructor. congruence.
      constructor.
    - eexists. econstructor. constructor.
      econstructor. constructor. congruence.
      econstructor. constructor.
      apply params_eval.
  * destruct vals; simpl.
    - eexists. econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor. congruence.
      constructor.
    - eexists. econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor.
      econstructor. constructor. congruence.
      econstructor. constructor.
      apply params_eval.
Qed.

Corollary params_eval_VValues :
 forall (vals : list Val) (Fs : list Frame),
 ⟨ Fs, °EValues (map VVal vals)⟩ -[
   2 + 2 * base.length vals ]-> ⟨ Fs, RValSeq vals ⟩.
Proof.
  intros. destruct vals.
  * simpl. econstructor. constructor.
    econstructor. econstructor. congruence. reflexivity.
    constructor.
  * simpl. econstructor. constructor.
    econstructor. constructor. congruence.
    econstructor. constructor.
    pose proof params_eval_create vals IValues [] Fs v (RValSeq (v::vals)) None eq_refl.
    replace (length vals + S (length vals + 0)) with
            (1 + 2 * length vals) by lia.
    assumption.
Qed.




Theorem put_back :
  forall F Fs (e : Exp) r k,
    FrameWf F -> (* required by map frames *)
    is_result r -> (* required by special case frames *)
    ⟨F :: Fs, e⟩ -[k]-> ⟨[], r⟩
  ->
    exists j, ⟨Fs, plug_f F e⟩ -[j]-> ⟨[], r⟩.
Proof.
  destruct F; intros; simpl.
  all: try by (eexists; econstructor; [ constructor | eassumption]).
  * eexists. econstructor. constructor.
    econstructor. constructor.
    econstructor. constructor. eassumption.
  (* parameter list frames: *)
  * pose proof (to_Exp_eval vl e el ident Fs H) as [k0 X].
    eexists.
    eapply transitive_eval. exact X.
    exact H1.
  (***)
  * eexists.
    econstructor. constructor.
    econstructor. constructor.
    econstructor. constructor. eassumption.
  (* Special "case" frame: *)
  * (* independent evaluation of e *)
    assert (terminates_in_k_sem (FCase2 lv ex le :: Fs) e k) as X. {
      exists r. split; eassumption.
    }
    apply semantic_iff_termination in X.
    apply term_empty in X as [k0 [X Hk0]].
    eapply term_eval_empty in X as [res [i [Hres [X Hi]]]].
    eapply frame_indep_nil in X as X'.
    replace k with (i+(k-i)) in H1 by lia.
    epose proof (transitive_eval_rev _ _ _ _ _ X' _ _ _ H1) as XX.
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
      eapply frame_indep_nil in X as X'. eapply transitive_eval.
      exact X'. clear X'. econstructor. constructor. reflexivity.
      eapply frame_indep_nil in X.
      replace k with (i+(k-i)) in H1 by lia.
      epose proof (transitive_eval_rev _ _ _ _ _ X _ _ _ H1) as XX.
      inv XX. inv H3. exact H6.
    (* true guard *)
    - eexists.
      econstructor. constructor.
      econstructor. constructor.
      econstructor. econstructor. congruence. reflexivity.
      econstructor. constructor. reflexivity.
      simpl. do 2 rewrite idsubst_is_id_exp.
      eapply frame_indep_nil in X. eapply transitive_eval.
      exact X. clear X. econstructor. constructor.
      eassumption.
    (* false guard *)
    - eexists.
      econstructor. constructor.
      econstructor. constructor.
      econstructor. econstructor. congruence. reflexivity.
      econstructor. constructor. reflexivity.
      simpl. do 2 rewrite idsubst_is_id_exp.
      eapply frame_indep_nil in X. eapply transitive_eval.
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
      eapply transitive_eval.
      apply params_eval_VValues. eassumption.
Qed.

Corollary put_back_term : forall F (e : Exp) Fs, FrameWf F ->
  | F :: Fs, e | ↓ -> | Fs, plug_f F e | ↓.
Proof.
  intros.
  destruct H0. apply semantic_iff_termination in H0.
  destruct H0 as [res [Hres H0]].
  apply put_back in H0; try assumption.
  destruct H0. exists x0.
  apply semantic_iff_termination. eexists. split; eassumption.
Qed.

Corollary transitive_eval_rev_lt :
  forall {Fs r Fs' r' k1}, ⟨Fs, r⟩ -[k1]-> ⟨Fs', r'⟩ ->
    forall {Fs'' r'' k2}, k2 <= k1 -> ⟨Fs, r⟩ -[k2]-> ⟨Fs'', r''⟩ ->
      ⟨Fs'', r''⟩ -[k1 - k2]-> ⟨Fs', r'⟩.
Proof.
  intros.
  replace k1 with (k2 + (k1 - k2)) in H by lia.
  eapply transitive_eval_rev in H. 2: eassumption.
  assumption.
Qed.

Theorem put_back_rev :
  forall F Fs (e : Exp) r k,
    FrameWf F -> (* required by map frames *)
    is_result r -> (* required by special case frames *)
    ⟨Fs, plug_f F e⟩ -[k]-> ⟨[], r⟩
  ->
    exists j, ⟨F :: Fs, e⟩ -[j]-> ⟨[], r⟩.
Proof.
  destruct F; intros; simpl in *.
  all: try by (inv H1; try inv_result; inv H2;
    eexists; eassumption).
  * inv H1; try inv_result. inv H2.
    inv H3. inv H1.
    inv H2. inv H1.
    eexists; eassumption.
  (* parameter list frame: *)
  * pose proof (to_Exp_eval vl e el ident Fs H) as [k0 X].
    assert (k0 <= k \/ k0 > k) as [Hlt | Hlt] by lia.
    - pose proof (transitive_eval_rev_lt H1 Hlt X).
      eexists. eassumption.
    (* k0 > k cannot happen: *)
    - unshelve (epose proof (transitive_eval_rev_lt X _ H1)).
      lia. inv H2.
      apply value_nostep in H4 as [].
      assumption.
  * inv H1; try inv_result. inv H2.
    inv H3. inv H1.
    inv H2. inv H1.
    eexists; eassumption.
  (* special "case" frame *)
  * inv H1. inv_result. inv H2.
    inv H3. inv H1.
    inv H2. inv H1. simpl in H9. invSome.
    inv H3. inv H1. simpl in *. invSome.
    simpl in *.
    do 2 rewrite idsubst_is_id_exp in H2.
    (* extract independent evaluation of e: *)
    assert (terminates_in_k_sem (FCase2 [] ex
      [([], ˝ VLit "true"%string,
        ° ECase (° EValues (map VVal lv)) le)] :: Fs) e k) as X. {
      exists r. split; eassumption.
    }
    apply semantic_iff_termination in X.
    eapply term_eval_empty in X as [res [i [Hres [X Hi]]]].
    (***)
    eapply frame_indep_nil in X as X'.
    pose proof (transitive_eval_rev_lt H2 Hi X') as XX.
    clear X' H2.
    (* check what's the guard result: exception, false, or true *)
    inv XX. inv Hres; inv H2.
    (* exception *)
    - eexists.
      eapply frame_indep_nil in X. eapply transitive_eval.
      exact X. econstructor. constructor. reflexivity.
      eassumption.
    (* true - proof is the same as in the previous case *)
    - eexists.
      eapply frame_indep_nil in X. eapply transitive_eval.
      exact X. econstructor. constructor.
      eassumption.
    (* false *)
    - inv H6. inv H2.
      simpl in H13. invSome. simpl in *.
      rewrite map_ext with (g := id) in H3. 2: {
        intros. by rewrite idsubst_is_id_exp.
      }
      rewrite map_id in H3.
      rewrite map_ext with (g := id) in H3. 2: {
        intros. destruct a as [[pl g] b].
        rewrite idsubst_upn.
        by do 2 rewrite idsubst_is_id_exp.
      }
      rewrite map_id in H3. inv H3. inv H2.
      inv H4. inv H2.
      inv H3. inv_result. inv H2.
      pose proof (params_eval_VValues lv (FCase1 le :: fs')).
      assert (k0 >= 2 + 2 * base.length lv \/ k0 < 2 + 2 * base.length lv) as [Hlt | Hlt] by lia.
      + pose proof (transitive_eval_rev_lt H4 Hlt H2) as XX.
        eexists.
        eapply frame_indep_nil in X.
        eapply transitive_eval. exact X.
        econstructor. constructor.
        exact XX.
      (* k0 should be greater; therefore, this is a contradiction *)
      + unshelve (epose proof (transitive_eval_rev_lt H2 _ H4) as XX).
        lia.
        inv XX.
        apply value_nostep in H6 as []. assumption.
Qed.


Theorem put_back_rev_term : forall F e Fs, FrameWf F ->
  | Fs, plug_f F e | ↓ -> | F :: Fs, e | ↓.
Proof.
  intros.
  destruct H0. apply semantic_iff_termination in H0.
  destruct H0 as [res [Hres H0]].
  apply put_back_rev in H0; try assumption.
  destruct H0. exists x0.
  apply semantic_iff_termination. eexists. split; eassumption.
Qed.

