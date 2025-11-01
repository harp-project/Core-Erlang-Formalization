(**
  This file contains numerous semantic properties about the frame stack semantics
  and the termination relation of Core Erlang.
 *)
From CoreErlang.FrameStack Require Export
  SubstSemantics
  SubstSemanticsLabeledLemmas
  Termination
  LabeledTermination.
Import ListNotations.

(**
  Equivalence between labeled and unlabeled semantics
  *)
Corollary step_unlabeled_to_labeled:
  forall Fs r Fs' r',
  ⟨ Fs, r ⟩ --> ⟨Fs', r'⟩ ->
  exists l, ⟨ Fs, r ⟩ -⌊l⌋->ₗ ⟨Fs', r'⟩.
Proof.
  intros Fs e Fs' v H.
  inv H; eexists; constructor; try destruct ident; try apply H0; try assumption; try apply H1; reflexivity.
Qed.

Corollary step_labeled_to_unlabeled:
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

Corollary step_unlabeled_labeled_determinism_one_step :
  forall Fs e Fs' v l Fs'' v',
  ⟨ Fs, e ⟩ --> ⟨Fs', v⟩ ->
  ⟨ Fs, e ⟩ -⌊l⌋->ₗ ⟨Fs'', v'⟩ -> Fs' = Fs'' /\ v = v'.
Proof.
  intros Fs e Fs' v l Fs'' v' H H0.
  apply step_unlabeled_to_labeled in H as [l0 H].
  pose proof (step_determinism H H0) as [? ?].
  firstorder.
Qed.

Corollary step_unlabeled_labeled_determinism_all_step :
  forall k 
         Fs e Fs' v l Fs'' v',
  ⟨ Fs, e ⟩ -[k]-> ⟨Fs', v⟩ ->
  ⟨ Fs, e ⟩ -[k , l]->ₗ ⟨Fs'', v'⟩ -> Fs' = Fs'' /\ v = v'.
Proof.
  intros.
  apply step_rt_unlabeled_to_labeled in H as [l0 H].
  epose proof (step_rt_determinism H H0). firstorder.
Qed.

Corollary termination_unlabled_to_labeled :
  forall Fs r k,
    | Fs, r | k ↓ ->
      exists l, | Fs, r | l – k ↓ .
Proof.
  intros. induction H; try destruct IHterminates_in_k; try (eexists; constructor; eassumption).
  1-2: destruct ident; inv H0; eexists; econstructor; try eassumption; try reflexivity.
  * eexists. eapply LabeledTermination.step_case_match; eassumption.
  * eexists. eapply LabeledTermination.heat_letrec; eassumption.
Qed.

Corollary termination_labled_to_unlabeled :
  forall Fs r k l,
    | Fs, r | l – k ↓ ->
      | Fs, r | k ↓ .
Proof.
  intros. induction H; econstructor; eassumption.
Qed.

Corollary terminates_in_sem_unlabeled_to_labeled :
  forall Fs r ,
    | Fs , r | ↓ ->
    exists l , | Fs , r |ₗ l ↓ .
Proof.
  intros. destruct H.
  apply termination_unlabled_to_labeled in H as [l H1].
  exists l. cbv. exists x. assumption.
Qed.

Corollary terminates_in_sem_labeled_to_unlabeled :
  forall Fs r l,
    | Fs , r |ₗ l ↓ ->
    | Fs , r | ↓ .
Proof.
  intros. destruct H. apply termination_labled_to_unlabeled in H.
  cbv. exists x. eassumption.
Qed.

Corollary term_in_sem_unlabeled_to_labeled :
  forall Fs r k,
    terminates_in_k_sem Fs r k ->
    exists l , terminates_in_k_l_sem Fs r k l .
Proof.
  intros. destruct H as [red [Hres Hstep]].
  apply step_rt_unlabeled_to_labeled in Hstep as [l H1].
  exists l. cbv. exists red. firstorder.
Qed.

Corollary term_in_sem_labeled_to_unlabeled :
  forall Fs r l k,
    terminates_in_k_l_sem Fs r k l ->
    terminates_in_k_sem Fs r k .
Proof.
  intros. destruct H as [red [Hres Hstep]]. apply step_rt_labeled_to_unlabeled in Hstep.
  cbv. exists red. firstorder.
Qed.


(**
  Tactics to collected to use labeled lemmas/corollaries
*)
Ltac translate_to_labeled :=
repeat match goal with
| [H : ⟨ _, _ ⟩ --> ⟨_, _⟩ |- _] => apply step_unlabeled_to_labeled in H as [? ?]
| [H : ⟨ _, _ ⟩ -[_]-> ⟨_, _⟩ |- _] => apply step_rt_unlabeled_to_labeled in H as [? ?]
| [H : | _, _ | _ ↓ |- _] => apply termination_unlabled_to_labeled in H as [? ?]
| [H : | _, _ | ↓ |- _] => apply terminates_in_sem_unlabeled_to_labeled in H as [? ?]
| [H : terminates_in_k_sem _ _ _ |- _] => apply term_in_sem_unlabeled_to_labeled in H as [? ?]
end.

(** Properties of the semantics *)
Corollary step_determinism {e e' fs fs'} :
  ⟨ fs, e ⟩ --> ⟨fs', e'⟩ ->
  (forall fs'' e'', ⟨fs, e⟩ --> ⟨fs'', e''⟩ -> fs'' = fs' /\ e'' = e').
Proof.
  intros.
  translate_to_labeled.
  pose proof (step_determinism H H0).
  firstorder.
Qed.

Corollary value_nostep v :
  is_result v ->
  forall fs' v', ⟨ [], v ⟩ --> ⟨fs' , v'⟩ -> False.
Proof.
  intros H fs' v' HD.
  translate_to_labeled.
  by apply value_nostep in H0.
Qed.

Corollary step_rt_determinism {e v fs fs' k} :
  ⟨fs, e⟩ -[k]-> ⟨fs', v⟩
->
  (forall fs'' v', ⟨fs, e⟩ -[k]-> ⟨fs'', v'⟩ -> fs' = fs'' /\ v' = v).
Proof.
  intros.
  translate_to_labeled.
  pose proof (step_rt_determinism H H0).
  firstorder.
Qed.

Corollary step_closedness : forall F e F' e',
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

Corollary transitive_eval : forall {n Fs Fs' e e'},
  ⟨ Fs, e ⟩ -[n]-> ⟨ Fs', e' ⟩ -> forall {n' Fs'' e''}, ⟨ Fs', e' ⟩ -[n']-> ⟨ Fs'', e'' ⟩
->
  ⟨ Fs, e ⟩ -[n + n']-> ⟨ Fs'', e''⟩.
Proof.
  intros.
  translate_to_labeled.
  pose proof transitive_eval H H0 as D.
  by apply step_rt_labeled_to_unlabeled in D.
Qed.

Corollary terminates_in_k_step :
  forall fs e fs' e' k, ⟨ fs, e ⟩ --> ⟨ fs', e' ⟩ ->
  | fs', e' | k ↓ ->
  | fs, e | S k ↓.
Proof.
  intros.
  translate_to_labeled.
  epose proof terminates_in_k_step _ _ _ _ _ _ _ H.
  by apply termination_labled_to_unlabeled in H1.
Qed.

Corollary semantic_iff_termination :
  forall k e fs, terminates_in_k_sem fs e k <-> | fs, e | k ↓.
Proof.
  intros.
  split; intros; translate_to_labeled.
  * epose proof (semantic_iff_termination _ _ _ _) as D.
    destruct D as [H1 _]. specialize (H1 H).
    by apply termination_labled_to_unlabeled in H1.
  * epose proof (semantic_iff_termination _ _ _ _) as D.
    destruct D as [_ H1]. specialize (H1 H).
    by apply term_in_sem_labeled_to_unlabeled in H1.
Qed.

Corollary terminates_step :
  forall n fs e, | fs, e | n ↓ -> forall fs' e', ⟨fs, e⟩ --> ⟨fs', e'⟩
->
  | fs', e' | n - 1↓.
Proof.
  intros.
  translate_to_labeled.
  epose proof (terminates_step _ _ _ _ H _ _ _ H0).
  by apply termination_labled_to_unlabeled in H1.
Qed.

Corollary term_step_term :
  forall k n fs e, | fs, e | n ↓ -> forall fs' e', ⟨fs, e⟩ -[k]-> ⟨fs', e'⟩
->
  | fs', e' | n - k ↓.
Proof.
  intros.
  translate_to_labeled.
  epose proof (term_step_term _ _ _ _ _ _ H _ _ H0).
  by apply termination_labled_to_unlabeled in H1.
Qed.

Corollary step_term_term :
  forall k n fs e fs' e',
  ⟨fs, e⟩ -[k]-> ⟨fs', e'⟩ -> | fs', e' | n - k ↓ -> n >= k 
->
  | fs, e | n ↓.
Proof.
  intros.
  translate_to_labeled.
  epose proof (step_term_term _ _ _ _ _ _ _ _ H H0 H1).
  by apply termination_labled_to_unlabeled in H2.
Qed.

Corollary step_term_term_plus :
  forall k k2 fs e fs' e', 
  ⟨fs, e⟩ -[k]-> ⟨fs', e'⟩ -> | fs', e' | k2 ↓
->
  | fs, e | k + k2 ↓.
Proof.
  intros.
  translate_to_labeled.
  pose proof (step_term_term_plus _ _ _ _ _ _ _ _ H H0).
  by apply termination_labled_to_unlabeled in H1.
Qed.

Corollary transitive_eval_rev : forall Fs Fs' e e' k1,
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

Corollary frame_indep_step : forall e F F' Fs e',
  ⟨ F :: Fs, e ⟩ --> ⟨ F' :: Fs, e' ⟩
->
  forall Fs', ⟨ F :: Fs', e ⟩ --> ⟨ F' :: Fs', e' ⟩.
Proof.
  intros.
  translate_to_labeled.
  eapply frame_indep_step in H.
  by apply step_labeled_to_unlabeled in H.
Qed.

Corollary frame_indep_red : forall e F Fs e',
  ⟨ F :: Fs, e ⟩ --> ⟨ Fs, e' ⟩
->
  forall Fs', ⟨ F :: Fs', e ⟩ --> ⟨ Fs', e' ⟩.
Proof.
  intros.
  translate_to_labeled.
  eapply frame_indep_red in H.
  by apply step_labeled_to_unlabeled in H.
Qed.

Corollary frame_indep_core : forall k e Fs Fs' v,
  ⟨ Fs, e ⟩ -[k]-> ⟨ Fs', v ⟩
->
  forall Fs'', ⟨ Fs ++ Fs'', e ⟩ -[k]-> ⟨ Fs' ++ Fs'', v ⟩.
Proof.
  intros.
  translate_to_labeled.
  eapply frame_indep_core in H.
  by eapply step_rt_labeled_to_unlabeled in H.
Qed.

Corollary frame_indep_nil : forall k e Fs v,
  ⟨ Fs, e ⟩ -[k]-> ⟨ [], v ⟩
->
  forall Fs', ⟨ Fs ++ Fs', e ⟩ -[k]-> ⟨ Fs', v ⟩.
Proof.
  intros.
  translate_to_labeled.
  eapply frame_indep_nil in H.
  by eapply step_rt_labeled_to_unlabeled in H.
Qed.

Corollary params_eval :
  forall vals ident vl exps e Fs (v : Val),
  ⟨ FParams ident vl ((map VVal vals) ++ e :: exps) :: Fs, RValSeq [v]⟩ -[1 + 2 * length vals]->
  ⟨ FParams ident (vl ++ v :: vals) exps :: Fs, e⟩.
Proof.
  intros.
  apply step_rt_labeled_to_unlabeled with (l := []).
  by apply params_eval.
Qed.

Corollary params_eval_create :
  forall vals ident vl Fs (v : Val) r eff',
  Forall (fun v => VALCLOSED v) vals ->
  Some (r, eff') = create_result ident (vl ++ v :: vals) ->
  ⟨ FParams ident vl (map VVal vals) :: Fs, RValSeq [v]⟩ -[1 + 2 * length vals]->
  ⟨ Fs, r ⟩.
Proof.
  intros.
  eapply step_rt_labeled_to_unlabeled.
  by apply params_eval_create.
Qed.

Corollary create_result_is_not_box :
  forall ident vl r eff',
  ICLOSED ident ->
  Forall (fun v => VALCLOSED v) vl ->
  Some (r, eff') = create_result ident vl ->
  REDCLOSED r.
Proof.
  intros.
  eapply SubstSemanticsLabeledLemmas.create_result_is_not_box; eassumption.
Qed.

Corollary term_empty : forall x Fs (e : Exp) (He : EXPCLOSED e),
  | Fs, e | x ↓ ->
  exists k, | [], e | k ↓ /\ k <= x.
Proof.
  intros. translate_to_labeled.
  epose proof (term_empty x Fs e He x0 H).
  destruct H0 as [k [l' [Hterm [Hlt _]]]].
  eexists. split. 2: eassumption. by apply termination_labled_to_unlabeled in Hterm.
Qed.

(* NOTE: This is not a duplicate! Do not remove! *)
(* sufficient to prove it for Exp, since value sequences and
   exceptions terminate in 0/1 step by definition in the
   empty stack (and RBox does not terminate!). *)
Corollary term_eval_empty : forall x Fs (e : Exp),
  | Fs, e | x ↓ ->
  exists res k, is_result res /\ ⟨ [], e ⟩ -[k]-> ⟨ [], res ⟩ /\ k <= x.
Proof.
  intros. translate_to_labeled.
  epose proof (term_eval_empty _ _ _ He _ H) as H0.
  destruct H0 as [res [k [lss [is_res [Hstep [Hlt _]]]]]].
  eexists res. exists k. apply step_rt_labeled_to_unlabeled in Hstep. firstorder.
Qed.

Corollary term_eval : forall x Fs (e : Exp), | Fs, e | x ↓ ->
  exists v k, is_result v /\ ⟨ Fs, e ⟩ -[k]-> ⟨ Fs, v ⟩ /\ k <= x.
Proof.
  intros. translate_to_labeled.
  epose proof (term_eval _ _ _ He _ H).
  destruct H0 as [v [k [lss [is_res [Hstep [Hlt _]]]]]].
  apply step_rt_labeled_to_unlabeled in Hstep.
  exists v. exists k. firstorder.
Qed.

Corollary term_eval_both : forall x Fs (e : Exp), | Fs, e | x ↓ ->
  exists v k, is_result v /\
  ⟨ [], e ⟩ -[k]-> ⟨ [], v ⟩ /\
  ⟨ Fs, e ⟩ -[k]-> ⟨ Fs, v ⟩ /\ k <= x.
Proof.
  intros. translate_to_labeled.
  epose proof (term_eval_both _ _ _ He _ H).
  destruct H0 as [v [k [ls [Hres [Hstep1 [Hstep2 [Hlt _]]]]]]].
  exists v. exists k. firstorder.
  all: eapply step_rt_labeled_to_unlabeled; eassumption.
Qed.

Corollary put_back : forall F e Fs (P : EXPCLOSED e) (P2 : FCLOSED F),
  | F :: Fs, e | ↓ -> | Fs, plug_f F e | ↓.
Proof.
  intros. translate_to_labeled.
  epose proof (put_back _ _ _ P P2 _ H).
  by eapply terminates_in_sem_labeled_to_unlabeled.
Qed.

Corollary put_back_rev : forall F e Fs (P : EXPCLOSED e), FCLOSED F ->
  | Fs, plug_f F e | ↓ -> | F :: Fs, e | ↓.
Proof.
  intros. translate_to_labeled.
  epose proof (put_back_rev _ _ _ P x H H0).
  by eapply terminates_in_sem_labeled_to_unlabeled.
Qed.
