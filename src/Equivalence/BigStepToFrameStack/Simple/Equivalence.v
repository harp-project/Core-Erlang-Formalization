From CoreErlang.Equivalence.BigStepToFrameStack.Simple Require Export MeasureLemmas Tactics.
From CoreErlang.Equivalence.BigStepToFrameStack Require Export WellFormedMapLemmas.

From CoreErlang.Equivalence.BigStepToFrameStack Require Export Induction FrameStackLemmas ScopingLemmas.
From CoreErlang.BigStep Require Import BigStep.
From CoreErlang.FrameStack Require Import SubstSemanticsLemmas.

Import BigStep.


(*TODO needs well_formed_map predicate*)

(*Todo: restriction to f?*)
(*Todo restriction to closed *)
Theorem equivalence_bigstep_framestack : 

  forall env modules own_module id id' e e' eff eff' f r,

    (eval_expr env modules own_module id e eff id' e' eff')

    ->

	  Some r = bres_to_fred f subst_env e'

(* wellformed_map r (valseq,exc) later on top level *)

	  ->

	  ⟨ [], (bexp_to_fexp_subst f subst_env env e) ⟩
    	-->*
	  r.

Proof.
  intros. revert f r H0. induction H; intros.
  (* Values *)
  * cbn in H6.
    destruct (bvs_to_fvs f subst_env vals).
    - admit.
    - congruence.
  * cbn in H6.
    destruct (bexc_to_fexc f subst_env ex).
    - admit.
    - congruence.
  (* Nil *)
  * eexists. split; inv H0.
    - constructor. 
      scope_solver.
    - econstructor.
      + cbv.
      unfold bexp_to_fexp_subst.
      
      
      cbn. 
(*         unfold subst_env. *)
        unfold bexp_to_fexp_subst, bexp_to_fexp, erase_names_exp. cbn.
        admit. (*constructor*)
      + admit.
  (* Lit *)
  * eexists. split; inv H0.
    - constructor.
      scope_solver.
    - do 1 do_step.
      constructor.
  (* Var *)
  * cbn in *.
    rewrite H.
    destruct
      (bvs_to_fvs f subst_env res)
      eqn:Hr.
    - inv H0.
      destruct res; cbn in *.
      + apply Environment.get_value_singelton_length in H. 
        cbn in H. 
        congruence.
      + destruct res; cbn in *.
        ** rewrite measure_reduction with (n2 := measure_val v0).
           {
             apply bs_to_fs_val_reduction.
             admit.
             (*assumption.*)
           }
           {
             clear Hr f id v eff own_module modules.
             apply get_value_some_than_is_elem in H.
             apply In_split in H.
             destruct H as [env1].
             destruct H as [env2].
             rewrite H.
             remember
               (λ '(_, y), measure_val y)
               as _measure.
             pose proof map_app _measure env1 ((inl s, v0) :: env2).
             rewrite H0.
             clear H0.
             pose proof list_sum_app (map _measure env1) (map _measure ((inl s, v0) :: env2)).
             rewrite H0.
             clear H0.
             simpl.
             inv Heq_measure.
             slia.
           }
           slia.
        ** apply Environment.get_value_singelton_length in H.
           cbn in H.
           congruence.
    - congruence.
  (* FunId *)
  * cbn in *.
    rewrite H.
    destruct
      (bvs_to_fvs f subst_env res) 
      eqn:Hr.
    - inv H0.
      destruct res; cbn in *.
      + apply Environment.get_value_singelton_length in H. 
        cbn in H.
        congruence.
      + destruct res; cbn in *.
        ** rewrite measure_reduction with (n2 := measure_val v0).
           {
             apply bs_to_fs_val_reduction.
             admit.
             (*assumption.*)
           }
           {
             clear Hr f id v eff own_module modules.
             apply get_value_some_than_is_elem in H.
             apply In_split in H.
             destruct H as [env1].
             destruct H as [env2].
             rewrite H.
             remember
               (λ '(_, y), measure_val y)
               as _measure.
             pose proof map_app _measure env1 ((inr fid, v0) :: env2).
             rewrite H0.
             clear H0.
             pose proof list_sum_app (map _measure env1) (map _measure ((inr fid, v0) :: env2)).
             rewrite H0.
             clear H0.
             simpl.
             inv Heq_measure.
             slia.
           }
           slia.
        ** apply Environment.get_value_singelton_length in H.
           cbn in H.
           congruence.
    - congruence.
  * admit.
  (* Fun *)
  * admit.
  (* Tuple*)
  * admit.
  (* Cons *)
  * specialize (IHeval_expr2 f).
    specialize (IHeval_expr1 f).
    (*
    unfold bres_to_fred in H1.
    case_match.
    2: { congruence. }
    inv H1.
    unfold bvs_to_fvs in H2.
    simpl in H2.
    *)
    unfold bres_to_fred in H1.
    case_match.
    2: { congruence. }
    inv H1.
    unfold bvs_to_fvs in H2.
    simpl in H2.
    unfold bs_to_fs_val in H2.
    remember (subst_env (measure_val (VCons hdv tlv))) as _fsubst.
    unfold val_to_exp in H2.
    fold val_to_exp in H2.
    unfold bs_to_fs_exp in H2.
    unfold eraseNames in H2.
    fold eraseNames in H2.
    unfold exp_to_val_fs in H2.
    fold exp_to_val_fs in H2.
    case_match.
    2: { inv H2. }
    case_match.
    2: { inv H2. }
    inv H2.
    rewrite measure_reduction with (n2 := measure_val hdv) in H1.
    2-3: slia.
    rewrite measure_reduction with (n2 := measure_val tlv) in H3.
    2-3: slia.
    cbn.
    rewrite measure_reduction_subst_env with (e := hd).
    2: { unfold measure_subst_env. lia. }
    rewrite measure_reduction_subst_env with (e := tl).
    2: { unfold measure_subst_env. lia. }
    unfold bres_to_fred in *.
    case_match.
    2: { admit. }
    case_match.
    2: { admit. }
    specialize (IHeval_expr1 v2 eq_refl).
    specialize (IHeval_expr2 v eq_refl).
    unfold bvs_to_fvs in *.
    simpl in H4.
    simpl in H2.
    unfold bs_to_fs_val in *.
    unfold bs_to_fs_exp in *.
    rewrite H1 in H2.
    rewrite H3 in H4.
    inv H2.
    inv H4.
    inv IHeval_expr1.
    inv IHeval_expr2.
    destruct H2.
    destruct H4.
    eexists. split.
    { admit. }
    eapply transitive_eval.
    - do_step.
      eapply frame_indep_core in H5.
      exact H5.
    - cbn.
      do_step.
      eapply frame_indep_core in H6.
      admit.
  (* Case *)
  * destruct (bres_to_fred f subst_env res).
    - admit.
    - congruence.
  (* Call *)    
  * admit.
  * admit.
  (* Primop *)
  * admit.
  (* App *)
  * admit.
  (* Let *)
  * specialize (IHeval_expr2 f r H2).
    specialize (IHeval_expr1 f).
    destruct (bres_to_fred f subst_env (inl vals)) eqn:Hvals.
    2: { admit. }
    specialize (IHeval_expr1 r0 eq_refl).
    inv IHeval_expr1.
    destruct H3.
    inv IHeval_expr2.
    destruct H5.
    eexists. split.
    { admit. }
    eapply transitive_eval.
    - cbn. do_step.
      rewrite measure_reduction_subst_env with (e := e2).
      2: { unfold measure_subst_env. admit. }
      rewrite measure_reduction_subst_env with (e := e1).
      2: { unfold measure_subst_env. lia. }
      eapply frame_indep_core in H4.
      unfold bs_to_fs_exp_env in H4.
      unfold bs_to_fs_exp in H4.
      exact H4.
    - cbn.
      unfold bs_to_fs_exp_env in H6.
      unfold bs_to_fs_exp in H6.
      remember (fold_left
               (λ (env' : list ((Var + FunctionIdentifier) * Value)) 
                  (key : Var + FunctionIdentifier),
                  filter (λ '(k, _), negb (var_funid_eqb k key)) env') 
               (map inl l) env) as env'.
      admit.
  (* Seq *)
  * specialize (IHeval_expr2 f r H1).
    specialize (IHeval_expr1 f).
    destruct (bres_to_fred f subst_env (inl [v1])) eqn:Hv1.
    2: { admit. }
    specialize (IHeval_expr1 r0 eq_refl).
    inv IHeval_expr1.
    destruct H2.
    inv IHeval_expr2.
    destruct H4.
    unfold bs_to_fs_exp_env in H5.
    unfold bs_to_fs_exp in H5.
    remember (eraseNames f (subst_env (measure_subst_env env e2) env e2)) as e.
    pose proof framestack_fseq e r r0 x0 H5.
    inv H6.
    eexists. split.
    { admit. }
    eapply transitive_eval.
    - cbn. do_step.
      rewrite measure_reduction_subst_env with (e := e2).
      2: { unfold measure_subst_env. lia. }
      rewrite measure_reduction_subst_env with (e := e1).
      2: { unfold measure_subst_env. lia. }
      eapply frame_indep_core in H3.
      unfold bs_to_fs_exp_env in H3.
      unfold bs_to_fs_exp in H3.
      exact H3.
    - cbn.
      apply H7.
  (* LetRec *)
  * admit.
  (* Map *)
  * admit.
  (* Cons *)
  * admit.
  * admit.
  (* Tuple *)
  * admit.
  (* Try *)
  * admit.
  * admit.
  (* Case *)
  * admit.
  * admit.
  (* Call *)
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  (* Primop *)
  * admit.
  (* App *)
  * admit.
  * admit.
  * admit.
  * admit.
  (* Let *)
  * admit.
  (* Seq *)
  * admit.
  (* Map *)
  * admit.
Admitted.