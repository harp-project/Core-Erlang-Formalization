From CoreErlang.FrameStack Require Export CIU.

Import ListNotations.

Ltac extract_meta_eval H :=
  let r := fresh "r" in
  let k := fresh "k" in
  let Hr := fresh "Hr" in
  let Hd := fresh "Hd" in
  let Hd' := fresh "Hd'" in
  let Hk := fresh "Hk" in
  let H' := fresh "H'" in
  eapply term_eval_both in H as H'; [destruct H' as [r [k [Hr [Hd [Hd' Hk]]]]];
  eapply term_step_term in Hd'; [|eassumption]; inv Hr| auto].

Ltac unfold_list := 
  match goal with
  | [H : length ?l = 0 |- _] => destruct l; try inv H
  | [H : 0 = length ?l |- _] => destruct l; try inv H
  | [H : length ?l = S ?n |- _] => destruct l; try inv H; unfold_list
  | [H : S ?n = length ?l |- _] => destruct l; try inv H; unfold_list
  end.

Section case_if_equiv.

  Open Scope string_scope.
  Variables (e1 e2 e3 : Exp) (Γ : nat).
  Hypotheses (He1 : EXP Γ ⊢ e1)
             (He2 : EXP Γ ⊢ e2)
             (He3 : EXP Γ ⊢ e3).

  Local Definition nonidiomatic :=
    ELet 1 e1
      (ECase (`VVar 0) 
              [([PLit (Atom "true")], `VLit "true", e2);
              ([PVar], `VLit "true", e3.[ren (fun n => 2 + n) ])]).

  Local Definition idiomatic :=
    ELet 1 e1
      (ECase (EValues [])
          [([], °ECall "erlang" "=:=" [`VVar 0;`VLit "true"], e2);
          ([], `VLit "true", e3.[ren (fun n => 1 + n) ])]).

  Local Proposition nonidiomatic_scope :
    EXP Γ ⊢ nonidiomatic.
  Proof.
    unfold nonidiomatic.
    scope_solver.
    apply -> subst_preserves_scope_exp. exact He3.
    intro. intros. simpl. lia. 
  Qed.

  Local Proposition idiomatic_scope :
    EXP Γ ⊢ idiomatic.
  Proof.
    unfold idiomatic.
    scope_solver.
    apply -> subst_preserves_scope_exp. exact He3.
    intro. intros. simpl. lia. 
  Qed.

  Local Theorem equivalence_part1 :
    CIU_open Γ nonidiomatic idiomatic.
  Proof.
    split. 2: split.
    constructor. apply -> subst_preserves_scope_exp; try apply nonidiomatic_scope; auto.
    constructor. apply -> subst_preserves_scope_exp; try apply idiomatic_scope; auto.
    {
      intros. unfold nonidiomatic in H1. simpl in H1.
      repeat deriv.

      extract_meta_eval H7; clear H7.
      { (* e1 evaluates to an exception *)
        inv Hd'. clear H7.
        unfold idiomatic.
        exists (S (S k1 + k0)). simpl. econstructor.
        eapply frame_indep_nil in Hd.
        eapply step_term_term. eassumption. 2: lia.
        replace (S (k1 + k0) - k0) with (S k1) by lia. constructor. congruence.
        eassumption.
      }
      { (* e1 evaluates correctly *)
        deriv. unfold_list. simpl in H8.
        do 3 deriv.
        { (* v is true *)
          simpl in H12. destruct v; try congruence. break_match_hyp; try congruence.
          break_match_hyp; try congruence. destruct l; simpl in Heqb; try congruence.
          break_match_hyp; try congruence. inv Heqo. simpl in H12. inv H12.
          simpl in H13. do 2 deriv.
          cbn in H12. inv H12.
          unfold idiomatic.
          exists (S (12 + k2 + k0)). simpl. econstructor.
          eapply frame_indep_nil in Hd.
          eapply step_term_term. eassumption. 2: lia.
          change clock to (12 + k2).
          constructor. reflexivity.
          simpl. constructor.
          constructor. econstructor. congruence. simpl. reflexivity.
          econstructor. reflexivity.
          simpl. constructor. econstructor. congruence.
          constructor. constructor. constructor. simpl. econstructor.
          auto. econstructor. cbn. reflexivity.
          econstructor. reflexivity. eassumption.
        }
        { (* v is not true *)
          deriv.
          2: { (* no more cases *)
            inv H11.
          }

          simpl in H14. do 2 deriv. rewrite H11 in H14. inv H14.
          unfold idiomatic.
          exists (S (15 + k1 + k0)). simpl. econstructor.
          eapply frame_indep_nil in Hd.
          eapply step_term_term. eassumption. 2: lia.
          change clock to (15 + k1).
          constructor. reflexivity.
          simpl. constructor.
          constructor. econstructor. congruence. simpl. reflexivity.
          econstructor. reflexivity.
          simpl. constructor. econstructor. congruence.
          constructor. auto. constructor. constructor. simpl. auto.
          econstructor.
          { (* v is not true *)
            cbn. destruct v; simpl; try reflexivity.
            2: destruct n; reflexivity.
            destruct l; try reflexivity. simpl.
            destruct string_dec; try reflexivity. subst. simpl in H12. congruence.
          }
          constructor. econstructor. reflexivity. constructor. auto. econstructor.
          reflexivity.
          simpl in H11. inv H11.
          do 2 rewrite subst_comp_exp in *.
          clear Hd. cbn in *.
          rewrite substcomp_id_r.
          rewrite subst_extend in H15.
          rewrite substcomp_scons_core, subst_extend in H15.
          rewrite subst_extend.
          rewrite subst_comp_exp in *.
          rewrite ren_scons in *.
          rewrite ren_scons in H15. assumption.
        }
      }
      apply -> subst_preserves_scope_exp; eauto.
    }
  Qed.

  Local Theorem equivalence_part2 :
    CIU_open Γ idiomatic nonidiomatic.
  Proof.
    apply Rrel_implies_CIU.
    apply Rrel_exp_compat. apply Erel_Let_compat; auto.
    apply Rrel_exp_compat_reverse. apply CIU_implies_Rrel.
    pose proof (nonidiomatic_scope).
    pose proof (idiomatic_scope).
    unfold idiomatic, nonidiomatic in *. inv H. inv H0. inv H3. inv H2.
    split. 2: split.
    1-2: constructor; apply -> subst_preserves_scope_exp; eauto.
    clear H6 H3 H7. intros. simpl in H1.
    do 4 deriv. simpl in H9. deriv. 2: { inv H11. }
    inv H11.
    simpl in H12. rewrite idsubst_is_id_val in H12. do 3 deriv.
    break_match_hyp.
    2: { specialize (H 0). rewrite Heqs in H. lia. }
    do 3 deriv. cbn in H13.
    break_match_hyp.
    { (* e1 is true *)
      deriv. inv H12. simpl in H14. rewrite idsubst_is_id_exp in H14.
      exists (5 + k). simpl.
      econstructor. rewrite Heqs.
      destruct v; simpl in Heqb; try congruence.
      destruct l; simpl in Heqb; try congruence.
      break_match_hyp; try congruence. subst.
      econstructor. auto. econstructor. reflexivity.
      constructor. auto. econstructor. reflexivity.
      simpl. now rewrite idsubst_is_id_exp.
    }
    { (* e1 is false *)
      do 2 deriv. 2: { inv H14. }
      simpl in H15. do 2 deriv. inv H15. inv H14.
      exists (6 + k0). simpl.
      econstructor. rewrite Heqs. constructor. auto. constructor.
      {
        destruct v; simpl in Heqb; try reflexivity.
        destruct l; simpl in Heqb; try reflexivity.
        break_match_hyp; subst; try congruence.
        cbn. destruct string_dec; auto. congruence.
      }
      econstructor. reflexivity. simpl. constructor. auto. econstructor.
      reflexivity. simpl.
      rewrite subst_comp_exp in *. simpl in *.
      rewrite subst_extend, subst_comp_exp in *.
      rewrite substcomp_id_r, ren_scons in *. assumption.
    }
  Qed.
End case_if_equiv.

Section length_0.

  Open Scope string_scope.
  Variables (e1 e2 : Exp) (Γ : nat).
  Hypotheses (He1 : EXP Γ ⊢ e1)
             (He2 : EXP Γ ⊢ e2).

  Local Definition nonidiomatic2 :=
    ECase e1
    [([PVar], 
      °ETry 
      (
        ELet 1 (ECall "erlang" "length" [`VVar 0])
          (ECall "erlang" "==" [`VVar 0;`VLit 0%Z])
      )
      1 (`VVar 0)
      3 (`VLit "false")
      , e2.[ren (fun n => 1 + n)])
    ;
    ([PVar], `VLit "true", °EPrimOp "match_fail" [°ETuple [`VLit "function_clause";`VVar 0]])].

  Local Definition idiomatic2 :=
    ECase e1 [(
      [PNil], `VLit "true", e2);
      ([PVar], `VLit "true", °EPrimOp "match_fail" [°ETuple [`VLit "function_clause"; `VVar 0]])].

  Local Proposition nonidiomatic2_scope :
    EXP Γ ⊢ nonidiomatic2.
  Proof.
    unfold nonidiomatic2.
    scope_solver.
    apply -> subst_preserves_scope_exp. exact He2.
    intro. intros. simpl. lia. 
  Qed.

  Local Proposition idiomatic2_scope :
    EXP Γ ⊢ idiomatic2.
  Proof.
    unfold idiomatic2.
    scope_solver.
  Qed.

  Local Theorem equivalence2_part1 :
    CIU_open Γ nonidiomatic2 idiomatic2.
  Proof.
    (* we cannot use compatibility lemmas here, because
       the patterns are different in the clauses *)
    pose proof idiomatic2_scope as Sc1.
    pose proof nonidiomatic2_scope as Sc2.
    split. 2: split.
    1-2: constructor; apply -> subst_preserves_scope_exp; eauto.
    intros. simpl in H1. destruct H1 as [k D].
    deriv. extract_meta_eval H5; clear H5.
    { (* e1 evaluates to an exception *)
      inv Hd'. exists (2 + k + k1). simpl.
      econstructor. eapply step_term_term.
      eapply frame_indep_nil in Hd. exact Hd. 2: lia.
      change clock to (S k1). econstructor; auto. congruence. 
    }
    { (* e1 evaluates correctly *)
      deriv.
      { (* pattern matching succeeds *)
        destruct vs. inv H4. destruct vs. 2: inv H4.
        simpl in H4. inv H4.
        inv H10. inv H11. repeat deriv.
        simpl in H12. destruct (eval_length [v]) eqn:EQ.
        {
          simpl in EQ. break_match_hyp; try congruence.
        }
        { (* v is a list *)
          apply eval_length_number in EQ as EQ'. intuition; repeat destruct_hyps.
          { (* v = VNil *)
            inv H2. inv H5. clear H4. simpl in EQ. rewrite EQ in H12.
            inv H12. simpl in H11. repeat deriv. cbn in H16. inv EQ.
            simpl in H16. inv H16. simpl in H18.
            repeat deriv. inv H18. simpl in H19.
            rewrite subst_comp_exp, subst_extend, subst_comp_exp in H19.
            rewrite ren_scons, substcomp_id_l in H19.
            (* evaluation *)
            exists (4 + k + k1). simpl.
            econstructor. eapply step_term_term.
            eapply frame_indep_nil in Hd; exact Hd. 2: lia.
            change clock to (3 + k1). econstructor. reflexivity.
            constructor. auto. econstructor. reflexivity. simpl.
            now rewrite idsubst_is_id_exp.
          }
          { (* v = VCons v1 v2 *)
            inv H2. inv H4. clear H5.
            pose proof EQ as EQ'. simpl in EQ. rewrite EQ in H12. clear EQ.
            simpl in H12. repeat deriv.
            simpl in H11. repeat deriv. cbn in H16.
            break_match_hyp. {
              pose proof (eval_length_positive _ _ _ EQ').
              lia.
            }
            repeat deriv. simpl in H18.
            repeat deriv. 2: inv H19. inv H19.
            simpl in H20. repeat deriv.
            inv H19. simpl in H20. repeat deriv. simpl in H23.
            repeat deriv. simpl in H22.
            (* evaluation *)
            simpl. exists (14 + k + k1). simpl.
            econstructor. eapply step_term_term.
            eapply frame_indep_nil in Hd; exact Hd. 2: lia.
            change clock to (13 + k1). constructor. reflexivity.
            econstructor. reflexivity. simpl.
            do 2 econstructor. reflexivity. simpl.
            do 2 econstructor. congruence.
            do 2 econstructor. congruence.
            do 4 econstructor. 1-2: now destruct_scopes.
            reflexivity. simpl.
            econstructor. reflexivity. simpl. assumption.
          }
        }
        { (* exception *)
          simpl in EQ. rewrite EQ in H12. inv H12. inv H8. 2: {
            specialize (H7 _ _ _ _ eq_refl). contradiction.
          }
          simpl in H13. repeat deriv. 2: inv H15.
          simpl in H16. repeat deriv.
          inv H17. 2: { inv H2. } inv H16. simpl in H12. repeat deriv.
          simpl in H15. inv H15. simpl in H20. inv H20. simpl in H18.
          (* evaluation *)
          simpl. exists (14 + k + k1). simpl.
          econstructor. eapply step_term_term.
          eapply frame_indep_nil in Hd; exact Hd. 2: lia.
          change clock to (13 + k1). constructor.
          destruct v; auto. inv EQ. clear H4 H8.
          econstructor. reflexivity. constructor. auto.
          econstructor. reflexivity. simpl.
          constructor. constructor. congruence.
          do 2 constructor. congruence. do 3 econstructor. auto.
          econstructor. reflexivity. simpl. econstructor. reflexivity. simpl.
          assumption.
        }
        {
          simpl in EQ. break_match_hyp; inv EQ.
        }
      }
      { (* pattern matching fails due to the degree of `vs` - in the concrete Core Erlang implementation this cannot happen, because such programs are filtered out by the compiler *)
        repeat deriv. congruence.
        (* evaluation *)
        simpl. exists (4 + k + k1). simpl.
        econstructor. eapply step_term_term.
        eapply frame_indep_nil in Hd; exact Hd. 2: lia.
        change clock to (3 + k1). constructor.
        {
          destruct vs; auto. destruct vs; simpl; destruct v; auto.
          inv H4.
        }
        constructor. assumption. constructor. assumption.
      }
    }
    apply -> subst_preserves_scope_exp; eauto.
  Qed.

  Local Theorem equivalence2_part2 :
    CIU_open Γ idiomatic2 nonidiomatic2.
  Proof.
    (* the beginning of this proof is the same as before *)
    (* we cannot use compatibility lemmas here, because
    the patterns are different in the clauses *)
    pose proof idiomatic2_scope as Sc1.
    pose proof nonidiomatic2_scope as Sc2.
    split. 2: split.
    1-2: constructor; apply -> subst_preserves_scope_exp; eauto.
    intros. simpl in H1. destruct H1 as [k D].
    deriv. extract_meta_eval H5; clear H5.
    { (* e1 evaluates to an exception *)
      inv Hd'. exists (2 + k + k1). simpl.
      econstructor. eapply step_term_term.
      eapply frame_indep_nil in Hd. exact Hd. 2: lia.
      change clock to (S k1). econstructor; auto. congruence. 
    }
    (* new stuff *)
    { (* e1 evaluates correctly *)
      inv Hd'.
      { (* vs = [VNil] *)
        simpl in H10. destruct vs. 2: destruct vs. all: inv H4.
        all: destruct v; inv H3.
        repeat deriv. inv H11. simpl in H12.
        rewrite idsubst_is_id_exp in H12.
        (* evaluation *)
        simpl. exists (18 + k + k1). simpl.
        econstructor. eapply step_term_term.
        eapply frame_indep_nil in Hd. exact Hd. 2: lia.
        change clock to (17 + k1).
        econstructor. reflexivity. simpl.
        repeat econstructor. 1-2: congruence. simpl.
        rewrite subst_comp_exp, subst_extend, subst_comp_exp.
        rewrite ren_scons, substcomp_id_l.
        assumption.
      }
      inv H10.
      { (* vs == [v] /\ v <> VNil *)
        destruct vs. 2: destruct vs.
        all: inv H12.
        simpl in H13. repeat deriv. inv H12.
        simpl in H13. repeat deriv.
        simpl in H16. repeat deriv.
        simpl in H15.
        (* evaluation *)
        simpl.
        simpl. destruct (eval_length [v]) eqn:EQ.
        {
          simpl in EQ. break_match_hyp; try congruence.
        }
        {
          exists (30 + k + k1). simpl.
          econstructor. eapply step_term_term.
          eapply frame_indep_nil in Hd. exact Hd. 2: lia.
          change clock to (29 + k1).
          econstructor. reflexivity.
          simpl. econstructor. constructor.
          do 2 constructor. congruence.
          constructor. auto. econstructor. reflexivity.
          apply eval_length_number in EQ as EQ'.
          intuition; repeat destruct_hyps. inv H1. inv H8.
          inv EQ.
          { (* v = VNil*)
            inv H4.
          }
          (* boiler plate so that we can see the individual steps
             of the evaluation *)
          { (* v = VCons v1 v2 *)
            inv H7.
            apply eval_length_positive in EQ as EQ'.
            Opaque eval_length. simpl. rewrite EQ.
            econstructor. reflexivity. simpl.
            econstructor. econstructor. congruence.
            econstructor. auto. econstructor. econstructor. auto.
            econstructor. reflexivity. cbn. break_match_goal. lia.
            econstructor. reflexivity. simpl.
            econstructor. constructor. econstructor.
            econstructor. reflexivity.
            econstructor. auto. econstructor. reflexivity. simpl.
            econstructor. constructor. congruence.
            econstructor. constructor. congruence.
            econstructor. auto. econstructor. simpl.
            econstructor. auto. econstructor. reflexivity.
            econstructor. reflexivity. simpl.
            assumption.
          }
        }
        {
          (* boiler plate so that we can see the individual steps
             of the evaluation *)
          exists (24 + k + k1). simpl.
          econstructor. eapply step_term_term.
          eapply frame_indep_nil in Hd. exact Hd. 2: lia.
          change clock to (23 + k1).
          econstructor. reflexivity.
          simpl. econstructor. constructor.
          do 2 constructor. congruence.
          constructor. auto. econstructor. reflexivity. cbn.
          rewrite EQ.
          Transparent eval_length.
          econstructor. congruence.
          destruct e, p. apply cool_try_err.
          econstructor. auto. econstructor. econstructor. reflexivity.
          econstructor. auto. econstructor. reflexivity. cbn.
          econstructor. econstructor. congruence.
          econstructor. econstructor. congruence.
          econstructor. auto. econstructor. simpl.
          econstructor. auto. econstructor. reflexivity.
          econstructor. reflexivity. simpl.
          assumption.
        }
        {
          simpl in EQ. break_match_hyp; inv EQ.
        }
      }
      { (* pattern matching fails due to the degree of `vs` - in the concrete Core Erlang implementation this cannot happen, because such programs are filtered out by the compiler *)
        inv H13. simpl.
        (* evaluation *)
        exists (4 + k1 + k). simpl.
        econstructor. eapply step_term_term.
        eapply frame_indep_nil in Hd. exact Hd. 2: lia.
        change clock to (3 + k1).
        constructor. assumption.
        constructor. assumption.
        constructor. assumption.
      }
    }
    apply -> subst_preserves_scope_exp; eauto.
  Qed.

End length_0.
