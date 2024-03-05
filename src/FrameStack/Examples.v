From CoreErlang.FrameStack Require Export CTX.

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
      (ECase (˝VVar 0) 
              [([PLit (Atom "true")], ˝VLit "true", e2);
              ([PVar], ˝VLit "true", e3.[ren (fun n => 2 + n) ])]).

  Local Definition idiomatic :=
    ELet 1 e1
      (ECase (EValues [])
          [([], °ECall (˝VLit "erlang") (˝VLit "=:=") [˝VVar 0;˝VLit "true"], e2);
          ([], ˝VLit "true", e3.[ren (fun n => 1 + n) ])]).

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
        replace (S (k1 + k0) - k0) with (S k1) by lia. constructor. reflexivity.
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
          unfold idiomatic.
          exists (S (16 + k2 + k0)). simpl. econstructor.
          eapply frame_indep_nil in Hd.
          eapply step_term_term. eassumption. 2: lia.
          change clock to (16 + k2).
          constructor. reflexivity.
          simpl. constructor.
          constructor. econstructor. congruence. simpl. reflexivity.
          econstructor. reflexivity.
          simpl. constructor. econstructor. auto.
          econstructor. econstructor. auto.
          econstructor. econstructor. congruence.
          constructor. constructor. constructor. simpl. econstructor.
          auto. econstructor. cbn. reflexivity.
          econstructor. eassumption.
        }
        { (* v is not true *)
          deriv.
          2: { (* no more cases *)
            inv H11.
          }

          simpl in H14. do 2 deriv.
          unfold idiomatic.
          exists (S (19 + k1 + k0)). simpl. econstructor.
          eapply frame_indep_nil in Hd.
          eapply step_term_term. eassumption. 2: lia.
          change clock to (19 + k1).
          constructor. reflexivity.
          simpl. constructor.
          constructor. econstructor. congruence. simpl. reflexivity.
          econstructor. reflexivity.
          simpl. constructor. econstructor. auto.
          econstructor. econstructor. auto.
          econstructor. econstructor. congruence.
          constructor. auto. constructor. constructor. simpl. auto.
          econstructor.
          { (* v is not true *)
            cbn. destruct v; simpl; try reflexivity.
            2: destruct n; reflexivity.
            destruct l; try reflexivity. simpl.
            destruct string_dec; try reflexivity. subst. simpl in H12. congruence.
          }
          constructor. econstructor. reflexivity. constructor. auto. econstructor.
          simpl in H11. inv H11.
          do 2 rewrite subst_comp_exp in *.
          clear Hd. cbn in *.
          rewrite substcomp_id_r.
          rewrite subst_extend in H13.
          rewrite substcomp_scons_core, subst_extend in H13.
          rewrite subst_extend.
          rewrite subst_comp_exp in *.
          rewrite ren_scons in *.
          rewrite ren_scons in H13. assumption.
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
    do 4 deriv. simpl in H7. inv H7. deriv. 2: { inv H11. }
    inv H11.
    simpl in H12. rewrite idsubst_is_id_val in H12. do 3 deriv.
    break_match_hyp.
    2: { specialize (H 0). rewrite Heqs in H. lia. }
    do 7 deriv. cbn in H14. invSome.
    break_match_hyp.
    { (* e1 is true *)
      deriv. rewrite idsubst_is_id_exp in H13.
      exists (5 + k). simpl.
      econstructor. rewrite Heqs.
      destruct v; simpl in Heqb; try congruence.
      destruct l; simpl in Heqb; try congruence.
      break_match_hyp; try congruence. subst.
      econstructor. auto. econstructor. reflexivity.
      constructor. auto. econstructor.
      simpl. now rewrite idsubst_is_id_exp.
    }
    { (* e1 is false *)
      do 2 deriv. 2: { inv H16. }
      simpl in H17. do 2 deriv.
      exists (6 + k0). simpl.
      econstructor. rewrite Heqs. constructor. auto. constructor.
      {
        destruct v; simpl in Heqb; try reflexivity.
        destruct l; simpl in Heqb; try reflexivity.
        break_match_hyp; subst; try congruence.
        cbn. destruct string_dec; auto. congruence.
      }
      inv H16.
      econstructor. reflexivity. simpl. constructor. auto. econstructor.
      rewrite subst_comp_exp in *. simpl in *.
      rewrite subst_comp_exp in *. rewrite subst_extend.
      rewrite ren_scons in *. rewrite substcomp_id_r in H15.
      assumption.
    }
  Qed.
End case_if_equiv.

Section length_0.

  Open Scope string_scope.
  Variables (e1 e2 e3 : Exp) (Γ : nat).
  Hypotheses (He1 : EXP Γ ⊢ e1)
             (He2 : EXP Γ ⊢ e2)
             (He3 : EXP Γ ⊢ e3).

  Local Definition nonidiomatic2 :=
    ECase e1
    [([PVar], 
      °ETry 
      (
        ELet 1 (ECall (˝VLit "erlang") (˝VLit "length") [˝VVar 0])
          (ECall (˝VLit "erlang") (˝VLit "==") [˝VVar 0;˝VLit 0%Z])
      )
      1 (˝VVar 0)
      3 (˝ffalse)
      , e2.[ren (fun n => 1 + n)]);
     ([PVar], ˝ttrue, e3.[ren (fun n => 1 + n)])
    ;
    ([PVar], ˝ttrue, °EPrimOp "match_fail" [°ETuple [˝VLit "function_clause";˝VVar 0]])].

  Local Definition idiomatic2 :=
    ECase e1 [(
      [PNil], ˝ttrue, e2);
      ([PVar], ˝ttrue, e3.[ren (fun n => 1 + n)]);
      ([PVar], ˝ttrue, °EPrimOp "match_fail" [°ETuple [˝VLit "function_clause"; ˝VVar 0]])].

  Local Proposition nonidiomatic2_scope :
    EXP Γ ⊢ nonidiomatic2.
  Proof.
    unfold nonidiomatic2.
    scope_solver.
    all: apply -> subst_preserves_scope_exp; eauto.
    all: intro; intros; simpl; lia.
  Qed.

  Local Proposition idiomatic2_scope :
    EXP Γ ⊢ idiomatic2.
  Proof.
    unfold idiomatic2.
    scope_solver.
    all: apply -> subst_preserves_scope_exp; eauto.
    all: intro; intros; simpl; lia.
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
      change clock to (S k1). econstructor; auto.
    }
    { (* e1 evaluates correctly *)
      deriv.
      { (* pattern matching succeeds *)
        destruct vs. inv H4. destruct vs. 2: inv H4.
        simpl in H4. inv H4.
        inv H10. inv H11. repeat deriv.
        simpl in H14. destruct (eval_length [v]) eqn:EQ.
        {
          simpl in EQ. break_match_hyp; try congruence.
        }
        { (* v is a list *)
          apply eval_length_number in EQ as EQ'. intuition; destruct_hyps.
          { (* v = VNil *)
            inv H2. inv H7. clear H6. simpl in EQ.
            cbn in H13. rewrite EQ in H13. invSome.
            inv H14. simpl in H13. repeat deriv. cbn in H19. inv EQ. invSome.
            inv H20. simpl in H22.
            repeat deriv.
            rewrite subst_comp_exp, subst_extend, subst_comp_exp in H20.
            rewrite ren_scons, substcomp_id_l in H20.
            (* evaluation *)
            exists (4 + k + k1). simpl.
            econstructor. eapply step_term_term.
            eapply frame_indep_nil in Hd; exact Hd. 2: lia.
            change clock to (3 + k1). econstructor. reflexivity.
            constructor. auto. econstructor. simpl.
            now rewrite idsubst_is_id_exp.
          }
          { (* v = VCons v1 v2 *)
            inv H2. inv H6. clear H7.
            pose proof EQ as EQ'. cbn in H13, EQ. rewrite EQ in H13. clear EQ.
            invSome.
            simpl in H14. repeat deriv.
            simpl in H13. repeat deriv. cbn in H20.
            cbn in H19. invSome.
            break_match_hyp. {
              pose proof (eval_length_positive _ _ _ EQ').
              lia.
            }
            repeat deriv. simpl in H22.
            repeat deriv. all: inv H23.
            simpl in H24. repeat deriv.
            (* evaluation *)
            simpl. exists (5 + k + k2). simpl.
            econstructor. eapply step_term_term.
            eapply frame_indep_nil in Hd; exact Hd. 2: lia.
            change clock to (4 + k2). constructor. reflexivity.
            econstructor. reflexivity. simpl.
            do 2 econstructor. eassumption.
          }
        }
        { (* exception *)
          cbn in EQ, H13. rewrite EQ in H13. invSome. inv H14. inv H11.
          2: {
            inv H10.
          }
          simpl in H15. repeat deriv. 2: inv H17.
          simpl in H18. repeat deriv. 2: { inv H17. }
          inv H17. simpl in *. repeat deriv.
          (* evaluation *)
          simpl. exists (5 + k + k2). simpl.
          econstructor. eapply step_term_term.
          eapply frame_indep_nil in Hd; exact Hd. 2: lia.
          change clock to (4 + k2). constructor.
          destruct v; auto. inv EQ. clear H4 H8.
          econstructor. reflexivity. constructor. auto.
          econstructor.
          assumption.
        }
        {
          simpl in EQ. break_match_hyp; inv EQ.
        }
      }
      { (* pattern matching fails due to the degree of ˝vs˝ - in the concrete Core Erlang implementation this cannot happen, because such programs are filtered out by the compiler *)
        repeat deriv; try congruence.
        (* evaluation *)
        simpl. exists (5 + k + k2). simpl.
        econstructor. eapply step_term_term.
        eapply frame_indep_nil in Hd; exact Hd. 2: lia.
        change clock to (4 + k2). constructor.
        {
          destruct vs; auto. destruct vs; simpl; destruct v; auto.
          inv H4.
        }
        constructor. assumption. constructor. assumption.
        constructor. assumption.
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
      change clock to (S k1). econstructor; auto.
    }
    (* new stuff *)
    { (* e1 evaluates correctly *)
      inv Hd'.
      { (* vs = [VNil] *)
        simpl in H10. destruct vs. 2: destruct vs. all: inv H4.
        all: destruct v; inv H3.
        repeat deriv.
        rewrite idsubst_is_id_exp in H10.
        (* evaluation *)
        simpl. exists (26 + k + k1). simpl.
        econstructor. eapply step_term_term.
        eapply frame_indep_nil in Hd. exact Hd. 2: lia.
        change clock to (25 + k1).
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
        simpl in H13. repeat deriv.
        (* evaluation *)
        simpl. destruct (eval_length [v]) eqn:EQ.
        {
          simpl in EQ. break_match_hyp; try congruence.
        }
        {
          exists (29 + k + k2). simpl.
          econstructor. eapply step_term_term.
          eapply frame_indep_nil in Hd. exact Hd. 2: lia.
          change clock to (28 + k2).
          econstructor. reflexivity.
          simpl. econstructor. constructor.
          do 2 constructor. auto.
          do 2 constructor. auto.
          do 2 constructor. congruence.
          constructor. now inv H1. econstructor. reflexivity.
          apply eval_length_number in EQ as EQ'.
          intuition; destruct_hyps. inv H2. inv H6.
          inv EQ.
          { (* v = VNil*)
            inv H4.
          }
          (* boiler plate so that we can see the individual steps
             of the evaluation *)
          { (* v = VCons v1 v2 *)
            inv H5.
            apply eval_length_positive in EQ as EQ'.
            Opaque eval_length. simpl. rewrite EQ.
            econstructor. reflexivity. simpl.
            econstructor. econstructor. auto.
            do 2 constructor. auto.
            do 2 constructor. congruence.
            econstructor. auto. econstructor. econstructor. auto.
            econstructor. reflexivity. cbn. break_match_goal. lia.
            econstructor. reflexivity. simpl.
            econstructor. constructor. econstructor.
            econstructor. reflexivity.
            econstructor. auto. econstructor. simpl. assumption.
          }
        }
        {
          (* boiler plate so that we can see the individual steps
             of the evaluation *)
          exists (19 + k + k2). simpl.
          econstructor. eapply step_term_term.
          eapply frame_indep_nil in Hd. exact Hd. 2: lia.
          change clock to (18 + k2).
          econstructor. reflexivity.
          simpl. econstructor. constructor.
          do 2 constructor. auto.
          do 2 constructor. auto.
          do 2 constructor. congruence.
          constructor. now inv H1. econstructor. reflexivity. cbn.
          rewrite EQ.
          Transparent eval_length.
          econstructor. reflexivity.
          destruct e, p. apply cool_try_err.
          econstructor. auto. econstructor. econstructor. reflexivity.
          econstructor. auto. econstructor. cbn.
          assumption.
        }
        {
          simpl in EQ. break_match_hyp; inv EQ.
        }
      }
      { (* pattern matching fails due to the degree of ˝vs˝ - in the concrete Core Erlang implementation this cannot happen, because such programs are filtered out by the compiler *)
        inv H13. congruence. inv H14. simpl.
        (* evaluation *)
        exists (5 + k2 + k). simpl.
        econstructor. eapply step_term_term.
        eapply frame_indep_nil in Hd. exact Hd. 2: lia.
        change clock to (4 + k2).
        constructor. assumption.
        constructor. assumption.
        constructor. assumption.
        constructor. assumption.
      }
    }
    apply -> subst_preserves_scope_exp; eauto.
  Qed.

End length_0.

Ltac do_step := econstructor; [constructor;auto| simpl].

Local Goal
  ⟨ [], nonidiomatic2 (˝VNil) (˝VLit 0%Z) (˝VLit 1%Z) ⟩ -->* RValSeq [VLit 0%Z].
Proof.
  unfold nonidiomatic2, step_any. eexists. split. constructor; auto.
  do 2 do_step.
  do 1 do_step. reflexivity. cbn.
  do 3 do_step.
  do 1 do_step.
  do 2 do_step.
  do 2 do_step. congruence.
  do 1 do_step. econstructor. econstructor. reflexivity.
  do 7 do_step. congruence.
  do 3 do_step. econstructor. econstructor. cbn. reflexivity.
  do 4 do_step. constructor.
Qed.

Local Goal
  ⟨ [], nonidiomatic2 (ECons (˝ttrue) (˝VNil)) (˝VLit 0%Z) (˝VLit 1%Z) ⟩ -->* RValSeq [VLit 1%Z].
Proof.
  unfold nonidiomatic2, step_any. eexists. split. constructor; auto.
  do 5 do_step.
  do 2 do_step. reflexivity. cbn.
  do 3 do_step.
  do 1 do_step.
  do 2 do_step.
  do 2 do_step. congruence.
  do_step. econstructor. econstructor. reflexivity.
  do 7 do_step. congruence.
  do 3 do_step. econstructor. econstructor. reflexivity.
  do 2 do_step.
  do 2 do_step. reflexivity.
  do 3 do_step. constructor.
Qed.

Local Goal
  ⟨ [], nonidiomatic2 (˝VLit 0%Z) (˝VLit 0%Z) (˝VLit 1%Z) ⟩ -->* RValSeq [VLit 1%Z].
Proof.
  unfold nonidiomatic2, step_any. eexists. split. constructor; auto.
  do 2 do_step.
  do 1 do_step. reflexivity. cbn.
  do 3 do_step.
  do 1 do_step.
  do 2 do_step.
  do 2 do_step. congruence.
  do_step. econstructor. econstructor. reflexivity.
  do_step.
  do_step.
  do 3 do_step. reflexivity.
  do 2 do_step.
  do_step. constructor.
Qed.

Section list_app_reverse.
(*
  From Francesco Cesarini, Simon Thompson: Erlang programming

double([X|T], Buffer) ->
  double(T, Buffer ++ [X*2]);
double([], Buffer) ->
  Buffer.

double2([X|T], Buffer) ->
  double2(T, [X*2|Buffer]);
double2([], Buffer) ->
  lists:reverse(Buffer).
*)

  Open Scope string_scope.
  Variables (e1 e2 f : Exp) (Γ : nat).
  Hypotheses (He1 : EXP Γ ⊢ e1)
             (He2 : EXP Γ ⊢ e2)
             (He3 : EXP Γ ⊢ f).

  Local Definition nonidiomatic3 :=
    ELetRec 
      [(2, °ECase (EValues [˝VVar 1;˝VVar 2])
        [
          ([PCons PVar PVar; PVar], ˝ttrue, 
             °ELet 1 (EApp f [˝VVar 0])
               (ELet 1 (ECall (˝VLit "erlang") (˝VLit "++") [˝VVar 3;˝VVar 0])
                 (EApp (˝VFunId (5, 2)) [˝VVar 3; ˝VVar 0])
               )
          );
          ([PNil; PVar], ˝ttrue,
            ˝VVar 0
          );
          ([PVar; PVar], ˝VLit "true", °EPrimOp "match_fail" [°ETuple [˝VLit "function_clause";˝VVar 0; ˝VVar 1]])
        ])]
        (EApp (˝VFunId (0, 2)) [e1;e2]).

  Local Definition idiomatic3 :=
    ELetRec 
      [(2, °ECase (EValues [˝VVar 1;˝VVar 2])
        [
          ([PCons PVar PVar; PVar], ˝ttrue, 
             °ELet 1 (EApp f [˝VVar 0])
               (EApp (˝VFunId (4, 2)) [˝VVar 2; °ECons (˝VVar 0) (˝VVar 3)])
          );
          ([PNil; PVar], ˝ttrue,
            °ECall (˝VLit "lists") (˝VLit "reverse") [˝VVar 0]
          );
          ([PVar; PVar], ˝VLit "true", °EPrimOp "match_fail" [°ETuple [˝VLit "function_clause";˝VVar 0; ˝VVar 1]])
        ])]
        (EApp (˝VFunId (0, 2)) [e1;e2]).

  Local Proposition nonidiomatic3_scope :
    EXP Γ ⊢ nonidiomatic3.
  Proof.
    unfold nonidiomatic3.
    scope_solver.
  Qed.

  Local Proposition idiomatic3_scope :
    EXP Γ ⊢ idiomatic3.
  Proof.
    unfold idiomatic.
    scope_solver.
  Qed.

  Local Theorem equivalence3_part1 :
    CIU_open Γ nonidiomatic3 idiomatic3.
  Proof.
    
  Abort.

  Local Theorem equivalence3_part2 :
    CIU_open Γ idiomatic3 nonidiomatic3.
  Proof.
  
  Abort.
End list_app_reverse.

(* Lemma CIU_beta_value : forall {Γ e2 x v},
    EXP S Γ ⊢ e2 -> VAL Γ ⊢ v ->
    (CIU_open Γ e2.[v/] (ELet x v e2) /\ 
     CIU_open Γ (ELet x v e2) e2.[v/]).
 *)

Local Theorem beta_reduction_let_single Γ e2 v:
  EXP S Γ ⊢ e2 -> VAL Γ ⊢ v ->
  (CIU_open Γ e2.[v/] (ELet 1 (˝v) e2) /\ 
   CIU_open Γ (ELet 1 (˝v) e2) e2.[v/]).
Proof.
  apply CIU_beta_value.
Qed.
(* Lemma CIU_beta_values : forall {Γ e vl vals},
    VAL Γ ⊢ EFun vl e -> Forall (fun v => VAL Γ ⊢ v) vals -> length vl = length vals ->
    (CIU_open Γ (e.[list_subst (EFun vl e :: vals) idsubst]) (EApp (EFun vl e) vals) /\ 
     CIU_open Γ (EApp (EFun vl e) vals) (e.[list_subst (EFun vl e :: vals) idsubst])).
 *)

Local Theorem beta_reduction_apply Γ ext vl vals id e:
  VAL Γ ⊢ VClos ext id vl e ->
  Forall (ValScoped Γ) vals ->
  vl = length vals ->
  CIU_open Γ (EApp (˝VClos ext id vl e) (map VVal vals)) (e.[list_subst (convert_to_closlist ext ++ vals) idsubst]) /\
  CIU_open Γ (e.[list_subst (convert_to_closlist ext ++ vals) idsubst]) (EApp (˝VClos ext id vl e) (map VVal vals)).
Proof.
  intros.
  unfold CIU_open.
  assert (forall ξ, SUBSCOPE Γ ⊢ ξ ∷ 0 -> REDCLOSED (° EApp (˝ VClos ext id vl e) (map VVal vals)).[ξ]ᵣ) as Happ. {
    intros. constructor. apply -> subst_preserves_scope_exp; eauto.
    do 2 constructor; try apply indexed_to_forall; try assumption.
    2: now apply Valscope_lift.
    now constructor.
  }
  assert (forall ξ, SUBSCOPE Γ ⊢ ξ ∷ 0 -> VALCLOSED (VClos ext id vl e).[ξ]ᵥ) as Hclos. {
    intros. apply -> subst_preserves_scope_val. eassumption. assumption.
  }
  assert (forall ξ, SUBSCOPE Γ ⊢ ξ ∷ 0 -> exists k, ⟨[], (° EApp (˝ VClos ext id vl e) (map VVal vals)).[ξ]ᵣ⟩ -[k]-> ⟨[], e.[list_subst (convert_to_closlist ext ++ vals) idsubst].[ξ]ᵣ⟩).
  {
    intros. simpl.
    specialize (Happ _ H2).
    specialize (Hclos _ H2).
    assert (length ext + length vals = length (convert_to_closlist (map (fun '(i, ls, x) => (i, ls, x.[upn (Datatypes.length ext + ls) ξ]))
           ext) ++ map (substVal ξ) vals)) as Hl. {
      intros.
      unfold convert_to_closlist; now rewrite app_length, map_length, map_length, map_length.
    }
    destruct vals; simpl in *; subst.
    * (* no parameters *)
      eexists.
      do 3 do_step. rewrite app_nil_r.
      econstructor. econstructor. congruence.
      reflexivity.
      rewrite subst_comp_exp.
      rewrite Hl.
      rewrite substcomp_list. rewrite app_nil_r, substcomp_id_r.
      rewrite subst_comp_exp.
      rewrite scons_substcomp_list.
      unfold convert_to_closlist. simpl.
      repeat rewrite map_map.
      assert ((fun x : nat * nat * Exp =>
         let
         '(id0, vc, e0) :=
          let '(i, ls, x0) := x in (i, ls, x0.[upn (Datatypes.length ext + ls) ξ])
          in
          VClos
            (map
               (fun '(i, ls, x0) =>
                (i, ls, x0.[upn (Datatypes.length ext + ls) ξ])) ext) id0 vc e0) =
           (fun x : nat * nat * Exp =>
         (let '(id0, vc, e0) := x in VClos ext id0 vc e0).[ξ]ᵥ)). {
        clear. extensionality x. now destruct x, p.
      }
      rewrite H1. now constructor.
    * (* at least one parameter *)
      eexists.
      do 3 do_step.
      simpl. do_step. congruence. do_step.
      {
        inv H0. clear-H2 H4. apply -> subst_preserves_scope_val; eassumption.
      }
      replace (map (fun x : Exp => x.[ξ]) (map VVal vals)) with
        (map VVal (map (substVal ξ) vals)).
      2: {
        clear. do 2 rewrite map_map. now f_equal.
      }
      eapply params_eval_create.
      {
        clear -H0 H2.
        inv H0. induction H4; auto.
        constructor.
        2: assumption.
        apply -> subst_preserves_scope_val; eassumption.
      }
      {
        simpl. rewrite map_length, Nat.eqb_refl.
        f_equal. f_equal.
        do 2 rewrite subst_comp_exp.
        rewrite Hl.
        rewrite substcomp_list.
        rewrite scons_substcomp_list.
        unfold convert_to_closlist. simpl.
        repeat rewrite map_map. rewrite map_app.
        rewrite map_map. repeat rewrite substcomp_id_r, substcomp_id_l.
        assert (X : (fun x : nat * nat * Exp =>
         (let '(id0, vc, e0) := x in VClos ext id0 vc e0).[ξ]ᵥ) =
         (fun x : nat * nat * Exp =>
         let
         '(id0, vc, e0) :=
          let '(i, ls, x0) := x in (i, ls, x0.[upn (Datatypes.length ext + ls) ξ])
          in
          VClos
            (map
               (fun '(i, ls, x0) =>
                (i, ls, x0.[upn (Datatypes.length ext + ls) ξ])) ext) id0 vc e0)).
         {
           extensionality x. destruct x, p. now simpl.
         }
         rewrite X. reflexivity.
      }
  }
  split; intros.
  1: {
     apply H2 in H3 as H3'.
     apply Happ in H3.
     destruct H3'.
     now apply CIU_eval_base in H4.
  }
  1: {
     apply H2 in H3 as H3'.
     apply Happ in H3.
     destruct H3'.
     now apply CIU_eval_base in H4.
  }
Qed.

(* Theorem plus_comm : forall Γ e1 e2,
  EXP Γ ⊢ e1 -> EXP Γ ⊢ e2 ->
  EBIF (ELit "+"%string) [e1; e2] ≈[Γ]≈ EBIF (ELit "+"%string) [e2; e1].
Proof.
 *)

(* Theorem let_delay : forall Γ e x e',
  EXP Γ ⊢ e -> EXPCLOSED e' -> | [], e' | ↓ ->
  e ≈[Γ]≈ ELet x e' (rename (fun n => S n) e).
 *)

(* Theorem map_foldr_equiv :
  forall l' l x y z e f
  (VsCL : VALCLOSED l) (SCE : EXP 2 ⊢ e),
  computes x e f -> cons_to_list l = Some l' ->
  CIU (obj_map (EFun [x] e) l) (obj_foldr (EFun [y;z] (ECons (EApp (EFun [x] e) [EVar 1]) (EVar 2))) l ENil).
 *)

(* Theorem eta_abstraction Γ e :
  EXP Γ ⊢ e ->
  e ≈[Γ]≈ EApp (EFun [] (rename (fun n => S n) e)) [].
 *)
  
