From CoreErlang.FrameStack Require Export CIU.

Import ListNotations.

Ltac scope_solver_step :=
  match goal with 
  | |- EXP _ ⊢ _ => constructor; simpl; auto
  | |- VAL _ ⊢ _ => constructor; simpl; auto
  | |- RED _ ⊢ _ => constructor; simpl; auto
  | |- NVAL _ ⊢ _ => constructor; simpl; auto
  | |- forall i, i < _ -> _ => simpl; intros
  | [H : ?i < _ |- _] => inv H; simpl in *; auto; try lia
  | [H : ?i <= _ |- _] => inv H; simpl in *; auto; try lia
  | [H : EXP ?n1 ⊢ ?e |- EXP ?n2 ⊢ ?e] => try now (eapply (loosen_scope_exp n2 n1 ltac:(lia)) in H)
  | [H : VAL ?n1 ⊢ ?e |- VAL ?n2 ⊢ ?e] => try now (eapply (loosen_scope_val n2 n1 ltac:(lia)) in H)
  | [H : NVAL ?n1 ⊢ ?e |- NVAL ?n2 ⊢ ?e] => try now (eapply (loosen_scope_nonval n2 n1 ltac:(lia)) in H)
  end.

Ltac scope_solver := repeat scope_solver_step; try lia.

Ltac deriv :=
  match goal with
  | [H : ?i < length _ |- _] => simpl in *; inv H; auto; try lia
  | [H : ?i <= length _ |- _] => simpl in *; inv H;  auto; try lia
  | [H : | _, _ | ↓ |- _] => inv H; try inv_val
  | [H : | _ :: _, RValSeq _ | _ ↓ |- _] => inv H; try inv_val
  | [H : | _ :: _, RExc _ | _ ↓ |- _] => inv H; try inv_val
  | [H : | _, RExp (EExp _) | _ ↓ |- _] => inv H; try inv_val
  | [H : | _, RExp (VVal _) | _ ↓ |- _] => inv H; try inv_val
  | [H : | _, RBox | _ ↓ |- _] => inv H; try inv_val
  end.

Ltac extract_meta_eval H :=
  let r := fresh "r" in
  let k := fresh "k" in
  let Hr := fresh "Hr" in
  let Hd := fresh "Hd" in
  let Hd' := fresh "Hd'" in
  let Hk := fresh "Hk" in
  let H' := fresh "H'" in
  eapply term_eval_both in H as H'; destruct H' as [r [k [Hr [Hd [Hd' Hk]]]]];
  eapply term_step_term in Hd'; [|eassumption]; inv Hr.

Theorem length_succ {B : Type} (a2 : B) (n : nat) (l2 : list B):
  n = length l2
  ->
  S n = length (a2 :: l2).
Proof.
  intros. simpl. rewrite H. auto.
Qed.

Ltac unfold_list := 
  match goal with
  | [H : length ?l = 0 |- _] => destruct l; try inv H
  | [H : 0 = length ?l |- _] => destruct l; try inv H
  | [H : length ?l = S ?n |- _] => destruct l; try inv H; unfold_list
  | [H : S ?n = length ?l |- _] => destruct l; try inv H; unfold_list
  end.

Tactic Notation "replace" "counter" "with" constr(num) :=
  match goal with
  | |- | _, _ | ?k ↓ => replace k with num by lia
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
        inv Hd'. clear H5.
        unfold idiomatic.
        exists (S (S k1 + k0)). simpl. econstructor.
        eapply frame_indep_nil in Hd.
        eapply step_term_term. eassumption. 2: lia.
        replace (S (k1 + k0) - k0) with (S k1) by lia. constructor. congruence.
        eassumption.
      }
      { (* e1 evaluates correctly *)
        deriv. unfold_list. simpl in H7.
        do 3 deriv.
        { (* v is true *)
          simpl in H10. destruct v; try congruence. break_match_hyp; try congruence.
          break_match_hyp; try congruence. destruct l; simpl in Heqb; try congruence.
          break_match_hyp; try congruence. inv Heqo. simpl in H10. inv H10.
          simpl in H11. do 2 deriv.
          cbn in H9. inv H9.
          unfold idiomatic.
          exists (S (12 + k2 + k0)). simpl. econstructor.
          eapply frame_indep_nil in Hd.
          eapply step_term_term. eassumption. 2: lia.
          replace counter with (12 + k2).
          constructor. reflexivity.
          simpl. constructor.
          constructor. econstructor. congruence. simpl. reflexivity.
          econstructor. reflexivity.
          simpl. constructor. econstructor. congruence.
          constructor. constructor. constructor. simpl. econstructor. cbn. reflexivity.
          econstructor. reflexivity. eassumption.
        }
        { (* v is not true *)
          deriv.
          2: { (* no more cases *)
            inv H9.
          }
          simpl in H12. do 2 deriv. rewrite H11 in H9. inv H9.
          unfold idiomatic.
          exists (S (15 + k1 + k0)). simpl. econstructor.
          eapply frame_indep_nil in Hd.
          eapply step_term_term. eassumption. 2: lia.
          replace counter with (15 + k1).
          constructor. reflexivity.
          simpl. constructor.
          constructor. econstructor. congruence. simpl. reflexivity.
          econstructor. reflexivity.
          simpl. constructor. econstructor. congruence.
          constructor. constructor. constructor. simpl. econstructor.
          { (* v is not true *)
            cbn. clear Hd H11 H12 H6. destruct v; simpl; try reflexivity.
            2: destruct n; reflexivity.
            destruct l; try reflexivity. simpl.
            destruct string_dec; try reflexivity. subst. simpl in H10. congruence.
          } 
          constructor. econstructor. reflexivity. constructor. econstructor.
          reflexivity.
          simpl in H11. inv H11.
          do 2 rewrite subst_comp_exp in *.
          clear Hd H10. cbn in *.
          rewrite substcomp_id_r.
          rewrite subst_extend in H12.
          rewrite substcomp_scons_core, subst_extend in H12.
          rewrite subst_extend.
          rewrite subst_comp_exp in *.
          rewrite ren_scons in *.
          rewrite ren_scons in H12. assumption.
        }
      }
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
    2: { (* technical, Q: should this be possible? Evaluation of variables shouldn't just fail? -> variables are values or expressions? *)
      do 3 deriv. cbn in H11.
      do 2 deriv. 2: { deriv. inv H12. }
      simpl in H13. do 2 deriv. inv H11. inv H12.
      exists (6 + k0). simpl.
      econstructor. rewrite Heqs. do 2 constructor. reflexivity.
      econstructor. reflexivity. simpl. constructor. econstructor.
      reflexivity. simpl.
      rewrite subst_comp_exp in *. simpl in *.
      rewrite subst_extend, subst_comp_exp in *.
      rewrite substcomp_id_r, ren_scons in *. assumption.
    }
    do 3 deriv. cbn in H11.
    break_match_hyp.
    { (* e1 is true *)
      deriv. inv H9. simpl in H12. rewrite idsubst_is_id_exp in H12.
      exists (5 + k). simpl.
      econstructor. rewrite Heqs.
      destruct v; simpl in Heqb; try congruence.
      destruct l; simpl in Heqb; try congruence.
      break_match_hyp; try congruence. subst.
      econstructor. econstructor. reflexivity.
      constructor. econstructor. reflexivity.
      simpl. now rewrite idsubst_is_id_exp.
    }
    { (* e1 is false *)
      do 2 deriv. 2: { inv H12. }
      simpl in H13. do 2 deriv. inv H12. inv H11.
      exists (6 + k0). simpl.
      econstructor. rewrite Heqs. do 2 constructor.
      {
        destruct v; simpl in Heqb; try reflexivity.
        destruct l; simpl in Heqb; try reflexivity.
        break_match_hyp; subst; try congruence.
        cbn. destruct string_dec; auto. congruence.
      }
      econstructor. reflexivity. simpl. constructor. econstructor.
      reflexivity. simpl.
      rewrite subst_comp_exp in *. simpl in *.
      rewrite subst_extend, subst_comp_exp in *.
      rewrite substcomp_id_r, ren_scons in *. assumption.
    }
  Qed.
End case_if_equiv.

