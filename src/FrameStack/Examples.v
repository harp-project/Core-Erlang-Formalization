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
              ([PVar], `VLit "true", e3)]).

  Local Definition idiomatic :=
    ELet 1 e1
      (ECase (EValues [])
          [([], °ECall "=:=" [`VVar 0;`VLit "true"], e2);
          ([], `VLit "true", e3)]).

  Local Proposition nonidiomatic_scope :
    EXP Γ ⊢ nonidiomatic.
  Proof.
    unfold nonidiomatic.
    scope_solver.
  Qed.

  Local Proposition idiomatic_scope :
    EXP Γ ⊢ idiomatic.
  Proof.
    unfold idiomatic.
    scope_solver.
  Qed.

  Local Theorem equivalence :
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
          unfold idiomatic.
          exists (S (15 + k2 + k0)). simpl. econstructor.
          eapply frame_indep_nil in Hd.
          eapply step_term_term. eassumption. 2: lia.
          replace counter with (15 + k2).
          constructor. reflexivity.
          simpl. constructor.
          constructor. econstructor. congruence. simpl. reflexivity.
          econstructor. reflexivity.
          simpl. constructor. econstructor. congruence.
          constructor. constructor. constructor. simpl. econstructor.
          unfold create_result.
        }
        { (* v is not true *)

        }
        
      }
    }
  Qed.
  Local Theorem equivalence :
    CIU idiomatic nonidiomatic.
  Proof.

  Qed.
End case_if_equiv.

