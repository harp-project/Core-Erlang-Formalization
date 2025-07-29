(**
This file defines "CIU" equivalence of redexes. This definition is the most
simple to show for concrete Core Erlang programs, thus we will use it for
showing the correctness of concrete refactorings.
*)

From CoreErlang.FrameStack Require Export Compatibility.

Import ListNotations.

Definition CIU (r1 r2 : Redex) : Prop :=
  REDCLOSED r1 /\ REDCLOSED r2 /\
  forall F, FSCLOSED F -> | F, r1 | ↓ -> | F, r2 | ↓.

Definition CIU_open (Γ : nat) (r1 r2 : Redex) :=
  forall ξ, SUBSCOPE Γ ⊢ ξ ∷ 0 ->
  CIU (r1.[ξ]ᵣ) (r2.[ξ]ᵣ).

Lemma CIU_closed :
  forall r1 r2,
  CIU r1 r2 -> REDCLOSED r1 /\ REDCLOSED r2.
Proof.
  intros. unfold CIU in H. intuition.
Qed.


Lemma CIU_closed_l : forall {r1 r2},
    CIU r1 r2 ->
    REDCLOSED r1.
Proof.
  intros.
  apply CIU_closed in H.
  intuition.
Qed.

Global Hint Resolve CIU_closed_l : core.



Lemma CIU_closed_r : forall {r1 r2},
    CIU r1 r2 ->
    REDCLOSED r2.
Proof.
  intros.
  apply CIU_closed in H.
  intuition.
Qed.

Global Hint Resolve CIU_closed_r : core.

Lemma CIU_open_scope : forall {Γ r1 r2},
    CIU_open Γ r1 r2 ->
    RED Γ ⊢ r1 /\ RED Γ ⊢ r2.
Proof.
  intros.
  unfold CIU_open in H.
  split; eapply subst_implies_scope_red; intros; apply H in H0; auto;
    now apply CIU_closed in H0.
Qed.


Lemma CIU_open_scope_l : forall {Γ r1 r2},
    CIU_open Γ r1 r2 ->
    RED Γ ⊢ r1.
Proof.
  intros.
  apply CIU_open_scope in H.
  intuition.
Qed.


Global Hint Resolve CIU_open_scope_l : core.

Lemma CIU_open_scope_r : forall {Γ r1 r2},
    CIU_open Γ r1 r2 ->
    RED Γ ⊢ r2.
Proof.
  intros.
  apply CIU_open_scope in H.
  intuition.
Qed.

Global Hint Resolve CIU_open_scope_r : core.

Lemma Rrel_implies_CIU : forall Γ r1 r2,
  Rrel_open Γ r1 r2 ->
  CIU_open Γ r1 r2.
Proof.
  intros.
  unfold CIU_open; intros.
  unfold CIU.
  split. 2: split.
  - apply -> (subst_preserves_scope_red); eauto.
  - apply -> (subst_preserves_scope_red); eauto.
  - intros. inv H2. eapply H. 3: apply Frel_Fundamental_closed; auto. 3: eassumption.
    apply Grel_Fundamental; auto.
    reflexivity.
Qed.

Lemma Rrel_comp_CIU_implies_Rrel : forall {Γ r1 r2 r3},
    Rrel_open Γ r1 r2 ->
    CIU_open Γ r2 r3 ->
    Rrel_open Γ r1 r3.
Proof.
  intros Γ r1 r2 r3 HRrel HCIU.
  intros.
  split. 2: split. 1-2: apply -> subst_preserves_scope_red; eauto; apply H.
  intros. eapply HRrel in H1; eauto. eapply HCIU in H1; eauto.
  apply H.
Qed.

Lemma CIU_implies_Rrel : forall {Γ r1 r2},
    CIU_open Γ r1 r2 ->
    Rrel_open Γ r1 r2.
Proof.
  intros.
  eapply Rrel_comp_CIU_implies_Rrel; eauto.
  apply Rrel_Fundamental.
  now apply CIU_open_scope_l in H.
Qed.

Theorem CIU_iff_Rrel : forall {Γ r1 r2},
    CIU_open Γ r1 r2 <->
    Rrel_open Γ r1 r2.
Proof.
  intuition (auto using CIU_implies_Rrel, Rrel_implies_CIU).
Qed.

Corollary CIU_iff_Rrel_closed : forall {r1 r2},
  CIU r1 r2 <->
  (forall m, Rrel m r1 r2).
Proof.
  intros.
  split.
  {
    split. 2: split. 1-2: apply H.
    intros. eapply H. apply H0.
    pose proof (Rrel_Fundamental_closed m0 r1 ltac:(apply H)).
    eapply H2; eauto.
  }
  {
    intros.
    split. 2: split. 1-2: apply (H 0).
    intros.
    inv H1. eapply H in H2. eassumption. reflexivity. auto.
  }
Qed.

Theorem CIU_eval_base : forall k r1 r2,
  REDCLOSED r1 ->
  ⟨ [], r1 ⟩ -[k]-> ⟨[], r2⟩ -> CIU r1 r2 /\ CIU r2 r1.
Proof.
  intros. split. split. 2: split. assumption.
  1: apply step_any_closedness in H0 as [? ?]; eauto.
  1: now constructor.

  intros. destruct H2 as [k0 H2]. eapply frame_indep_nil in H0.
  eapply term_step_term in H0. 2: eassumption. eexists. eassumption.

  split. 2: split. 2: assumption.
  1: apply step_any_closedness in H0 as [? ?]; eauto.
  1: now constructor.

  intros. destruct H2 as [k0 H2]. eapply frame_indep_nil in H0.
  eapply step_term_term_plus in H0. 2: eassumption. eexists. eassumption.
Qed.

Theorem CIU_eval : forall r1 v,
  REDCLOSED r1 ->
  ⟨ [], r1 ⟩ -->* v -> CIU r1 v /\ CIU v r1.
Proof.
  intros. destruct H0 as [k [H0 H1]].
  apply CIU_eval_base in H1; assumption.
Qed.

Theorem CIU_transitive_closed :
  forall x y z, CIU x y -> CIU y z -> CIU x z.
Proof.
  unfold CIU; intros. intuition.
Qed.

Theorem CIU_transitive :
  forall Γ x y z, CIU_open Γ x y -> CIU_open Γ y z -> CIU_open Γ x z.
Proof.
  unfold CIU_open; intros. intuition.
  eapply CIU_transitive_closed. apply H; auto. apply H0; auto.
Qed.

Corollary CIU_compat_reverse :
  forall v v' : Val, CIU (˝v) (˝v') -> CIU (RValSeq [v]) (RValSeq [v']).
Proof.
  intros. assert (⟨[], ˝v⟩ -->* RValSeq [v]). {
    apply CIU_closed_l in H. destruct_scopes.
    eexists. split; auto. econstructor. constructor; auto.
    econstructor.
  }
  assert (⟨[], ˝v'⟩ -->* RValSeq [v']). {
    apply CIU_closed_r in H. destruct_scopes.
    eexists. split; auto. econstructor. constructor; auto. constructor.
  }
  apply CIU_eval in H0, H1. 2-3: apply H. intuition.
  epose proof (CIU_transitive_closed _ _ _ H H0).
  now epose proof (CIU_transitive_closed _ _ _ H3 H1).
Qed.

Theorem CIU_Val_compat_closed_reverse :
  forall (v v' : Val), CIU (˝v) (˝v') -> forall m, Vrel m v v'.
Proof.
  valinduction; try destruct v'; intros; auto; destruct H as [Hcl1 [Hcl2 H]].
  1-8: epose proof (H [FCase1 [([PNil], ˝ttrue, ˝VNil);([PVar], ˝ttrue , °inf)]] ltac:(scope_solver) _) as H0;
       repeat deriv; inv H9; inv H8; simpl in H11; do 2 deriv; simpl in H8; apply inf_diverges in H8; contradiction.
  1,3-9: epose proof (H [FCase1 [([PLit l], ˝ttrue, ˝VNil);([PVar], ˝ttrue , °inf)]] ltac:(scope_solver) _) as H0; repeat deriv; inv H9; inv H8; simpl in H11; do 2 deriv; simpl in H8; apply inf_diverges in H8; contradiction.
  (* PIDs have to be handled separately *)
  Opaque Val_eqb.
  2: {
    assert (| [FParams (ICall (VLit "erlang"%string) (VLit "=="%string)) [VNil] [];
           FCase1 [([PLit "true"%string], ˝ttrue, °inf); ([PVar], ˝ttrue, ˝ok)]], ˝ VPid p | ↓ ) as D. {
      econstructor. do 8 econstructor. auto.
    }
    epose proof (H 
          [FParams (ICall (VLit "erlang"%string) (VLit "=="%string)) [VNil] [];
           FCase1 [([PLit "true"%string], ˝ttrue, °inf); ([PVar], ˝ttrue, ˝ok)]] ltac:(destruct_scopes;scope_solver) D) as H0; clear D; repeat deriv.
    cbn in H7. inv H7. rewrite Val_eqb_refl in H8.
    repeat deriv. inv H9. simpl in *. do 2 deriv.
    now apply inf_diverges in H8.
    inv H8. inv H9.
  }
  2: {
    assert (| [FParams (ICall (VLit "erlang"%string) (VLit "=="%string)) [VLit l] [];
           FCase1 [([PLit "true"%string], ˝ttrue, °inf); ([PVar], ˝ttrue, ˝ok)]], ˝ VPid p | ↓ ) as D. {
      econstructor. do 8 econstructor. auto.
    }
    epose proof (H 
          [FParams (ICall (VLit "erlang"%string) (VLit "=="%string)) [VLit l] [];
           FCase1 [([PLit "true"%string], ˝ttrue, °inf); ([PVar], ˝ttrue, ˝ok)]] ltac:(destruct_scopes;scope_solver) D) as H0; clear D; repeat deriv.
    cbn in H7. rewrite Val_eqb_refl in H7.
    inv H7. repeat deriv. inv H9. simpl in *. do 2 deriv.
    now apply inf_diverges in H8.
    inv H8. inv H9.
  }
  2: {
    assert (| [FParams (ICall (VLit "erlang"%string) (VLit "=="%string)) [VCons v'1 v'2] [];
           FCase1 [([PLit "true"%string], ˝ttrue, °inf); ([PVar], ˝ttrue, ˝ok)]], ˝ VPid p | ↓ ) as D. {
      econstructor. do 8 econstructor. auto.
    }
    epose proof (H 
          [FParams (ICall (VLit "erlang"%string) (VLit "=="%string)) [VCons v'1 v'2] [];
           FCase1 [([PLit "true"%string], ˝ttrue, °inf); ([PVar], ˝ttrue, ˝ok)]] ltac:(destruct_scopes;scope_solver) D) as H0; clear D; repeat deriv.
    cbn in H7. rewrite Val_eqb_refl in H7.
    inv H7. repeat deriv. inv H9. simpl in *. do 2 deriv.
    now apply inf_diverges in H8.
    inv H8. inv H9.
  }
  2: {
    assert (| [FParams (ICall (VLit "erlang"%string) (VLit "=="%string)) [VTuple l] [];
           FCase1 [([PLit "true"%string], ˝ttrue, °inf); ([PVar], ˝ttrue, ˝ok)]], ˝ VPid p | ↓ ) as D. {
      econstructor. do 8 econstructor. auto.
    }
    epose proof (H 
          [FParams (ICall (VLit "erlang"%string) (VLit "=="%string)) [VTuple l] [];
           FCase1 [([PLit "true"%string], ˝ttrue, °inf); ([PVar], ˝ttrue, ˝ok)]] ltac:(destruct_scopes;scope_solver) D) as H0; clear D; repeat deriv.
    cbn in H7. rewrite Val_eqb_refl in H7.
    inv H7. repeat deriv. inv H9. simpl in *. do 2 deriv.
    now apply inf_diverges in H8.
    inv H8. inv H9.
  }
  2: {
    assert (| [FParams (ICall (VLit "erlang"%string) (VLit "=="%string)) [VMap l] [];
           FCase1 [([PLit "true"%string], ˝ttrue, °inf); ([PVar], ˝ttrue, ˝ok)]], ˝ VPid p | ↓ ) as D. {
      econstructor. do 8 econstructor. auto.
    }
    epose proof (H 
          [FParams (ICall (VLit "erlang"%string) (VLit "=="%string)) [VMap l] [];
           FCase1 [([PLit "true"%string], ˝ttrue, °inf); ([PVar], ˝ttrue, ˝ok)]] ltac:(destruct_scopes;scope_solver) D) as H0; clear D; repeat deriv.
    cbn in H7. rewrite Val_eqb_refl in H7.
    inv H7. repeat deriv. inv H9. simpl in *. do 2 deriv.
    now apply inf_diverges in H8.
    inv H8. inv H9.
  }
  2: {
    destruct_scopes. lia.
  }
  2: {
    destruct_scopes. lia.
  }
  2: {
    (* Trick with fun_info here: *)
    assert (| [FParams (ICall (VLit "erlang"%string) (VLit "fun_info"%string)) [] [˝VLit "arity"%string];
           FTry 1 inf 3 (˝ok)], ˝ VPid p | ↓ ) as D. {
      econstructor. repeat econstructor.
    }
    epose proof (H 
          [FParams (ICall (VLit "erlang"%string) (VLit "fun_info"%string)) [] [˝VLit "arity"%string];
           FTry 1 inf 3 (˝ok)] ltac:(destruct_scopes; scope_solver) D) as H0; clear D; repeat deriv.
    cbn in H8. rewrite Val_eqb_refl in H8.
    inv H8. repeat deriv.
    now apply inf_diverges in H11.
  }
  Transparent Val_eqb.
  (**)
  2-4,6-10: epose proof (H [FCase1 [([PCons PVar PVar], ˝ttrue, ˝VNil);([PVar], ˝ttrue , °inf)]] ltac:(scope_solver) _) as H0; repeat deriv; inv H9; inv H8; simpl in H11; do 2 deriv; simpl in H8; apply inf_diverges in H8; contradiction.
  3-6, 8-11: epose proof (H [FCase1 [([PTuple (repeat PVar (length l))], ˝ttrue, ˝VNil);([PVar], ˝ttrue , °inf)]] ltac:(scope_solver) _) as H0; repeat deriv; inv H9; inv H8; simpl in H11; do 2 deriv; simpl in H8; apply inf_diverges in H8; contradiction.
  4-8,10-12: epose proof (H [FCase1 [([PMap (repeat (PVar, PVar) (length l))], ˝ttrue, ˝VNil);([PVar], ˝ttrue , °inf)]] ltac:(scope_solver) _) as H0; repeat deriv; inv H9; inv H8; simpl in H11; do 2 deriv; simpl in H8; apply inf_diverges in H8; contradiction.
  5-22: destruct_scopes; lia.
  Unshelve. (* evaluation in the omitted proofs *)
  14-21: now do 10 econstructor.
  14-21:
    econstructor; econstructor; auto; econstructor;
    [simpl; rewrite Lit_eqb_refl; reflexivity|];
    simpl; econstructor; auto; constructor; econstructor;
    constructor; auto.
  14-19: congruence.
  14-21:
    destruct_scopes; econstructor; econstructor; auto; econstructor;
    [reflexivity|]; simpl; econstructor; auto; econstructor;
    constructor; auto;
    constructor; auto.
  14-21:
    destruct_scopes; econstructor; econstructor; auto; econstructor;
    [apply match_pattern_list_tuple_vars|]; simpl; econstructor; auto; econstructor;
    constructor; auto;
    constructor; auto.
  14-21:
    destruct_scopes; econstructor; econstructor; auto; econstructor;
    [apply match_pattern_list_map_vars|];
    simpl; econstructor; auto; econstructor;
    constructor; auto;
    constructor; auto.
  * epose proof (H [FCase1 [([PLit l], ˝ttrue, ˝VNil);([PVar], ˝ttrue , °inf)]] ltac:(scope_solver) _) as H0; repeat deriv.
    - simpl in H9. destruct Lit_beq eqn:EQ.
      + apply Lit_eqb_eq in EQ. subst. choose_compat_lemma.
      + congruence.
    - inv H8. cbn in H11. inv H11. inv H4. now apply inf_diverges in H8.
    - inv H8.
  Unshelve.
    econstructor; econstructor; auto; econstructor;
    [simpl; rewrite Lit_eqb_refl; reflexivity|];
    simpl; econstructor; auto; econstructor;
    constructor; auto;
    constructor; auto.
  * choose_compat_lemma.
    - apply IHv1. destruct_scopes. split. 2: split. 1-2: auto.
      intros. epose proof (H (FCase1 [([PCons PVar PVar], ˝ttrue, ˝VVar 0);([PVar], ˝ttrue , °inf)] :: F) ltac:(scope_solver) _) as H2; repeat deriv.
      + inv H16. cbn in H17. repeat deriv. exists (S k0). now econstructor.
      + inv H16.
      + inv H15.
    - apply IHv2. destruct_scopes. split. 2: split. 1-2: auto.
      intros. epose proof (H (FCase1 [([PCons PVar PVar], ˝ttrue, ˝VVar 1);([PVar], ˝ttrue , °inf)] :: F) ltac:(scope_solver) _) as H2; repeat deriv.
      + inv H16. cbn in H17. repeat deriv. exists (S k0). now econstructor.
      + inv H16.
      + inv H15.
  Unshelve.
    all: auto.
    all: destruct H1; destruct_scopes; econstructor; econstructor; auto;
       econstructor; [reflexivity|]; simpl; econstructor; auto;
       econstructor; eauto.
  (* Tuple *)
  * choose_compat_lemma.
    revert l0 Hcl2 H. induction l; destruct l0; intros.
    - now auto.
    - epose proof (H [FCase1 [([PTuple []], ˝ttrue, ˝VNil);([PVar], ˝ttrue , °inf)]] ltac:(scope_solver) _) as H0; repeat deriv.
      + inv H9.
      + cbn in H11. inv H11. inv H4. now apply inf_diverges in H10.
      + now inv H8.
    - epose proof (H [FCase1 [([PTuple (repeat PVar (length (a :: l)))], ˝ttrue, ˝VNil);([PVar], ˝ttrue , °inf)]] ltac:(scope_solver) _) as H0; repeat deriv.
      + inv H9.
      + cbn in H11. inv H11. inv H4. now apply inf_diverges in H10.
      + now inv H8.
    - inv IHv.
      assert (REDCLOSED (˝VTuple l) /\ REDCLOSED (˝VTuple l0)) as [IS1 IS2]. {
        destruct_scopes. split; do 3 constructor; intros;
        try apply (H4 (S i)); try apply (H5 (S i)); slia.
      }
      assert (forall F : FrameStack, FSCLOSED F -> | F, ˝ VTuple l | ↓ -> | F, ˝ VTuple l0 | ↓) as IS3. {
        intros.
        epose proof (H (FCase1 [([PTuple (repeat PVar (length (a :: l)))], ˝ttrue, ˝VTuple (varsFrom 1 (length l)));([PVar], ˝ttrue , °inf)] :: F) _ _) as H4.
        repeat deriv.
        * pose proof (match_pattern_list_tuple_vars_length (1 + length l) (v::l0) vs') as H1. simpl repeat in H1.
          apply H1 in H14 as H14'. destruct H14' as [Hlen EQ].
          simpl length in *. clear H1. inv EQ.
          simpl in H15. repeat deriv.
          pose proof (map_varsFrom (length l) 1 (v :: l0) ltac:(slia)) as H17'.
          simpl in H17'. rewrite H17' in H10.
          replace (length l) with (length l0) in H10 by lia.
          rewrite firstn_all in H10. exists (S k0). econstructor; eauto.
          inv IS2. now inv H9.
        * cbn in H16. inv H16. inv H9. now apply inf_diverges in H15.
        * inv H13.
      }
      specialize (IHl H3 IS1 _ IS2 IS3).
      constructor; auto.
      + apply H2. apply biforall_length in IHl as Hlen.
        split. 2: split.
        1-2: do 2 constructor; destruct_scopes; try apply (H6 0); try apply (H7 0); slia.
        intros. epose proof (H (FCase1 [([PTuple (repeat PVar (length (a :: l)))], ˝ttrue, ˝VVar 0);([PVar], ˝ttrue , °inf)] :: F) ltac:(scope_solver) _) as H4; repeat deriv.
        ** pose proof (match_pattern_list_tuple_vars (v :: l0)) as H1.
           simpl repeat in H1. rewrite <-Hlen in H1. rewrite H1 in H14.
           inv H14. simpl in H15. repeat deriv.
           exists (S k0). now econstructor.
        ** pose proof (match_pattern_list_tuple_vars (v :: l0)) as H1.
           simpl repeat in H1. rewrite <-Hlen in H1. rewrite H1 in H14.
           congruence.
        ** inv H13.
    Unshelve.
      all: auto.
      3: {
        constructor; auto. do 2 constructor.
        - do 3 constructor.
          intros.
          rewrite varsFrom_length in H4. simpl.
          rewrite scope_repeat_var.
          pose proof (varsFrom_scope (length l) 1 i).
          eapply loosen_scope_val. 2: eassumption. lia.
        - simpl in *.
          simpl. scope_solver.
      }
      {
        destruct_scopes; econstructor; econstructor; auto; econstructor;
        [reflexivity|]; simpl; econstructor; auto; econstructor;
        constructor; auto;
        constructor; auto.
      }
      {
        destruct_scopes; econstructor; econstructor; auto; econstructor;
        [apply match_pattern_list_tuple_vars|]; simpl; econstructor; auto. econstructor;
        constructor; auto;
        constructor; auto.
      }
      {
        inv H1. inv H4. 2: { inv H1. }
        destruct_scopes; econstructor; econstructor; auto; econstructor;
        [apply match_pattern_list_tuple_vars|]; simpl; econstructor; auto.
        econstructor.
        constructor; auto;
        rewrite (map_varsFrom _ 1 (a::l)); try slia; simpl; rewrite firstn_all; eauto.
      }
      {
        inv H1. inv H4. 2: { inv H1. }
        destruct_scopes; econstructor; econstructor; auto; econstructor;
        [apply match_pattern_list_tuple_vars|]; simpl; econstructor; auto. 
        econstructor; simpl;
        constructor; auto. simpl. eassumption.
      }
  (* Map *)
  * choose_compat_lemma.
    revert l0 Hcl2 H. induction l; destruct l0; intros.
    - now auto.
    - epose proof (H [FCase1 [([PMap []], ˝ttrue, ˝VNil);([PVar], ˝ttrue , °inf)]] ltac:(scope_solver) _) as H0; repeat deriv.
      + inv H9.
      + cbn in H11. inv H11. inv H4. now apply inf_diverges in H10.
      + now inv H8.
    - epose proof (H [FCase1 [([PMap (repeat (PVar, PVar) (length (a :: l)))], ˝ttrue, ˝VNil);([PVar], ˝ttrue , °inf)]] ltac:(scope_solver) _) as H0; repeat deriv.
      + inv H9.
      + cbn in H11. inv H11. inv H4. now apply inf_diverges in H10.
      + now inv H8.
    - inv IHv.
      assert (REDCLOSED (˝VMap l) /\ REDCLOSED (˝VMap l0)) as [IS1 IS2]. {
        destruct_scopes. split; do 3 constructor; intros;
        try apply (H1 (S i)); try apply (H4 (S i));
        try apply (H7 (S i)); try apply (H8 (S i)); try slia.
      }
      assert (forall F : FrameStack, FSCLOSED F -> | F, ˝ VMap l | ↓ -> | F, ˝ VMap l0 | ↓) as IS3. {
        intros.
        epose proof (H (FCase1 [([PMap (repeat (PVar, PVar) (length (a :: l)))], ˝ttrue, ˝VMap (deflatten_list (varsFrom 2 (length (flatten_list l)))));([PVar], ˝ttrue , °inf)] :: F) _ _) as H4.
        repeat deriv.
        * pose proof (match_pattern_list_map_vars_length (1 + length l) (p::l0) vs') as H1. simpl repeat in H1.
          apply H1 in H14 as H14'. destruct H14' as [Hlen EQ].
          simpl length in *. clear H1. inv EQ.
          simpl in H15. repeat deriv.
          destruct p.
          pose proof (length_flatten_list l) as Hlen1.
          pose proof (length_flatten_list l0) as Hlen2.
          pose proof (map_varsFrom (length (flatten_list l)) 2 (v :: v0 :: flatten_list l0) ltac:(slia)) as H17'.
          replace (map
          (fun '(x, y) =>
           (x.[list_subst (v :: v0 :: flatten_list l0) idsubst]ᵥ,
            y.[list_subst (v :: v0 :: flatten_list l0) idsubst]ᵥ))
          (deflatten_list (varsFrom 2 (Datatypes.length (flatten_list l))))) with
                  (deflatten_list (map (fun x : Val => x.[list_subst (v :: v0 :: flatten_list l0) idsubst]ᵥ)
                  (varsFrom 2 (Datatypes.length (flatten_list l))))) in H10.
          2: {
            replace (length (flatten_list l)) with (length (flatten_list l0)) by lia.
            clear. rewrite deflatten_map. reflexivity.
          }
          simpl in H17', H10.
          rewrite H17' in H10.
          replace (length (flatten_list l)) with (length (flatten_list l0)) in H10 by lia.
          rewrite firstn_all, skipn_O in H10.
          rewrite flatten_deflatten in H10. exists (S k0). econstructor; eauto.
          inv IS2. now inv H9.
        * cbn in H16. inv H16. inv H9. now apply inf_diverges in H15.
        * inv H13.
      }
      specialize (IHl H3 IS1 _ IS2 IS3). destruct a, p.
      constructor; auto. split.
      + apply H2. simpl. apply biforall_length in IHl as Hlen.
        split. 2: split.
        1-2: do 2 constructor; destruct_scopes; try apply (H5 0); try apply (H6 0); slia.
        intros. epose proof (H (FCase1 [([PMap (repeat (PVar, PVar) (length ((v1, v2) :: l)))], ˝ttrue, ˝VVar 0);([PVar], ˝ttrue , °inf)] :: F) ltac:(scope_solver) _) as H4; repeat deriv.
        ** pose proof (match_pattern_list_map_vars ((v1, v2) :: l0)) as H1.
          simpl repeat in H1. rewrite <-Hlen in H1. rewrite H1 in H14.
          inv H14. simpl in H15. repeat deriv.
          exists (S k0). now econstructor.
        ** pose proof (match_pattern_list_map_vars ((v1, v2) :: l0)) as H1.
          simpl repeat in H1. rewrite <-Hlen in H1. rewrite H1 in H14.
          congruence.
        ** inv H13.
    + apply H2. simpl. apply biforall_length in IHl as Hlen.
      split. 2: split.
      1-2: do 2 constructor; destruct_scopes; try apply (H11 0); try apply (H12 0); slia.
      intros. epose proof (H (FCase1 [([PMap (repeat (PVar, PVar) (length ((v1, v2) :: l)))], ˝ttrue, ˝VVar 1);([PVar], ˝ttrue , °inf)] :: F) ltac:(scope_solver) _) as H4; repeat deriv.
      ** pose proof (match_pattern_list_map_vars ((v1, v2) :: l0)) as H1.
        simpl repeat in H1. rewrite <-Hlen in H1. rewrite H1 in H14.
        inv H14. simpl in H15. repeat deriv.
        exists (S k0). now econstructor.
      ** pose proof (match_pattern_list_map_vars ((v1, v2) :: l0)) as H1.
        simpl repeat in H1. rewrite <-Hlen in H1. rewrite H1 in H14.
        congruence.
      ** inv H13.
    Unshelve.
    all: auto.
    3: {
      constructor; auto. do 2 constructor.
      - do 2 constructor. auto.
        apply VMap_scope_Forall. apply deflatten_keeps_prop_match.
        rewrite indexed_to_forall with (def := VNil). intros.
        rewrite length_flatten_list. simpl.
        rewrite scope_repeat_var_prod.
        pose proof (varsFrom_scope (length l * 2) 2 i).
        eapply loosen_scope_val. 2: exact H5.
        rewrite varsFrom_length, length_flatten_list in H4. lia.
      - simpl in *.
        simpl. scope_solver.
    }
    {
      destruct_scopes; econstructor; econstructor; auto; econstructor;
      [reflexivity|]; simpl; econstructor; auto; econstructor;
      constructor; auto;
      constructor; auto.
    }
    {
      destruct_scopes; econstructor; econstructor; auto; econstructor;
      [apply match_pattern_list_map_vars|]; simpl; econstructor; auto.
      econstructor;
      constructor; auto;
      constructor; auto.
    }
    {
      inv H1. inv H4. 2: { inv H1. }
      destruct_scopes; econstructor; econstructor; auto; econstructor;
      [apply match_pattern_list_map_vars|]; simpl; econstructor; auto.
      econstructor; simpl.
      rewrite deflatten_map.
      constructor; auto.
      * rewrite map_varsFrom.
        2: destruct a; slia.
        destruct a. simpl. rewrite firstn_all, skipn_O, flatten_deflatten.
        constructor; intros; try apply H10; try apply H16; assumption.
      * rewrite map_varsFrom.
        2: destruct a; slia.
        destruct a. simpl. rewrite firstn_all, skipn_O, flatten_deflatten. eassumption.
    }
    {
      inv H1. inv H4. 2: { inv H1. }
      destruct_scopes; econstructor; econstructor; auto. econstructor;      
      [apply (match_pattern_list_map_vars ((v, v0)::l))|]; simpl; econstructor; auto. simpl. econstructor;
      constructor; auto. simpl. eassumption.
    }
    {
      inv H1. inv H4. 2: { inv H1. }
      destruct_scopes; econstructor; econstructor; auto. econstructor;      
      [apply (match_pattern_list_map_vars ((v, v0)::l))|]; simpl; econstructor; auto. simpl. econstructor;
      constructor; auto. simpl. eassumption.
    }
  (* closures - anything : create different exceptions in a try expr.
     e.g., apply the closure with a non-matching argument number, 
     then match on the exception:
      - if it's badarity -> result is VNil
      - if it's badfun -> result is divergence
    TODO (boilerplate): The following proof is identical for the next 7 cases
  *)
  * destruct params.
    (* we have to make sure, that the number of parameters differ *)
    - epose proof (H [FApp1 [˝VNil];FTry 1 (˝VNil) 3 (ECase (˝VVar 1) [
        ([PLit "badarity"%string], ˝ttrue, ˝VNil);
        ([PVar], ˝ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H10. repeat deriv. inv H9.
      cbn in H10. repeat deriv. cbn in H12.
      2: { inv H5. }
      repeat deriv. inv H12. 2: inv H11. inv H11. cbn in H14.
      inv H14. inv H6. now apply inf_diverges in H11.
    - epose proof (H [FApp1 [];FTry 1 (˝VNil) 3 (ECase (˝VVar 1) [
        ([PLit "badarity"%string], ˝ttrue, ˝VNil);
        ([PVar], ˝ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H8. repeat deriv.
      cbn in H5. inv H5.
      repeat deriv. cbn in H11.
      2: { inv H5. }
      repeat deriv. inv H11. 2: inv H10. inv H10. cbn in H13.
      inv H13. inv H6. now apply inf_diverges in H10.
    Unshelve.
    {
      eexists. destruct_scopes. repeat econstructor; eauto.
    }
    {
      eexists. destruct_scopes. repeat econstructor; eauto.
    }
  * destruct params.
  (* we have to make sure, that the number of parameters differ *)
    - epose proof (H [FApp1 [˝VNil];FTry 1 (˝VNil) 3 (ECase (˝VVar 1) [
        ([PLit "badarity"%string], ˝ttrue, ˝VNil);
        ([PVar], ˝ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H10. repeat deriv.
      cbn in H9. inv H9.
      repeat deriv. cbn in H12.
      2: { inv H5. }
      repeat deriv. inv H12. 2: inv H11. inv H11. cbn in H14.
      inv H14. inv H6. now apply inf_diverges in H11.
    - epose proof (H [FApp1 [];FTry 1 (˝VNil) 3 (ECase (˝VVar 1) [
        ([PLit "badarity"%string], ˝ttrue, ˝VNil);
        ([PVar], ˝ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H8. repeat deriv.
      inv H5. repeat deriv.
      cbn in H11.
      2: { inv H5. }
      repeat deriv. inv H11. 2: inv H10. inv H10. cbn in H13.
      inv H13. inv H6. now apply inf_diverges in H10.
    Unshelve.
    {
      eexists. destruct_scopes. repeat econstructor; eauto.
    }
    {
      eexists. destruct_scopes. repeat econstructor; eauto.
    }
  * destruct params.
  (* we have to make sure, that the number of parameters differ *)
    - epose proof (H [FApp1 [˝VNil];FTry 1 (˝VNil) 3 (ECase (˝VVar 1) [
        ([PLit "badarity"%string], ˝ttrue, ˝VNil);
        ([PVar], ˝ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H10. repeat deriv.
      inv H9. repeat deriv.
      cbn in H12.
      2: { inv H5. }
      repeat deriv. inv H12. 2: inv H11. inv H11. cbn in H14.
      inv H14. inv H6. now apply inf_diverges in H11.
    - epose proof (H [FApp1 [];FTry 1 (˝VNil) 3 (ECase (˝VVar 1) [
        ([PLit "badarity"%string], ˝ttrue, ˝VNil);
        ([PVar], ˝ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H8. repeat deriv.
      inv H5. repeat deriv.
      cbn in H11.
      2: { inv H5. }
      repeat deriv. inv H11. 2: inv H10. inv H10. cbn in H13.
      inv H13. inv H6. now apply inf_diverges in H10.
    Unshelve.
    {
      eexists. destruct_scopes. repeat econstructor; eauto.
    }
    {
      eexists. destruct_scopes. repeat econstructor; eauto.
    }
  * destruct params.
  (* we have to make sure, that the number of parameters differ *)
    - epose proof (H [FApp1 [˝VNil];FTry 1 (˝VNil) 3 (ECase (˝VVar 1) [
        ([PLit "badarity"%string], ˝ttrue, ˝VNil);
        ([PVar], ˝ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H10. repeat deriv.
      inv H9. repeat deriv.
      cbn in H12.
      2: { inv H5. }
      repeat deriv. inv H12. 2: inv H11. inv H11. cbn in H14.
      inv H14. inv H6. now apply inf_diverges in H11.
    - epose proof (H [FApp1 [];FTry 1 (˝VNil) 3 (ECase (˝VVar 1) [
        ([PLit "badarity"%string], ˝ttrue, ˝VNil);
        ([PVar], ˝ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H8. repeat deriv.
      inv H5. repeat deriv.
      cbn in H11.
      2: { inv H5. }
      repeat deriv. inv H11. 2: inv H10. inv H10. cbn in H13.
      inv H13. inv H6. now apply inf_diverges in H10.
    Unshelve.
    {
      eexists. destruct_scopes. repeat econstructor; eauto.
    }
    {
      eexists. destruct_scopes. repeat econstructor; eauto.
    }
  * destruct params.
  (* we have to make sure, that the number of parameters differ *)
    - epose proof (H [FApp1 [˝VNil];FTry 1 (˝VNil) 3 (ECase (˝VVar 1) [
        ([PLit "badarity"%string], ˝ttrue, ˝VNil);
        ([PVar], ˝ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H10. repeat deriv.
      inv H9. repeat deriv.
      cbn in H12.
      2: { inv H5. }
      repeat deriv. inv H12. 2: inv H11. inv H11. cbn in H14.
      inv H14. inv H6. now apply inf_diverges in H11.
    - epose proof (H [FApp1 [];FTry 1 (˝VNil) 3 (ECase (˝VVar 1) [
        ([PLit "badarity"%string], ˝ttrue, ˝VNil);
        ([PVar], ˝ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H8. repeat deriv.
      inv H5. repeat deriv.
      cbn in H11.
      2: { inv H5. }
      repeat deriv. inv H11. 2: inv H10. inv H10. cbn in H13.
      inv H13. inv H6. now apply inf_diverges in H10.
    Unshelve.
    {
      eexists. destruct_scopes. repeat econstructor; eauto.
    }
    {
      eexists. destruct_scopes. repeat econstructor; eauto.
    }
  * destruct params.
  (* we have to make sure, that the number of parameters differ *)
    - epose proof (H [FApp1 [˝VNil];FTry 1 (˝VNil) 3 (ECase (˝VVar 1) [
        ([PLit "badarity"%string], ˝ttrue, ˝VNil);
        ([PVar], ˝ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H10. repeat deriv.
      inv H9. repeat deriv.
      cbn in H12.
      2: { inv H5. }
      repeat deriv. inv H12. 2: inv H11. inv H11. cbn in H14.
      inv H14. inv H6. now apply inf_diverges in H11.
    - epose proof (H [FApp1 [];FTry 1 (˝VNil) 3 (ECase (˝VVar 1) [
        ([PLit "badarity"%string], ˝ttrue, ˝VNil);
        ([PVar], ˝ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H8. repeat deriv.
      inv H5. repeat deriv.
      cbn in H11.
      2: { inv H5. }
      repeat deriv. inv H11. 2: inv H10. inv H10. cbn in H13.
      inv H13. inv H6. now apply inf_diverges in H10.
    Unshelve.
    {
      eexists. destruct_scopes. repeat econstructor; eauto.
    }
    {
      eexists. destruct_scopes. repeat econstructor; eauto.
    }
  * destruct params.
  (* we have to make sure, that the number of parameters differ *)
    - epose proof (H [FApp1 [˝VNil];FTry 1 (˝VNil) 3 (ECase (˝VVar 1) [
        ([PLit "badarity"%string], ˝ttrue, ˝VNil);
        ([PVar], ˝ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H10. repeat deriv.
      inv H9. repeat deriv.
      cbn in H12.
      2: { inv H5. }
      repeat deriv. inv H12. 2: inv H11. inv H11. cbn in H14.
      inv H14. inv H6. now apply inf_diverges in H11.
    - epose proof (H [FApp1 [];FTry 1 (˝VNil) 3 (ECase (˝VVar 1) [
        ([PLit "badarity"%string], ˝ttrue, ˝VNil);
        ([PVar], ˝ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H8. repeat deriv.
      inv H5. repeat deriv.
      cbn in H11.
      2: { inv H5. }
      repeat deriv. inv H11. 2: inv H10. inv H10. cbn in H13.
      inv H13. inv H6. now apply inf_diverges in H10.
    Unshelve.
    {
      eexists. destruct_scopes. repeat econstructor; eauto.
    }
    {
      eexists. destruct_scopes. repeat econstructor; eauto.
    }
    (* closure - closure -> induction on m *)
  *  destruct params.
  (* we have to make sure, that the number of parameters differ *)
    - epose proof (H [FApp1 [˝VNil];FTry 1 (˝VNil) 3 (ECase (˝VVar 1) [
        ([PLit "badarity"%string], ˝ttrue, ˝VNil);
        ([PVar], ˝ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H10. repeat deriv.
      inv H9. repeat deriv.
      cbn in H12.
      2: { inv H5. }
      repeat deriv. inv H12. 2: inv H11. inv H11. cbn in H14.
      inv H14. inv H6. now apply inf_diverges in H11.
    - epose proof (H [FApp1 [];FTry 1 (˝VNil) 3 (ECase (˝VVar 1) [
        ([PLit "badarity"%string], ˝ttrue, ˝VNil);
        ([PVar], ˝ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H8. repeat deriv.
      inv H5. repeat deriv.
      cbn in H11.
      2: { inv H5. }
      repeat deriv. inv H11. 2: inv H10. inv H10. cbn in H13.
      inv H13. inv H6. now apply inf_diverges in H10.
    Unshelve.
    {
      eexists. destruct_scopes. repeat econstructor; eauto.
    }
    {
      eexists. destruct_scopes. repeat econstructor; eauto.
    }
  * inv Hcl1. inv Hcl2.

    (* First, we show that the closures have the same arity with erlang:fun_info *)
    assert (params = params0). {
      epose proof (H [FParams (ICall (VLit "erlang"%string) (VLit "fun_info"%string)) [] [˝VLit "arity"%string];FCase1 [([PLit (Z.of_nat params)], ˝ttrue, ˝VNil);([PVar], ˝ttrue, °inf)]] ltac:(scope_solver) _) as H0; repeat deriv.
      simpl in H11. repeat deriv. cbn in H10. invSome. repeat deriv.
      2-3: inv H11.
      2: { simpl in H14. inv H14. inv H7. now apply inf_diverges in H11. }
      inv H12. destruct (Z.of_nat params0 =? Z.of_nat params)%Z eqn:P; inv H5.
      - apply Z.eqb_eq in P. now apply Znat.Nat2Z.inj in P.
      Unshelve.
        congruence.
        auto.
        destruct_scopes. repeat econstructor; auto.
        simpl. rewrite Z.eqb_refl. reflexivity.
    }

    (* Next we show that the identifiers are also equal using erlang:== *)
    assert (id = id0). {
      inv H1. inv H2.
      epose proof (H [FParams (ICall (VLit "erlang"%string) (VLit "=="%string)) [] [˝ VClos ext id params0 e];FCase1 [([PLit "true"%string], ˝ttrue, ˝VNil);([PVar], ˝ttrue, °inf)]] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H10.
      break_match_hyp. now apply Nat.eqb_eq in Heqb.
      invSome.
      repeat deriv; inv H12; inv H11. simpl in *.
      inv H14. inv H7. now apply inf_diverges in H11.
    Unshelve.
      congruence.
      auto.
      destruct_scopes.
      repeat econstructor; auto. cbn.
      rewrite Nat.eqb_refl. repeat econstructor.
    }

      (* Starting the proof of Vrel clos1 clos2: *)
      subst. inv H1. inv H2.

      rewrite Vrel_Fix_eq. simpl. intuition; auto.
      (* scopes *)
      split. 2: split.
      1-2: destruct_scopes; apply -> subst_preserves_scope_exp; eauto.
      1-2: apply scoped_list_subscoped_eq; try simpl_convert_length; auto.
      2: apply biforall_length in H1; auto.
      1-2: apply Forall_app; split.
      1,3: apply closlist_scope; auto.
      1-2: now apply biforall_vrel_closed in H1.

      (* We fold back the CIU equivalence, with value lists: *)
      assert (H2 : CIU (RValSeq [VClos ext id0 params0 e]) (RValSeq [VClos ext0 id0 params0 e0])). {
        split. 2: split. all: auto.
        intros.
        assert (| F, ˝ VClos ext id0 params0 e | ↓). {
          inv H5. eexists. econstructor. auto. eassumption.
        }
        eapply H in H2; auto. inv H2. inv H7. eexists. eassumption.
        inv H0.
      }
      intros.

      (* We turn CIU into Rrel so that we can use equivalent frame stacks
         instead of equal ones. *)
      eapply CIU_iff_Rrel_closed in H2 as [_ [_ H2]].
      Unshelve. 2: exact (5 + 2 * Datatypes.length vl1 + 1 + m).
      (* IDEA: we use ˝try˝ to even out the evaluation counter for exceptions
          and correct application *)
      assert (Heval_e : | FTry 1 (° EApp (˝ VVar 0) (map VVal vl1)) 0 (° ETuple (map VVal vl1)) :: F1,
     ˝ VClos ext id0 params0 e | 5 + 2 * length vl1 + 1 + m1 ↓). {
        simpl. econstructor; auto. constructor; auto. simpl.
        replace (map (fun x : Exp => x.[VClos ext id0 params0 e/]) (map VVal vl1))
           with (map VVal vl1).
        2: {
          clear -H1. rewrite map_map. simpl.
          apply biforall_vrel_closed in H1 as [H1 _].
          apply map_ext_Forall. induction vl1; inv H1; constructor; auto.
          now rewrite vclosed_ignores_sub.
        }
        do 2 constructor. auto.
        constructor. destruct vl1.
        * simpl. econstructor. congruence. cbn. rewrite <- H0. reflexivity. simpl.
          assumption.
        * simpl. constructor. congruence.
          simpl. change clock to (S (1 + 2 * length vl1) + m1).
          inv H1. constructor. now apply Vrel_closed_l in H9.
          eapply step_term_term_plus. eapply params_eval_create.
          now apply biforall_vrel_closed in H11.
          simpl. rewrite Nat.eqb_refl. reflexivity.
          assumption.
      }

      (* We assert that the frame stack with the ˝try˝ expressions are equivalent
        in as many steps that are needed to evaluate the closures. *)
      assert (Hrel : Frel (4 + 2 * length vl1 + 1 + m1) (* dirty trick here with 0 *)
          (FTry 1 (EApp (˝VVar 0) (map VVal vl1)) 0 (ETuple (map VVal vl1))::F1)
          (FTry 1 (EApp (˝VVar 0) (map VVal vl2)) 0 (ETuple (map VVal vl2))::F2)
            ). {
        clear Heval_e.
        split. 2: split. 1-2: constructor; [constructor|apply H5].
        1-4: do 2 constructor; auto; apply indexed_to_forall; apply biforall_vrel_closed in H1; clear -H1.

        (* boiler plate codes: *)
        1-2: destruct H1 as [H1 _]; induction vl1; simpl; auto; inv H1; constructor;
             [ constructor; eapply loosen_scope_val; [|eassumption]; lia | auto].
        1-2: destruct H1 as [_ H1]; induction vl2; simpl; auto; inv H1; constructor;
             [ constructor; eapply loosen_scope_val; [|eassumption]; lia | auto].
        (****)

        split. 2: split.
        all: intros.
        * deriv. inv H7. inv H16. inv H8.
          simpl in H17.
          deriv. deriv. deriv. inv H1.
          - deriv.
            simpl in Hmn1.
            pose proof (Rel_create_result _ [] [] (IApp hd) (IApp hd') ltac:(auto) ltac:(constructor; eauto)).
            intuition. destruct H7 as [eff0 [eff0' H7]].
            intuition.
            + destruct_hyps.
              specialize (H1 k ltac:(lia)) as [Hrel [Eq1 Eq2]].
              rewrite Eq1 in H12. invSome.
              eapply Hrel in H15 as [kk D]. 2: reflexivity.
              2: eapply Frel_downclosed in H5; eassumption.
              eexists. constructor; auto. simpl.
              constructor; auto. constructor; auto. now apply Vrel_closed_r in H0.
              constructor. econstructor. congruence. eauto.
              exact D.
              Unshelve. lia.
            + destruct_hyps. rewrite H7 in H12. invSome.
              eapply H5 in H15 as [kk D]. 2: lia. 2: eapply biforall_impl;[|eassumption]; intros; downclose_Vrel.
              eexists. constructor; auto. simpl.
              constructor; auto. constructor; auto. now apply Vrel_closed_r in H0.
              constructor. econstructor. congruence. eauto.
              exact D.
              Unshelve. lia.
            + destruct_hyps. rewrite H7 in H12. invSome.
              eapply H5 in H15 as [kk D]. 2: lia. 2: eapply Excrel_downclosed; eassumption.
              eexists. constructor; auto. simpl.
              constructor; auto. constructor; auto. now apply Vrel_closed_r in H0.
              constructor. econstructor. congruence. eauto.
              exact D.
              Unshelve. lia.
            + congruence.
          - inv H14. inv H18.
            rewrite map_map in H13.
            rewrite vclosed_ignores_sub in H11. 2: now apply Vrel_closed_l in H7.
            replace (map (fun x : Val => (˝ x).[hd/]) tl) with
                    (map VVal tl) in H13.
            2: {
              clear -H10. simpl.
              apply biforall_vrel_closed in H10 as [H1 _].
              apply map_ext_Forall. induction tl; inv H1; constructor; auto.
              now rewrite vclosed_ignores_sub.
            }
            rewrite vclosed_ignores_sub in H13. 2: now apply Vrel_closed_l in H0.
            assert (exists r eff, Some (r, eff) =
                    create_result (IApp hd) (hd0 :: tl)) as [result [eff1 EQ]]. {
              simpl. repeat break_match_goal; do 2 eexists; reflexivity.
            }
            eapply term_step_term in H13.
            2: eapply params_eval_create.
            2: now apply biforall_vrel_closed in H10.
            2: exact EQ.
            simpl app in H13.
            simpl in Hmn1.
            assert (list_biforall (Vrel (k0 - (1 + 2 * Datatypes.length tl)))
                                  (hd0 :: tl) (hd'0 :: tl') ) as Hfinally.
            {
              constructor. downclose_Vrel.
              eapply biforall_impl. 2: eassumption. intros. downclose_Vrel.
            }
            epose proof (Rel_create_result_relaxed _ (hd0 :: tl) (hd'0 :: tl') (IApp hd) (IApp hd') Hfinally _). Unshelve.
            4: {
              split. 2: split.
              1-2: constructor; now apply Vrel_closed in H0.
              downclose_Vrel.
            }
            intuition. destruct H12 as [eff0 [eff0' H12]].
            intuition.
            + destruct_hyps. simpl in Hmn1.
              specialize (H1 (k0 - (1 + 2 * Datatypes.length tl)) ltac:(lia)).
              destruct H1 as [Hrel [H1_1 H1_2]].
              rewrite H1_1 in EQ. invSome. eapply Hrel in H13 as [k D].
              eexists. constructor. reflexivity. simpl.
              do 2 constructor. now apply Vrel_closed_r in H0.
              do 2 constructor. congruence. rewrite vclosed_ignores_sub.
              2: now apply Vrel_closed_r in H7.
              rewrite map_map.
              replace (map (fun x : Val => (˝ x).[hd'/]) tl') with
                      (map VVal tl').
              2: {
                clear -H10. simpl.
                apply biforall_vrel_closed in H10 as [_ H1].
                apply map_ext_Forall. induction tl'; inv H1; constructor; auto.
                now rewrite vclosed_ignores_sub.
              }
              constructor. now apply Vrel_closed_r in H7.
              eapply step_term_term_plus. eapply params_eval_create.
              now apply biforall_vrel_closed in H10. simpl app. setoid_rewrite H1_2. reflexivity.
              exact D.
              lia.
              eapply Frel_downclosed. eassumption.
              Unshelve. lia. lia.
            + destruct_hyps.
              rewrite H12 in EQ. invSome.
              eapply H5 in H13 as [k D].
              eexists. constructor. reflexivity. simpl.
              do 2 constructor. now apply Vrel_closed_r in H0.
              do 2 constructor. congruence. rewrite vclosed_ignores_sub.
              2: now apply Vrel_closed_r in H7.
              rewrite map_map.
              replace (map (fun x : Val => (˝ x).[hd'/]) tl') with
                      (map VVal tl').
              2: {
                clear -H10. simpl.
                apply biforall_vrel_closed in H10 as [_ H1].
                apply map_ext_Forall. induction tl'; inv H1; constructor; auto.
                now rewrite vclosed_ignores_sub.
              }
              constructor. now apply Vrel_closed_r in H7.
              eapply step_term_term_plus. eapply params_eval_create.
              now apply biforall_vrel_closed in H10. simpl app. setoid_rewrite H14.
              reflexivity.
              exact D. simpl in Hmn1. lia.
              eapply biforall_impl. 2: eassumption.
              intros. downclose_Vrel.
              Unshelve. lia.
            + destruct_hyps.
              rewrite H12 in EQ. invSome.
              eapply H5 in H13 as [k D].
              eexists. constructor. reflexivity. simpl.
              do 2 constructor. now apply Vrel_closed_r in H0.
              do 2 constructor. congruence. rewrite vclosed_ignores_sub.
              2: now apply Vrel_closed_r in H7.
              rewrite map_map.
              replace (map (fun x : Val => (˝ x).[hd'/]) tl') with
                      (map VVal tl').
              2: {
                clear -H10. simpl.
                apply biforall_vrel_closed in H10 as [_ H1].
                apply map_ext_Forall. induction tl'; inv H1; constructor; auto.
                now rewrite vclosed_ignores_sub.
              }
              constructor. now apply Vrel_closed_r in H7.
              eapply step_term_term_plus. eapply params_eval_create.
              now apply biforall_vrel_closed in H10. simpl app. setoid_rewrite H14.
              reflexivity.
              exact D. simpl in Hmn1. lia.
              eapply Excrel_downclosed. eassumption.
              Unshelve. simpl in Hmn1. lia.
            + congruence.
            + lia.
            + lia.
        * inv H8. (* Having 0 params in ˝catch˝ is exploited here,
                     because we only want to evaluate the ˝of˝ subexpression
                     in this ˝try˝ expression.
                   *)
        * inv H7.
      }

      (* Finally, we combine the previous assertions with the closures
         being in Rrel (H2). *)
      inv Heval_e.
      epose proof (H2 := H2 _ _ _ _ Hrel H11).
      Unshelve. 2: lia.
      clear -H2 H1. (* DANGER, nothing else is needed for now, however this
                               is fragile if refactoring is needed *)
      (* We deconstruct the evaluation in the premise: *)
      inv H2. deriv. simpl in H9. deriv. deriv. simpl in H3.
      deriv.
      rewrite map_map in H6.
      replace (map (fun x : Val => (˝ x).[VClos ext0 id0 (Datatypes.length vl1) e0/]) vl2) with
                      (map VVal vl2) in H6.
      2: {
        clear -H1. simpl.
        apply biforall_vrel_closed in H1 as [_ H1].
        apply map_ext_Forall. induction vl2; inv H1; constructor; auto.
        now rewrite vclosed_ignores_sub.
      }
      destruct vl2.
      - deriv. simpl in H5. apply biforall_length in H1. rewrite H1 in H5.
        simpl in H5. invSome. eexists. eassumption.
      - deriv. deriv.
        eapply term_step_term in H4. 2: eapply params_eval_create.
        2: {
          apply biforall_vrel_closed in H1 as [_ H1]. now inv H1.
        }
        eexists. eassumption.
        simpl. apply biforall_length in H1. rewrite H1, Nat.eqb_refl. reflexivity.
Qed.

Ltac inf_congr :=
  match goal with
  | [H :  | _ , RExp (EExp inf) | _ ↓ |- _ ] => apply inf_diverges in H; contradiction
  | [H :  | _ , RExp (EExp inf.[_]ₑ) | _ ↓ |- _ ] => apply inf_diverges in H; contradiction
  end.

Lemma Erel_Tuple_compat_reverse :
  forall Γ l l', Erel_open Γ (˝VTuple l) (˝VTuple l') ->
    list_biforall (Erel_open Γ) (map VVal l) (map VVal l').
Proof.
  induction l; destruct l'; intros; auto.
  * exfalso. apply Rrel_exp_compat in H. apply CIU_iff_Rrel in H.
      assert (| [FCase1 [([PTuple []], ˝ttrue, ˝VNil);([PVar], ˝ttrue, °inf)]], ˝VTuple [] |↓). {
        eexists. econstructor. scope_solver.
        econstructor. reflexivity. simpl.
        constructor. auto.
        econstructor.
        do 2 constructor. auto.
      }
      specialize (H (default_subst VNil) ltac:(auto)). simpl in H.
      apply H in H0. 2: scope_solver.
      inv H0. repeat deriv. inv H9. 2: inv H8. simpl in H11. inv H11.
      inv H4. now apply inf_diverges in H10.
  * exfalso. apply Rrel_exp_compat in H. apply CIU_iff_Rrel in H.
      assert (| [FCase1 [([PTuple (repeat PVar (length (a :: l)))], ˝ttrue, ˝VNil);([PVar], ˝ttrue, °inf)]], (˝VTuple (a :: l)).[default_subst VNil]ᵣ |↓). {
        assert (VALCLOSED (VTuple (a :: l)).[default_subst VNil]ᵥ). {
          apply CIU_open_scope_l in H. inv H. inv H1.
          apply -> subst_preserves_scope_val; eauto.
        }
        eexists. simpl. econstructor. exact H0.
        econstructor. apply (match_pattern_list_tuple_vars_map (a :: l)). simpl.
        constructor. auto.
        econstructor. simpl.
        do 2 constructor. auto.
      }
      specialize (H (default_subst VNil) ltac:(auto)). simpl in H.
      apply H in H0. 2: scope_solver.
      inv H0. repeat deriv. inv H9. 2: inv H8. simpl in H11. inv H11.
      inv H4. now apply inf_diverges in H10.
  * simpl.
    assert (Erel_open Γ (˝VTuple l) (˝VTuple l')). {
      apply Rrel_exp_compat, CIU_iff_Rrel in H.
      apply Rrel_exp_compat_reverse, CIU_iff_Rrel.
      intros ??. apply H in H0. clear H. simpl in *.
      destruct H0 as [Hsc1 [Hsc2 Hrel]].
      assert (VALCLOSED (VTuple l).[ξ]ᵥ /\ VALCLOSED (VTuple l').[ξ]ᵥ) as [Hsc3 Hsc4]. {
        simpl in *.
        destruct_scopes. simpl. split; constructor; intros;
          try apply (H1 (S i)); try apply (H2 (S i)); slia.
      }
      split. 2: split.
      1-2: do 2 constructor; auto.
      intros.
      epose proof (Hrel (FCase1 [([PTuple (repeat PVar (length (a :: l)))], ˝ttrue, ˝VTuple (varsFrom 1 (length l)));([PVar], ˝ttrue , °inf)] :: F) _ _) as Hrel.
      repeat deriv.
      * pose proof (match_pattern_list_tuple_vars_length (1 + length l) (map (fun x => x.[ξ]ᵥ) (v::l')) vs') as H1. simpl repeat in H1.
        apply H1 in H10 as H10'. destruct H10' as [Hlen EQ].
        simpl length in *. rewrite length_map in Hlen. clear H1. destruct vs'; inv EQ.
        simpl in H11. repeat deriv.
        pose proof (map_varsFrom (length l) 1 (map (fun x => x.[ξ]ᵥ) (v :: l')) ltac:(rewrite length_map;slia)) as H17'.
        simpl in H17'. rewrite H17' in H7.
        replace (length l) with (length l') in H7 by lia.
        rewrite <- (length_map (fun x => x.[ξ]ᵥ) l') in H7.
        rewrite firstn_all in H7. exists (S k1). econstructor; auto.
      * cbn in H12. do 2 deriv. now apply inf_diverges in H12.
      * inv H9.
      Unshelve.
        - constructor; auto. do 5 scope_solver_step.
          intros. rewrite scope_repeat_var.
          pose proof (varsFrom_scope (length l) 1 i).
          eapply loosen_scope_val. 2: eassumption.
          rewrite varsFrom_length in H1. lia.
        - inv H0. inv H1. 2: { inv H0. }
          pose proof (match_pattern_list_tuple_vars (map (fun x : Val => x.[ξ]ᵥ) (a :: l))). rewrite length_map in H0.
          destruct_scopes; econstructor; econstructor; auto; econstructor.
          apply H0.
          simpl; econstructor. auto. econstructor; simpl;
          constructor;
          rewrite (map_varsFrom _ 1 (a.[ξ]ᵥ::map (substVal ξ) l)); try (rewrite length_map; slia).
          1, 3: simpl; rewrite <- (length_map (fun x : Val => x.[ξ]ᵥ) l); rewrite firstn_all; eauto;
          simpl; rewrite length_map; slia.
          all: simpl; rewrite <- (length_map (fun x : Val => x.[ξ]ᵥ) l);
          do 2 rewrite length_map; lia.
    }
    apply IHl in H0. constructor; auto.
    apply biforall_length in H0. do 2 rewrite length_map in H0.
    apply Rrel_exp_compat, CIU_iff_Rrel in H.
    apply Rrel_exp_compat_reverse, CIU_iff_Rrel.
    intros ??. apply H in H1. clear H. simpl in *.
    destruct H1 as [Hsc1 [Hsc2 Hrel]].
    assert (VALCLOSED a.[ξ]ᵥ /\ VALCLOSED v.[ξ]ᵥ) as [Hsc3 Hsc4]. {
      simpl in *.
      destruct_scopes. simpl. split; try apply (H3 0); try apply (H2 0); slia.
    }
    split. 2: split.
    1-2: do 2 constructor; auto.
    intros.
    epose proof (Hrel (FCase1 [([PTuple (repeat PVar (length (a :: l)))], ˝ttrue, ˝VVar 0);([PVar], ˝ttrue , °inf)] :: F) _ _) as Hrel.
    repeat deriv.
    - pose proof (match_pattern_list_tuple_vars_length (1 + length l) (map (fun x => x.[ξ]ᵥ) (v::l')) vs') as H1. simpl repeat in H1.
      apply H1 in H11 as H11'. destruct H11' as [Hlen EQ].
      simpl length in *. rewrite length_map in Hlen. clear H1. destruct vs'; inv EQ.
      simpl in H12. repeat deriv.
      eexists. econstructor; eassumption.
    - cbn in H13. do 2 deriv. now apply inf_diverges in H13.
    - inv H10.
  Unshelve.
    + constructor; auto. do 5 scope_solver_step. lia.
    + inv H1. inv H2. 2: { inv H1. }
      pose proof (match_pattern_list_tuple_vars (map (fun x : Val => x.[ξ]ᵥ) (a :: l))).
      rewrite length_map in H1.
      destruct_scopes; econstructor; econstructor; auto; econstructor.
      apply H1.
      simpl; econstructor. auto. econstructor; simpl;
      constructor.
      cbn. auto.
      simpl. eassumption.
Qed.

Lemma Erel_Map_compat_reverse :
  forall Γ l l', Erel_open Γ (˝VMap l) (˝VMap l') ->
    list_biforall (fun '(e1, e2) '(e1', e2') => Erel_open Γ e1 e1' /\ Erel_open Γ e2 e2') (map (fun '(e1, e2) => (˝e1, ˝e2)) l) (map (fun '(e1, e2) => (˝e1, ˝e2)) l').
Proof.
  induction l; destruct l'; intros; auto.
  * exfalso. apply Rrel_exp_compat in H. apply CIU_iff_Rrel in H.
      assert (| [FCase1 [([PMap []], ˝ttrue, ˝VNil);([PVar], ˝ttrue, °inf)]], ˝VMap [] |↓). {
        eexists. econstructor. scope_solver.
        econstructor. reflexivity. simpl.
        constructor. auto.
        econstructor. simpl.
        do 2 constructor. auto.
      }
      specialize (H (default_subst VNil) ltac:(auto)). simpl in H.
      apply H in H0. 2: scope_solver.
      inv H0. repeat deriv. inv H9. 2: inv H8. simpl in H11. inv H11.
      inv H4. now apply inf_diverges in H10.
  * exfalso. apply Rrel_exp_compat in H. apply CIU_iff_Rrel in H.
      assert (| [FCase1 [([PMap (repeat (PVar, PVar) (length (a :: l)))], ˝ttrue, ˝VNil);([PVar], ˝ttrue, °inf)]], (˝VMap (a :: l)).[default_subst VNil]ᵣ |↓). {
        assert (VALCLOSED (VMap (a :: l)).[default_subst VNil]ᵥ). {
          apply CIU_open_scope_l in H. inv H. inv H1.
          apply -> subst_preserves_scope_val; eauto.
        }
        eexists. simpl. econstructor. exact H0. destruct a.
        pose proof (HM := match_pattern_list_map_vars_map ((v, v0) :: l) (fun '(x, y) => (x.[default_subst VNil]ᵥ, y.[default_subst VNil]ᵥ))). (* Coq cannot infer f correctly somewhy *)
        simpl repeat in HM. simpl map in HM.
        econstructor. apply HM.
        simpl.
        constructor. auto.
        econstructor. simpl.
        do 2 constructor. auto.
      }
      specialize (H (default_subst VNil) ltac:(auto)). simpl in H.
      apply H in H0. 2: scope_solver.
      inv H0. repeat deriv. inv H9. 2: inv H8. simpl in H11. inv H11.
      inv H4. now apply inf_diverges in H10.
  * simpl.
    assert (Erel_open Γ (˝VMap l) (˝VMap l')). {
      apply Rrel_exp_compat, CIU_iff_Rrel in H.
      apply Rrel_exp_compat_reverse, CIU_iff_Rrel.
      intros ??. apply H in H0. clear H. simpl in *.
      destruct H0 as [Hsc1 [Hsc2 Hrel]].
      assert (VALCLOSED (VMap l).[ξ]ᵥ /\ VALCLOSED (VMap l').[ξ]ᵥ) as [Hsc3 Hsc4]. {
        simpl in *.
        destruct_scopes. simpl. split; constructor; intros;
          try apply (H1 (S i)); try apply (H5 (S i));
          try apply (H0 (S i)); try apply (H4 (S i)); slia.
      }
      split. 2: split.
      1-2: do 2 constructor; auto.
      intros.
      epose proof (Hrel (FCase1 [([PMap (repeat (PVar, PVar) (length (a :: l)))], ˝ttrue, ˝VMap (deflatten_list (varsFrom 2 (length (flatten_list l)))));([PVar], ˝ttrue , °inf)] :: F) _ _) as H4.
        repeat deriv.
        * pose proof (match_pattern_list_map_vars_length (1 + length l) (map (fun '(x, y) => (x.[ξ]ᵥ, y.[ξ]ᵥ)) (p::l')) vs') as H1. simpl repeat in H1. destruct p.
          apply H1 in H11 as H11'. destruct H11' as [Hlen EQ].
          simpl length in *. clear H1. destruct vs'; inv EQ.
          simpl in H12. repeat deriv.
          pose proof (length_flatten_list (map (fun '(x0, y0) => (x0.[ξ]ᵥ, y0.[ξ]ᵥ)) l)) as Hlen1.
          pose proof (length_flatten_list (map (fun '(x0, y0) => (x0.[ξ]ᵥ, y0.[ξ]ᵥ)) l')) as Hlen2.
          epose proof (map_varsFrom (length (flatten_list (map (fun '(x0, y0) => (x0.[ξ]ᵥ, y0.[ξ]ᵥ)) l))) 2 (v.[ξ]ᵥ :: v0.[ξ]ᵥ :: flatten_list (map (fun '(x0, y0) => (x0.[ξ]ᵥ, y0.[ξ]ᵥ)) l')) ltac:(rewrite length_map in *; slia)) as H13'.
          replace (map
             (fun '(x, y) =>
              (x.[v.[ξ]ᵥ
                  .: v0.[ξ]ᵥ
                     .: list_subst
                          (flatten_list (map (fun '(x0, y0) => (x0.[ξ]ᵥ, y0.[ξ]ᵥ)) l'))
                          idsubst]ᵥ,
               y.[v.[ξ]ᵥ
                  .: v0.[ξ]ᵥ
                     .: list_subst
                          (flatten_list (map (fun '(x0, y0) => (x0.[ξ]ᵥ, y0.[ξ]ᵥ)) l'))
                          idsubst]ᵥ))
             (deflatten_list (varsFrom 2 (Datatypes.length (flatten_list l))))) with
                  (deflatten_list (map (fun x : Val => x.[list_subst (v.[ξ]ᵥ :: v0.[ξ]ᵥ :: flatten_list (map (fun '(x0, y0) => (x0.[ξ]ᵥ, y0.[ξ]ᵥ)) l')) idsubst]ᵥ)
                  (varsFrom 2 (Datatypes.length (flatten_list l))))) in H7.
          2: {
            rewrite length_map in *.
            replace (length (flatten_list l)) with (length (flatten_list l')).
            clear. rewrite deflatten_map. reflexivity.
            do 2 rewrite length_flatten_list. lia.
          }
          simpl in H13', H7. rewrite length_flatten_list in H13', H7.
          rewrite length_map in H13'.
          rewrite H13' in H7.
          replace (Datatypes.length l * 2) with
                  (length (flatten_list (map (fun '(x0, y0) => (x0.[ξ]ᵥ, y0.[ξ]ᵥ)) l')))
            in H7 by (rewrite length_flatten_list; lia).
          rewrite firstn_all, skipn_O in H7.
          rewrite flatten_deflatten in H7. exists (S k0).
          econstructor; auto.
        * cbn in H13. do 2 deriv. now apply inf_diverges in H12.
        * inv H10.
      Unshelve.
        - constructor; auto. do 4 scope_solver_step.
          apply VMap_scope_Forall, deflatten_keeps_prop_match.
          rewrite indexed_to_forall with (def := VNil). intros.
          rewrite length_flatten_list.
          rewrite scope_repeat_var_prod.
          pose proof (varsFrom_scope (length l * 2) 2 i).
          eapply loosen_scope_val. 2: exact H2.
          rewrite varsFrom_length, length_flatten_list in H1. lia.
          auto.
          auto.
        - inv H0. inv H1. 2: { inv H0. }
          destruct a.
          pose proof (match_pattern_list_map_vars (map (fun '(x, y) => (x.[ξ]ᵥ, y.[ξ]ᵥ)) ((v, v0) :: l))). rewrite length_map in H0.
          destruct_scopes; econstructor; econstructor; auto; econstructor.
          apply H0.
          simpl; econstructor. auto. econstructor; simpl;
          constructor.
          {
            apply VMap_scope_Forall. rewrite deflatten_map.
            apply deflatten_keeps_prop_match. rewrite (map_varsFrom _ _ (v.[ξ]ᵥ :: v0.[ξ]ᵥ :: (flatten_list (map (fun '(x, y) => (x.[ξ]ᵥ, y.[ξ]ᵥ)) l)))).
            replace (length (flatten_list l)) with
                  (length (skipn 2
            (flatten_list (map (fun '(x, y) => (x.[ξ]ᵥ, y.[ξ]ᵥ)) ((v, v0) :: l))))).
            2: {
              rewrite length_skipn, length_flatten_list, length_flatten_list, length_map.
              simpl. lia.
            }
            rewrite firstn_all. simpl.
            apply flatten_keeps_prop. rewrite indexed_to_forall with (def := (VNil, VNil)); intros.
            2: simpl; rewrite length_flatten_list, length_flatten_list, length_map; slia.
            specialize (H6 i H1). specialize (H10 i H1).
            rewrite map_nth with (d := (VNil, VNil)) in H6, H10.
            destruct (nth i (map _ l) _); auto.
          }
          rewrite deflatten_map.
          rewrite (map_varsFrom _ _ (v.[ξ]ᵥ :: v0.[ξ]ᵥ :: (flatten_list
                        (map (fun '(x, y) => (x.[ξ]ᵥ, y.[ξ]ᵥ)) l)))).
          replace (length (flatten_list l)) with
                  (length (skipn 2
            (flatten_list (map (fun '(x, y) => (x.[ξ]ᵥ, y.[ξ]ᵥ)) ((v, v0) :: l))))).
          2: {
            rewrite length_skipn, length_flatten_list, length_flatten_list, length_map.
            simpl. lia.
          }
          rewrite firstn_all. simpl.
          rewrite skipn_O, flatten_deflatten. eassumption.
          simpl. rewrite length_flatten_list, length_flatten_list, length_map. slia.
    }
    apply IHl in H0. constructor; auto.
    apply biforall_length in H0. do 2 rewrite length_map in H0.
    apply Rrel_exp_compat, CIU_iff_Rrel in H.
    destruct a as [v1 v2], p as [v1' v2'].

    (* boiler plate code starts here *)
    split.
    {
      apply Rrel_exp_compat_reverse, CIU_iff_Rrel.
      intros ??. apply H in H1. clear H. simpl in *.
      destruct H1 as [Hsc1 [Hsc2 Hrel]].
      assert (VALCLOSED v1.[ξ]ᵥ /\ VALCLOSED v1'.[ξ]ᵥ) as [Hsc3 Hsc4]. {
        simpl in *.
        destruct_scopes. simpl. split; try apply (H1 0); try apply (H2 0); slia.
      }
      split. 2: split.
      1-2: do 2 constructor; auto.
      intros.
      epose proof (Hrel (FCase1 [([PMap (repeat (PVar, PVar) (length ((v1, v2) :: l)))], ˝ttrue, ˝VVar 0);([PVar], ˝ttrue , °inf)] :: F) _ _) as Hrel.
      repeat deriv.
      - pose proof (match_pattern_list_map_vars_length (1 + length l) (map (fun '(x, y) => (x.[ξ]ᵥ, y.[ξ]ᵥ)) ((v1', v2')::l')) vs') as H1. simpl repeat in H1.
        apply H1 in H11 as H11'. destruct H11' as [Hlen EQ].
        simpl length in *. rewrite length_map in Hlen. clear H1. destruct vs'; inv EQ.
        simpl in H12. repeat deriv.
        eexists. econstructor; eassumption.
      - cbn in H13. do 2 deriv. now apply inf_diverges in H13.
      - inv H10.
    Unshelve.
      + constructor; auto. do 5 scope_solver_step. constructor. lia.
      + inv H1. inv H2. 2: { inv H1. }
        pose proof (match_pattern_list_map_vars (map (fun '(x,y) => (x.[ξ]ᵥ,y.[ξ]ᵥ)) ((v1,v2) :: l))).
        rewrite length_map in H1.
        destruct_scopes; econstructor; econstructor; auto; econstructor.
        apply H1.
        simpl; econstructor. auto. econstructor; simpl;
        constructor.
        cbn. auto.
        simpl. eassumption.
    }
    { (* Same as before, except at two places *)
      apply Rrel_exp_compat_reverse, CIU_iff_Rrel.
      intros ??. apply H in H1. clear H. simpl in *.
      destruct H1 as [Hsc1 [Hsc2 Hrel]].
      assert (VALCLOSED v2.[ξ]ᵥ /\ VALCLOSED v2'.[ξ]ᵥ) as [Hsc3 Hsc4]. { (* difference here *)
        simpl in *.
        destruct_scopes. simpl. split; try apply (H5 0); try apply (H6 0); slia.
      }
      split. 2: split.
      1-2: do 2 constructor; auto.
      intros.
      epose proof (Hrel (FCase1 [([PMap (repeat (PVar, PVar) (length ((v1, v2) :: l)))], ˝ttrue, ˝VVar 1);([PVar], ˝ttrue , °inf)] :: F) _ _) as Hrel. (* difference here: VVar 1 !!! *)
      repeat deriv.
      - pose proof (match_pattern_list_map_vars_length (1 + length l) (map (fun '(x, y) => (x.[ξ]ᵥ, y.[ξ]ᵥ)) ((v1', v2')::l')) vs') as H1. simpl repeat in H1.
        apply H1 in H11 as H11'. destruct H11' as [Hlen EQ].
        simpl length in *. rewrite length_map in Hlen. clear H1. destruct vs'; inv EQ.
        simpl in H12. repeat deriv.
        eexists. econstructor; eassumption.
      - cbn in H13. do 2 deriv. now apply inf_diverges in H13.
      - inv H10.
    Unshelve.
      + constructor; auto. do 5 scope_solver_step. lia.
      + inv H1. inv H2. 2: { inv H1. }
        pose proof (match_pattern_list_map_vars (map (fun '(x,y) => (x.[ξ]ᵥ,y.[ξ]ᵥ)) ((v1,v2) :: l))).
        rewrite length_map in H1.
        destruct_scopes; econstructor; econstructor; auto; econstructor.
        apply H1.
        simpl; econstructor. auto. econstructor; simpl;
        constructor.
        cbn. auto.
        simpl. eassumption.
    }
Qed.

Lemma map_map_subst :
  forall l ξ,
    map (fun x => x.[ξ]) (map VVal l) =
    map VVal (map (fun x => x.[ξ]ᵥ) l).
Proof.
  induction l; intros; simpl; auto.
  now rewrite IHl.
Qed.

Lemma vmap_ignores_sub :
  forall l ξ,
    Forall (fun x => VALCLOSED x) l ->
    map (substVal ξ) l = l.
Proof.
  induction l; intros; simpl; auto. inv H.
  rewrite IHl. rewrite vclosed_ignores_sub. all: auto.
Qed.

Lemma convert_map : forall l ξ, map (substVal ξ) (convert_to_closlist l) =
                                convert_to_closlist (map (fun '(i, ls, x) => (i, ls, x.[upn (Datatypes.length l + ls) ξ])) l).
Proof.
  clear. intros. unfold convert_to_closlist.
  do 2 rewrite map_map. f_equal.
  extensionality x. destruct x, p. now simpl.
Qed.


Lemma CIU_Clos_compat_reverse :
  forall Γ b1 b2 ext1 ext2 id1 id2 p1 p2, p1 = p2 -> id1 = id2 ->
    CIU_open Γ (˝VClos ext1 id1 p1 b1) (˝VClos ext2 id2 p2 b2) ->
    forall ξ l, SUBSCOPE Γ ⊢ ξ ∷ 0 -> Forall (fun v => VALCLOSED v) l -> length l = p1 ->
      CIU (b1.[list_subst (convert_to_closlist ext1 ++ l) idsubst].[ξ])
          (b2.[list_subst (convert_to_closlist ext2 ++ l) idsubst].[ξ]).
Proof.
  intros. subst.
  assert (VALCLOSED (VClos ext1 id2 (length l) b1).[ξ]ᵥ /\
          VALCLOSED (VClos ext2 id2 (length l) b2).[ξ]ᵥ) as [Hcl1 Hcl2]. {
    apply CIU_open_scope in H1. destruct H1. inv H. inv H0. inv H4. inv H1.
    split; apply -> subst_preserves_scope_val; eauto.
  }
  split. 2: split.
  (* scopes *)
  1-2: simpl in *; destruct_scopes; rewrite length_map in *.
  1-2: constructor; rewrite subst_comp_exp.
  {
    rewrite subst_comm, <- subst_comp_exp. simpl_convert_length.
    apply -> subst_preserves_scope_exp; eauto.
    apply scoped_list_subscoped_eq; auto.
    now rewrite length_map, length_app, length_map.
    rewrite map_app. apply Forall_app. split. 2: now rewrite vmap_ignores_sub.
    epose proof (closlist_scope _ (map (fun '(i0, ls, x) => (i0, ls, x.[upn (Datatypes.length ext1 + ls) ξ]))
               ext1) _).
    Unshelve.
      3: {
        intros. rewrite length_map in H. apply H6 in H.
        rewrite length_map. exact H.
      }
    unfold convert_to_closlist in H. rewrite map_map in *.
    assert (
    (fun x : nat * nat * Exp =>
          let
          '(id, vc, e) :=
           let '(i0, ls, x0) := x in (i0, ls, x0.[upn (Datatypes.length ext1 + ls) ξ]) in
           VClos
             (map (fun '(i0, ls, x0) => (i0, ls, x0.[upn (Datatypes.length ext1 + ls) ξ]))
                ext1) id vc e)
     = (fun x : nat * nat * Exp => (let '(id, vc, e) := x in VClos ext1 id vc e).[ξ]ᵥ)
     ). {
      clear. extensionality x. destruct x, p. now simpl.
    }
    rewrite H0 in H. assumption.
  }
  (* boiler plate code for ext2 *)
  {
    rewrite subst_comm, <- subst_comp_exp. simpl_convert_length.
    apply -> subst_preserves_scope_exp; eauto.
    apply scoped_list_subscoped_eq; auto.
    now rewrite length_map, length_app, length_map.
    rewrite map_app. apply Forall_app. split. 2: now rewrite vmap_ignores_sub.
    epose proof (closlist_scope _ (map (fun '(i0, ls, x) => (i0, ls, x.[upn (Datatypes.length ext2 + ls) ξ]))
               ext2) _).
    Unshelve.
      3: {
        intros. rewrite length_map in H. apply H5 in H.
        rewrite length_map. exact H.
      }
    unfold convert_to_closlist in H. rewrite map_map in *.
    assert (
    (fun x : nat * nat * Exp =>
          let
          '(id, vc, e) :=
           let '(i0, ls, x0) := x in (i0, ls, x0.[upn (Datatypes.length ext2 + ls) ξ]) in
           VClos
             (map (fun '(i0, ls, x0) => (i0, ls, x0.[upn (Datatypes.length ext2 + ls) ξ]))
                ext2) id vc e)
     = (fun x : nat * nat * Exp => (let '(id, vc, e) := x in VClos ext2 id vc e).[ξ]ᵥ)
     ). {
      clear. extensionality x. destruct x, p. now simpl.
    }
    rewrite H0 in H. assumption.
  }
  (* evaluation *)
  intros.
  apply H1 in H2 as [_ [_ Hrel]]. clear H1.
  unshelve (epose proof (Hrel (FApp1 (map VVal l) :: F) _ _)).
  {
    constructor; auto. constructor. clear -H3. induction l; simpl; inv H3; constructor; auto.
  }
  {
    destruct H0 as [k D].
    simpl. destruct l.
    * eexists. constructor. auto. constructor. econstructor. congruence.
      reflexivity. simpl.
      rewrite subst_comp_exp, substcomp_list_eq, substcomp_id_l.
      rewrite subst_comp_exp in D. rewrite <- convert_map.
      2: simpl_convert_length;slia.
      rewrite scons_substcomp_list in D.
      rewrite app_nil_r in *. eassumption.
    * eexists. simpl. constructor; auto. constructor.
      constructor. congruence. inv H3. constructor; auto.
      eapply step_term_term_plus. eapply params_eval_create. assumption.
      simpl. rewrite Nat.eqb_refl. reflexivity.
      rewrite subst_comp_exp, substcomp_list_eq, substcomp_id_l.
      rewrite subst_comp_exp in D. rewrite <- convert_map.
      2: simpl_convert_length;slia.
      rewrite scons_substcomp_list, substcomp_id_r in D.
      rewrite map_app in D. rewrite (vmap_ignores_sub (v::l)) in D.
      2: now constructor.
      exact D.
  }
  destruct H1 as [k D]. simpl in D. inv D. destruct l.
  * inv H5. inv H8. simpl in H7.
    rewrite subst_comp_exp, substcomp_list_eq, substcomp_id_l in H7.
    rewrite subst_comp_exp. rewrite <- convert_map in H7.
    2: simpl_convert_length;slia.
    rewrite scons_substcomp_list.
    rewrite app_nil_r in *. eexists. invSome. eassumption.
  * inv H5. inv H8. inv H11. eapply term_step_term in H6.
    2: eapply params_eval_create. eexists. eassumption. now inv H3.
    simpl. rewrite Nat.eqb_refl. f_equal. f_equal.
    do 2 rewrite subst_comp_exp. rewrite substcomp_list_eq, substcomp_id_l.
    rewrite <- convert_map.
    2: simpl_convert_length;slia.
    rewrite scons_substcomp_list, substcomp_id_r.
    rewrite map_app. rewrite (vmap_ignores_sub (v::l)).
    2: assumption. reflexivity.
Qed.

