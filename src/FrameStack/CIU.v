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

Theorem CIU_eval : forall r1 v,
  REDCLOSED r1 ->
  ⟨ [], r1 ⟩ -->* v -> CIU r1 v /\ CIU v r1.
Proof.
  intros. split. split. 2: split. auto.
  inv H0. eapply step_any_closedness; eauto. apply H1. now constructor.

  destruct H0 as [k [Hr Hd]].
  intros. inv H1. eapply frame_indep_nil in Hd.
  eapply term_step_term in H2. 2: eassumption. eexists. eassumption.

  split. 2: split. 2: auto.
  inv H0. eapply step_any_closedness; eauto. apply H1. now constructor.

  intros. destruct H0 as [k [Hr Hd]]. inv H2. eapply frame_indep_nil in Hd.
  eapply step_term_term_plus in Hd. 2: eassumption.
  eexists. eassumption.
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
  forall v v' : Val, CIU (`v) (`v') -> CIU (RValSeq [v]) (RValSeq [v']).
Proof.
  intros. assert (⟨[], `v⟩ -->* RValSeq [v]). {
    eexists. split; auto. econstructor. constructor. constructor.
  }
  assert (⟨[], `v'⟩ -->* RValSeq [v']). {
    eexists. split; auto. econstructor. constructor. constructor.
  }
  apply CIU_eval in H0, H1. 2-3: apply H. intuition.
  epose proof (CIU_transitive_closed _ _ _ H H0).
  now epose proof (CIU_transitive_closed _ _ _ H3 H1).
Qed.

Lemma Erel_Val_compat_closed_reverse :
  forall (v v' : Val), CIU (`v) (`v') -> forall m, Vrel m v v'.
Proof.
  induction v; destruct v'; intros; auto; destruct H as [_ [_ H]].
  1-7: epose proof (H [FCase1 [([PNil], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as H0;
       repeat deriv; inv H8; inv H7; simpl in H10; do 2 deriv; simpl in H8; apply inf_diverges in H8; contradiction.
  1,3-8: epose proof (H [FCase1 [([PLit l], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as H0; repeat deriv; inv H8; inv H7; simpl in H10; do 2 deriv; simpl in H8; apply inf_diverges in H8; contradiction.
  2-3,5-9: epose proof (H [FCase1 [([PCons PVar PVar], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as H0; repeat deriv; inv H8; inv H7; simpl in H10; do 2 deriv; simpl in H8; apply inf_diverges in H8; contradiction.
  3-5,7-10: epose proof (H [FCase1 [([PTuple (repeat PVar (length l))], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as H0; repeat deriv; inv H8; inv H7; simpl in H10; do 2 deriv; simpl in H8; apply inf_diverges in H8; contradiction.
  4-7,9-11: epose proof (H [FCase1 [([PMap (repeat (PVar, PVar) (length l))], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as H0; repeat deriv; inv H8; inv H7; simpl in H10; do 2 deriv; simpl in H8; apply inf_diverges in H8; contradiction.
  5: { admit. }
Qed.

Lemma Erel_Val_compat_reverse :
  forall Γ (v v' : Val), Erel_open Γ (`v) (`v') -> Vrel_open Γ v v'.
Proof.
  intros. unfold Erel_open, Vrel_open in *. intros.
  apply H in H0. simpl in H0. destruct H0 as [HCl1 [HCl2 H0]].
  rewrite Vrel_Fix_eq. inv HCl1. inv HCl2.
  
Qed.