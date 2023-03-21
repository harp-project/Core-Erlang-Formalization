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


(*--- ProgRes Ver ---*)
(* 
Definition substProg (ξ : Substitution) (base : ProgResult) : ProgResult :=
match base with
| RExp e      => RExp (e.[ξ])
| ValSeqRes vs  => ValSeqRes (map (fun x => substVal ξ x) vs)
| ExcRes (class, reason, details) => ExcRes (class, reason.[ξ]ᵥ, details.[ξ]ᵥ)
end.
Notation "s .[ σ ]ₚ" := (substProg σ s)
  (at level 2, σ at level 200, left associativity,
   format "s .[ σ ]ₚ" ).


Definition CIU (p1 p2 : ProgResult) : Prop :=
  PROGCLOSED p1 /\ PROGCLOSED p2 /\
  forall F, FSCLOSED F -> | F, p1 | ↓ -> | F, p2 | ↓.



Definition CIU_open (Γ : nat) (p1 p2 : ProgResult) :=
  forall ξ, SUBSCOPE Γ ⊢ ξ ∷ 0 ->
  CIU (p1.[ξ]ₚ) (p2.[ξ]ₚ).



Lemma CIU_closed :
  forall p1 p2,
  CIU p1 p2 -> PROGCLOSED p1 /\ PROGCLOSED p2.
Proof.
  intros. unfold CIU in H. intuition.
Qed.



Lemma CIU_closed_l : forall {p1 p2},
    CIU p1 p2 ->
    PROGCLOSED p1.
Proof.
  intros.
  apply CIU_closed in H.
  intuition.
Qed.

Global Hint Resolve CIU_closed_l : core.



Lemma CIU_closed_r : forall {p1 p2},
    CIU p1 p2 ->
    PROGCLOSED p2.
Proof.
  intros.
  apply CIU_closed in H.
  intuition.
Qed.

Global Hint Resolve CIU_closed_r : core.



Check subst_implies_scope_exp.
Lemma CIU_open_scope : forall {Γ p1 p2},
    CIU_open Γ p1 p2 ->
    PROG Γ ⊢ p1 /\ PROG Γ ⊢ p2.
Proof.
  intros.
  unfold CIU_open in H.
  split.
  * destruct p1.
    - constructor. Check subst_implies_scope_exp.
      eapply (subst_implies_scope_exp _ _ 0).
      intros. specialize (H ξ H0). inversion H.
      inversion H1. auto.
    - constructor. Check subst_implies_scope_val.
      intros. eapply (subst_implies_scope_val _ _ 0).
      intros. specialize (H ξ H1). inversion H.
      inversion H2. rewrite map_length in H5.
      specialize (H5 i H0).
      Check map_nth. remember (fun x : ValueExpression => x.[ξ]ᵥ) as F.
      replace VNil with (F VNil) in H5 by (subst;simpl;auto).
      rewrite map_nth in H5. subst. auto.
    - destruct e. destruct p. constructor.
      + eapply (subst_implies_scope_val _ _ 0).
        intros. specialize (H ξ H0). inversion H.
        inversion H1. auto.
      + eapply (subst_implies_scope_val _ _ 0).
        intros. specialize (H ξ H0). inversion H.
        inversion H1. auto.
  * destruct p2.
    - constructor. Check subst_implies_scope_exp.
      eapply (subst_implies_scope_exp _ _ 0).
      intros. specialize (H ξ H0). inversion H.
      destruct H2. inversion H2. auto.
    - constructor. Check subst_implies_scope_val.
      intros. eapply (subst_implies_scope_val _ _ 0).
      intros. specialize (H ξ H1). inversion H.
      destruct H3. inversion H3. rewrite map_length in H6.
      specialize (H6 i H0).
      Check map_nth. remember (fun x : ValueExpression => x.[ξ]ᵥ) as F.
      replace VNil with (F VNil) in H6 by (subst;simpl;auto).
      rewrite map_nth in H6. subst. auto.
    - destruct e. destruct p. constructor.
      + eapply (subst_implies_scope_val _ _ 0).
        intros. specialize (H ξ H0). inversion H.
        destruct H2. inversion H2. auto.
      + eapply (subst_implies_scope_val _ _ 0).
        intros. specialize (H ξ H0). inversion H.
        destruct H2. inversion H2. auto.
Qed.



Lemma CIU_open_scope_l : forall {Γ p1 p2},
    CIU_open Γ p1 p2 ->
    PROG Γ ⊢ p1.
Proof.
  intros.
  apply CIU_open_scope in H.
  intuition.
Qed.


Global Hint Resolve CIU_open_scope_l : core.

Lemma CIU_open_scope_r : forall {Γ p1 p2},
    CIU_open Γ p1 p2 ->
    PROG Γ ⊢ p2.
Proof.
  intros.
  apply CIU_open_scope in H.
  intuition.
Qed.

Global Hint Resolve CIU_open_scope_r : core.
*)
