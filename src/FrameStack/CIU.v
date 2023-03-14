From CoreErlang.FrameStack Require Export Compatibility.

Import ListNotations.


Definition CIU (e1 e2 : Exp) : Prop :=
  EXPCLOSED e1 /\ EXPCLOSED e2 /\
  forall F, FSCLOSED F -> | F, RExp e1 | ↓ -> | F, RExp e2 | ↓.



Definition CIU_open (Γ : nat) (e1 e2 : Exp) :=
  forall ξ, SUBSCOPE Γ ⊢ ξ ∷ 0 ->
  CIU (e1.[ξ]) (e2.[ξ]).


Lemma CIU_closed :
  forall e1 e2,
  CIU e1 e2 -> EXPCLOSED e1 /\ EXPCLOSED e2.
Proof.
  intros. unfold CIU in H. intuition.
Qed.


Lemma CIU_closed_l : forall {e1 e2},
    CIU e1 e2 ->
    EXPCLOSED e1.
Proof.
  intros.
  apply CIU_closed in H.
  intuition.
Qed.

Global Hint Resolve CIU_closed_l : core.



Lemma CIU_closed_r : forall {e1 e2},
    CIU e1 e2 ->
    EXPCLOSED e2.
Proof.
  intros.
  apply CIU_closed in H.
  intuition.
Qed.

Global Hint Resolve CIU_closed_r : core.

Lemma CIU_open_scope : forall {Γ e1 e2},
    CIU_open Γ e1 e2 ->
    EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2.
Proof.
  intros.
  unfold CIU_open in H.
  split.
  * destruct e1.
    - constructor. simpl in H.
      apply (subst_implies_scope_val _ _ 0). intros.
      specialize (H ξ H0). inversion H. inversion H1. auto.
    - constructor. simpl in H.
      apply (subst_implies_scope_nval _ _ 0). intros.
      specialize (H ξ H0). inversion H. inversion H1. auto.
  * destruct e2.
    - constructor. simpl in H.
      apply (subst_implies_scope_val _ _ 0). intros.
      specialize (H ξ H0). inversion H. destruct H2. inversion H2.
      auto.
    - constructor. simpl in H.
      apply (subst_implies_scope_nval _ _ 0). intros.
      specialize (H ξ H0). inversion H. destruct H2. inversion H2.
      auto.
Qed.


Lemma CIU_open_scope_l : forall {Γ e1 e2},
    CIU_open Γ e1 e2 ->
    EXP Γ ⊢ e1.
Proof.
  intros.
  apply CIU_open_scope in H.
  intuition.
Qed.


Global Hint Resolve CIU_open_scope_l : core.

Lemma CIU_open_scope_r : forall {Γ e1 e2},
    CIU_open Γ e1 e2 ->
    EXP Γ ⊢ e2.
Proof.
  intros.
  apply CIU_open_scope in H.
  intuition.
Qed.

Global Hint Resolve CIU_open_scope_r : core.

Lemma Erel_implies_CIU : forall Γ e1 e2,
  Erel_open Γ e1 e2 ->
  CIU_open Γ e1 e2.
Proof.
  intros.
  unfold CIU_open; intros.
  unfold CIU.
  split. 2: split.
  - apply -> (subst_preserves_scope_exp); eauto.
  - apply -> (subst_preserves_scope_exp); eauto.
  - unfold Erel_open, Erel, exp_rel in H. intros. destruct H2.
    specialize (H x ξ ξ (Grel_Fundamental _ _ H0 _)). destruct H, H3.
    eapply H4 in H2; eauto. apply Frel_Fundamental_closed. auto.
Qed.

Lemma Erel_comp_CIU_implies_Erel : forall {Γ e1 e2 e3},
    Erel_open Γ e1 e2 ->
    CIU_open Γ e2 e3 ->
    Erel_open Γ e1 e3.
Proof.
  intros Γ e1 e2 e3 HErel HCIU.
  unfold Erel_open, Erel, exp_rel.
  intros.
  inversion H as [Hξ1 [Hξ2 _]].
  split. 2: split. 1-2: apply -> subst_preserves_scope_exp; eauto.
  intros. eapply HErel in H1; eauto. eapply HCIU in H1; eauto.
Qed.

Lemma CIU_implies_Erel : forall {Γ e1 e2},
    CIU_open Γ e1 e2 ->
    Erel_open Γ e1 e2.
Proof.
  intros.
  eapply Erel_comp_CIU_implies_Erel; eauto.
Qed.

Theorem CIU_iff_Erel : forall {Γ e1 e2},
    CIU_open Γ e1 e2 <->
    Erel_open Γ e1 e2.
Proof.
  intuition (auto using CIU_implies_Erel, Erel_implies_CIU).
Qed.

Theorem CIU_eval : forall e1 v,
  EXPCLOSED e1 ->
  ⟨ [], e1 ⟩ -->* v -> CIU e1 v /\ CIU v e1.
Proof.
  intros. split. split. 2: split. auto.
  apply step_any_closedness in H0; auto. now constructor.
  intros. destruct H2, H0, H3. eapply frame_indep_nil in H3.
  eapply terminates_step_any. 2: exact H3. eexists. exact H2.

  split. 2: split. 2: auto.
  apply step_any_closedness in H0; auto. now constructor.
  intros. destruct H2, H0, H3. eapply frame_indep_nil in H3.
  exists (x + x0).
  eapply term_step_term. exact H3. 2: lia. replace (x + x0 - x0) with x by lia. exact H2.
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
