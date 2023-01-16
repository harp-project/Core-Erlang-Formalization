From CoreErlang Require Export Manipulation.

Ltac extract_map_fun F :=
  match goal with
  | |- context G [map ?f _] => remember f as F
  | [H : context G [map ?f _] |- _ ] =>  remember f as F
  end.

Tactic Notation "extract_map_fun" "in" constr(H) "as" ident(F) :=
  match type of H with 
  | context G [map ?f _] => remember f as F
  end.

(** 
  This definition states that all variables in Γ are preserved
  by the substitution.
*)
Definition subst_preserves (Γ : nat) (ξ : Substitution) : Prop :=
  forall v, v < Γ -> ξ v = inr v.

(** If Γ is preserved by a sustitution, then 1 + Γ is preserved by the shifted substitution. *)
Theorem subst_preserves_up : forall Γ ξ,
  subst_preserves Γ ξ -> subst_preserves (S Γ) (up_subst ξ).
Proof.
  intros. unfold subst_preserves in *. intros. unfold up_subst. destruct v; auto.
  apply Nat.succ_lt_mono in H0. apply H in H0. unfold shift. rewrite H0. auto.
Qed.

Global Hint Resolve subst_preserves_up : core.

(** 
This theorem is the iterated version of the previous one.

This corollary means that if for a given Γ (nat), Substitution ξ returns the input for every input that are smaller than Γ, than for (n + Γ) (nat that are n value bigger tan Γ) Substitution (upn n ξ) (ξ exept returns n value bigger numbers) will be in the same relation.*)
Corollary subst_preserves_upn : forall n Γ ξ,
  subst_preserves Γ ξ -> subst_preserves (n + Γ) (upn n ξ).
Proof.
  induction n; intros.
  * simpl. auto.
  * simpl. apply subst_preserves_up, IHn. auto.
Qed.

Global Hint Resolve subst_preserves_upn : core.

(** the empty set (0) is always preserved by any substitution *)
Theorem subst_preserves_empty ξ : subst_preserves 0 ξ.
Proof. intro. intros. inversion H. Qed.

Global Hint Resolve subst_preserves_empty : core.

(** This theorem says that if an Exp is scoped in Γ then every substitution ξ that preserves this Γ, if e does not change when substituted with such a ξ Substitution.*)
Theorem scoped_ignores_sub :
  (forall Γ e, EXP  Γ ⊢ e -> forall ξ, subst_preserves Γ ξ -> e.[ξ] = e) /\
  (forall Γ e, VAL  Γ ⊢ e -> forall ξ, subst_preserves Γ ξ -> e.[ξ]ᵥ = e) /\
  (forall Γ e, NVAL Γ ⊢ e -> forall ξ, subst_preserves Γ ξ -> e.[ξ]ₑ = e).
Proof.
  apply scoped_ind; intros; simpl; try (auto + rewrite H; now auto).
  * destruct fi. rewrite H; auto.
  * erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - rewrite indexed_to_forall with (def := VNil). intros. now apply H.
  * now rewrite H0, H.
 (* This needed a rewrite afther the map fst l, type of rewrites in the scoping. The new proof is below.*)
  * erewrite map_ext_Forall with (g := id).
    - now rewrite map_id.
    - rewrite indexed_to_forall with (def := (VNil,VNil)). intros.
      destruct (nth i l) eqn:Eq. unfold id. 
      specialize (H i H2 ξ H1).
      specialize (H0 i H2 ξ H1).
      f_equal.
      + replace VNil with (fst (VNil,VNil)) in H by auto.
        rewrite map_nth, Eq in H. now cbn in *.
      + replace VNil with (snd (VNil,VNil)) in H0 by auto.
        rewrite map_nth, Eq in H0. now simpl in H0.
  * erewrite map_ext_Forall  with (g := Datatypes.id).
    - rewrite H0, map_id. reflexivity.
      now apply subst_preserves_upn.
    - rewrite indexed_to_forall with (def := (0,0,VVal VNil)). intros.
      specialize (H i H2).
      unfold Datatypes.id. destruct (nth i ext) eqn:Eq. destruct p eqn:Eq2. simpl in *.
      specialize (H (upn (Datatypes.length ext + nth i (map (snd ∘ fst) ext) 0) ξ)).
      specialize (H (subst_preserves_upn _ _ _ H1)).
      replace (VVal VNil) with (snd (0,0,VVal VNil)) in H by auto.
      rewrite map_nth in H. rewrite Eq in H. simpl in H. 
      replace (nth i (map (snd ∘ fst) ext) 0) with n1 in H.
      + rewrite H. auto.
      + replace 0 with ((snd ∘ fst) (0,0,VVal VNil)) by auto.
        rewrite map_nth. rewrite Eq. auto.
  * erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - rewrite indexed_to_forall with (def := (VVal VNil)). intros. specialize (H i H1). rewrite H.
      + unfold id. reflexivity.
      + assumption.
  * rewrite H.
    - rewrite H0.
      + reflexivity.
      + assumption.
    - assumption.
  * erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - rewrite indexed_to_forall with (def := (VVal VNil,VVal VNil)). intros. specialize (H i H2).
      specialize (H0 i H2). destruct (nth i l) eqn:Eq. unfold id. simpl in *.
      f_equal.
      + specialize (H ξ H1). replace (VVal VNil) with (fst (VVal VNil,VVal VNil)) in H
        by auto. rewrite map_nth in H. rewrite Eq in H. simpl in H. assumption.
      + specialize (H0 ξ H1). replace (VVal VNil) with (snd (VVal VNil,VVal VNil)) in H0
        by auto. rewrite map_nth in H0. rewrite Eq in H0. simpl in H0. assumption.
  * erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - rewrite indexed_to_forall with (def := (VVal VNil)). intros. unfold id. specialize (H i H1).
      rewrite H.
      + reflexivity.
      + assumption.
  * erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - rewrite indexed_to_forall with (def := (VVal VNil)). intros. unfold id. specialize (H i H1). 
      rewrite H.
      + reflexivity.
      + assumption.
  * erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - rewrite indexed_to_forall with (def := (VVal VNil)). intros. unfold id. specialize (H i H1).
      rewrite H.
      + reflexivity.
      + assumption.
  * erewrite map_ext_Forall with (g := id).
    - rewrite map_id. rewrite H.
      + reflexivity.
      + assumption.
    - rewrite indexed_to_forall with (def := (VVal VNil)). intros. unfold id. specialize (H0 i H2). 
      rewrite H0.
      + reflexivity.
      + assumption.
  * erewrite map_ext_Forall with (g := id).
    - rewrite map_id. rewrite H.
      + reflexivity.
      + assumption.
    - rewrite indexed_to_forall with (def := (nil,VVal VNil,VVal VNil)). intros. unfold id.
      specialize (H0 i H3). specialize (e1 i H3). specialize (H1 i H3).
      destruct (nth i l) eqn:Eq. destruct p eqn:Eq2. simpl in *. 
      f_equal.
      + f_equal. specialize (H0 (upn (PatListScope (nth i (map (fst ∘ fst) l) nil)) ξ)).
        specialize (H0 (subst_preserves_upn _ _ _ H2)). 
        replace (VVal VNil) with ((fst >>> snd) (nil : list Pat, VVal VNil, VVal VNil)) in H0 by auto.
        rewrite map_nth in H0. rewrite Eq in H0.
        replace nil with ((fst >>> fst) (nil : list Pat, VVal VNil, VVal VNil)) in H0 by auto.
        rewrite map_nth in H0. rewrite Eq in H0. simpl in H0. assumption.
      + specialize (H1 (upn (PatListScope (nth i (map (fst >>> fst) l) nil)) ξ)).
        specialize (H1 (subst_preserves_upn _ _ _ H2)).
        replace (VVal VNil) with (snd((nil : list Pat, VVal VNil, VVal VNil))) in H1 by auto.
        rewrite map_nth in H1. rewrite Eq in H1.
        replace nil with ((fst >>> fst)(nil : list Pat, VVal VNil, VVal VNil)) in H1 by auto.
        rewrite map_nth in H1. rewrite Eq in H1. simpl in H1. assumption.
  * rewrite H.
    - rewrite H0.
      + reflexivity.
      + apply subst_preserves_upn. assumption.
    - assumption.
  * rewrite H.
    - rewrite H0.
      + reflexivity.
      + assumption.
    - assumption.
  * erewrite map_ext_Forall with (g := id).
    - rewrite map_id. rewrite H0.
      + reflexivity.
      + apply subst_preserves_upn. assumption.
    - rewrite indexed_to_forall with (def := (0,VVal VNil)). intros. unfold id.
      specialize (H i H2). specialize (e0 i H2). destruct (nth i l) eqn:Eq. simpl in *.
      f_equal. specialize (H (upn (Datatypes.length l + nth i (map fst l) 0) ξ)).
      specialize (H (subst_preserves_upn _ _ _ H1)).
      replace (VVal VNil) with (snd (0,VVal VNil)) in H by auto. rewrite map_nth in H.
      rewrite Eq in H. replace 0 with (fst(0,VVal VNil)) in H by auto. rewrite map_nth in H.
      rewrite Eq in H. simpl in H. assumption.
  * rewrite H.
    - rewrite H0.
      + rewrite H1.
        ** reflexivity.
        ** apply subst_preserves_upn. assumption.
      + apply subst_preserves_upn. assumption.
    - assumption.
Qed.

(** This Corollary says that if an e Exp is is closed (has no free variables, i.e. it's scope is empty), then the application of any ξ Substitution will not change it. *)
Corollary eclosed_ignores_sub :
  forall e ξ,
  EXPCLOSED e -> subst ξ e = e.
Proof.
  intros. eapply scoped_ignores_sub with (Γ := 0); auto.
Qed.


(** Same for values: *)
Corollary vclosed_ignores_sub :
  forall e ξ,
  VALCLOSED e -> substVal ξ e = e.
Proof.
  intros. pose proof scoped_ignores_sub as [_ [Hs _]]. specialize (Hs 0 e). apply Hs.
  - assumption.
  - apply subst_preserves_empty.
Qed.

(** Same for non-values: *)
Corollary nvclosed_ignores_sub :
  forall e ξ,
  NVALCLOSED e -> substNonVal ξ e = e.
Proof.
  intros. pose proof scoped_ignores_sub as [_ [_ Hs]]. specialize (Hs 0 e). apply Hs.
  - assumption.
  - apply subst_preserves_empty.
Qed.

Global Hint Resolve eclosed_ignores_sub : core.

Global Hint Resolve vclosed_ignores_sub : core.

Global Hint Resolve nvclosed_ignores_sub : core.


(** This Theorem says that if an e Exp is scoped in Γ then it is also scoped in (S Γ), a one increment bigger value. So the scoping can be extended. *)
Theorem scope_ext :
  (forall Γ e, EXP Γ ⊢ e  ->  EXP (S Γ) ⊢ e) /\
  (forall Γ e, VAL Γ ⊢ e  ->  VAL (S Γ) ⊢ e) /\
  (forall Γ e, NVAL Γ ⊢ e ->  NVAL (S Γ) ⊢ e).
Proof.
  eapply scoped_ind; intros; try now (constructor; auto).
  (* * intros. constructor. assumption. *)
  * intros. constructor.
    - intros. specialize (H i H1). rewrite Nat.add_succ_r. assumption.
    - rewrite Nat.add_succ_r. assumption.
  * intros. constructor. rewrite Nat.add_succ_r. assumption.
  * intros. constructor.
    - assumption.
    - intros. rewrite Nat.add_succ_r. apply H0. assumption.
    - intros. rewrite Nat.add_succ_r. apply H1. assumption.
  * intros. constructor.
    - assumption.
    - rewrite Nat.add_succ_r. assumption.
  * intros. constructor.
    - intros. rewrite Nat.add_succ_r. apply H. assumption.
    - rewrite Nat.add_succ_r. assumption.
  * intros. constructor.
    - assumption.
    - rewrite Nat.add_succ_r. assumption.
    - rewrite Nat.add_succ_r. assumption.
Qed.


(** This corollary is a projection of the previous theorem for Exps *)
Corollary scope_ext_Exp : forall {e Γ},
    EXP Γ ⊢ e -> EXP S Γ ⊢ e.
Proof.
  intros.
  apply scope_ext.
  auto.
Qed.

(** This corollary is a projection of the previous theorem for values *)
Corollary scope_ext_Val : forall {e Γ},
    VAL Γ ⊢ e -> VAL S Γ ⊢ e.
Proof.
  intros.
  apply scope_ext.
  auto.
Qed.

(** This corollary is a projection of the previous theorem for non-values *)
Corollary scope_ext_NonVal : forall {e Γ},
    NVAL Γ ⊢ e -> NVAL S Γ ⊢ e.
Proof.
  intros.
  apply scope_ext.
  auto.
Qed.

(** This Corollary is the generalisation of the previous theorem.
    It says that the scope can be extended by any number. *)
Corollary scope_ext_app : forall Γ' Γ, Γ <= Γ' ->
  (forall e, VAL Γ ⊢ e -> VAL Γ' ⊢ e) /\
  forall e, EXP Γ ⊢ e -> EXP Γ' ⊢ e.
Proof.
 intros. induction H.
 * intuition.
 * split; intros; eapply scope_ext; eapply IHle; auto. 
Qed.

(** This Lemma says that id maps scope Γ to Γ. *)
Lemma renscope_id Γ : RENSCOPE Γ ⊢ id ∷ Γ.
Proof.
  firstorder.
Qed.

Global Hint Resolve renscope_id : core.

(** This Lemma says that the idsubst maps Γ to Γ.*)
Lemma scope_idsubst Γ : SUBSCOPE Γ ⊢ idsubst ∷ Γ.
Proof.
  firstorder.
Qed.

Global Hint Resolve scope_idsubst : core.

(** This Lemma says that if a ξ renaming maps Γ to Γ', then the its shifing maps (S Γ) to (S Γ')*)
Lemma upren_scope : forall Γ Γ' ξ,
  RENSCOPE Γ ⊢ ξ ∷ Γ' ->
  RENSCOPE (S Γ) ⊢ upren ξ ∷ (S Γ').
Proof.
  intros.
  unfold renscoped in *.
  intros.
  revert ξ Γ Γ' H H0.
  induction x;
    intros;
    simpl;
    firstorder using Nat.succ_lt_mono.
    lia.
  apply -> Nat.succ_lt_mono. apply H. lia.
Qed.

(** This corollary is the generalisation of the previous lemma. *)
Corollary uprenn_scope : forall Γ'' Γ Γ' ξ,
  RENSCOPE Γ ⊢ ξ ∷ Γ' ->
  RENSCOPE (Γ'' + Γ) ⊢ uprenn Γ'' ξ ∷ (Γ'' + Γ').
Proof.
  induction Γ''; intros.
  * repeat rewrite Nat.add_0_l. apply H.
  * repeat rewrite Nat.add_succ_l. apply upren_scope. apply IHΓ''. auto.
Qed.

Global Hint Resolve upren_scope : core.
Global Hint Resolve uprenn_scope : core.



(** This Lemma says that if an e Exp is scoped in Γ then, if a ξ renaming maps Γ to Γ', then e renamed with this ξ is scoped in Γ', and vica versa. *)
Lemma ren_preserves_scope :
    (forall e Γ, EXP Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       EXP Γ' ⊢ rename ξ e) /\
       
    (forall e Γ, NVAL Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       NVAL Γ' ⊢ renameNonVal ξ e) /\
       
    (forall e Γ, VAL Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       VAL Γ' ⊢ renameVal ξ e).
Proof.
   eapply Exp_ind with
    (QV := fun l => Forall (fun e => forall Γ, VAL Γ ⊢ e <->
    forall (Γ' : nat) (ξ : Renaming),
    RENSCOPE Γ ⊢ ξ ∷ Γ' -> VAL Γ' ⊢ renameVal ξ e) l)
  (RV := fun l => forall i, i < length l -> 
    (forall Γ, VAL Γ ⊢ (nth i (map fst l) VNil) <->
      forall (Γ' : nat) (ξ : Renaming), RENSCOPE Γ ⊢ ξ ∷ Γ' -> VAL Γ' ⊢ renameVal ξ    (nth i (map fst l) VNil))
    /\ 
    (forall Γ, VAL Γ ⊢  (nth i (map snd l) VNil) <->
     forall (Γ' : nat) (ξ : Renaming), RENSCOPE Γ ⊢ ξ ∷ Γ' -> VAL Γ' ⊢ renameVal ξ  (nth i (map snd l) VNil)))
  (VV := fun l => 
	forall i, i < length l -> 
    (forall Γ, EXP Γ ⊢ (nth i (map snd l) (VVal VNil)) <->
      forall (Γ' : nat) (ξ : Renaming), RENSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ rename ξ (nth i (map snd l) (VVal VNil)))
)
  (Q := fun l => forall i, i < length l -> (forall Γ, EXP Γ ⊢ (nth i l (VVal VNil)) <-> forall Γ' ξ, RENSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ rename ξ (nth i l (VVal VNil))))
  (R := fun l => forall i, i < length l -> 
    (forall Γ, EXP Γ ⊢ (nth i (map fst l) (VVal VNil)) <->
      forall (Γ' : nat) (ξ : Renaming), RENSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ rename ξ (nth i (map fst l) (VVal VNil)))
    /\ 
    (forall Γ, EXP Γ ⊢  (nth i (map snd l) (VVal VNil)) <->
     forall (Γ' : nat) (ξ : Renaming), RENSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ rename ξ (nth i (map snd l) (VVal VNil))))
  (W := fun l => forall i, i < length l -> 
    (forall Γ, EXP Γ ⊢ (nth i (map (fst >>> snd) l) (VVal VNil)) <->
      forall (Γ' : nat) (ξ : Renaming), RENSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ rename ξ (nth i (map (fst >>> snd) l) (VVal VNil)))
    /\ 
    (forall Γ, EXP Γ ⊢  (nth i (map snd l) (VVal VNil)) <->
     forall (Γ' : nat) (ξ : Renaming), RENSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ rename ξ (nth i (map snd l) (VVal VNil))))
  (Z := fun l =>  forall i, i < length l ->  (forall Γ, EXP Γ ⊢ (nth i (map snd l) (VVal VNil)) <->
      forall (Γ' : nat) (ξ : Renaming), RENSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ rename ξ (nth i (map snd l) (VVal VNil))))
  ; try now (intros; simpl; split; constructor; auto).
  * intros. simpl. split.
    - intros. inversion H0. subst. specialize (H Γ). destruct H. constructor. now apply H.
    - intros. constructor. specialize (H Γ). destruct H. apply H1.
      intros. apply H0 in H2. now inversion H2.
  * intros. simpl. split.
    - intros. inversion H0. subst. specialize (H Γ). destruct H. constructor. now apply H.
    - intros. constructor. specialize (H Γ). destruct H. apply H1.
      intros. apply H0 in H2. now inversion H2.
  * intros. simpl. split.
    - intros. inversion H1. constructor.
      + specialize (H Γ). destruct H. subst. now apply H.
      + specialize (H0 Γ). destruct H0. subst. now apply H0.
    - intros. constructor.
      + specialize (H Γ). destruct H. apply H2. intros.
        specialize (H1 _ _ H3).
        now inversion H1.
      + specialize (H0 Γ). destruct H0. apply H2. intros.
        specialize (H1 _ _ H3). now inversion H1.
  * intros. split.
    - intros. simpl. constructor. inversion H0. subst. intros.
      rewrite indexed_to_forall with (def := VNil) in H. rewrite map_length in H2.
      specialize (H i H2 Γ). destruct H. specialize (H4 i H2). specialize (H H4).
      specialize (H _ _ H1). rewrite <- map_nth in H.
      assumption.
    - intros. constructor. rewrite indexed_to_forall with (def := VNil) in H.
      intros. specialize (H i H1 Γ). destruct H. apply H2. intros.
      specialize (H0 _ _ H3). simpl in H0. inversion H0. subst. rewrite <- map_nth.
      apply H6. rewrite map_length. assumption.
  * intros. split.
    - intros.
      inversion H0. subst. simpl. constructor.
        + intros. rewrite map_length in H2.  specialize (H i H2).
          destruct H. specialize (H Γ). destruct H.
          apply H3 in H2 as H2'. specialize (H H2'). specialize (H Γ' ξ). specialize (H H1).
          rewrite map_map. rewrite <- map_nth in H. simpl in H. rewrite map_map in H.
          (* you can proove the eqvivalence of these functions. *)
          replace ((fun x : Val * Val =>
          fst (let '(x0, y) := x in (renameVal ξ x0, renameVal ξ y)))) with
          (fun x : Val * Val => renameVal ξ (fst x)).
        ** assumption.
        ** apply functional_extensionality. intros x. destruct x. simpl. auto.
      + intros. rewrite map_length in H2.  specialize (H i H2).
        destruct H. specialize (H4 Γ). destruct H4. apply H5 in H2 as H2'.
        specialize (H4 H2' Γ' ξ H1).
        rewrite map_map. rewrite <- map_nth in H4. simpl in H4.
        rewrite map_map in H4.
        replace ((fun x : Val * Val =>
        snd (let '(x0, y) := x in (renameVal ξ x0, renameVal ξ y)))) with
        (fun x : Val * Val => renameVal ξ (snd x)).
        ** assumption.
        ** apply functional_extensionality. intros x. destruct x. simpl. auto.
    - intros. constructor.
      + intros. specialize (H i H1). destruct H. specialize (H Γ). destruct H.
        apply H3. intros. specialize (H0 _ _ H4). simpl in H0. inversion H0. subst.
        rewrite <- map_nth. rewrite <- map_nth. simpl. specialize (H6 i).
        rewrite map_length in H6. specialize (H6 H1).
        rewrite <- map_nth in H6. 
        replace (map fst (map (fun '(x, y) => (renameVal ξ x, renameVal ξ y)) l))
        with (map (renameVal ξ) (map fst l)) in H6.
        ** assumption.
        ** rewrite map_map. rewrite map_map. f_equal.
           apply functional_extensionality. intros x. destruct x. simpl. auto.
      + intros. specialize (H i H1). destruct H. specialize (H2 Γ). destruct H2.
        apply H3. intros. specialize (H0 _ _ H4). simpl in H0. inversion H0. subst.
        rewrite <- map_nth. rewrite <- map_nth. simpl. specialize (H8 i).
        rewrite map_length in H8. specialize (H8 H1).
        rewrite <- map_nth in H8. 
        replace (map snd (map (fun '(x, y) => (renameVal ξ x, renameVal ξ y)) l))
        with (map (renameVal ξ) (map snd l)) in H8.
        ** assumption.
        ** rewrite map_map. rewrite map_map. f_equal.
           apply functional_extensionality. intros x. destruct x. simpl. auto.
  * intros. split.
    - intros. simpl. inversion H. subst. constructor. auto.
    - intros. specialize (H Γ id). simpl in *.
      apply H. apply renscope_id.
  * intros. split.
    - intros. simpl. inversion H. subst. destruct n. constructor.
      now apply H0 in H3.
    - intros. specialize (H Γ). specialize (H id). simpl in *.
      destruct n. apply H. apply renscope_id.
  (* This one is complicated. *)
  * intros. split.
    - simpl. constructor. 
      + intros. rewrite map_length. rewrite map_length in H3.
        clear H0. specialize (H i H3). inversion H1. subst.
        specialize (H (Datatypes.length ext + (nth i (map (fst >>> snd) ext) 0) + Γ)).
        destruct H. clear H0 H1. specialize (H6 i H3). specialize (H H6).
        pose proof uprenn_scope as H0.
        specialize (H0 (Datatypes.length ext + (nth i (map (snd ∘ fst) ext) 0)) Γ Γ' ξ H2).
        specialize (H (Datatypes.length ext + (nth i (map (snd ∘ fst) ext) 0) + Γ')
        (uprenn (Datatypes.length ext + nth i (map (snd ∘ fst) ext) 0) ξ)).
        specialize (H H0). clear H0.
        remember (fun x : nat * nat * Exp => (snd ∘ fst) x) as Fsf.
        replace 0 with (Fsf (0,0,VVal VNil)) in H by (subst;auto).
        replace (VVal VNil) with (snd (0,0,VVal VNil)) in H by auto.
        do 2 rewrite map_nth in H.
        do 2 rewrite map_map.
        extract_map_fun FSF.
        replace 0 with (FSF (0,0,VVal VNil)) by (subst;auto).
        rewrite map_nth.
        extract_map_fun FS.
        replace (VVal VNil) with (FS (0,0,VVal VNil)) by (subst;auto).
        rewrite map_nth. subst FS FSF Fsf. cbn in *.
        destruct (nth i ext (0, 0, ` VNil)), p; now cbn in *.
      + clear H. inv H1.
        specialize (H0 (Datatypes.length ext + vl + Γ)). destruct H0.
        clear H0. pose proof uprenn_scope.
        specialize (H0 (Datatypes.length ext + vl) Γ Γ' ξ H2).
        specialize (H H8 (Datatypes.length ext + vl + Γ')
        (uprenn (Datatypes.length ext + vl) ξ)). specialize (H H0).
        clear H2 H0 H8. rewrite map_length. assumption.
    - clear H H0. intros. pose proof idrenaming_is_id as [_ [_ H0]].
      specialize (H Γ Datatypes.id). specialize (H (renscope_id Γ)).
      rewrite H0 in H. assumption.
  * intros. split.
    - intros. simpl. constructor. inversion H0. subst. specialize (H (n+Γ)).
      destruct H. apply H; auto.
    - intros. constructor. specialize (H0 Γ id). specialize (H0 (renscope_id Γ)).
      inversion H0. subst. rewrite idrenaming_upn in H3.
      pose proof idrenaming_is_id as [H5 [_ _]].
      now rewrite H5 in H3.
  * intros. split.
    - intros. simpl. constructor. intros. rewrite map_length in H2.
      specialize (H i H2). specialize (H Γ). destruct H.
      inversion H0. subst. specialize (H6 i H2). specialize (H H6).
      specialize (H Γ' ξ H1). replace (VVal VNil) with (rename ξ (VVal VNil)) by auto.
      rewrite map_nth. assumption.
    - intros. constructor. intros. specialize (H i H1). 
      specialize (H Γ). destruct H.
      apply H2. intros. specialize (H0 Γ' ξ). specialize (H0 H3).
      inversion H0. subst. rewrite map_length in H6. specialize (H6 i H1).
      replace (VVal VNil) with (rename ξ (VVal VNil)) in H6 by auto.
      now rewrite map_nth in H6.
  * intros. split.
    - intros. simpl. constructor.
      + specialize (H Γ). destruct H. inversion H1. subst.
        specialize (H H7 Γ' ξ H2). assumption.
      + specialize (H0 Γ). destruct H0. inversion H1. subst.
        specialize (H0 H8 Γ' ξ H2). assumption.
    - intros. constructor.
      + specialize (H Γ). destruct H. apply H2. intros. specialize (H1 Γ' ξ H3).
        inversion H1. now subst.
      + specialize (H0 Γ). destruct H0. apply H2. intros. specialize (H1 Γ' ξ H3).
        inversion H1. now subst.
  * intros. split.
    - intros. simpl. constructor. intros. rewrite map_length in H2.
      replace (VVal VNil) with (rename ξ (VVal VNil)) by auto. rewrite map_nth.
      specialize (H i H2 Γ). destruct H. inversion H0. subst.
      specialize (H6 i H2). specialize (H H6 Γ' ξ H1). assumption.
    - intros. constructor. intros. specialize (H i H1 Γ).
      destruct H. apply H2. intros. specialize (H0 Γ' ξ H3). inversion H0. subst.
      rewrite map_length in H6. specialize (H6 i H1).
      replace (VVal VNil) with (rename ξ (VVal VNil)) in H6 by auto.
      now rewrite map_nth in H6.
  * intros. split.
    - intros. simpl. constructor.
      + intros. rewrite map_length in H2. specialize (H i H2 ). destruct H.
        specialize (H Γ). destruct H. inversion H0. subst. specialize (H6 i H2).
        specialize (H H6 Γ' ξ H1). rewrite <- map_nth in H.
        replace (nth i (map fst (map (fun '(x, y) => (rename ξ x, rename ξ y)) l)) 
        (VVal VNil)) with (nth i (map (rename ξ) (map fst l)) (rename ξ (VVal VNil))).
        ** assumption.
        ** f_equal. rewrite map_map. rewrite map_map. f_equal. 
           apply functional_extensionality. intros x. destruct x. simpl. auto.
      + intros. rewrite map_length in H2. specialize (H i H2 ). destruct H.
        specialize (H3 Γ). destruct H3. inversion H0. subst. specialize (H8 i H2).
        specialize (H3 H8 Γ' ξ H1). rewrite <- map_nth in H3.
        replace (nth i (map snd (map (fun '(x, y) => (rename ξ x, rename ξ y)) l)) 
        (VVal VNil)) with (nth i (map (rename ξ) (map snd l)) (rename ξ (VVal VNil))).
        ** assumption.
        ** f_equal. rewrite map_map. rewrite map_map. f_equal.
           apply functional_extensionality. intros x. destruct x. simpl. auto.
    - intros. constructor.
      + intros. specialize (H i H1). destruct H. specialize (H Γ). destruct H.
        apply H3. intros. specialize (H0 Γ' ξ H4). inversion H0. subst.
        rewrite map_length in H6. specialize (H6 i H1). rewrite <- map_nth.
        replace (nth i (map fst (map (fun '(x, y) => (rename ξ x, rename ξ y)) l)) 
        (VVal VNil)) with (nth i (map (rename ξ) (map fst l)) (rename ξ (VVal VNil)))
        in H6.
        ** assumption.
        ** f_equal. rewrite map_map. rewrite map_map. f_equal. 
           apply functional_extensionality. intros x. destruct x. simpl. auto.
      + intros. specialize (H i H1). destruct H. specialize (H2 Γ). destruct H2.
        apply H3. intros. specialize (H0 Γ' ξ H4). inversion H0. subst.
        rewrite map_length in H8. specialize (H8 i H1). rewrite <- map_nth.
        replace (nth i (map snd (map (fun '(x, y) => (rename ξ x, rename ξ y)) l)) 
        (VVal VNil)) with (nth i (map (rename ξ) (map snd l)) (rename ξ (VVal VNil)))
        in H8.
        ** assumption.
        ** f_equal. rewrite map_map. rewrite map_map. f_equal. 
           apply functional_extensionality. intros x. destruct x. simpl. auto.
  * intros. split.
    - intros. simpl. constructor. intros. rewrite map_length in H2.
      specialize (H i H2 Γ). destruct H. inversion H0.
      subst. specialize (H6 i H2). specialize (H H6 Γ' ξ H1).
      replace (VVal VNil) with (rename ξ (VVal VNil)) by auto. rewrite map_nth.
      assumption.
    - intros. constructor. intros. specialize (H i H1 Γ).
      destruct H. apply H2. intros. specialize (H0 Γ' ξ H3). inversion H0. subst.
      rewrite map_length in H6. specialize (H6 i H1).
      replace (VVal VNil) with (rename ξ (VVal VNil)) in H6 by auto.
      now rewrite map_nth in H6.
  * intros. split.
    - intros. simpl. constructor. intros. rewrite map_length in H2.
      specialize (H i H2 Γ). destruct H. inversion H0. subst.
      specialize (H6 i H2). specialize (H H6 Γ' ξ H1).
      replace (VVal VNil) with (rename ξ (VVal VNil)) by auto. rewrite map_nth.
      assumption.
    - intros. constructor. intros. specialize (H i H1 Γ).
      destruct H. apply H2. intros. specialize (H0 Γ' ξ H3). inversion H0. subst.
      rewrite map_length in H6. specialize (H6 i H1).
      replace (VVal VNil) with (rename ξ (VVal VNil)) in H6 by auto.
      rewrite map_nth in H6. assumption.
  * intros. split.
    - intros. simpl. constructor.
      + specialize (H Γ). destruct H. apply H.
        ** inversion H1. now subst.
        ** assumption.
      + intros. rewrite map_length in H3.
        replace (VVal VNil) with (rename ξ (VVal VNil)) by auto. rewrite map_nth.
        specialize (H0 i H3 Γ). destruct H0. apply H0.
        ** inversion H1. subst. specialize (H9 i H3). assumption.
        ** assumption.
    - intros. constructor.
      + specialize (H Γ). destruct H. apply H2. intros. specialize (H1 Γ' ξ H3).
        inversion H1. now subst.
      + intros. specialize (H0 i H2 Γ). destruct H0.
        apply H3. intros. specialize (H1 Γ' ξ H4). inversion H1. subst.
        rewrite map_length in H9. specialize (H9 i H2).
        replace (VVal VNil) with (rename ξ (VVal VNil)) in H9 by auto.
        rewrite map_nth in H9. assumption.
  * intros. split.
    - intros. simpl. constructor.
      + specialize (H Γ). destruct H. apply H.
        ** inversion H1. subst. assumption.
        ** assumption.
      + intros. rewrite map_length in H3.
        (* Trying to get it from H0*)
        specialize (H0 i H3). destruct H0. (* Still need the H0 not H4*) clear H4 H.
        specialize (H0 (PatListScope (nth i (map (fst >>> fst) l) nil) + Γ)). 
        destruct H0. (*only H will be needed*) clear H0.
        inversion H1. subst.
        clear H8. specialize (H7 i H3). specialize (H H7).
        specialize (H (PatListScope (nth i (map (fst >>> fst) l) nil) + Γ') (uprenn
        (PatListScope (nth i (map (fst >>> fst) l) nil)) ξ)).
        pose proof uprenn_scope as H0.
        specialize (H0 (PatListScope (nth i (map (fst >>> fst) l) nil)) Γ Γ' ξ H2).
        specialize (H H0). clear H0 H2.
        (* Try to simplify H here*)
        remember (fun x : list Pat * Exp * Exp => (fst >>> fst) x) as Fff.
        remember (fun x : list Pat * Exp * Exp => (fst >>> snd) x) as Fsf.
        replace nil with (Fff (nil, VVal VNil, VVal VNil)) in H by (subst; auto).
        rewrite map_nth in H. 
        replace (VVal VNil) with (Fsf (nil, VVal VNil, VVal VNil)) in H by (subst; auto).
        rewrite map_nth in H. subst. simpl in *.
        (* Try to simplify the goal here*)
        do 2 rewrite map_map. 
        remember (fun x : list Pat * Exp * Exp =>
        (fst >>> fst)
          (let
           '(y0, y) := x in
            let
            '(p, x0) := y0 in
             (p, rename (uprenn (PatListScope p) ξ) x0,
             rename (uprenn (PatListScope p) ξ) y))) as FFF.
        remember (fun x : list Pat * Exp * Exp =>
        (fst >>> snd)
          (let
           '(y0, y) := x in
            let
            '(p, x0) := y0 in
             (p, rename (uprenn (PatListScope p) ξ) x0,
             rename (uprenn (PatListScope p) ξ) y))) as FSF.
        replace nil with (FFF (nil, VVal VNil, VVal VNil)) by (subst;auto).
        rewrite map_nth.
        replace (VVal VNil) with
        (FSF (nil, VVal VNil, VVal VNil)) by (subst;auto).
        rewrite map_nth.
        (* replace then solw eq *)
        cbn in H.
        replace ((fst >>> fst) (nth i l (nil, VVal VNil, VVal VNil))) with
        (FFF (nth i l (nil, FSF (nil, VVal VNil, VVal VNil), FSF (nil, VVal VNil, VVal VNil))))
        in H.
        ** replace (rename (uprenn (PatListScope (FFF (nth i l
           (nil, FSF (nil, VVal VNil, VVal VNil), FSF (nil, VVal VNil, VVal VNil))))) ξ)
           ((snd ∘ fst) (nth i l (nil, VVal VNil, VVal VNil)))) with
           (FSF (nth i l (nil, VVal VNil, VVal VNil))) in H.
           -- subst FFF. assumption.
           -- clear H. subst. cbn. destruct (nth i l (nil, VVal VNil, VVal VNil)).
              destruct p. cbn. reflexivity.
        ** clear H. subst. cbn. destruct (nth i l (nil, VVal VNil, VVal VNil)).
           destruct p. simpl. reflexivity.
      + intros. rewrite map_length in H3. clear H. specialize (H0 i H3).
        destruct H0. clear H. inversion H1. subst.
        specialize (H8 i H3). clear H1 H3.
        specialize (H0 (PatListScope (nth i (map (fst >>> fst) l) nil) + Γ)).
        destruct H0. clear H0. specialize (H H8).
        specialize (H (PatListScope (nth i (map (fst >>> fst) l) nil) + Γ')).
        pose proof uprenn_scope.
        specialize (H0 (PatListScope (nth i (map (fst >>> fst) l) nil)) Γ Γ' ξ H2).
        specialize (H (uprenn (PatListScope (nth i (map (fst >>> fst) l) nil)) ξ)).
        specialize (H H0).
        remember (fun x : list Pat * Exp * Exp => (fst >>> fst) x) as Fff.
        replace nil with (Fff (nil, VVal VNil, VVal VNil)) in H by (subst;auto).
        replace (VVal VNil) with (snd (nil:(list Pat), VVal VNil, VVal VNil)) in H by auto.
        do 2 rewrite map_nth in H.
        do 2 rewrite map_map.
        remember (fun x : list Pat * Exp * Exp =>
        Fff
          (let
           '(y0, y) := x in
            let
            '(p, x0) := y0 in
             (p, rename (uprenn (PatListScope p) ξ) x0,
             rename (uprenn (PatListScope p) ξ) y))) as FFF.
        remember (fun x : list Pat * Exp * Exp =>
        snd
          (let
           '(y0, y) := x in
            let
            '(p, x0) := y0 in
             (p, rename (uprenn (PatListScope p) ξ) x0,
             rename (uprenn (PatListScope p) ξ) y))) as FS.
        replace nil with (FFF (nil, VVal VNil, VVal VNil)) by (subst;auto).
        replace (VVal VNil) with (FS (nil, VVal VNil, VVal VNil)) by (subst;auto).
        do 2 rewrite map_nth.
        replace (Fff (nth i l (nil:(list Pat), snd (nil:(list Pat), 
        VVal VNil, VVal VNil), snd (nil:(list Pat), VVal VNil, VVal VNil)))) 
        with (FFF (nth i l (nil:(list Pat), FS (nil:(list Pat), VVal VNil, VVal VNil),
        FS (nil:(list Pat), VVal VNil, VVal VNil)))) in H.
        ** replace (rename (uprenn (PatListScope (FFF (nth i l
           (nil, FS (nil, VVal VNil, VVal VNil), FS (nil, VVal VNil, VVal VNil))))) ξ)
           (snd (nth i l (nil, VVal VNil, VVal VNil)))) with
           (FS (nth i l (nil, VVal VNil, VVal VNil))) in H.
           -- assumption.
           -- clear H. subst. simpl. destruct (nth i l (nil, VVal VNil, VVal VNil)).
              destruct p. simpl. reflexivity.
        ** clear H. subst. simpl. destruct (nth i l (nil, VVal VNil, VVal VNil)).
           destruct p. simpl. reflexivity.
    - intros. specialize (H1 Γ id). specialize (H1 (renscope_id Γ)).
      inversion H1. subst. pose proof idrenaming_is_id as [_ [H8 _]].
      rewrite H8 in H1. assumption.
  * intros. split.
    - intros. simpl. constructor.
      + specialize (H Γ). destruct H. inversion H1. subst. 
        specialize (H H7 Γ' ξ H2). assumption.
      + specialize (H0 (l + Γ)). destruct H0. inversion H1. subst. 
        specialize (H0 H9 (l + Γ') (uprenn l ξ)). pose proof uprenn_scope.
        specialize (H4 l Γ Γ' ξ H2). specialize (H0 H4). assumption.
    - intros. specialize (H1 Γ id). specialize (H1 (renscope_id Γ)).
      inversion H1. subst. rewrite idrenaming_upn in H7.
      pose proof idrenaming_is_id as [H8 [_ _]].
      rewrite H8 in H7. rewrite H8 in H5. now constructor.
  * intros. split.
    - intros. simpl. constructor.
      + specialize (H Γ). destruct H. inversion H1. subst.
        specialize (H H7 Γ' ξ H2). assumption.
      + specialize (H0 Γ). destruct H0. inversion H1. subst.
        specialize (H0 H8 Γ' ξ H2). assumption.
    - intros. constructor.
      + specialize (H Γ). destruct H. apply H2. intros. specialize (H1 Γ' ξ H3).
        inversion H1. now subst.
      + specialize (H0 Γ). destruct H0. apply H2. intros. specialize (H1 Γ' ξ H3).
        inversion H1. now subst.
  * intros. split.
    - intros. simpl. constructor.
      + intros. rewrite map_length in H3. clear H. specialize (H0 i H3).
        inversion H1. subst. specialize (H6 i H3).
        specialize (H0 (Datatypes.length l + nth i (map fst l) 0 + Γ)).
        destruct H0. clear H0 H1 H3. specialize (H H6). clear H6.
        pose proof uprenn_scope.
        specialize (H0 (Datatypes.length l + nth i (map fst l) 0) Γ Γ' ξ H2).
        clear H2 H7. specialize (H (Datatypes.length l + nth i (map fst l) 0 + Γ') 
        (uprenn (Datatypes.length l + nth i (map fst l) 0) ξ)). specialize (H H0).
        clear H0. replace 0 with (fst (0,VVal VNil)) in H by auto.
        replace (VVal VNil) with (snd (0, VVal VNil)) in H by auto.
        do 2 rewrite map_nth in H. simpl in *. rewrite map_length.
        do 2 rewrite map_map.
        remember (fun x : nat * Exp =>
          fst
            (let
             '(n, x0) := x in
              (n, rename (uprenn (Datatypes.length l + n) ξ) x0))) as FF.
        remember (fun x : nat * Exp =>
        snd
          (let
           '(n, x0) := x in
            (n, rename (uprenn (Datatypes.length l + n) ξ) x0))) as FS.
        replace 0 with (FF (0, VVal VNil)) by (subst;auto).
        replace (VVal VNil) with (FS (0, VVal VNil)) by (subst;auto).
        do 2 rewrite map_nth. replace (FF (nth i l (0, FS (0, VVal VNil))))
        with (fst (nth i l (0, VVal VNil))).
        ** replace (FS (nth i l (0, VVal VNil))) with
           (rename (uprenn (Datatypes.length l + fst (nth i l (0, VVal VNil))) ξ)
           (snd (nth i l (0, VVal VNil)))).
           -- assumption.
           -- clear H. subst. simpl. destruct (nth i l (0, VVal VNil)).
              simpl. reflexivity.
        ** clear H. subst. simpl. destruct (nth i l (0, VVal VNil)).
           simpl. reflexivity.
      + inversion H1. subst. rewrite map_length. clear H0 H1.
        specialize (H ((Datatypes.length l) + Γ)). destruct H. clear H0.
        specialize (H H7). pose proof uprenn_scope.
        specialize (H0 (Datatypes.length l) Γ Γ' ξ H2). clear H2 H7.
        specialize (H (Datatypes.length l + Γ') (uprenn (Datatypes.length l) ξ)).
        specialize (H H0). clear H0. assumption.
    - intros. specialize (H1 Γ id (renscope_id Γ)).
      pose proof idrenaming_is_id as [_ [H2 _]]. rewrite H2 in H1. assumption.
  * intros. split.
    - intros. simpl. constructor.
      + specialize (H Γ). destruct H. inversion H2. subst. 
        specialize (H H9 Γ' ξ H3). assumption.
      + specialize (H0 (vl1 + Γ)). destruct H0. inversion H2. subst. 
        specialize (H0 H12 (vl1 + Γ') (uprenn vl1 ξ)). pose proof uprenn_scope.
        specialize (H5 vl1 Γ Γ' ξ H3). specialize (H0 H5). assumption.
      + specialize (H1 (vl2 + Γ)). destruct H1. inversion H2. subst. 
        specialize (H1 H13 (vl2 + Γ') (uprenn vl2 ξ)). pose proof uprenn_scope.
        specialize (H5 vl2 Γ Γ' ξ H3). specialize (H1 H5). assumption.
    - intros. specialize (H2 Γ id). specialize (H2 (renscope_id Γ)).
      inversion H2. subst. rewrite idrenaming_upn in H10, H11.
      pose proof idrenaming_is_id as [H12 [_ _]].
      rewrite H12 in H7, H10, H11. now constructor.
  * intros. inversion H.
  * intros. split.
    - intros. destruct i.
      + simpl. specialize (H Γ). destruct H. apply H.
        ** auto.
        ** auto.
      + simpl. simpl in H1. specialize (H0 i ltac:(lia) Γ). destruct H0. apply H0.
        ** simpl in H2. assumption.
        ** assumption.
    - intros. specialize (H2 Γ id). specialize (H2 (renscope_id Γ)).
      pose proof idrenaming_is_id as [H3 [_ _]]. rewrite H3 in H2. assumption.
  * apply Forall_nil.
  * intros. rewrite indexed_to_forall with (def := VNil). 
    rewrite indexed_to_forall with (def := VNil) in H0. intros. destruct i.
    - simpl. specialize (H Γ). assumption.
    - simpl in *. specialize (H0 i ltac:(slia) Γ). assumption.
  * intros. split.
    - intros. destruct i.
      + simpl. specialize (H Γ). assumption.
      + simpl in *. pose proof Nat.succ_lt_mono. 
        specialize (H1 i ltac:(slia)). destruct H1. specialize (H1 Γ).
        assumption.
    - intros. destruct i.
      + simpl. specialize (H0 Γ). assumption.
      + simpl in *. pose proof Nat.succ_lt_mono.
        specialize (H1 i ltac:(slia)). destruct H1. specialize (H4 Γ).
        assumption.
  * intros. split.
    - intros. destruct i.
      + simpl. specialize (H Γ). assumption.
      + simpl in *. specialize (H1 i ltac:(slia)). destruct H1. specialize (H1 Γ).
        assumption.
    - intros. destruct i.
      + simpl. specialize (H0 Γ). assumption.
      + simpl in *. specialize (H1 i ltac:(slia)). destruct H1. specialize (H3 Γ).
        assumption.
  * intros. inversion H.
  * intros. split.
    - intros. destruct i.
      + simpl in *. specialize (H Γ). destruct H. specialize (H H2 Γ' ξ H3).
        assumption.
      + simpl in *. specialize (H0 i ltac:(slia) Γ). destruct H0.
        specialize (H0 H2 Γ' ξ H3). assumption.
    - intros. specialize (H2 Γ id). specialize (H2 (renscope_id Γ)).
      pose proof idrenaming_is_id as [H3 [_ _]]. rewrite H3 in H2. assumption.
  * intros. split.
    - intros. simpl in H2. destruct i.
      + simpl. specialize (H Γ). assumption.
      + simpl. specialize (H1 i ltac:(slia)). destruct H1.
        specialize (H1 Γ). assumption.
    - intros. simpl in H2. destruct i.
      + simpl. specialize (H0 Γ). assumption.
      + simpl. specialize (H1 i ltac:(slia)). destruct H1.
        specialize (H3 Γ). assumption.
  * intros. inversion H.
  * intros. destruct i.
    - simpl. specialize (H Γ). assumption.
    - simpl in *. specialize (H0 i ltac:(slia) Γ). assumption.
Qed.

(** This corollary is the projection of the previous one for expressions. *)
Corollary ren_preserves_scope_exp : forall Γ e,
    (EXP Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       EXP Γ' ⊢ rename ξ e).
Proof.
  intros.
  apply ren_preserves_scope.
Qed.

(** This corollary is the projection of the previous one for values. *)
Corollary ren_preserves_scope_val : forall Γ e,
    (VAL Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       VAL Γ' ⊢ renameVal ξ e).
Proof.
  intros.
  apply ren_preserves_scope.
Qed.

(** This corollary is the projection of the previous one for non-values. *)
Corollary ren_preserves_scope_nval : forall Γ e,
    (NVAL Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       NVAL Γ' ⊢ renameNonVal ξ e).
Proof.
  intros.
  apply ren_preserves_scope.
Qed.

Lemma up_val : forall Γ v (ξ : Substitution),
  match ξ v with
  | inl exp => VAL Γ ⊢ exp
  | inr num => num < Γ
  end ->
  match up_subst ξ (S v) with
  | inl exp => VAL S Γ ⊢ exp
  | inr num => num < S Γ
  end.
Proof.
  intros. unfold up_subst.
  break_match_hyp.
  * unfold shift. rewrite Heqs. apply -> ren_preserves_scope_val; eauto.
    intro. intros. lia.
  * unfold shift. rewrite Heqs. lia.
Qed.

Lemma up_scope : forall Γ Γ' ξ,
  SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
  SUBSCOPE (S Γ) ⊢ up_subst ξ ∷ (S Γ').
Proof.
  intros.
  unfold subscoped in *.
  intros.
  destruct x; intros.
  * simpl. lia.
  * simpl. unfold shift. break_match_goal. break_match_hyp.
    - inversion Heqs. eapply ren_preserves_scope_val with (Γ:= Γ'); eauto.
      + epose (H x _). rewrite Heqs0 in y. auto. Unshelve. lia.
      + intro. intros. lia.
    - inversion Heqs.
    - break_match_hyp.
      + inversion Heqs.
      + inversion Heqs. subst. epose (H x _). rewrite Heqs0 in y. lia. Unshelve. lia.
Qed.

Global Hint Resolve up_scope : core.

Lemma upn_scope : forall n Γ Γ' ξ,
  SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
  SUBSCOPE (n + Γ) ⊢ upn n ξ ∷ (n + Γ').
Proof.
  induction n; intros.
  * repeat rewrite Nat.add_0_l. apply H.
  * repeat rewrite Nat.add_succ_l. apply up_scope. apply IHn. auto.
Qed.

Global Hint Resolve upn_scope : core.

Lemma cons_scope : forall v Γ Γ' ξ,
    VAL Γ' ⊢ v ->
    SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
    SUBSCOPE (S Γ) ⊢ v.:ξ ∷ Γ'.
Proof.
  intros.
  unfold subscoped in *.
  intros. destruct x.
  * simpl. auto.
  * simpl. apply H0. lia.
Qed.


Lemma consn_scope : forall (vals : list Val) Γ Γ' (ξ : Substitution),
    Forall (fun v => VAL Γ' ⊢ v) vals ->
    SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
    SUBSCOPE length vals + Γ ⊢ fold_right (fun v acc => v .: acc) ξ vals ∷ Γ'.
Proof.
  induction vals; intros.
  * simpl. auto.
  * simpl. inversion H. apply cons_scope; auto.
Qed.

Corollary vclosed_ignores_ren v ρ:
  VALCLOSED v ->
  renameVal ρ v = v.
Proof.
  intros. rewrite (proj2 (proj2 renaming_is_subst)).
  now apply vclosed_ignores_sub.
Qed.

Global Hint Resolve cons_scope : core.
Global Hint Resolve consn_scope : core.

Lemma subst_preserves_scope :
    (forall e Γ, EXP Γ ⊢ e <->
     forall Γ' ξ,
       SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
       EXP Γ' ⊢ e.[ξ]) /\
       
     (forall e Γ, NVAL Γ ⊢ e <->
     forall Γ' ξ,
       SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
       NVAL Γ' ⊢ e.[ξ]ₑ) /\
       
    (forall e Γ, VAL Γ ⊢ e <->
     forall Γ' ξ,
       SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
       VAL Γ' ⊢ e.[ξ]ᵥ).
Proof.
  eapply Exp_ind with
  (QV := fun l => forall i, i < length l -> (forall Γ, VAL Γ ⊢ (nth i l VNil) <-> forall Γ' ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> VAL Γ' ⊢ (nth i l VNil) .[ξ]ᵥ))
  (RV := fun l => forall i, i < length l -> (forall Γ, VAL Γ ⊢ (nth i (map fst l) VNil) <-> forall Γ' ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> VAL Γ' ⊢ (nth i (map fst l) VNil) .[ξ]ᵥ) /\
					  (forall Γ, VAL Γ ⊢ (nth i (map snd l) VNil) <-> forall Γ' ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> VAL Γ' ⊢ (nth i (map snd l) VNil) .[ξ]ᵥ))
  (VV := fun l =>  forall i, i < length l ->  (forall Γ, EXP Γ ⊢ (nth i (map snd l) (VVal VNil)) <-> forall Γ' ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ (nth i (map snd l) (VVal VNil)).[ξ]))
  (Q := fun l => forall i, i < length l -> (forall Γ, EXP Γ ⊢ (nth i l (VVal VNil)) <-> forall Γ' ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ (nth i l (VVal VNil)).[ξ]))
  (R := fun l => forall i, i < length l -> (forall Γ, EXP Γ ⊢ (nth i (map fst l) (VVal VNil)) <-> forall Γ' ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ (nth i (map fst l) (VVal VNil)) .[ξ]) /\
					 (forall Γ, EXP Γ ⊢ (nth i (map snd l) (VVal VNil)) <-> forall Γ' ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ (nth i (map snd l) (VVal VNil)) .[ξ]))
  (W := fun l => forall i, i < length l -> (forall Γ, EXP Γ ⊢ (nth i (map (fst >>> snd) l) (VVal VNil)) <-> forall Γ' ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ (nth i (map (fst >>> snd) l) (VVal VNil)) .[ξ]) /\
					 (forall Γ, EXP Γ ⊢ (nth i (map snd l) (VVal VNil)) <-> forall Γ' ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ (nth i (map snd l) (VVal VNil)) .[ξ]))
  (Z := fun l =>  forall i, i < length l ->  (forall Γ, EXP Γ ⊢ (nth i (map snd l) (VVal VNil)) <-> forall Γ' ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ (nth i (map snd l) (VVal VNil)).[ξ]))
  .
  * intros. split.
    - specialize (H Γ). destruct H. intros. simpl. constructor. apply H.
      + inversion H1. subst. assumption.
      + assumption.
    - intros. specialize (H Γ). destruct H. constructor. apply H1. intros.
      specialize (H0 _ _ H2). simpl in H0. inversion H0. subst. assumption.
  * intros. split.
    - intros. inversion H0. subst. specialize (H Γ). inversion H. simpl. constructor.
      destruct H. specialize (H H4 Γ' ξ H1). assumption.
    - intros. constructor. specialize (H Γ). destruct H. apply H1. intros.
      specialize (H0 Γ' ξ H2). inversion H0. subst. assumption.
  * intros. split.
    - intros. simpl. constructor.
    - intros. constructor.
  * intros. split.
    - intros. simpl. constructor.
    - intros. constructor.
  * intros. split.
    - intros. simpl. constructor.
      + specialize (H Γ). destruct H. clear H3 H0. inversion H1. subst.
        specialize (H H5 Γ' ξ H2). assumption.
      + specialize (H0 Γ). destruct H0. clear H H3. inversion H1. subst.
        specialize (H0 H6 Γ' ξ H2). assumption.
    - intros. constructor.
      + clear H0. specialize (H Γ). destruct H. clear H. apply H0.
        intros. specialize (H1 Γ' ξ H). inversion H1. subst. assumption.
      + clear H. specialize (H0 Γ). destruct H0. clear H. apply H0.
        intros. specialize (H1 Γ' ξ H). inversion H1. subst. assumption.
  * intros. split.
    - intros. simpl. constructor. intros. rewrite map_length in H2.
      specialize (H i H2 Γ). destruct H. clear H3. inversion H0.
      subst. specialize (H5 i H2). specialize (H H5 Γ' ξ H1).
      clear H0 H1 H2 H5. replace VNil with (VNil.[ξ]ᵥ) by auto.
      rewrite map_nth. assumption.
    - clear H. intros. specialize (H Γ idsubst). specialize (H (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [_ H0]]. rewrite H0 in H. assumption.
  * intros. split.
    - intros. simpl. constructor.
      + intros. rewrite map_length in H2. specialize (H i H2).
        destruct H. clear H3. specialize (H Γ). destruct H. clear H3.
        inversion H0. subst. specialize (H4 i H2).
        specialize (H H4 Γ' ξ H1). clear H0 H1 H2 H4. rewrite map_map.
        remember (fun x : Val * Val =>
        fst (let '(x0, y) := x in (x0.[ξ]ᵥ, y.[ξ]ᵥ))) as FF.
        replace VNil with (FF (VNil,VNil)) by (subst;auto).
        rewrite map_nth. replace VNil with (fst (VNil,VNil)) in H by auto.
        rewrite map_nth in H. replace (FF (nth i l (VNil, VNil))) with 
        ((fst (nth i l (VNil, VNil))).[ξ]ᵥ).
        ** assumption.
        ** subst. destruct (nth i l (VNil, VNil)). simpl. reflexivity.
      + intros. rewrite map_length in H2. specialize (H i H2).
        destruct H. clear H. specialize (H3 Γ). destruct H3. clear H3.
        inversion H0. subst. clear H4. specialize (H6 i H2).
        specialize (H H6 Γ' ξ H1). clear H0 H1 H2 H6. rewrite map_map.
        remember ((fun x : Val * Val =>
        snd (let '(x0, y) := x in (x0.[ξ]ᵥ, y.[ξ]ᵥ)))) as FS.
        replace VNil with (FS (VNil,VNil)) by (subst;auto).
        rewrite map_nth. replace VNil with (snd (VNil,VNil)) in H by auto.
        rewrite map_nth in H. replace (FS (nth i l (VNil, VNil))) with 
        ((snd (nth i l (VNil, VNil))).[ξ]ᵥ).
        ** assumption.
        ** subst. destruct (nth i l (VNil, VNil)). simpl. reflexivity.
    - clear H. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [_ H0]]. rewrite H0 in H. assumption.
  * intros. split.
    (*- intros. simpl. inversion H. subst. constructor. auto.*)
    - intros. inversion H. subst. simpl. unfold subscoped in H0. apply H0 in H3.
      destruct (ξ n).
      + assumption.
      + constructor. assumption.
    - intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [_ H0]]. rewrite H0 in H. assumption.
  * intros. split.
    - intros. inversion H. subst. simpl. unfold subscoped in H0. apply H0 in H3.
      destruct n. simpl in *. destruct (ξ n).
      + assumption.
      + constructor. assumption.
    - intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [_ H0]]. rewrite H0 in H. assumption.
  * intros. split.
    - intros. simpl. constructor.
      + do 2 rewrite map_map. intros. rewrite map_length in H3.
        inversion H1. subst. specialize (H7 i H3).
        specialize (H i H3 (Datatypes.length ext + nth i (map (snd ∘ fst) ext) 0 + Γ)).
        destruct H. clear H4. specialize (H H7 (Datatypes.length ext + nth i (map (fst >>> snd)
        ext) 0 + Γ')). pose proof upn_scope. specialize (H4 (Datatypes.length ext + 
        nth i (map (snd ∘ fst) ext) 0) Γ Γ' ξ H2). specialize (H (upn
        (Datatypes.length ext + nth i (map (snd ∘ fst) ext) 0) ξ) H4).
        clear H0 H1 H2 H3 H7 H10 H4. rewrite map_length.
        remember (fun x : nat * nat * Exp => (snd ∘ fst) x) as Fsf.
        replace 0 with (Fsf (0,0,VVal VNil)) in H by (subst;auto). rewrite map_nth in H.
        replace (VVal VNil) with (snd (0,0,VVal VNil))in H by auto. rewrite map_nth in H.
        simpl in *. remember (fun x : nat * nat * Exp =>
        Fsf
          (let
           '(y, x0) := x in
            let
            '(i0, ls) := y in
             (i0, ls, x0.[upn (Datatypes.length ext + ls) ξ]))) as FSF.
        replace 0 with (FSF (0,0,VVal VNil)) by (subst;auto). rewrite map_nth.
        remember (fun x : nat * nat * Exp => snd (let '(i0, ls, x0) := x in
        (i0, ls, x0.[upn (Datatypes.length ext + ls) ξ]))) as FS.
        replace (VVal VNil) with (FS (0,0,VVal VNil)) by (subst;auto).
        rewrite map_nth. replace (FSF (nth i ext (0, 0, FS (0, 0, VVal VNil)))) with
        (Fsf (nth i ext (0, 0, VVal VNil))).
        ** replace (FS (nth i ext (0, 0, VVal VNil))) with 
           ((snd (nth i ext (0, 0, VVal VNil))).[upn (Datatypes.length ext +
           Fsf (nth i ext (0, 0, VVal VNil))) ξ]).
           -- assumption.
           -- clear H. subst. destruct (nth i ext (0, 0, VVal VNil)). simpl.
              destruct p. simpl. reflexivity.
        ** clear H. subst. simpl. destruct (nth i ext (0, 0, VVal VNil)). simpl. destruct p.
           simpl. reflexivity.
      + rewrite map_length. clear H. specialize (H0 (Datatypes.length ext + vl + Γ)).
        destruct H0. clear H0. inversion H1. subst. specialize (H H8).
        pose proof upn_scope. specialize (H0 (Datatypes.length ext + vl) Γ Γ' ξ H2).
        specialize (H (Datatypes.length ext + vl + Γ') (upn (Datatypes.length ext + vl) ξ)).
        specialize (H H0). assumption.
    - clear H H0. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [_ H0]]. rewrite H0 in H. assumption.
  * intros. split.
    - intros. simpl. constructor. specialize (H (n + Γ)). destruct H.
      clear H2. inversion H0. subst. specialize (H H4 (n + Γ') (upn n ξ)).
      pose proof upn_scope. specialize (H2 n Γ Γ' ξ H1). specialize (H H2).
      assumption.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. assumption.
  * intros. split.
    - intros. simpl. constructor. intros. rewrite map_length in H2.
      specialize (H i H2 Γ). destruct H. clear H3. inversion H0. subst.
      specialize (H5 i H2). specialize (H H5 Γ' ξ H1).
      replace (VVal VNil) with ((VVal VNil).[ξ]) by auto. rewrite map_nth.
      assumption.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. assumption.
  * intros. split.
    - intros. simpl. constructor.
      + clear H0. inversion H1. subst. specialize (H Γ). destruct H.
        clear H0 H1 H6. specialize (H H5 Γ' ξ H2). assumption.
      + clear H. inversion H1. subst. specialize (H0 Γ). destruct H0.
        clear H0 H1 H5. specialize (H H6 Γ' ξ H2). assumption.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. assumption.
  * intros. split.
    - intros. simpl. constructor. intros. rewrite map_length in H2.
      specialize (H i H2 Γ). destruct H. clear H3. inversion H0. subst.
      specialize (H5 i H2). specialize (H H5 Γ' ξ H1).
      replace (VVal VNil) with ((VVal VNil).[ξ]) by auto. rewrite map_nth.
      assumption.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. assumption.
  * intros. split.
    - intros. simpl. constructor.
      + intros. rewrite map_length in H2. specialize (H i H2). destruct H.
        clear H3. specialize (H Γ). destruct H. clear H3. inversion H0. subst.
        specialize (H4 i H2 ). specialize (H H4 Γ' ξ H1).
        replace (VVal VNil) with (fst (VVal VNil,VVal VNil)) in H by auto.
        rewrite map_nth in H. rewrite map_map. remember (fun x : Exp * Exp =>
        fst (let '(x0, y) := x in (x0.[ξ], y.[ξ]))) as FF. replace (VVal VNil) with
        (FF (VVal VNil,VVal VNil)) by (subst;auto). rewrite map_nth. replace
        (FF (nth i l (VVal VNil, VVal VNil))) with ((fst (nth i l (VVal VNil, VVal VNil))).[ξ]).
        ** assumption.
        ** subst. clear. destruct (nth i l (VVal VNil, VVal VNil)). simpl. reflexivity.
      + intros. rewrite map_length in H2. specialize (H i H2). destruct H.
        clear H. specialize (H3 Γ). destruct H3. clear H3. inversion H0. subst.
        clear H4. specialize (H6 i H2). specialize (H H6 Γ' ξ H1).
        replace (VVal VNil) with (snd (VVal VNil,VVal VNil)) in H by auto.
        rewrite map_nth in H. rewrite map_map. remember (fun x : Exp * Exp =>
        snd (let '(x0, y) := x in (x0.[ξ], y.[ξ]))) as FS. replace (VVal VNil) with
        (FS (VVal VNil,VVal VNil)) by (subst;auto). rewrite map_nth. replace
        (FS (nth i l (VVal VNil, VVal VNil))) with ((snd (nth i l (VVal VNil, VVal VNil))).[ξ]).
        ** assumption.
        ** subst. clear. destruct (nth i l (VVal VNil, VVal VNil)). simpl. reflexivity.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. assumption.
  * intros. split.
    - intros. simpl. constructor. intros. rewrite map_length in H2.
      specialize (H i H2 Γ). destruct H. clear H3. inversion H0. subst.
      specialize (H5 i H2). specialize (H H5 Γ' ξ H1).
      replace (VVal VNil) with ((VVal VNil).[ξ]) by auto. rewrite map_nth. assumption.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. assumption.
  * intros. split.
    - intros. simpl. constructor. intros. rewrite map_length in H2.
      specialize (H i H2 Γ). destruct H. clear H3. inversion H0. subst.
      specialize (H5 i H2). specialize (H H5 Γ' ξ H1).
      replace (VVal VNil) with ((VVal VNil).[ξ]) by auto. rewrite map_nth. assumption.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. assumption.
  * intros. split.
    - intros. simpl. constructor.
      + inversion H1. subst. specialize (H Γ). destruct H. clear H3.
        specialize (H H6 Γ' ξ H2). assumption.
      + intros. rewrite map_length in H3. clear H. inversion H1. subst. 
        specialize (H7 i H3). specialize (H0 i H3 Γ). destruct H0. clear H0.
        specialize (H H7 Γ' ξ H2). replace (VVal VNil) with ((VVal VNil).[ξ]) by auto.
        rewrite map_nth. assumption.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. assumption.
  * intros. split.
    - intros. simpl. constructor.
      + specialize (H Γ). destruct H. inversion H1. subst. specialize (H H6 Γ' ξ H2).
        assumption.
      + clear H. intros. rewrite map_length in H. do 2 rewrite map_map.
        specialize (H0 i H). destruct H0. clear H3. inversion H1. subst. clear H8 H1.
        specialize (H7 i H). pose proof upn_scope.
        specialize (H0 (PatListScope (nth i (map (fst >>> fst) l) nil) + Γ)).
        destruct H0. clear H3. specialize (H0 H7 
        (PatListScope (nth i (map (fst >>> fst) l) nil) + Γ') 
        (upn (PatListScope (nth i (map (fst >>> fst) l) nil)) ξ)).
        specialize (H1 (PatListScope (nth i (map (fst >>> fst) l) nil)) Γ Γ' ξ H2).
        specialize (H0 H1). clear H H2 H1 H5 H7.
        remember (fun x : list Pat * Exp * Exp => (fst ∘ fst) x) as Fff.
        remember (fun x : list Pat * Exp * Exp => (snd ∘ fst) x) as Fsf.
        replace nil with (Fff(nil,VVal VNil,VVal VNil)) in H0 by (subst;auto).
        replace (VVal VNil) with (Fsf(nil,VVal VNil,VVal VNil)) in H0 by (subst;auto).
        do 2 rewrite map_nth in H0. remember (fun x : list Pat * Exp * Exp =>
        Fff
          (let
           '(y0, y) := x in
            let
            '(p, x0) := y0 in
             (p, x0.[upn (PatListScope p) ξ],
             y.[upn (PatListScope p) ξ]))) as FFF.
        remember (fun x : list Pat * Exp * Exp =>
        Fsf
          (let
           '(y0, y) := x in
            let
            '(p, x0) := y0 in
             (p, x0.[upn (PatListScope p) ξ], y.[upn (PatListScope p) ξ]))) as FSF. replace nil with (FFF (nil,VVal VNil,VVal VNil)) by (subst;auto).
        replace (VVal VNil) with (FSF (nil,VVal VNil,VVal VNil)) by (subst;auto).
        do 2 rewrite map_nth. subst. cbn in *.
        destruct (nth i l (nil, ` VNil, ` VNil)) eqn:EQ. destruct p.
        cbn in *. assumption.
      + clear H. intros. rewrite map_length in H. do 2 rewrite map_map.
      specialize (H0 i H). destruct H0. clear H0. inversion H1. subst. clear H7 H1.
      specialize (H8 i H). pose proof upn_scope.
      specialize (H3 (PatListScope (nth i (map (fst >>> fst) l) nil) + Γ)).
      destruct H3. clear H3. specialize (H1 H8 
      (PatListScope (nth i (map (fst >>> fst) l) nil) + Γ') 
      (upn (PatListScope (nth i (map (fst >>> fst) l) nil)) ξ)).
      specialize (H0 (PatListScope (nth i (map (fst >>> fst) l) nil)) Γ Γ' ξ H2).
      specialize (H1 H0). clear H H2 H0 H5 H8.
      replace nil with ((fst >>> fst) ((nil:list Pat),VVal VNil,VVal VNil)) in H1 at 1 by (subst;auto).
      replace (VVal VNil) with (snd ((nil:list Pat),VVal VNil,VVal VNil)) in H1 at 3 by (subst;auto).
      do 2 rewrite map_nth in H1. remember (fun x : list Pat * Exp * Exp =>
      (fst >>> fst)
        (let
         '(y0, y) := x in
          let
          '(p, x0) := y0 in
           (p, x0.[upn (PatListScope p) ξ],
           y.[upn (PatListScope p) ξ]))) as FFF.
      remember (fun x : list Pat * Exp * Exp =>
      snd
        (let
         '(y0, y) := x in
          let
          '(p, x0) := y0 in
           (p, x0.[upn (PatListScope p) ξ], y.[upn (PatListScope p) ξ])))as FSF. replace nil with (FFF (nil,VVal VNil,VVal VNil)) by (subst;auto).
      replace (VVal VNil) with (FSF (nil,VVal VNil,VVal VNil)) by (subst;auto).
      do 2 rewrite map_nth. subst. cbn in *.
      destruct (nth i l (nil, ` VNil, ` VNil)) eqn:EQ. destruct p.
      cbn in *.
      replace nil with ((fst >>> fst) (nil:list Pat, `VNil, `VNil)) in H1 by auto. rewrite map_nth, EQ in H1.
      assumption.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. assumption.
  * intros. split.
    - intros. simpl. constructor.
      + clear H0. specialize (H Γ). destruct H. clear H0. inversion H1. subst.
        specialize (H H5 Γ' ξ H2). assumption.
      + clear H. specialize (H0 (l + Γ)). destruct H0. clear H0. inversion H1. subst.
        specialize (H H7 (l + Γ') (upn l ξ)). pose proof upn_scope.
        specialize (H0 l Γ Γ' ξ H2). specialize (H H0). assumption.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. assumption.
  * intros. split.
    - intros. simpl. constructor.
      + clear H0. specialize (H Γ). destruct H. clear H0. inversion H1. subst.
        specialize (H H5 Γ' ξ H2). assumption.
      + clear H. specialize (H0 Γ). destruct H0. clear H0. inversion H1. subst.
        specialize (H H6 Γ' ξ H2). assumption.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. assumption.
  * intros. split.
    - intros. simpl. constructor.
      + intros. rewrite map_length in H3. clear H. specialize (H0 i H3 (Datatypes.length l +
        nth i (map fst l) 0 + Γ)). destruct H0. clear H0. inversion H1. subst.
        specialize (H6 i H3). specialize (H H6 (Datatypes.length l + nth i (map fst l) 0
        +  Γ') (upn (Datatypes.length l + nth i (map fst l) 0) ξ)). pose proof upn_scope.
        specialize (H0 (Datatypes.length l + nth i (map fst l) 0) Γ Γ' ξ H2).
        specialize (H H0). clear H0 H1 H2 H3 H6 H7. do 2 rewrite map_map. rewrite map_length.
        replace 0 with (fst (0, VVal VNil)) in H by auto. replace (VVal VNil) with
        (snd (0, VVal VNil)) in H by auto. do 2 rewrite map_nth in H.
        remember (fun x : nat * Exp => fst (let '(n, x0) := x in 
        (n, x0.[upn (Datatypes.length l + n) ξ]))) as FF.
        remember (fun x : nat * Exp => snd (let '(n, x0) := x in 
        (n, x0.[upn (Datatypes.length l + n) ξ]))) as FS.
        replace 0 with (FF (0, VVal VNil)) by (subst;auto).
        replace (VVal VNil) with (FS (0, VVal VNil)) by (subst;auto).
        do 2 rewrite map_nth. replace (FF (nth i l (0, FS (0, VVal VNil)))) with
        (fst (nth i l (0, snd (0, VVal VNil)))).
        ** replace (FS (nth i l (0, VVal VNil))) with ((snd (nth i l (0, VVal VNil)))
           .[upn (Datatypes.length l + fst (nth i l (0, snd (0, VVal VNil)))) ξ]).
           -- assumption.
           -- subst. clear. simpl. destruct (nth i l (0, VVal VNil)). simpl. reflexivity.
        ** subst. clear. simpl. destruct (nth i l (0, VVal VNil)). simpl. reflexivity.
      + clear H0. rewrite map_length. inversion H1. subst.
        specialize (H (Datatypes.length l + Γ)). destruct H. clear H0 H1.
        specialize (H H6 (Datatypes.length l + Γ') (upn (Datatypes.length l) ξ)).
        pose proof upn_scope. specialize (H0 (Datatypes.length l) Γ Γ' ξ H2).
        specialize (H H0). assumption.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. assumption.
  * intros. split.
    - intros. simpl. constructor.
      + clear H0 H1. specialize (H Γ). destruct H. clear H0. inversion H2. subst.
        specialize (H H6 Γ' ξ H3). assumption.
      + clear H H1. specialize (H0 (vl1 + Γ)). destruct H0. clear H0. inversion H2. subst.
        specialize (H H9 (vl1 + Γ') (upn vl1 ξ)). pose proof upn_scope.
        specialize (H0 vl1 Γ Γ' ξ H3). specialize (H H0). assumption.
      + clear H H0. specialize (H1 (vl2 + Γ)). destruct H1. clear H0. inversion H2. subst.
        specialize (H H10 (vl2 + Γ') (upn vl2 ξ)). pose proof upn_scope.
        specialize (H0 vl2 Γ Γ' ξ H3). specialize (H H0). assumption.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. assumption.
  * intros. inversion H.
  * intros. split.
    - intros. destruct i.
      + simpl. specialize (H Γ). destruct H. apply H.
        ** auto.
        ** auto.
      + simpl. simpl in H1. specialize (H0 i ltac:(lia) Γ). destruct H0. apply H0.
        ** simpl in H2. assumption.
        ** assumption.
    - intros. specialize (H2 Γ idsubst). specialize (H2 (renscope_id Γ)).
      pose proof idsubst_is_id as [H3 [_ _]]. rewrite H3 in H2. assumption.
  * intros. inversion H.
  * intros. split.
    - intros. destruct i.
      + simpl. specialize (H Γ). destruct H. apply H.
        ** auto.
        ** auto.
      + simpl. simpl in H1. specialize (H0 i ltac:(lia) Γ). destruct H0. apply H0.
        ** simpl in H2. assumption.
        ** assumption.
    - intros. specialize (H2 Γ idsubst). specialize (H2 (renscope_id Γ)).
      pose proof idsubst_is_id as [_ [_ H3]]. rewrite H3 in H2. assumption.
  * intros. inversion H.
  * intros. split.
    - intros. destruct i.
      + simpl. specialize (H Γ). assumption.
      + simpl in *. specialize (H1 i ltac:(slia)). destruct H1. specialize (H1 Γ).
        assumption.
    - intros. destruct i.
      + simpl. specialize (H0 Γ). assumption.
      + simpl in *. specialize (H1 i ltac:(slia)). destruct H1. specialize (H3 Γ).
        assumption.
  * intros. inversion H.
  * intros. split.
    - intros. destruct i.
      + simpl. specialize (H Γ). assumption.
      + simpl in *. specialize (H1 i ltac:(slia)). destruct H1. specialize (H1 Γ).
        assumption.
    - intros. destruct i.
      + simpl. specialize (H0 Γ). assumption.
      + simpl in *. specialize (H1 i ltac:(slia)). destruct H1. specialize (H3 Γ).
        assumption.
  * intros. inversion H.
  * intros. split.
    - intros. destruct i.
      + simpl in *. specialize (H Γ). destruct H. specialize (H H2 Γ' ξ H3).
        assumption.
      + simpl in *. specialize (H0 i ltac:(slia) Γ). destruct H0.
        specialize (H0 H2 Γ' ξ H3). assumption.
    - intros. specialize (H2 Γ idsubst). specialize (H2 (renscope_id Γ)).
      pose proof idsubst_is_id as [H3 [_ _]]. rewrite H3 in H2. assumption.
  * intros. inversion H.
  * intros. split.
    - intros. simpl in H2. destruct i.
      + simpl. specialize (H Γ). assumption.
      + simpl. specialize (H1 i ltac:(slia)). destruct H1.
        specialize (H1 Γ). assumption.
    - intros. simpl in H2. destruct i.
      + simpl. specialize (H0 Γ). assumption.
      + simpl. specialize (H1 i ltac:(slia)). destruct H1.
        specialize (H3 Γ). assumption.
  * intros. inversion H.
  * intros. destruct i.
    - simpl. specialize (H Γ). assumption.
    - simpl in *. specialize (H0 i ltac:(slia) Γ). assumption.
Qed.

Lemma subst_preserves_scope_exp : forall Γ e,
    EXP Γ ⊢ e <->
    forall Γ' ξ,
      SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
      EXP Γ' ⊢ e.[ξ].
Proof.
  intros.
  apply subst_preserves_scope.
Qed.

Lemma subst_preserves_scope_val : forall Γ e,
    VAL Γ ⊢ e <->
    forall Γ' ξ,
      SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
      VAL Γ' ⊢ e.[ξ]ᵥ.
Proof.
  intros.
  apply subst_preserves_scope.
Qed.

(**)
Lemma subst_preserves_scope_nval : forall Γ e,
    NVAL Γ ⊢ e <->
    forall Γ' ξ,
      SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
      NVAL Γ' ⊢ e.[ξ]ₑ.
Proof.
  intros.
  apply subst_preserves_scope.
Qed.

(** *)
Module SUB_IMPLIES_SCOPE.
  Definition magic_ξ (Γ Γ' : nat) (a : Val) (n : nat) : Val + nat :=
    if Compare_dec.lt_dec n Γ
    then if Compare_dec.lt_dec n Γ'
         then inr n
         else inl a
    else inr Γ'.

  Lemma magic_ξ_scope : forall Γ Γ' a,
    VAL Γ' ⊢ a ->
    SUBSCOPE Γ ⊢ magic_ξ Γ Γ' a ∷ Γ'.
  Proof.
    unfold subscoped.
    intros.
    unfold magic_ξ.
    repeat destruct Compare_dec.lt_dec; try congruence.
  Qed.

  Lemma up_magic Γ Γ' a:
    up_subst (magic_ξ Γ Γ' a) = 
    magic_ξ (S Γ) (S Γ') (renameVal S a).
  Proof.
    extensionality x.
    unfold magic_ξ, up_subst.
    destruct x; cbn; auto.
    unfold shift.
    repeat break_match_goal; repeat break_match_hyp;
      try congruence; auto; try lia.
  Qed.

  Lemma upn_magic : forall n Γ Γ' a,
    upn n (magic_ξ Γ Γ' a) =
    magic_ξ (n + Γ) (n + Γ') (renameVal (fun m => n + m) a).
  Proof.
    induction n; intros; simpl; auto.
    * replace (fun m => m) with (id : nat -> nat) by auto.
      now rewrite (proj2 (proj2 idrenaming_is_id)).
    * replace (fun m : nat => S (n + m)) with (S ∘ fun m => n + m) by auto.
      rewrite <- (proj2 (proj2 rename_comp)).
      now rewrite <- up_magic, IHn.
  Qed.

  Lemma magic_ξ_implies_scope :
      (forall e Γ Γ' a, VALCLOSED a -> EXP Γ' ⊢ e.[magic_ξ Γ Γ' a] ->
       EXP Γ ⊢ e) /\
      (forall e Γ Γ' a, VALCLOSED a -> NVAL Γ' ⊢ e.[magic_ξ Γ Γ' a]ₑ ->
       NVAL Γ ⊢ e) /\
      (forall e Γ Γ' a, VALCLOSED a -> VAL Γ' ⊢ e.[magic_ξ Γ Γ' a]ᵥ ->
       VAL Γ ⊢ e).
  Proof.
    eapply Exp_ind with
    (QV := fun l => forall i, i < length l -> (forall Γ Γ' a, VALCLOSED a -> VAL Γ' ⊢ (nth i l VNil).[magic_ξ Γ Γ' a]ᵥ -> VAL Γ ⊢ (nth i l VNil)))
    (RV := fun l => forall i, i < length l -> (forall Γ Γ' a, VALCLOSED a -> VAL Γ' ⊢ (nth i (map fst l) VNil).[magic_ξ Γ Γ' a]ᵥ -> VAL Γ ⊢ (nth i (map fst l) VNil))  /\
(forall Γ Γ' a, VALCLOSED a -> VAL Γ' ⊢ (nth i (map snd l) VNil).[magic_ξ Γ Γ' a]ᵥ -> VAL Γ ⊢ (nth i (map snd l) VNil)))
    (VV := fun l => forall i, i < length l -> (forall Γ Γ' a, VALCLOSED a -> EXP Γ' ⊢ (nth i (map snd l) (VVal VNil)).[magic_ξ Γ Γ' a] -> EXP Γ ⊢ (nth i (map snd l) (VVal VNil))))
    (Q := fun l => forall i, i < length l -> (forall Γ Γ' a, VALCLOSED a -> EXP Γ' ⊢ (nth i l (VVal VNil)).[magic_ξ Γ Γ' a] -> EXP Γ ⊢ (nth i l (VVal VNil))))
    (R := fun l => forall i, i < length l -> (forall Γ Γ' a, VALCLOSED a -> EXP Γ' ⊢ (nth i (map fst l) (VVal VNil)).[magic_ξ Γ Γ' a] -> EXP Γ ⊢ (nth i (map fst l) (VVal VNil))) /\
(forall Γ Γ' a, VALCLOSED a -> EXP Γ' ⊢ (nth i (map snd l) (VVal VNil)).[magic_ξ Γ Γ' a] -> EXP Γ ⊢ (nth i (map snd l) (VVal VNil))))
    (W := fun l => forall i, i < length l -> (forall Γ Γ' a, VALCLOSED a -> EXP Γ' ⊢ (nth i (map (fst >>> snd) l) (VVal VNil)).[magic_ξ Γ Γ' a] -> EXP Γ ⊢ (nth i (map (fst >>> snd) l) (VVal VNil))) /\
(forall Γ Γ' a, VALCLOSED a -> EXP Γ' ⊢ (nth i (map snd l) (VVal VNil)).[magic_ξ Γ Γ' a] -> EXP Γ ⊢ (nth i (map snd l) (VVal VNil))))
    (Z := fun l => forall i, i < length l -> (forall Γ Γ' a, VALCLOSED a -> EXP Γ' ⊢ (nth i (map snd l) (VVal VNil)).[magic_ξ Γ Γ' a] -> EXP Γ ⊢ (nth i (map snd l) (VVal VNil))))
    .
    * intros. constructor. inv H1. specialize (H Γ Γ' a H0 H4). assumption.
    * intros. constructor. inv H1. specialize (H Γ Γ' a H0 H4). assumption.
    * intros. constructor.
    * intros. constructor.
    * intros. inv H2. constructor.
      - now apply H in H6.
      - now apply H0 in H7.
    * intros. constructor. intros. inv H1.
      eapply H in H2; eauto.
      rewrite map_length in H5. apply H5 in H2.
      replace VNil with (VNil.[magic_ξ Γ Γ' a]ᵥ) in H2 by auto.
      rewrite map_nth in H2. eassumption.
    * intros. inv H1.
      constructor; intros; rewrite map_length in *; apply H in H1 as HH; eapply HH; eauto.
      - apply H3 in H1. rewrite map_map in *.
        clear -H1.
        rewrite map_nth with (d := (VNil, VNil)) in H1.
        rewrite map_nth with (d := (VNil, VNil)).
        cbn in *. destruct (nth i l (VNil, VNil)).
        eassumption.
      - apply H5 in H1. rewrite map_map in *.
        clear -H1.
        rewrite map_nth with (d := (VNil, VNil)) in H1.
        rewrite map_nth with (d := (VNil, VNil)).
        cbn in *. destruct (nth i l (VNil, VNil)).
        eassumption.
    * intros. constructor. simpl in H0. unfold magic_ξ in H0. destruct (Compare_dec.lt_dec n Γ) in H0.
      - auto.
      - inv H0. subst. lia.
    * intros. constructor. simpl in H0. unfold magic_ξ in H0.
      destruct n. destruct (Compare_dec.lt_dec n Γ) in H0.
      - auto.
      - inv H0. cbn in *. lia.
    * intros. constructor.
      - intros. specialize (H i H3). simpl in H2. inv H2.
        rewrite map_length in *.
        (* simplify the goal*)
        do 2 rewrite map_nth with (d := (0,0,VVal VNil)).
        
        (* simpl in H7 that will be needed to specialize H *)
        specialize (H7 i H3). do 2 rewrite map_map in H7.
        do 2 rewrite map_nth with (d := (0,0,VVal VNil)) in H7.
        destruct (nth i ext (0, 0, ` VNil)) eqn:Q, p; cbn in *.
        epose proof (H (length ext + n0 + Γ) (length ext + n0 + Γ') a H1).
        rewrite map_nth with (d := (0,0,VVal VNil)) in H2.
        rewrite Q in H2. cbn in H2.
        rewrite upn_magic in H7.
        rewrite vclosed_ignores_ren in H7; auto.
      - inv H2. rewrite map_length in *.
        specialize (H0 (Datatypes.length ext + vl + Γ) (Datatypes.length ext + vl + Γ') a H1).
        apply H0.
        now rewrite upn_magic, vclosed_ignores_ren in H9.
    * intros. constructor. inv H1. specialize (H (n + Γ) (n + Γ') a H0).
      rewrite upn_magic, vclosed_ignores_ren in H4; auto.
    * intros. constructor. intros.
      specialize (H i H2 Γ Γ' a H0). inv H1.
      rewrite map_length in H5. apply H5 in H2.
      rewrite map_nth with (d := `VNil) in H2.
      now auto.
    * intros. simpl in H2. inv H2. constructor.
      - eapply H; eauto.
      - eapply H0; eauto.
    * intros. constructor. intros.
      specialize (H i H2 Γ Γ' a H0). inv H1.
      rewrite map_length in H5. apply H5 in H2.
      rewrite map_nth with (d := `VNil) in H2.
      now auto.
    * intros. inv H1. rewrite map_length in *. constructor.
      - intros. apply H3 in H1 as HF.
        apply H in H1 as [H1 _].
        rewrite map_map in HF.
        rewrite map_nth with (d := (`VNil, `VNil)) in *.
        destruct nth.
        eapply H1; now eauto.
      - intros. apply H5 in H1 as HF.
        apply H in H1 as [_ H1].
        rewrite map_map in HF.
        rewrite map_nth with (d := (`VNil, `VNil)) in *.
        destruct nth.
        eapply H1; now eauto.
    * intros. constructor. intros.
      specialize (H i H2 Γ Γ' a H0). inv H1.
      rewrite map_length in H5. apply H5 in H2.
      rewrite map_nth with (d := `VNil) in H2.
      now auto.
    * intros. constructor. intros.
      specialize (H i H2 Γ Γ' a H0). inv H1.
      rewrite map_length in H5. apply H5 in H2.
      rewrite map_nth with (d := `VNil) in H2.
      now auto.
    * intros. simpl in H2. inv H2. rewrite map_length in *.
      constructor. intros.
      - now apply H in H6.
      - intros. apply H7 in H2 as HF. eapply H0 in H2.
        1-2: eassumption.
        rewrite map_nth with (d := `VNil) in HF.
        now eassumption.
    * intros. inv H2. rewrite map_length in *. constructor.
      - now eapply H in H5.
      - intros. clear H8.
        apply H7 in H2 as HF.
        eapply H0 in H2 as [H2 _].
        repeat rewrite map_map in HF.
        rewrite map_nth with (d := (nil, `VNil, `VNil)) in HF.
        extract_map_fun in HF as G.
        (* The next map_nth does not work without the replace
           for some reason *)
        replace nil with (G (nil, `VNil, `VNil)) in HF at 1 by now subst G.
        rewrite (map_nth G l) with (d := (nil, `VNil, `VNil)) in HF.
        subst G.
        rewrite map_nth with (d := (nil, `VNil, `VNil)).
        (* The next map_nth does not work without the replace
           for some reason *)
        replace nil with ((fst >>> fst) (nil:list Pat, `VNil, `VNil)) at 1 by auto.
        rewrite map_nth.
        rewrite map_nth with (d := (nil, `VNil, `VNil)) in H2.  
        destruct nth, p; cbn in *.
        rewrite upn_magic, vclosed_ignores_ren in HF; auto.
        now apply H2 in HF.
      - intros. clear H7.
        apply H8 in H2 as HF.
        eapply H0 in H2 as [_ H2].
        repeat rewrite map_map in HF.
        rewrite map_nth with (d := (nil, `VNil, `VNil)) in HF.
        extract_map_fun in HF as G.
        (* The next map_nth does not work without the replace
           for some reason *)
        replace nil with (G (nil, `VNil, `VNil)) in HF at 1 by now subst G.
        rewrite (map_nth G l) with (d := (nil, `VNil, `VNil)) in HF.
        subst G.
        rewrite map_nth with (d := (nil, `VNil, `VNil)).
        (* The next map_nth does not work without the replace
           for some reason *)
        replace nil with ((fst >>> fst) (nil:list Pat, `VNil, `VNil)) at 1 by auto.
        rewrite map_nth.
        rewrite map_nth with (d := (nil, `VNil, `VNil)) in H2.  
        destruct nth, p; cbn in *.
        rewrite upn_magic, vclosed_ignores_ren in HF; auto.
        now apply H2 in HF.
    * intros. inv H2. constructor.
      - now apply H in H6.
      - rewrite upn_magic, vclosed_ignores_ren in H8; auto.
        now apply H0 in H8.
    * intros. inv H2. constructor.
      - now apply H in H6.
      - now apply H0 in H7.
    * intros. simpl in *. inv H2. rewrite map_length in *. constructor.
      - intros. apply H6 in H2 as HF.
        specialize (H0 i H2) as HF2.
        rewrite map_nth with (d := (0, `VNil)).
        rewrite map_nth with (d := (0, `VNil)).
        do 2 rewrite map_map in HF.
        rewrite map_nth with (d := (0, `VNil)) in HF.
        rewrite map_nth with (d := (0, `VNil)) in HF.
        rewrite map_nth with (d := (0, `VNil)) in HF2.
        destruct nth; cbn in *.
        rewrite upn_magic, vclosed_ignores_ren in HF; auto.
        now apply HF2 in HF.
      - rewrite upn_magic, vclosed_ignores_ren in H7; auto.
        now apply H in H7.
    * intros. inv H3. rewrite upn_magic, vclosed_ignores_ren in *; auto.
      apply H in H8. apply H0 in H11. apply H1 in H12. constructor.
      all: now auto.
    (*List*)
    * simpl; intros; lia.
    * intros. destruct i.
      - simpl in *. eapply H; eassumption.
      - simpl in *. eapply (H0 i); try eassumption; lia.
    * simpl; intros; lia.
    * intros. destruct i.
      - simpl in *. eapply H; eassumption.
      - simpl in *. eapply (H0 i); try eassumption; lia.
    * simpl; intros; lia.
    * intros. destruct i.
      - simpl in *. split.
        + eapply H; eassumption.
        + eapply H0; eassumption.
      - simpl in *. eapply (H1 i); try eassumption; lia.
    * simpl; intros; lia.
    * intros. destruct i.
      - split; intros; simpl in *.
        + eapply H; eassumption.
        + eapply H0; eassumption.
      - simpl in *. eapply (H1 i); try eassumption; lia.
    * simpl; intros; lia.
    * intros. destruct i.
      - simpl in *. eapply H; eassumption.
      - simpl in *. eapply (H0 i); try eassumption; lia.
    * simpl; intros; lia.
    * intros. destruct i.
      - split; intros; simpl in *.
        + eapply H; eassumption.
        + eapply H0; eassumption.
      - simpl in *. eapply (H1 i); try eassumption; lia.
    * simpl; intros; lia.
    * intros. destruct i.
      - simpl in *. eapply H; eassumption.
      - simpl in *. eapply (H0 i); try eassumption; lia.
  Qed.

  Lemma sub_implies_scope_exp : forall e Γ Γ',
      (forall ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ e.[ξ]) ->
      EXP Γ ⊢ e.
  Proof.
    intros;
    eapply magic_ξ_implies_scope with (a := VNil); auto.
    apply H.
    apply magic_ξ_scope. now auto.
  Qed.

  Lemma sub_implies_scope_nval : forall e Γ Γ',
      (forall ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> NVAL Γ' ⊢ e.[ξ]ₑ) ->
      NVAL Γ ⊢ e.
  Proof.
    intros;
    eapply magic_ξ_implies_scope with (a := VNil); auto.
    apply H;
    apply magic_ξ_scope. now auto.
  Qed.

  Lemma sub_implies_scope_val : forall e Γ Γ',
      (forall ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> VAL Γ' ⊢ e.[ξ]ᵥ) ->
      VAL Γ ⊢ e.
  Proof.
    intros;
    eapply magic_ξ_implies_scope with (a := VNil); auto.
    apply H;
    apply magic_ξ_scope. now auto.
  Qed.

  Definition magic_ξ_2 Γ' a :=
    fun n =>
      if Compare_dec.lt_dec n Γ'
      then idsubst n
      else if Nat.eq_dec n Γ'
           then inl a
           else idsubst (pred n).

  Lemma up_magic_2 : forall Γ a,
      up_subst (magic_ξ_2 Γ a) = magic_ξ_2 (S Γ) (renameVal S a).
  Proof.
    intros.
    unfold magic_ξ_2.
    extensionality x.
    unfold up_subst, shift, idsubst.
    destruct x; auto.
    simpl.
    unfold Init.Nat.pred.
    repeat destruct Compare_dec.lt_dec; auto; destruct Nat.eq_dec; auto; try lia.
    f_equiv. destruct x; lia.
  Qed.

  Lemma upn_magic_2 : forall n Γ a,
    upn n (magic_ξ_2 Γ a) = magic_ξ_2 (n + Γ) (renameVal (fun m => n + m) a).
  Proof.
    induction n; intros; cbn; auto.
    * replace (fun m => m) with (id : nat -> nat) by reflexivity.
      now rewrite (proj2 (proj2 idrenaming_is_id)).
    * replace (fun m : nat => S (n + m)) with (S ∘ fun m => n + m) by auto.
      rewrite <- (proj2 (proj2 rename_comp)).
      now rewrite <- up_magic_2, IHn.
  Qed.

  Lemma magic_const a : magic_ξ_2 0 a = a .: idsubst.
  Proof.
    unfold magic_ξ_2.
    extensionality x.
    destruct Compare_dec.lt_dec; unfold idsubst. inversion l.
    destruct Nat.eq_dec; subst; auto.
    destruct x; cbn; auto. lia.
  Qed.

  Lemma upn_lt n : forall ξ x, x < n -> upn n ξ x = inr x.
  Proof.
    induction n; intros; try lia.
    * simpl. destruct x; auto. cbn. unfold shift. rewrite IHn; auto. lia. 
  Qed.

  Lemma upn_eq : forall n a ξ, upn n (a .: ξ) n = inl (renameVal (fun m => n + m) a).
  Proof.
    induction n; intros; cbn.
    * now rewrite (proj2 (proj2 idrenaming_is_id)).
    * unfold shift. rewrite IHn. now rewrite (proj2 (proj2 rename_comp)).
  Qed.

  Lemma magic_const_ind a Γ :
    magic_ξ_2 Γ (renameVal (fun n => Γ + n) a) = upn Γ (a .: idsubst).
  Proof.
    unfold magic_ξ_2.
    extensionality x.
    destruct Compare_dec.lt_dec; unfold idsubst.
    * now rewrite upn_lt.
    * break_match_goal. subst. now rewrite upn_eq.
      generalize dependent x.
      induction Γ; intros; cbn.
      - destruct x. lia. now simpl.
      - destruct x. lia. simpl. unfold shift. rewrite <- IHΓ. 2-3: lia.
        destruct x; f_equal; try lia.
  Qed.

  Lemma magic_ξ_magic_ξ_2 :
      (forall e Γ' a, VALCLOSED a -> EXP Γ' ⊢ e.[magic_ξ_2 Γ' a] ->
       e.[magic_ξ (S Γ') Γ' a] = e.[magic_ξ_2 Γ' a]) /\
      (forall e Γ' a, VALCLOSED a -> NVAL Γ' ⊢ e.[magic_ξ_2 Γ' a]ₑ ->
       e.[magic_ξ (S Γ') Γ' a]ₑ = e.[magic_ξ_2 Γ' a]ₑ) /\
      (forall e Γ' a, VALCLOSED a -> VAL Γ' ⊢ e.[magic_ξ_2 Γ' a]ᵥ ->
       e.[magic_ξ (S Γ') Γ' a]ᵥ = e.[magic_ξ_2 Γ' a]ᵥ).
  Proof.
    eapply Exp_ind with
    (QV := fun l => forall i, i < length l -> (forall Γ' a, VALCLOSED a -> VAL Γ' ⊢ (nth i l VNil).[magic_ξ_2 Γ' a]ᵥ -> (nth i l VNil).[magic_ξ (S Γ') Γ' a]ᵥ = (nth i l VNil).[magic_ξ_2 Γ' a]ᵥ))
    (RV := fun l => forall i, i < length l -> (forall Γ' a, VALCLOSED a -> VAL Γ' ⊢ (nth i (map fst l) VNil).[magic_ξ_2 Γ' a]ᵥ -> (nth i (map fst l) VNil).[magic_ξ (S Γ') Γ' a]ᵥ = (nth i (map fst l) VNil).[magic_ξ_2 Γ' a]ᵥ) /\
(forall Γ' a, VALCLOSED a -> VAL Γ' ⊢ (nth i (map snd l) VNil).[magic_ξ_2 Γ' a]ᵥ -> (nth i (map snd l) VNil).[magic_ξ (S Γ') Γ' a]ᵥ = (nth i (map snd l) VNil).[magic_ξ_2 Γ' a]ᵥ))
    (VV := fun l => forall i, i < length l -> (forall Γ' a, VALCLOSED a -> EXP Γ' ⊢ (nth i (map snd l) (VVal VNil)).[magic_ξ_2 Γ' a] -> (nth i (map snd l) (VVal VNil)).[magic_ξ (S Γ') Γ' a] = (nth i (map snd l) (VVal VNil)).[magic_ξ_2 Γ' a]))
    (Q := fun l => forall i, i < length l -> (forall Γ' a, VALCLOSED a -> EXP Γ' ⊢ (nth i l (VVal VNil)).[magic_ξ_2 Γ' a] -> (nth i l (VVal VNil)).[magic_ξ (S Γ') Γ' a] = (nth i l (VVal VNil)).[magic_ξ_2 Γ' a]))
    (R := fun l => forall i, i < length l -> (forall Γ' a, VALCLOSED a -> EXP Γ' ⊢ (nth i (map fst l) (VVal VNil)).[magic_ξ_2 Γ' a] -> (nth i (map fst l) (VVal VNil)).[magic_ξ (S Γ') Γ' a] = (nth i (map fst l) (VVal VNil)).[magic_ξ_2 Γ' a]) /\
(forall Γ' a, VALCLOSED a -> EXP Γ' ⊢ (nth i (map snd l) (VVal VNil)).[magic_ξ_2 Γ' a] -> (nth i (map snd l) (VVal VNil)).[magic_ξ (S Γ') Γ' a] = (nth i (map snd l) (VVal VNil)).[magic_ξ_2 Γ' a]))
    (W := fun l => forall i, i < length l -> (forall Γ' a, VALCLOSED a -> EXP Γ' ⊢ (nth i (map (fst >>> snd) l) (VVal VNil)).[magic_ξ_2 Γ' a] -> (nth i (map (fst >>> snd) l) (VVal VNil)).[magic_ξ (S Γ') Γ' a] = (nth i (map (fst >>> snd) l) (VVal VNil)).[magic_ξ_2 Γ' a]) /\
(forall Γ' a, VALCLOSED a -> EXP Γ' ⊢ (nth i (map snd l) (VVal VNil)).[magic_ξ_2 Γ' a] -> (nth i (map snd l) (VVal VNil)).[magic_ξ (S Γ') Γ' a] = (nth i (map snd l) (VVal VNil)).[magic_ξ_2 Γ' a]))
    (Z := fun l => forall i, i < length l -> (forall Γ' a, VALCLOSED a -> EXP Γ' ⊢ (nth i (map snd l) (VVal VNil)).[magic_ξ_2 Γ' a] -> (nth i (map snd l) (VVal VNil)).[magic_ξ (S Γ') Γ' a] = (nth i (map snd l) (VVal VNil)).[magic_ξ_2 Γ' a]))
    .
    * intros. simpl. f_equal. inv H1. now apply H in H4.
    * intros. simpl. f_equal. inv H1. now apply H in H4.
    * intros. simpl. reflexivity.
    * intros. simpl. reflexivity.
    * intros. simpl. inv H2. apply H in H6. apply H0 in H7. now f_equal.
      1-2: now auto.
    * intros. inv H1. simpl. f_equal. rewrite map_length in *.
      apply mapeq_if_ntheq with (d := VNil). intros.
      apply H4 in H1 as HF.
      rewrite map_nth with (d := VNil) in HF.
      do 2 rewrite map_nth with (d := VNil).
      now apply H in HF.
    * intros. inv H1. simpl. rewrite map_length, map_map in *. f_equal.
      apply mapeq_if_ntheq with (d := (VNil, VNil)). intros.
      apply H3 in H1 as HF1.
      apply H5 in H1 as HF2.
      clear H3 H5. apply H in H1 as [HF11 HF22].
      repeat rewrite map_nth with (d := (VNil, VNil)) in *.
      destruct nth; cbn in *.
      apply HF11 in HF1. apply HF22 in HF2. now f_equal.
      1-2: now auto.
    * intros. simpl in *. unfold magic_ξ_2, magic_ξ, idsubst in *.
      destruct Compare_dec.lt_dec.
      - inv H0. destruct Compare_dec.lt_dec.
        + reflexivity.
        + lia.
      - destruct Compare_dec.lt_dec.
        + destruct Nat.eq_dec.
          ** reflexivity.
          ** lia.
        + destruct Nat.eq_dec.
          ** lia.
          ** inv H0. lia.
    * intros. simpl in *. unfold magic_ξ_2, magic_ξ, idsubst in *. destruct n; simpl in *.
      destruct Compare_dec.lt_dec.
      - inv H0. destruct Compare_dec.lt_dec.
        + reflexivity.
        + lia.
      - destruct Compare_dec.lt_dec.
        + destruct Nat.eq_dec.
          ** reflexivity.
          ** lia.
        + destruct Nat.eq_dec.
          ** lia.
          ** inv H0. simpl in H3. lia.
    * intros. simpl in *. inv H2.
      rewrite map_length, map_map in *.
      rewrite upn_magic_2, vclosed_ignores_ren in H9; auto.
      apply H0 in H9; auto. f_equal.
      - clear H9. apply mapeq_if_ntheq with (d := (0, 0, `VNil)). intros.
        apply H6 in H2 as HF. specialize (H _ H2).
        repeat rewrite map_nth with (d := (0, 0, `VNil)) in *.
        destruct nth, p; cbn in *.
        rewrite upn_magic_2 in *. rewrite upn_magic.
        rewrite vclosed_ignores_ren in *; auto.
        apply H in HF; auto.
        replace (length ext + n0 + S Γ') with (S (length ext + n0 + Γ')) by lia.
        now rewrite HF.
      - rewrite upn_magic, upn_magic_2, vclosed_ignores_ren; auto.
        now replace (length ext + vl + S Γ') with (S (length ext + vl + Γ')) by lia.
    * intros. simpl. inv H1. f_equal.
      rewrite upn_magic_2 in *. rewrite upn_magic.
      rewrite vclosed_ignores_ren in *; auto.
      apply H in H4; auto.
      now rewrite <- plus_n_Sm.
    * intros. inv H1. simpl. f_equal. rewrite map_length in *.
      apply mapeq_if_ntheq with (d := `VNil). intros.
      apply H4 in H1 as HF.
      rewrite map_nth with (d := `VNil) in HF.
      do 2 rewrite map_nth with (d := `VNil).
      now apply H in HF.
    * intros. simpl. inv H2. apply H in H6. apply H0 in H7. now f_equal.
      1-2: now auto.
    * intros. inv H1. simpl. f_equal. rewrite map_length in *.
      apply mapeq_if_ntheq with (d := `VNil). intros.
      apply H4 in H1 as HF.
      rewrite map_nth with (d := `VNil) in HF.
      do 2 rewrite map_nth with (d := `VNil).
      now apply H in HF.
    * intros. inv H1. simpl. rewrite map_length, map_map in *. f_equal.
      apply mapeq_if_ntheq with (d := (`VNil, `VNil)). intros.
      apply H3 in H1 as HF1.
      apply H5 in H1 as HF2.
      clear H3 H5. apply H in H1 as [HF11 HF22].
      repeat rewrite map_nth with (d := (`VNil, `VNil)) in *.
      destruct nth; cbn in *.
      apply HF11 in HF1. apply HF22 in HF2. now f_equal.
      1-2: now auto.
    * intros. inv H1. simpl. f_equal. rewrite map_length in *.
      apply mapeq_if_ntheq with (d := `VNil). intros.
      apply H4 in H1 as HF.
      rewrite map_nth with (d := `VNil) in HF.
      do 2 rewrite map_nth with (d := `VNil).
      now apply H in HF.
    * intros. inv H1. simpl. f_equal. rewrite map_length in *.
      apply mapeq_if_ntheq with (d := `VNil). intros.
      apply H4 in H1 as HF.
      rewrite map_nth with (d := `VNil) in HF.
      do 2 rewrite map_nth with (d := `VNil).
      now apply H in HF.
    * intros. inv H2. simpl. f_equal.
      - now apply H in H6.
      - rewrite map_length in *.
        apply mapeq_if_ntheq with (d := `VNil). intros.
        apply H7 in H2 as HF.
        rewrite map_nth with (d := `VNil) in HF.
        do 2 rewrite map_nth with (d := `VNil).
        now apply H0 in HF.
    * intros. inv H2. rewrite map_length in *. simpl. f_equal.
      - clear -H1 H H5. now apply H in H5.
      - clear -H1 H0 H7 H8. apply mapeq_if_ntheq with (d := (nil, `VNil, `VNil)).
        intros. specialize (H7 _ H). specialize (H8 _ H).
        specialize (H0 _ H) as [IH1 IH2].
        do 2 rewrite map_map in *.
        repeat rewrite map_nth with (d := (nil, `VNil, `VNil)) in *.
        (* simple rewriting does not work for the goal for some reason *)
        extract_map_fun F.
        replace (nil, `VNil, `VNil) with (F (nil, `VNil, `VNil)) at 1 by now subst F.
        rewrite map_nth. subst F.
        extract_map_fun F.
        replace (nil, `VNil, `VNil) with (F (nil, `VNil, `VNil)) at 2 by now subst F.
        rewrite map_nth. subst F.
        destruct nth, p; cbn in *.
        rewrite upn_magic_2 in *. rewrite upn_magic.
        rewrite vclosed_ignores_ren in *; auto.
        apply IH1 in H7; auto. apply IH2 in H8; auto. rewrite <- plus_n_Sm.
        now rewrite H7, H8.
    * intros. simpl. inv H2. rewrite upn_magic_2 in *. rewrite upn_magic.
      rewrite vclosed_ignores_ren in *; auto.
      rewrite <- plus_n_Sm. f_equal.
      - now apply H in H6.
      - now apply H0 in H8.
    * intros. simpl. inv H2. f_equal.
      - now apply H in H6.
      - now apply H0 in H7.
    * intros. inv H2. rewrite map_length, map_map in *. simpl. f_equal.
      - clear H7 H. apply mapeq_if_ntheq with (d := (0, `VNil)). intros.
        apply H6 in H as HF. clear H6.
        specialize (H0 _ H).
        repeat rewrite map_nth with (d := (0, `VNil)) in *.
        destruct nth. simpl in *.
        rewrite upn_magic_2 in *. rewrite upn_magic.
        rewrite vclosed_ignores_ren in *; auto.
        apply H0 in HF; auto. now rewrite <- plus_n_Sm, HF.
      - clear H6 H0.
        rewrite upn_magic_2 in *. rewrite upn_magic.
        rewrite vclosed_ignores_ren in *; auto.
        apply H in H7; auto. now rewrite <- plus_n_Sm.
    * intros. simpl. inv H3. do 2 rewrite upn_magic.
      do 2 rewrite <- plus_n_Sm. do 2 rewrite upn_magic_2 in *.
      do 2 rewrite vclosed_ignores_ren in *; auto. f_equal.
      - now apply H in H8.
      - now apply H0 in H11.
      - now apply H1 in H12.
    (* Lists *)
    * intros. inv H.
    * intros. destruct i; simpl in *.
      - now apply H in H3.
      - apply H0; auto. lia.
    * intros. inv H.
    * intros. destruct i; simpl in *.
      - now apply H in H3.
      - apply H0; auto. lia.
    * intros. inv H.
    * intros. destruct i; simpl in *. split.
      - intros. now apply H in H4.
      - intros. now apply H0 in H4.
      - apply H1; auto. lia.
    * intros. inv H.
    * intros. destruct i; simpl in *. split.
      - intros. now apply H in H4.
      - intros. now apply H0 in H4.
      - apply H1; auto. lia.
    * intros. inv H.
    * intros. destruct i; simpl in *.
      - now apply H in H3.
      - apply H0; auto. lia.
    * intros. inv H.
    * intros. destruct i; simpl in *. split.
      - intros. now apply H in H4.
      - intros. now apply H0 in H4.
      - apply H1; auto. lia.
    * intros. inv H.
    * intros. destruct i; simpl in *. 
      - now apply H in H3.
      - apply H0; auto. lia.
  Qed.

  Lemma magic_ξ_magic_ξ_2_closed : 
      (forall e a, VALCLOSED a -> EXPCLOSED e.[ a /] ->
      e.[magic_ξ 1 0 a] = e.[a /]) /\
      (forall e a, VALCLOSED a -> NVALCLOSED e.[ a /]ₑ ->
      e.[magic_ξ 1 0 a]ₑ = e.[a /]ₑ) /\
      (forall e a, VALCLOSED a -> VALCLOSED e.[ a /]ᵥ ->
      e.[magic_ξ 1 0 a]ᵥ = e.[a /]ᵥ).
  Proof.
    split. 2: split. all: intros.
    * rewrite <- magic_const, (proj1 magic_ξ_magic_ξ_2); auto.
      now rewrite magic_const.
    * rewrite <- magic_const, (proj1 (proj2 magic_ξ_magic_ξ_2)); auto.
      now rewrite magic_const.
    * rewrite <- magic_const, (proj2 (proj2 magic_ξ_magic_ξ_2)); auto.
      now rewrite magic_const.
  Qed.

  Lemma sub_implies_scope_exp_1 : forall e a,
    VALCLOSED a ->
    EXPCLOSED e.[ a /] ->
    EXP 1 ⊢ e.
  Proof.
    intros. eapply magic_ξ_implies_scope. eassumption.
    pose proof magic_ξ_magic_ξ_2_closed as [HH [_ _]].
    now rewrite HH.
  Qed.

  Lemma sub_implies_scope_val_1 : forall e a,
    VALCLOSED a ->
    VALCLOSED e.[ a /]ᵥ ->
    VAL 1 ⊢ e.
  Proof.
    intros. eapply magic_ξ_implies_scope. exact H. (* do NOT use eassumption here *)
    pose proof magic_ξ_magic_ξ_2_closed as [_ [_ HH]].
    now rewrite HH.
  Qed.

  Lemma sub_implies_scope_nval_1 : forall e a,
    VALCLOSED a ->
    NVALCLOSED e.[ a /]ₑ ->
    NVAL 1 ⊢ e.
  Proof.
    intros. eapply magic_ξ_implies_scope. eassumption.
    pose proof magic_ξ_magic_ξ_2_closed as [_ [HH _]].
    now rewrite HH.
  Qed.

  Lemma scons_subst :
    forall x ξ, x.[ξ]ᵥ .: ξ = (x .: idsubst) >> ξ.
  Proof.
    intros. extensionality y. unfold scons, substcomp. destruct y; auto.
  Qed.

  Lemma list_subst_app :
    forall l1 l2,
      list_subst (l1 ++ l2) idsubst = 
      upn (length l1) (list_subst l2 idsubst) >> list_subst l1 idsubst.
  Proof.
    induction l1; cbn; intros.
    * now rewrite substcomp_id_r.
    * unfold list_subst in *. rewrite IHl1; auto.
      now rewrite substcomp_scons_core.
  Qed.

  (* NOTE: this only holds for EXPCLOSED e.[list_subst vl idsubst], it
     cannot be generalized to EXP Γ ⊢ e.[list_subst vl idsubst]!!! *)
  Corollary subst_preserves_list_scope :
    forall vl e, Forall (fun v => VALCLOSED v) vl ->
    EXPCLOSED e.[list_subst vl idsubst] ->
    EXP length vl ⊢ e.  
  Proof.
    induction vl using list_length_ind.
    destruct (length vl) eqn:P; simpl; intros.
    * apply length_zero_iff_nil in P. subst. now rewrite idsubst_is_id_exp in H1.
    * apply eq_sym, last_element_exists in P as P'. destruct P' as [l [x EQ]]. subst.
      apply Forall_app in H0 as [H01 H02]. inv H02. clear H4.
      rewrite list_subst_app in H1; auto. rewrite <- subst_comp_exp in H1.
      cbn in H1.
      apply H in H1; auto. 2: rewrite app_length in P; simpl in P; lia.
      rewrite <- magic_const_ind in H1. rewrite vclosed_ignores_ren in H1; auto.
      rewrite <- (proj1 magic_ξ_magic_ξ_2) in H1; auto.
      replace n with (length l) . 2: {
        rewrite app_length in P; simpl in P. lia.
      }
      eapply (proj1 magic_ξ_implies_scope); eassumption.
  Qed.

End SUB_IMPLIES_SCOPE.

Add Search Blacklist "SUB_IMPLIES_SCOPE".

Definition subst_implies_scope_exp := SUB_IMPLIES_SCOPE.sub_implies_scope_exp.
Definition subst_implies_scope_val := SUB_IMPLIES_SCOPE.sub_implies_scope_val.
Definition subst_implies_scope_nval := SUB_IMPLIES_SCOPE.sub_implies_scope_nval.
Definition subst_implies_scope_exp_1 := SUB_IMPLIES_SCOPE.sub_implies_scope_exp_1.
Definition subst_implies_scope_val_1 := SUB_IMPLIES_SCOPE.sub_implies_scope_val_1.
Definition subst_implies_scope_nval_1 := SUB_IMPLIES_SCOPE.sub_implies_scope_nval_1.
Definition subst_implies_list_scope := SUB_IMPLIES_SCOPE.subst_implies_list_scope.

Lemma upn_Var : forall (Γ : nat) (ξ : Substitution) (v : nat),
    v < Γ -> upn Γ ξ v = inr v.
Proof.
  intros Γ ξ.
  induction Γ;
    intros.
  + inversion H.
  + simpl. destruct v.
    * simpl. auto.
    * simpl. unfold shift. rewrite IHΓ. 2: lia. auto.
Qed.

Corollary upn_ignores_sub :
     (forall e Γ ξ,  EXP Γ ⊢ e -> e.[upn Γ ξ]  = e) /\
     (forall e Γ ξ, NVAL Γ ⊢ e -> e.[upn Γ ξ]ₑ = e) /\
     (forall e Γ ξ,  VAL Γ ⊢ e -> e.[upn Γ ξ]ᵥ = e).
Proof.
  split.
  * intros. eapply scoped_ignores_sub; eauto. intro. intros. apply upn_Var. auto.
  * split.
    - intros. eapply scoped_ignores_sub; eauto. intro. intros. apply upn_Var. auto.
    - intros. eapply scoped_ignores_sub; eauto. intro. intros. apply upn_Var. auto.
Qed.

Lemma escoped_ignores_sub : forall e Γ ξ,
    EXP Γ ⊢ e -> e.[upn Γ ξ] = e.
Proof.
  intros.
  eapply upn_ignores_sub in H.
  eauto.
Qed.
Global Hint Resolve escoped_ignores_sub : core.

Lemma vscoped_ignores_sub : forall e Γ ξ,
    VAL Γ ⊢ e -> e.[upn Γ ξ]ᵥ = e.
Proof.
  intros.
  eapply upn_ignores_sub in H.
  eauto.
Qed.

(* New *)
Lemma nvscoped_ignores_sub : forall e Γ ξ,
    NVAL Γ ⊢ e -> e.[upn Γ ξ]ₑ = e.
Proof.
  intros.
  eapply upn_ignores_sub in H.
  eauto.
Qed.

Global Hint Resolve vscoped_ignores_sub : core.

Lemma eclosed_sub_closed : forall v ξ,
    EXPCLOSED v -> EXPCLOSED v.[ξ].
Proof.
  intros.
  rewrite eclosed_ignores_sub;
    auto.
Qed.
Global Hint Resolve eclosed_sub_closed : core.

Lemma vclosed_sub_closed : forall v ξ,
    VALCLOSED v -> VALCLOSED v.[ξ]ᵥ.
Proof.
  intros.
  rewrite vclosed_ignores_sub;
    auto.
Qed.
Global Hint Resolve vclosed_sub_closed : core.

(* New *)
Lemma nvclosed_sub_closed : forall v ξ,
    NVALCLOSED v -> NVALCLOSED v.[ξ]ₑ.
Proof.
  intros.
  rewrite nvclosed_ignores_sub;
    auto.
Qed.
Global Hint Resolve nvclosed_sub_closed : core.


Lemma scoped_list_subscoped :
  forall vals Γ ξ Γ', Forall (fun v => VAL Γ ⊢ v) vals -> SUBSCOPE Γ' ⊢ ξ ∷ Γ ->
  SUBSCOPE length vals + Γ' ⊢ list_subst vals ξ ∷ Γ.
Proof.
  induction vals; intros; simpl; auto.
  simpl. inversion H. intros y Hy. subst. destruct y.
  * simpl. apply H3.
  * simpl. specialize (IHvals _ _ _ H4 H0 y). apply IHvals. lia.
Qed.

Corollary scoped_list_subscoped_eq :
  forall vals Γ ξ Γ' n,
  n = length vals ->
  Forall (fun v => VAL Γ ⊢ v) vals ->
  SUBSCOPE Γ' ⊢ ξ ∷ Γ ->
  SUBSCOPE n + Γ' ⊢ list_subst vals ξ ∷ Γ.
Proof.
  intros. subst. now apply scoped_list_subscoped.
Qed.

Lemma scoped_list_idsubst :
  forall vals Γ, Forall (fun v => VAL Γ ⊢ v) vals ->
  SUBSCOPE length vals ⊢ list_subst vals idsubst ∷ Γ.
Proof.
  induction vals; intros. simpl.
  unfold idsubst. intro. intros. inversion H0.
  simpl. inversion H. intro. intros. destruct x0.
  * simpl. apply H2.
  * simpl. apply IHvals; auto. lia.
Qed.

Lemma substcomp_scoped :
  forall ξ σ Γ Δ Ω, SUBSCOPE Γ ⊢ ξ ∷ Δ -> SUBSCOPE Δ ⊢ σ ∷ Ω
->
  SUBSCOPE Γ ⊢ ξ >> σ ∷ Ω.
Proof.
  intros. intro. intros. unfold subscoped in H.
  unfold ">>".
  specialize (H x H1).
  destruct (ξ x) eqn:D1.
  * apply -> subst_preserves_scope_val; eassumption.
  * specialize (H0 n H). auto.
Qed.

Lemma closlist_scope Γ ext :
  (forall i : nat,
  i < length ext ->
  EXP length ext + nth i (map (snd ∘ fst) ext) 0 + Γ
  ⊢ nth i (map snd ext) (` VNil))
  ->
  Forall (fun v : Val => VAL Γ ⊢ v) (convert_to_closlist ext).
Proof.
  intros. rewrite indexed_to_forall. Unshelve. 2: exact VNil.
  intros.
  unfold convert_to_closlist in *.
  rewrite map_length in H0. apply H in H0 as H0'.
  replace 0 with ((snd ∘ fst) (0, 0, `VNil)) in H0' by auto.
  replace (`VNil) with (snd (0, 0, `VNil)) in H0' by auto.
  do 2 rewrite map_nth in H0'. simpl in H0'.
  rewrite nth_indep with (d' := VClos ext 0 0 (`VNil)).
  2: now rewrite map_length.
  remember (fun '(y, e) => let '(id, vc) := y in VClos ext id vc e) as F.
  replace (VClos ext 0 0 (`VNil)) with (F (0, 0, `VNil)) by (subst;auto).
  rewrite map_nth. subst.
  destruct (nth i ext (0, 0, ` VNil)). destruct p; cbn in *.
  constructor; auto.
Qed.
