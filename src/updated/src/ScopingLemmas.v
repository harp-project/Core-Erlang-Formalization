Require Export Manipulation.

(** This Definition helps with declaring lemmas. It means if for all v input parameter that are smaller then a given Γ, Substitution ξ will return with the same v (v here is in (ValueExpression + nat)).*)
Definition subst_preserves (Γ : nat) (ξ : Substitution) : Prop :=
  forall v, v < Γ -> ξ v = inr v.

(** This Theorem means that if for a given Γ (nat), Substitution ξ returns the input for every input that are smaller than Γ, than for S Γ (nat that are one value bigger tan Γ) Substitution up_subst ξ (ξ exept returns one value bigger numbers) will be in the same relation.*)
Theorem subst_preserves_up : forall Γ ξ,
  subst_preserves Γ ξ -> subst_preserves (S Γ) (up_subst ξ).
Proof.
  intros. unfold subst_preserves in *. intros. unfold up_subst. destruct v; auto.
  apply Lt.lt_S_n in H0. apply H in H0. unfold shift. rewrite H0. auto.
Qed.

Global Hint Resolve subst_preserves_up : core.

(** This Theorem means that if for a given Γ (nat), Substitution ξ returns the input for every input that are smaller than Γ, than for (n + Γ) (nat that are n value bigger tan Γ) Substitution (upn n ξ) (ξ exept returns n value bigger numbers) will be in the same relation.*)
Corollary subst_preserves_upn : forall n Γ ξ,
  subst_preserves Γ ξ -> subst_preserves (n + Γ) (upn n ξ).
Proof.
  induction n; intros.
  * simpl. auto.
  * simpl. apply subst_preserves_up, IHn. auto.
Qed.

Global Hint Resolve subst_preserves_upn : core.

(** This Theorem means that *)
Theorem subst_preserves_empty ξ : subst_preserves 0 ξ.
Proof. intro. intros. inversion H. Qed.

Global Hint Resolve subst_preserves_empty : core.

(*
Theorem scoped_ignores_sub_helper vals : forall l ξ,
  (forall i : nat,
     i < Datatypes.length vals ->
     forall ξ : Substitution,
     subst_preserves l ξ -> subst ξ (Val (nth i vals (VLit (Integer 0)))) = (Val (nth i vals (VLit (Integer 0))))) ->
  subst_preserves l ξ ->
  (map (subst ξ) vals) = vals.
Proof.
  induction vals; intros.
  * reflexivity.
  * simpl. epose (H 0 _ _ H0). simpl in e. rewrite e.
    erewrite IHvals; eauto. intros. eapply (H (S i)). simpl. lia. auto.
Unshelve. simpl. lia.
Qed.
*)

Check scoped_ind.
Check indexed_to_forall.

(** This theorem says that if an expression is scoped in Γ then every substitution ξ that subst_preserves with this Γ (So for every v input that are smaller than Γ will return v) if e is substituted with such a ξ Substitution it will remain the same e Expression.*)
Theorem scoped_ignores_sub :
  (forall e Γ, EXP  Γ ⊢ e -> forall ξ, subst_preserves Γ ξ -> e.[ξ] = e) /\
  (forall e Γ, VAL  Γ ⊢ e -> forall ξ, subst_preserves Γ ξ -> e.[ξ]ᵥ = e) /\
  (forall e Γ, NVAL Γ ⊢ e -> forall ξ, subst_preserves Γ ξ -> e.[ξ]ₑ = e).
Proof.
  apply scoped_ind.
  * intros. simpl. rewrite H.
    - reflexivity.
    - exact H0.
  * intros. simpl. rewrite H.
    - reflexivity.
    - exact H0.
  * intros. simpl. reflexivity.
  * intros. simpl. reflexivity.
  * intros. simpl. specialize (H v). rewrite H.
    - reflexivity.
    - exact g.
  * intros. simpl. specialize (H fi). rewrite H.
    - reflexivity.
    - exact g.
  * intros. simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - rewrite indexed_to_forall with (def := VNil). intros. apply H.
      + exact H1.
      + exact H0.
  * intros. simpl. rewrite H0.
    - rewrite H.
      + reflexivity.
      + exact H1.
    - exact H1.
  (* * intros. simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - rewrite indexed_to_forall with (def := (VNil,VNil)). intros. specialize (H i H2).
      specialize (H0 i H2). destruct (nth i l) eqn:Eq. unfold id. simpl in *. rewrite H.
      + rewrite H0. 
        ** reflexivity. 
        ** exact H1.
      + exact H1. *)
 (* This needed a rewrite afther the map fst l, type of rewrites in the scoping. The new proof is below.*)
  * intros. simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - rewrite indexed_to_forall with (def := (VNil,VNil)). intros. specialize (H i H2).
      specialize (H0 i H2). destruct (nth i l) eqn:Eq. unfold id. specialize (H ξ). specialize (H H1).
      f_equal. (*apply pair_equal_spec. split.*)
      + Search nth. replace VNil with (fst (VNil,VNil)) in H. rewrite map_nth in H.
        rewrite Eq in H. simpl in H. exact H. simpl. reflexivity.
      + admit.
      rewrite H.
  * intros. simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - rewrite indexed_to_forall with (def := VNil). intros. unfold id. specialize (H i H1). rewrite H.
      + reflexivity.
      + exact H0.
  * intros. simpl. erewrite map_ext_Forall  with (g := Datatypes.id).
    - rewrite H0. rewrite map_id. reflexivity. apply subst_preserves_upn. exact H1.
    - rewrite indexed_to_forall with (def := (0,0,Val VNil)). intros. specialize (H i H2).
      unfold Datatypes.id. destruct (nth i ext) eqn:Eq. destruct p eqn:Eq2. simpl in *.
      rewrite H.
      + reflexivity.
      + apply subst_preserves_upn. exact H1.
  * intros. simpl. specialize (H (upn vl ξ)). rewrite H.
    - reflexivity.
    - apply subst_preserves_upn. exact H0.
  * intros. simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - rewrite indexed_to_forall with (def := (Val VNil)). intros. specialize (H i H1). rewrite H.
      + unfold id. reflexivity.
      + exact H0.
  * intros. simpl. rewrite H.
    - rewrite H0.
      + reflexivity.
      + exact H1.
    - exact H1.
  * intros. simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - rewrite indexed_to_forall with (def := (Val VNil,Val VNil)). intros. specialize (H i H2).
      specialize (H0 i H2). destruct (nth i l) eqn:Eq. unfold id. simpl in *. rewrite H.
      + rewrite H0.
          ** reflexivity.
          ** exact H1.
      + exact H1.
  * intros. simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - rewrite indexed_to_forall with (def := (Val VNil)). intros. unfold id. specialize (H i H1).
      rewrite H.
      + reflexivity.
      + exact H0.
  * intros. simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - rewrite indexed_to_forall with (def := (Val VNil)). intros. unfold id. specialize (H i H1). 
      rewrite H.
      + reflexivity.
      + exact H0.
  * intros. simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - rewrite indexed_to_forall with (def := (Val VNil)). intros. unfold id. specialize (H i H1).
      rewrite H.
      + reflexivity.
      + exact H0.
  * intros. simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. rewrite H.
      + reflexivity.
      + exact H1.
    - rewrite indexed_to_forall with (def := (Val VNil)). intros. unfold id. specialize (H0 i H2). 
      rewrite H0.
      + reflexivity.
      + exact H1.
  * intros. simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. rewrite H.
      + reflexivity.
      + exact H2.
    - rewrite indexed_to_forall with (def := (nil,Val VNil,Val VNil)). intros. unfold id.
      specialize (H0 i H3). specialize (e1 i H3). specialize (H1 i H3).
      destruct (nth i l) eqn:Eq. destruct p eqn:Eq2. simpl in *. rewrite H0.
      + rewrite H1.
        ** reflexivity.
        ** apply subst_preserves_upn. exact H2.
      + apply subst_preserves_upn. exact H2.
  * intros. simpl. rewrite H.
    - rewrite H0.
      + reflexivity.
      + apply subst_preserves_upn. exact H1.
    - exact H1.
  * intros. simpl. rewrite H.
    - rewrite H0.
      + reflexivity.
      + exact H1.
    - exact H1.
  * intros. simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. rewrite H0.
      + reflexivity.
      + apply subst_preserves_upn. exact H1.
    - rewrite indexed_to_forall with (def := (0,Val VNil)). intros. unfold id.
      specialize (H i H2). specialize (e0 i H2). destruct (nth i l) eqn:Eq. simpl in *.
      rewrite H.
      + reflexivity.
      + apply subst_preserves_upn. exact H1.
  * intros. simpl. rewrite H.
    - rewrite H0.
      + rewrite H1.
        ** reflexivity.
        ** apply subst_preserves_upn. exact H2.
      + apply subst_preserves_upn. exact H2.
    - exact H2.
Qed.

(** This Corollary says that if an e Expression is scoped in 0, so the Expression is closed (has no free variables), then substituting in it with any ξ Substitution will return the original e Expression. (will not change it)*)
Corollary eclosed_ignores_sub :
  forall e ξ,
  EXPCLOSED e -> subst ξ e = e.
Proof.
  intros. eapply scoped_ignores_sub with (Γ := 0); auto.
Qed.


(** This Corollary says that if an e Value Expression is scoped in 0, so the Value Expression is closed (has no free variables), then Substituting in it with any ξ Substitution will return the original e Value Expression. (will not change it)*)
Corollary vclosed_ignores_sub :
  forall e ξ,
  VALCLOSED e -> substVal ξ e = e.
Proof.
  intros. pose proof scoped_ignores_sub as [_ [Hs _]]. specialize (Hs e 0). apply Hs.
  - exact H.
  - apply subst_preserves_empty.
Qed.

(** This Corollary says that if an e Non Value Expression is scoped in 0, so the Non Value Expression is closed (has no free variables), then Substituting in it with any ξ Substitution will return the original e Non Value Expression. (will not change it)*)
Corollary nvclosed_ignores_sub :
  forall e ξ,
  NONVALCLOSED e -> substNonVal ξ e = e.
Proof.
  intros. pose proof scoped_ignores_sub as [_ [_ Hs]]. specialize (Hs e 0). apply Hs.
  - exact H.
  - apply subst_preserves_empty.
Qed.

Global Hint Resolve eclosed_ignores_sub : core.

Global Hint Resolve vclosed_ignores_sub : core.

Global Hint Resolve nvclosed_ignores_sub : core.


(** This Theorem says that if an e expression is scoped in Γ then it is also scoped in (S Γ), a one increment bigger value. So the scoping can be extended. The same for Value and Non Value Expressions.*)
Theorem scope_ext :
  (forall e Γ, EXP Γ ⊢ e  ->  EXP (S Γ) ⊢ e) /\
  (forall e Γ, VAL Γ ⊢ e  ->  VAL (S Γ) ⊢ e) /\
  (forall e Γ, NVAL Γ ⊢ e ->  NVAL (S Γ) ⊢ e).
Proof.
  Check scoped_ind. eapply scoped_ind.
  * intros. constructor. exact H.
  * intros. constructor. exact H.
  * intros. apply scoped_nil.
  * intros. constructor.
  * intros. constructor. auto.
  * intros. constructor. auto.
  * intros. constructor. exact H.
  * intros. constructor.
    - exact H.
    - exact H0.
  * intros. constructor.
    - exact H.
    - exact H0.
  * intros. constructor. exact H.
  * intros. constructor.
    - auto.
    - intros. specialize (H i H1). Search S "+". rewrite Nat.add_succ_r. exact H.
    - rewrite Nat.add_succ_r. exact H0.
  * intros. constructor. rewrite Nat.add_succ_r. exact H.
  * intros. constructor. exact H.
  * intros. constructor.
    - exact H.
    - exact H0.
  * intros. constructor.
    - exact H.
    - exact H0.
  * intros. constructor. exact H.
  * intros. constructor. exact H.
  * intros. constructor. exact H.
  * intros. constructor.
    - exact H.
    - exact H0.
  * intros. constructor.
    - exact H.
    - intros. rewrite Nat.add_succ_r. apply H0. exact H2.
    - intros. rewrite Nat.add_succ_r. apply H1. exact H2.
  * intros. constructor.
    - exact H.
    - rewrite Nat.add_succ_r. exact H0.
  * intros. constructor.
    - exact H.
    - exact H0.
  * intros. constructor.
    - intros. rewrite Nat.add_succ_r. apply H. exact H1.
    - rewrite Nat.add_succ_r. exact H0.
  * intros. constructor.
    - exact H.
    - rewrite Nat.add_succ_r. exact H0.
    - rewrite Nat.add_succ_r. exact H1.
Qed.


(** This Corollary says that if an e Expression is scoped in Γ then it is also scoped in (S Γ), a one increment bigger value. So the scoping can be extended. *)
Corollary scope_ext_Exp : forall {e Γ},
    EXP Γ ⊢ e -> EXP S Γ ⊢ e.
Proof.
  intros.
  apply scope_ext.
  auto.
Qed.

(** This Corollary says that if an e Value Expression is scoped in Γ then it is also scoped in (S Γ), a one increment bigger value. So the scoping can be extended. *)
Corollary scope_ext_Val : forall {e Γ},
    VAL Γ ⊢ e -> VAL S Γ ⊢ e.
Proof.
  intros.
  apply scope_ext.
  auto.
Qed.

(** This Corollary says that if an e Non Value Expression is scoped in Γ then it is also scoped in (S Γ), a one increment bigger value. So the scoping can be extended. *)
Corollary scope_ext_NonVal : forall {e Γ},
    NVAL Γ ⊢ e -> NVAL S Γ ⊢ e.
Proof.
  intros.
  apply scope_ext.
  auto.
Qed.

(** This Corollary says that for any Γ' and Γ number if Γ <= Γ' and an e Expression is scoped in Γ then it is also scoped in Γ'.*)
Corollary scope_ext_app : forall Γ' Γ, Γ <= Γ' ->
  (forall e, VAL Γ ⊢ e -> VAL Γ' ⊢ e) /\
  forall e, EXP Γ ⊢ e -> EXP Γ' ⊢ e.
Proof.
 intros. induction H.
 * intuition.
 * split; intros; eapply scope_ext; eapply IHle; auto. 
Qed.

(** This Definition describes that a ξ Substitution is subscoped with Γ Γ' numbers if, for all input number of ξ Substitution that is smaller than Γ, if the substitution returns an expression it will be an expression that is sopen in Γ', or if it returns a nuber it will be smaller than Γ'.*)
Definition subscoped (Γ Γ' : nat) (ξ : Substitution) : Prop :=
  forall v, v < Γ -> (match ξ v with
                      | inl exp => VAL Γ' ⊢ exp
                      | inr num => num < Γ'  (** in case of identity subst *)
                      end).

Notation "'SUBSCOPE' Γ ⊢ ξ ∷ Γ'" := (subscoped Γ Γ' ξ)
         (at level 69, ξ at level 99, no associativity).

(** This Definition describes that a ξ Renaming is renscoped with Γ Γ' numbers if, for all input number of ξ Renaming that is smaller than Γ, the renaming returns a nuber that is smaller than Γ'.*)
Definition renscoped (Γ : nat) (Γ' : nat) (ξ : Renaming) : Prop :=
  forall v, v < Γ -> (ξ v) < Γ'.

Notation "'RENSCOPE' Γ ⊢ ξ ∷ Γ'" := (renscoped Γ Γ' ξ)
         (at level 69, ξ at level 99, no associativity).

(** This Lemma says that id as a renaming is renscoped with Γ and Γ.*)
Lemma renscope_id Γ : RENSCOPE Γ ⊢ id ∷ Γ.
Proof.
  firstorder.
Qed.

Global Hint Resolve renscope_id : core.

(** This Lemma says that the idsubst Substitution is subscoped with Γ and Γ.*)
Lemma scope_idsubst Γ : SUBSCOPE Γ ⊢ idsubst ∷ Γ.
Proof.
  firstorder.
Qed.

Global Hint Resolve scope_idsubst : core.

(** This Lemma says taht if a ξ renaming is renscoped with Γ Γ', then the upren ξ Renameing (ξ but returns an increment bigger value for every input) is renscoped with (S Γ) (S Γ')*)
Lemma upren_scope : forall Γ Γ' ξ,
  RENSCOPE Γ ⊢ ξ ∷ Γ' ->
  RENSCOPE (S Γ) ⊢ upren ξ ∷ (S Γ').
Proof.
  intros.
  unfold renscoped in *.
  intros.
  revert ξ Γ Γ' H H0.
  induction v;
    intros;
    simpl;
    firstorder using Nat.succ_lt_mono.
    lia.
  apply -> Nat.succ_lt_mono. apply H. lia.
Qed.

(** This Lemma says taht if a ξ renaming is renscoped with Γ Γ', then the uprenn Γ'' ξ Renameing (ξ but returns a +Γ'' bigger value for every input) is renscoped with (Γ'' + Γ) (Γ'' + Γ')*)
Lemma uprenn_scope : forall Γ'' Γ Γ' ξ,
  RENSCOPE Γ ⊢ ξ ∷ Γ' ->
  RENSCOPE (Γ'' + Γ) ⊢ uprenn Γ'' ξ ∷ (Γ'' + Γ').
Proof.
  induction Γ''; intros.
  * repeat rewrite Nat.add_0_l. apply H.
  * repeat rewrite Nat.add_succ_l. apply upren_scope. apply IHΓ''. auto.
Qed.

Global Hint Resolve upren_scope : core.
Global Hint Resolve uprenn_scope : core.

(*
Lemma ren_preserves_scope : forall e Γ,
    (EXP Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       EXP Γ' ⊢ rename ξ e) /\
    (VAL Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       VAL Γ' ⊢ rename ξ e).
Proof.
  induction e using Exp_ind2 with
  (Q := fun l => Forall (fun e => forall Γ,(EXP Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       EXP Γ' ⊢ rename ξ e) /\
    (VAL Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       VAL Γ' ⊢ rename ξ e)) l);
  try (intros Γ;
  split;
  split;
  intros; cbn; unfold renscoped in * ).
  1-4: constructor. 1-2: constructor.
  1, 5, 7: repeat constructor; try apply H0; try inversion H; try inversion H1; auto.
  all: (** this solves around half the goals *)
    try (specialize (H Γ id (renscope_id _)); rewrite idrenaming_is_id in H; apply H).
  all: try (inversion H; inversion H1).
  * constructor. apply H0. inversion H. auto.
  * constructor. constructor. inversion H; inversion H1. subst.
    eapply IHe; eauto. intros. pose (uprenn_scope (S (length vl)) _ Γ' ξ H0 v H2). auto.
  * constructor. inversion H. subst.
    eapply IHe; eauto. intros. pose (uprenn_scope (S (length vl)) _ Γ' ξ H0 v H1). auto.
  * subst. constructor.
    - eapply IHe; eauto.
    - intros. rewrite indexed_to_forall in IHe0.
      replace (ELit 0) with (rename ξ (ELit 0)) by auto.
      rewrite map_nth. rewrite map_length in H1. eapply IHe0; eauto.
  * subst. constructor.
    - eapply IHe1; eauto.
    - eapply IHe2; eauto. intros. eapply upren_scope; eauto.
  * subst. constructor.
    - eapply IHe1; eauto. intros. eapply upren_scope; eauto.
    - eapply IHe2; eauto. intros. eapply upren_scope; eauto.
  * subst. constructor.
    - eapply IHe1; eauto.
    - eapply IHe2; eauto.
  * subst. constructor.
    - eapply IHe1; eauto.
    - eapply IHe2; eauto. intros. eapply uprenn_scope; eauto.
    - eapply IHe3; eauto.
  * subst. constructor.
    - eapply IHe1; eauto.
    - eapply IHe2; eauto.
  * do 2 constructor.
  * constructor.
  * subst. apply scoped_val, vscoped_cons.
    - eapply IHe1; eauto.
    - eapply IHe2; eauto.
  * subst. constructor.
    - eapply IHe1; eauto.
    - eapply IHe2; eauto.
  * constructor; eauto.
  * constructor.
Qed.*)

Search map.

(*
Lemma hlp_plz :
  forall i l f f' Z Z', i < length l -> 
  (nth i (map f (map fst l)) Z)
  =
  (fst (nth i (map (fun '(x, y) => (f x, f' y)) l) (Z,Z'))).
Qed.
Admitted.
*)

(** This Lemma says that if an e Expression is scoped in Γ then, if a ξ Renameing is renscoped whith this Γ and another Γ' (so for all input number of ξ that is smaller than Γ, the renaming returns a nuber that is smaller than Γ'), then e renamed with this ξ is scoped in Γ'. And this also holds the other way araund. *)
Lemma ren_preserves_scope :
    (forall e Γ, EXP Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       EXP Γ' ⊢ rename ξ e) /\
       
    (forall e Γ, NVAL Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       NVAL Γ' ⊢ renameNonValue ξ e) /\
       
    (forall e Γ, VAL Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       VAL Γ' ⊢ renameValue ξ e).
Proof.
    Check Exp_ind.
   eapply Exp_ind with
    (QV := fun l => Forall (fun e => forall Γ, VAL Γ ⊢ e <->
    forall (Γ' : nat) (ξ : Renaming),
    RENSCOPE Γ ⊢ ξ ∷ Γ' -> VAL Γ' ⊢ renameValue ξ e) l)
    (*
   (RV := fun l => forall i, i < length l -> 
    (forall Γ, VAL Γ ⊢ fst (nth i l (VNil, VNil)) <->
      forall (Γ' : nat) (ξ : Renaming), RENSCOPE Γ ⊢ ξ ∷ Γ' -> VAL Γ' ⊢ renameValue ξ (fst (nth i l (VNil, VNil))))
    /\ 
    (forall Γ, VAL Γ ⊢ snd (nth i l (VNil, VNil)) <->
     forall (Γ' : nat) (ξ : Renaming), RENSCOPE Γ ⊢ ξ ∷ Γ' -> VAL Γ' ⊢ renameValue ξ (snd (nth i l (VNil, VNil))))) *) 
  (RV := fun l => forall i, i < length l -> 
    (forall Γ, VAL Γ ⊢ (nth i (map fst l) (VNil)) <->
      forall (Γ' : nat) (ξ : Renaming), RENSCOPE Γ ⊢ ξ ∷ Γ' -> VAL Γ' ⊢ renameValue ξ    (nth i (map fst l) (VNil)))
    /\ 
    (forall Γ, VAL Γ ⊢  (nth i (map snd l) (VNil)) <->
     forall (Γ' : nat) (ξ : Renaming), RENSCOPE Γ ⊢ ξ ∷ Γ' -> VAL Γ' ⊢ renameValue ξ  (nth i (map snd l) (VNil)))).
  * intros. simpl. split.
    - intros. inversion H0. subst. specialize (H Γ). destruct H. constructor. apply H.
      + exact H3.
      + exact H1.
    - intros. constructor. specialize (H Γ). destruct H. apply H1.
      intros. apply H0 in H2. inversion H2. exact H4.
  * intros. simpl. split.
    - intros. inversion H0. subst. specialize (H Γ). destruct H. constructor. apply H.
      + exact H3.
      + exact H1.
    - intros. constructor. specialize (H Γ). destruct H. apply H1.
      intros. apply H0 in H2. inversion H2. exact H4.
  * intros. simpl. split.
    - intros. constructor.
    - intros. constructor.
  * intros. simpl. split.
    - intros. constructor.
    - intros. constructor.
  * intros. simpl. split.
    - intros. constructor.
      + specialize (H Γ). destruct H. apply H.
        ** inversion H1. exact H6.
        ** exact H2.
      + specialize (H0 Γ). destruct H0. apply H0.
        ** inversion H1. exact H8.
        ** exact H2.
    - intros. constructor.
      + specialize (H Γ). destruct H. apply H2. intros. specialize (H1 _ _ H3).
        inversion H1. exact H6.
      + specialize (H0 Γ). destruct H0. apply H2. intros. specialize (H1 _ _ H3).
        inversion H1. exact H8.
  * intros. split.
    - intros. simpl. constructor. inversion H0. subst. intros.
      rewrite indexed_to_forall with (def := (VNil)) in H. rewrite map_length in H2.
      specialize (H i H2 Γ). destruct H. specialize (H3 i H2). specialize (H H3).
      specialize (H _ _ H1). Check map_nth. rewrite <- map_nth in H.
      exact H.
    - intros. constructor. rewrite indexed_to_forall with (def := (VNil)) in H.
      intros. specialize (H i H1 Γ). destruct H. apply H2. intros.
      specialize (H0 _ _ H3). simpl in H0. inversion H0. subst. rewrite <- map_nth.
      apply H5. rewrite map_length. exact H1.
  * intros. split.
    - intros.
      inversion H0. subst. simpl. constructor.
        + intros. rewrite map_length in H2.  specialize (H i H2).
          destruct H. specialize (H Γ). destruct H.
          apply H3 in H2 as H2'. specialize (H H2'). specialize (H Γ' ξ). specialize (H H1).
          rewrite map_map. rewrite <- map_nth in H. simpl in H. rewrite map_map in H.
          (* you can proove the eqvivalence of these functions. *)
          replace ((fun x : ValueExpression * ValueExpression =>
        fst (let '(x0, y) := x in (renameValue ξ x0, renameValue ξ y)))) with
        (fun x : ValueExpression * ValueExpression => renameValue ξ (fst x)).
        2: { apply functional_extensionality. intros x. extensionality x. destruct x. simpl. auto. }
        exact H.
        (* indukció a lista elemeire *)
          (*clear H6 H5 H0 H1 H2' H3 H4. generalize dependent i. induction l.
          ** intros. inversion H2.
          ** intros. simpl. destruct i.
            *** destruct a. simpl. simpl in H. exact H.
            *** apply IHl.
              **** exact H.
              **** simpl in H2. lia. *)
          specialize (H5 Γ'). destruct H5. Check map_nth. (* rewrite <- map_nth. *)
          replace (nth i (map (fun '(x, y) => (renameValue ξ x, renameValue ξ y)) l) (VNil, VNil)) with (nth i l (VNil, VNil)).
          ** apply H6. intros. specialize (H4 i H2). admit. (*specialize (H5 H4).*)
          ** admit.
    - intros. constructor.
      + intros. specialize (H i H1). destruct H. specialize (H Γ). destruct H.
        apply H3. intros. specialize (H0 _ _ H4). simpl in H0. inversion H0. subst.
        rewrite <- map_nth. rewrite <- map_nth. simpl. specialize (H6 i).
        rewrite map_length in H6. specialize (H6 H1).
        rewrite <- map_nth in H6. rewrite <- map_nth in H6. rewrite <- map_nth.
        simpl in H6.
        (* I need the fst before the nth rather then on l *)
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * intros. split.
    - intros. simpl. constructor.
      + intros. inversion H1.
      + intros. inversion H1.
    - admit.
  * intros. split.
    - intros.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  
Qed.

(** This Lemma comes from ren_preserves_scope but stated only for Expressions. Using this Lemma in proofs might be more convinient in some cases.*)
Lemma ren_preserves_scope_exp : forall e Γ,
    (EXP Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       EXP Γ' ⊢ rename ξ e).
Proof.
  intros.
  apply ren_preserves_scope.
Qed.

(** This Lemma comes from ren_preserves_scope but stated only for Value Expressions. Using this Lemma in proofs might be more convinient in some cases.*)
Lemma ren_preserves_scope_val : forall e Γ,
    (VAL Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       VAL Γ' ⊢ renameValue ξ e).
Proof.
  intros.
  apply ren_preserves_scope.
Qed.

(** This Lemma comes from ren_preserves_scope but stated only for Non Value Expressions. Using this Lemma in proofs might be more convinient in some cases.*)
Lemma ren_preserves_scope_nval : forall e Γ,
    (NVAL Γ ⊢ e <->
     forall Γ' ξ,
       RENSCOPE Γ ⊢ ξ ∷ Γ' ->
       NVAL Γ' ⊢ renameNonValue ξ e).
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
  destruct v; intros.
  * simpl. lia.
  * simpl. unfold shift. break_match_goal. break_match_hyp.
    - inversion Heqs. eapply ren_preserves_scope_val with (Γ:= Γ'); eauto.
      + epose (H v _). rewrite Heqs0 in y. auto. Unshelve. lia.
      + intro. intros. lia.
    - inversion Heqs.
    - break_match_hyp.
      + inversion Heqs.
      + inversion Heqs. subst. epose (H v _). rewrite Heqs0 in y. lia. Unshelve. lia.
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
  intros. destruct v0.
  * simpl. auto.
  * simpl. apply H0. lia.
Qed.


Lemma consn_scope : forall (vals : list ValueExpression) Γ Γ' (ξ : Substitution),
    Forall (fun v => VAL Γ' ⊢ v) vals ->
    SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
    SUBSCOPE length vals + Γ ⊢ fold_right (fun v acc => v .: acc) ξ vals ∷ Γ'.
Proof.
  induction vals; intros.
  * simpl. auto.
  * simpl. inversion H. apply cons_scope; auto.
Qed.

Global Hint Resolve cons_scope : core.
Global Hint Resolve consn_scope : core.

(** Substitution is scope-preserving. *)
(*Lemma subst_preserves_scope : forall e Γ,
    (EXP Γ ⊢ e <->
     forall Γ' ξ,
       SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
       EXP Γ' ⊢ e.[ξ]) /\
    (VAL Γ ⊢ e <->
     forall Γ' ξ,
       SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
       VAL Γ' ⊢ e.[ξ]).
Proof.
  induction e using Exp_ind2 with
  (Q := fun l => forall Γ,
  Forall (fun e => (EXP Γ ⊢ e <->
     forall Γ' ξ,
       SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
       EXP Γ' ⊢ e.[ξ]) /\
    (VAL Γ ⊢ e <->
     forall Γ' ξ,
       SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
       VAL Γ' ⊢ e.[ξ])) l);
    try intros Γ;
    try split;
    try split;
    intros.
  all: cbn; unfold subscoped in *.
  1-4: repeat constructor.
  all: try (inversion H); try inversion H1; subst. (** cleaup contradictions *)
  (** prove backward directions: *)
  all: try (specialize (H Γ idsubst (scope_idsubst _)); rewrite idsubst_is_id in H; auto).
  (** forward: *)
  * specialize (H0 n H4). break_match_goal.
    - constructor. auto.
    - constructor. constructor. auto.
  * specialize (H0 n H2). break_match_goal.
    - auto.
    - constructor. auto.
  * specialize (H0 n H4). break_match_goal.
    - constructor. auto.
    - constructor. constructor. auto.
  * specialize (H0 n H2). break_match_goal.
    - auto.
    - constructor. auto.
  * constructor. constructor. eapply IHe; eauto. intros.
    eapply up_scope; eauto.
  * constructor. eapply IHe; eauto. intros.
    eapply up_scope; eauto.
  * constructor.
    - eapply IHe; eauto.
    - replace (ELit 0) with (subst ξ (ELit 0)) by reflexivity. intros.
      specialize (IHe0 Γ).
      rewrite map_nth. rewrite indexed_to_forall in IHe0. rewrite map_length in H1.
      eapply IHe0; eauto.
  * constructor.
    - eapply IHe1; eauto.
    - eapply IHe2; eauto. apply up_scope. auto.
  * constructor.
    - eapply IHe1; eauto. apply up_scope. auto.
    - eapply IHe2; eauto. apply up_scope. auto.
  * constructor.
    - eapply IHe1; eauto.
    - eapply IHe2; eauto.
  * constructor.
    - eapply IHe1; eauto.
    - eapply IHe2; eauto. apply upn_scope. auto.
    - eapply IHe3; eauto.
  * constructor.
    - eapply IHe1; eauto.
    - eapply IHe2; eauto.
  * do 2 constructor.
  * constructor.
  * do 2 constructor.
    - eapply IHe1; eauto.
    - eapply IHe2; eauto.
  * constructor.
    - eapply IHe1; eauto.
    - eapply IHe2; eauto.
  * constructor; auto.
  * constructor.
Qed.*)

(* TODO: Ez kell e?*)
Lemma val_exp_scope :
  forall v Γ, EXP Γ ⊢ Val v -> VAL Γ ⊢ v.
Proof.
  intros. inversion H. exact H1.
Qed.

(* TODO: Ez kell e?*)
Lemma substexp_to_substval :
  forall v Γ ξ, EXP Γ ⊢ (Val v).[ξ] -> VAL Γ ⊢ v.[ξ]ᵥ.
Proof.
  intros. inversion H. exact H1.
Qed.

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
  eapply Exp_ind.
  * intros. split.
    - specialize (H Γ). destruct H. intros. simpl. constructor. apply H.
      + inversion H1. subst. exact H4.
      + exact H2.
    - intros. specialize (H Γ). destruct H. constructor. apply H1. intros.
      specialize (H0 _ _ H2). simpl in H0. inversion H0. subst. exact H4.
  * intros. split.
    - intros. inversion H0. subst. specialize (H Γ). inversion H. inversion H2.
Qed.


(* ----------------------------------------------------------------------------- *)

Lemma subst_preserves_scope_exp : forall e Γ,
    EXP Γ ⊢ e <->
    forall Γ' ξ,
      SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
      EXP Γ' ⊢ e.[ξ].
Proof.
  intros.
  apply subst_preserves_scope.
Qed.

Lemma subst_preserves_scope_val : forall e Γ,
    VAL Γ ⊢ e <->
    forall Γ' ξ,
      SUBSCOPE Γ ⊢ ξ ∷ Γ' ->
      VAL Γ' ⊢ e.[ξ].
Proof.
  intros.
  apply subst_preserves_scope.
Qed.

Module SUB_IMPLIES_SCOPE.
  Definition magic_ξ (Γ Γ' : nat) (n : nat) : Exp + nat :=
    if Compare_dec.lt_dec n Γ
    then if Compare_dec.lt_dec n Γ'
         then inr n
         else inl (ELit 0)
    else inr Γ'.

  Lemma magic_ξ_scope : forall Γ Γ', SUBSCOPE Γ ⊢ magic_ξ Γ Γ' ∷ Γ'.
  Proof.
    unfold subscoped.
    intros.
    unfold magic_ξ.
    repeat destruct Compare_dec.lt_dec; try congruence.
    constructor.
  Qed.

  Lemma up_magic Γ Γ': up_subst (magic_ξ Γ Γ') = magic_ξ (S Γ) (S Γ').
  Proof.
    extensionality x.
    unfold magic_ξ, up_subst.
    destruct x; cbn; auto.
    unfold shift. repeat destruct Compare_dec.lt_dec; auto; lia.
  Qed.

  Lemma upn_magic : forall n Γ Γ', upn n (magic_ξ Γ Γ') = magic_ξ (n + Γ) (n + Γ').
  Proof.
    induction n; intros; simpl; auto.
    rewrite <- up_magic, IHn. auto.
  Qed.

  Lemma magic_ξ_implies_scope : forall e Γ Γ',
      (EXP Γ' ⊢ e.[magic_ξ Γ Γ'] ->
       EXP Γ ⊢ e) /\
      (VAL Γ' ⊢ e.[magic_ξ Γ Γ'] ->
       VAL Γ ⊢ e).
  Proof.
    induction e using Exp_ind2 with
    (Q := fun l =>
      Forall (fun e => forall Γ Γ', (EXP Γ' ⊢ e.[magic_ξ Γ Γ'] ->
       EXP Γ ⊢ e) /\
      (VAL Γ' ⊢ e.[magic_ξ Γ Γ'] ->
       VAL Γ ⊢ e)) l);
      try intros Γ Γ';
      try split;
      intros;
      try cbn in H.
    1-2, 4, 6, 8: constructor.
    constructor.
    * break_match_hyp; 
       (unfold magic_ξ in Heqs; break_match_hyp; [ auto | try congruence ]).
       inversion H. inversion H0. subst. inversion Heqs. subst. lia.
    * break_match_hyp; 
       (unfold magic_ξ in Heqs; break_match_hyp; [ auto | try congruence ]).
       inversion H. inversion H0. subst. inversion Heqs. subst. lia.
    * inversion H. inversion H0. subst.
      eapply IHe. rewrite upn_magic, up_magic in H1. eauto.
    * constructor. constructor. break_match_hyp; 
       (unfold magic_ξ in Heqs; break_match_hyp; [ auto | try congruence ]).
       inversion H. inversion H0. subst. inversion Heqs. subst. lia.
    * constructor. constructor. break_match_hyp; 
       (unfold magic_ξ in Heqs; break_match_hyp; [ auto | try congruence ]).
       inversion H. inversion H0. subst. inversion Heqs. subst. lia.
    * constructor. constructor. inversion H. inversion H0. subst.
      eapply IHe. replace (up_subst (upn (Datatypes.length vl) (magic_ξ Γ Γ'))) with
                          (upn (S (length vl)) ((magic_ξ Γ Γ'))) in H3 by reflexivity.
      rewrite upn_magic in H3. eauto.
    * inversion H. 2: inversion H0. constructor.
      - eapply IHe; eauto.
      - replace (ELit 0) with (subst (magic_ξ Γ Γ') (ELit 0)) in H3 by reflexivity.
        intros. erewrite <- map_length in H4. specialize (H3 i H4).
        rewrite map_nth in H3. subst. rewrite indexed_to_forall in IHe0.
        rewrite map_length in H4.
        eapply IHe0; eauto.
    * inversion H.
    * inversion H. 2: inversion H0. subst. constructor.
      - eapply IHe1; eauto.
      - eapply IHe2; eauto. rewrite up_magic in H4. eauto.
    * inversion H.
    * inversion H. 2: inversion H0. constructor.
      - eapply IHe1; eauto.
        replace (up_subst (upn (Datatypes.length vl) (magic_ξ Γ Γ'))) with
                (upn (S (length vl)) (magic_ξ Γ Γ')) in H2 by reflexivity.
        rewrite upn_magic in H2. exact H2.
      - eapply IHe2; eauto.
        rewrite up_magic in H5. exact H5.
    * inversion H.
    * inversion H. 2: inversion H0. constructor.
      - eapply IHe1; eauto.
      - eapply IHe2; eauto.
    * inversion H.
    * inversion H. 2: inversion H0. constructor.
      - eapply IHe1; eauto.
      - eapply IHe2; eauto.
        rewrite upn_magic in H5. exact H5.
      - eapply IHe3; eauto.
    * inversion H.
    * inversion H.
      - constructor.
        + eapply IHe1; eauto.
        + eapply IHe2; eauto.
      - inversion H0.
    * inversion H.
    * do 2 constructor.
    * constructor.
    * inversion H. inversion H0. subst. do 2 constructor.
      - eapply IHe1; eauto.
      - eapply IHe2; eauto.
    * inversion H. subst. constructor.
      - eapply IHe1; eauto.
      - eapply IHe2; eauto.
    * constructor; auto.
    * constructor.
  Qed.

  Lemma sub_implies_scope_exp : forall e Γ Γ',
      (forall ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ e.[ξ]) ->
      EXP Γ ⊢ e.
  Proof.
    intros;
    eapply magic_ξ_implies_scope;
    apply H;
    apply magic_ξ_scope.
  Qed.

  Lemma sub_implies_scope_val : forall e Γ Γ',
      (forall ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> VAL Γ' ⊢ e.[ξ]) ->
      VAL Γ ⊢ e.
  Proof.
    intros;
    eapply magic_ξ_implies_scope;
    apply H;
    apply magic_ξ_scope.
  Qed.

  Definition magic_ξ_2 Γ' :=
    fun n =>
      if Compare_dec.lt_dec n Γ'
      then idsubst n
      else if Nat.eq_dec n Γ'
           then inl (ELit 0)
           else idsubst (pred n).

  Lemma up_magic_2 : forall Γ,
      up_subst (magic_ξ_2 Γ) = magic_ξ_2 (S Γ).
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

  Lemma upn_magic_2 : forall n Γ,
    upn n (magic_ξ_2 Γ) = magic_ξ_2 (n + Γ).
  Proof.
    induction n; intros; cbn; auto.
    * rewrite <- up_magic_2, IHn. auto.
  Qed.

  Lemma magic_const : magic_ξ_2 0 = ELit 0 .: idsubst.
  Proof.
    unfold magic_ξ_2.
    extensionality x.
    destruct Compare_dec.lt_dec; unfold idsubst. inversion l.
    destruct Nat.eq_dec; subst; auto.
    destruct x; cbn; auto. lia.
  Qed.

  Lemma magic_ξ_magic_ξ_2 : forall e Γ',
      (EXP Γ' ⊢ e.[magic_ξ_2 Γ'] ->
       e.[magic_ξ (S Γ') Γ'] = e.[magic_ξ_2 Γ']) /\
      (VAL Γ' ⊢ e.[magic_ξ_2 Γ'] ->
       e.[magic_ξ (S Γ') Γ'] = e.[magic_ξ_2 Γ']).
  Proof.
    induction e using Exp_ind2 with
      (Q := fun l => forall Γ', Forall (fun e =>
        (EXP Γ' ⊢ e.[magic_ξ_2 Γ'] -> e.[magic_ξ (S Γ') Γ'] = e.[magic_ξ_2 Γ']) /\
        (VAL Γ' ⊢ e.[magic_ξ_2 Γ'] -> e.[magic_ξ (S Γ') Γ'] = e.[magic_ξ_2 Γ'])
      ) l); intros; cbn; auto.
    * unfold magic_ξ_2, magic_ξ, idsubst.
      repeat destruct Compare_dec.lt_dec; try destruct Nat.eq_dec; auto.
      lia. lia. lia. split; intros; inversion H. inversion H0. all: subst.
      all : lia.
    * unfold magic_ξ_2, magic_ξ, idsubst.
      repeat destruct Compare_dec.lt_dec; try destruct Nat.eq_dec; auto.
      lia. lia. lia. split; intros; inversion H. inversion H0. all: subst.
      all : lia.
    * rewrite upn_magic, up_magic, upn_magic_2, up_magic_2.
      replace (S (length vl + S Γ')) with (S (S (length vl) + Γ')) by lia.
      specialize (IHe (S (length vl + Γ'))). destruct IHe. split; intros.
      - rewrite <- H; auto. inversion H1. inversion H2. auto.
      - rewrite <- H; auto. inversion H1. subst. auto.
    * specialize (IHe Γ'). specialize (IHe0 Γ'). destruct IHe.
      split; intros; inversion H1; subst. 2: inversion H2. rewrite H; auto.
      apply Forall_and_inv in IHe0. destruct IHe0. erewrite map_ext_Forall. reflexivity.
      rewrite indexed_to_forall in *. intros. apply H2; auto.
      replace (ELit 0) with ((ELit 0).[magic_ξ_2 Γ']) in H5 by reflexivity.
      rewrite map_length in H5. specialize (H5 i H6). rewrite map_nth in H5.
      exact H5.
    * specialize (IHe1 Γ'). specialize (IHe2 (S Γ')). destruct IHe1, IHe2.
      split; intros; inversion H3; subst. 2: inversion H4.
      rewrite H; auto. rewrite up_magic, up_magic_2, H1; auto.
      now rewrite up_magic_2 in H8.
    * specialize (IHe1 (length vl + S Γ')). specialize (IHe2 (S Γ')).
      destruct IHe1, IHe2.
      split; intros; inversion H3; subst. 2: inversion H4.
      rewrite upn_magic, upn_magic_2, up_magic, up_magic_2.
      replace (S (Datatypes.length vl + Γ')) with (Datatypes.length vl + S Γ') by lia.
      rewrite H; auto. rewrite up_magic, up_magic_2, H1 in *; auto.
      rewrite upn_magic_2, up_magic_2 in H6. now rewrite <- Nat.add_succ_comm.
    * specialize (IHe1 Γ'). specialize (IHe2 Γ'). destruct IHe1, IHe2.
      split; intros; inversion H3; subst. 2: inversion H4. now rewrite H, H1.
    * rewrite upn_magic, upn_magic_2.
      specialize (IHe1 Γ'). specialize (IHe2 (pat_vars p + Γ')). specialize (IHe3 Γ').
      destruct IHe1, IHe2, IHe3.
      split; intros; inversion H5; subst. 2: inversion H6.
      rewrite <- plus_n_Sm.
      now rewrite H, H1, H3.
    * specialize (IHe1 Γ'). specialize (IHe2 Γ'). destruct IHe1, IHe2.
      split; intros; inversion H3; subst; try now rewrite H, H1.
    * specialize (IHe1 Γ'). specialize (IHe2 Γ'). destruct IHe1, IHe2.
      split; intros; inversion H3; inversion H4; subst; rewrite H0, H2; auto.
  Unshelve. exact (ELit 0).
  Qed.

  Lemma magic_ξ_magic_ξ_2_closed : forall e,
      (EXPCLOSED e.[ELit 0/] ->
       e.[magic_ξ 1 0] = e.[ELit 0 .: idsubst]) /\
      (VALCLOSED e.[ELit 0/] ->
       e.[magic_ξ 1 0] = e.[ELit 0 .: idsubst]).
  Proof.
    intros.
    rewrite <- magic_const.
    apply magic_ξ_magic_ξ_2.
  Qed.

  Lemma sub_implies_scope_exp_1 : forall e,
      EXPCLOSED e.[ELit 0/] ->
      EXP 1 ⊢ e.
  Proof.
    intros;
      eapply magic_ξ_implies_scope.
    destruct (magic_ξ_magic_ξ_2_closed e).
    rewrite H0; auto.
  Qed.

  Lemma sub_implies_scope_val_1 : forall e,
      VALCLOSED e.[ELit 0/] ->
      VAL 1 ⊢ e.
  Proof.
    intros;
      eapply magic_ξ_implies_scope.
    destruct (magic_ξ_magic_ξ_2_closed e).
    rewrite H1; auto.
  Qed.
End SUB_IMPLIES_SCOPE.

Definition subst_implies_scope_exp := SUB_IMPLIES_SCOPE.sub_implies_scope_exp.
Definition subst_implies_scope_val := SUB_IMPLIES_SCOPE.sub_implies_scope_val.
Definition subst_implies_scope_exp_1 := SUB_IMPLIES_SCOPE.sub_implies_scope_exp_1.
Definition subst_implies_scope_val_1 := SUB_IMPLIES_SCOPE.sub_implies_scope_val_1.

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

Corollary upn_ignores_sub : forall e Γ ξ,
     (EXP Γ ⊢ e -> e.[upn Γ ξ] = e) /\
     (VAL Γ ⊢ e -> e.[upn Γ ξ] = e).
Proof.
  intros. split; intros.
  * eapply scoped_ignores_sub; eauto. intro. intros. apply upn_Var. auto.
  * pose (scoped_ignores_sub Γ). destruct a. apply H0. auto.
    intro. intros. apply upn_Var. auto.
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
    VAL Γ ⊢ e -> e.[upn Γ ξ] = e.
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
    VALCLOSED v -> VALCLOSED v.[ξ].
Proof.
  intros.
  rewrite vclosed_ignores_sub;
    auto.
Qed.
Global Hint Resolve vclosed_sub_closed : core.

(** FrameStack *)
(** Based on Pitts' work: https://www.cl.cam.ac.uk/~amp12/papers/opespe/opespe-lncs.pdf *)
Inductive Frame : Set :=
| FApp1 (l : list Exp) (* apply □(e₁, e₂, ..., eₙ) *)
| FApp2 (v : Exp) (l1 l2 : list Exp) (* apply v(v₁, v₂, ... vᵢ₋₁, □, eᵢ₊₁, ..., eₙ) *)
| FLet (v : Var) (e2 : Exp) (* let v = □ in e2 *)
| FPlus1 (e2 : Exp) (* □ + e2 *)
| FPlus2 (v : Exp) (* (p : is_value v) *) (* v + □ *)
| FCase (p : Pat) (e2 e3 : Exp) (* if □ then e2 else e3 *)
| FCons1 (e1 : Exp) (* [e1 | □] *)
| FCons2 (v2 : Exp) (* [□ | v2] *).

Inductive frame_wf : Frame -> Prop :=
| wf_app1 l : frame_wf (FApp1 l)
| wf_app2 vl b l1 l2 :  Forall (fun v => VALCLOSED v) l2 -> frame_wf (FApp2 (EFun vl b) l1 l2)
| wf_let v e : frame_wf (FLet v e)
| wf_plus1 e : frame_wf (FPlus1 e)
| wf_plus2 v : VALCLOSED v -> frame_wf (FPlus2 v)
| wf_if p e2 e3 : frame_wf (FCase p e2 e3)
| wf_cons1 e : frame_wf (FCons1 e)
| wf_cons2 v : VALCLOSED v -> frame_wf (FCons2 v).

Definition plug_f (F : Frame) (e : Exp) : Exp :=
match F with
 | FApp1 l => EApp e l
 | FApp2 v l1 l2 => EApp v (l2 ++ [e] ++ l1)
 | FLet v e2 => ELet v e e2
 | FPlus1 e2 => EPlus e e2
 | FPlus2 v => EPlus v e
 | FCase p e2 e3 => ECase e p e2 e3
 | FCons1 e1 => ECons e1 e
 | FCons2 v2 => ECons e v2
end.

Definition FrameStack := list Frame.

Inductive FCLOSED : Frame -> Prop :=
| fclosed_app1 l:
  Forall (fun e => EXPCLOSED e) l
->
  FCLOSED (FApp1 l)
| fclosed_app2 v l1 l2:
  VALCLOSED v -> Forall (fun e => EXPCLOSED e) l1 -> Forall (fun e => VALCLOSED e) l2
->
  FCLOSED (FApp2 v l1 l2)
| fclosed_let e2 v :
  EXP 1 ⊢ e2
->
  FCLOSED (FLet v e2)
| fclosed_plus1 e2:
  EXPCLOSED e2
->
  FCLOSED (FPlus1 e2)
| fclosed_plus2 v1:
  VALCLOSED v1
->
  FCLOSED (FPlus2 v1)
| fclosed_if e2 e3 p:
  EXP pat_vars p ⊢ e2 -> EXPCLOSED e3
->
  FCLOSED (FCase p e2 e3)
| fclosed_cons1 e1:
  EXPCLOSED e1
->
  FCLOSED (FCons1 e1)
| fclosed_cons2 v:
  VALCLOSED v
->
  FCLOSED (FCons2 v).

Definition FSCLOSED (fs : FrameStack) := Forall FCLOSED fs.

Lemma scoped_list_subscoped :
  forall vals Γ ξ Γ', Forall (fun v => VAL Γ ⊢ v) vals -> SUBSCOPE Γ' ⊢ ξ ∷ Γ ->
  SUBSCOPE length vals + Γ' ⊢ list_subst vals ξ ∷ Γ.
Proof.
  induction vals; intros; simpl; auto.
  simpl. inversion H. intro. intros. destruct v.
  * simpl. apply H3.
  * simpl. specialize (IHvals _ _ _ H4 H0 v). apply IHvals. lia.
Qed.

Lemma scoped_list_idsubst :
  forall vals Γ, Forall (fun v => VAL Γ ⊢ v) vals ->
  SUBSCOPE length vals ⊢ list_subst vals idsubst ∷ Γ.
Proof.
  induction vals; intros. simpl.
  unfold idsubst. intro. intros. inversion H0.
  simpl. inversion H. intro. intros. destruct v.
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
  specialize (H v H1).
  destruct (ξ v) eqn:D1.
  * apply -> subst_preserves_scope_val; eassumption.
  * specialize (H0 n H). auto.
Qed.

Theorem match_pattern_scoped : forall p v l Γ,
  VAL Γ ⊢ v -> match_pattern p v = Some l
->
  Forall (fun v => VAL Γ ⊢ v) l.
Proof.
  induction p; intros.
  * simpl in *. destruct v; inversion H0. break_match_hyp; inversion H0. auto.
  * simpl in *. destruct v; inversion H0; subst; auto.
  * simpl in *. destruct v; inversion H0. subst. auto.
  * simpl. simpl in H0. destruct v; try congruence.
    break_match_hyp; try congruence. break_match_hyp; try congruence. inversion H0.
    subst. apply Forall_app. split.
    - inversion H. subst. eapply IHp1. exact H3. auto.
    - inversion H. subst. eapply IHp2. exact H4. auto.
Qed.

Ltac inversion_is_value :=
match goal with
| [ H: VAL _ ⊢ (ELet _ _ _) |- _ ] => inversion H
| [ H: VAL _ ⊢ (ELetRec _ _ _ _) |- _ ] => inversion H
| [ H: VAL _ ⊢ (EPlus _ _) |- _ ] => inversion H
| [ H: VAL _ ⊢ (ECase _ _ _ _) |- _ ] => inversion H
| [ H: VAL _ ⊢ (EApp _ _) |- _ ] => inversion H
| [ H: VAL _ ⊢ (EVar _) |- _ ] => inversion H
| [ H: VAL _ ⊢ (EFunId _) |- _ ] => inversion H
| [ H: VAL _ ⊢ (ECons _ _) |- _ ] => inversion H
end.