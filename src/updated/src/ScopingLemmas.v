Require Export Manipulation.

(** This Definition helps with declaring lemmas. It means if for all v input parameter that are smaller then a given Γ, Substitution ξ will return with the same v (inr v here is in (ValueExpression + nat)).*)
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
 (* This needed a rewrite afther the map fst l, type of rewrites in the scoping. The new proof is below.*)
  * intros. simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - rewrite indexed_to_forall with (def := (VNil,VNil)). intros. specialize (H i H2).
      specialize (H0 i H2). destruct (nth i l) eqn:Eq. unfold id. specialize (H ξ). specialize (H H1).
      f_equal. (*apply pair_equal_spec. split.*)
      + Search nth. replace VNil with (fst (VNil,VNil)) in H. rewrite map_nth in H.
        rewrite Eq in H. simpl in H. exact H. simpl. reflexivity.
      + specialize (H0 ξ). specialize (H0 H1). replace VNil with (snd (VNil,VNil)) in H0.
        rewrite map_nth in H0. rewrite Eq in H0. simpl in H0. exact H0. reflexivity.
  (* * intros. simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - rewrite indexed_to_forall with (def := VNil). intros. unfold id. specialize (H i H1). rewrite H.
      + reflexivity.
      + exact H0. *)
  * intros. simpl. erewrite map_ext_Forall  with (g := Datatypes.id).
    - rewrite H0. rewrite map_id. reflexivity. apply subst_preserves_upn. exact H1.
    - rewrite indexed_to_forall with (def := (0,0,Val VNil)). intros. specialize (H i H2).
      unfold Datatypes.id. destruct (nth i ext) eqn:Eq. destruct p eqn:Eq2. simpl in *.
      specialize (H (upn (Datatypes.length ext + nth i (map snd (map fst ext)) 0) ξ)).
      specialize (H (subst_preserves_upn _ _ _ H1)).
      replace (Val VNil) with (snd (0,0,Val VNil)) in H by auto.
      rewrite map_nth in H. rewrite Eq in H. simpl in H. 
      replace (nth i (map snd (map fst ext)) 0) with n1 in H.
      + rewrite H. auto.
      + replace 0 with (snd (fst (0,0,Val VNil))) by auto. rewrite map_nth. rewrite map_nth.
        rewrite Eq. auto.
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
      specialize (H0 i H2). destruct (nth i l) eqn:Eq. unfold id. simpl in *.
      f_equal.
      + specialize (H ξ H1). Search nth map. replace (Val VNil) with (fst (Val VNil,Val VNil)) in H
        by auto. rewrite map_nth in H. rewrite Eq in H. simpl in H. exact H.
      + specialize (H0 ξ H1). Search nth map. replace (Val VNil) with (snd (Val VNil,Val VNil)) in H0
        by auto. rewrite map_nth in H0. rewrite Eq in H0. simpl in H0. exact H0.
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
      destruct (nth i l) eqn:Eq. destruct p eqn:Eq2. simpl in *. 
      f_equal.
      + f_equal. specialize (H0 (upn (patternListScope (nth i (map fst (map fst l)) nil)) ξ)).
        specialize (H0 (subst_preserves_upn _ _ _ H2)). 
        replace (Val VNil) with (snd (fst((nil : list Pattern, Val VNil, Val VNil)))) in H0 by auto.
        rewrite (map_nth snd (map fst l) (fst(nil, Val VNil, Val VNil)) i) in H0.
        rewrite map_nth in H0. rewrite Eq in H0.
        replace nil with (fst (fst((nil : list Pattern, Val VNil, Val VNil)))) in H0 by auto.
        rewrite map_nth in H0. rewrite map_nth in H0. rewrite Eq in H0. simpl in H0. exact H0.
      + specialize (H1 (upn (patternListScope (nth i (map fst (map fst l)) nil)) ξ)).
        specialize (H1 (subst_preserves_upn _ _ _ H2)).
        replace (Val VNil) with (snd((nil : list Pattern, Val VNil, Val VNil))) in H1 by auto.
        rewrite map_nth in H1. rewrite Eq in H1.
        replace nil with (fst (fst((nil : list Pattern, Val VNil, Val VNil)))) in H1 by auto.
        rewrite map_nth in H1. rewrite map_nth in H1. rewrite Eq in H1. simpl in H1. exact H1.
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
      f_equal. specialize (H (upn (Datatypes.length l + nth i (map fst l) 0) ξ)).
      specialize (H (subst_preserves_upn _ _ _ H1)).
      replace (Val VNil) with (snd (0,Val VNil)) in H by auto. rewrite map_nth in H.
      rewrite Eq in H. replace 0 with (fst(0,Val VNil)) in H by auto. rewrite map_nth in H.
      rewrite Eq in H. simpl in H. exact H.
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
  (* * intros. constructor. exact H. *)
  * intros. constructor.
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
     forall (Γ' : nat) (ξ : Renaming), RENSCOPE Γ ⊢ ξ ∷ Γ' -> VAL Γ' ⊢ renameValue ξ  (nth i (map snd l) (VNil))))
     
  (* New, Please Check with Peter. *)
  (VV := fun l => 
	forall i, i < length l -> 
    (forall Γ, EXP Γ ⊢ (nth i (map snd l) (Val VNil)) <->
      forall (Γ' : nat) (ξ : Renaming), RENSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ rename ξ (nth i (map snd l) (Val VNil)))
)
  (Q := fun l => forall i, i < length l -> (forall Γ, EXP Γ ⊢ (nth i l (Val VNil)) <-> forall Γ' ξ, RENSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ rename ξ (nth i l (Val VNil))))
  (R := fun l => forall i, i < length l -> 
    (forall Γ, EXP Γ ⊢ (nth i (map fst l) (Val VNil)) <->
      forall (Γ' : nat) (ξ : Renaming), RENSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ rename ξ (nth i (map fst l) (Val VNil)))
    /\ 
    (forall Γ, EXP Γ ⊢  (nth i (map snd l) (Val VNil)) <->
     forall (Γ' : nat) (ξ : Renaming), RENSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ rename ξ (nth i (map snd l) (Val VNil))))
  (W := fun l => forall i, i < length l -> 
    (forall Γ, EXP Γ ⊢ (nth i (map snd (map fst l)) (Val VNil)) <->
      forall (Γ' : nat) (ξ : Renaming), RENSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ rename ξ (nth i (map snd (map fst l)) (Val VNil)))
    /\ 
    (forall Γ, EXP Γ ⊢  (nth i (map snd l) (Val VNil)) <->
     forall (Γ' : nat) (ξ : Renaming), RENSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ rename ξ (nth i (map snd l) (Val VNil))))
  (Z := fun l =>  forall i, i < length l ->  (forall Γ, EXP Γ ⊢ (nth i (map snd l) (Val VNil)) <->
      forall (Γ' : nat) (ξ : Renaming), RENSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ rename ξ (nth i (map snd l) (Val VNil))))
  .
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
        ** exact H.
        ** apply functional_extensionality. intros x. destruct x. simpl. auto.
        (* indukció a lista elemeire *)
          (*clear H6 H5 H0 H1 H2' H3 H4. generalize dependent i. induction l.
          ** intros. inversion H2.
          ** intros. simpl. destruct i.
            *** destruct a. simpl. simpl in H. exact H.
            *** apply IHl.
              **** exact H.
              **** simpl in H2. lia. *)
          (*specialize (H5 Γ'). destruct H5. Check map_nth. (* rewrite <- map_nth. *)
          replace (nth i (map (fun '(x, y) => (renameValue ξ x, renameValue ξ y)) l) (VNil, VNil)) with (nth i l (VNil, VNil)).
          ** apply H6. intros. specialize (H4 i H2). admit. (*specialize (H5 H4).*)
          ** admit. *)
      + intros. rewrite map_length in H2.  specialize (H i H2).
        destruct H. specialize (H5 Γ). destruct H5. apply H4 in H2 as H2'.
        specialize (H5 H2'). specialize (H5 Γ' ξ). specialize (H5 H1).
        rewrite map_map. rewrite <- map_nth in H5. simpl in H5. rewrite map_map in H5.
        replace ((fun x : ValueExpression * ValueExpression =>
        snd (let '(x0, y) := x in (renameValue ξ x0, renameValue ξ y)))) with
        (fun x : ValueExpression * ValueExpression => renameValue ξ (snd x)).
        ** exact H5.
        ** apply functional_extensionality. intros x. destruct x. simpl. auto.
    - intros. constructor.
      + intros. specialize (H i H1). destruct H. specialize (H Γ). destruct H.
        apply H3. intros. specialize (H0 _ _ H4). simpl in H0. inversion H0. subst.
        rewrite <- map_nth. rewrite <- map_nth. simpl. specialize (H6 i).
        rewrite map_length in H6. specialize (H6 H1).
        rewrite <- map_nth in H6. 
        replace (map fst (map (fun '(x, y) => (renameValue ξ x, renameValue ξ y)) l))
        with (map (renameValue ξ) (map fst l)) in H6.
        ** exact H6.
        ** rewrite map_map. rewrite map_map. f_equal.
           apply functional_extensionality. intros x. destruct x. simpl. auto.
      + intros. specialize (H i H1). destruct H. specialize (H2 Γ). destruct H2.
        apply H3. intros. specialize (H0 _ _ H4). simpl in H0. inversion H0. subst.
        rewrite <- map_nth. rewrite <- map_nth. simpl. specialize (H7 i).
        rewrite map_length in H7. specialize (H7 H1).
        rewrite <- map_nth in H7. 
        replace (map snd (map (fun '(x, y) => (renameValue ξ x, renameValue ξ y)) l))
        with (map (renameValue ξ) (map snd l)) in H7.
        ** exact H7.
        ** rewrite map_map. rewrite map_map. f_equal.
           apply functional_extensionality. intros x. destruct x. simpl. auto.
  (* * intros. rewrite indexed_to_forall with (def := (VNil)) in H. split.
    - intros. inversion H0. subst. simpl. constructor. intros.
      rewrite map_length in H2. specialize (H i H2 Γ). destruct H.
      specialize (H3 i H2). specialize (H H3). specialize (H Γ' ξ H1).
      rewrite <- map_nth in H. simpl in H.
      replace (fun x : ValueExpression => renameValue ξ x) with (renameValue ξ).
      + exact H.
      + apply functional_extensionality. auto.
    - intros. constructor. intros. specialize (H i H1 Γ). destruct H.
      apply H2. intros. specialize (H0 Γ' ξ H3). simpl in H0. inversion H0. subst.
      rewrite <- map_nth.
      apply H5. rewrite map_length. exact H1. *)
  * intros. split.
    - intros. simpl. inversion H. subst. constructor. auto.
    - intros. specialize (H Γ). specialize (H id). simpl in *.
      apply H. apply renscope_id.
  * intros. split.
    - intros. simpl. inversion H. subst. constructor. auto.
    - intros. specialize (H Γ). specialize (H id). simpl in *.
      apply H. apply renscope_id.
  (* This one is complicated. *)
  * intros. split.
    - simpl. constructor. 
      + intros. rewrite map_length. rewrite map_length in H3.
        clear H0. specialize (H i H3). inversion H1. subst.
        specialize (H (Datatypes.length ext + (nth i (map snd (map fst ext)) 0) + Γ)).
        destruct H. clear H0 H1. specialize (H8 i H3). specialize (H H8).
        clear H3 H8 H9. pose proof uprenn_scope.
        specialize (H0 (Datatypes.length ext + (nth i (map snd (map fst ext)) 0)) Γ Γ' ξ H2).
        specialize (H (Datatypes.length ext + (nth i (map snd (map fst ext)) 0) + Γ')
        (uprenn (Datatypes.length ext + nth i (map snd (map fst ext)) 0) ξ)).
        specialize (H H0). clear H0 H2. rewrite map_map in H.
        remember (fun x : nat * nat * Expression => snd (fst x)) as Fsf.
        replace 0 with (Fsf (0,0,Val VNil)) in H by (subst;auto).
        replace (Val VNil) with (snd (0,0,Val VNil)) in H by auto.
        do 2 rewrite map_nth in H.
        do 3 rewrite map_map.
        remember (fun x : nat * nat * Expression =>
          snd
            (fst
               (let
                '(i0, ls, x0) := x in
                 (i0, ls,
                 rename (uprenn (Datatypes.length ext + ls) ξ) x0)))) as FSF.
        remember (fun x : nat * nat * Expression =>
        snd
          (let
           '(i0, ls, x0) := x in
            (i0, ls, rename (uprenn (Datatypes.length ext + ls) ξ) x0))) as FS.
        replace 0 with (FSF (0,0,Val VNil)) by (subst;auto).
        replace (Val VNil) with (FS (0,0,Val VNil)) by (subst;auto).
        do 2 rewrite map_nth. replace (FSF (nth i ext (0, 0, FS (0, 0, Val VNil)))) with
        (Fsf (nth i ext (0, 0, Val VNil))).
        ** replace (FS (nth i ext (0, 0, Val VNil))) with
           (rename (uprenn (Datatypes.length ext + Fsf (nth i ext (0, 0, snd (0, 0, Val
           VNil)))) ξ) (snd (nth i ext (0, 0, Val VNil)))).
           -- exact H.
           -- clear H. subst. simpl. destruct (nth i ext (0, 0, Val VNil)).
              destruct p. simpl. reflexivity.
        ** clear H. subst. simpl. destruct (nth i ext (0, 0, Val VNil)).
           destruct p. simpl. reflexivity.
      + clear H. inversion H1. subst. clear H1 H7.
        specialize (H0 (Datatypes.length ext + vl + Γ)). destruct H0.
        clear H0. pose proof uprenn_scope.
        specialize (H0 (Datatypes.length ext + vl) Γ Γ' ξ H2).
        specialize (H H8 (Datatypes.length ext + vl + Γ')
        (uprenn (Datatypes.length ext + vl) ξ)). specialize (H H0).
        clear H2 H0 H8. rewrite map_length. exact H.
    - clear H H0. intros. pose proof idrenaming_is_id as [_ [_ H0]].
      specialize (H Γ Datatypes.id). specialize (H (renscope_id Γ)).
      rewrite H0 in H. exact H.
  * intros. split.
    - intros. simpl. constructor. inversion H0. subst. specialize (H (n+Γ)).
      destruct H. apply H.
      + exact H5.
      + apply (uprenn_scope n Γ Γ' ξ) in H1. exact H1.
    - intros. constructor. specialize (H0 Γ id). specialize (H0 (renscope_id Γ)).
      inversion H0. subst. Search id uprenn. rewrite idrenaming_upn in H4.
      Search id rename. pose proof idrenaming_is_id as [H5 [_ _]].
      rewrite H5 in H4. exact H4.
  * intros. split.
    - intros. simpl. constructor. intros. rewrite map_length in H2.
      specialize (H i H2). specialize (H Γ). destruct H.
      inversion H0. subst. specialize (H5 i H2). specialize (H H5).
      specialize (H Γ' ξ H1). replace (Val VNil) with (rename ξ (Val VNil)) by auto.
      rewrite map_nth. exact H.
    - intros. constructor. intros. specialize (H i H1). 
      specialize (H Γ). destruct H.
      apply H2. intros. specialize (H0 Γ' ξ). specialize (H0 H3).
      inversion H0. subst. rewrite map_length in H5. specialize (H5 i H1).
      replace (Val VNil) with (rename ξ (Val VNil)) in H5 by auto.
      rewrite map_nth in H5. exact H5.
  * intros. split.
    - intros. simpl. constructor.
      + specialize (H Γ). destruct H. inversion H1. subst.
        specialize (H H6 Γ' ξ H2). exact H.
      + specialize (H0 Γ). destruct H0. inversion H1. subst.
        specialize (H0 H8 Γ' ξ H2). exact H0.
    - intros. constructor.
      + specialize (H Γ). destruct H. apply H2. intros. specialize (H1 Γ' ξ H3).
        inversion H1. subst. exact H6.
      + specialize (H0 Γ). destruct H0. apply H2. intros. specialize (H1 Γ' ξ H3).
        inversion H1. subst. exact H8.
  * intros. split.
    - intros. simpl. constructor. intros. rewrite map_length in H2.
      replace (Val VNil) with (rename ξ (Val VNil)) by auto. rewrite map_nth.
      specialize (H i H2 Γ). destruct H. inversion H0. subst.
      specialize (H5 i H2). specialize (H H5 Γ' ξ H1). exact H.
    - intros. constructor. intros. specialize (H i H1 Γ).
      destruct H. apply H2. intros. specialize (H0 Γ' ξ H3). inversion H0. subst.
      rewrite map_length in H5. specialize (H5 i H1).
      replace (Val VNil) with (rename ξ (Val VNil)) in H5 by auto.
      rewrite map_nth in H5. exact H5.
  * intros. split.
    - intros. simpl. constructor.
      + intros. rewrite map_length in H2. specialize (H i H2 ). destruct H.
        specialize (H Γ). destruct H. inversion H0. subst. specialize (H6 i H2).
        specialize (H H6 Γ' ξ H1). rewrite <- map_nth in H.
        replace (nth i (map fst (map (fun '(x, y) => (rename ξ x, rename ξ y)) l)) 
        (Val VNil)) with (nth i (map (rename ξ) (map fst l)) (rename ξ (Val VNil))).
        ** exact H.
        ** f_equal. rewrite map_map. rewrite map_map. f_equal. 
           apply functional_extensionality. intros x. destruct x. simpl. auto.
      + intros. rewrite map_length in H2. specialize (H i H2 ). destruct H.
        specialize (H3 Γ). destruct H3. inversion H0. subst. specialize (H7 i H2).
        specialize (H3 H7 Γ' ξ H1). rewrite <- map_nth in H3.
        replace (nth i (map snd (map (fun '(x, y) => (rename ξ x, rename ξ y)) l)) 
        (Val VNil)) with (nth i (map (rename ξ) (map snd l)) (rename ξ (Val VNil))).
        ** exact H3.
        ** f_equal. rewrite map_map. rewrite map_map. f_equal.
           apply functional_extensionality. intros x. destruct x. simpl. auto.
    - intros. constructor.
      + intros. specialize (H i H1). destruct H. specialize (H Γ). destruct H.
        apply H3. intros. specialize (H0 Γ' ξ H4). inversion H0. subst.
        rewrite map_length in H6. specialize (H6 i H1). rewrite <- map_nth.
        replace (nth i (map fst (map (fun '(x, y) => (rename ξ x, rename ξ y)) l)) 
        (Val VNil)) with (nth i (map (rename ξ) (map fst l)) (rename ξ (Val VNil)))
        in H6.
        ** exact H6.
        ** f_equal. rewrite map_map. rewrite map_map. f_equal. 
           apply functional_extensionality. intros x. destruct x. simpl. auto.
      + intros. specialize (H i H1). destruct H. specialize (H2 Γ). destruct H2.
        apply H3. intros. specialize (H0 Γ' ξ H4). inversion H0. subst.
        rewrite map_length in H7. specialize (H7 i H1). rewrite <- map_nth.
        replace (nth i (map snd (map (fun '(x, y) => (rename ξ x, rename ξ y)) l)) 
        (Val VNil)) with (nth i (map (rename ξ) (map snd l)) (rename ξ (Val VNil)))
        in H7.
        ** exact H7.
        ** f_equal. rewrite map_map. rewrite map_map. f_equal. 
           apply functional_extensionality. intros x. destruct x. simpl. auto.
  * intros. split.
    - intros. simpl. constructor. intros. rewrite map_length in H2.
      specialize (H i H2 Γ). destruct H. inversion H0.
      subst. specialize (H7 i H2). specialize (H H7 Γ' ξ H1).
      replace (Val VNil) with (rename ξ (Val VNil)) by auto. rewrite map_nth.
      exact H.
    - intros. constructor. intros. specialize (H i H1 Γ).
      destruct H. apply H2. intros. specialize (H0 Γ' ξ H3). inversion H0. subst.
      rewrite map_length in H7. specialize (H7 i H1).
      replace (Val VNil) with (rename ξ (Val VNil)) in H7 by auto.
      rewrite map_nth in H7. exact H7.
  * intros. split.
    - intros. simpl. constructor. intros. rewrite map_length in H2.
      specialize (H i H2 Γ). destruct H. inversion H0. subst.
      specialize (H7 i H2). specialize (H H7 Γ' ξ H1).
      replace (Val VNil) with (rename ξ (Val VNil)) by auto. rewrite map_nth.
      exact H.
    - intros. constructor. intros. specialize (H i H1 Γ).
      destruct H. apply H2. intros. specialize (H0 Γ' ξ H3). inversion H0. subst.
      rewrite map_length in H7. specialize (H7 i H1).
      replace (Val VNil) with (rename ξ (Val VNil)) in H7 by auto.
      rewrite map_nth in H7. exact H7.
  * intros. split.
    - intros. simpl. constructor.
      + specialize (H Γ). destruct H. apply H.
        ** inversion H1. subst. exact H6.
        ** exact H2.
      + intros. rewrite map_length in H3.
        replace (Val VNil) with (rename ξ (Val VNil)) by auto. rewrite map_nth.
        specialize (H0 i H3 Γ). destruct H0. apply H0.
        ** inversion H1. subst. specialize (H9 i H3). exact H9.
        ** exact H2.
    - intros. constructor.
      + specialize (H Γ). destruct H. apply H2. intros. specialize (H1 Γ' ξ H3).
        inversion H1. subst. exact H6.
      + intros. specialize (H0 i H2 Γ). destruct H0.
        apply H3. intros. specialize (H1 Γ' ξ H4). inversion H1. subst.
        rewrite map_length in H9. specialize (H9 i H2).
        replace (Val VNil) with (rename ξ (Val VNil)) in H9 by auto.
        rewrite map_nth in H9. exact H9.
  * intros. split.
    - intros. simpl. constructor.
      + specialize (H Γ). destruct H. apply H.
        ** inversion H1. subst. exact H6.
        ** exact H2.
      + intros. rewrite map_length in H3.
        (* Trying to get it from H0*)
        specialize (H0 i H3). destruct H0. (* Still need the H0 not H4*) clear H4 H.
        specialize (H0 (patternListScope (nth i (map fst (map fst l)) nil) + Γ)). 
        destruct H0. (*only H will be needed*) clear H0.
        inversion H1. subst.
        clear H8. specialize (H6 i H3). specialize (H H6).
        specialize (H (patternListScope (nth i (map fst (map fst l)) nil) + Γ') (uprenn
        (patternListScope (nth i (map fst (map fst l)) nil)) ξ)).
        Search ren. clear H1 H3 H5 H6. pose proof uprenn_scope.
        specialize (H0 (patternListScope (nth i (map fst (map fst l)) nil)) Γ Γ' ξ H2).
        specialize (H H0). clear H0 H2.
        (* Try to simplify H here*)
        do 2 rewrite map_map in H. 
        remember (fun x : list Pattern * Expression * Expression => fst (fst x)) as Fff.
        remember (fun x : list Pattern * Expression * Expression => snd (fst x)) as Fsf.
        replace nil with (Fff (nil, Val VNil, Val VNil)) in H by (subst; auto).
        rewrite map_nth in H. 
        replace (Val VNil) with (Fsf (nil, Val VNil, Val VNil)) in H by (subst; auto).
        rewrite map_nth in H. subst. simpl in *.
        (* Try to simplify the goal here*)
        do 4 rewrite map_map. 
        remember (fun x : list Pattern * Expression * Expression =>
             fst
               (fst
                  (let
                   '(p, x0, y) := x in
                    (p, rename (uprenn (patternListScope p) ξ) x0,
                    rename (uprenn (patternListScope p) ξ) y)))) as FFF.
        remember (fun x : list Pattern * Expression * Expression =>
        snd
          (fst
             (let
              '(p, x0, y) := x in
               (p, rename (uprenn (patternListScope p) ξ) x0,
               rename (uprenn (patternListScope p) ξ) y)))) as FSF.
        replace nil with (FFF (nil, Val VNil, Val VNil)) by (subst;auto).
        rewrite map_nth.
        replace (Val VNil) with
        (FSF (nil, Val VNil, Val VNil)) by (subst;auto).
        rewrite map_nth.
        (* replace then solw eq *)
        replace (fst (fst (nth i l (nil, Val VNil, Val VNil)))) with
        (FFF (nth i l (nil, FSF (nil, Val VNil, Val VNil), FSF (nil, Val VNil, Val VNil))))
        in H.
        ** replace (rename (uprenn (patternListScope (FFF (nth i l
           (nil, FSF (nil, Val VNil, Val VNil), FSF (nil, Val VNil, Val VNil))))) ξ)
           (snd (fst (nth i l (nil, Val VNil, Val VNil))))) with
           (FSF (nth i l (nil, Val VNil, Val VNil))) in H.
           -- exact H.
           -- clear H. subst. simpl. destruct (nth i l (nil, Val VNil, Val VNil)).
              destruct p. simpl. reflexivity.
        ** clear H. subst. simpl. Search fst. destruct (nth i l (nil, Val VNil, Val VNil)).
           destruct p. simpl. reflexivity.
      + intros. rewrite map_length in H3. clear H. specialize (H0 i H3).
        destruct H0. clear H. inversion H1. subst. clear H6 H5.
        specialize (H8 i H3). clear H1 H3.
        specialize (H0 (patternListScope (nth i (map fst (map fst l)) nil) + Γ)).
        destruct H0. clear H0. specialize (H H8).
        specialize (H (patternListScope (nth i (map fst (map fst l)) nil) + Γ')).
        pose proof uprenn_scope.
        specialize (H0 (patternListScope (nth i (map fst (map fst l)) nil)) Γ Γ' ξ H2).
        specialize (H (uprenn (patternListScope (nth i (map fst (map fst l)) nil)) ξ)).
        specialize (H H0). clear H2 H8 H0. rewrite map_map in H.
        remember (fun x : list Pattern * Expression * Expression => fst (fst x)) as Fff.
        replace nil with (Fff (nil, Val VNil, Val VNil)) in H by (subst;auto).
        replace (Val VNil) with (snd (nil:(list Pattern), Val VNil, Val VNil)) in H by auto.
        do 2 rewrite map_nth in H.
        do 3 rewrite map_map.
        remember (fun x : list Pattern * Expression * Expression =>
             fst
               (fst
                  (let
                   '(p, x0, y) := x in
                    (p, rename (uprenn (patternListScope p) ξ) x0,
                    rename (uprenn (patternListScope p) ξ) y)))) as FFF.
        remember (fun x : list Pattern * Expression * Expression =>
        snd
          (let
           '(p, x0, y) := x in
            (p, rename (uprenn (patternListScope p) ξ) x0,
            rename (uprenn (patternListScope p) ξ) y))) as FS.
        replace nil with (FFF (nil, Val VNil, Val VNil)) by (subst;auto).
        replace (Val VNil) with (FS (nil, Val VNil, Val VNil)) by (subst;auto).
        do 2 rewrite map_nth.
        replace (Fff (nth i l (nil:(list Pattern), snd (nil:(list Pattern), 
        Val VNil, Val VNil), snd (nil:(list Pattern), Val VNil, Val VNil)))) 
        with (FFF (nth i l (nil:(list Pattern), FS (nil:(list Pattern), Val VNil, Val VNil),
        FS (nil:(list Pattern), Val VNil, Val VNil)))) in H.
        ** replace (rename (uprenn (patternListScope (FFF (nth i l
           (nil, FS (nil, Val VNil, Val VNil), FS (nil, Val VNil, Val VNil))))) ξ)
           (snd (nth i l (nil, Val VNil, Val VNil)))) with
           (FS (nth i l (nil, Val VNil, Val VNil))) in H.
           -- exact H.
           -- clear H. subst. simpl. destruct (nth i l (nil, Val VNil, Val VNil)).
              destruct p. simpl. reflexivity.
        ** clear H. subst. simpl. destruct (nth i l (nil, Val VNil, Val VNil)).
           destruct p. simpl. reflexivity.
    - intros. specialize (H1 Γ id). specialize (H1 (renscope_id Γ)).
      inversion H1. subst. pose proof idrenaming_is_id as [_ [H8 _]].
      rewrite H8 in H1. exact H1.
  * intros. split.
    - intros. simpl. constructor.
      + specialize (H Γ). destruct H. inversion H1. subst. 
        specialize (H H8 Γ' ξ H2). exact H.
      + specialize (H0 (l + Γ)). destruct H0. inversion H1. subst. 
        specialize (H0 H9 (l + Γ') (uprenn l ξ)). pose proof uprenn_scope.
        specialize (H4 l Γ Γ' ξ H2). specialize (H0 H4). exact H0.
    - intros. specialize (H1 Γ id). specialize (H1 (renscope_id Γ)).
      inversion H1. subst. Search id uprenn. rewrite idrenaming_upn in H7.
      Search id rename. pose proof idrenaming_is_id as [H8 [_ _]].
      rewrite H8 in H7. rewrite H8 in H6. constructor. exact H6. exact H7.
  * intros. split.
    - intros. simpl. constructor.
      + specialize (H Γ). destruct H. inversion H1. subst.
        specialize (H H6 Γ' ξ H2). exact H.
      + specialize (H0 Γ). destruct H0. inversion H1. subst.
        specialize (H0 H8 Γ' ξ H2). exact H0.
    - intros. constructor.
      + specialize (H Γ). destruct H. apply H2. intros. specialize (H1 Γ' ξ H3).
        inversion H1. subst. exact H6.
      + specialize (H0 Γ). destruct H0. apply H2. intros. specialize (H1 Γ' ξ H3).
        inversion H1. subst. exact H8.
  * intros. split.
    - intros. simpl. constructor.
      + intros. rewrite map_length in H3. clear H. specialize (H0 i H3).
        inversion H1. subst. specialize (H5 i H3).
        specialize (H0 (Datatypes.length l + nth i (map fst l) 0 + Γ)).
        destruct H0. clear H0 H1 H3. specialize (H H5). clear H5.
        pose proof uprenn_scope.
        specialize (H0 (Datatypes.length l + nth i (map fst l) 0) Γ Γ' ξ H2).
        clear H2 H7. specialize (H (Datatypes.length l + nth i (map fst l) 0 + Γ') 
        (uprenn (Datatypes.length l + nth i (map fst l) 0) ξ)). specialize (H H0).
        clear H0. replace 0 with (fst (0,Val VNil)) in H by auto.
        replace (Val VNil) with (snd (0, Val VNil)) in H by auto.
        do 2 rewrite map_nth in H. simpl in *. rewrite map_length.
        do 2 rewrite map_map.
        remember (fun x : nat * Expression =>
          fst
            (let
             '(n, x0) := x in
              (n, rename (uprenn (Datatypes.length l + n) ξ) x0))) as FF.
        remember (fun x : nat * Expression =>
        snd
          (let
           '(n, x0) := x in
            (n, rename (uprenn (Datatypes.length l + n) ξ) x0))) as FS.
        replace 0 with (FF (0, Val VNil)) by (subst;auto).
        replace (Val VNil) with (FS (0, Val VNil)) by (subst;auto).
        do 2 rewrite map_nth. replace (FF (nth i l (0, FS (0, Val VNil))))
        with (fst (nth i l (0, Val VNil))).
        ** replace (FS (nth i l (0, Val VNil))) with
           (rename (uprenn (Datatypes.length l + fst (nth i l (0, Val VNil))) ξ)
           (snd (nth i l (0, Val VNil)))).
           -- exact H.
           -- clear H. subst. simpl. destruct (nth i l (0, Val VNil)).
              simpl. reflexivity.
        ** clear H. subst. simpl. destruct (nth i l (0, Val VNil)).
           simpl. reflexivity.
      + inversion H1. subst. rewrite map_length. clear H0 H1 H5.
        specialize (H ((Datatypes.length l) + Γ)). destruct H. clear H0.
        specialize (H H7). pose proof uprenn_scope.
        specialize (H0 (Datatypes.length l) Γ Γ' ξ H2). clear H2 H7.
        specialize (H (Datatypes.length l + Γ') (uprenn (Datatypes.length l) ξ)).
        specialize (H H0). clear H0. exact H.
    - intros. specialize (H1 Γ id (renscope_id Γ)).
      pose proof idrenaming_is_id as [_ [H2 _]]. rewrite H2 in H1. exact H1.
  * intros. split.
    - intros. simpl. constructor.
      + specialize (H Γ). destruct H. inversion H2. subst. 
        specialize (H H11 Γ' ξ H3). exact H.
      + specialize (H0 (vl1 + Γ)). destruct H0. inversion H2. subst. 
        specialize (H0 H12 (vl1 + Γ') (uprenn vl1 ξ)). pose proof uprenn_scope.
        specialize (H5 vl1 Γ Γ' ξ H3). specialize (H0 H5). exact H0.
      + specialize (H1 (vl2 + Γ)). destruct H1. inversion H2. subst. 
        specialize (H1 H13 (vl2 + Γ') (uprenn vl2 ξ)). pose proof uprenn_scope.
        specialize (H5 vl2 Γ Γ' ξ H3). specialize (H1 H5). exact H1.
    - intros. specialize (H2 Γ id). specialize (H2 (renscope_id Γ)).
      inversion H2. subst. Search id uprenn. rewrite idrenaming_upn in H10, H11.
      Search id rename. pose proof idrenaming_is_id as [H12 [_ _]].
      rewrite H12 in H9, H10, H11. constructor. exact H9. exact H10. exact H11.
  * intros. inversion H.
  * intros. split.
    - intros. destruct i.
      + simpl. specialize (H Γ). destruct H. apply H.
        ** auto.
        ** auto.
      + simpl. simpl in H1. specialize (H0 i ltac:(lia) Γ). destruct H0. apply H0.
        ** simpl in H2. exact H2.
        ** exact H3.
    - intros. specialize (H2 Γ id). specialize (H2 (renscope_id Γ)).
      pose proof idrenaming_is_id as [H3 [_ _]]. rewrite H3 in H2. exact H2.
  * apply Forall_nil.
  * intros. rewrite indexed_to_forall with (def := (VNil)). 
    rewrite indexed_to_forall with (def := (VNil)) in H0. intros. destruct i.
    - simpl. specialize (H Γ). exact H.
    - simpl in *. pose proof Lt.lt_S_n. specialize (H2 i (Datatypes.length el)).
      specialize (H2 H1). specialize (H0 i H2 Γ). exact H0.
  * intros. inversion H.
  * intros. split.
    - intros. destruct i.
      + simpl. specialize (H Γ). exact H.
      + simpl in *. Search "<" "S". pose proof Lt.lt_S_n. 
        specialize (H3 i (Datatypes.length el)). specialize (H3 H2).
        specialize (H1 i H3). destruct H1. specialize (H1 Γ).
        exact H1.
    - intros. destruct i.
      + simpl. specialize (H0 Γ). exact H0.
      + simpl in *. pose proof Lt.lt_S_n. 
        specialize (H3 i (Datatypes.length el)). specialize (H3 H2).
        specialize (H1 i H3). destruct H1. specialize (H4 Γ).
        exact H4.
  * intros. inversion H.
  * intros. split.
    - intros. destruct i.
      + simpl. specialize (H Γ). exact H.
      + simpl in *. pose proof Lt.lt_S_n. specialize (H3 i (Datatypes.length el)).
        specialize (H3 H2). specialize (H1 i H3). destruct H1. specialize (H1 Γ).
        exact H1.
    - intros. destruct i.
      + simpl. specialize (H0 Γ). exact H0.
      + simpl in *. pose proof Lt.lt_S_n. specialize (H3 i (Datatypes.length el)).
        specialize (H3 H2). specialize (H1 i H3). destruct H1. specialize (H4 Γ).
        exact H4.
  * intros. inversion H.
  * intros. split.
    - intros. destruct i.
      + simpl in *. specialize (H Γ). destruct H. specialize (H H2 Γ' ξ H3).
        exact H.
      + simpl in *. pose proof Lt.lt_S_n. specialize (H4 i (Datatypes.length el)).
        specialize (H4 H1). specialize (H0 i H4 Γ). destruct H0.
        specialize (H0 H2 Γ' ξ H3). exact H0.
    - intros. specialize (H2 Γ id). specialize (H2 (renscope_id Γ)).
      pose proof idrenaming_is_id as [H3 [_ _]]. rewrite H3 in H2. exact H2.
  * intros. inversion H.
  * intros. split.
    - intros. simpl in H2. destruct i.
      + simpl. specialize (H Γ). exact H.
      + simpl. pose proof Lt.lt_S_n. specialize (H3 i (Datatypes.length lv)).
        specialize (H3 H2). specialize (H1 i H3). destruct H1.
        specialize (H1 Γ). exact H1.
    - intros. simpl in H2. destruct i.
      + simpl. specialize (H0 Γ). exact H0.
      + simpl. pose proof Lt.lt_S_n. specialize (H3 i (Datatypes.length lv)).
        specialize (H3 H2). specialize (H1 i H3). destruct H1.
        specialize (H4 Γ). exact H4.
  * intros. inversion H.
  * intros. destruct i.
    - simpl. specialize (H Γ). exact H.
    - simpl in *. pose proof Lt.lt_S_n. specialize (H2 i (Datatypes.length el)).
      specialize (H2 H1). specialize (H0 i H2 Γ). exact H0.
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
  eapply Exp_ind with
  (QV := fun l => forall i, i < length l -> (forall Γ, VAL Γ ⊢ (nth i l VNil) <-> forall Γ' ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> VAL Γ' ⊢ (nth i l VNil) .[ξ]ᵥ))
  (RV := fun l => forall i, i < length l -> (forall Γ, VAL Γ ⊢ (nth i (map fst l) VNil) <-> forall Γ' ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> VAL Γ' ⊢ (nth i (map fst l) VNil) .[ξ]ᵥ) /\
					  (forall Γ, VAL Γ ⊢ (nth i (map snd l) VNil) <-> forall Γ' ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> VAL Γ' ⊢ (nth i (map snd l) VNil) .[ξ]ᵥ))
  (VV := fun l =>  forall i, i < length l ->  (forall Γ, EXP Γ ⊢ (nth i (map snd l) (Val VNil)) <-> forall Γ' ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ (nth i (map snd l) (Val VNil)).[ξ]))
  (Q := fun l => forall i, i < length l -> (forall Γ, EXP Γ ⊢ (nth i l (Val VNil)) <-> forall Γ' ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ (nth i l (Val VNil)).[ξ]))
  (R := fun l => forall i, i < length l -> (forall Γ, EXP Γ ⊢ (nth i (map fst l) (Val VNil)) <-> forall Γ' ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ (nth i (map fst l) (Val VNil)) .[ξ]) /\
					 (forall Γ, EXP Γ ⊢ (nth i (map snd l) (Val VNil)) <-> forall Γ' ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ (nth i (map snd l) (Val VNil)) .[ξ]))
  (W := fun l => forall i, i < length l -> (forall Γ, EXP Γ ⊢ (nth i (map snd (map fst l)) (Val VNil)) <-> forall Γ' ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ (nth i (map snd (map fst l)) (Val VNil)) .[ξ]) /\
					 (forall Γ, EXP Γ ⊢ (nth i (map snd l) (Val VNil)) <-> forall Γ' ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ (nth i (map snd l) (Val VNil)) .[ξ]))
  (Z := fun l =>  forall i, i < length l ->  (forall Γ, EXP Γ ⊢ (nth i (map snd l) (Val VNil)) <-> forall Γ' ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> EXP Γ' ⊢ (nth i (map snd l) (Val VNil)).[ξ]))
  .
  * intros. split.
    - specialize (H Γ). destruct H. intros. simpl. constructor. apply H.
      + inversion H1. subst. exact H4.
      + exact H2.
    - intros. specialize (H Γ). destruct H. constructor. apply H1. intros.
      specialize (H0 _ _ H2). simpl in H0. inversion H0. subst. exact H4.
  * intros. split.
    - intros. inversion H0. subst. specialize (H Γ). inversion H. simpl. constructor.
      destruct H. specialize (H H3 Γ' ξ H1). exact H.
    - intros. constructor. specialize (H Γ). destruct H. apply H1. intros.
      specialize (H0 Γ' ξ H2). inversion H0. subst. exact H4.
  * intros. split.
    - intros. simpl. constructor.
    - intros. constructor.
  * intros. split.
    - intros. simpl. constructor.
    - intros. constructor.
  * intros. split.
    - intros. simpl. constructor.
      + specialize (H Γ). destruct H. clear H3 H0. inversion H1. subst.
        specialize (H H4 Γ' ξ H2). exact H.
      + specialize (H0 Γ). destruct H0. clear H H3. inversion H1. subst.
        specialize (H0 H6 Γ' ξ H2). exact H0.
    - intros. constructor.
      + clear H0. specialize (H Γ). destruct H. clear H. apply H0.
        intros. specialize (H1 Γ' ξ H). inversion H1. subst. exact H4.
      + clear H. specialize (H0 Γ). destruct H0. clear H. apply H0.
        intros. specialize (H1 Γ' ξ H). inversion H1. subst. exact H6.
  * intros. split.
    - intros. simpl. constructor. intros. rewrite map_length in H2.
      specialize (H i H2 Γ). destruct H. clear H3. inversion H0.
      subst. specialize (H4 i H2). specialize (H H4 Γ' ξ H1).
      clear H0 H1 H2 H4. replace VNil with (VNil.[ξ]ᵥ) by auto.
      rewrite map_nth. exact H.
    - clear H. intros. specialize (H Γ idsubst). specialize (H (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [_ H0]]. rewrite H0 in H. exact H.
  * intros. split.
    - intros. simpl. constructor.
      + intros. rewrite map_length in H2. specialize (H i H2).
        destruct H. clear H3. specialize (H Γ). destruct H. clear H3.
        inversion H0. subst. clear H5. specialize (H4 i H2).
        specialize (H H4 Γ' ξ H1). clear H0 H1 H2 H4. rewrite map_map.
        remember (fun x : ValueExpression * ValueExpression =>
        fst (let '(x0, y) := x in (x0.[ξ]ᵥ, y.[ξ]ᵥ))) as FF.
        replace VNil with (FF (VNil,VNil)) by (subst;auto).
        rewrite map_nth. replace VNil with (fst (VNil,VNil)) in H by auto.
        rewrite map_nth in H. replace (FF (nth i l (VNil, VNil))) with 
        ((fst (nth i l (VNil, VNil))).[ξ]ᵥ).
        ** exact H.
        ** subst. destruct (nth i l (VNil, VNil)). simpl. reflexivity.
      + intros. rewrite map_length in H2. specialize (H i H2).
        destruct H. clear H. specialize (H3 Γ). destruct H3. clear H3.
        inversion H0. subst. clear H4. specialize (H5 i H2).
        specialize (H H5 Γ' ξ H1). clear H0 H1 H2 H5. rewrite map_map.
        remember ((fun x : ValueExpression * ValueExpression =>
        snd (let '(x0, y) := x in (x0.[ξ]ᵥ, y.[ξ]ᵥ)))) as FS.
        replace VNil with (FS (VNil,VNil)) by (subst;auto).
        rewrite map_nth. replace VNil with (snd (VNil,VNil)) in H by auto.
        rewrite map_nth in H. replace (FS (nth i l (VNil, VNil))) with 
        ((snd (nth i l (VNil, VNil))).[ξ]ᵥ).
        ** exact H.
        ** subst. destruct (nth i l (VNil, VNil)). simpl. reflexivity.
    - clear H. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [_ H0]]. rewrite H0 in H. exact H.
  (* * intros. split.
    - intros. simpl. constructor. intros. rewrite map_length in H2.
      specialize (H i H2 Γ). destruct H. clear H3. inversion H0. subst.
      specialize (H4 i H2). specialize (H H4 Γ' ξ H1). clear H0 H1 H2 H4.
      replace VNil with (VNil.[ξ]ᵥ) by auto. rewrite map_nth. exact H.
    - clear H. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [_ H0]]. rewrite H0 in H. exact H. *)
  * intros. split.
    (*- intros. simpl. inversion H. subst. constructor. auto.*)
    - intros. inversion H. subst. simpl. unfold subscoped in H0. apply H0 in H2.
      destruct (ξ n).
      + exact H2.
      + constructor. exact H2.
    - intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [_ H0]]. rewrite H0 in H. exact H.
  * intros. split.
    - intros. inversion H. subst. simpl. unfold subscoped in H0. apply H0 in H2.
      destruct (ξ n).
      + exact H2.
      + constructor. exact H2.
    - intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [_ H0]]. rewrite H0 in H. exact H.
  * intros. split.
    - intros. simpl. constructor.
      + do 3 rewrite map_map. intros. rewrite map_length in H3.
        inversion H1. subst. specialize (H9 i H3).
        specialize (H i H3 (Datatypes.length ext + nth i (map snd (map fst ext)) 0 + Γ)).
        destruct H. clear H4. specialize (H H9 (Datatypes.length ext + nth i (map snd (map fst
        ext)) 0 + Γ')). pose proof upn_scope. specialize (H4 (Datatypes.length ext + 
        nth i (map snd (map fst ext)) 0) Γ Γ' ξ H2). specialize (H (upn
        (Datatypes.length ext + nth i (map snd (map fst ext)) 0) ξ) H4).
        clear H0 H1 H2 H3 H9 H10 H4. rewrite map_map in H. rewrite map_length.
        remember (fun x : nat * nat * Expression => snd (fst x)) as Fsf.
        replace 0 with (Fsf (0,0,Val VNil)) in H by (subst;auto). rewrite map_nth in H.
        replace (Val VNil) with (snd (0,0,Val VNil))in H by auto. rewrite map_nth in H.
        simpl in *. remember (fun x : nat * nat * Expression => snd (fst (let 
        '(i0, ls, x0) := x in (i0, ls, x0.[upn (Datatypes.length ext + ls) ξ])))) as FSF.
        replace 0 with (FSF (0,0,Val VNil)) by (subst;auto). rewrite map_nth.
        remember (fun x : nat * nat * Expression => snd (let '(i0, ls, x0) := x in
        (i0, ls, x0.[upn (Datatypes.length ext + ls) ξ]))) as FS.
        replace (Val VNil) with (FS (0,0,Val VNil)) by (subst;auto).
        rewrite map_nth. replace (FSF (nth i ext (0, 0, FS (0, 0, Val VNil)))) with
        (Fsf (nth i ext (0, 0, Val VNil))).
        ** replace (FS (nth i ext (0, 0, Val VNil))) with 
           ((snd (nth i ext (0, 0, Val VNil))).[upn (Datatypes.length ext +
           Fsf (nth i ext (0, 0, Val VNil))) ξ]).
           -- exact H.
           -- clear H. subst. destruct (nth i ext (0, 0, Val VNil)). simpl.
              destruct p. simpl. reflexivity.
        ** clear H. subst. simpl. destruct (nth i ext (0, 0, Val VNil)). simpl. destruct p.
           simpl. reflexivity.
      + rewrite map_length. clear H. specialize (H0 (Datatypes.length ext + vl + Γ)).
        destruct H0. clear H0. inversion H1. subst. clear H7. specialize (H H8).
        pose proof upn_scope. specialize (H0 (Datatypes.length ext + vl) Γ Γ' ξ H2).
        specialize (H (Datatypes.length ext + vl + Γ') (upn (Datatypes.length ext + vl) ξ)).
        specialize (H H0). exact H.
    - clear H H0. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [_ H0]]. rewrite H0 in H. exact H.
  * intros. split.
    - intros. simpl. constructor. specialize (H (n + Γ)). destruct H.
      clear H2. inversion H0. subst. specialize (H H5 (n + Γ') (upn n ξ)).
      pose proof upn_scope. specialize (H2 n Γ Γ' ξ H1). specialize (H H2).
      exact H.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. exact H.
  * intros. split.
    - intros. simpl. constructor. intros. rewrite map_length in H2.
      specialize (H i H2 Γ). destruct H. clear H3. inversion H0. subst.
      specialize (H4 i H2). specialize (H H4 Γ' ξ H1).
      replace (Val VNil) with ((Val VNil).[ξ]) by auto. rewrite map_nth.
      exact H.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. exact H.
  * intros. split.
    - intros. simpl. constructor.
      + clear H0. inversion H1. subst. specialize (H Γ). destruct H.
        clear H0 H1 H6. specialize (H H4 Γ' ξ H2). exact H.
      + clear H. inversion H1. subst. specialize (H0 Γ). destruct H0.
        clear H0 H1 H4. specialize (H H6 Γ' ξ H2). exact H.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. exact H.
  * intros. split.
    - intros. simpl. constructor. intros. rewrite map_length in H2.
      specialize (H i H2 Γ). destruct H. clear H3. inversion H0. subst.
      specialize (H4 i H2). specialize (H H4 Γ' ξ H1).
      replace (Val VNil) with ((Val VNil).[ξ]) by auto. rewrite map_nth.
      exact H.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. exact H.
  * intros. split.
    - intros. simpl. constructor.
      + intros. rewrite map_length in H2. specialize (H i H2). destruct H.
        clear H3. specialize (H Γ). destruct H. clear H3. inversion H0. subst.
        clear H5. specialize (H4 i H2 ). specialize (H H4 Γ' ξ H1).
        replace (Val VNil) with (fst (Val VNil,Val VNil)) in H by auto.
        rewrite map_nth in H. rewrite map_map. remember (fun x : Expression * Expression =>
        fst (let '(x0, y) := x in (x0.[ξ], y.[ξ]))) as FF. replace (Val VNil) with
        (FF (Val VNil,Val VNil)) by (subst;auto). rewrite map_nth. replace
        (FF (nth i l (Val VNil, Val VNil))) with ((fst (nth i l (Val VNil, Val VNil))).[ξ]).
        ** exact H.
        ** subst. clear. destruct (nth i l (Val VNil, Val VNil)). simpl. reflexivity.
      + intros. rewrite map_length in H2. specialize (H i H2). destruct H.
        clear H. specialize (H3 Γ). destruct H3. clear H3. inversion H0. subst.
        clear H4. specialize (H5 i H2). specialize (H H5 Γ' ξ H1).
        replace (Val VNil) with (snd (Val VNil,Val VNil)) in H by auto.
        rewrite map_nth in H. rewrite map_map. remember (fun x : Expression * Expression =>
        snd (let '(x0, y) := x in (x0.[ξ], y.[ξ]))) as FS. replace (Val VNil) with
        (FS (Val VNil,Val VNil)) by (subst;auto). rewrite map_nth. replace
        (FS (nth i l (Val VNil, Val VNil))) with ((snd (nth i l (Val VNil, Val VNil))).[ξ]).
        ** exact H.
        ** subst. clear. destruct (nth i l (Val VNil, Val VNil)). simpl. reflexivity.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. exact H.
  * intros. split.
    - intros. simpl. constructor. intros. rewrite map_length in H2.
      specialize (H i H2 Γ). destruct H. clear H3. inversion H0. subst.
      specialize (H6 i H2). specialize (H H6 Γ' ξ H1).
      replace (Val VNil) with ((Val VNil).[ξ]) by auto. rewrite map_nth. exact H.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. exact H.
  * intros. split.
    - intros. simpl. constructor. intros. rewrite map_length in H2.
      specialize (H i H2 Γ). destruct H. clear H3. inversion H0. subst.
      specialize (H6 i H2). specialize (H H6 Γ' ξ H1).
      replace (Val VNil) with ((Val VNil).[ξ]) by auto. rewrite map_nth. exact H.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. exact H.
  * intros. split.
    - intros. simpl. constructor.
      + inversion H1. subst. specialize (H Γ). destruct H. clear H3.
        specialize (H H5 Γ' ξ H2). exact H.
      + intros. rewrite map_length in H3. clear H. inversion H1. subst. 
        specialize (H7 i H3). specialize (H0 i H3 Γ). destruct H0. clear H0.
        specialize (H H7 Γ' ξ H2). replace (Val VNil) with ((Val VNil).[ξ]) by auto.
        rewrite map_nth. exact H.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. exact H.
  * intros. split.
    - intros. simpl. constructor.
      + specialize (H Γ). destruct H. inversion H1. subst. specialize (H H6 Γ' ξ H2).
        exact H.
      + clear H. intros. rewrite map_length in H. do 4 rewrite map_map.
        specialize (H0 i H). destruct H0. clear H3. inversion H1. subst. clear H8 H1.
        specialize (H6 i H). pose proof upn_scope.
        specialize (H0 (patternListScope (nth i (map fst (map fst l)) nil) + Γ)).
        destruct H0. clear H3. specialize (H0 H6 
        (patternListScope (nth i (map fst (map fst l)) nil) + Γ') 
        (upn (patternListScope (nth i (map fst (map fst l)) nil)) ξ)).
        specialize (H1 (patternListScope (nth i (map fst (map fst l)) nil)) Γ Γ' ξ H2).
        specialize (H0 H1). clear H H2 H1 H5 H6. do 2 rewrite map_map in H0.
        remember (fun x : list Pattern * Expression * Expression => fst (fst x)) as Fff.
        remember (fun x : list Pattern * Expression * Expression => snd (fst x)) as Fsf.
        replace nil with (Fff(nil,Val VNil,Val VNil)) in H0 by (subst;auto).
        replace (Val VNil) with (Fsf(nil,Val VNil,Val VNil)) in H0 by (subst;auto).
        do 2 rewrite map_nth in H0. remember (fun x : list Pattern * Expression * Expression
        => fst (fst (let '(p, x0, y) := x in (p, x0.[upn (patternListScope p) ξ],
        y.[upn (patternListScope p) ξ])))) as FFF.
        remember (fun x : list Pattern * Expression * Expression => snd (fst (let
        '(p, x0, y) := x in (p, x0.[upn (patternListScope p) ξ], y.[upn (patternListScope p)
        ξ])))) as FSF. replace nil with (FFF (nil,Val VNil,Val VNil)) by (subst;auto).
        replace (Val VNil) with (FSF (nil,Val VNil,Val VNil)) by (subst;auto).
        do 2 rewrite map_nth. replace (FFF (nth i l (nil, FSF (nil, Val VNil, Val VNil),
        FSF (nil, Val VNil, Val VNil)))) with (Fff (nth i l
        (nil, Fsf (nil, Val VNil, Val VNil), Fsf (nil, Val VNil, Val VNil)))).
        ** replace (FSF (nth i l (nil, Val VNil, Val VNil))) with
           ((Fsf (nth i l (nil, Val VNil, Val VNil))).[ upn (patternListScope (Fff
           (nth i l (nil, Fsf (nil, Val VNil, Val VNil), Fsf (nil, Val VNil, Val VNil))))) ξ]).
           -- exact H0.
           -- subst. clear. simpl. destruct (nth i l (nil, Val VNil, Val VNil)). simpl.
              destruct p. simpl. reflexivity.
        ** subst. clear. simpl. destruct (nth i l (nil, Val VNil, Val VNil)). simpl.
           destruct p. simpl. reflexivity.
      + intros. do 3 rewrite map_map. rewrite map_length in H3. clear H.
        specialize (H0 i H3). destruct H0.
        
        clear H. inversion H1. subst. clear H6. specialize (H8 i H3).
        specialize (H0 (patternListScope (nth i (map fst (map fst l)) nil) + Γ)).
        destruct H0. clear H0. specialize (H H8).
        
        pose proof upn_scope. specialize (H0 (patternListScope (nth i (map fst (map fst l)) nil))
        Γ Γ' ξ H2).
        
        specialize (H (patternListScope (nth i (map fst (map fst l)) nil) + Γ') (upn
        (patternListScope (nth i (map fst (map fst l)) nil)) ξ) H0). clear H0 H1 H2 H3 H5 H8.
        
        
        rewrite map_map in H.
        
        remember (fun x : list Pattern * Expression * Expression => fst (fst x)) as Fff.
        replace nil with (Fff (nil, Val VNil, Val VNil)) in H by (subst;auto).
        replace (Val VNil) with (snd (nil : list Pattern, Val VNil, Val VNil)) in H by auto.
        
        do 2 rewrite map_nth in H.
        
        remember (fun x : list Pattern * Expression * Expression 
        => fst (fst (let '(p, x0, y) := x in (p, x0.[upn (patternListScope p) ξ],
        y.[upn (patternListScope p) ξ])))) as FFF.
        remember (fun x : list Pattern * Expression * Expression => snd (let '(p, x0, y) := x
        in (p, x0.[upn (patternListScope p) ξ], y.[upn (patternListScope p) ξ]))) as FSF.
        
        replace nil with (FFF (nil,Val VNil,Val VNil)) by (subst;auto).
        replace (Val VNil) with (FSF (nil,Val VNil,Val VNil)) by (subst;auto).
        
        do 2 rewrite map_nth.
        
        replace (FFF (nth i l (nil, FSF (nil, Val VNil, Val VNil), FSF (nil, Val VNil, Val VNil))))
        with (Fff (nth i l (nil, snd (nil : list Pattern, Val VNil, Val VNil),
        snd (nil : list Pattern, Val VNil, Val VNil)))).
        ** replace (FSF (nth i l (nil, Val VNil, Val VNil))) with ((snd (nth i l (nil, Val VNil, 
           Val VNil))).[ upn (patternListScope (Fff (nth i l (nil, snd (nil : list Pattern, Val VNil,
           Val VNil), snd (nil : list Pattern, Val VNil, Val VNil))))) ξ]).
           -- exact H.
           -- subst. clear. simpl. destruct (nth i l (nil, Val VNil, Val VNil)). simpl.
              destruct p. simpl. reflexivity.
        ** subst. clear. simpl. destruct (nth i l (nil, Val VNil, Val VNil)). simpl.
           destruct p. simpl. reflexivity.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. exact H.
  * intros. split.
    - intros. simpl. constructor.
      + clear H0. specialize (H Γ). destruct H. clear H0. inversion H1. subst.
        specialize (H H6 Γ' ξ H2). exact H.
      + clear H. specialize (H0 (l + Γ)). destruct H0. clear H0. inversion H1. subst.
        specialize (H H7 (l + Γ') (upn l ξ)). pose proof upn_scope.
        specialize (H0 l Γ Γ' ξ H2). specialize (H H0). exact H.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. exact H.
  * intros. split.
    - intros. simpl. constructor.
      + clear H0. specialize (H Γ). destruct H. clear H0. inversion H1. subst.
        specialize (H H4 Γ' ξ H2). exact H.
      + clear H. specialize (H0 Γ). destruct H0. clear H0. inversion H1. subst.
        specialize (H H6 Γ' ξ H2). exact H.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. exact H.
  * intros. split.
    - intros. simpl. constructor.
      + intros. rewrite map_length in H3. clear H. specialize (H0 i H3 (Datatypes.length l +
        nth i (map fst l) 0 + Γ)). destruct H0. clear H0. inversion H1. subst.
        specialize (H5 i H3). specialize (H H5 (Datatypes.length l + nth i (map fst l) 0
        +  Γ') (upn (Datatypes.length l + nth i (map fst l) 0) ξ)). pose proof upn_scope.
        specialize (H0 (Datatypes.length l + nth i (map fst l) 0) Γ Γ' ξ H2).
        specialize (H H0). clear H0 H1 H2 H3 H5 H7. do 2 rewrite map_map. rewrite map_length.
        replace 0 with (fst (0, Val VNil)) in H by auto. replace (Val VNil) with
        (snd (0, Val VNil)) in H by auto. do 2 rewrite map_nth in H.
        remember (fun x : nat * Expression => fst (let '(n, x0) := x in 
        (n, x0.[upn (Datatypes.length l + n) ξ]))) as FF.
        remember (fun x : nat * Expression => snd (let '(n, x0) := x in 
        (n, x0.[upn (Datatypes.length l + n) ξ]))) as FS.
        replace 0 with (FF (0, Val VNil)) by (subst;auto).
        replace (Val VNil) with (FS (0, Val VNil)) by (subst;auto).
        do 2 rewrite map_nth. replace (FF (nth i l (0, FS (0, Val VNil)))) with
        (fst (nth i l (0, snd (0, Val VNil)))).
        ** replace (FS (nth i l (0, Val VNil))) with ((snd (nth i l (0, Val VNil)))
           .[upn (Datatypes.length l + fst (nth i l (0, snd (0, Val VNil)))) ξ]).
           -- exact H.
           -- subst. clear. simpl. destruct (nth i l (0, Val VNil)). simpl. reflexivity.
        ** subst. clear. simpl. destruct (nth i l (0, Val VNil)). simpl. reflexivity.
      + clear H0. rewrite map_length. inversion H1. subst.
        specialize (H (Datatypes.length l + Γ)). destruct H. clear H0 H1 H4.
        specialize (H H6 (Datatypes.length l + Γ') (upn (Datatypes.length l) ξ)).
        pose proof upn_scope. specialize (H0 (Datatypes.length l) Γ Γ' ξ H2).
        specialize (H H0). exact H.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. exact H.
  * intros. split.
    - intros. simpl. constructor.
      + clear H0 H1. specialize (H Γ). destruct H. clear H0. inversion H2. subst.
        specialize (H H8 Γ' ξ H3). exact H.
      + clear H H1. specialize (H0 (vl1 + Γ)). destruct H0. clear H0. inversion H2. subst.
        specialize (H H9 (vl1 + Γ') (upn vl1 ξ)). pose proof upn_scope.
        specialize (H0 vl1 Γ Γ' ξ H3). specialize (H H0). exact H.
      + clear H H0. specialize (H1 (vl2 + Γ)). destruct H1. clear H0. inversion H2. subst.
        specialize (H H10 (vl2 + Γ') (upn vl2 ξ)). pose proof upn_scope.
        specialize (H0 vl2 Γ Γ' ξ H3). specialize (H H0). exact H.
    - clear. intros. specialize (H Γ idsubst (scope_idsubst _)).
      pose proof idsubst_is_id as [_ [H0 _]]. rewrite H0 in H. exact H.
  * intros. inversion H.
  * intros. split.
    - intros. destruct i.
      + simpl. specialize (H Γ). destruct H. apply H.
        ** auto.
        ** auto.
      + simpl. simpl in H1. specialize (H0 i ltac:(lia) Γ). destruct H0. apply H0.
        ** simpl in H2. exact H2.
        ** exact H3.
    - intros. specialize (H2 Γ idsubst). specialize (H2 (renscope_id Γ)). Search idsubst.
      pose proof idsubst_is_id as [H3 [_ _]]. rewrite H3 in H2. exact H2.
  * intros. inversion H.
  * intros. split.
    - intros. destruct i.
      + simpl. specialize (H Γ). destruct H. apply H.
        ** auto.
        ** auto.
      + simpl. simpl in H1. specialize (H0 i ltac:(lia) Γ). destruct H0. apply H0.
        ** simpl in H2. exact H2.
        ** exact H3.
    - intros. specialize (H2 Γ idsubst). specialize (H2 (renscope_id Γ)). Search idsubst.
      pose proof idsubst_is_id as [_ [_ H3]]. rewrite H3 in H2. exact H2.
  * intros. inversion H.
  * intros. split.
    - intros. destruct i.
      + simpl. specialize (H Γ). exact H.
      + simpl in *. pose proof Lt.lt_S_n. 
        specialize (H3 i (Datatypes.length el)). specialize (H3 H2).
        specialize (H1 i H3). destruct H1. specialize (H1 Γ).
        exact H1.
    - intros. destruct i.
      + simpl. specialize (H0 Γ). exact H0.
      + simpl in *. pose proof Lt.lt_S_n. 
        specialize (H3 i (Datatypes.length el)). specialize (H3 H2).
        specialize (H1 i H3). destruct H1. specialize (H4 Γ).
        exact H4.
  * intros. inversion H.
  * intros. split.
    - intros. destruct i.
      + simpl. specialize (H Γ). exact H.
      + simpl in *. pose proof Lt.lt_S_n. specialize (H3 i (Datatypes.length el)).
        specialize (H3 H2). specialize (H1 i H3). destruct H1. specialize (H1 Γ).
        exact H1.
    - intros. destruct i.
      + simpl. specialize (H0 Γ). exact H0.
      + simpl in *. pose proof Lt.lt_S_n. specialize (H3 i (Datatypes.length el)).
        specialize (H3 H2). specialize (H1 i H3). destruct H1. specialize (H4 Γ).
        exact H4.
  * intros. inversion H.
  * intros. split.
    - intros. destruct i.
      + simpl in *. specialize (H Γ). destruct H. specialize (H H2 Γ' ξ H3).
        exact H.
      + simpl in *. pose proof Lt.lt_S_n. specialize (H4 i (Datatypes.length el)).
        specialize (H4 H1). specialize (H0 i H4 Γ). destruct H0.
        specialize (H0 H2 Γ' ξ H3). exact H0.
    - intros. specialize (H2 Γ idsubst). specialize (H2 (renscope_id Γ)).
      pose proof idsubst_is_id as [H3 [_ _]]. rewrite H3 in H2. exact H2.
  * intros. inversion H.
  * intros. split.
    - intros. simpl in H2. destruct i.
      + simpl. specialize (H Γ). exact H.
      + simpl. pose proof Lt.lt_S_n. specialize (H3 i (Datatypes.length lv)).
        specialize (H3 H2). specialize (H1 i H3). destruct H1.
        specialize (H1 Γ). exact H1.
    - intros. simpl in H2. destruct i.
      + simpl. specialize (H0 Γ). exact H0.
      + simpl. pose proof Lt.lt_S_n. specialize (H3 i (Datatypes.length lv)).
        specialize (H3 H2). specialize (H1 i H3). destruct H1.
        specialize (H4 Γ). exact H4.
  * intros. inversion H.
  * intros. destruct i.
    - simpl. specialize (H Γ). exact H.
    - simpl in *. pose proof Lt.lt_S_n. specialize (H2 i (Datatypes.length el)).
      specialize (H2 H1). specialize (H0 i H2 Γ). exact H0.
Qed.


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
      VAL Γ' ⊢ e.[ξ]ᵥ.
Proof.
  intros.
  apply subst_preserves_scope.
Qed.

(**)
Lemma subst_preserves_scope_nval : forall e Γ,
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
  Definition magic_ξ (Γ Γ' : nat) (n : nat) : ValueExpression + nat :=
    if Compare_dec.lt_dec n Γ
    then if Compare_dec.lt_dec n Γ'
         then inr n
         else inl (VLit (Integer 0))
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
  
  Lemma magic_ξ_implies_scope :
      (forall e Γ Γ', EXP Γ' ⊢ e.[magic_ξ Γ Γ'] ->
       EXP Γ ⊢ e) /\
      (forall e Γ Γ', NVAL Γ' ⊢ e.[magic_ξ Γ Γ']ₑ ->
       NVAL Γ ⊢ e) /\
      (forall e Γ Γ', VAL Γ' ⊢ e.[magic_ξ Γ Γ']ᵥ ->
       VAL Γ ⊢ e).
  Proof.
    eapply Exp_ind with
    (QV := fun l => forall i, i < length l -> (forall Γ Γ', VAL Γ' ⊢ (nth i l (VNil)).[magic_ξ Γ Γ']ᵥ -> VAL Γ ⊢ (nth i l (VNil))))
    (RV := fun l => forall i, i < length l -> (forall Γ Γ', VAL Γ' ⊢ (nth i (map fst l) (VNil)).[magic_ξ Γ Γ']ᵥ -> VAL Γ ⊢ (nth i (map fst l) (VNil)))  /\
(forall Γ Γ', VAL Γ' ⊢ (nth i (map snd l) (VNil)).[magic_ξ Γ Γ']ᵥ -> VAL Γ ⊢ (nth i (map snd l) (VNil))))
    (VV := fun l => forall i, i < length l -> (forall Γ Γ', EXP Γ' ⊢ (nth i (map snd l) (Val VNil)).[magic_ξ Γ Γ'] -> EXP Γ ⊢ (nth i (map snd l) (Val VNil))))
    (Q := fun l => forall i, i < length l -> (forall Γ Γ', EXP Γ' ⊢ (nth i l (Val VNil)).[magic_ξ Γ Γ'] -> EXP Γ ⊢ (nth i l (Val VNil))))
    (R := fun l => forall i, i < length l -> (forall Γ Γ', EXP Γ' ⊢ (nth i (map fst l) (Val VNil)).[magic_ξ Γ Γ'] -> EXP Γ ⊢ (nth i (map fst l) (Val VNil))) /\
(forall Γ Γ', EXP Γ' ⊢ (nth i (map snd l) (Val VNil)).[magic_ξ Γ Γ'] -> EXP Γ ⊢ (nth i (map snd l) (Val VNil))))
    (W := fun l => forall i, i < length l -> (forall Γ Γ', EXP Γ' ⊢ (nth i (map snd (map fst l)) (Val VNil)).[magic_ξ Γ Γ'] -> EXP Γ ⊢ (nth i (map snd (map fst l)) (Val VNil))) /\
(forall Γ Γ', EXP Γ' ⊢ (nth i (map snd l) (Val VNil)).[magic_ξ Γ Γ'] -> EXP Γ ⊢ (nth i (map snd l) (Val VNil))))
    (Z := fun l => forall i, i < length l -> (forall Γ Γ', EXP Γ' ⊢ (nth i (map snd l) (Val VNil)).[magic_ξ Γ Γ'] -> EXP Γ ⊢ (nth i (map snd l) (Val VNil))))
    .
    * intros. constructor. inversion H0. subst. specialize (H Γ Γ' H2). exact H.
    * intros. constructor. inversion H0. subst. specialize (H Γ Γ' H2). exact H.
    * intros. constructor.
    * intros. constructor.
    * intros. constructor.
      - clear H0. inversion H1. subst. specialize (H Γ Γ' H3). exact H.
      - clear H. inversion H1. subst. specialize (H0 Γ Γ' H5). exact H0.
    * intros. constructor. intros. specialize (H i H1 Γ Γ'). inversion H0. subst.
      rewrite map_length in H3. specialize (H3 i H1). replace VNil with (VNil.[magic_ξ Γ Γ']ᵥ) in H3
      by auto. rewrite map_nth in H3. specialize (H H3). exact H.
    * intros. constructor.
      - intros. specialize (H i H1). destruct H. clear H2. inversion H0. subst. clear H4.
        rewrite map_length in H3. specialize (H3 i H1). rewrite map_map in H3.
        remember (fun x : ValueExpression * ValueExpression => fst (let '(x0, y) := x in
        (x0.[magic_ξ Γ Γ']ᵥ, y.[magic_ξ Γ Γ']ᵥ))) as Ff.
        replace VNil with (Ff (VNil,VNil)) in H3 by (subst;auto). rewrite map_nth in H3.
        replace (Ff (nth i l (VNil, VNil))) with ((nth i (map fst l) VNil).[magic_ξ Γ Γ']ᵥ) in H3.
        + specialize (H Γ Γ' H3). exact H.
        + subst. clear. replace VNil with (fst (VNil,VNil)) by auto. rewrite map_nth.
          replace (fst (VNil, VNil), fst (VNil, VNil)) with (VNil, VNil) by auto.
          destruct (nth i l (VNil, VNil)) eqn:H. reflexivity.
      - intros. specialize (H i H1). destruct H. clear H. inversion H0. subst. clear H3.
        rewrite map_length in H4. specialize (H4 i H1). rewrite map_map in H4.
        remember (fun x : ValueExpression * ValueExpression => snd (let '(x0, y) := x in
        (x0.[magic_ξ Γ Γ']ᵥ, y.[magic_ξ Γ Γ']ᵥ))) as Fs.
        replace VNil with (Fs (VNil,VNil)) in H4 by (subst;auto). rewrite map_nth in H4.
        replace (Fs (nth i l (VNil, VNil))) with ((nth i (map snd l) VNil).[magic_ξ Γ Γ']ᵥ) in H4.
        + specialize (H2 Γ Γ' H4). exact H2.
        + subst. clear. replace VNil with (snd (VNil,VNil)) by auto. rewrite map_nth.
          replace (snd (VNil, VNil), snd (VNil, VNil)) with (VNil, VNil) by auto.
          destruct (nth i l (VNil, VNil)) eqn:H. simpl. reflexivity.
    (* * intros. constructor. intros. inversion H0. subst. rewrite map_length in H3.
      specialize (H3 i H1). replace VNil with (VNil.[magic_ξ Γ Γ']ᵥ) in H3 by auto.
      rewrite map_nth in H3. specialize (H i H1 Γ Γ' H3). exact H. *)
    * intros. constructor. simpl in H. unfold magic_ξ in H. destruct (Compare_dec.lt_dec n Γ) in H.
      - auto.
      - inversion H. subst. lia.
    * intros. constructor. simpl in H. unfold magic_ξ in H. destruct (Compare_dec.lt_dec n Γ) in H.
      - auto.
      - inversion H. subst. lia.
    * intros. constructor.
      - intros. clear H0. specialize (H i H2). inversion H1. subst. rewrite map_length in H7.
        (* simplify the goal*)
        rewrite map_map. remember (fun x : nat * nat * Expression => snd (fst x)) as FSF.
        replace 0 with (FSF (0,0,Val VNil)) by (subst;auto).
        replace (Val VNil) with (snd (0,0,Val VNil)) by auto. do 2 rewrite map_nth.
        
        (* simpl in H7 that will be needed to specialize H *)
        specialize (H7 i H2). do 3 rewrite map_map in H7. remember (fun x : nat * nat * Expression =>
        snd (fst (let '(i, ls, x0) := x in (i, ls, x0.[upn (Datatypes.length ext + ls)
        (magic_ξ Γ Γ')])))) as Fsf.
        replace 0 with (Fsf (0,0,Val VNil)) in H7 by (subst;auto).
        remember (fun x : nat * nat * Expression => snd (let '(i, ls, x0) := x in
        (i, ls, x0.[upn (Datatypes.length ext + ls) (magic_ξ Γ Γ')]))) as Fs.
        replace (Val VNil) with (Fs (0,0,Val VNil)) in H7 by (subst;auto).
        do 2 rewrite map_nth in H7.
        
        specialize (H (Datatypes.length ext + FSF (nth i ext (0, 0, snd (0, 0, Val VNil))) + Γ)
        (Datatypes.length ext + Fsf (nth i ext (0, 0, Fs (0, 0, Val VNil))) + Γ')).
        rewrite map_length in H8. replace (Val VNil) with (snd (0,0,Val VNil)) in H by auto.
        rewrite map_nth in H. simpl in H. replace ((snd (nth i ext (0, 0, Val VNil))).[magic_ξ
        (Datatypes.length ext + FSF (nth i ext (0, 0, Val VNil)) + Γ)
        (Datatypes.length ext + Fsf (nth i ext (0, 0, Fs (0, 0, Val VNil))) + Γ')]) with
        (Fs (nth i ext (0, 0, Val VNil))) in H.
        ** specialize (H H7). clear H1 H2 H7 H8. exact H.
        ** subst. clear. simpl. destruct (nth i ext (0, 0, Val VNil)). simpl. destruct p. simpl.
           rewrite upn_magic. reflexivity.
      - clear H. inversion H1. subst. clear H1 H6. rewrite map_length in H7.
        specialize (H0 (Datatypes.length ext + vl + Γ) (Datatypes.length ext + vl + Γ')).
        rewrite <- upn_magic in H0. specialize (H0 H7). exact H0.
    * intros. constructor. inversion H0. subst. specialize (H (n + Γ) (n + Γ')).
      rewrite upn_magic in H4. specialize (H H4). exact H.
    * intros. constructor. intros. specialize (H i H1 Γ Γ'). inversion H0. subst.
      rewrite map_length in H3. specialize(H3 i H1).
      replace (Val VNil) with ((Val VNil).[magic_ξ Γ Γ']) in H3 by auto.
      rewrite map_nth in H3. specialize (H H3). exact H.
    * intros. constructor.
      - clear H0. specialize (H Γ Γ'). inversion H1. subst. specialize (H H3). exact H.
      - clear H. specialize (H0 Γ Γ'). inversion H1. subst. specialize (H0 H5). exact H0.
    * intros. constructor. intros. specialize (H i H1 Γ Γ'). inversion H0. subst.
      rewrite map_length in H3. specialize (H3 i H1). replace (Val VNil) with
      ((Val VNil).[magic_ξ Γ Γ']) in H3 by (auto). rewrite map_nth in H3. specialize (H H3).
      exact H.
    * intros. constructor.
      - intros. specialize (H i H1). destruct H. clear H2. specialize (H Γ Γ').
        inversion H0. subst. clear H4. rewrite map_length in H3. rewrite map_map in H3.
        specialize (H3 i H1). remember (fun x : Expression * Expression => fst (let
        '(x0, y) := x in (x0.[magic_ξ Γ Γ'], y.[magic_ξ Γ Γ']))) as Ff.
        replace (Val VNil) with (Ff (Val VNil,Val VNil)) in H3 by (subst;auto).
        rewrite map_nth in H3. 
        replace ((nth i (map fst l) (Val VNil)).[magic_ξ Γ Γ']) with
        (Ff (nth i l (Val VNil, Val VNil))) in H.
        + specialize (H H3). exact H.
        + subst. clear. simpl. replace ((Val VNil)) with (fst (Val VNil, Val VNil)) by auto.
          rewrite map_nth. simpl. destruct (nth i l (Val VNil, Val VNil)). simpl. reflexivity.
      - intros. specialize (H i H1). destruct H. clear H. specialize (H2 Γ Γ').
        inversion H0. subst. clear H3. rewrite map_length in H4. specialize (H4 i H1).
        rewrite map_map in H4. remember (fun x : Expression * Expression => snd (let
        '(x0, y) := x in (x0.[magic_ξ Γ Γ'], y.[magic_ξ Γ Γ']))) as Fs.
        replace (Val VNil) with (Fs (Val VNil, Val VNil)) in H4 by (subst;auto).
        rewrite map_nth in H4. replace ((nth i (map snd l) (Val VNil)).[magic_ξ Γ Γ']) with
        (Fs (nth i l (Val VNil, Val VNil))) in H2.
        + specialize (H2 H4). exact H2.
        + subst. clear. replace (Val VNil) with (snd (Val VNil,Val VNil)) by auto.
          rewrite map_nth. simpl. destruct (nth i l (Val VNil, Val VNil)). simpl. reflexivity.
    * intros. constructor. intros. specialize (H i H1 Γ Γ'). inversion H0. subst.
      rewrite map_length in H5. specialize (H5 i H1). replace (Val VNil) with 
      ((Val VNil).[magic_ξ Γ Γ']) in H5 by auto. rewrite map_nth in H5. specialize (H H5).
      exact H.
    * intros. constructor. intros. specialize (H i H1 Γ Γ'). inversion H0. subst.
      rewrite map_length in H5. specialize (H5 i H1). replace (Val VNil) with 
      ((Val VNil).[magic_ξ Γ Γ']) in H5 by auto. rewrite map_nth in H5. specialize (H H5).
      exact H.
    * intros. constructor.
      - specialize (H Γ Γ'). clear H0. inversion H1. subst. specialize (H H3).
        exact H.
      - intros. clear H. specialize (H0 i H2 Γ Γ'). inversion H1. subst. clear H4.
        rewrite map_length in H6. specialize (H6 i H2). replace (Val VNil) with
        ((Val VNil).[magic_ξ Γ Γ']) in H6 by auto. rewrite map_nth in H6.
        specialize (H0 H6). exact H0.
    * intros. constructor.
      - clear H0. specialize (H Γ Γ'). inversion H1. subst. specialize (H H3). exact H.
      - intros. clear H. specialize (H0 i H2). destruct H0. clear H0. inversion H1.
        subst. clear H1 H4 H7. rewrite map_length in H5. do 4 rewrite map_map in H5.
        specialize (H5 i H2).
        
        remember (fun x : list Pattern * Expression * Expression
        =>fst (fst (let '(p, x0, y) := x in (p, x0.[upn (patternListScope p) (magic_ξ Γ Γ')],
        y.[upn (patternListScope p) (magic_ξ Γ Γ')])))) as Fff.
        remember (fun x : list Pattern * Expression * Expression => snd (fst (let
        '(p, x0, y) := x in (p,  x0.[upn (patternListScope p) (magic_ξ Γ Γ')],
        y.[upn (patternListScope p) (magic_ξ Γ Γ')])))) as Fsf.
        
        replace nil with (Fff (nil, Val VNil, Val VNil)) in H5 by (subst;auto).
        replace (Val VNil) with (Fsf (nil, Val VNil, Val VNil)) in H5 by (subst;auto).
        do 2 rewrite map_nth in H5.
        
        do 2 rewrite map_map in *. remember (fun x : list Pattern * Expression * Expression =>
        fst (fst x)) as FFF.
        remember (fun x : list Pattern * Expression * Expression => snd (fst x)) as FSF.
        replace nil with (FFF (nil, Val VNil, Val VNil)) by (subst;auto).
        replace (Val VNil) with (FSF (nil, Val VNil, Val VNil)) by (subst;auto).
        replace (Val VNil) with (FSF (nil, Val VNil, Val VNil)) in H by (subst;auto).
        do 2 rewrite map_nth. rewrite map_nth in H.
        
        specialize (H (patternListScope (FFF (nth i l (nil, FSF (nil, Val VNil, Val VNil),
        FSF (nil, Val VNil, Val VNil)))) + Γ) (patternListScope (FFF (nth i l
        (nil, FSF (nil, Val VNil, Val VNil), FSF (nil, Val VNil, Val VNil)))) + Γ')).
        
        replace (Fff (nth i l (nil, Fsf (nil, Val VNil, Val VNil), Fsf (nil, Val VNil,
        Val VNil)))) with (FFF (nth i l (nil, FSF (nil, Val VNil, Val VNil),
        FSF (nil, Val VNil, Val VNil)))) in H5.
        + replace (Fsf (nth i l (nil, Val VNil, Val VNil))) with ((FSF (nth i l (nil, Val VNil,
          Val VNil))).[ magic_ξ (patternListScope (FFF (nth i l (nil, FSF (nil, Val VNil, Val VNil),
          FSF (nil, Val VNil, Val VNil)))) + Γ) (patternListScope (FFF (nth i l
          (nil, FSF (nil, Val VNil, Val VNil), FSF (nil, Val VNil, Val VNil)))) + Γ')]) in H5.
          ** specialize (H H5). exact H.
          ** subst. clear. simpl. destruct (nth i l (nil, Val VNil, Val VNil)). simpl.
             destruct p. simpl. rewrite upn_magic. reflexivity.
        + subst. clear. simpl. destruct (nth i l (nil, Val VNil, Val VNil)). simpl.
          destruct p. simpl. reflexivity.
      - intros. clear H. specialize (H0 i H2). destruct H0. clear H. inversion H1. subst.
        clear H1 H4 H5. rewrite map_length in H7. specialize (H7 i H2).
        do 3 rewrite map_map in H7.
        
        remember (fun x : list Pattern * Expression * Expression => fst (fst (let
        '(p, x0, y) := x in (p, x0.[upn (patternListScope p) (magic_ξ Γ Γ')],
        y.[upn (patternListScope p) (magic_ξ Γ Γ')])))) as Fff.
        remember (fun x : list Pattern * Expression * Expression => snd (let '(p, x0, y) := x
        in (p, x0.[upn (patternListScope p) (magic_ξ Γ Γ')], y.[upn (patternListScope p)
        (magic_ξ Γ Γ')]))) as Fs.
        
        replace nil with (Fff (nil, Val VNil, Val VNil)) in H7 by (subst;auto).
        replace (Val VNil) with (Fs (nil, Val VNil, Val VNil)) in H7 by (subst;auto).
        do 2 rewrite map_nth in H7.
        
        rewrite map_map. remember (fun x : list Pattern * Expression * Expression =>
        fst (fst x)) as FFF.
        
        replace nil with (FFF (nil, Val VNil, Val VNil)) by (subst;auto).
        replace (Val VNil) with (snd (nil:list Pattern, Val VNil, Val VNil)) by (subst;auto).
        do 2 rewrite map_nth.
        
        do 2 replace (Val VNil) with (snd (nil:list Pattern, Val VNil, Val VNil)) in H0 by auto.
        rewrite map_nth in H0.
        
        specialize (H0 (patternListScope (FFF (nth i l (nil:list Pattern, snd (nil:list Pattern,
        Val VNil, Val VNil), snd (nil:list Pattern, Val VNil, Val VNil)))) + Γ) (patternListScope
        (FFF (nth i l (nil:list Pattern, snd (nil:list Pattern, Val VNil, Val VNil),
        snd (nil:list Pattern, Val VNil, Val VNil)))) + Γ')).
        
        replace (Fff (nth i l (nil, Fs (nil, Val VNil, Val VNil), Fs (nil, Val VNil, Val VNil))))
        with (FFF (nth i l (nil : list Pattern, snd (nil : list Pattern, Val VNil, Val VNil),
        snd (nil : list Pattern, Val VNil, Val VNil)))) in H7.
        + replace (Fs (nth i l (nil, Val VNil, Val VNil))) with ((snd (nth i l
          (nil, snd (nil: list Pattern, Val VNil, Val VNil), snd (nil:list Pattern, Val VNil,
          Val VNil)))).[ magic_ξ (patternListScope (FFF (nth i l (nil : list Pattern,
          snd (nil : list Pattern, Val VNil, Val VNil), snd (nil : list Pattern, Val VNil,
          Val VNil)))) + Γ) (patternListScope (FFF (nth i l (nil : list Pattern,
          snd (nil : list Pattern, Val VNil, Val VNil), snd (nil : list Pattern, Val VNil, 
          Val VNil)))) + Γ')]) in H7.
          ** specialize (H0 H7). exact H0.
          ** subst. clear. simpl. destruct (nth i l (nil, Val VNil, Val VNil)). simpl.
             destruct p. simpl. rewrite upn_magic. reflexivity.
        + subst. clear. simpl. destruct (nth i l (nil, Val VNil, Val VNil)). simpl.
          destruct p. simpl. reflexivity.
    * intros. constructor.
      - clear H0. specialize (H Γ Γ'). inversion H1. subst. specialize (H H5). exact H.
      - clear H. specialize (H0 (l + Γ) (l + Γ')). inversion H1. subst. rewrite upn_magic in H6.
        specialize (H0 H6). exact H0.
    * intros. constructor. 
      - clear H0. inversion H1. subst. specialize (H Γ Γ' H3). exact H.
      - clear H. inversion H1. subst. specialize (H0 Γ Γ' H5). exact H0.
    * intros. constructor.
      - intros. clear H. inversion H1. subst. clear H1 H6. do 2 rewrite map_map in H4.
        rewrite map_length in H4. specialize (H4 i H2).
        
        remember (fun x : nat * Expression => fst (let '(n, x0) := x in (n,
        x0.[upn (Datatypes.length l + n) (magic_ξ Γ Γ')]))) as Ff.
        remember (fun x : nat * Expression => snd (let '(n, x0) := x in
        (n, x0.[upn (Datatypes.length l + n) (magic_ξ Γ Γ')]))) as Fs.
        
        replace 0 with (Ff (0,Val VNil)) in H4 by (subst;auto).
        replace (Val VNil) with (Fs (0,Val VNil)) in H4 by (subst;auto).
        do 2 rewrite map_nth in H4.
        
        replace 0 with (fst (0,Val VNil)) by auto.
        replace (Val VNil) with (snd (0,Val VNil)) by auto.
        do 2 rewrite map_nth.
        
        specialize (H0 i H2 (Datatypes.length l + fst (nth i l (0, snd (0, Val VNil)))
        + Γ) (Datatypes.length l + fst (nth i l (0, snd (0, Val VNil))) + Γ')).
        
        replace (Val VNil) with (snd (0,Val VNil)) in H0 by auto.
        rewrite map_nth in H0. simpl in *.
        
        replace (Ff (nth i l (0, Fs (0, Val VNil)))) with (fst (nth i l (0, Val VNil))) in H4.
        + replace (Fs (nth i l (0, Val VNil))) with ((snd (nth i l (0, Val VNil))).[magic_ξ
          (Datatypes.length l + fst (nth i l (0, Val VNil)) + Γ) (Datatypes.length l +
          fst (nth i l (0, Val VNil)) + Γ')]) in H4.
          ** specialize (H0 H4). exact H0.
          ** subst. clear. destruct (nth i l (0, Val VNil)). simpl.
             rewrite upn_magic. reflexivity.
        + subst. clear. simpl. destruct (nth i l (0, Val VNil)). simpl. reflexivity.
      - clear H0. inversion H1. subst. clear H3. rewrite map_length in H5.
        specialize (H (Datatypes.length l + Γ) (Datatypes.length l + Γ')).
        rewrite upn_magic in H5. specialize (H H5). exact H.
    * intros. constructor. 
      - clear H0 H1. inversion H2. subst. clear H2 H8 H9. specialize (H Γ Γ' H7).
        exact H.
      - clear H H1. inversion H2. subst. clear H2 H7 H9.
        specialize (H0 (vl1 + Γ) (vl1 + Γ')). rewrite upn_magic in H8.
        specialize (H0 H8). exact H0.
      - clear H H0. inversion H2. subst. clear H2 H7 H8.
        specialize (H1 (vl2 + Γ) (vl2 + Γ')). rewrite upn_magic in H9.
        specialize (H1 H9). exact H1.
    (*List*)
    * intros. inversion H.
    * intros. destruct i.
      - simpl in *. specialize (H Γ Γ' H2). exact H.
      - simpl in *. specialize (H0 i ltac:(lia) Γ Γ' H2). exact H0.
    * intros. inversion H.
    * intros. destruct i.
      - simpl in *. specialize (H Γ Γ' H2). exact H.
      - simpl in *. specialize (H0 i ltac:(lia) Γ Γ' H2). exact H0.
    * intros. inversion H.
    * intros. split.
      - intros. destruct i.
        + simpl in *. specialize (H Γ Γ' H3). exact H.
        + simpl in *. specialize (H1 i ltac:(lia)). destruct H1.
          specialize (H1 Γ Γ' H3). exact H1.
      - intros. destruct i.
        + simpl in *. specialize (H0 Γ Γ' H3). exact H0.
        + simpl in *. specialize (H1 i ltac:(lia)). destruct H1.
          specialize (H4 Γ Γ' H3). exact H4.
    * intros. inversion H.
    * intros. split.
       - intros. destruct i.
        + simpl in *. specialize (H Γ Γ' H3). exact H.
        + simpl in *. specialize (H1 i ltac:(lia)). destruct H1.
          specialize (H1 Γ Γ' H3). exact H1.
      - intros. destruct i.
        + simpl in *. specialize (H0 Γ Γ' H3). exact H0.
        + simpl in *. specialize (H1 i ltac:(lia)). destruct H1.
          specialize (H4 Γ Γ' H3). exact H4.
    * intros. inversion H.
    * intros. destruct i.
      - simpl in *. specialize (H Γ Γ' H2). exact H.
      - simpl in *. specialize (H0 i ltac:(lia) Γ Γ' H2). exact H0.
    * intros. inversion H.
    * intros. split.
       - intros. destruct i.
        + simpl in *. specialize (H Γ Γ' H3). exact H.
        + simpl in *. specialize (H1 i ltac:(lia)). destruct H1.
          specialize (H1 Γ Γ' H3). exact H1.
      - intros. destruct i.
        + simpl in *. specialize (H0 Γ Γ' H3). exact H0.
        + simpl in *. specialize (H1 i ltac:(lia)). destruct H1.
          specialize (H4 Γ Γ' H3). exact H4.
    * intros. inversion H.
    * intros. destruct i.
      - simpl in *. specialize (H Γ Γ' H2). exact H.
      - simpl in *. specialize (H0 i ltac:(lia) Γ Γ' H2). exact H0.
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

  Lemma sub_implies_scope_nval : forall e Γ Γ',
      (forall ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> NVAL Γ' ⊢ e.[ξ]ₑ) ->
      NVAL Γ ⊢ e.
  Proof.
    intros;
    eapply magic_ξ_implies_scope;
    apply H;
    apply magic_ξ_scope.
  Qed.

  Lemma sub_implies_scope_val : forall e Γ Γ',
      (forall ξ, SUBSCOPE Γ ⊢ ξ ∷ Γ' -> VAL Γ' ⊢ e.[ξ]ᵥ) ->
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
           then inl (VLit (Integer 0))
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

  Lemma magic_const : magic_ξ_2 0 = (VLit (Integer 0)) .: idsubst.
  Proof.
    unfold magic_ξ_2.
    extensionality x.
    destruct Compare_dec.lt_dec; unfold idsubst. inversion l.
    destruct Nat.eq_dec; subst; auto.
    destruct x; cbn; auto. lia.
  Qed.
  
  Lemma mapeq_if_ntheq :
    forall {A B : Type} (f : A -> B) (g : A -> B) (l : list A) (d : B),
    map f l = map g l <->
    forall i, i < length l -> nth i (map f l) d = nth i (map g l) d.
  Proof.
    split.
    * intros. f_equal. exact H.
    * intros. induction l.
      - simpl. reflexivity.
      - simpl. f_equal. Search list "=". Search "::".
        + specialize (H 0). simpl in H. Search "<" "0".
          specialize (H (Nat.lt_0_succ (Datatypes.length l))). exact H.
        + apply IHl. intros. specialize (H (S i)).
          remember (nth (S i) (map f (a :: l)) d = nth (S i) (map g (a :: l)) d)
          as F.
          simpl in H. specialize (H ltac:(lia)). subst. auto.
  Qed.
  
  Lemma magic_ξ_magic_ξ_2 :
      (forall e Γ',EXP Γ' ⊢ e.[magic_ξ_2 Γ'] ->
       e.[magic_ξ (S Γ') Γ'] = e.[magic_ξ_2 Γ']) /\
      (forall e Γ',NVAL Γ' ⊢ e.[magic_ξ_2 Γ']ₑ ->
       e.[magic_ξ (S Γ') Γ']ₑ = e.[magic_ξ_2 Γ']ₑ) /\
      (forall e Γ',VAL Γ' ⊢ e.[magic_ξ_2 Γ']ᵥ ->
       e.[magic_ξ (S Γ') Γ']ᵥ = e.[magic_ξ_2 Γ']ᵥ).
  Proof.
    eapply Exp_ind with
    (QV := fun l => forall i, i < length l -> (forall Γ',VAL Γ' ⊢ (nth i l VNil).[magic_ξ_2 Γ']ᵥ -> (nth i l VNil).[magic_ξ (S Γ') Γ']ᵥ = (nth i l VNil).[magic_ξ_2 Γ']ᵥ))
    (RV := fun l => forall i, i < length l -> (forall Γ', VAL Γ' ⊢ (nth i (map fst l) VNil).[magic_ξ_2 Γ']ᵥ -> (nth i (map fst l) VNil).[magic_ξ (S Γ') Γ']ᵥ = (nth i (map fst l) VNil).[magic_ξ_2 Γ']ᵥ) /\
(forall Γ', VAL Γ' ⊢ (nth i (map snd l) VNil).[magic_ξ_2 Γ']ᵥ -> (nth i (map snd l) VNil).[magic_ξ (S Γ') Γ']ᵥ = (nth i (map snd l) VNil).[magic_ξ_2 Γ']ᵥ))
    (VV := fun l => forall i, i < length l -> (forall Γ', EXP Γ' ⊢ (nth i (map snd l) (Val VNil)).[magic_ξ_2 Γ'] -> (nth i (map snd l) (Val VNil)).[magic_ξ (S Γ') Γ'] = (nth i (map snd l) (Val VNil)).[magic_ξ_2 Γ']))
    (Q := fun l => forall i, i < length l -> (forall Γ', EXP Γ' ⊢ (nth i l (Val VNil)).[magic_ξ_2 Γ'] -> (nth i l (Val VNil)).[magic_ξ (S Γ') Γ'] = (nth i l (Val VNil)).[magic_ξ_2 Γ']))
    (R := fun l => forall i, i < length l -> (forall Γ', EXP Γ' ⊢ (nth i (map fst l) (Val VNil)).[magic_ξ_2 Γ'] -> (nth i (map fst l) (Val VNil)).[magic_ξ (S Γ') Γ'] = (nth i (map fst l) (Val VNil)).[magic_ξ_2 Γ']) /\
(forall Γ', EXP Γ' ⊢ (nth i (map snd l) (Val VNil)).[magic_ξ_2 Γ'] -> (nth i (map snd l) (Val VNil)).[magic_ξ (S Γ') Γ'] = (nth i (map snd l) (Val VNil)).[magic_ξ_2 Γ']))
    (W := fun l => forall i, i < length l -> (forall Γ', EXP Γ' ⊢ (nth i (map snd (map fst l)) (Val VNil)).[magic_ξ_2 Γ'] -> (nth i (map snd (map fst l)) (Val VNil)).[magic_ξ (S Γ') Γ'] = (nth i (map snd (map fst l)) (Val VNil)).[magic_ξ_2 Γ']) /\
(forall Γ', EXP Γ' ⊢ (nth i (map snd l) (Val VNil)).[magic_ξ_2 Γ'] -> (nth i (map snd l) (Val VNil)).[magic_ξ (S Γ') Γ'] = (nth i (map snd l) (Val VNil)).[magic_ξ_2 Γ']))
    (Z := fun l => forall i, i < length l -> (forall Γ', EXP Γ' ⊢ (nth i (map snd l) (Val VNil)).[magic_ξ_2 Γ'] -> (nth i (map snd l) (Val VNil)).[magic_ξ (S Γ') Γ'] = (nth i (map snd l) (Val VNil)).[magic_ξ_2 Γ']))
    .
    * intros. simpl. f_equal. inversion H0. subst. specialize (H Γ' H2). exact H.
    * intros. simpl. f_equal. inversion H0. subst. specialize (H Γ' H2). exact H.
    * intros. simpl. reflexivity.
    * intros. simpl. reflexivity.
    * intros. simpl. f_equal.
      - clear H0. inversion H1. subst. specialize (H Γ' H3). exact H.
      - clear H. inversion H1. subst. specialize (H0 Γ' H5). exact H0.
    * intros. simpl. f_equal.
      apply (mapeq_if_ntheq (fun x : ValueExpression => x.[magic_ξ (S Γ') Γ']ᵥ)
      (fun x : ValueExpression => x.[magic_ξ_2 Γ']ᵥ) l (VNil)).
      intros. specialize (H i H1 Γ').
      inversion H0. subst. rewrite map_length in H3. specialize (H3 i H1).
      
      (* I need to seperate the two sides of "=" so that I can do a replace
      in them separately. So I will use remember and replace in the rememberd. *)
      remember (nth i (map (fun x : ValueExpression => x.[magic_ξ_2 Γ']ᵥ) l)
      VNil) as F. replace VNil with (VNil.[magic_ξ_2 Γ']ᵥ) in HeqF by auto.
      
      replace VNil with (VNil.[magic_ξ (S Γ') Γ']ᵥ) by auto. subst.
      
      do 2 rewrite map_nth. rewrite map_nth in H3.
      
      specialize (H H3). exact H.
      
    * intros. simpl. f_equal.
      apply (mapeq_if_ntheq (fun '(x, y) => (x.[magic_ξ (S Γ')
      Γ']ᵥ, y.[magic_ξ (S Γ') Γ']ᵥ)) (fun '(x, y) => (x.[magic_ξ_2 Γ']ᵥ,
      y.[magic_ξ_2 Γ']ᵥ)) l (VNil,VNil)).
      
      intros. specialize (H i H1). destruct H.
      
      specialize (H Γ'). specialize (H2 Γ'). inversion H0. subst.
      rewrite map_length in H4, H5. rewrite map_map in H4, H5.
      specialize (H4 i H1). specialize (H5 i H1).
      
      remember (fun x : ValueExpression * ValueExpression =>
      fst (let '(x0, y) := x in (x0.[magic_ξ_2 Γ']ᵥ, y.[magic_ξ_2 Γ']ᵥ)))
      as Ff.
      replace VNil with (Ff (VNil, VNil)) in H4 by (subst;auto).
      rewrite map_nth in H4.
      
      remember (fun x : ValueExpression * ValueExpression =>
      snd (let '(x0, y) := x in (x0.[magic_ξ_2 Γ']ᵥ, y.[magic_ξ_2 Γ']ᵥ)))
      as Fs.
      replace VNil with (Fs (VNil, VNil)) in H5 by (subst;auto).
      rewrite map_nth in H5.
      
      remember (nth i (map (fun '(x, y) => (x.[magic_ξ_2 Γ']ᵥ,
      y.[magic_ξ_2 Γ']ᵥ)) l) (VNil, VNil)) as R.
      remember (fun '(x, y) => (x.[magic_ξ_2 Γ']ᵥ, y.[magic_ξ_2 Γ']ᵥ)) as FR.
      replace (VNil, VNil) with (FR (VNil, VNil)) in HeqR by (subst;auto).
      rewrite map_nth in HeqR.
      
      remember (fun '(x, y) => (x.[magic_ξ (S Γ') Γ']ᵥ, y.[magic_ξ (S Γ') Γ']ᵥ))
      as FL.
      replace (VNil, VNil) with (FL (VNil, VNil)) by (subst;auto).
      rewrite map_nth. subst. clear H0.
      
      destruct (nth i l (VNil, VNil)) eqn:H6. f_equal.
      - replace VNil with (fst (VNil, VNil)) in H by auto.
        rewrite map_nth in H.
        replace v with (fst (nth i l (VNil, VNil))) in * by 
        (rewrite H6;simpl; reflexivity).
        simpl in H4.
        specialize (H H4).
        exact H.
      - replace VNil with (snd (VNil, VNil)) in H2 by auto.
        rewrite map_nth in H2.
        replace v0 with (snd (nth i l (VNil, VNil))) in * by 
        (rewrite H6;simpl; reflexivity).
        simpl in H5.
        specialize (H2 H5).
        exact H2.
    (* * intros. simpl. f_equal. 
      apply (mapeq_if_ntheq (fun x : ValueExpression => x.[magic_ξ (S Γ') Γ']ᵥ)
      (fun x : ValueExpression => x.[magic_ξ_2 Γ']ᵥ) el (VNil)).
      intros.
      
      specialize (H i H1 Γ'). inversion H0. subst. rewrite map_length in H3.
      specialize (H3 i H1).
      
      remember (nth i (map (fun x : ValueExpression => x.[magic_ξ_2 Γ']ᵥ) el)
      VNil) as R.
      replace VNil with (VNil.[magic_ξ_2 Γ']ᵥ) in HeqR by auto.
      rewrite map_nth in HeqR.
      
      replace VNil with (VNil.[magic_ξ (S Γ') Γ']ᵥ) by auto.
      rewrite map_nth. subst R.
      
      specialize (H H3). exact H. *)
    * intros. simpl in *. unfold magic_ξ_2, magic_ξ, idsubst in *.
      destruct Compare_dec.lt_dec.
      - inversion H. subst. destruct Compare_dec.lt_dec.
        + reflexivity.
        + lia.
      - destruct Compare_dec.lt_dec.
        + destruct Nat.eq_dec.
          ** reflexivity.
          ** lia.
        + destruct Nat.eq_dec.
          ** lia.
          ** inversion H. subst. lia.
    * intros. simpl in *. unfold magic_ξ_2, magic_ξ, idsubst in *.
      destruct Compare_dec.lt_dec.
      - inversion H. subst. destruct Compare_dec.lt_dec.
        + reflexivity.
        + lia.
      - destruct Compare_dec.lt_dec.
        + destruct Nat.eq_dec.
          ** reflexivity.
          ** lia.
        + destruct Nat.eq_dec.
          ** lia.
          ** inversion H. subst. lia.
    * intros. simpl. f_equal.
      - apply (mapeq_if_ntheq _ _ ext (0,0,Val VNil)). intros. clear H0.
        specialize (H i H2). inversion H1. subst. clear H1 H8.
        rewrite map_length in H7. specialize (H7 i H2). do 3 rewrite map_map in H7.
        
        remember (fun x : nat * nat * Expression => snd (fst (let '(i, ls, x0) := x in
        (i, ls, x0.[upn (Datatypes.length ext + ls) (magic_ξ_2 Γ')])))) as Ff.
        replace 0 with (Ff (0,0,Val VNil)) in H7 by (subst;auto).
        
        remember (fun x : nat * nat * Expression => snd (let '(i, ls, x0) := x in
        (i, ls, x0.[upn (Datatypes.length ext + ls) (magic_ξ_2 Γ')]))) as Fs.
        remember (nth i (map Fs ext) (Val VNil)) as Tmp.
        replace (Val VNil) with (Fs (0,0,Val VNil)) in HeqTmp by (subst;auto). subst Tmp.
        
        do 2 rewrite map_nth in H7.
        
        replace (Val VNil) with (snd (0,0,Val VNil)) in H by (auto).
        rewrite map_nth in H.
        
        specialize (H (Datatypes.length ext + Ff (nth i ext (0, 0, Val VNil)) + Γ')).
        
        replace ((snd (nth i ext (0, 0, Val VNil))).[magic_ξ_2 (Datatypes.length ext +
        Ff (nth i ext (0, 0, Val VNil)) + Γ')]) with (Fs (nth i ext (0, 0, Val VNil))) in H.
        + specialize (H H7). remember (fun '(i0, ls, x) => (i0, ls, x.[upn (Datatypes.length ext
          + ls) (magic_ξ (S Γ') Γ')])) as FL.
          
          remember (fun '(i0, ls, x) => (i0, ls, x.[upn (Datatypes.length ext + ls)
          (magic_ξ_2 Γ')])) as FR.
          
          remember (nth i (map FR ext) (0, 0, Val VNil)) as R.
          replace (0, 0, Val VNil) with (FR  (0, 0, Val VNil)) in HeqR by (subst;auto).
          rewrite map_nth in HeqR.
          
          replace (0, 0, Val VNil) with (FL (0, 0, Val VNil)) by (subst;auto).
          rewrite map_nth.
          subst R.
          
          Check (Fs (nth i ext (0, 0, Val VNil))).
          Check (FR (nth i ext (0, 0, Val VNil))).
          (* Here we need to use H to get the goal but H uses snd (l,r) where as
           the goal does not us snd but only uses the r. *)
          subst. clear H2 H7. simpl in *. destruct (nth i ext (0, 0, Val VNil)).
          simpl in *. destruct p. simpl in *. f_equal. rewrite upn_magic.
          rewrite <- plus_n_Sm. exact H.
          
        + subst. clear. destruct (nth i ext (0, 0, Val VNil)). simpl. destruct p. simpl.
          rewrite upn_magic_2. reflexivity.
      - specialize (H0 (Datatypes.length ext + vl + Γ')). inversion H1. subst. clear H1 H7.
        rewrite map_length in H8. rewrite (upn_magic_2 (Datatypes.length ext + vl) Γ') in H8.
        specialize (H0 H8). rewrite (upn_magic_2 (Datatypes.length ext + vl) Γ').
        rewrite (upn_magic (Datatypes.length ext + vl)). Search "S" "=" "+".
        rewrite <- plus_n_Sm. exact H0.
    * intros. simpl. f_equal. specialize (H (n + Γ')). inversion H0. subst.
      rewrite upn_magic_2 in H4. specialize (H H4). rewrite upn_magic.
      rewrite <- plus_n_Sm. rewrite upn_magic_2. exact H.
    * intros. simpl. f_equal. apply (mapeq_if_ntheq _ _ el (Val VNil)). intros.
      
      remember (nth i (map (fun x : Expression => x.[magic_ξ_2 Γ']) el) (Val VNil)) as R.
      replace (Val VNil) with ((Val VNil).[magic_ξ_2 Γ']) in HeqR by auto.
      rewrite map_nth in HeqR.
      
      replace (Val VNil) with ((Val VNil).[magic_ξ (S Γ') Γ']) by auto.
      rewrite map_nth. subst R.
      
      inversion H0. subst. rewrite map_length in H3. specialize (H3 i H1).
      replace (Val VNil) with ((Val VNil).[magic_ξ_2 Γ']) in H3 by auto.
      rewrite map_nth in H3. 
      
      specialize (H i H1 Γ' H3). exact H.
    * intros. simpl. f_equal.
      - clear H0. inversion H1. subst. specialize (H Γ' H3). exact H.
      - clear H. inversion H1. subst. specialize (H0 Γ' H5). exact H0.
    * intros. simpl. f_equal. apply (mapeq_if_ntheq _ _ l (Val VNil)). intros.
      
      remember (nth i (map (fun x : Expression => x.[magic_ξ_2 Γ']) l) (Val VNil)) as R.
      replace (Val VNil) with ((Val VNil).[magic_ξ_2 Γ']) in HeqR by auto.
      rewrite map_nth in HeqR.
      
      replace (Val VNil) with ((Val VNil).[magic_ξ (S Γ') Γ']) by auto.
      rewrite map_nth. subst R.
      
      inversion H0. subst. rewrite map_length in H3. specialize (H3 i H1).
      replace (Val VNil) with ((Val VNil).[magic_ξ_2 Γ']) in H3 by auto.
      rewrite map_nth in H3.
      
      specialize (H i H1 Γ' H3). exact H.
    * intros. simpl. f_equal. apply (mapeq_if_ntheq _ _ l (Val VNil, Val VNil)).
      intros. specialize (H i H1). destruct H. specialize (H Γ'). specialize (H2 Γ').
      
      inversion H0. subst. rewrite map_length in H4, H5. specialize (H4 i H1).
      specialize (H5 i H1).
      
      remember (nth i (map (fun '(x, y) => (x.[magic_ξ_2 Γ'], y.[magic_ξ_2 Γ'])) l)
      (Val VNil, Val VNil)) as R.
      remember (fun '(x, y) => (x.[magic_ξ_2 Γ'], y.[magic_ξ_2 Γ'])) as FM2.
      replace (Val VNil, Val VNil) with (FM2 (Val VNil, Val VNil)) in HeqR by (subst;auto).
      rewrite map_nth in HeqR.
      
      remember (fun '(x, y) => (x.[magic_ξ (S Γ') Γ'], y.[magic_ξ (S Γ') Γ'])) as FM.
      replace (Val VNil, Val VNil) with (FM (Val VNil, Val VNil)) by (subst;auto).
      rewrite map_nth. subst R.
      
      rewrite map_map in H4, H5.
      remember (fun x : Expression * Expression => fst (FM2 x)) as Ff.
      replace (Val VNil) with (Ff (Val VNil, Val VNil)) in H4 by (subst;auto).
      rewrite map_nth in H4.
      
      remember (fun x : Expression * Expression => snd (FM2 x)) as Fs.
      replace (Val VNil) with (Fs (Val VNil, Val VNil)) in H5 by (subst;auto).
      rewrite map_nth in H5.
      
      replace (Val VNil) with (fst (Val VNil, Val VNil)) in H by auto.
      rewrite map_nth in H.
      
      replace (Val VNil) with (snd (Val VNil, Val VNil)) in H2 by auto.
      rewrite map_nth in H2.
      
      subst. clear H0. destruct (nth i l (Val VNil, Val VNil)). simpl in *. f_equal.
      + specialize (H H4). exact H.
      + specialize (H2 H5). exact H2.
    * intros. simpl. f_equal. apply (mapeq_if_ntheq _ _ l (Val VNil)). intros.
      
      remember (nth i (map (fun x : Expression => x.[magic_ξ_2 Γ']) l) (Val VNil)) as R.
      replace (Val VNil) with ((Val VNil).[magic_ξ_2 Γ']) in HeqR by auto.
      rewrite map_nth in HeqR.
      
      replace (Val VNil) with ((Val VNil).[magic_ξ (S Γ') Γ']) by auto.
      rewrite map_nth. subst R.
      
      inversion H0. subst. rewrite map_length in H5. specialize (H5 i H1).
      replace (Val VNil) with ((Val VNil).[magic_ξ_2 Γ']) in H5 by auto.
      rewrite map_nth in H5.
      
      specialize (H i H1 Γ' H5). exact H.
    * intros. simpl. f_equal. apply (mapeq_if_ntheq _ _ l (Val VNil)). intros.
      
      remember (nth i (map (fun x : Expression => x.[magic_ξ_2 Γ']) l) (Val VNil)) as R.
      replace (Val VNil) with ((Val VNil).[magic_ξ_2 Γ']) in HeqR by auto.
      rewrite map_nth in HeqR.
      
      replace (Val VNil) with ((Val VNil).[magic_ξ (S Γ') Γ']) by auto.
      rewrite map_nth. subst R.
      
      inversion H0. subst. rewrite map_length in H5. specialize (H5 i H1).
      replace (Val VNil) with ((Val VNil).[magic_ξ_2 Γ']) in H5 by auto.
      rewrite map_nth in H5.
      
      specialize (H i H1 Γ' H5). exact H.
    * intros. simpl. inversion H1. subst. clear H1. f_equal.
      - specialize (H Γ' H4). exact H.
      - clear H H4. rewrite map_length in H6. apply (mapeq_if_ntheq _ _ l (Val VNil)). intros.
        
        remember (nth i (map (fun x : Expression => x.[magic_ξ_2 Γ']) l) (Val VNil)) as R.
        replace (Val VNil) with ((Val VNil).[magic_ξ_2 Γ']) in HeqR by auto.
        rewrite map_nth in HeqR.
        
        replace (Val VNil) with ((Val VNil).[magic_ξ (S Γ') Γ']) by auto.
        rewrite map_nth. subst R.
        
        specialize (H6 i H). replace (Val VNil) with ((Val VNil).[magic_ξ_2 Γ'])
        in H6 by auto. rewrite map_nth in H6.
        
        specialize (H0 i H Γ' H6). exact H0.
    * intros. simpl. inversion H1. subst. rewrite map_length in H5, H7. clear H1. f_equal.
      - clear H0 H5 H7. specialize (H Γ' H4). exact H.
      - clear H H4. apply (mapeq_if_ntheq _ _ l (nil, Val VNil,Val VNil)). intros.
        
        remember (nth i (map (fun '(p, x, y) => (p, x.[upn (patternListScope p) 
        (magic_ξ_2 Γ')], y.[upn (patternListScope p) (magic_ξ_2 Γ')])) l) 
        (nil, Val VNil, Val VNil)) as R.
        remember (fun '(p, x, y) => (p, x.[upn (patternListScope p) (magic_ξ_2 Γ')],
        y.[upn (patternListScope p) (magic_ξ_2 Γ')])) as FR.
        replace (nil, Val VNil, Val VNil) with (FR (nil, Val VNil, Val VNil)) in HeqR
        by (subst;auto). rewrite map_nth in HeqR.
        
        remember (fun '(p, x, y) => (p, x.[upn (patternListScope p) (magic_ξ (S Γ') Γ')],
        y.[upn (patternListScope p) (magic_ξ (S Γ') Γ')])) as FL.
        replace (nil, Val VNil, Val VNil) with (FL (nil, Val VNil, Val VNil)) by (subst;auto).
        rewrite map_nth. subst R.
        
        specialize (H0 i H). destruct H0. specialize (H5 i H). specialize (H7 i H).
        do 4 rewrite map_map in H5. do 3 rewrite map_map in H7.
        
        remember (fun x : list Pattern * Expression * Expression => fst (fst (FR x))) as Fff.
        remember (fun x : list Pattern * Expression * Expression => snd (fst (FR x))) as Fsf.
        replace nil with (Fff (nil,Val VNil,Val VNil)) in H5 by (subst;auto).
        remember (nth i (map Fsf l) (Val VNil)) as Tmp.
        replace (Val VNil) with (Fsf (nil,Val VNil,Val VNil)) in HeqTmp by (subst;auto).
        subst Tmp. do 2 rewrite map_nth in H5.
        
        remember (fun x : list Pattern * Expression * Expression => snd (FR x)) as Fs.
        replace nil with (Fff (nil,Val VNil,Val VNil)) in H7 by (subst;auto).
        remember (nth i (map Fs l) (Val VNil)) as Tmp.
        replace (Val VNil) with (Fs (nil,Val VNil,Val VNil)) in HeqTmp by (subst;auto).
        subst Tmp. do 2 rewrite map_nth in H7.
        
        rewrite map_map in H0.
        remember (fun x : list Pattern * Expression * Expression => snd (fst x)) as fsf.
        replace (Val VNil) with (fsf (nil,Val VNil,Val VNil)) in H0 by (subst;auto).
        rewrite map_nth in H0.
        
        replace (Val VNil) with (snd (nil : list Pattern,Val VNil,Val VNil)) in H1 by auto.
        rewrite map_nth in H1.
        
        specialize (H0 (patternListScope (Fff (nth i l (nil, Val VNil, Val VNil))) + Γ')).
        specialize (H1 (patternListScope (Fff (nth i l (nil, Val VNil, Val VNil))) + Γ')).
        
        subst. destruct (nth i l (nil, Val VNil, Val VNil)). simpl in *. destruct p. 
        simpl in *. f_equal.
        + f_equal. rewrite upn_magic. rewrite <- plus_n_Sm. rewrite upn_magic_2.
          rewrite upn_magic_2 in H5. specialize (H0 H5). exact H0.
        + rewrite upn_magic. rewrite <- plus_n_Sm. rewrite upn_magic_2.
          rewrite upn_magic_2 in H7. specialize (H1 H7). exact H1.
    * intros. simpl. inversion H1. subst. rewrite upn_magic_2. rewrite upn_magic.
      rewrite <- plus_n_Sm. clear H1. f_equal.
      - clear H0 H7. specialize (H Γ' H6). exact H.
      - clear H H6. rewrite upn_magic_2 in H7. specialize (H0 (l + Γ') H7). exact H0.
    * intros. simpl. inversion H1. subst. clear H1. f_equal.
      - specialize (H Γ' H4). exact H.
      - specialize (H0 Γ' H6). exact H0.
    * intros. simpl. inversion H1. subst. clear H1. rewrite map_length in H4,H6. f_equal.
      - apply (mapeq_if_ntheq _ _ l (0, Val VNil)). clear H H6. intros.
        specialize (H0 i H). specialize (H4 i H).
        
        replace (Val VNil) with (snd (0, Val VNil)) in H0 by auto.
        rewrite map_nth in H0.
        
        remember (fun '(n, x) => (n, x.[upn (Datatypes.length l + n) (magic_ξ (S Γ') Γ')]))
        as FL.
        remember (fun '(n, x) => (n, x.[upn (Datatypes.length l + n) (magic_ξ_2 Γ')]))
        as FR.
        
        remember (nth i (map FR l) (0, Val VNil)) as R.
        replace (0, Val VNil) with (FR (0, Val VNil)) in HeqR by (subst;auto).
        rewrite map_nth in HeqR.
        
        replace (0, Val VNil) with (FL (0, Val VNil)) by (subst;auto).
        rewrite map_nth. subst R.
        
        do 2 rewrite map_map in H4.
        remember (fun x : nat * Expression => fst (FR x)) as Ff.
        remember (fun x : nat * Expression => snd (FR x)) as Fs.
        replace 0 with (Ff (0,Val VNil)) in H4 by (subst;auto).
        remember (nth i (map Fs l) (Val VNil)) as Tmp.
        replace (Val VNil) with (Fs (0, Val VNil)) in HeqTmp by (subst;auto).
        subst Tmp. do 2 rewrite map_nth in H4. clear H.
        
        specialize (H0 (Datatypes.length l + Ff (nth i l (0, Val VNil)) + Γ')).
        subst. simpl in *. destruct (nth i l (0, Val VNil)). simpl in *.
        
        f_equal. rewrite upn_magic. rewrite <- plus_n_Sm. rewrite upn_magic_2.
        rewrite upn_magic_2 in H4. specialize (H0 H4). exact H0.
      - clear H0 H4. rewrite upn_magic_2 in H6. specialize (H (Datatypes.length l + Γ') H6).
        rewrite upn_magic_2. rewrite upn_magic. rewrite <- plus_n_Sm. exact H.
    * intros. simpl. inversion H2. subst. clear H2. do 2 rewrite upn_magic in *.
      do 2 rewrite <- plus_n_Sm. do 2 rewrite upn_magic_2 in *. f_equal.
      - specialize (H Γ' H9). exact H.
      - specialize (H0 (vl1 + Γ') H10). exact H0.
      - specialize (H1 (vl2 + Γ') H11). exact H1.
    (* Lists *)
    * intros. inversion H.
    * intros. destruct i.
      - simpl in *. specialize (H Γ' H2). exact H.
      - simpl in *. specialize (H0 i ltac:(lia) Γ' H2). exact H0.
    * intros. inversion H.
    * intros. destruct i.
      - simpl in *. specialize (H Γ' H2). exact H.
      - simpl in *. specialize (H0 i ltac:(lia) Γ' H2). exact H0.
    * intros. inversion H.
    * intros. split.
      - intros. destruct i.
        + auto.
        + simpl in *. specialize (H1 i ltac:(lia)). destruct H1.
          specialize (H1 Γ' H3). exact H1.
      - intros. destruct i.
        + auto.
        + simpl in *. specialize (H1 i ltac:(lia)). destruct H1.
          specialize (H4 Γ' H3). exact H4.
    * intros. inversion H.
    * intros. split.
      - intros. destruct i.
        + auto.
        + simpl in *. specialize (H1 i ltac:(lia)). destruct H1.
          specialize (H1 Γ' H3). exact H1.
      - intros. destruct i.
        + auto.
        + simpl in *. specialize (H1 i ltac:(lia)). destruct H1.
          specialize (H4 Γ' H3). exact H4.
    * intros. inversion H.
    * intros. destruct i.
      - simpl in *. specialize (H Γ' H2). exact H.
      - simpl in *. specialize (H0 i ltac:(lia) Γ' H2). exact H0.
    * intros. inversion H.
    * intros. split.
      - intros. destruct i.
        + auto.
        + simpl in *. specialize (H1 i ltac:(lia)). destruct H1.
          specialize (H1 Γ' H3). exact H1.
      - intros. destruct i.
        + auto.
        + simpl in *. specialize (H1 i ltac:(lia)). destruct H1.
          specialize (H4 Γ' H3). exact H4.
    * intros. inversion H.
    * intros. destruct i.
      - simpl in *. specialize (H Γ' H2). exact H.
      - simpl in *. specialize (H0 i ltac:(lia) Γ' H2). exact H0.
  Qed.
  
  (*
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
  *)
  
  Lemma magic_ξ_magic_ξ_2_closed : 
      (forall e, EXPCLOSED e.[ (VLit (Integer 0)) /] ->
      e.[magic_ξ 1 0] = e.[(VLit (Integer 0)) .: idsubst]) /\
      (forall e, NONVALCLOSED e.[ (VLit (Integer 0)) /]ₑ ->
      e.[magic_ξ 1 0]ₑ = e.[(VLit (Integer 0)) .: idsubst]ₑ) /\
      (forall e, VALCLOSED e.[ (VLit (Integer 0)) /]ᵥ ->
      e.[magic_ξ 1 0]ᵥ = e.[(VLit (Integer 0)) .: idsubst]ᵥ).
  Proof.
    intros.
    rewrite <- magic_const. Check magic_ξ_magic_ξ_2. pose proof magic_ξ_magic_ξ_2.
    destruct H. destruct H0. split.
    - clear H0 H1. intros. specialize (H e 0 H0). exact H.
    - clear H. split.
      + clear H1. intros. specialize (H0 e 0 H). exact H0.
      + clear H0. intros. specialize (H1 e 0 H). exact H1.
  Qed.
  
  (* Lemma sub_implies_scope_exp_1 : forall e,
      EXPCLOSED e.[ELit 0/] ->
      EXP 1 ⊢ e.
  Proof.
    intros;
      eapply magic_ξ_implies_scope.
    destruct (magic_ξ_magic_ξ_2_closed e).
    rewrite H0; auto.
  Qed. *)
  
  Lemma sub_implies_scope_exp_1 : forall e,
      EXPCLOSED e.[ (VLit (Integer 0)) /] ->
      EXP 1 ⊢ e.
  Proof.
    intros. eapply magic_ξ_implies_scope.
    pose proof magic_ξ_magic_ξ_2_closed as [H0 [_ _]].
    rewrite H0.
    - exact H.
    - exact H.
  Qed.
  
  (* Lemma sub_implies_scope_val_1 : forall e,
      VALCLOSED e.[ELit 0/] ->
      VAL 1 ⊢ e.
  Proof.
    intros;
      eapply magic_ξ_implies_scope.
    destruct (magic_ξ_magic_ξ_2_closed e).
    rewrite H1; auto.
  Qed. *)
  
  Lemma sub_implies_scope_val_1 : forall e,
      VALCLOSED e.[ (VLit (Integer 0)) /]ᵥ ->
      VAL 1 ⊢ e.
  Proof.
    intros. eapply magic_ξ_implies_scope.
    pose proof magic_ξ_magic_ξ_2_closed as [_ [_ H0]].
    rewrite H0.
    - exact H.
    - exact H.
  Qed.
  
  (* New *)
  Lemma sub_implies_scope_nval_1 : forall e,
      NONVALCLOSED e.[ (VLit (Integer 0)) /]ₑ ->
      NVAL 1 ⊢ e.
  Proof.
    intros. eapply magic_ξ_implies_scope.
    pose proof magic_ξ_magic_ξ_2_closed as [_ [H0 _]].
    rewrite H0.
    - exact H.
    - exact H.
  Qed.
  
End SUB_IMPLIES_SCOPE.


Definition subst_implies_scope_exp := SUB_IMPLIES_SCOPE.sub_implies_scope_exp.
Definition subst_implies_scope_val := SUB_IMPLIES_SCOPE.sub_implies_scope_val.
Definition subst_implies_scope_nval := SUB_IMPLIES_SCOPE.sub_implies_scope_nval.
Definition subst_implies_scope_exp_1 := SUB_IMPLIES_SCOPE.sub_implies_scope_exp_1.
Definition subst_implies_scope_val_1 := SUB_IMPLIES_SCOPE.sub_implies_scope_val_1.
Definition subst_implies_scope_nval_1 := SUB_IMPLIES_SCOPE.sub_implies_scope_nval_1.

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
    NONVALCLOSED v -> NONVALCLOSED v.[ξ]ₑ.
Proof.
  intros.
  rewrite nvclosed_ignores_sub;
    auto.
Qed.
Global Hint Resolve nvclosed_sub_closed : core.

