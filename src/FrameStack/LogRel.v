From CoreErlang.FrameStack Require Export Termination.
Import ListNotations.

(** Because of this, reasoning about preorder relations is enough *)
Goal forall T : Type, forall R : relation T, Reflexive R -> Transitive R ->
  let R' := fun x y => R x y /\ R y x in Reflexive R' /\ Symmetric R' /\ Transitive R'.
Proof.
  intros. split. 2: split.
  * intro. unfold R'. split; apply H.
  * intro. intros. unfold R' in *. destruct H1.
    split; auto.
  * intro. intros. unfold R' in *. destruct H1, H2. split.
    - eapply H0; eauto.
    - eapply H0; eauto.
Qed.

Definition exc_rel (n : nat)
                    (Vrel : forall m, m <= n -> Val -> Val -> Prop)
                    (e1 e2 : Exception) : Prop :=
match e1, e2 with
  | (class1, reason1, details1), (class2, reason2, details2)  =>
    class1 = class2 /\
    (forall m (Hmn : m <= n),
    Vrel m Hmn reason1 reason2 /\
    Vrel m Hmn details1 details2)
end.

(* Normal forms are exceptions and value sequences! This is why there
   is two clauses. *)
Definition frame_rel (n : nat)
                     (Vrel : forall m, m <= n -> Val -> Val -> Prop)
                     (F1 F2 : FrameStack) : Prop :=
  FSCLOSED F1 /\ FSCLOSED F2 /\
  (forall m (Hmn : m <= n) (vl1 vl2 : ValSeq),
    list_biforall (Vrel m Hmn) vl1 vl2 ->
    | F1, RValSeq vl1 | m ↓ -> | F2, RValSeq vl2 | ↓)
  /\
  (forall m (Hmn : m <= n) (e1 e2 : Exception),
    exc_rel m (fun m' H => Vrel m' (Nat.le_trans _ _ _ H Hmn)) e1 e2 ->
    | F1, RExc e1 | m ↓ -> | F2, RExc e2 | ↓)
  /\
  (forall m (Hmn : m <= n), | F1, RBox | m ↓ -> | F2, RBox | ↓).

Definition exp_rel (n : nat)
                   (Vrel : forall m, m <= n -> Val -> Val -> Prop)
                   (p1 p2 : Exp)
                 : Prop :=
  EXPCLOSED p1 /\ EXPCLOSED p2 /\
  forall m (Hmn : m <= n) F1 F2,
     frame_rel m (fun m' H => Vrel m' (Nat.le_trans _ _ _ H Hmn)) F1 F2 ->
     | F1, RExp p1 | m ↓ -> | F2, RExp p2 | ↓
.

Fixpoint Vrel_rec (n : nat)
                  (Vrel : forall m, m < n -> Val -> Val -> Prop)
                  (v1 v2 : Val) : Prop :=
  VALCLOSED v1 /\ VALCLOSED v2 /\
  match v1, v2 with
  | VNil, VNil => True
  | VLit l, VLit l' => l = l'
  | VPid p, VPid p' => True
  | VCons hd tl, VCons hd' tl' => Vrel_rec n Vrel hd hd' /\ Vrel_rec n Vrel tl tl'
  | VTuple l, VTuple l' =>
    (fix go l l' :=
      match l, l' with
        | [], []        => True
        | x::xs, y::ys  => Vrel_rec n Vrel x y /\ go xs ys
        | _,  _         => False
      end) l l'
  | VMap l, VMap l' => 
    (fix go l l' :=
      match l, l' with
        | [], []        => True
        | (x1,x2)::xs, (y1,y2)::ys  => Vrel_rec n Vrel x1 y1 /\
                                       Vrel_rec n Vrel x2 y2 /\
                                       go xs ys
        | _,  _         => False
      end) l l'  
  | VClos ext id vc e, VClos ext' id' vc' e' =>
    vc = vc' /\
    id = id' /\ 
    (forall m (Hmn : m < n),
     forall (vl1 vl2 : list Val),
     length vl1 = vc -> (* list_biforall restricts the length of vl2, thus
                           this is sufficient*)
     list_biforall (Vrel m Hmn) vl1 vl2 ->
     exp_rel m (fun m' H => Vrel m' (Nat.le_lt_trans _ _ _ H Hmn))
                (e.[list_subst ((convert_to_closlist ext)++vl1) idsubst])
                (e'.[list_subst ((convert_to_closlist ext')++vl2) idsubst])
   )
  | _, _ => False
  end
.

Definition Vrel : nat -> Val -> Val -> Prop :=
  Fix Wf_nat.lt_wf _ Vrel_rec.

Definition Erel (n : nat) (e1 e2 : Exp) : Prop :=
  exp_rel n (fun m _ => Vrel m) e1 e2.

Definition Frel (n : nat) (K1 K2 : FrameStack) : Prop :=
  frame_rel n (fun m _ => Vrel m) K1 K2.

Definition Excrel (n: nat) (ex1 ex2 : Exception) : Prop :=
  exc_rel n (fun m _ => Vrel m) ex1 ex2.


(* --------------------------------------------------------------- *)

(** ξ and η assigns closed expressions to vars in Γ 
  Basically this says, ξ and η are equivalent pointwise for Γ
*)
Lemma Vrel_rec_pointwise {n : nat} :
  forall (f g : forall m : nat, (m < n)%nat -> Val -> Val -> Prop),
    (forall (m : nat) (p : (m < n)%nat), f m p = g m p) ->
    Vrel_rec n f = Vrel_rec n g.
Proof.
  intros.
  extensionality v1.
  extensionality v2. generalize dependent v2.
  induction v1 using Val_ind_weakened with
    (Q := Forall (
      fun v1 => forall v2 : Val, Vrel_rec n f v1 v2 = Vrel_rec n g v1 v2
    ))
    (R := Forall (
      fun '(v11, v12) =>
        (forall v2 : Val, Vrel_rec n f v11 v2 = Vrel_rec n g v11 v2)
      /\
        (forall v2 : Val, Vrel_rec n f v12 v2 = Vrel_rec n g v12 v2)
    )); try destruct v2; unfold Vrel_rec; intros; try reflexivity.
  * f_equal. f_equal. rewrite IHv1_1, IHv1_2; reflexivity.
  * do 2 f_equal.
    generalize dependent l0. induction l; destruct l0; try reflexivity; cbn.
    destruct_foralls; unfold Vrel_rec in *; f_equal.
    - now rewrite H2.
    - clear H2. now apply IHl with (l0 := l0) in H3.
  * do 2 f_equal.
    generalize dependent l0. induction l; destruct l0; try reflexivity; cbn.
    destruct a, p.
    destruct_foralls; simpl. f_equal. 2: f_equal.
    - fold Vrel_rec in *. now rewrite (proj1 H2).
    - fold Vrel_rec in *. now rewrite (proj2 H2).
    - clear H2. now apply IHl with (l0 := l0) in H3.
  * repeat f_equal.
    extensionality m.
    extensionality Hmn.
    extensionality v1'.
    extensionality v2'.
    rewrite H.
    extensionality l1.
    extensionality bif.
    f_equal.
    extensionality m'.
    extensionality H0.
    trivial.
  * auto.
  * auto.
  * auto.
  * auto.
Qed.

Lemma Vrel_Fix_eq : forall {n : nat} {v1 v2 : Val},
  Vrel n v1 v2
  = 
  Vrel_rec n (fun (m : nat) (_ : m < n) => Vrel m) v1 v2.
Proof.
  intros.
  unfold Vrel.
  rewrite Fix_eq by (auto using Vrel_rec_pointwise).
  trivial.
Qed.

Scheme le_dep_ind := Induction for le Sort Prop.

Ltac forall_to_Forall :=
  match goal with
  | [H : forall i : nat, i < length _ -> ?P (nth i _ _) |- _] =>
    apply indexed_to_forall in H
  end.
Ltac foralls_to_Foralls :=
  repeat forall_to_Forall.

Ltac fdestruct_scopes :=
  destruct_scopes;
  foralls_to_Foralls;
  destruct_foralls.

Lemma Vrel_downclosed :
  forall {n m : nat} {Hmn : m <= n} {v1 v2 : Val},
    Vrel n v1 v2 ->
    Vrel m v1 v2.
Proof.
  induction 1 using le_dep_ind;
    intros;
    eauto.
  generalize dependent v2.
  induction v1 using Val_ind_weakened with
  (Q := Forall (
    fun v1 => forall v2 : Val, Vrel (S m0) v1 v2 -> Vrel m v1 v2
  ))
  (R := Forall (
    fun '(v11, v12) =>
      (forall v2 : Val, Vrel (S m0) v11 v2 -> Vrel m v11 v2)
    /\
      (forall v2 : Val, Vrel (S m0) v12 v2 -> Vrel m v12 v2)
  )); try destruct v2; intros; intuition; try break_match_hyp; intros.
  * rewrite Vrel_Fix_eq.
    rewrite Vrel_Fix_eq in H. destruct H as [cl1 [cl2 H]].
    split. 2: split. 1-2: auto.
    simpl. simpl in H. intros.
    specialize (IHv1_1 v2_1). specialize (IHv1_2 v2_2).
    do 2 rewrite Vrel_Fix_eq in IHv1_1. do 2 rewrite Vrel_Fix_eq in IHv1_2.
    split. apply IHv1_1, H. apply IHv1_2, H.
  * rewrite Vrel_Fix_eq.
    rewrite Vrel_Fix_eq in H. simpl in *.
    intuition.
    generalize dependent l0. induction l; intros; auto.
    - destruct_foralls; destruct l0; intuition; simpl in *.
      + specialize (H4 v). do 2 rewrite Vrel_Fix_eq in H4. now apply H4.
      + apply H2; auto.
        fdestruct_scopes. constructor; now apply indexed_to_forall.
        fdestruct_scopes. constructor; now apply indexed_to_forall.
  * rewrite Vrel_Fix_eq.
    rewrite Vrel_Fix_eq in H. simpl in *.
    intuition.
    generalize dependent l0. induction l; intros; auto.
    - destruct_foralls; destruct l0; intuition; simpl in *.
      destruct a, p. intuition.
      + specialize (H2 v1). do 2 rewrite Vrel_Fix_eq in H2. now apply H2.
      + specialize (H7 v2). do 2 rewrite Vrel_Fix_eq in H7. now apply H7.
      + apply H1; auto;
        destruct_scopes.
        constructor; intros; [apply (H6 (S i) ltac:(slia))|apply (H12 (S i) ltac:(slia))].
        constructor; intros; [apply (H9 (S i) ltac:(slia))|apply (H11 (S i) ltac:(slia))].
  * rewrite Vrel_Fix_eq. rewrite Vrel_Fix_eq in H.
    unfold Vrel_rec at 1.
    unfold Vrel_rec at 1 in H. intuition.
    apply H4; auto. lia.
Qed.

Lemma Erel_downclosed :
  forall {n m : nat} {Hmn : m <= n} {e1 e2 : Exp},
    Erel n e1 e2 ->
    Erel m e1 e2.
Proof.
  intros.
  unfold Erel, exp_rel.
  unfold Erel, exp_rel in H.
  destruct H, H0. split; auto. split; auto.
  intros. eapply (H1 m0); eauto. lia.
Qed.

Lemma Excrel_downclosed :
  forall {n m : nat} {Hmn : m <= n} {e1 e2 : Exception},
    Excrel n e1 e2 ->
    Excrel m e1 e2.
Proof.
  intros.
  unfold Excrel, exc_rel in *. destruct e1, e2, p, p0.
  split. apply H.
  intros. split; eapply Vrel_downclosed; apply H; eassumption.
  Unshelve. 1-2: lia.
Qed.

Lemma Vrel_closed : forall {n : nat} {v1 v2 : Val},
    Vrel n v1 v2 ->
    VALCLOSED v1 /\ VALCLOSED v2.
Proof.
  intros. rewrite Vrel_Fix_eq in H.
  destruct v1, v2; destruct H as [Cl1 [Cl2 H]];
  split; try contradiction.
  all: auto.
Qed.

Lemma Vrel_closed_l : forall {n : nat} {v1 v2 : Val},
    Vrel n v1 v2 ->
    VALCLOSED v1.
Proof.
  intros.
  apply Vrel_closed in H.
  intuition.
Qed.

Global Hint Resolve Vrel_closed_l : core.

Lemma Vrel_closed_r : forall {n : nat} {v1 v2 : Val},
    Vrel n v1 v2 ->
    VALCLOSED v2.
Proof.
  intros.
  apply Vrel_closed in H.
  intuition.
Qed.

Global Hint Resolve Vrel_closed_r : core.

Lemma Erel_closed : forall {n : nat} {e1 e2 : Exp},
    Erel n e1 e2 ->
    EXPCLOSED e1 /\ EXPCLOSED e2.
Proof.
  intros.
  unfold Erel, exp_rel in H.
  intuition.
Qed.

Lemma Erel_closed_l : forall {n : nat} {e1 e2 : Exp},
    Erel n e1 e2 ->
    EXPCLOSED e1.
Proof.
  intros.
  apply Erel_closed in H.
  intuition.
Qed.

Global Hint Resolve Erel_closed_l : core.

Lemma Erel_closed_r : forall {n : nat} {e1 e2 : Exp},
    Erel n e1 e2 ->
    EXPCLOSED e2.
Proof.
  intros.
  apply Erel_closed in H.
  intuition.
Qed.

Global Hint Resolve Erel_closed_r : core.

(** closing substitutions *)
Definition Grel (n : nat) (Γ : nat) (ξ₁ ξ₂ : Substitution) : Prop :=
  SUBSCOPE Γ ⊢ ξ₁ ∷ 0 /\ SUBSCOPE Γ ⊢ ξ₂ ∷ 0 /\
  forall x, x < Γ -> 
    match (ξ₁ x), (ξ₂ x) with
    | inl e1, inl e2 => Vrel n e1 e2
    | _, _ => False
    end.


Lemma Grel_downclosed_helper : forall vals1 vals2 m n,
  m <= n -> length vals1 = length vals2 ->
  list_biforall (Vrel n) vals1 vals2 ->
  list_biforall (Vrel m) vals1 vals2.
Proof.
  intro. induction vals1 using list_length_ind; intros.
  destruct vals1, vals2.
  * constructor.
  * inversion H1.
  * inversion H1.
  * inversion H2. subst. constructor. 
    - eapply Vrel_downclosed. eauto.
    - eapply H; eauto.
Unshelve. auto.
Qed.

Lemma Grel_downclosed :
  forall {n m : nat} {Hmn : m <= n} {Γ : nat} {ξ₁ ξ₂ : Substitution},
    Grel n Γ ξ₁ ξ₂ ->
    Grel m Γ ξ₁ ξ₂ .
Proof.
  unfold Grel; intros.
  unfold Grel; intros. intuition.
  repeat break_match_goal; specialize (H2 x H1); try rewrite Heqs in H2; try rewrite Heqs0 in H2; [ intuition (eauto using Vrel_downclosed) | contradiction | contradiction ].
Qed.



Definition Vrel_open (Γ : nat) (v1 v2 : Val) :=
  forall n ξ₁ ξ₂,
  Grel n Γ ξ₁ ξ₂
->
  Vrel n (substVal ξ₁ v1) (substVal ξ₂ v2).

Definition Excrel_open (Γ : nat) (e1 e2 : Exception) :=
  forall n ξ₁ ξ₂,
  Grel n Γ ξ₁ ξ₂
->
  Excrel n e1.[ξ₁]ₑₓ e2.[ξ₂]ₑₓ.


Definition Erel_open (Γ : nat) (e1 e2 : Exp) :=
  forall n ξ₁ ξ₂,
  Grel n Γ ξ₁ ξ₂
->
  Erel n (subst ξ₁ e1) (subst ξ₂ e2).

Lemma Erel_open_closed : forall {Γ e1 e2},
    Erel_open Γ e1 e2 ->
    forall ξ, SUBSCOPE Γ ⊢ ξ ∷ 0 ->
              EXPCLOSED (e1.[ξ]) /\ EXPCLOSED (e2.[ξ]).
Proof.
  intros.
  apply @Erel_closed with (n:=0).
  apply H; auto.
  unfold Grel.
  intuition idtac. break_match_goal.
  (* rewrite Vrel_Fix_eq. unfold Vrel_rec at 1. *)
  specialize (H0 x H1) as P'. rewrite Heqs in P'. clear dependent ξ.
  * clear H H1 x e1 e2 Γ. rewrite Vrel_Fix_eq. revert P'. revert v.
    einduction v using Val_ind_weakened with
      (Q := Forall (
        fun v => VALCLOSED v -> Vrel_rec 0 (fun (m : nat) (_ : m < 0) => Vrel m) v v
      ))
      (R := Forall (
        fun '(v1, v2) =>
         (VALCLOSED v1 -> Vrel_rec 0 (fun (m : nat) (_ : m < 0) => Vrel m) v1 v1) /\
         (VALCLOSED v2 -> Vrel_rec 0 (fun (m : nat) (_ : m < 0) => Vrel m) v2 v2)
      )); intros; auto.
    all: split;[auto|split;auto].
    - destruct_scopes. split. now eapply IHv0_1. now eapply IHv0_2.
    - induction l; auto.
      fdestruct_scopes. split.
      + now apply H1.
      + apply IHl; auto. constructor. now apply indexed_to_forall.
    - induction l; auto.
      fdestruct_scopes. destruct a. split. 2: split.
      + apply H3. apply (H0 0). slia.
      + apply H3. apply (H2 0). slia.
      + apply IHl; auto. constructor.
        intros. apply (H0 (S i)). slia.
        intros. apply (H2 (S i)). slia.
    - inv P'. lia.
    - inv P'. lia.
    - split; auto. intros. split; auto. lia.
  * specialize (H0 x H1). rewrite Heqs in H0. lia.
Qed.

Lemma Erel_open_scope : forall {Γ e1 e2},
    Erel_open Γ e1 e2 ->
    EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2.
Proof.
  intros.
  pose proof (Erel_open_closed H).
  split;
  eapply (subst_implies_scope_exp); intros; apply H0; auto.
Qed.

Lemma Erel_open_scope_l : forall {Γ e1 e2},
    Erel_open Γ e1 e2 ->
    EXP Γ ⊢ e1.
Proof.
  intros. eapply Erel_open_scope in H. destruct H. auto.
Qed.

Global Hint Resolve Erel_open_scope_l : core.

Lemma Erel_open_scope_r : forall {Γ e1 e2},
    Erel_open Γ e1 e2 ->
    EXP Γ ⊢ e2.
Proof.
  intros. eapply Erel_open_scope in H. destruct H. auto.
Qed.

Global Hint Resolve Erel_open_scope_r : core.

Theorem Vrel_fundamental_0 v :
  VALCLOSED v -> Vrel 0 v v.
Proof.
  rewrite Vrel_Fix_eq. induction v using Val_ind_weakened with
    (Q := Forall (
      fun v => VALCLOSED v -> Vrel 0 v v
    ))
    (R := Forall (
      fun '(v1, v2) =>
        (VALCLOSED v1 -> Vrel 0 v1 v1)
        /\
        (VALCLOSED v2 -> Vrel 0 v2 v2)
    )); intros; simpl; intuition.
  * destruct_scopes. now apply IHv1.
  * destruct_scopes. now apply IHv2.
  * fdestruct_scopes. induction l; auto.
    destruct_foralls. split.
    rewrite <- Vrel_Fix_eq. now apply H2. intuition.
  * destruct_scopes. induction l; auto. destruct_foralls.
    destruct a. split. 2: split.
    1-2: rewrite <- Vrel_Fix_eq; apply H2.
    1: now apply (H1 0 ltac:(slia)).
    1: now apply (H3 0 ltac:(slia)).
    apply IHl; auto; intros.
    1: now apply (H1 (S i) ltac:(slia)).
    1: now apply (H3 (S i) ltac:(slia)).
  * inv H. lia.
  * inv H. lia.
  * lia.
  * constructor; auto. intro. rewrite Vrel_Fix_eq. now apply IHv.
  * constructor; auto. split; intro; rewrite Vrel_Fix_eq.
    now apply IHv1.
    now apply IHv2.
Qed.

Lemma Vrel_open_closed : forall {Γ v1 v2},
    Vrel_open Γ v1 v2 ->
    forall ξ, SUBSCOPE Γ ⊢ ξ ∷ 0 ->
              VALCLOSED (v1.[ξ]ᵥ) /\ VALCLOSED (v2.[ξ]ᵥ).
Proof.
  intros.
  apply @Vrel_closed with (n:=0).
  apply H; auto.
  unfold Grel.
  intuition idtac. break_match_goal. 2: {
    epose proof (H0 x H1). rewrite Heqs in H2. lia.
  }
  specialize (H0 x H1) as P'. rewrite Heqs in P'.
  now apply Vrel_fundamental_0.
Qed.

Lemma Vrel_open_scope : forall {Γ e1 e2},
    Vrel_open Γ e1 e2 ->
    VAL Γ ⊢ e1 /\ VAL Γ ⊢ e2.
Proof.
  intros.
  pose proof (Vrel_open_closed H).
  split;
  eapply (subst_implies_scope_val); intros; apply H0; auto.
Qed.

Lemma Vrel_open_scope_l : forall {Γ e1 e2},
    Vrel_open Γ e1 e2 ->
    VAL Γ ⊢ e1.
Proof.
  intros. eapply Vrel_open_scope in H. destruct H. auto.
Qed.

Global Hint Resolve Vrel_open_scope_l : core.

Lemma Vrel_open_scope_r : forall {Γ e1 e2},
    Vrel_open Γ e1 e2 ->
    VAL Γ ⊢ e2.
Proof.
  intros. eapply Vrel_open_scope in H. destruct H. auto.
Qed.

Global Hint Resolve Vrel_open_scope_r : core.

Lemma Frel_downclosed :
  forall {n m : nat} {Hmn : m <= n} {F1 F2 : FrameStack},
    Frel n F1 F2 ->
    Frel m F1 F2.
Proof.
  unfold Frel, frame_rel.
  intuition. eapply H1 in H5. exact H5. lia. assumption.
  eapply H2. 3: exact H5. lia. assumption.
  eapply H4. 2: eassumption. lia.
Qed.

Global Hint Resolve Frel_downclosed : core.

Ltac downclose_Vrel :=
  match goal with
  | [H : Vrel _ ?a ?b |- Vrel _ ?a ?b] =>
    eapply Vrel_downclosed; exact H
  end.

Lemma Frel_closed : forall {n : nat} {F1 F2 : FrameStack},
    Frel n F1 F2 ->
    FSCLOSED F1 /\ FSCLOSED F2.
Proof.
  intros.
  unfold Frel, frame_rel in H.
  intuition.
Qed.

Lemma Frel_closed_l : forall {n : nat} {F1 F2 : FrameStack},
    Frel n F1 F2 ->
    FSCLOSED F1.
Proof.
  intros.
  apply Frel_closed in H.
  intuition.
Qed.

Global Hint Resolve Frel_closed_l : core.

Lemma Frel_closed_r : forall {n : nat} {F1 F2 : FrameStack},
    Frel n F1 F2 ->
    FSCLOSED F2.
Proof.
  intros.
  apply Frel_closed in H.
  intuition.
Qed.

Global Hint Resolve Frel_closed_r : core.


Lemma biforall_vrel_scoped : forall vals1 vals2 Γ,
  list_biforall (Vrel_open Γ) vals1 vals2 ->
  Forall (fun e => VAL Γ ⊢ e) vals1 /\ Forall (fun e => VAL Γ ⊢ e) vals2.
Proof.
  induction vals1; intros; inversion H; subst; repeat constructor.
  * eapply Vrel_open_scope_l; eauto.
  * specialize (IHvals1 _ _ H4); apply IHvals1.
  * eapply Vrel_open_scope_r; eauto.
  * eapply IHvals1; eauto.
Qed.

Lemma biforall_erel_scoped : forall vals1 vals2 Γ,
  list_biforall (Erel_open Γ) vals1 vals2 ->
  Forall (fun e => EXP Γ ⊢ e) vals1 /\ Forall (fun e => EXP Γ ⊢ e) vals2.
Proof.
  induction vals1; intros; inversion H; subst; split; constructor.
  * eapply Erel_open_scope_l; eauto.
  * specialize (IHvals1 _ _ H4); apply IHvals1.
  * eapply Erel_open_scope_r; eauto.
  * eapply IHvals1; eauto.
Qed.

Lemma biforall_vrel_closed : forall vals1 vals2 m,
  list_biforall (Vrel m) vals1 vals2 ->
  Forall (fun e => VALCLOSED e) vals1 /\ Forall (fun e => VALCLOSED e) vals2.
Proof.
  induction vals1; intros; inversion H; subst; repeat constructor.
  * eapply Vrel_closed_l; eauto.
  * specialize (IHvals1 _ _ H4); apply IHvals1.
  * eapply Vrel_closed_r; eauto.
  * eapply IHvals1; eauto.
Qed.

Lemma biforall_erel_closed : forall vals1 vals2 m,
  list_biforall (Erel m) vals1 vals2 ->
  Forall (fun e => EXPCLOSED e) vals1 /\ Forall (fun e => EXPCLOSED e) vals2.
Proof.
  induction vals1; intros; inversion H; subst; split; constructor.
  * eapply Erel_closed_l; eauto.
  * specialize (IHvals1 _ _ H4); apply IHvals1.
  * eapply Erel_closed_r; eauto.
  * eapply IHvals1; eauto.
Qed.

Lemma Grel_scons : forall n v1 v2 ξ₁ ξ₂ Γ,
  Grel n Γ ξ₁ ξ₂ -> Vrel n v1 v2 -> Grel n (S Γ) (v1.:ξ₁) (v2.:ξ₂).
Proof.
  intros. split. 2: split.
  1-2: apply cons_scope; auto.
  2, 4: apply H. 1-2: now apply Vrel_closed in H0.
  intros. destruct x; simpl; auto.
  apply H. lia.
Qed.

Corollary Grel_list : forall n vl1 vl2 ξ₁ ξ₂ Γ,
  Grel n Γ ξ₁ ξ₂ -> list_biforall (Vrel n) vl1 vl2 ->
  Grel n (length vl1 + Γ) (list_subst vl1 ξ₁) (list_subst vl2 ξ₂).
Proof.
  induction vl1; intros; inversion H0; subst; simpl; auto.
  apply Grel_scons; auto.
Qed.

(* To avoid unnecessary case separations: *)
Lemma Vrel_possibilities : forall {n v1 v2},
  Vrel n v1 v2 ->
  (v1 = VNil /\ v2 = VNil) \/
  (exists n, v1 = VLit n /\ v2 = VLit n) \/
  (exists p1 p2, v1 = VPid p1 /\ v2 = VPid p2) \/
  (exists v11 v12 v21 v22, v1 = VCons v11 v12 /\ v2 = VCons v21 v22) \/
  (exists l l', v1 = VTuple l /\ v2 = VTuple l') \/
  (exists l l', v1 = VMap l /\ v2 = VMap l') \/
  (exists ext1 ext2 id1 id2 vl1 vl2 b1 b2,
    v1 = VClos ext1 id1 vl1 b1 /\ v2 = VClos ext2 id2 vl2 b2).
Proof.
  intros; destruct v1, v2; destruct H as [? [? ?] ]; subst; try contradiction.
  * left. auto.
  * right. left. repeat eexists.
  * right. right. left. repeat eexists.
  * right. right. right. left. repeat eexists.
  * right. right. right. right. left. repeat eexists.
  * right. right. right. right. right. left. repeat eexists.
  * right. right. right. right. right. right. repeat eexists.
Qed.

Ltac Vrel_possibilities H0 :=
  let H0' := fresh "H" in
  apply Vrel_possibilities in H0 as H0'; intuition; destruct_hyps; subst.


Lemma Grel_list_subst m vl' Γ ξ₁ ξ₂:
  forall vl1 vl2,
  list_biforall (Vrel m) vl1 vl2 ->
  Grel m Γ ξ₁ ξ₂ ->
  length vl1 = vl' ->
  Grel m (vl' + Γ) (upn vl' ξ₁ >> list_subst vl1 idsubst)
  (upn vl' ξ₂ >> list_subst vl2 idsubst).
Proof.
  split. 2: split.
  1-2: eapply substcomp_scoped.
  1,3: apply upn_scope; now apply H0.
  1-2: apply scoped_list_subscoped_eq; auto.
  all: apply biforall_length in H as HB.
  2: lia.
  {
    rewrite indexed_to_forall; intros.
    eapply biforall_forall with (i := i) in H. 2: lia.
    apply Vrel_closed_l in H. eassumption.
  }
  {
    rewrite indexed_to_forall; intros.
    eapply biforall_forall with (i := i) in H.
    2: lia.
    apply Vrel_closed_r in H. eassumption.
  }
  intros.
  assert (x < vl' \/ x >= vl') as [LT | LT] by lia.
  {
    rewrite substcomp_list_eq, substcomp_list_eq. 2-3: lia.
    do 2 rewrite substcomp_id_r.
    rewrite list_subst_lt, list_subst_lt. 2-3: lia.
    eapply biforall_forall with (i := x) in H. eassumption.
    lia.
  }
  {
    rewrite substcomp_list_eq, substcomp_list_eq. 2-3: lia.
    do 2 rewrite substcomp_id_r.
    rewrite list_subst_ge, list_subst_ge. 2-3: lia.
    destruct H0 as [_ [_ H0]].
    rewrite HB. apply H0. lia.
  }
  Unshelve. all: exact VNil.
Qed.

Definition Rrel (n : nat) (r1 r2 : Redex) :=
  REDCLOSED r1 /\ REDCLOSED r2 /\
  forall m (Hmn : m <= n) F1 F2, Frel m F1 F2 ->
    | F1, r1 | m ↓ -> | F2, r2 | ↓.

Definition Rrel_open (Γ : nat) (r1 r2 : Redex) :=
  forall (n : nat) (ξ₁ ξ₂ : Substitution),
  Grel n Γ ξ₁ ξ₂ -> Rrel n r1.[ξ₁]ᵣ r2.[ξ₂]ᵣ.

Theorem Rrel_downclosed :
  forall n r1 r2, Rrel n r1 r2 -> forall m, m <= n -> Rrel m r1 r2.
Proof.
  intros. destruct H as [Hcl1 [Hcl2 H]]. split. 2: split.
  1-2: auto.
  intros. eapply H. 3: exact H2. lia. eapply Frel_downclosed. eassumption.
  Unshelve. lia.
Qed.

Lemma Vrel_ind :
  forall (P : Val -> Val -> Prop)
  (HNil : P VNil VNil)
  (HLit : forall l, P (VLit l) (VLit l))
  (HPid : forall p1 p2, P (VPid p1) (VPid p2))
  (HClos : forall ext ident vl e ext' ident' e', P (VClos ext ident vl e) (VClos ext' ident' vl e'))
  (HCons : forall v1 v2 v1' v2', P v1 v1' -> P v2 v2' -> P (VCons v1 v2) (VCons v1' v2'))
  (HTuple : forall l l', list_biforall P l l' -> P (VTuple l) (VTuple l'))
  (HMap : forall l l', list_biforall (fun '(a, b) '(a', b') => P a a' /\ P b b') l l' -> P (VMap l) (VMap l')),
  forall {m} v1 v2 (IH: Vrel m v1 v2),
  P v1 v2.
Proof.
  intros ? ? ? ? ? ? ? ? ?. valinduction; try destruct v2; intros.
  all: try rewrite Vrel_Fix_eq in IH.
  all: try destruct IH as [IHv1 [IHv2 IH]]; try inv IH; auto.
  all: try destruct_hyps; try contradiction.
  * now subst.
  (* * now subst. *)
  * rewrite <- Vrel_Fix_eq in H. rewrite <- Vrel_Fix_eq in H0.
    apply IHv1_1 in H; auto.
  * apply HTuple. generalize dependent l0. induction l; destruct l0; intros; try contradiction; constructor.
    - inv IHv1. apply H4; auto. destruct H1. now rewrite Vrel_Fix_eq.
    - destruct H1. apply IHl; auto.
      now inv IHv1.
      all: inv H0; inv H; constructor; intros.
      1: apply (H4 (S i)); slia.
      1: apply (H5 (S i)); slia.
  * apply HMap. generalize dependent l0. induction l; destruct l0; try destruct a; try destruct p;
    intros; try contradiction; constructor.
    - inv IHv1. inv H4. split.
      + apply H2; auto. destruct H1. now rewrite Vrel_Fix_eq.
      + apply H3; auto. destruct H1. now rewrite Vrel_Fix_eq.
    - destruct H1 as [H1_1 [H1_2 H1]]. apply IHl; auto.
      now inv IHv1.
      all: inv H0; inv H; constructor; intros.
      1: apply (H2 (S i)); slia.
      1: apply (H6 (S i)); slia.
      1: apply (H3 (S i)); slia.
      1: apply (H5 (S i)); slia.
Qed.
