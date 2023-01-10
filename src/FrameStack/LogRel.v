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
    | F1, RExc e1 | m ↓ -> | F2, RExc e2 | ↓).

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
  | VLit l, VLit l' => if Lit_beq l l' then True else False
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
Section Val_ind_weakened.

Variables (P : Val -> Prop)
          (Q : list Val -> Prop)
          (R : list (Val * Val) -> Prop).
Hypotheses
  (HV1 : P VNil)
  (HV2 : forall l : Lit, P (VLit l))
  (HV3 : forall hd : Val, P hd -> forall tl : Val, P tl -> P (VCons hd tl))
  (HV4 : forall (l : list Val), Q l -> P (VTuple l))
  (HV5 : forall (l : list (Val * Val)), R l -> P (VMap l))
  (HV6 : forall n : Var, P (VVar n))
  (HV7 : forall n : FunId, P (VFunId n))
  (HV8 : forall (ext : list (nat * nat * Exp)) (id params : nat) (e : Exp),
  P (VClos ext id params e))
  (HQ1: Q [])
  (HQ2: forall (v : Val), P v -> forall (vl : list Val), Q vl -> Q (v::vl))
  (HR1: R [])
  (HR2: forall (v1 : Val), P v1 -> forall (v2 : Val), P v2 -> 
   forall (vl : list (Val * Val)), R vl -> R ((v1,v2)::vl)).

Fixpoint Val_ind_weakened (v : Val) : P v :=
  match v as x return P x with
  | VNil => HV1
  | VLit l => HV2 l
  | VCons hd tl => HV3 hd (Val_ind_weakened hd) tl (Val_ind_weakened tl)
  | VTuple l => HV4 l (list_ind Q HQ1 (fun e ls => HQ2 e (Val_ind_weakened e) ls) l)
  | VMap l => HV5 l (list_ind R HR1 (fun '(e1,e2) ls => HR2 e1 (Val_ind_weakened e1) e2 (Val_ind_weakened e2) ls) l)
  | VVar n => HV6 n
  | VFunId n => HV7 n
  | VClos ext id vl e => HV8 ext id vl e
  end.

End Val_ind_weakened.

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

Definition inf :=
  ELetRec
    [(0, °EApp (`VFunId (0, 0)) [])]
    (EApp (`VFunId (0, 0)) []).

Theorem inf_diverges :
  forall n Fs, ~|Fs, inf| n↓.
Proof.
  intros. intro. induction n using Wf_nat.lt_wf_ind.
  inv H. 2: inv H1.
  * simpl in *. inv H6. inv H4. inv H2. inv H5. 2: inv H.
    cbn in H7.
    unfold inf in H0. specialize (H0 (1 + k) ltac:(nia)).
    apply H0. econstructor. reflexivity. cbn. assumption.
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
    apply H3; auto. nia.
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
    - now rewrite Lit_eqb_refl.
    - destruct_scopes. split. now eapply IHv0_1. now eapply IHv0_2.
    - induction l; auto.
      fdestruct_scopes. split.
      + now apply H1.
      + apply IHl; auto. constructor. now apply indexed_to_forall.
    - induction l; auto.
      fdestruct_scopes. destruct a. split. 2: split.
      + apply H3. apply (H0 0). snia.
      + apply H3. apply (H2 0). snia.
      + apply IHl; auto. constructor.
        intros. apply (H0 (S i)). snia.
        intros. apply (H2 (S i)). snia.
    - inv P'. nia.
    - inv P'. nia.
    - split; auto. intros. nia.
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
  * now rewrite Lit_eqb_refl.
  * destruct_scopes. now apply IHv1.
  * destruct_scopes. now apply IHv2.
  * fdestruct_scopes. induction l; auto.
    destruct_foralls. split.
    rewrite <- Vrel_Fix_eq. now apply H2. intuition.
  * destruct_scopes. induction l; auto. destruct_foralls.
    destruct a. split. 2: split.
    1-2: rewrite <- Vrel_Fix_eq; apply H2.
    1: now apply (H1 0 ltac:(snia)).
    1: now apply (H3 0 ltac:(snia)).
    apply IHl; auto; intros.
    1: now apply (H1 (S i) ltac:(snia)).
    1: now apply (H3 (S i) ltac:(snia)).
  * inv H. nia.
  * inv H. nia.
  * nia.
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
  intuition. eapply H1 in H4. exact H4. nia. assumption.
  eapply H3. 3: exact H4. nia. assumption.
Qed.

Global Hint Resolve Frel_downclosed : core.

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
