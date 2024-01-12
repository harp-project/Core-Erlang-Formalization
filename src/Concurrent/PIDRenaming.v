From CoreErlang.FrameStack Require Import SubstSemanticsLemmas.
From stdpp Require Export gmap sets.

Import ListNotations.

Fixpoint renamePID (from to : PID) (e : Exp) : Exp :=
match e with
 | VVal e => VVal (renamePIDVal from to e)
 | EExp e => EExp (renamePIDNVal from to e)
end
with renamePIDVal (from to : PID) (v : Val) : Val :=
match v with
 | VNil => VNil
 | VLit l => VLit l
 | VPid p =>
   if Nat.eqb from p then VPid to else VPid p
 | VCons hd tl => VCons (renamePIDVal from to hd) (renamePIDVal from to tl)
 | VTuple l => VTuple (map (renamePIDVal from to) l)
 | VMap l => VMap (map (fun '(x,y) => (renamePIDVal from to x, renamePIDVal from to y)) l)
 | VVar n => VVar n
 | VFunId n => VFunId n
 | VClos ext id params e => VClos (map (fun '(id, vl, e) => (id, vl, renamePID from to e)) ext) id params (renamePID from to e)
end
with renamePIDNVal (from to : PID) (n : NonVal) : NonVal :=
match n with
 | EFun vl e => EFun vl (renamePID from to e)
 | EValues el => EValues (map (renamePID from to) el)
 | ECons hd tl => ECons (renamePID from to hd) (renamePID from to tl)
 | ETuple l => ETuple (map (renamePID from to) l)
 | EMap l => EMap (map (fun '(x,y) => (renamePID from to x, renamePID from to y)) l)
 | ECall m f l => ECall (renamePID from to m) (renamePID from to f) (map (renamePID from to) l)
 | EPrimOp f l => EPrimOp f (map (renamePID from to) l)
 | EApp exp l => EApp (renamePID from to exp) (map (renamePID from to) l)
 | ECase e l => ECase (renamePID from to e)
                      (map (fun '(p, g, e) => (p, renamePID from to g, renamePID from to e)) l)
 | ELet l e1 e2 => ELet l (renamePID from to e1) (renamePID from to e2)
 | ESeq e1 e2 => ESeq (renamePID from to e1) (renamePID from to e2)
 | ELetRec l e => ELetRec (map (fun '(vl, e) => (vl, renamePID from to e)) l)
                          (renamePID from to e)
 | ETry e1 vl1 e2 vl2 e3 => ETry (renamePID from to e1)
                                 vl1 (renamePID from to e2)
                                 vl2 (renamePID from to e3)
end.

Notation "e .⟦ x ↦ y ⟧" := (renamePID x y e) (at level 2, left associativity).
Notation "e .⟦ x ↦ y ⟧ᵥ" := (renamePIDVal x y e) (at level 2, left associativity).
Notation "e .⟦ x ↦ y ⟧ₙ" := (renamePIDNVal x y e) (at level 2, left associativity).

Definition renamePIDRed (from to : PID) (r : Redex) : Redex :=
match r with
 | RExp e => RExp (renamePID from to e)
 | RValSeq vs => RValSeq (map (renamePIDVal from to) vs)
 | RExc (class, reas, det) => RExc (class, renamePIDVal from to reas,
                                           renamePIDVal from to det)
 | RBox => RBox
end.

Notation "e .⟦ x ↦ y ⟧ᵣ" := (renamePIDRed x y e) (at level 2, left associativity).

Definition renamePIDFrameId (from to : PID) (f : FrameIdent) : FrameIdent :=
match f with
 | IValues => f
 | ITuple => f
 | IMap => f
 | ICall m f => ICall (renamePIDVal from to m) (renamePIDVal from to f)
 | IPrimOp f => IPrimOp f
 | IApp v => IApp (renamePIDVal from to v)
end.

Notation "e .⟦ x ↦ y ⟧ᵢ" := (renamePIDFrameId x y e) (at level 2, left associativity).

Definition renamePIDFrame (from to : PID) (f : Frame) : Frame :=
match f with
 | FCons1 hd => FCons1 (renamePID from to hd)
 | FCons2 tl => FCons2 (renamePIDVal from to tl)
 | FParams ident vl el =>
     FParams (renamePIDFrameId from to ident) (map (renamePIDVal from to) vl)
                                                (map (renamePID from to) el)
 | FApp1 l => FApp1 (map (renamePID from to) l)
 | FCallMod f l => FCallMod (renamePID from to f) (map (renamePID from to) l)
 | FCallFun m l => FCallFun (renamePIDVal from to m) (map (renamePID from to) l)
 | FCase1 l => FCase1 (map (fun '(p, g, e) => (p, renamePID from to g, renamePID from to e)) l)
 | FCase2 lv ex le =>
   FCase2
     (map (renamePIDVal from to) lv)
     (renamePID from to ex)
     (map (fun '(p, g, e) => (p, renamePID from to g, renamePID from to e)) le)
 | FLet l e => FLet l (renamePID from to e)
 | FSeq e => FSeq (renamePID from to e)
 | FTry vl1 e2 vl2 e3 => FTry vl1 (renamePID from to e2)
                              vl2 (renamePID from to e3)
end.

Notation "e .⟦ x ↦ y ⟧ₖ" := (renamePIDFrame x y e) (at level 2, left associativity).

Definition renamePIDStack (from to : PID) (fs : FrameStack) :=
  map (renamePIDFrame from to) fs.

Notation "e .⟦ x ↦ y ⟧ₛₜ" := (renamePIDStack x y e) (at level 2,left associativity).

Lemma renamePID_preserves_scope :
  (forall Γ e, EXP Γ ⊢ e -> forall from to, EXP Γ ⊢ renamePID from to e) /\
  (forall Γ e, VAL Γ ⊢ e -> forall from to, VAL Γ ⊢ renamePIDVal from to e) /\
  (forall Γ e, NVAL Γ ⊢ e -> forall from to, NVAL Γ ⊢ renamePIDNVal from to e).
Proof.
  apply scoped_ind; intros; cbn; try now constructor.
  * break_match_goal; constructor.
  * constructor. intros.
    rewrite map_nth with (d := VNil).
    rewrite map_length in H0. eapply H in H0.
    eassumption.
  * constructor; intros.
    - rewrite map_map.
      rewrite map_nth with (d := (VNil, VNil)).
      rewrite map_length in H1. eapply H in H1.
      rewrite map_nth with (d := (VNil, VNil)) in H1.
      destruct nth. eassumption.
    - rewrite map_map.
      rewrite map_nth with (d := (VNil, VNil)).
      rewrite map_length in H1. eapply H0 in H1.
      rewrite map_nth with (d := (VNil, VNil)) in H1.
      destruct nth. eassumption.
  * constructor; intros.
    - do 2 rewrite map_map.
      do 2 rewrite map_nth with (d := (0, 0, ˝VNil)).
      rewrite map_length in H1. eapply H in H1.
      do 2 rewrite map_nth with (d := (0, 0, ˝VNil)) in H1.
      destruct nth, p. rewrite map_length. eassumption.
    - rewrite map_length. auto.
  * constructor. intros.
    rewrite map_nth with (d := ˝VNil).
    rewrite map_length in H0. eapply H in H0.
    eassumption.
  * constructor; intros.
    - rewrite map_map.
      rewrite map_nth with (d := (˝VNil, ˝VNil)).
      rewrite map_length in H1. eapply H in H1.
      rewrite map_nth with (d := (˝VNil, ˝VNil)) in H1.
      destruct nth. eassumption.
    - rewrite map_map.
      rewrite map_nth with (d := (˝VNil, ˝VNil)).
      rewrite map_length in H1. eapply H0 in H1.
      rewrite map_nth with (d := (˝VNil, ˝VNil)) in H1.
      destruct nth. eassumption.
  * constructor. intros.
    rewrite map_nth with (d := ˝VNil).
    rewrite map_length in H0. eapply H in H0.
    eassumption.
  * constructor; intros.
    - rewrite map_nth with (d := ˝VNil).
      rewrite map_length in H2. eapply H in H2.
      eassumption.
    - auto.
    - auto.
  * constructor. intros.
    rewrite map_nth with (d := ˝VNil).
    rewrite map_length in H0. eapply H in H0.
    eassumption.
  * constructor; intros.
    - auto.
    - rewrite map_nth with (d := ˝VNil).
      rewrite map_length in H1. eapply H0 in H1.
      eassumption.
  * constructor; intros.
    - auto.
    - do 2 rewrite map_map.
      rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
      rewrite map_nth with (f := (fun x : list Pat * Exp * Exp =>
             (fst ∘ fst)
               (let
                '(p, g, e3) := x in
                 (p, renamePID from to g, renamePID from to e3)))) (d := ([], ˝VNil, ˝VNil)).
      rewrite map_length in H2. eapply H0 in H2.
      rewrite map_nth with (d := ([], ˝VNil, ˝VNil)) in H2.
      setoid_rewrite (map_nth (fst ∘ fst)) with (d := ([], ˝VNil, ˝VNil)) in H2.
      destruct nth, p. cbn in *. eassumption.
    - do 2 rewrite map_map.
      rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
      rewrite map_nth with (f := (fun x : list Pat * Exp * Exp =>
             (fst ∘ fst)
               (let
                '(p, g, e3) := x in
                 (p, renamePID from to g, renamePID from to e3)))) (d := ([], ˝VNil, ˝VNil)).
      rewrite map_length in H2. eapply H1 in H2.
      rewrite map_nth with (d := ([], ˝VNil, ˝VNil)) in H2.
      setoid_rewrite (map_nth (fst ∘ fst)) with (d := ([], ˝VNil, ˝VNil)) in H2.
      destruct nth, p. cbn in *. eassumption.
  * constructor; intros.
    - do 2 rewrite map_map.
      rewrite map_length in *. eapply H in H1.
      do 2 rewrite map_nth with (d := (0, ˝VNil)).
      do 2 rewrite map_nth with (d := (0, ˝VNil)) in H1.
      destruct nth. cbn in *. eassumption.
    - rewrite map_length. apply H0.
Qed.

Definition renamePID_subst (from to : PID) (σ : Substitution) : Substitution :=
  fun x =>
    match σ x with
    | inl val => inl (renamePIDVal from to val)
    | r => r
    end.

Theorem rename_renamePID :
  (forall e ρ from to, rename ρ (renamePID from to e) =
                      renamePID from to (rename ρ e)) /\
  (forall e ρ from to, renameNonVal ρ (renamePIDNVal from to e) =
                      renamePIDNVal from to (renameNonVal ρ e)) /\
  (forall e ρ from to, renameVal ρ (renamePIDVal from to e) =
                      renamePIDVal from to (renameVal ρ e)).
Proof.
  eapply Exp_ind with
    (QV := fun l => Forall (fun e => forall ρ from to, renameVal ρ (renamePIDVal from to e) =
                      renamePIDVal from to (renameVal ρ e)) l)
    (Q := fun l => Forall (fun e => forall ρ from to, rename ρ (renamePID from to e) =
                      renamePID from to (rename ρ e)) l)
    (RV := fun l => Forall (fun '(e1, e2) => forall ρ from to, renameVal ρ (renamePIDVal from to e1) =
                      renamePIDVal from to (renameVal ρ e1) /\
         renameVal ρ (renamePIDVal from to e2) =
                      renamePIDVal from to (renameVal ρ e2)) l)
    (R := fun l => Forall (fun '(e1, e2) => forall from to ρ, rename ρ (renamePID from to e1) =
                      renamePID from to (rename ρ e1) /\
         rename ρ (renamePID from to e2) =
                      renamePID from to (rename ρ e2)) l)
    (W := fun l => Forall (fun '(p, g, e) => forall from to ρ,
       rename ρ (renamePID from to g) =
                      renamePID from to (rename ρ g) /\
       rename ρ (renamePID from to e) =
                      renamePID from to (rename ρ e)) l)
    (Z := fun l => Forall (fun '(n, e) => forall from to ρ, rename ρ (renamePID from to e) =
                      renamePID from to (rename ρ e)) l)
   (VV := fun l => Forall
      (fun '(id, vl, e) => forall from to ρ, rename ρ (renamePID from to e) =
                      renamePID from to (rename ρ e)) l)
  ; intros.
  all: cbn; auto.
  1-2: now rewrite H.
  * now break_match_goal.
  * now rewrite H, H0.
  * f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto.
  * f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto. destruct x.
    specialize (H ρ from to) as [H_1 H_2]. now rewrite H_1, H_2.
  * now destruct n.
  * f_equal.
    - do 2 rewrite map_map. apply map_ext_Forall.
      rewrite List.Forall_nth in *. intros. eapply (H _ d) in H1. destruct nth, p.
      rewrite H1. now rewrite map_length.
    - rewrite map_length. now rewrite H0.
  * now rewrite H.
  * f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto.
  * now rewrite H, H0.
  * f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto.
  * f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto. destruct x.
    specialize (H from to ρ) as [H_1 H_2]. now rewrite H_1, H_2.
  * f_equal.
    - now rewrite H.
    - now rewrite H0.
    - do 2 rewrite map_map. apply map_ext_Forall.
      induction H1; constructor; auto.
  * f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto.
  * f_equal.
    - now rewrite H.
    - do 2 rewrite map_map. apply map_ext_Forall.
      induction H0; constructor; auto.
  * f_equal.
    - now rewrite H.
    - do 2 rewrite map_map. apply map_ext_Forall.
      rewrite List.Forall_nth in *. intros. eapply (H0 _ d) in H1. destruct nth, p.
      now rewrite (proj1 (H1 _ _ _)), (proj2 (H1 _ _ _)).
  * now rewrite H, H0.
  * now rewrite H, H0.
  * f_equal.
    - do 2 rewrite map_map. apply map_ext_Forall.
      rewrite List.Forall_nth in *. intros. eapply (H0 _ d) in H1. destruct nth.
      rewrite (H1 _ _ _). now rewrite map_length.
    - rewrite H. now rewrite map_length.
  * now rewrite H, H0, H1.
Qed.

Lemma renamePID_subst_up :
  forall σ from to, up_subst (renamePID_subst from to σ) =
                    renamePID_subst from to (up_subst σ).
Proof.
  unfold renamePID_subst, up_subst. intros.
  extensionality x. destruct x; auto.
  unfold Manipulation.shift. destruct σ; auto.
  now rewrite (proj2 (proj2 rename_renamePID)).
Qed.

Corollary renamePID_upn :
  forall n σ from to, upn n (renamePID_subst from to σ) =
                      renamePID_subst from to (upn n σ).
Proof.
  induction n; intros; simpl; auto.
  now rewrite IHn, renamePID_subst_up.
Qed.

Theorem split_renamePID_subst :
     (forall e from to σ, renamePID from to e.[σ] = 
       (renamePID from to e).[renamePID_subst from to σ])
  /\ (forall e from to σ, renamePIDNVal from to e.[σ]ₑ = 
       (renamePIDNVal from to e).[renamePID_subst from to σ]ₑ)
  /\ (forall e from to σ, renamePIDVal from to e.[σ]ᵥ = 
       (renamePIDVal from to e).[renamePID_subst from to σ]ᵥ).
Proof.
  eapply Exp_ind with
    (QV := fun l => Forall (fun e => forall from to σ, renamePIDVal from to e.[σ]ᵥ = 
       (renamePIDVal from to e).[renamePID_subst from to σ]ᵥ) l)
    (Q := fun l => Forall (fun e => forall from to σ, renamePID from to e.[σ] = 
       (renamePID from to e).[renamePID_subst from to σ]) l)
    (RV := fun l => Forall (fun '(e1, e2) => forall from to σ, renamePIDVal from to e1.[σ]ᵥ = 
       (renamePIDVal from to e1).[renamePID_subst from to σ]ᵥ /\
         renamePIDVal from to e2.[σ]ᵥ = 
       (renamePIDVal from to e2).[renamePID_subst from to σ]ᵥ) l)
    (R := fun l => Forall (fun '(e1, e2) => forall from to σ, renamePID from to e1.[σ] = 
       (renamePID from to e1).[renamePID_subst from to σ] /\
         renamePID from to e2.[σ] = 
       (renamePID from to e2).[renamePID_subst from to σ]) l)
    (W := fun l => Forall (fun '(p, g, e) => forall from to σ,
       renamePID from to g.[σ] =
       (renamePID from to g).[(renamePID_subst from to σ)] /\
       renamePID from to e.[σ] = 
       (renamePID from to e).[(renamePID_subst from to σ)]) l)
    (Z := fun l => Forall (fun '(n, e) => forall from to σ, renamePID from to e.[σ] = 
       (renamePID from to e).[(renamePID_subst from to σ)]) l)
   (VV := fun l => Forall
      (fun '(id, vl, e) => forall from to σ, renamePID from to e.[σ] = 
       (renamePID from to e).[(renamePID_subst from to σ)]) l)
  ; intros.
  all: cbn; auto.
  1-2: now rewrite H.
  * now break_match_goal.
  * now rewrite H, H0.
  * f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto.
  * f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto. destruct x.
    specialize (H from to σ) as [H_1 H_2]. now rewrite H_1, H_2.
  * unfold renamePID_subst. now destruct σ.
  * unfold renamePID_subst. destruct n. now destruct σ.
  * f_equal.
    - do 2 rewrite map_map. apply map_ext_Forall.
      rewrite List.Forall_nth in *. intros. eapply (H _ d) in H1. destruct nth, p.
      rewrite H1. now rewrite map_length, renamePID_upn.
    - rewrite map_length. now rewrite H0, renamePID_upn.
  * now rewrite H, renamePID_upn.
  * f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto.
  * now rewrite H, H0.
  * f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto.
  * f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto. destruct x.
    specialize (H from to σ) as [H_1 H_2]. now rewrite H_1, H_2.
  * f_equal.
    - now rewrite H.
    - now rewrite H0.
    - do 2 rewrite map_map. apply map_ext_Forall.
      induction H1; constructor; auto.
  * f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto.
  * f_equal.
    - now rewrite H.
    - do 2 rewrite map_map. apply map_ext_Forall.
      induction H0; constructor; auto.
  * f_equal.
    - now rewrite H.
    - do 2 rewrite map_map. apply map_ext_Forall.
      rewrite List.Forall_nth in *. intros. eapply (H0 _ d) in H1. destruct nth, p.
      rewrite (proj1 (H1 _ _ _)), (proj2 (H1 _ _ _)). now rewrite renamePID_upn.
  * rewrite H, H0. now rewrite renamePID_upn.
  * now rewrite H, H0.
  * f_equal.
    - do 2 rewrite map_map. apply map_ext_Forall.
      rewrite List.Forall_nth in *. intros. eapply (H0 _ d) in H1. destruct nth.
      rewrite (H1 _ _ _). now rewrite renamePID_upn, map_length.
    - rewrite H. now rewrite map_length, renamePID_upn.
  * rewrite H, H0, H1. now repeat rewrite renamePID_upn.
Qed.

Corollary split_renamePID_subst_exp :
  (forall e from to σ, renamePID from to e.[σ] = 
    (renamePID from to e).[renamePID_subst from to σ]).
Proof.
  apply split_renamePID_subst.
Qed.

Corollary split_renamePID_subst_val :
  (forall e from to σ, renamePIDVal from to e.[σ]ᵥ = 
       (renamePIDVal from to e).[renamePID_subst from to σ]ᵥ).
Proof.
  apply split_renamePID_subst.
Qed.

Proposition renamePID_subst_id :
  forall from to, renamePID_subst from to idsubst = idsubst.
Proof.
  now intros.
Qed.

Proposition renamePID_subst_list_subst :
  forall vs from to σ,
    renamePID_subst from to (list_subst vs σ) =
    list_subst (map (renamePIDVal from to) vs) (renamePID_subst from to σ).
Proof.
  induction vs; simpl; intros; auto.
  rewrite <- IHvs. clear. unfold scons, renamePID_subst.
  extensionality x. destruct x; auto.
Qed.

Proposition rename_subst_flatten_list :
  forall el from to, 
    map (renamePID from to) (flatten_list el) =
    flatten_list (map (fun '(x, y) => (renamePID from to x, renamePID from to y)) el).
Proof.
  induction el using list_length_ind; destruct el; intros; simpl; auto.
  destruct p. simpl. do 2 f_equal. rewrite H. reflexivity. slia.
Qed.

Proposition rename_subst_deflatten_list_val :
  forall el from to, 
    map (fun '(x, y) => (renamePIDVal from to x, renamePIDVal from to y)) (deflatten_list el) =
    deflatten_list (map (renamePIDVal from to) el).
Proof.
  induction el using list_length_ind; destruct el; intros; simpl; auto.
  destruct el; auto. simpl.
  do 2 f_equal. rewrite H. reflexivity. slia.
Qed.

Proposition renamePID_match_pattern :
  forall p v vs', match_pattern p v = Some vs' ->
    forall from to,
      match_pattern p (renamePIDVal from to v) = Some (map (renamePIDVal from to) vs').
Proof.
  induction p using Pat_ind2
    with (Q := fun l => Forall (fun p => forall v vs', match_pattern p v = Some vs' ->
    forall from to,
      match_pattern p (renamePIDVal from to v) = Some (map (renamePIDVal from to) vs')) l)
      (R := fun l => Forall (PBoth (fun p => forall v vs', match_pattern p v = Some vs' ->
    forall from to,
      match_pattern p (renamePIDVal from to v) = Some (map (renamePIDVal from to) vs'))) l); try destruct v; simpl; intros; try inv H; simpl; auto.
  * break_match_hyp; inv H1; now simpl.
  * repeat break_match_hyp; try congruence. inv H1.
    eapply IHp1 in Heqo. eapply IHp2 in Heqo0. now rewrite Heqo, Heqo0, map_app.
  * generalize dependent vs'. revert l0. induction IHp; intros.
    - destruct l0; now inv H1.
    - destruct l0; inv H1. simpl. break_match_hyp. 2: congruence.
      eapply H in Heqo. rewrite Heqo. break_match_hyp. 2: congruence.
      apply IHIHp in Heqo0. rewrite Heqo0. inv H2. now rewrite map_app.
  * generalize dependent vs'. revert l0. induction IHp; intros.
    - destruct l0; now inv H1.
    - destruct x; cbn in *. destruct l0; inv H1. destruct p1.
      break_match_hyp. 2: congruence.
      break_match_hyp. 2: congruence.
      break_match_hyp. 2: congruence.
      inv H2. simpl.
      destruct H as [H_1 H_2].
      eapply H_1 in Heqo. rewrite Heqo.
      eapply H_2 in Heqo0. rewrite Heqo0.
      apply IHIHp in Heqo1. rewrite Heqo1. now rewrite map_app, map_app.
Qed.

Proposition renamePID_nomatch_pattern :
  forall p v, match_pattern p v = None ->
    forall from to,
      match_pattern p (renamePIDVal from to v) = None.
Proof.
  induction p using Pat_ind2
    with (Q := fun l => Forall (fun p => forall v, match_pattern p v = None ->
    forall from to,
      match_pattern p (renamePIDVal from to v) = None) l)
      (R := fun l => Forall (PBoth (fun p => forall v, match_pattern p v = None ->
    forall from to,
      match_pattern p (renamePIDVal from to v) = None)) l); try destruct v; simpl; intros; try now (inv H; simpl; auto).
  all: try now break_match_goal; auto; break_match_hyp; congruence.
  * repeat break_match_hyp; try congruence; inv H.
    - eapply renamePID_match_pattern in Heqo. eapply IHp2 in Heqo0.
      now rewrite Heqo, Heqo0.
    - eapply IHp1 in Heqo. now rewrite Heqo.
  * generalize dependent l0. induction IHp; intros.
    - destruct l0; now inv H.
    - destruct l0; inv H0. now simpl.
      simpl. break_match_hyp.
      + eapply renamePID_match_pattern in Heqo. rewrite Heqo. break_match_hyp. congruence.
        apply IHIHp in Heqo0. now rewrite Heqo0.
      + eapply H in Heqo. now rewrite Heqo.
  * generalize dependent l0. induction IHp; intros.
    - destruct l0; now inv H.
    - destruct x; cbn in *. destruct l0; inv H0. now simpl. destruct H as [H_1 H_2].
      destruct p1. simpl in *.
      break_match_hyp. break_match_hyp. break_match_hyp. congruence.
      + eapply renamePID_match_pattern in Heqo. rewrite Heqo.
        eapply renamePID_match_pattern in Heqo0. rewrite Heqo0.
        apply IHIHp in Heqo1. now rewrite Heqo1.
      + eapply renamePID_match_pattern in Heqo. rewrite Heqo.
        eapply H_2 in Heqo0. now rewrite Heqo0.
      + eapply H_1 in Heqo. now rewrite Heqo.
  * constructor; auto.
  * constructor; auto.
  * constructor; auto.
  * constructor; auto.
Qed.

Corollary renamePID_match_pattern_list :
  forall lp vs vs', match_pattern_list lp vs = Some vs' ->
    forall from to,
      match_pattern_list lp (map (renamePIDVal from to) vs) = Some (map (renamePIDVal from to) vs').
Proof.
  induction lp; destruct vs; simpl; intros; try congruence.
  * now inv H.
  * break_match_hyp. 2: congruence. break_match_hyp. 2: congruence.
    eapply renamePID_match_pattern in Heqo. rewrite Heqo. inv H.
    eapply IHlp in Heqo0. rewrite Heqo0. now rewrite map_app.
Qed.

Corollary renamePID_nomatch_pattern_list :
  forall lp vs, match_pattern_list lp vs = None ->
    forall from to,
      match_pattern_list lp (map (renamePIDVal from to) vs) = None.
Proof.
  induction lp; destruct vs; simpl; intros; try congruence.
  break_match_hyp. break_match_hyp. congruence.
  * eapply IHlp in Heqo0. eapply renamePID_match_pattern in Heqo.
    now rewrite Heqo, Heqo0.
  * eapply renamePID_nomatch_pattern in Heqo. now rewrite Heqo.
Qed.

Proposition renamePID_Val_eqb :
  forall v (* v' *) from to, (* v =ᵥ v' = renamePIDVal from to v =ᵥ renamePIDVal from to v' *)
    v =ᵥ renamePIDVal from to v = true.
Proof.
  valinduction; (* try destruct v'; *) intros; simpl; auto.
  2: try now destruct Nat.eqb eqn:P.
  * apply Lit_eqb_refl.
  * erewrite IHv1, IHv2. reflexivity.
  * induction IHv; simpl; auto.
    now erewrite IHIHv, H.
  * induction IHv; simpl; try reflexivity. destruct x; auto.
    destruct H. simpl in *. now erewrite IHIHv, H, H0.
  * apply Nat.eqb_refl.
  * destruct n. simpl. now do 2 rewrite Nat.eqb_refl.
  * apply Nat.eqb_refl.
Qed.

Proposition renamePID_Val_eqb_alt :
  forall v v' from to, v =ᵥ v' = renamePIDVal from to v =ᵥ renamePIDVal from to v'.
Proof.
  valinduction; try destruct v'; intros; simpl; auto.
  all: try now destruct Nat.eqb eqn:P.
  * repeat break_match_goal; auto.
  * erewrite IHv1, IHv2. reflexivity.
  * revert l0. induction IHv; destruct l0; simpl; auto.
    now erewrite IHIHv, H.
  * revert l0. induction IHv; destruct l0; simpl; auto.
    - destruct x; auto.
    - destruct x; simpl. destruct H, p. simpl in *. now erewrite IHIHv, H, H0.
Qed.

Proposition renamePID_Val_ltb :
  forall v v' from to, v <ᵥ v' = renamePIDVal from to v <ᵥ renamePIDVal from to v'.
Proof.
  valinduction; try destruct v'; intros; simpl; auto.
  all: try now destruct Nat.eqb eqn:P.
  * repeat break_match_goal; auto.
  * erewrite IHv1, IHv2.
    break_match_goal; erewrite renamePID_Val_eqb_alt in Heqb; now rewrite Heqb.
  * revert l0. induction IHv; destruct l0; simpl; auto.
    break_match_goal; erewrite renamePID_Val_eqb_alt in Heqb; rewrite Heqb; specialize (IHIHv l0).
    all: repeat rewrite map_length in *.
    - rewrite Bool.orb_lazy_alt, Bool.andb_lazy_alt in IHIHv.
      repeat break_match_hyp; auto.
      + apply Nat.ltb_lt, Arith_prebase.lt_n_S_stt, Nat.ltb_lt in Heqb0.
        rewrite Heqb0. auto.
      + apply Nat.ltb_nlt in Heqb0.
        assert (~S (length l) < S (length l0)) by lia.
        apply Nat.ltb_nlt in H0. rewrite H0. simpl. now rewrite IHIHv.
    - rewrite Bool.orb_lazy_alt, Bool.andb_lazy_alt in IHIHv.
      repeat break_match_hyp; auto.
      + apply Nat.ltb_lt, Arith_prebase.lt_n_S_stt, Nat.ltb_lt in Heqb0.
        rewrite Heqb0. auto.
      + apply Nat.ltb_nlt in Heqb0.
        assert (~S (length l) < S (length l0)) by lia.
        apply Nat.ltb_nlt in H0. rewrite H0. simpl.
        apply H.
  * revert l0. induction IHv; destruct l0; simpl; auto.
    destruct x, p, H.
    break_match_goal; erewrite renamePID_Val_eqb_alt in Heqb; rewrite Heqb; specialize (IHIHv l0); simpl in *.
    all: repeat rewrite map_length in *.
    - rewrite Bool.orb_lazy_alt, Bool.andb_lazy_alt in IHIHv.
      repeat break_match_hyp; auto.
      + apply Nat.ltb_lt, Arith_prebase.lt_n_S_stt, Nat.ltb_lt in Heqb0.
        rewrite Heqb0. auto.
      + apply Nat.ltb_nlt in Heqb0.
        assert (~S (length l) < S (length l0)) by lia.
        apply Nat.ltb_nlt in H1. rewrite H1. simpl.
        rewrite Bool.orb_lazy_alt, Bool.andb_lazy_alt in IHIHv.
        break_match_hyp; simpl in *.
        ** rewrite Bool.orb_lazy_alt. admit. (* TODO: Technical - use induction later! *)
        ** admit.
    - rewrite Bool.orb_lazy_alt, Bool.andb_lazy_alt in IHIHv.
      repeat break_match_hyp; auto.
      + apply Nat.ltb_lt, Arith_prebase.lt_n_S_stt, Nat.ltb_lt in Heqb0.
        rewrite Heqb0. auto.
      + apply Nat.ltb_nlt in Heqb0.
        assert (~S (length l) < S (length l0)) by lia.
        apply Nat.ltb_nlt in H1. rewrite H1. simpl.
        erewrite H, H0. admit. (* TODO Technical *)
Admitted.

Lemma renamePID_make_val_map :
  forall vs from to,
  map (fun '(x, y) => (renamePIDVal from to x, renamePIDVal from to y))
         (make_val_map vs) =
  make_val_map (map (fun '(x, y) => (renamePIDVal from to x, renamePIDVal from to y))
         vs).
Proof.
  induction vs; intros; simpl; auto.
  destruct a. specialize (IHvs from to).
  rewrite <- IHvs. clear IHvs.
  (* map_insert *)
  remember (make_val_map vs) as vl. clear Heqvl vs.
  revert v v0 from to.
  induction vl; intros; simpl; auto.
  destruct a. erewrite (renamePID_Val_eqb_alt _ _ from to), (renamePID_Val_ltb _ _ from to).
  repeat break_match_goal; simpl; eauto.
  now rewrite IHvl.
Qed.

Ltac destruct_eqb_in_if EQ :=
  match goal with
  | [|- context G [if ?from =? ?p then _ else _]] => destruct (from =? p) eqn:EQ
  end.

Lemma renamePID_eval_arith :
  forall m f vs r,
    eval_arith m f vs = r ->
    forall from to,
      eval_arith m f (map (renamePIDVal from to) vs) = renamePIDRed from to r.
Proof.
  intros. unfold eval_arith in *. break_match_goal; inv H.
  all: destruct vs; simpl; try reflexivity.
  all: destruct v; simpl; try reflexivity.
  all: try destruct l; simpl; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  all: try now (destruct vs; simpl; try reflexivity).
  all: try destruct v; simpl; try reflexivity.
  all: try destruct_eqb_in_if EQ; try reflexivity.
  all: try destruct l; simpl; try rewrite EQ; try reflexivity.
  all: try destruct vs; simpl; try rewrite EQ; try reflexivity.
  all: try destruct (Nat.eqb from p) eqn:EQ2; try reflexivity.
  all: destruct x0; try reflexivity.
Qed.

Lemma renamePID_eval_logical :
  forall m f vs r,
    eval_logical m f vs = r ->
    forall from to,
      eval_logical m f (map (renamePIDVal from to) vs) = renamePIDRed from to r.
Proof.
  intros. unfold eval_logical in *. break_match_goal; inv H; try reflexivity; clear Heqb.
  all: destruct vs; simpl; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  all: try destruct vs; simpl; try reflexivity.
  all: repeat break_match_hyp.
  all: erewrite renamePID_Val_eqb_alt in Heqb;
       try erewrite renamePID_Val_eqb_alt in Heqb0;
       try erewrite renamePID_Val_eqb_alt in Heqb1.
  all: simpl in *; try rewrite Heqb;
                   try rewrite Heqb0;
                   try rewrite Heqb1;
                   try reflexivity.
  all: erewrite renamePID_Val_eqb_alt in Heqb2; rewrite Heqb2; try reflexivity.
Qed.

Lemma renamePID_eval_equality :
  forall m f vs r,
    eval_equality m f vs = r ->
    forall from to,
      eval_equality m f (map (renamePIDVal from to) vs) = renamePIDRed from to r.
Proof.
  intros. unfold eval_equality in *. break_match_goal; inv H; try reflexivity; clear Heqb.
  all: destruct vs; simpl; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  all: destruct Val_eqb eqn:P; erewrite renamePID_Val_eqb_alt in P; rewrite P.
  all: reflexivity.
Qed.

Lemma renamePID_eval_cmp :
  forall m f vs r,
    eval_cmp m f vs = r ->
    forall from to,
      eval_cmp m f (map (renamePIDVal from to) vs) = renamePIDRed from to r.
Proof.
  intros. unfold eval_cmp in *. break_match_goal; inv H; try reflexivity; clear Heqb.
  all: destruct vs; simpl; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  all: destruct Val_ltb eqn:P; erewrite renamePID_Val_ltb in P; rewrite P.
  all: try reflexivity.
  all: simpl in *.
  all: destruct Val_eqb eqn:P0; erewrite renamePID_Val_eqb_alt in P0; rewrite P0.
  all: try reflexivity.
Qed.

Lemma renamePID_eval_hd_tl :
  forall m f vs r,
    eval_hd_tl m f vs = r ->
    forall from to,
      eval_hd_tl m f (map (renamePIDVal from to) vs) = renamePIDRed from to r.
Proof.
  intros. unfold eval_hd_tl in *. break_match_goal; inv H; try reflexivity; clear Heqb.
  all: destruct vs; simpl; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  all: destruct v; try reflexivity; simpl; destruct Nat.eqb; try reflexivity.
Qed.

Lemma renamePID_eval_check :
  forall m f vs r,
    eval_check m f vs = r ->
    forall from to,
      eval_check m f (map (renamePIDVal from to) vs) = renamePIDRed from to r.
Proof.
  intros. unfold eval_check in *. break_match_goal; inv H; try reflexivity; clear Heqb.
  all: destruct vs; simpl; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  all: destruct v; try reflexivity.
  all: simpl in *; try destruct l; try reflexivity.
  all: try destruct (Nat.eqb from p); try reflexivity.
  destruct Lit_beq; simpl in *. reflexivity.
  destruct string_dec; reflexivity.
Qed.

Lemma renamePID_eval_funinfo :
  forall vs r,
    eval_funinfo vs = r ->
    forall from to,
      eval_funinfo (map (renamePIDVal from to) vs) = renamePIDRed from to r.
Proof.
  intros. unfold eval_funinfo in *.
  all: destruct vs; simpl; try reflexivity.
  * now inv H.
  * destruct v; cbn.
    all: destruct vs; simpl.
    all: try destruct vs; simpl.
    all: try now inversion H.
    all: try destruct (Nat.eqb from p) eqn:P; try now inversion H.
    inv H; cbn; destruct Nat.eqb; cbn; try reflexivity; try congruence.
    inv H; cbn; destruct Nat.eqb; cbn; try reflexivity; try congruence.
    break_match_hyp; erewrite renamePID_Val_eqb_alt in Heqb; rewrite Heqb.
    now inv H.
    now inv H.
Qed.

Lemma renamePID_eval_transform_list :
  forall m f vs r,
    eval_transform_list m f vs = r ->
    forall from to,
      eval_transform_list m f (map (renamePIDVal from to) vs) = renamePIDRed from to r.
Proof.
  intros. unfold eval_transform_list in *. break_match_goal; inv H; try reflexivity; clear Heqb.
  all: destruct vs; simpl; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  {
    clear H0.
    generalize dependent v0. induction v; simpl; intros; auto.
    all: try destruct_eqb_in_if Heq; try reflexivity.
    rewrite IHv2. destruct eval_append; simpl; try reflexivity.
    * destruct vs; simpl; try reflexivity.
      destruct vs; try reflexivity.
    * destruct e, p. reflexivity.
  }
  {
    admit. (* TODO: Technical *)
  }
Admitted.

Lemma renamePID_eval_elem_tuple :
  forall m f vs r,
    eval_elem_tuple m f vs = r ->
    forall from to,
      eval_elem_tuple m f (map (renamePIDVal from to) vs) = renamePIDRed from to r.
Proof.
  intros. unfold eval_elem_tuple in *.
  break_match_goal; inv H; try reflexivity; clear Heqb.
  all: destruct vs; simpl; try reflexivity.
  all: destruct v; simpl; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  all: try destruct vs; simpl; try reflexivity.
  all: try destruct_eqb_in_if Heq; try reflexivity.
  all: try destruct vs; simpl; try reflexivity.
  9-10: now rewrite Heq.
  all: try destruct l; simpl; try reflexivity.
  all: try destruct v; simpl; try reflexivity.
  all: try destruct_eqb_in_if Heq; try reflexivity.
  all: destruct x; try reflexivity.
  all: remember (Nat.pred (Pos.to_nat p)) as n; clear Heqn; clear H0.
  * rewrite nth_error_map. destruct nth_error; simpl; try reflexivity.
  * rewrite replace_nth_error_map. now destruct replace_nth_error.
Qed.

Lemma renamePID_eval_list_tuple :
  forall m f vs r,
    eval_list_tuple m f vs = r ->
    forall from to,
      eval_list_tuple m f (map (renamePIDVal from to) vs) = renamePIDRed from to r.
Proof.
  intros. unfold eval_list_tuple in *.
  break_match_goal; inv H; try reflexivity; clear Heqb.
  all: destruct vs; simpl; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  * clear H0. destruct v; simpl; try reflexivity.
    break_match_goal; reflexivity.
    induction l; simpl; auto.
    inv IHl. now rewrite H0.
  * clear H0. induction v; simpl; try reflexivity.
    destruct Nat.eqb; reflexivity.
    Opaque transform_list.
    destruct v2; try reflexivity; simpl.
    1: destruct Nat.eqb; simpl; reflexivity.
    clear IHv1. simpl in IHv2.
    break_match_hyp; break_match_hyp; inv IHv2; try reflexivity.
    destruct e, p. congruence.
    destruct e0, p; inv H0. reflexivity.
    Transparent transform_list.
Qed.

Lemma renamePID_eval_length :
  forall vs r,
    eval_length vs = r ->
    forall from to,
      eval_length (map (renamePIDVal from to) vs) = renamePIDRed from to r.
Proof.
  intros. unfold eval_length in *.
  rewrite <- H. clear H.
  all: destruct vs; simpl; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  induction v; simpl; try reflexivity.
  1: destruct Nat.eqb; reflexivity.
  clear IHv1. destruct (_ v2.⟦from ↦ to⟧ᵥ) eqn:P.
  break_match_hyp. all: inv IHv2.
  * now destruct z0.
  * break_match_hyp; inv H0. reflexivity.
Qed.

Lemma renamePID_eval_tuple_size :
  forall vs r,
    eval_tuple_size vs = r ->
    forall from to,
      eval_tuple_size (map (renamePIDVal from to) vs) = renamePIDRed from to r.
Proof.
  intros. unfold eval_tuple_size in *.
  rewrite <- H. clear H.
  all: destruct vs; simpl; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  all: destruct v; try reflexivity.
  all: simpl.
  2: now rewrite map_length.
  all: now destruct Nat.eqb.
Qed.

Lemma renamePID_eval_io :
  forall m f vs eff r eff',
    eval_io m f vs eff = (r, eff') ->
    forall from to,
      eval_io m f (map (renamePIDVal from to) vs) (map (fun '(a, b) => (a, map (renamePIDVal from to) b)) eff) =
        (renamePIDRed from to r, map (fun '(a, b) => (a, map (renamePIDVal from to) b)) eff').
Proof.
  intros. unfold eval_io in *. break_match_goal; inv H; clear Heqb; try reflexivity.
  all: rewrite map_length.
  all: destruct vs; simpl; try reflexivity.
  all: try destruct vs; simpl; try reflexivity.
  all: try destruct vs; simpl; try reflexivity.
  all: simpl in H1; inv H1; try reflexivity.
  all: simpl; rewrite map_app; reflexivity.
Qed.

Lemma renamePID_eval_concurrent :
  forall m f vs class reas det,
    eval_concurrent m f vs = Some (class, reas, det) ->
    forall from to,
      eval_concurrent m f (map (renamePIDVal from to) vs) = Some (class, renamePIDVal from to reas, renamePIDVal from to det).
Proof.
  intros. unfold eval_concurrent in *. break_match_goal; inv H; clear Heqb; try reflexivity.
  all: destruct vs; inv H1; simpl; try reflexivity.
  all: destruct vs; inv H0; simpl; try reflexivity.
Qed.


Lemma renamePID_eval_error :
  forall m f vs class reas det,
    eval_error m f vs = Some (class, reas, det) ->
    forall from to,
      eval_error m f (map (renamePIDVal from to) vs) = Some (class, renamePIDVal from to reas, renamePIDVal from to det).
Proof.
  intros. unfold eval_error in *. break_match_goal; inv H; clear Heqb; try reflexivity.
  all: destruct vs; inv H1; simpl; try reflexivity.
  all: destruct vs; inv H0; simpl; try reflexivity.
  all: destruct vs; inv H1; simpl; try reflexivity.
  all: destruct vs; inv H0; simpl; try reflexivity.
Qed.

Proposition renamePID_eval :
  forall m f vs eff r eff',
    eval m f vs eff = Some (r, eff') ->
    forall from to,
      eval m f (map (renamePIDVal from to) vs) (map (fun '(a, b) => (a, map (renamePIDVal from to) b)) eff) =
        Some (renamePIDRed from to r, map (fun '(a, b) => (a, map (renamePIDVal from to) b)) eff').
Proof.
  intros. unfold eval in *.
  break_match_hyp; try rewrite Heqb in *; inv H.
  all:
    try (erewrite renamePID_eval_arith; reflexivity);
    try (erewrite renamePID_eval_logical; reflexivity);
    try (erewrite renamePID_eval_equality; reflexivity);
    try (erewrite renamePID_eval_cmp; reflexivity);
    try (erewrite renamePID_eval_hd_tl; reflexivity);
    try (erewrite renamePID_eval_funinfo; reflexivity);
    try (erewrite renamePID_eval_length; reflexivity);
    try (erewrite renamePID_eval_elem_tuple; reflexivity);
    try (erewrite renamePID_eval_transform_list; reflexivity);
    try (erewrite renamePID_eval_list_tuple; reflexivity);
    try (erewrite renamePID_eval_tuple_size; reflexivity);
    try (erewrite renamePID_eval_check; reflexivity).
  1-2: erewrite renamePID_eval_io; try eassumption; reflexivity.
  1-3: break_match_hyp; try congruence; destruct e, p;
       eapply renamePID_eval_error in Heqo; rewrite Heqo; inv H1; reflexivity.
  1-6: break_match_hyp; try congruence; destruct e, p;
       eapply renamePID_eval_concurrent in Heqo; rewrite Heqo; inv H1; reflexivity.
  reflexivity.
Qed.

Proposition renamePID_primop_eval :
  forall f vs eff r eff',
    primop_eval f vs eff = Some (r, eff') ->
    forall from to,
      primop_eval f (map (renamePIDVal from to) vs) (map (fun '(a, b) => (a, map (renamePIDVal from to) b)) eff) = Some (renamePIDRed from to r, map (fun '(a, b) => (a, map (renamePIDVal from to) b)) eff').
Proof.
  intros. destruct (convert_primop_to_code f) eqn:EQ;
  unfold primop_eval in *; rewrite EQ in *.
  all: try now inv H.
  all: unfold eval_primop_error in *; rewrite EQ in *; destruct vs; cbn in *.
  all: try congruence.
  all: destruct vs; cbn in *; try congruence.
  1: now inv H.
  all: destruct vs; cbn in *; try congruence.
  1: now inv H.
Qed.

Corollary renamePID_create_result :
  forall vs ident eff r eff',
    create_result ident vs eff = Some (r, eff') ->
    forall from to, create_result (renamePIDFrameId from to ident)
                                  (map (renamePIDVal from to) vs) (map (fun '(a, b) => (a, map (renamePIDVal from to) b)) eff) =
                                  Some (renamePIDRed from to r, map (fun '(a, b) => (a, map (renamePIDVal from to) b)) eff').
Proof.
  intros. destruct ident; simpl in *.
  * now inv H.
  * now inv H.
  * inv H. cbn.
    now rewrite <- rename_subst_deflatten_list_val, renamePID_make_val_map.
  * destruct m, f; simpl in *; inv H; auto.
    all: try destruct l; try destruct l0; try inv H1; auto.
    2-14: destruct (from =? p) eqn:P; cbn; now try rewrite P.
    eapply renamePID_eval in H0. simpl in H0. exact H0.
  * eapply renamePID_primop_eval in H. exact H.
  * rewrite map_length.
    destruct v; simpl. all: try now inv H.
    - destruct Nat.eqb eqn:P; inv H; cbn; now rewrite P.
    - break_match_hyp; try now inv H.
      inv H. simpl. rewrite split_renamePID_subst_exp, renamePID_subst_list_subst.
      unfold convert_to_closlist. repeat f_equal.
      rewrite map_map, map_app. f_equal. rewrite map_map.
      f_equal. extensionality x. destruct x, p. cbn. f_equal.
Qed.

Theorem renamePID_is_preserved :
  forall fs r fs' r', ⟨fs, r⟩ --> ⟨fs', r'⟩ ->
    forall from to,
      ⟨renamePIDStack from to fs, renamePIDRed from to r⟩ -->
      ⟨renamePIDStack from to fs', renamePIDRed from to r'⟩.
Proof.
  intros. inv H; cbn; try now constructor.
  * constructor. now apply renamePID_preserves_scope.
  * rewrite map_app. constructor.
  * constructor. destruct ident; cbn; congruence.
  * econstructor.
    - destruct ident; cbn; congruence.
    - eapply eq_sym, renamePID_create_result in H1. symmetry. eassumption.
  * econstructor.
    - replace (map (renamePIDVal from to) vl ++ [renamePIDVal from to v]) with
              (map (renamePIDVal from to) (vl ++ [v])) by now rewrite map_app.
      eapply eq_sym, renamePID_create_result in H0. symmetry. eassumption.
  * rewrite rename_subst_flatten_list. constructor.
  * rewrite split_renamePID_subst_exp,
            renamePID_subst_list_subst,
            renamePID_subst_id.
    constructor. now rewrite map_length.
  * repeat rewrite split_renamePID_subst_exp,
                   renamePID_subst_list_subst,
                   renamePID_subst_id.
    constructor. now apply renamePID_match_pattern_list.
  * econstructor. now apply renamePID_nomatch_pattern_list.
  * rewrite split_renamePID_subst_exp,
            renamePID_subst_list_subst,
            renamePID_subst_id.
    constructor.
    unfold convert_to_closlist. repeat rewrite map_map. f_equal.
    extensionality x. destruct x. simpl. rewrite map_map. do 2 f_equal.
    extensionality x. now destruct x.
  * rewrite split_renamePID_subst_exp,
            renamePID_subst_list_subst,
            renamePID_subst_id.
    constructor. now rewrite map_length.
  * rewrite split_renamePID_subst_exp.
    pose proof (renamePID_subst_list_subst [exclass_to_value class; reason; details]).
    simpl in H. rewrite H.
    destruct class; cbn; constructor.
  * destruct exc, p. constructor.
    destruct F; auto.
Qed.

(* (* NOTE: instead of fold_right, Exists would be better, but Coq cannot guess the
   decreasing argument that way.
   Prop is not as usable in fold_right, as bool, thus we use bool instead *)
Fixpoint isUsedPIDExp (from : PID) (e : Exp) : bool :=
match e with
 | VVal e => isUsedPIDVal from e
 | EExp e => isUsedPIDNVal from e
end
with isUsedPIDVal (from : PID) (v : Val) : bool :=
match v with
 | VNil => false
 | VLit l => false
 | VPid p => from =? p
 | VCons hd tl => isUsedPIDVal from hd || isUsedPIDVal from tl
 | VTuple l => fold_right (fun x acc => (isUsedPIDVal from x || acc)%bool) false l
 | VMap l => fold_right (fun x acc => (isUsedPIDVal from x.1 || isUsedPIDVal from x.2 || acc)%bool) false l
 | VVar n => false
 | VFunId n => false
 | VClos ext id params e => fold_right (fun x acc => (isUsedPIDExp from x.2 || acc)%bool) false ext || isUsedPIDExp from e
end
with isUsedPIDNVal (from : PID) (n : NonVal) : bool :=
match n with
 | EFun vl e => isUsedPIDExp from e
 | EValues el => fold_right (fun x acc => (isUsedPIDExp from x || acc)%bool) false el
 | ECons hd tl => isUsedPIDExp from hd || isUsedPIDExp from tl
 | ETuple l => fold_right (fun x acc => (isUsedPIDExp from x || acc)%bool) false l
 | EMap l => fold_right (fun x acc => (isUsedPIDExp from x.1 || isUsedPIDExp from x.2 || acc)%bool) false l
 | ECall m f l => isUsedPIDExp from m || isUsedPIDExp from f || fold_right (fun x acc => (isUsedPIDExp from x || acc)%bool) false l
 | EPrimOp f l => fold_right (fun x acc => (isUsedPIDExp from x || acc)%bool) false l
 | EApp exp l => (isUsedPIDExp from exp) || fold_right (fun x acc => (isUsedPIDExp from x || acc)%bool) false l
 | ECase e l => (isUsedPIDExp from e) || fold_right (fun x acc => (isUsedPIDExp from x.1.2 || isUsedPIDExp from x.2 || acc)%bool) false l
 | ELet l e1 e2 => isUsedPIDExp from e1 || isUsedPIDExp from e2
 | ESeq e1 e2 => isUsedPIDExp from e1 || isUsedPIDExp from e2
 | ELetRec l e => (isUsedPIDExp from e) || fold_right (fun e acc => (isUsedPIDExp from e.2 || acc)%bool) false l
 | ETry e1 vl1 e2 vl2 e3 => isUsedPIDExp from e1 || isUsedPIDExp from e2 || isUsedPIDExp from e3
end.

Definition isUsedPIDRed (from : PID) (r : Redex) : bool :=
match r with
 | RExp e => isUsedPIDExp from e
 | RValSeq vs => fold_right (fun x acc => (isUsedPIDVal from x || acc)%bool) false vs
 | RExc (class, reas, det) => isUsedPIDVal from reas || isUsedPIDVal from det
 | RBox => false
end.


Definition isUsedPIDFrameId (from : PID) (f : FrameIdent) : bool :=
match f with
 | ICall m f => isUsedPIDVal from m || isUsedPIDVal from f
 | IApp v => isUsedPIDVal from v
 | _ => false
end.

Definition isUsedPIDFrame (from : PID) (f : Frame) : bool :=
match f with
 | FCons1 hd => isUsedPIDExp from hd
 | FCons2 tl => isUsedPIDVal from tl
 | FParams ident vl el =>
     (isUsedPIDFrameId from ident) ||
     fold_right (fun x acc => (isUsedPIDExp from x || acc)%bool) false el ||
     fold_right (fun x acc => (isUsedPIDVal from x || acc)%bool) false vl
 | FApp1 l => fold_right (fun x acc => (isUsedPIDExp from x || acc)%bool) false l
 | FCallMod f l => (isUsedPIDExp from f) || fold_right (fun x acc => (isUsedPIDExp from x || acc)%bool) false l
 | FCallFun m l => (isUsedPIDVal from m) || fold_right (fun x acc => (isUsedPIDExp from x || acc)%bool) false l
 | FCase1 l => fold_right (fun x acc => (isUsedPIDExp from x.1.2 || isUsedPIDExp from x.2 || acc)%bool) false l
 | FCase2 lv ex le =>
   (isUsedPIDExp from ex) ||
   fold_right (fun x acc => (isUsedPIDVal from x || acc)%bool) false lv ||
   fold_right (fun x acc => (isUsedPIDExp from x.1.2 || isUsedPIDExp from x.2 || acc)%bool) false le
 | FLet l e => isUsedPIDExp from e
 | FSeq e => isUsedPIDExp from e
 | FTry vl1 e2 vl2 e3 => isUsedPIDExp from e2 || isUsedPIDExp from e3
end.

Definition isUsedPIDStack (from : PID) (fs : FrameStack) : bool :=
  fold_right (fun x acc => (isUsedPIDFrame from x || acc)%bool) false fs. *)

Definition flat_union {A B} {H : EqDecision B} {H0 : Countable B}
  (f : A -> gset B) (l : list A) : gset B :=
    foldr (fun x acc => f x ∪ acc) ∅ l.

Fixpoint usedPIDsExp (e : Exp) : gset PID :=
match e with
 | VVal e => usedPIDsVal e
 | EExp e => usedPIDsNVal e
end
with usedPIDsVal (v : Val) : gset PID :=
match v with
 | VNil => ∅
 | VLit l => ∅
 | VPid p => {[p]}
 | VCons hd tl => usedPIDsVal hd ∪ usedPIDsVal tl
 | VTuple l => flat_union usedPIDsVal l
 | VMap l => flat_union (fun x => usedPIDsVal x.1 ∪ usedPIDsVal x.2) l
 | VVar n => ∅
 | VFunId n => ∅
 | VClos ext id params e => usedPIDsExp e ∪ flat_union (fun x => usedPIDsExp x.2) ext
end

with usedPIDsNVal (n : NonVal) : gset PID :=
match n with
 | EFun vl e => usedPIDsExp e
 | EValues el => flat_union usedPIDsExp el
 | ECons hd tl => usedPIDsExp hd ∪ usedPIDsExp tl
 | ETuple l => flat_union usedPIDsExp l
 | EMap l => flat_union (fun x => usedPIDsExp x.1 ∪ usedPIDsExp x.2) l
 | ECall m f l => usedPIDsExp m ∪ usedPIDsExp f ∪ flat_union usedPIDsExp l
 | EPrimOp f l => flat_union usedPIDsExp l
 | EApp exp l => usedPIDsExp exp ∪ flat_union usedPIDsExp l
 | ECase e l => usedPIDsExp e ∪ flat_union (fun x => usedPIDsExp x.1.2 ∪ usedPIDsExp x.2) l
 | ELet l e1 e2 => usedPIDsExp e1 ∪ usedPIDsExp e2
 | ESeq e1 e2 => usedPIDsExp e1 ∪ usedPIDsExp e2
 | ELetRec l e => usedPIDsExp e ∪ flat_union (fun x => usedPIDsExp x.2) l
 | ETry e1 vl1 e2 vl2 e3 => usedPIDsExp e1 ∪ usedPIDsExp e2 ∪ usedPIDsExp e3
end.

Definition usedPIDsRed (r : Redex) : gset PID :=
match r with
 | RExp e => usedPIDsExp e
 | RValSeq vs => flat_union usedPIDsVal vs
 | RExc e => usedPIDsVal e.1.2 ∪ usedPIDsVal e.2
 | RBox => ∅
end.

Definition usedPIDsFrameId (i : FrameIdent) : gset PID :=
match i with
 | IValues => ∅
 | ITuple => ∅
 | IMap => ∅
 | ICall m f => usedPIDsVal m ∪ usedPIDsVal f
 | IPrimOp f => ∅
 | IApp v => usedPIDsVal v
end.

Definition usedPIDsFrame (f : Frame) : gset PID :=
match f with
 | FCons1 hd => usedPIDsExp hd
 | FCons2 tl => usedPIDsVal tl
 | FParams ident vl el => usedPIDsFrameId ident ∪
                          flat_union usedPIDsVal vl ∪
                          flat_union usedPIDsExp el
 | FApp1 l => flat_union usedPIDsExp l
 | FCallMod f l => usedPIDsExp f ∪ flat_union usedPIDsExp l
 | FCallFun m l => usedPIDsVal m ∪ flat_union usedPIDsExp l
 | FCase1 l => flat_union (fun x => usedPIDsExp x.1.2 ∪ usedPIDsExp x.2) l
 | FCase2 lv ex le =>
   usedPIDsExp ex ∪
   flat_union usedPIDsVal lv ∪
   flat_union (fun x => usedPIDsExp x.1.2 ∪ usedPIDsExp x.2) le
 | FLet l e => usedPIDsExp e
 | FSeq e => usedPIDsExp e
 | FTry vl1 e2 vl2 e3 => usedPIDsExp e2 ∪ usedPIDsExp e3
end.

Definition usedPIDsStack (fs : FrameStack) : gset PID :=
  flat_union usedPIDsFrame fs.

(* Basics.v *)
Lemma foldr_orb_not_Forall :
  forall {A} (f : A -> bool) l,
    Forall (fun x => f x = false) l <->
    fold_right (fun x acc => (f x || acc)%bool) false l = false.
Proof.
  induction l; intros; split; intros; auto.
  {
    simpl in *. inv H. now rewrite H2, (proj1 IHl).
  }
  {
    simpl in H. apply Bool.orb_false_iff in H as [? ?]. constructor.
    assumption.
    now apply IHl.
  }
Qed.

Ltac destruct_bool :=
  match goal with
  | [H : orb  _ _ = true  |- _] => apply Bool.orb_true_iff in H as [? | ?]
  | [H : orb  _ _ = false |- _] => apply Bool.orb_false_iff in H as [? ?]
  | [H : andb _ _ = true  |- _] => apply Bool.andb_true_iff in H as [? ?]
  | [H : andb _ _ = false |- _] => apply Bool.andb_false_iff in H as [? | ?]
  end.
Ltac destruct_bools := repeat destruct_bool.

Ltac destruct_not_in_base :=
  match goal with
  | [H : ~In _ (_ ++ _) |- _] => apply not_in_app in H as [? ?]
  end.
Ltac destruct_not_in := repeat destruct_not_in_base.

(* Basics.v *)
Lemma foldr_not_in_Forall :
  forall {A B} (f : A -> list B) (l : list A) y b,
    Forall (fun x => ~In y (f x)) l /\ ~In y b <->
    ~In y (fold_right (fun x acc => f x ++ acc) b l).
Proof.
  induction l; intros; split; intros; auto.
  {
    inv H. simpl in *. congruence.
  }
  {
    simpl in *. inv H. inv H0.
    intro. apply in_app_iff in H as [? | ?]. congruence.
    apply (IHl y b) in H; auto.
  }
  {
    simpl in H. destruct_not_in.
    apply (IHl y b) in H0. destruct H0.
    repeat constructor; auto.
  }
Qed.


Lemma flat_union_map :
  forall {A B} {H : EqDecision B} {H0 : Countable B} (f : A -> gset B) l,
    flat_union f l = union_list (map f l).
Proof.
  induction l; simpl. reflexivity.
  * by rewrite IHl.
Qed.

Lemma elem_of_flat_union :
  forall {A B} {H : EqDecision B} {H0 : Countable B} (f : A -> gset B) l,
   forall x, x ∈ flat_union f l <->
     exists y, y ∈ l /\ x ∈ f y.
Proof.
  induction l; intros; simpl in *.
  * split; set_solver.
  * split; set_solver.
Qed.

Corollary not_elem_of_flat_union :
  forall {A B} {H : EqDecision B} {H0 : Countable B} (f : A -> gset B) l,
   forall x, x ∉ flat_union f l <->
     forall y, y ∈ l -> x ∉ f y.
Proof.
  intros. split; intros; intro.
  * apply H1. apply elem_of_flat_union. set_solver.
  * apply elem_of_flat_union in H2. destruct_hyps. set_solver.
Qed.

Local Theorem isNotUsed_renamePID_ind :
  (forall e from to, from ∉ (usedPIDsExp e) -> renamePID from to e = e) /\
  (forall e from to, from ∉ (usedPIDsNVal e) -> renamePIDNVal from to e = e) /\
  (forall e from to, from ∉ (usedPIDsVal e) -> renamePIDVal from to e = e).
Proof.
  apply Exp_ind with
    (QV := fun l => Forall (fun e => forall from to, from ∉ (usedPIDsVal e) -> renamePIDVal from to e = e) l)
    (Q := fun l => Forall (fun e => forall from to, from ∉ (usedPIDsExp e) -> renamePID from to e = e) l)
    (RV := fun l => Forall (fun '(e1, e2) => forall from to,
        (from ∉ (usedPIDsVal e1) -> renamePIDVal from to e1 = e1) /\
        (from ∉ (usedPIDsVal e2) -> renamePIDVal from to e2 = e2)) l)
    (R := fun l => Forall (fun '(e1, e2) => forall from to,
        (from ∉ (usedPIDsExp e1) -> renamePID from to e1 = e1) /\
        (from ∉ (usedPIDsExp e2) -> renamePID from to e2 = e2)) l)
    (W := fun l => Forall (fun '(p, g, e) => forall from to,
       (from ∉ (usedPIDsExp g) -> renamePID from to g = g) /\
       (from ∉ (usedPIDsExp e) -> renamePID from to e = e)) l)
    (Z := fun l => Forall (fun '(n, e) => forall from to, from ∉ (usedPIDsExp e) -> renamePID from to e = e) l)
   (VV := fun l => Forall
      (fun '(id, vl, e) => forall from to, from ∉ (usedPIDsExp e) -> renamePID from to e = e) l); intros; simpl; try reflexivity.
  all: try now intuition.
  all: try now (rewrite H; try rewrite H0; auto; simpl in *; auto).
  all: simpl in *; destruct_not_in.
  * simpl in H. break_match_goal. 2: reflexivity.
    apply Nat.eqb_eq in Heqb. subst. set_solver.
  * rewrite H, H0. reflexivity. all: set_solver.
  * f_equal. rewrite <- (map_id l) at 2.
    apply map_ext_in.
    rewrite List.Forall_forall in H. intros. eapply H in H1 as P. now erewrite P.
    simpl in H0.
    rewrite not_elem_of_flat_union in H0.
    apply elem_of_list_In in H1. by apply H0 in H1.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext_in.
    rewrite List.Forall_forall in H. intros. eapply H in H1 as P. destruct a.
    simpl in H0.
    rewrite not_elem_of_flat_union in H0.
    apply elem_of_list_In in H1. apply H0 in H1.
    rewrite (proj1 (P _ _)), (proj2 (P _ _)). reflexivity.
    all: set_solver.
  * rewrite H0. 2: set_solver. f_equal.
    rewrite <- (map_id ext) at 2. apply map_ext_in. intros.
    rewrite List.Forall_forall in H. intros. eapply H in H2 as P.
    destruct a, p.
    apply not_elem_of_union in H1 as [_ ?].
    rewrite not_elem_of_flat_union in H1.
    apply elem_of_list_In in H2. apply H1 in H2.
    simpl in *. by rewrite P.
  * f_equal. rewrite <- (map_id el) at 2.
    apply map_ext_in.
    rewrite List.Forall_forall in H. intros. eapply H in H1 as P. now erewrite P.
    simpl in H0.
    rewrite not_elem_of_flat_union in H0.
    apply elem_of_list_In in H1. by apply H0 in H1.
  * rewrite H, H0. all: set_solver.
  * f_equal. rewrite <- (map_id l) at 2.
    apply map_ext_in.
    rewrite List.Forall_forall in H. intros. eapply H in H1 as P. now erewrite P.
    simpl in H0.
    rewrite not_elem_of_flat_union in H0.
    apply elem_of_list_In in H1. by apply H0 in H1.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext_in.
    rewrite List.Forall_forall in H. intros. eapply H in H1 as P. destruct a.
    simpl in H0.
    rewrite not_elem_of_flat_union in H0.
    apply elem_of_list_In in H1. apply H0 in H1.
    rewrite (proj1 (P _ _)), (proj2 (P _ _)). reflexivity.
    all: set_solver.
  * f_equal.
    - rewrite H; set_solver.
    - rewrite H0; set_solver.
    - rewrite <- (map_id l) at 2.
      apply map_ext_in.
      rewrite List.Forall_forall in H1. intros. eapply H1 in H3 as P. now erewrite P.
      simpl in H2. apply not_elem_of_union in H2 as [_ H2].
      rewrite not_elem_of_flat_union in H2.
      apply elem_of_list_In in H3. by apply H2 in H3.
  * f_equal. rewrite <- (map_id l) at 2.
    apply map_ext_in.
    rewrite List.Forall_forall in H. intros. eapply H in H1 as P. now erewrite P.
    simpl in H0.
    rewrite not_elem_of_flat_union in H0.
    apply elem_of_list_In in H1. by apply H0 in H1.
  * f_equal.
    - rewrite H; set_solver.
    - rewrite <- (map_id l) at 2.
      apply map_ext_in.
      rewrite List.Forall_forall in H0. intros. eapply H0 in H2 as P. now erewrite P.
      simpl in H1. apply not_elem_of_union in H1 as [_ H1].
      rewrite not_elem_of_flat_union in H1.
      apply elem_of_list_In in H2. by apply H1 in H2.
  * f_equal.
    - rewrite H; set_solver.
    - f_equal. rewrite <- (map_id l) at 2. apply map_ext_in.
      rewrite List.Forall_forall in H0. intros. eapply H0 in H2 as P. destruct a, p.
      simpl in H1. apply not_elem_of_union in H1 as [_ H1].
      rewrite not_elem_of_flat_union in H1.
      apply elem_of_list_In in H2. apply H1 in H2.
      rewrite (proj1 (P _ _)), (proj2 (P _ _)). reflexivity.
      all: set_solver.
  * rewrite H, H0; set_solver.
  * rewrite H, H0; set_solver.
  * f_equal.
    - f_equal. rewrite <- (map_id l) at 2. apply map_ext_in.
      rewrite List.Forall_forall in H0. intros. eapply H0 in H2 as P. destruct a.
      simpl in H1. apply not_elem_of_union in H1 as [_ H1].
      rewrite not_elem_of_flat_union in H1.
      apply elem_of_list_In in H2. apply H1 in H2.
      rewrite P. reflexivity. set_solver.
    - rewrite H; set_solver.
  * rewrite H, H0, H1; set_solver.
Qed.

Corollary isNotUsed_renamePID_exp :
  (forall e from to, from ∉ (usedPIDsExp e) -> renamePID from to e = e).
Proof.
  apply isNotUsed_renamePID_ind.
Qed.

Corollary isNotUsed_renamePID_nval :
  (forall e from to, from ∉ (usedPIDsNVal e) -> renamePIDNVal from to e = e).
Proof.
  apply isNotUsed_renamePID_ind.
Qed.

Corollary isNotUsed_renamePID_val :
  (forall e from to, from ∉ (usedPIDsVal e) -> renamePIDVal from to e = e).
Proof.
  apply isNotUsed_renamePID_ind.
Qed.

Corollary isNotUsed_renamePID_red :
  (forall e from to, from ∉ (usedPIDsRed e) -> renamePIDRed from to e = e).
Proof.
  destruct e; simpl; intros; auto.
  * now rewrite isNotUsed_renamePID_exp.
  * f_equal. rewrite <- (map_id vs) at 2.
    apply map_ext_in. intros.
    rewrite not_elem_of_flat_union in H.
    apply elem_of_list_In in H0. apply H in H0.
    by rewrite isNotUsed_renamePID_val.
  * destruct e, p. destruct_not_in.
    rewrite isNotUsed_renamePID_val, isNotUsed_renamePID_val.
    all: set_solver.
Qed.

Corollary isNotUsed_renamePID_frameId :
  forall ident from to, from ∉ (usedPIDsFrameId ident) -> renamePIDFrameId from to ident = ident.
Proof.
  destruct ident; auto; intros; simpl in *; repeat rewrite isNotUsed_renamePID_val; try reflexivity; set_solver.
Qed.

Corollary isNotUsed_renamePID_frame :
  forall f from to, from ∉ (usedPIDsFrame f) -> renamePIDFrame from to f = f.
Proof.
  destruct f; intros; simpl in *; destruct_not_in.
  * now rewrite isNotUsed_renamePID_exp.
  * now rewrite isNotUsed_renamePID_val.
  * rewrite isNotUsed_renamePID_frameId by set_solver.
    f_equal.
    - rewrite <- (map_id vl) at 2.
      apply map_ext_in. intros.
      apply not_elem_of_union in H as [H _].
      apply not_elem_of_union in H as [_ H].
      rewrite not_elem_of_flat_union in H.
      apply elem_of_list_In in H0. apply H in H0.
      by rewrite isNotUsed_renamePID_val.
    - rewrite <- (map_id el) at 2.
      apply map_ext_in. intros.
      apply not_elem_of_union in H as [_ H].
      rewrite not_elem_of_flat_union in H.
      apply elem_of_list_In in H0. apply H in H0.
      by rewrite isNotUsed_renamePID_exp.
  * f_equal. rewrite <- (map_id l) at 2.
    apply map_ext_in. intros.
    rewrite not_elem_of_flat_union in H.
    apply elem_of_list_In in H0. apply H in H0.
    by rewrite isNotUsed_renamePID_exp.
  * f_equal.
    - rewrite isNotUsed_renamePID_exp; set_solver.
    - rewrite <- (map_id l) at 2.
      apply map_ext_in. intros.
      apply not_elem_of_union in H as [_ H].
      rewrite not_elem_of_flat_union in H.
      apply elem_of_list_In in H0. apply H in H0.
      by rewrite isNotUsed_renamePID_exp.
  * f_equal.
    - rewrite isNotUsed_renamePID_val; set_solver.
    - rewrite <- (map_id l) at 2.
      apply map_ext_in. intros.
      apply not_elem_of_union in H as [_ H].
      rewrite not_elem_of_flat_union in H.
      apply elem_of_list_In in H0. apply H in H0.
      by rewrite isNotUsed_renamePID_exp.
  * f_equal.
    rewrite <- (map_id l) at 2. apply map_ext_in. intros. destruct a, p.
    rewrite not_elem_of_flat_union in H.
    apply elem_of_list_In in H0. apply H in H0.
    rewrite isNotUsed_renamePID_exp, isNotUsed_renamePID_exp. reflexivity.
    all: set_solver.
  * f_equal.
    - rewrite <- (map_id lv) at 2. apply map_ext_in. intros.
      apply not_elem_of_union in H as [H _].
      apply not_elem_of_union in H as [_ H].
      rewrite not_elem_of_flat_union in H.
      apply elem_of_list_In in H0. apply H in H0.
      rewrite isNotUsed_renamePID_val. reflexivity. set_solver.
    - rewrite isNotUsed_renamePID_exp; set_solver.
    - rewrite <- (map_id le) at 2. apply map_ext_in. intros.
      apply not_elem_of_union in H as [_ H]. destruct a, p.
      rewrite not_elem_of_flat_union in H.
      apply elem_of_list_In in H0. apply H in H0.
      rewrite isNotUsed_renamePID_exp, isNotUsed_renamePID_exp. reflexivity.
      all: set_solver.
  * now rewrite isNotUsed_renamePID_exp.
  * now rewrite isNotUsed_renamePID_exp.
  * rewrite isNotUsed_renamePID_exp, isNotUsed_renamePID_exp; set_solver.
Qed.

Corollary isNotUsed_renamePID_stack :
  forall fs from to, from ∉ (usedPIDsStack fs) -> renamePIDStack from to fs = fs.
Proof.
  intros. unfold renamePIDStack, usedPIDsStack in *.
  f_equal. rewrite <- (map_id fs) at 2.
  apply map_ext_in. intros.
  rewrite not_elem_of_flat_union in H.
  apply elem_of_list_In in H0. apply H in H0.
  by rewrite isNotUsed_renamePID_frame.
Qed.

Local Theorem double_PIDrenaming_ind :
  (forall e from to, to ∉ (usedPIDsExp e) -> e.⟦from ↦ to⟧.⟦to ↦ from⟧ = e) /\
  (forall e from to, to ∉ (usedPIDsNVal e) -> e.⟦from ↦ to⟧ₙ.⟦to ↦ from⟧ₙ = e) /\
  (forall e from to, to ∉ (usedPIDsVal e) -> e.⟦from ↦ to⟧ᵥ.⟦to ↦ from⟧ᵥ = e).
Proof.
  apply Exp_ind with
    (QV := fun l => Forall (fun e => forall from to, to ∉ (usedPIDsVal e) -> e.⟦from ↦ to⟧ᵥ.⟦to ↦ from⟧ᵥ = e) l)
    (Q := fun l => Forall (fun e => forall from to, to ∉ (usedPIDsExp e) -> e.⟦from ↦ to⟧.⟦to ↦ from⟧ = e) l)
    (RV := fun l => Forall (fun '(e1, e2) => forall from to,
        (to ∉ (usedPIDsVal e1) -> e1.⟦from ↦ to⟧ᵥ.⟦to ↦ from⟧ᵥ = e1) /\
        (to ∉ (usedPIDsVal e2) -> e2.⟦from ↦ to⟧ᵥ.⟦to ↦ from⟧ᵥ = e2)) l)
    (R := fun l => Forall (fun '(e1, e2) => forall from to,
        (to ∉ (usedPIDsExp e1) -> e1.⟦from ↦ to⟧.⟦to ↦ from⟧ = e1) /\
        (to ∉ (usedPIDsExp e2) -> e2.⟦from ↦ to⟧.⟦to ↦ from⟧ = e2)) l)
    (W := fun l => Forall (fun '(p, g, e) => forall from to,
       (to ∉ (usedPIDsExp g) -> g.⟦from ↦ to⟧.⟦to ↦ from⟧ = g) /\
       (to ∉ (usedPIDsExp e) -> e.⟦from ↦ to⟧.⟦to ↦ from⟧ = e)) l)
    (Z := fun l => Forall (fun '(n, e) => forall from to, to ∉ (usedPIDsExp e) -> e.⟦from ↦ to⟧.⟦to ↦ from⟧ = e) l)
   (VV := fun l => Forall
      (fun '(id, vl, e) => forall from to, to ∉ (usedPIDsExp e) -> e.⟦from ↦ to⟧.⟦to ↦ from⟧ = e) l); intros; simpl; try reflexivity; try now rewrite H.
  18-31: try now (constructor; auto).
  * break_match_goal; simpl. 2: break_match_goal; eqb_to_eq.
    - rewrite Nat.eqb_refl. eqb_to_eq. now subst.
    - subst. cbn in H. set_solver.
    - reflexivity.
  * rewrite H, H0; set_solver.
  * rewrite map_map. f_equal. rewrite <- map_id. apply map_ext_in.
    intros. simpl in H0. eapply List.Forall_forall in H. rewrite H; auto. 2: assumption.
    apply elem_of_list_In in H1.
    rewrite not_elem_of_flat_union in H0.
    by apply H0 in H1.
  * rewrite map_map. f_equal. rewrite <- map_id. apply map_ext_in.
    intros. simpl in H0. rewrite List.Forall_forall in H. destruct a.
    specialize (H (v, v0) H1 from to) as [H_1 H_2].
    rewrite H_1, H_2. reflexivity.
    all: apply elem_of_list_In in H1; rewrite not_elem_of_flat_union in H0;
         apply H0 in H1; set_solver.
  * rewrite map_map.
    simpl in H1. apply not_elem_of_union in H1 as [H1_1 H1_2].
    rewrite not_elem_of_flat_union in H1_2.
    f_equal. 2: now rewrite H0. rewrite <- map_id. apply map_ext_in.
    intros. rewrite List.Forall_forall in H.
    specialize (H a H1). destruct a,p.
    rewrite H; auto.
    apply elem_of_list_In in H1.
    by apply H1_2 in H1.
  * rewrite map_map. f_equal. rewrite <- map_id. apply map_ext_in.
    intros. simpl in H0. rewrite List.Forall_forall in H. rewrite H; auto.
    rewrite not_elem_of_flat_union in H0. apply elem_of_list_In in H1. set_solver.
  * rewrite H, H0; set_solver.
  * rewrite map_map. f_equal. rewrite <- map_id. apply map_ext_in.
    intros. simpl in H0. rewrite List.Forall_forall in H. rewrite H; auto.
    rewrite not_elem_of_flat_union in H0. apply elem_of_list_In in H1. set_solver.
  * rewrite map_map. f_equal. rewrite <- map_id. apply map_ext_in.
    intros. simpl in H0. rewrite List.Forall_forall in H. destruct a.
    specialize (H (e, e0) H1 from to) as [H_1 H_2].
    rewrite H_1, H_2. reflexivity.
    all: apply elem_of_list_In in H1; rewrite not_elem_of_flat_union in H0;
         apply H0 in H1; set_solver.
  * rewrite map_map. simpl in H2.
    apply not_elem_of_union in H2 as [? H2].
    rewrite not_elem_of_flat_union in H2.
    f_equal. 1: rewrite H; set_solver. 1: rewrite H0; set_solver.
    rewrite <- map_id. apply map_ext_in.
    intros. simpl in H0. rewrite List.Forall_forall in H1. rewrite H1; auto.
    apply elem_of_list_In in H4. set_solver.
  * rewrite map_map. f_equal. rewrite <- map_id. apply map_ext_in.
    intros. simpl in H0. rewrite List.Forall_forall in H. rewrite H; auto.
    rewrite not_elem_of_flat_union in H0.
    apply elem_of_list_In in H1. set_solver.
  * rewrite map_map. simpl in H1.
    apply not_elem_of_union in H1 as [H1_1 H1_2].
    rewrite not_elem_of_flat_union in H1_2.
    f_equal. 1: rewrite H; set_solver.
    rewrite <- map_id. apply map_ext_in.
    intros. simpl in H1_2. rewrite List.Forall_forall in H0. rewrite H0; auto.
    apply elem_of_list_In in H1; set_solver.
  * rewrite map_map. simpl in H1.
    apply not_elem_of_union in H1 as [H1_1 H1_2].
    rewrite not_elem_of_flat_union in H1_2.
    f_equal. 1: now rewrite H.
    rewrite <- map_id. apply map_ext_in.
    intros. rewrite List.Forall_forall in H0. specialize (H0 _ H1). destruct a, p.
    rewrite (proj1 (H0 _ _)); auto. rewrite (proj2 (H0 _ _)); auto.
    all: apply elem_of_list_In in H1; apply H1_2 in H1; set_solver.
  * simpl in H1. apply not_elem_of_union in H1 as [? ?].
    now rewrite H, H0.
  * simpl in H1. apply not_elem_of_union in H1 as [? ?].
    now rewrite H, H0.
  * rewrite map_map. simpl in H1.
    apply not_elem_of_union in H1 as [H1_1 H1_2].
    rewrite not_elem_of_flat_union in H1_2.
    f_equal. 2: now rewrite H.
    rewrite <- map_id. apply map_ext_in.
    intros. rewrite List.Forall_forall in H0. specialize (H0 _ H1). destruct a.
    rewrite H0; auto.
    apply elem_of_list_In in H1. set_solver.
  * simpl in H2. apply not_elem_of_union in H2 as [H3 ?]. apply not_elem_of_union in H3 as [? ?].
    now rewrite H, H0, H1.
Qed.


Corollary double_PIDrenaming_exp :
  forall e from to, to ∉ (usedPIDsExp e) -> e.⟦from ↦ to⟧.⟦to ↦ from⟧ = e.
Proof.
  apply double_PIDrenaming_ind.
Qed.

Corollary double_PIDrenaming_nval :
  forall e from to, to ∉ (usedPIDsNVal e) -> e.⟦from ↦ to⟧ₙ.⟦to ↦ from⟧ₙ = e.
Proof.
  apply double_PIDrenaming_ind.
Qed.

Corollary double_PIDrenaming_val :
  forall e from to, to ∉ (usedPIDsVal e) -> e.⟦from ↦ to⟧ᵥ.⟦to ↦ from⟧ᵥ = e.
Proof.
  apply double_PIDrenaming_ind.
Qed.

Corollary double_PIDrenaming_red :
  forall e from to, to ∉ (usedPIDsRed e) -> e.⟦from ↦ to⟧ᵣ.⟦to ↦ from⟧ᵣ = e.
Proof.
  destruct e; simpl; intros; auto.
  * now rewrite double_PIDrenaming_exp.
  * rewrite <- (map_id vs) at 2. f_equal. (* change to vseq equality *)
    rewrite map_map. apply map_ext_in. intros.
    apply elem_of_list_In in H0.
    rewrite not_elem_of_flat_union in H. apply H in H0.
    rewrite double_PIDrenaming_val; set_solver.
  * destruct e, p. destruct_not_in.
    simpl. rewrite double_PIDrenaming_val, double_PIDrenaming_val; set_solver.
Qed.

Corollary double_PIDrenaming_frameId :
  forall ident from to, to ∉ (usedPIDsFrameId ident) -> ident.⟦from ↦ to⟧ᵢ.⟦to ↦ from⟧ᵢ = ident.
Proof.
  destruct ident; auto; intros; simpl in *; repeat rewrite double_PIDrenaming_val; set_solver.
Qed.

Corollary double_PIDrenaming_frame :
  forall f from to, to ∉ (usedPIDsFrame f) -> f.⟦from ↦ to⟧ₖ.⟦to ↦ from⟧ₖ = f.
Proof.
  destruct f; intros; simpl in *; destruct_not_in.
  * now rewrite double_PIDrenaming_exp.
  * now rewrite double_PIDrenaming_val.
  * rewrite double_PIDrenaming_frameId by set_solver.
    f_equal.
    - rewrite <- (map_id vl) at 2. rewrite map_map. apply map_ext_in. intros.
      apply not_elem_of_union in H as [H _].
      apply not_elem_of_union in H as [_ H].
      rewrite not_elem_of_flat_union in H.
      apply elem_of_list_In in H0.
      rewrite double_PIDrenaming_val; set_solver.
    - rewrite <- (map_id el) at 2. rewrite map_map. apply map_ext_in. intros.
      apply not_elem_of_union in H as [_ H].
      rewrite not_elem_of_flat_union in H.
      apply elem_of_list_In in H0.
      rewrite double_PIDrenaming_exp; set_solver.
  * f_equal. rewrite <- (map_id l) at 2. rewrite map_map. apply map_ext_in. intros.
    rewrite not_elem_of_flat_union in H.
    apply elem_of_list_In in H0.
    rewrite double_PIDrenaming_exp; set_solver.
  * f_equal.
    - rewrite double_PIDrenaming_exp; set_solver.
    - rewrite <- (map_id l) at 2. rewrite map_map. apply map_ext_in. intros.
      apply not_elem_of_union in H as [_ H].
      rewrite not_elem_of_flat_union in H.
      apply elem_of_list_In in H0.
      rewrite double_PIDrenaming_exp; set_solver.
  * f_equal.
    - rewrite double_PIDrenaming_val; set_solver.
    - rewrite <- (map_id l) at 2. rewrite map_map. apply map_ext_in. intros.
      apply not_elem_of_union in H as [_ H].
      rewrite not_elem_of_flat_union in H.
      apply elem_of_list_In in H0.
      rewrite double_PIDrenaming_exp; set_solver.
  * f_equal.
    rewrite <- (map_id l) at 2. rewrite map_map. apply map_ext_in. intros.
    rewrite not_elem_of_flat_union in H.
    destruct a, p. simpl in *.
    apply elem_of_list_In in H0. apply H in H0.
    rewrite double_PIDrenaming_exp, double_PIDrenaming_exp; set_solver.
  * f_equal.
    - rewrite <- (map_id lv) at 2. rewrite map_map. apply map_ext_in. intros.
      apply not_elem_of_union in H as [H _].
      apply not_elem_of_union in H as [_ H].
      rewrite not_elem_of_flat_union in H.
      apply elem_of_list_In in H0. apply H in H0.
      rewrite double_PIDrenaming_val; set_solver.
    - rewrite double_PIDrenaming_exp; set_solver.
    - rewrite <- (map_id le) at 2. rewrite map_map. apply map_ext_in. intros.
      apply not_elem_of_union in H as [_ H].
      rewrite not_elem_of_flat_union in H.
      apply elem_of_list_In in H0. apply H in H0.
      destruct a, p.
      rewrite double_PIDrenaming_exp, double_PIDrenaming_exp; set_solver.
  * now rewrite double_PIDrenaming_exp.
  * now rewrite double_PIDrenaming_exp.
  * rewrite double_PIDrenaming_exp, double_PIDrenaming_exp; set_solver.
Qed.

Corollary double_PIDrenaming_stack :
  forall fs from to, to ∉ (usedPIDsStack fs) -> fs.⟦from ↦ to⟧ₛₜ.⟦to ↦ from⟧ₛₜ = fs.
Proof.
  intros. unfold renamePIDStack, usedPIDsStack in *.
  rewrite <- (map_id fs) at 2. rewrite map_map. apply map_ext_in. intros.
  rewrite not_elem_of_flat_union in H.
  apply elem_of_list_In in H0.
  rewrite double_PIDrenaming_frame; set_solver.
Qed.

Lemma renamePID_implies_scope :
  (forall e Γ from to, EXP Γ ⊢ renamePID from to e -> EXP Γ ⊢ e) /\
  (forall e Γ from to, NVAL Γ ⊢ renamePIDNVal from to e -> NVAL Γ ⊢ e) /\
  (forall e Γ from to, VAL Γ ⊢ renamePIDVal from to e -> VAL Γ ⊢ e).
Proof.
  apply Exp_ind with
    (Q := fun l => Forall (fun e => forall Γ from to, EXP Γ ⊢ renamePID from to e -> EXP Γ ⊢ e) l)
    (QV := fun l => Forall (fun e => forall Γ from to, VAL Γ ⊢ renamePIDVal from to e -> VAL Γ ⊢ e) l)
    (R := fun l => Forall (fun '(e1, e2) => forall Γ from to, (EXP Γ ⊢ renamePID from to e1 -> EXP Γ ⊢ e1) /\ (EXP Γ ⊢ renamePID from to e2 -> EXP Γ ⊢ e2)) l)
    (RV := fun l => Forall (fun '(e1, e2) => forall Γ from to, (VAL Γ ⊢ renamePIDVal from to e1 -> VAL Γ ⊢ e1) /\ (VAL Γ ⊢ renamePIDVal from to e2 -> VAL Γ ⊢ e2)) l)
    (VV := fun l => Forall (fun '(_, _, e) => forall Γ from to, EXP Γ ⊢ renamePID from to e -> EXP Γ ⊢ e) l)
    (W := fun l => Forall (fun '(_,g,e) => forall Γ from to, (EXP Γ ⊢ renamePID from to g -> EXP Γ ⊢ g) /\ (EXP Γ ⊢ renamePID from to e -> EXP Γ ⊢ e)) l)
    (Z := fun l => Forall (fun '(_, e) => forall Γ from to, EXP Γ ⊢ renamePID from to e -> EXP Γ ⊢ e) l).
  all: intros. 25-38: constructor; auto.
  25-27: intros; split; firstorder.
  all: simpl in *; destruct_scopes; try (by (constructor; firstorder)).
  * rewrite Forall_nth in H. constructor. intros.
    eapply H; auto.
    rewrite <- map_nth. eapply H3. by rewrite map_length.
  * rewrite (Forall_nth) in H. Unshelve. 2: exact (VNil, VNil).
    constructor; intros.
    - apply H in H0 as H0'. rewrite map_length in *.
      apply H2 in H0. rewrite map_nth with (d := (VNil, VNil)).
      rewrite map_map, map_nth with (d := (VNil, VNil)) in H0. destruct (nth i l _).
      simpl in *. eapply (proj1 (H0' _ _ _)). apply H0.
    - apply H in H0 as H0'. rewrite map_length in *.
      apply H4 in H0. rewrite map_nth with (d := (VNil, VNil)).
      rewrite map_map, map_nth with (d := (VNil, VNil)) in H0. destruct (nth i l _).
      simpl in *. eapply (proj2 (H0' _ _ _)). apply H0.
  * rewrite (Forall_nth) in H. Unshelve. 2: exact (0,0, ˝VNil).
    constructor; intros.
    - apply H in H1 as H1'. rewrite map_length in *.
      apply H5 in H1. do 2 rewrite map_nth with (d := (0,0, ˝VNil)).
      do 2 rewrite map_map in H1.
      do 2 rewrite map_nth with (d := (0,0, ˝VNil)) in H1. destruct (nth i ext _).
      simpl in *. destruct p. eapply (H1' _ _ _). apply H1.
    - eapply H0. rewrite map_length in H8. eapply H8.
  * rewrite Forall_nth in H. constructor. intros.
    eapply H; auto.
    rewrite <- map_nth. eapply H3. by rewrite map_length.
  * rewrite Forall_nth in H. constructor. intros.
    eapply H; auto.
    rewrite <- map_nth. eapply H3. by rewrite map_length.
  * rewrite (Forall_nth) in H. Unshelve. 2: exact (˝VNil, ˝VNil).
    constructor; intros.
    - apply H in H0 as H0'. rewrite map_length in *.
      apply H2 in H0. rewrite map_nth with (d := (˝VNil, ˝VNil)).
      rewrite map_map, map_nth with (d := (˝VNil, ˝VNil)) in H0. destruct (nth i l _).
      simpl in *. eapply (proj1 (H0' _ _ _)). apply H0.
    - apply H in H0 as H0'. rewrite map_length in *.
      apply H4 in H0. rewrite map_nth with (d := (˝VNil, ˝VNil)).
      rewrite map_map, map_nth with (d := (˝VNil, ˝VNil)) in H0. destruct (nth i l _).
      simpl in *. eapply (proj2 (H0' _ _ _)). apply H0.
  * constructor.
    - rewrite Forall_nth in H1. intros.
      eapply H1; auto.
      rewrite <- map_nth. eapply H7. by rewrite map_length.
    - by eapply H.
    - by eapply H0.
  * rewrite Forall_nth in H. constructor. intros.
    eapply H; auto.
    rewrite <- map_nth. eapply H3. by rewrite map_length.
  * constructor.
    - by eapply H.
    - rewrite Forall_nth in H0. intros.
      eapply H0; auto.
      rewrite <- map_nth. eapply H6. by rewrite map_length.
  * rewrite (Forall_nth) in H0. Unshelve. 2: exact ([], ˝VNil, ˝VNil).
    constructor; intros.
    - by eapply H.
    - apply H0 in H1 as P. rewrite map_length in *.
      apply H6 in H1. rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
      rewrite map_map, map_map in H1.
      rewrite map_nth with (d := ([], ˝VNil, ˝VNil)) in H1.
      rewrite (map_nth (λ x : list Pat * Exp * Exp,
                    (fst ∘ fst)
                      (let '(p, g, e) := x in (p, g .⟦ from ↦ to ⟧, e .⟦ from ↦ to ⟧))) l) with (d := ([], ˝VNil, ˝VNil)) in H1.
      rewrite (map_nth (fst ∘ fst) l) with (d := ([], ˝VNil, ˝VNil)).
      destruct (nth i l _).
      simpl in *. destruct p. eapply (proj1 (P _ _ _)). apply H1.
    - apply H0 in H1 as P. rewrite map_length in *.
      apply H7 in H1. rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
      rewrite map_map, map_map in H1.
      rewrite map_nth with (d := ([], ˝VNil, ˝VNil)) in H1.
      rewrite (map_nth (λ x : list Pat * Exp * Exp,
                    (fst ∘ fst)
                      (let '(p, g, e) := x in (p, g .⟦ from ↦ to ⟧, e .⟦ from ↦ to ⟧))) l) with (d := ([], ˝VNil, ˝VNil)) in H1.
      rewrite (map_nth (fst ∘ fst) l) with (d := ([], ˝VNil, ˝VNil)).
      destruct (nth i l _).
      simpl in *. destruct p. eapply (proj2 (P _ _ _)). apply H1.
  * constructor.
    - rewrite Forall_nth in H0. Unshelve. 2: exact (0, ˝VNil). intros.
      rewrite map_length in *.
      do 2 rewrite map_nth with (d := (0, ˝VNil)).
      apply H0 in H1 as P.
      apply H5 in H1.
      do 2 rewrite map_map in H1.
      do 2 rewrite map_nth with (d := (0, ˝VNil)) in H1. destruct nth.
      eapply P. apply H1.
    - eapply H. by rewrite map_length in H6.
Qed.

Corollary flat_union_app :
  forall {A B} {H : EqDecision B} {H0 : Countable B}
         (f : A -> gset B) (l1 l2 : list A),
    flat_union f (l1 ++ l2) = flat_union f l1 ∪ flat_union f l2.
Proof.
  intros. rewrite flat_union_map, map_app.
  do 2 rewrite flat_union_map.
  by rewrite union_list_app_L.
Qed.


Lemma renamePID_id :
  (forall e p, renamePID p p e = e) /\
  (forall e p, renamePIDNVal p p e = e) /\
  (forall e p, renamePIDVal p p e = e).
Proof.

Admitted.

Corollary renamePID_id_red :
  forall r p, renamePIDRed p p r = r.
Proof.
  destruct r; intros; cbn; auto.
  * f_equal. apply renamePID_id.
  * rewrite <- (map_id vs) at 2. f_equal. apply map_ext_in.
    intros. apply renamePID_id.
  * destruct e, p0.
    by do 2 rewrite (proj2 (proj2 renamePID_id)).
Qed.

Lemma renamePID_id_frameId :
  forall i p, renamePIDFrameId p p i = i.
Proof.
  destruct i; simpl; intros; try reflexivity.
  * by do 2 rewrite (proj2 (proj2 renamePID_id)).
  * by rewrite (proj2 (proj2 renamePID_id)).
Qed.


Lemma renamePID_id_frame :
  forall f p, renamePIDFrame p p f = f.
Proof.

Admitted.

Lemma renamePID_id_fstack :
  forall fs p, renamePIDStack p p fs = fs.
Proof.
  intros. rewrite <- (map_id fs) at 2. f_equal. apply map_ext_in.
  intros. by apply renamePID_id_frame.
Qed.
