From CoreErlang.FrameStack Require Import SubstSemanticsLemmas.

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

Notation "e .[ x ↦ y ]" := (renamePID x y e) (at level 2).
Notation "e .[ x ↦ y ]ᵥ" := (renamePIDVal x y e) (at level 2).
Notation "e .[ x ↦ y ]ₙ" := (renamePIDNVal x y e) (at level 2).

Definition renamePIDRed (from to : PID) (r : Redex) : Redex :=
match r with
 | RExp e => RExp (renamePID from to e)
 | RValSeq vs => RValSeq (map (renamePIDVal from to) vs)
 | RExc (class, reas, det) => RExc (class, renamePIDVal from to reas,
                                           renamePIDVal from to det)
 | RBox => RBox
end.

Notation "e .[ x ↦ y ]ᵣ" := (renamePIDRed x y e) (at level 2).

Definition renamePIDFrameId (from to : PID) (f : FrameIdent) : FrameIdent :=
match f with
 | IValues => f
 | ITuple => f
 | IMap => f
 | ICall m f => ICall (renamePIDVal from to m) (renamePIDVal from to f)
 | IPrimOp f => IPrimOp f
 | IApp v => IApp (renamePIDVal from to v)
end.

Notation "e .[ x ↦ y ]ᵢ" := (renamePIDFrameId x y e) (at level 2).

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

Notation "e .[ x ↦ y ]ₖ" := (renamePIDFrame x y e) (at level 2).

Definition renamePIDStack (from to : PID) (fs : FrameStack) :=
  map (renamePIDFrame from to) fs.

Notation "e .[ x ↦ y ]ₛ" := (renamePIDStack x y e) (at level 2).

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
      do 2 rewrite map_nth with (d := (0, 0, `VNil)).
      rewrite map_length in H1. eapply H in H1.
      do 2 rewrite map_nth with (d := (0, 0, `VNil)) in H1.
      destruct nth, p. rewrite map_length. eassumption.
    - rewrite map_length. auto.
  * constructor. intros.
    rewrite map_nth with (d := `VNil).
    rewrite map_length in H0. eapply H in H0.
    eassumption.
  * constructor; intros.
    - rewrite map_map.
      rewrite map_nth with (d := (`VNil, `VNil)).
      rewrite map_length in H1. eapply H in H1.
      rewrite map_nth with (d := (`VNil, `VNil)) in H1.
      destruct nth. eassumption.
    - rewrite map_map.
      rewrite map_nth with (d := (`VNil, `VNil)).
      rewrite map_length in H1. eapply H0 in H1.
      rewrite map_nth with (d := (`VNil, `VNil)) in H1.
      destruct nth. eassumption.
  * constructor. intros.
    rewrite map_nth with (d := `VNil).
    rewrite map_length in H0. eapply H in H0.
    eassumption.
  * constructor; intros.
    - rewrite map_nth with (d := `VNil).
      rewrite map_length in H2. eapply H in H2.
      eassumption.
    - auto.
    - auto.
  * constructor. intros.
    rewrite map_nth with (d := `VNil).
    rewrite map_length in H0. eapply H in H0.
    eassumption.
  * constructor; intros.
    - auto.
    - rewrite map_nth with (d := `VNil).
      rewrite map_length in H1. eapply H0 in H1.
      eassumption.
  * constructor; intros.
    - auto.
    - do 2 rewrite map_map.
      rewrite map_nth with (d := ([], `VNil, `VNil)).
      rewrite map_nth with (f := (fun x : list Pat * Exp * Exp =>
             (fst ∘ fst)
               (let
                '(p, g, e3) := x in
                 (p, renamePID from to g, renamePID from to e3)))) (d := ([], `VNil, `VNil)).
      rewrite map_length in H2. eapply H0 in H2.
      rewrite map_nth with (d := ([], `VNil, `VNil)) in H2.
      setoid_rewrite (map_nth (fst ∘ fst)) with (d := ([], `VNil, `VNil)) in H2.
      destruct nth, p. cbn in *. eassumption.
    - do 2 rewrite map_map.
      rewrite map_nth with (d := ([], `VNil, `VNil)).
      rewrite map_nth with (f := (fun x : list Pat * Exp * Exp =>
             (fst ∘ fst)
               (let
                '(p, g, e3) := x in
                 (p, renamePID from to g, renamePID from to e3)))) (d := ([], `VNil, `VNil)).
      rewrite map_length in H2. eapply H1 in H2.
      rewrite map_nth with (d := ([], `VNil, `VNil)) in H2.
      setoid_rewrite (map_nth (fst ∘ fst)) with (d := ([], `VNil, `VNil)) in H2.
      destruct nth, p. cbn in *. eassumption.
  * constructor; intros.
    - do 2 rewrite map_map.
      rewrite map_length in *. eapply H in H1.
      do 2 rewrite map_nth with (d := (0, `VNil)).
      do 2 rewrite map_nth with (d := (0, `VNil)) in H1.
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
      rewrite Forall_nth in *. intros. eapply (H _ d) in H1. destruct nth, p.
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
      rewrite Forall_nth in *. intros. eapply (H0 _ d) in H1. destruct nth, p.
      now rewrite (proj1 (H1 _ _ _)), (proj2 (H1 _ _ _)).
  * now rewrite H, H0.
  * now rewrite H, H0.
  * f_equal.
    - do 2 rewrite map_map. apply map_ext_Forall.
      rewrite Forall_nth in *. intros. eapply (H0 _ d) in H1. destruct nth.
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
  unfold shift. destruct σ; auto.
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
      rewrite Forall_nth in *. intros. eapply (H _ d) in H1. destruct nth, p.
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
      rewrite Forall_nth in *. intros. eapply (H0 _ d) in H1. destruct nth, p.
      rewrite (proj1 (H1 _ _ _)), (proj2 (H1 _ _ _)). now rewrite renamePID_upn.
  * rewrite H, H0. now rewrite renamePID_upn.
  * now rewrite H, H0.
  * f_equal.
    - do 2 rewrite map_map. apply map_ext_Forall.
      rewrite Forall_nth in *. intros. eapply (H0 _ d) in H1. destruct nth.
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
    break_match_goal; erewrite renamePID_Val_eqb in Heqb; now rewrite Heqb.
  * revert l0. induction IHv; destruct l0; simpl; auto.
    break_match_goal; erewrite renamePID_Val_eqb in Heqb; rewrite Heqb; specialize (IHIHv l0).
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
    break_match_goal; erewrite renamePID_Val_eqb in Heqb; rewrite Heqb; specialize (IHIHv l0); simpl in *.
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
  destruct a. erewrite (renamePID_Val_eqb _ _ from to), (renamePID_Val_ltb _ _ from to).
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
  all: erewrite renamePID_Val_eqb in Heqb;
       try erewrite renamePID_Val_eqb in Heqb0;
       try erewrite renamePID_Val_eqb in Heqb1.
  all: simpl in *; try rewrite Heqb;
                   try rewrite Heqb0;
                   try rewrite Heqb1;
                   try reflexivity.
  all: erewrite renamePID_Val_eqb in Heqb2; rewrite Heqb2; try reflexivity.
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
  all: destruct Val_eqb eqn:P; erewrite renamePID_Val_eqb in P; rewrite P.
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
  all: destruct Val_eqb eqn:P0; erewrite renamePID_Val_eqb in P0; rewrite P0.
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
    break_match_hyp; erewrite renamePID_Val_eqb in Heqb; rewrite Heqb.
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
  clear IHv1. destruct (_ v2.[from ↦ to]ᵥ) eqn:P.
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

(* NOTE: instead of fold_right, Exists would be better, but Coq cannot guess the
   decreasing argument that way. *)
Fixpoint isUsedPIDExp (from : PID) (e : Exp) : Prop :=
match e with
 | VVal e => isUsedPIDVal from e
 | EExp e => isUsedPIDNVal from e
end
with isUsedPIDVal (from : PID) (v : Val) : Prop :=
match v with
 | VNil => False
 | VLit l => False
 | VPid p => from = p
 | VCons hd tl => isUsedPIDVal from hd \/ isUsedPIDVal from tl
 | VTuple l => fold_right (fun x acc => isUsedPIDVal from x \/ acc) False l
 | VMap l => fold_right (fun '(x, y) acc => isUsedPIDVal from x \/ isUsedPIDVal from y \/ acc) False l
 | VVar n => False
 | VFunId n => False
 | VClos ext id params e => fold_right (fun '(_, _, x) acc => isUsedPIDExp from x \/ acc) False ext \/ isUsedPIDExp from e
end
with isUsedPIDNVal (from : PID) (n : NonVal) : Prop :=
match n with
 | EFun vl e => isUsedPIDExp from e
 | EValues el => fold_right (fun x acc => isUsedPIDExp from x \/ acc) False el
 | ECons hd tl => isUsedPIDExp from hd \/ isUsedPIDExp from tl
 | ETuple l => fold_right (fun x acc => isUsedPIDExp from x \/ acc) False l
 | EMap l => fold_right (fun '(x, y) acc => isUsedPIDExp from x \/ isUsedPIDExp from y \/ acc) False l
 | ECall m f l => isUsedPIDExp from m \/ isUsedPIDExp from f \/ fold_right (fun x acc => isUsedPIDExp from x \/ acc) False l
 | EPrimOp f l => fold_right (fun x acc => isUsedPIDExp from x \/ acc) False l
 | EApp exp l => (isUsedPIDExp from exp) \/ fold_right (fun x acc => isUsedPIDExp from x \/ acc) False l
 | ECase e l => (isUsedPIDExp from e) \/ fold_right (fun '(_, g, e) acc => isUsedPIDExp from g \/ isUsedPIDExp from e \/ acc) False l
 | ELet l e1 e2 => isUsedPIDExp from e1 \/ isUsedPIDExp from e2
 | ESeq e1 e2 => isUsedPIDExp from e1 \/ isUsedPIDExp from e2
 | ELetRec l e => (isUsedPIDExp from e) \/ fold_right (fun '(_, e) acc => isUsedPIDExp from e \/ acc) False l
 | ETry e1 vl1 e2 vl2 e3 => isUsedPIDExp from e1 \/ isUsedPIDExp from e2 \/ isUsedPIDExp from e3
end.

Definition isUsedPIDRed (from : PID) (r : Redex) : Prop :=
match r with
 | RExp e => isUsedPIDExp from e
 | RValSeq vs => fold_right (fun x acc => isUsedPIDVal from x \/ acc) False vs
 | RExc (class, reas, det) => isUsedPIDVal from reas \/ isUsedPIDVal from det
 | RBox => False
end.


Definition isUsedPIDFrameId (from : PID) (f : FrameIdent) : Prop :=
match f with
 | ICall m f => isUsedPIDVal from m \/ isUsedPIDVal from f
 | IApp v => isUsedPIDVal from v
 | _ => False
end.

Definition isUsedPIDFrame (from : PID) (f : Frame) : Prop :=
match f with
 | FCons1 hd => isUsedPIDExp from hd
 | FCons2 tl => isUsedPIDVal from tl
 | FParams ident vl el =>
     (isUsedPIDFrameId from ident) \/
     fold_right (fun x acc => isUsedPIDExp from x \/ acc) False el \/
     fold_right (fun x acc => isUsedPIDVal from x \/ acc) False vl
 | FApp1 l => fold_right (fun x acc => isUsedPIDExp from x \/ acc) False l
 | FCallMod f l => (isUsedPIDExp from f) \/ fold_right (fun x acc => isUsedPIDExp from x \/ acc) False l
 | FCallFun m l => (isUsedPIDVal from m) \/ fold_right (fun x acc => isUsedPIDExp from x \/ acc) False l
 | FCase1 l => fold_right (fun '(_, g, e) acc => isUsedPIDExp from g \/ isUsedPIDExp from e \/ acc) False l
 | FCase2 lv ex le =>
   (isUsedPIDExp from ex) \/
   fold_right (fun x acc => isUsedPIDVal from x \/ acc) False lv \/
   fold_right (fun '(_, g, e) acc => isUsedPIDExp from g \/ isUsedPIDExp from e \/ acc) False le
 | FLet l e => isUsedPIDExp from e
 | FSeq e => isUsedPIDExp from e
 | FTry vl1 e2 vl2 e3 => isUsedPIDExp from e2 \/  isUsedPIDExp from e3
end.

Definition isUsedPIDStack (from : PID) (fs : FrameStack) : Prop :=
  fold_right (fun x acc => isUsedPIDFrame from x \/ acc) False fs.

Local Theorem isNotUsed_renamePID_ind :
  (forall e from to, ~isUsedPIDExp from e -> renamePID from to e = e) /\
  (forall e from to, ~isUsedPIDNVal from e -> renamePIDNVal from to e = e) /\
  (forall e from to, ~isUsedPIDVal from e -> renamePIDVal from to e = e).
Proof.
  apply Exp_ind with
    (QV := fun l => Forall (fun e => forall from to, ~isUsedPIDVal from e -> renamePIDVal from to e = e) l)
    (Q := fun l => Forall (fun e => forall from to, ~isUsedPIDExp from e -> renamePID from to e = e) l)
    (RV := fun l => Forall (fun '(e1, e2) => forall from to,
        (~isUsedPIDVal from e1 -> renamePIDVal from to e1 = e1) /\
        (~isUsedPIDVal from e2 -> renamePIDVal from to e2 = e2)) l)
    (R := fun l => Forall (fun '(e1, e2) => forall from to,
        (~isUsedPIDExp from e1 -> renamePID from to e1 = e1) /\
        (~isUsedPIDExp from e2 -> renamePID from to e1 = e2)) l)
    (W := fun l => Forall (fun '(p, g, e) => forall from to,
       (~isUsedPIDExp from g -> renamePID from to e = g) /\
       (~isUsedPIDExp from e -> renamePID from to e = e)) l)
    (Z := fun l => Forall (fun '(n, e) => forall from to, ~isUsedPIDExp from e -> renamePID from to e = e) l)
   (VV := fun l => Forall
      (fun '(id, vl, e) => forall from to, ~isUsedPIDExp from e -> renamePID from to e = e) l); intros; simpl; try reflexivity.
  all: try now intuition.
  all: try rewrite H; try rewrite H0; auto; try firstorder.
  * simpl in H. break_match_goal. now apply Nat.eqb_eq in Heqb. reflexivity.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext_in.
    rewrite Forall_forall in H. intros. eapply H in H1 as H1'. now erewrite H1'.
    simpl in H0. rewrite <- Exists_fold_right, Exists_exists in H0. firstorder.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext_in.
    rewrite Forall_forall in H. intros. eapply H in H1 as H1'. destruct a.
    erewrite (proj1 (H1' _ _)). erewrite (proj2 (H1' _ _)). reflexivity.
    - simpl in H0.
      rewrite <- Exists_fold_right with (P := fun x => ), Exists_exists in H0. firstorder.
Qed.
