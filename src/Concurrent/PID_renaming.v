From CoreErlang.FrameStack Require Import SubstSemanticsLemmas.

Import ListNotations.

Fixpoint rename_PID (from to : PID) (e : Exp) : Exp :=
match e with
 | VVal e => VVal (rename_PID_val from to e)
 | EExp e => EExp (rename_PID_nval from to e)
end
with rename_PID_val (from to : PID) (v : Val) : Val :=
match v with
 | VNil => VNil
 | VLit l => VLit l
 | VPid p =>
   if Nat.eqb from p then VPid to else VPid p
 | VCons hd tl => VCons (rename_PID_val from to hd) (rename_PID_val from to tl)
 | VTuple l => VTuple (map (rename_PID_val from to) l)
 | VMap l => VMap (map (fun '(x,y) => (rename_PID_val from to x, rename_PID_val from to y)) l)
 | VVar n => VVar n
 | VFunId n => VFunId n
 | VClos ext id params e => VClos (map (fun '(id, vl, e) => (id, vl, rename_PID from to e)) ext) id params (rename_PID from to e)
end
with rename_PID_nval (from to : PID) (n : NonVal) : NonVal :=
match n with
 | EFun vl e => EFun vl (rename_PID from to e)
 | EValues el => EValues (map (rename_PID from to) el)
 | ECons hd tl => ECons (rename_PID from to hd) (rename_PID from to tl)
 | ETuple l => ETuple (map (rename_PID from to) l)
 | EMap l => EMap (map (fun '(x,y) => (rename_PID from to x, rename_PID from to y)) l)
 | ECall m f l => ECall (rename_PID from to m) (rename_PID from to f) (map (rename_PID from to) l)
 | EPrimOp f l => EPrimOp f (map (rename_PID from to) l)
 | EApp exp l => EApp (rename_PID from to exp) (map (rename_PID from to) l)
 | ECase e l => ECase (rename_PID from to e)
                      (map (fun '(p, g, e) => (p, rename_PID from to g, rename_PID from to e)) l)
 | ELet l e1 e2 => ELet l (rename_PID from to e1) (rename_PID from to e2)
 | ESeq e1 e2 => ESeq (rename_PID from to e1) (rename_PID from to e2)
 | ELetRec l e => ELetRec (map (fun '(vl, e) => (vl, rename_PID from to e)) l)
                          (rename_PID from to e)
 | ETry e1 vl1 e2 vl2 e3 => ETry (rename_PID from to e1)
                                 vl1 (rename_PID from to e2)
                                 vl2 (rename_PID from to e3)
end.

Notation "e .[ x ↦ y ]" := (rename_PID x y e) (at level 2).
Notation "e .[ x ↦ y ]ᵥ" := (rename_PID_val x y e) (at level 2).
Notation "e .[ x ↦ y ]ₙ" := (rename_PID_nval x y e) (at level 2).

Definition rename_PID_red (from to : PID) (r : Redex) : Redex :=
match r with
 | RExp e => RExp (rename_PID from to e)
 | RValSeq vs => RValSeq (map (rename_PID_val from to) vs)
 | RExc (class, reas, det) => RExc (class, rename_PID_val from to reas,
                                           rename_PID_val from to det)
 | RBox => RBox
end.

Notation "e .[ x ↦ y ]ᵣ" := (rename_PID_red x y e) (at level 2).

Definition rename_PID_frameId (from to : PID) (f : FrameIdent) : FrameIdent :=
match f with
 | IValues => f
 | ITuple => f
 | IMap => f
 | ICall m f => ICall (rename_PID_val from to m) (rename_PID_val from to f)
 | IPrimOp f => IPrimOp f
 | IApp v => IApp (rename_PID_val from to v)
end.

Notation "e .[ x ↦ y ]ᵢ" := (rename_PID_frameId x y e) (at level 2).

Definition rename_PID_frame (from to : PID) (f : Frame) : Frame :=
match f with
 | FCons1 hd => FCons1 (rename_PID from to hd)
 | FCons2 tl => FCons2 (rename_PID_val from to tl)
 | FParams ident vl el =>
     FParams (rename_PID_frameId from to ident) (map (rename_PID_val from to) vl)
                                                (map (rename_PID from to) el)
 | FApp1 l => FApp1 (map (rename_PID from to) l)
 | FCallMod f l => FCallMod (rename_PID from to f) (map (rename_PID from to) l)
 | FCallFun m l => FCallFun (rename_PID_val from to m) (map (rename_PID from to) l)
 | FCase1 l => FCase1 (map (fun '(p, g, e) => (p, rename_PID from to g, rename_PID from to e)) l)
 | FCase2 lv ex le =>
   FCase2
     (map (rename_PID_val from to) lv)
     (rename_PID from to ex)
     (map (fun '(p, g, e) => (p, rename_PID from to g, rename_PID from to e)) le)
 | FLet l e => FLet l (rename_PID from to e)
 | FSeq e => FSeq (rename_PID from to e)
 | FTry vl1 e2 vl2 e3 => FTry vl1 (rename_PID from to e2)
                              vl2 (rename_PID from to e3)
end.

Notation "e .[ x ↦ y ]ₖ" := (rename_PID_frame x y e) (at level 2).

Definition rename_PID_stack (from to : PID) (fs : FrameStack) :=
  map (rename_PID_frame from to) fs.

Notation "e .[ x ↦ y ]ₛ" := (rename_PID_stack x y e) (at level 2).

Lemma rename_PID_preserves_scope :
  (forall Γ e, EXP Γ ⊢ e -> forall from to, EXP Γ ⊢ rename_PID from to e) /\
  (forall Γ e, VAL Γ ⊢ e -> forall from to, VAL Γ ⊢ rename_PID_val from to e) /\
  (forall Γ e, NVAL Γ ⊢ e -> forall from to, NVAL Γ ⊢ rename_PID_nval from to e).
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
                 (p, rename_PID from to g, rename_PID from to e3)))) (d := ([], `VNil, `VNil)).
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
                 (p, rename_PID from to g, rename_PID from to e3)))) (d := ([], `VNil, `VNil)).
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

Definition rename_PID_subst (from to : PID) (σ : Substitution) : Substitution :=
  fun x =>
    match σ x with
    | inl val => inl (rename_PID_val from to val)
    | r => r
    end.

Theorem rename_rename_PID :
  (forall e ρ from to, rename ρ (rename_PID from to e) =
                      rename_PID from to (rename ρ e)) /\
  (forall e ρ from to, renameNonVal ρ (rename_PID_nval from to e) =
                      rename_PID_nval from to (renameNonVal ρ e)) /\
  (forall e ρ from to, renameVal ρ (rename_PID_val from to e) =
                      rename_PID_val from to (renameVal ρ e)).
Proof.
  eapply Exp_ind with
    (QV := fun l => Forall (fun e => forall ρ from to, renameVal ρ (rename_PID_val from to e) =
                      rename_PID_val from to (renameVal ρ e)) l)
    (Q := fun l => Forall (fun e => forall ρ from to, rename ρ (rename_PID from to e) =
                      rename_PID from to (rename ρ e)) l)
    (RV := fun l => Forall (fun '(e1, e2) => forall ρ from to, renameVal ρ (rename_PID_val from to e1) =
                      rename_PID_val from to (renameVal ρ e1) /\
         renameVal ρ (rename_PID_val from to e2) =
                      rename_PID_val from to (renameVal ρ e2)) l)
    (R := fun l => Forall (fun '(e1, e2) => forall from to ρ, rename ρ (rename_PID from to e1) =
                      rename_PID from to (rename ρ e1) /\
         rename ρ (rename_PID from to e2) =
                      rename_PID from to (rename ρ e2)) l)
    (W := fun l => Forall (fun '(p, g, e) => forall from to ρ,
       rename ρ (rename_PID from to g) =
                      rename_PID from to (rename ρ g) /\
       rename ρ (rename_PID from to e) =
                      rename_PID from to (rename ρ e)) l)
    (Z := fun l => Forall (fun '(n, e) => forall from to ρ, rename ρ (rename_PID from to e) =
                      rename_PID from to (rename ρ e)) l)
   (VV := fun l => Forall
      (fun '(id, vl, e) => forall from to ρ, rename ρ (rename_PID from to e) =
                      rename_PID from to (rename ρ e)) l)
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

Lemma rename_PID_subst_up :
  forall σ from to, up_subst (rename_PID_subst from to σ) =
                    rename_PID_subst from to (up_subst σ).
Proof.
  unfold rename_PID_subst, up_subst. intros.
  extensionality x. destruct x; auto.
  unfold shift. destruct σ; auto.
  now rewrite (proj2 (proj2 rename_rename_PID)).
Qed.

Corollary rename_PID_upn :
  forall n σ from to, upn n (rename_PID_subst from to σ) =
                      rename_PID_subst from to (upn n σ).
Proof.
  induction n; intros; simpl; auto.
  now rewrite IHn, rename_PID_subst_up.
Qed.

Theorem split_rename_PID_subst :
     (forall e from to σ, rename_PID from to e.[σ] = 
       (rename_PID from to e).[rename_PID_subst from to σ])
  /\ (forall e from to σ, rename_PID_nval from to e.[σ]ₑ = 
       (rename_PID_nval from to e).[rename_PID_subst from to σ]ₑ)
  /\ (forall e from to σ, rename_PID_val from to e.[σ]ᵥ = 
       (rename_PID_val from to e).[rename_PID_subst from to σ]ᵥ).
Proof.
  eapply Exp_ind with
    (QV := fun l => Forall (fun e => forall from to σ, rename_PID_val from to e.[σ]ᵥ = 
       (rename_PID_val from to e).[rename_PID_subst from to σ]ᵥ) l)
    (Q := fun l => Forall (fun e => forall from to σ, rename_PID from to e.[σ] = 
       (rename_PID from to e).[rename_PID_subst from to σ]) l)
    (RV := fun l => Forall (fun '(e1, e2) => forall from to σ, rename_PID_val from to e1.[σ]ᵥ = 
       (rename_PID_val from to e1).[rename_PID_subst from to σ]ᵥ /\
         rename_PID_val from to e2.[σ]ᵥ = 
       (rename_PID_val from to e2).[rename_PID_subst from to σ]ᵥ) l)
    (R := fun l => Forall (fun '(e1, e2) => forall from to σ, rename_PID from to e1.[σ] = 
       (rename_PID from to e1).[rename_PID_subst from to σ] /\
         rename_PID from to e2.[σ] = 
       (rename_PID from to e2).[rename_PID_subst from to σ]) l)
    (W := fun l => Forall (fun '(p, g, e) => forall from to σ,
       rename_PID from to g.[σ] =
       (rename_PID from to g).[(rename_PID_subst from to σ)] /\
       rename_PID from to e.[σ] = 
       (rename_PID from to e).[(rename_PID_subst from to σ)]) l)
    (Z := fun l => Forall (fun '(n, e) => forall from to σ, rename_PID from to e.[σ] = 
       (rename_PID from to e).[(rename_PID_subst from to σ)]) l)
   (VV := fun l => Forall
      (fun '(id, vl, e) => forall from to σ, rename_PID from to e.[σ] = 
       (rename_PID from to e).[(rename_PID_subst from to σ)]) l)
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
  * unfold rename_PID_subst. now destruct σ.
  * unfold rename_PID_subst. destruct n. now destruct σ.
  * f_equal.
    - do 2 rewrite map_map. apply map_ext_Forall.
      rewrite Forall_nth in *. intros. eapply (H _ d) in H1. destruct nth, p.
      rewrite H1. now rewrite map_length, rename_PID_upn.
    - rewrite map_length. now rewrite H0, rename_PID_upn.
  * now rewrite H, rename_PID_upn.
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
      rewrite (proj1 (H1 _ _ _)), (proj2 (H1 _ _ _)). now rewrite rename_PID_upn.
  * rewrite H, H0. now rewrite rename_PID_upn.
  * now rewrite H, H0.
  * f_equal.
    - do 2 rewrite map_map. apply map_ext_Forall.
      rewrite Forall_nth in *. intros. eapply (H0 _ d) in H1. destruct nth.
      rewrite (H1 _ _ _). now rewrite rename_PID_upn, map_length.
    - rewrite H. now rewrite map_length, rename_PID_upn.
  * rewrite H, H0, H1. now repeat rewrite rename_PID_upn.
Qed.

Corollary split_rename_PID_subst_exp :
  (forall e from to σ, rename_PID from to e.[σ] = 
    (rename_PID from to e).[rename_PID_subst from to σ]).
Proof.
  apply split_rename_PID_subst.
Qed.

Corollary split_rename_PID_subst_val :
  (forall e from to σ, rename_PID_val from to e.[σ]ᵥ = 
       (rename_PID_val from to e).[rename_PID_subst from to σ]ᵥ).
Proof.
  apply split_rename_PID_subst.
Qed.

Proposition rename_PID_subst_id :
  forall from to, rename_PID_subst from to idsubst = idsubst.
Proof.
  now intros.
Qed.

Proposition rename_PID_subst_list_subst :
  forall vs from to σ,
    rename_PID_subst from to (list_subst vs σ) =
    list_subst (map (rename_PID_val from to) vs) (rename_PID_subst from to σ).
Proof.
  induction vs; simpl; intros; auto.
  rewrite <- IHvs. clear. unfold scons, rename_PID_subst.
  extensionality x. destruct x; auto.
Qed.

Proposition rename_subst_flatten_list :
  forall el from to, 
    map (rename_PID from to) (flatten_list el) =
    flatten_list (map (fun '(x, y) => (rename_PID from to x, rename_PID from to y)) el).
Proof.
  induction el using list_length_ind; destruct el; intros; simpl; auto.
  destruct p. simpl. do 2 f_equal. rewrite H. reflexivity. slia.
Qed.

Proposition rename_subst_deflatten_list_val :
  forall el from to, 
    map (fun '(x, y) => (rename_PID_val from to x, rename_PID_val from to y)) (deflatten_list el) =
    deflatten_list (map (rename_PID_val from to) el).
Proof.
  induction el using list_length_ind; destruct el; intros; simpl; auto.
  destruct el; auto. simpl.
  do 2 f_equal. rewrite H. reflexivity. slia.
Qed.

Proposition rename_PID_match_pattern :
  forall p v vs', match_pattern p v = Some vs' ->
    forall from to,
      match_pattern p (rename_PID_val from to v) = Some (map (rename_PID_val from to) vs').
Proof.
  induction p using Pat_ind2
    with (Q := fun l => Forall (fun p => forall v vs', match_pattern p v = Some vs' ->
    forall from to,
      match_pattern p (rename_PID_val from to v) = Some (map (rename_PID_val from to) vs')) l)
      (R := fun l => Forall (PBoth (fun p => forall v vs', match_pattern p v = Some vs' ->
    forall from to,
      match_pattern p (rename_PID_val from to v) = Some (map (rename_PID_val from to) vs'))) l); try destruct v; simpl; intros; try inv H; simpl; auto.
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

Proposition rename_PID_nomatch_pattern :
  forall p v, match_pattern p v = None ->
    forall from to,
      match_pattern p (rename_PID_val from to v) = None.
Proof.
  induction p using Pat_ind2
    with (Q := fun l => Forall (fun p => forall v, match_pattern p v = None ->
    forall from to,
      match_pattern p (rename_PID_val from to v) = None) l)
      (R := fun l => Forall (PBoth (fun p => forall v, match_pattern p v = None ->
    forall from to,
      match_pattern p (rename_PID_val from to v) = None)) l); try destruct v; simpl; intros; try now (inv H; simpl; auto).
  all: try now break_match_goal; auto; break_match_hyp; congruence.
  * repeat break_match_hyp; try congruence; inv H.
    - eapply rename_PID_match_pattern in Heqo. eapply IHp2 in Heqo0.
      now rewrite Heqo, Heqo0.
    - eapply IHp1 in Heqo. now rewrite Heqo.
  * generalize dependent l0. induction IHp; intros.
    - destruct l0; now inv H.
    - destruct l0; inv H0. now simpl.
      simpl. break_match_hyp.
      + eapply rename_PID_match_pattern in Heqo. rewrite Heqo. break_match_hyp. congruence.
        apply IHIHp in Heqo0. now rewrite Heqo0.
      + eapply H in Heqo. now rewrite Heqo.
  * generalize dependent l0. induction IHp; intros.
    - destruct l0; now inv H.
    - destruct x; cbn in *. destruct l0; inv H0. now simpl. destruct H as [H_1 H_2].
      destruct p1. simpl in *.
      break_match_hyp. break_match_hyp. break_match_hyp. congruence.
      + eapply rename_PID_match_pattern in Heqo. rewrite Heqo.
        eapply rename_PID_match_pattern in Heqo0. rewrite Heqo0.
        apply IHIHp in Heqo1. now rewrite Heqo1.
      + eapply rename_PID_match_pattern in Heqo. rewrite Heqo.
        eapply H_2 in Heqo0. now rewrite Heqo0.
      + eapply H_1 in Heqo. now rewrite Heqo.
  * constructor; auto.
  * constructor; auto.
  * constructor; auto.
  * constructor; auto.
Qed.

Corollary rename_PID_match_pattern_list :
  forall lp vs vs', match_pattern_list lp vs = Some vs' ->
    forall from to,
      match_pattern_list lp (map (rename_PID_val from to) vs) = Some (map (rename_PID_val from to) vs').
Proof.
  induction lp; destruct vs; simpl; intros; try congruence.
  * now inv H.
  * break_match_hyp. 2: congruence. break_match_hyp. 2: congruence.
    eapply rename_PID_match_pattern in Heqo. rewrite Heqo. inv H.
    eapply IHlp in Heqo0. rewrite Heqo0. now rewrite map_app.
Qed.

Corollary rename_PID_nomatch_pattern_list :
  forall lp vs, match_pattern_list lp vs = None ->
    forall from to,
      match_pattern_list lp (map (rename_PID_val from to) vs) = None.
Proof.
  induction lp; destruct vs; simpl; intros; try congruence.
  break_match_hyp. break_match_hyp. congruence.
  * eapply IHlp in Heqo0. eapply rename_PID_match_pattern in Heqo.
    now rewrite Heqo, Heqo0.
  * eapply rename_PID_nomatch_pattern in Heqo. now rewrite Heqo.
Qed.

Proposition rename_PID_Val_eqb :
  forall v v' from to, v =ᵥ v' = rename_PID_val from to v =ᵥ rename_PID_val from to v'.
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

Proposition rename_PID_Val_ltb :
  forall v v' from to, v <ᵥ v' = rename_PID_val from to v <ᵥ rename_PID_val from to v'.
Proof.
  valinduction; try destruct v'; intros; simpl; auto.
  all: try now destruct Nat.eqb eqn:P.
  * repeat break_match_goal; auto.
  * erewrite IHv1, IHv2.
    break_match_goal; erewrite rename_PID_Val_eqb in Heqb; now rewrite Heqb.
  * revert l0. induction IHv; destruct l0; simpl; auto.
    break_match_goal; erewrite rename_PID_Val_eqb in Heqb; rewrite Heqb; specialize (IHIHv l0).
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
    break_match_goal; erewrite rename_PID_Val_eqb in Heqb; rewrite Heqb; specialize (IHIHv l0); simpl in *.
    all: repeat rewrite map_length in *.
    - rewrite Bool.orb_lazy_alt, Bool.andb_lazy_alt in IHIHv.
      repeat break_match_hyp; auto.
      + apply Nat.ltb_lt, Arith_prebase.lt_n_S_stt, Nat.ltb_lt in Heqb0.
        rewrite Heqb0. auto.
      + apply Nat.ltb_nlt in Heqb0.
        assert (~S (length l) < S (length l0)) by lia.
        apply Nat.ltb_nlt in H1. rewrite H1. simpl. admit. (* TODO Technical *)
    - rewrite Bool.orb_lazy_alt, Bool.andb_lazy_alt in IHIHv.
      repeat break_match_hyp; auto.
      + apply Nat.ltb_lt, Arith_prebase.lt_n_S_stt, Nat.ltb_lt in Heqb0.
        rewrite Heqb0. auto.
      + apply Nat.ltb_nlt in Heqb0.
        assert (~S (length l) < S (length l0)) by lia.
        apply Nat.ltb_nlt in H1. rewrite H1. simpl.
        erewrite H, H0. admit. (* TODO Technical *)
Admitted.

Lemma rename_PID_make_val_map :
  forall vs from to,
  map (fun '(x, y) => (rename_PID_val from to x, rename_PID_val from to y))
         (make_val_map vs) =
  make_val_map (map (fun '(x, y) => (rename_PID_val from to x, rename_PID_val from to y))
         vs).
Proof.
  induction vs; intros; simpl; auto.
  destruct a. specialize (IHvs from to).
  rewrite <- IHvs. clear IHvs.
  (* map_insert *)
  remember (make_val_map vs) as vl. clear Heqvl vs.
  revert v v0 from to.
  induction vl; intros; simpl; auto.
  destruct a. erewrite (rename_PID_Val_eqb _ _ from to), (rename_PID_Val_ltb _ _ from to).
  repeat break_match_goal; simpl; eauto.
  now rewrite IHvl.
Qed.

Proposition rename_PID_eval :
  forall m f vs eff r eff',
    eval m f vs eff = Some (r, eff') ->
    forall from to,
      eval m f (map (rename_PID_val from to) vs) eff =
        Some (rename_PID_red from to r, map (fun '(a, b) => (a, map )) eff').
Proof.
  intros. unfold eval in *.
  break_match_hyp; unfold eval_arith, eval_logical, eval_equality,
  eval_transform_list, eval_list_tuple, eval_cmp, eval_io,
  eval_hd_tl, eval_elem_tuple, eval_check, eval_error, eval_concurrent, eval_funinfo in *; try rewrite Heqb in *; try invSome; clear Heqb.
  (* eval_arith *)
  46: { reflexivity. }
  27-28: shelve.
  all: try rewrite map_length.
  all: destruct vs; cbn in *; repeat invSome; auto.
  1-9,27-33,40: destruct v; cbn in *; repeat invSome; auto.
  all: try match goal with
  | [|- context G [if ?from =? ?p then _ else _]] => destruct (from =? p) eqn:EQ
  end.
  all: destruct vs; cbn in *; repeat invSome; try rewrite EQ; auto.
  (* fragile *)
  all: try destruct vs; cbn in *; repeat invSome; try rewrite EQ; auto.
  all: try destruct l; cbn in *; repeat invSome; auto.
  all: try destruct v; cbn in *; repeat invSome; auto.
  all: try match goal with
  | [|- context G [if ?from =? ?p then _ else _]] => destruct (from =? p) eqn:EQ
  end; try reflexivity.
  all: try destruct l; cbn in *; repeat invSome; auto.
  all: try destruct vs; cbn in *; repeat invSome; try rewrite EQ; auto.
Admitted.

Proposition rename_PID_primop_eval :
  forall f vs eff r eff',
    primop_eval f vs eff = Some (r, eff') ->
    forall from to,
      primop_eval f (map (rename_PID_val from to) vs) eff = Some (rename_PID_red from to r, eff').
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

Corollary rename_PID_create_result :
  forall vs ident eff r eff',
    create_result ident vs eff = Some (r, eff') ->
    forall from to, create_result (rename_PID_frameId from to ident)
                                  (map (rename_PID_val from to) vs) eff =
                                  Some (rename_PID_red from to r, eff').
Proof.
  intros. destruct ident; simpl in *.
  * now inv H.
  * now inv H.
  * inv H. cbn.
    now rewrite <- rename_subst_deflatten_list_val, rename_PID_make_val_map.
  * destruct m, f; simpl in *; inv H; auto.
    all: try destruct l; try destruct l0; try inv H1; auto.
    2-14: destruct (from =? p) eqn:P; cbn; now try rewrite P.
    now apply rename_PID_eval.
  * now apply rename_PID_primop_eval.
  * rewrite map_length.
    destruct v; simpl. all: try now inv H.
    - destruct Nat.eqb eqn:P; inv H; cbn; now rewrite P.
    - break_match_hyp; try now inv H.
      inv H. simpl. rewrite split_rename_PID_subst_exp, rename_PID_subst_list_subst.
      unfold convert_to_closlist. repeat f_equal.
      rewrite map_map, map_app. f_equal. rewrite map_map.
      f_equal. extensionality x. destruct x, p. cbn. f_equal.
Qed.

Theorem rename_PID_is_preserved :
  forall fs r fs' r', ⟨fs, r⟩ --> ⟨fs', r'⟩ ->
    forall from to,
      ⟨rename_PID_stack from to fs, rename_PID_red from to r⟩ -->
      ⟨rename_PID_stack from to fs', rename_PID_red from to r'⟩.
Proof.
  intros. inv H; cbn; try now constructor.
  * constructor. now apply rename_PID_preserves_scope.
  * rewrite map_app. constructor.
  * constructor. destruct ident; cbn; congruence.
  * econstructor.
    - destruct ident; cbn; congruence.
    - apply eq_sym, rename_PID_create_result. symmetry. eassumption.
  * econstructor.
    - replace (map (rename_PID_val from to) vl ++ [rename_PID_val from to v]) with
              (map (rename_PID_val from to) (vl ++ [v])) by now rewrite map_app.
      apply eq_sym, rename_PID_create_result. symmetry. eassumption.
  * rewrite rename_subst_flatten_list. constructor.
  * rewrite split_rename_PID_subst_exp,
            rename_PID_subst_list_subst,
            rename_PID_subst_id.
    constructor. now rewrite map_length.
  * repeat rewrite split_rename_PID_subst_exp,
                   rename_PID_subst_list_subst,
                   rename_PID_subst_id.
    constructor. now apply rename_PID_match_pattern_list.
  * econstructor. now apply rename_PID_nomatch_pattern_list.
  * rewrite split_rename_PID_subst_exp,
            rename_PID_subst_list_subst,
            rename_PID_subst_id.
    constructor.
    unfold convert_to_closlist. repeat rewrite map_map. f_equal.
    extensionality x. destruct x. simpl. rewrite map_map. do 2 f_equal.
    extensionality x. now destruct x.
  * rewrite split_rename_PID_subst_exp,
            rename_PID_subst_list_subst,
            rename_PID_subst_id.
    constructor. now rewrite map_length.
  * rewrite split_rename_PID_subst_exp.
    pose proof (rename_PID_subst_list_subst [exclass_to_value class; reason; details]).
    simpl in H. rewrite H.
    destruct class; cbn; constructor.
  * destruct exc, p. constructor.
    destruct F; auto.
Qed.

