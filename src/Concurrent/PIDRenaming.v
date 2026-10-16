(**
  This file defines the (sequential) renaming of process identifiers to reason
  about alpha-equivalence of Core Erlang nodes.
*)

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
 | VBitstring bits => VBitstring bits
end
with renamePIDNVal (from to : PID) (n : NonVal) : NonVal :=
match n with
 | EFun vl e => EFun vl (renamePID from to e)
 | EValues el => EValues (map (renamePID from to) el)
 | ECons hd tl => ECons (renamePID from to hd) (renamePID from to tl)
 | ETuple l => ETuple (map (renamePID from to) l)
 | EMap l => EMap (map (prod_map (renamePID from to) (renamePID from to)) l)
 | ECall m f l => ECall (renamePID from to m) (renamePID from to f) (map (renamePID from to) l)
 | EPrimOp f l => EPrimOp f (map (renamePID from to) l)
 | EApp exp l => EApp (renamePID from to exp) (map (renamePID from to) l)
 | ECase e l => ECase (renamePID from to e)
                      (map (fun '(p, g, e) => (map (renamePIDPat from to) p, renamePID from to g, renamePID from to e)) l)
 | ELet l e1 e2 => ELet l (renamePID from to e1) (renamePID from to e2)
 | ESeq e1 e2 => ESeq (renamePID from to e1) (renamePID from to e2)
 | ELetRec l e => ELetRec (map (fun '(vl, e) => (vl, renamePID from to e)) l)
                          (renamePID from to e)
 | ETry e1 vl1 e2 vl2 e3 => ETry (renamePID from to e1)
                                 vl1 (renamePID from to e2)
                                 vl2 (renamePID from to e3)
 | EBin l => EBin (map (renamePID from to) l)
 | ESeg (Build_Segment v s u t sgn endi) =>
    ESeg {| val := renamePID from to v; Syntax.size := renamePID from to s;
            type := t; unit := u; sign := sgn; endian := endi |}
end
with renamePIDPat (from to : PID) (p : Pat) : Pat :=
match p with
 | PVar => PVar
 | PLit l => PLit l
 | PCons hd tl => PCons (renamePIDPat from to hd) (renamePIDPat from to tl)
 | PTuple l => PTuple (map (renamePIDPat from to) l)
 | PMap l => PMap (map (prod_map (renamePIDPat from to) (renamePIDPat from to)) l)
 | PNil => PNil
 | PBin segments =>
   PBin (map (fun seg => {| val := renamePIDPat from to (val seg);
                            Syntax.size := renamePIDVal from to (Syntax.size seg);
                            unit := unit seg;
                            type := type seg;
                            sign := sign seg;
                            endian := endian seg |}) segments)
end.

Notation "e .⟦ x ↦ y ⟧" := (renamePID x y e) (at level 1, left associativity).
Notation "e .⟦ x ↦ y ⟧ᵥ" := (renamePIDVal x y e) (at level 1, left associativity).
Notation "e .⟦ x ↦ y ⟧ₙ" := (renamePIDNVal x y e) (at level 1, left associativity).

Definition renamePIDRed (from to : PID) (r : Redex) : Redex :=
match r with
 | RExp e => RExp (renamePID from to e)
 | RValSeq vs => RValSeq (map (renamePIDVal from to) vs)
 | RExc (class, reas, det) => RExc (class, renamePIDVal from to reas,
                                           renamePIDVal from to det)
 | RBox => RBox
end.

Notation "e .⟦ x ↦ y ⟧ᵣ" := (renamePIDRed x y e) (at level 1, left associativity).

Definition renamePIDFrameId (from to : PID) (f : FrameIdent) : FrameIdent :=
match f with
 | IValues => f
 | ITuple => f
 | IMap => f
 | ICall m f => ICall (renamePIDVal from to m) (renamePIDVal from to f)
 | IPrimOp f => IPrimOp f
 | IApp v => IApp (renamePIDVal from to v)
 | IBin => f
end.

Notation "e .⟦ x ↦ y ⟧ᵢ" := (renamePIDFrameId x y e) (at level 1, left associativity).

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
 | FCase1 l => FCase1 (map (fun '(p, g, e) => (map (renamePIDPat from to) p, renamePID from to g, renamePID from to e)) l)
 | FCase2 lv ex le =>
   FCase2
     (map (renamePIDVal from to) lv)
     (renamePID from to ex)
     (map (fun '(p, g, e) => (map (renamePIDPat from to) p, renamePID from to g, renamePID from to e)) le)
 | FLet l e => FLet l (renamePID from to e)
 | FSeq e => FSeq (renamePID from to e)
 | FTry vl1 e2 vl2 e3 => FTry vl1 (renamePID from to e2)
                              vl2 (renamePID from to e3)
 | FSeg1 size unit type sign endi => FSeg1 (renamePID from to size) unit type sign endi
 | FSeg2 val unit type sign endi => FSeg2 (renamePIDVal from to val) unit type sign endi
end.

Notation "e .⟦ x ↦ y ⟧ₖ" := (renamePIDFrame x y e) (at level 1, left associativity).

Definition renamePIDStack (from to : PID) (fs : FrameStack) :=
  map (renamePIDFrame from to) fs.

Notation "e .⟦ x ↦ y ⟧ₛₜ" := (renamePIDStack x y e) (at level 1,left associativity).

Lemma PatVars_renamePID : forall p from to, PatVars (renamePIDPat from to p) = PatVars p.
Proof.
  intros p from to.
  induction p using Pat_ind_weakened with
    (Q := fun l => Forall (fun p => PatVars (renamePIDPat from to p) = PatVars p) l)
    (R := fun l => Forall (PBoth (fun p => PatVars (renamePIDPat from to p) = PatVars p)) l)
    (T := fun l => Forall (fun seg => PatVars (renamePIDPat from to (val seg)) = PatVars (val seg)) l);
  simpl; auto.
  * induction l; simpl; auto. inversion IHp; subst. rewrite H1. f_equal. auto.
  * induction l; simpl; auto. inversion IHp; subst. destruct H1 as [H1a H1b]. destruct a. simpl in *. rewrite H1a, H1b. f_equal. auto.
  * induction l; simpl; auto. inversion IHp; subst. destruct a; simpl in *. rewrite H1. f_equal. auto.
Qed.

Corollary PatListVars_renamePID : forall l from to,
  PatListVars (map (renamePIDPat from to) l) = PatListVars l.
Proof.
  induction l; intros; simpl; auto.
  unfold PatListVars in *; simpl. rewrite PatVars_renamePID, IHl. reflexivity.
Qed.

Lemma renamePID_preserves_scope :
  (forall Γ e, EXP Γ ⊢ e -> forall from to, EXP Γ ⊢ renamePID from to e) /\
  (forall Γ v, VAL Γ ⊢ v -> forall from to, VAL Γ ⊢ renamePIDVal from to v) /\
  (forall Γ e, NVAL Γ ⊢ e -> forall from to, NVAL Γ ⊢ renamePIDNVal from to e) /\
  (forall Γ p, PAT Γ ⊢ p -> forall from to, PAT Γ ⊢ renamePIDPat from to p).
Proof.
  apply scoped_ind; intros; cbn; try now constructor.
  * break_match_goal; constructor.
  * constructor. intros.
    rewrite map_nth with (d := VNil).
    rewrite length_map in H0. eapply H in H0.
    eassumption.
  * constructor; intros.
    - rewrite map_map.
      rewrite map_nth with (d := (VNil, VNil)).
      rewrite length_map in H1. eapply H in H1.
      rewrite map_nth with (d := (VNil, VNil)) in H1.
      destruct nth. eassumption.
    - rewrite map_map.
      rewrite map_nth with (d := (VNil, VNil)).
      rewrite length_map in H1. eapply H0 in H1.
      rewrite map_nth with (d := (VNil, VNil)) in H1.
      destruct nth. eassumption.
  * constructor; intros.
    - do 2 rewrite map_map.
      do 2 rewrite map_nth with (d := (0, 0, ˝VNil)).
      rewrite length_map in H1. eapply H in H1.
      do 2 rewrite map_nth with (d := (0, 0, ˝VNil)) in H1.
      destruct nth, p. rewrite length_map. eassumption.
    - rewrite length_map. auto.
  * constructor. intros.
    rewrite map_nth with (d := ˝VNil).
    rewrite length_map in H0. eapply H in H0.
    eassumption.
  * constructor; intros.
    - rewrite map_map.
      rewrite map_nth with (d := (˝VNil, ˝VNil)).
      rewrite length_map in H1. eapply H in H1.
      rewrite map_nth with (d := (˝VNil, ˝VNil)) in H1.
      destruct nth. cbn in *. eassumption.
    - rewrite map_map.
      rewrite map_nth with (d := (˝VNil, ˝VNil)).
      rewrite length_map in H1. eapply H0 in H1.
      rewrite map_nth with (d := (˝VNil, ˝VNil)) in H1.
      destruct nth. cbn in *. eassumption.
  * constructor. intros.
    rewrite map_nth with (d := ˝VNil).
    rewrite length_map in H0. eapply H in H0.
    eassumption.
  * constructor; intros.
    - rewrite map_nth with (d := ˝VNil).
      rewrite length_map in H2. eapply H in H2.
      eassumption.
    - auto.
    - auto.
  * constructor. intros.
    rewrite map_nth with (d := ˝VNil).
    rewrite length_map in H0. eapply H in H0.
    eassumption.
  * constructor; intros.
    - auto.
    - rewrite map_nth with (d := ˝VNil).
      rewrite length_map in H1. eapply H0 in H1.
      eassumption.
  * constructor; intros.
    - auto.
    - (* guards *)
      do 2 rewrite map_map.
      rewrite length_map in H3.
      specialize (H0 i H3 from to).
      do 2 rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
      setoid_rewrite map_nth with (d := ([], ˝VNil, ˝VNil)) in H0.
      destruct (nth i l ([], ˝VNil, ˝VNil)) as [[ps g] b]. cbn in *.
      rewrite PatListVars_renamePID. exact H0.
    - (* bodies *)
      do 2 rewrite map_map.
      rewrite length_map in H3.
      specialize (H1 i H3 from to).
      do 2 rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
      setoid_rewrite map_nth with (d := ([], ˝VNil, ˝VNil)) in H1.
      destruct (nth i l ([], ˝VNil, ˝VNil)) as [[ps g] b]. cbn in *.
      rewrite PatListVars_renamePID. exact H1.
    - (* patterns *)
      rewrite map_map in H4. rewrite map_map.
      rewrite length_map in H3.
      rewrite map_nth with (d := ([], ˝VNil, ˝VNil)) in H4.
      rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
      setoid_rewrite map_nth with (d := ([], ˝VNil, ˝VNil)) in H2.
      destruct (nth i l ([], ˝VNil, ˝VNil)) as [[ps g] b] eqn:E. cbn in *.
      rewrite length_map in H4.
      rewrite map_nth with (d := PNil).
      specialize (H2 i H3). rewrite E in H2. cbn in H2.
      eapply H2; eauto.
  * constructor; intros.
    - do 2 rewrite map_map.
      rewrite length_map in *. eapply H in H1.
      do 2 rewrite map_nth with (d := (0, ˝VNil)).
      do 2 rewrite map_nth with (d := (0, ˝VNil)) in H1.
      destruct nth. cbn in *. eassumption.
    - rewrite length_map. apply H0.
  * (* EBin *)
    constructor; intros. rewrite map_nth with (d := ˝VNil).
    rewrite length_map in H0. now apply H.
  * (* ESeg *)
    destruct seg as [v s u t sg en]. simpl in *. constructor; simpl; auto.
  * (* PTuple *)
    constructor. intros. rewrite length_map in H0.
    rewrite map_nth with (d := PNil). now apply H.
  * (* PMap *)
    constructor; intros.
    - rewrite map_map.
      rewrite map_nth with (d := (PNil, PNil)).
      rewrite length_map in H1. eapply H in H1.
      rewrite map_nth with (d := (PNil, PNil)) in H1.
      destruct nth. cbn in *. eassumption.
    - rewrite map_map.
      rewrite map_nth with (d := (PNil, PNil)).
      rewrite length_map in H1. eapply H0 in H1.
      rewrite map_nth with (d := (PNil, PNil)) in H1.
      destruct nth. cbn in *. eassumption.
  * (* PBin *)
    constructor; intros.
    - rewrite map_map. rewrite length_map in H1.
      rewrite map_nth with (d := default_segment).
      cbn. specialize (H i H1 from to).
      setoid_rewrite (map_nth val) with (d := default_segment) in H.
      now cbn in H.
    - rewrite map_map. rewrite length_map in H1.
      rewrite map_nth with (d := default_segment).
      cbn. specialize (H0 i H1 from to).
      setoid_rewrite map_nth with (d := default_segment) in H0.
      now cbn in H0.
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
                      renamePIDVal from to (renameVal ρ e)) /\
  (forall p ρ from to, renamePat ρ (renamePIDPat from to p) =
                      renamePIDPat from to (renamePat ρ p)).
Proof.
  eapply Exp_ind with
    (PQ := fun l => Forall (fun p => forall ρ from to, renamePat ρ (renamePIDPat from to p) =
                      renamePIDPat from to (renamePat ρ p)) l)
    (PR := fun l => Forall (fun '(p1, p2) => forall ρ from to, renamePat ρ (renamePIDPat from to p1) =
                      renamePIDPat from to (renamePat ρ p1) /\
         renamePat ρ (renamePIDPat from to p2) =
                      renamePIDPat from to (renamePat ρ p2)) l)
    (PT := fun l => Forall (fun seg => forall ρ from to, renamePat ρ (renamePIDPat from to (val seg)) =
                      renamePIDPat from to (renamePat ρ (val seg)) /\
         renameVal ρ (renamePIDVal from to (Syntax.size seg)) =
                      renamePIDVal from to (renameVal ρ (Syntax.size seg))) l)
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
       map (renamePat ρ) (map (renamePIDPat from to) p) =
                      map (renamePIDPat from to) (map (renamePat ρ) p) /\
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
    specialize (H ρ from to) as [H_1 H_2]. cbn. now rewrite H_1, H_2.
  * now destruct n.
  * f_equal.
    - do 2 rewrite map_map. apply map_ext_Forall.
      rewrite List.Forall_nth in *. intros. eapply (H _ d) in H1. destruct nth, p.
      rewrite H1. now rewrite length_map.
    - rewrite length_map. now rewrite H0.
  * now rewrite H.
  * f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto.
  * now rewrite H, H0.
  * f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto.
  * f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto. destruct x.
    specialize (H from to ρ) as [H_1 H_2]. cbn. now rewrite H_1, H_2.
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
      rewrite List.Forall_nth in *. intros. eapply (H0 _ d) in H1.
      destruct (nth i l d) as [[ps g] b]. cbn.
      destruct (H1 from to ρ) as [Hp _].
      destruct (H1 from to (uprenn (PatListVars ps) ρ)) as [_ [Hg Hb]].
      rewrite PatListVars_renamePID.
      rewrite Hp, Hg, Hb. reflexivity.
  * now rewrite H, H0.
  * now rewrite H, H0.
  * f_equal.
    - do 2 rewrite map_map. apply map_ext_Forall.
      rewrite List.Forall_nth in *. intros. eapply (H0 _ d) in H1. destruct nth.
      rewrite (H1 _ _ _). now rewrite length_map.
    - rewrite H. now rewrite length_map.
  * now rewrite H, H0, H1.
  * (* EBin *)
    f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto.
  * (* ESeg *)
    destruct seg as [v s u t sg en]. cbn in *. rewrite H, H0. reflexivity.
  * (* PCons *)
    now rewrite H, H0.
  * (* PTuple *)
    f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto.
  * (* PMap *)
    f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto. destruct x.
    specialize (H ρ from to) as [H_1 H_2]. cbn. now rewrite H_1, H_2.
  * (* PBin *)
    f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto.
    destruct x as [v s u t sg en]. specialize (H ρ from to) as [H_1 H_2]. cbn in *.
    now rewrite H_1, H_2.
  * (* clauses of ECase *)
    constructor; [|assumption].
    intros from to ρ. split; [|split]; [| apply H0 | apply H1].
    do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto.
Qed.

Lemma renamePID_subst_up :
  forall σ from to, up_subst (renamePID_subst from to σ) =
                    renamePID_subst from to (up_subst σ).
Proof.
  unfold renamePID_subst, up_subst. intros.
  extensionality x. destruct x; auto.
  unfold Manipulation.shift. destruct σ; auto.
  now rewrite (proj1 (proj2 (proj2 rename_renamePID))).
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
       (renamePIDVal from to e).[renamePID_subst from to σ]ᵥ)
  /\ (forall p from to σ, renamePIDPat from to p.[σ]ₚ =
       (renamePIDPat from to p).[renamePID_subst from to σ]ₚ).
Proof.
  eapply Exp_ind with
    (PQ := fun l => Forall (fun p => forall from to σ, renamePIDPat from to p.[σ]ₚ =
       (renamePIDPat from to p).[renamePID_subst from to σ]ₚ) l)
    (PR := fun l => Forall (fun '(p1, p2) => forall from to σ, renamePIDPat from to p1.[σ]ₚ =
       (renamePIDPat from to p1).[renamePID_subst from to σ]ₚ /\
         renamePIDPat from to p2.[σ]ₚ =
       (renamePIDPat from to p2).[renamePID_subst from to σ]ₚ) l)
    (PT := fun l => Forall (fun seg => forall from to σ, renamePIDPat from to (val seg).[σ]ₚ =
       (renamePIDPat from to (val seg)).[renamePID_subst from to σ]ₚ /\
         renamePIDVal from to (Syntax.size seg).[σ]ᵥ =
       (renamePIDVal from to (Syntax.size seg)).[renamePID_subst from to σ]ᵥ) l)
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
       map (renamePIDPat from to) (map (substPat σ) p) =
       map (substPat (renamePID_subst from to σ)) (map (renamePIDPat from to) p) /\
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
    specialize (H from to σ) as [H_1 H_2]. cbn. now rewrite H_1, H_2.
  * unfold renamePID_subst. now destruct σ.
  * unfold renamePID_subst. destruct n. now destruct σ.
  * f_equal.
    - do 2 rewrite map_map. apply map_ext_Forall.
      rewrite List.Forall_nth in *. intros. eapply (H _ d) in H1. destruct nth, p.
      rewrite H1. now rewrite length_map, renamePID_upn.
    - rewrite length_map. now rewrite H0, renamePID_upn.
  * now rewrite H, renamePID_upn.
  * f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto.
  * now rewrite H, H0.
  * f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto.
  * f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto. destruct x.
    specialize (H from to σ) as [H_1 H_2]. cbn. now rewrite H_1, H_2.
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
      destruct (H1 from to σ) as [Hp _].
      destruct (H1 from to (upn (PatListVars l0) σ)) as [_ [Hg Hb]].
      rewrite PatListVars_renamePID, renamePID_upn, Hp, Hg, Hb. reflexivity.
  * rewrite H, H0. now rewrite renamePID_upn.
  * now rewrite H, H0.
  * f_equal.
    - do 2 rewrite map_map. apply map_ext_Forall.
      rewrite List.Forall_nth in *. intros. eapply (H0 _ d) in H1. destruct nth.
      rewrite (H1 _ _ _). now rewrite renamePID_upn, length_map.
    - rewrite H. now rewrite length_map, renamePID_upn.
  * rewrite H, H0, H1. now repeat rewrite renamePID_upn.
  * (* EBin *)
    f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto.
  * (* ESeg *)
    destruct seg as [v s u t sg en]. cbn in *. rewrite H, H0. reflexivity.
  * (* PCons *)
    now rewrite H, H0.
  * (* PTuple *)
    f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto.
  * (* PMap *)
    f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto. destruct x.
    specialize (H from to σ) as [H_1 H_2]. cbn. now rewrite H_1, H_2.
  * (* PBin *)
    f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto.
    destruct x as [v s u t sg en]. specialize (H from to σ) as [H_1 H_2]. cbn in *.
    now rewrite H_1, H_2.
  * (* clauses of ECase *)
    constructor; [|assumption].
    intros from to σ. split; [|split]; [| apply H0 | apply H1].
    do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto.
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

Corollary split_renamePID_subst_nval :
  (forall e from to σ, renamePIDNVal from to e.[σ]ₑ = 
    (renamePIDNVal from to e).[renamePID_subst from to σ]ₑ).
Proof.
  apply split_renamePID_subst.
Qed.

Corollary split_renamePID_subst_pat :
  (forall p from to σ, renamePIDPat from to p.[σ]ₚ = 
       (renamePIDPat from to p).[renamePID_subst from to σ]ₚ).
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
    flatten_list (map (prod_map (renamePID from to) (renamePID from to)) el).
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

Instance FMap_Match : FMap Match :=
{  fmap {A B} (f : A -> B) m :=
     match m with
     | Matches x => Matches (f x)
     | NotMatches => NotMatches
     | NotSupported => NotSupported
     end;
}.

Lemma map_match_and_app : forall (f : Val -> Val) r1 r2,
  fmap (map f) (match_and (fun l1 l2 => l1 ++ l2) r1 r2) =
  match_and (fun l1 l2 => l1 ++ l2) (fmap (map f) r1) (fmap (map f) r2).
Proof.
  intros. destruct r1, r2; simpl; try reflexivity. now rewrite map_app.
Qed.

Lemma map_match_bind_id : forall (m : Match Val) (g : Val -> Match (list Val)) (f : list Val -> list Val),
  fmap f (bind_match m g) = bind_match m (fun x => fmap f (g x)).
Proof.
  intros. destruct m; reflexivity.
Qed.

(** Decoded segment values (integers, bitstrings) never contain PIDs. *)
Lemma decode_bits_pidfree : forall bits type unit sign endi dv,
  decode_bits bits type unit sign endi = Matches dv ->
  forall from to, renamePIDVal from to dv = dv.
Proof.
  unfold decode_bits. intros. destruct type; try discriminate;
    try (inv H; reflexivity).
  case_match; inv H; reflexivity.
Qed.

Lemma bind_decode_pidfree : forall p bits type unit sign endi from to,
  (forall v, match_pattern p (renamePIDVal from to v) =
             fmap (map (renamePIDVal from to)) (match_pattern p v)) ->
  fmap (map (renamePIDVal from to))
    (bind_match (decode_bits bits type unit sign endi) (match_pattern p)) =
  bind_match (decode_bits bits type unit sign endi) (match_pattern p).
Proof.
  intros p bits type unit sign endi from to Hp.
  rewrite map_match_bind_id.
  destruct (decode_bits bits type unit sign endi) eqn:E; try reflexivity.
  simpl. specialize (Hp v). erewrite decode_bits_pidfree in Hp; [|exact E].
  symmetry. exact Hp.
Qed.

(** Matching a bitstring never binds PIDs, so renaming the bindings is a no-op. *)
Lemma match_PBin_pidfree : forall l from to,
  Forall (fun seg => forall v, match_pattern (val seg) (renamePIDVal from to v) =
            fmap (map (renamePIDVal from to)) (match_pattern (val seg) v)) l ->
  forall bits,
    fmap (map (renamePIDVal from to)) (match_pattern (PBin l) (VBitstring bits)) =
    match_pattern (PBin l) (VBitstring bits).
Proof.
  intros l from to H. induction H; intros bits; simpl.
  * destruct (bvn_n bits =? 0)%N; reflexivity.
  * destruct x as [v s u t sg en]. simpl in *.
    destruct s; try reflexivity.
    destruct (null l && Lit_beq l0 "all"%string) eqn:Hb.
    - apply (bind_decode_pidfree v bits t (N.of_nat u) sg en from to H).
    - destruct l0 as [a|z]; [reflexivity|].
      destruct ((z <? 0)%Z || (bvn_n bits <? Z.to_N z * N.of_nat u)%N) eqn:Hc; [reflexivity|].
      rewrite map_match_and_app.
      rewrite (bind_decode_pidfree v _ t (N.of_nat u) sg en from to H).
      rewrite IHForall. reflexivity.
Qed.

Lemma renamePID_match_pattern_eq : forall p v from to,
  match_pattern p (renamePIDVal from to v) =
  fmap (map (renamePIDVal from to)) (match_pattern p v).
Proof.
  intros p. induction p using Pat_ind_weakened with
    (Q := Forall (fun p => forall v from to, match_pattern p (renamePIDVal from to v) =
            fmap (map (renamePIDVal from to)) (match_pattern p v)))
    (R := Forall (PBoth (fun p => forall v from to, match_pattern p (renamePIDVal from to v) =
            fmap (map (renamePIDVal from to)) (match_pattern p v))))
    (T := Forall (fun seg => forall v from to, match_pattern (val seg) (renamePIDVal from to v) =
            fmap (map (renamePIDVal from to)) (match_pattern (val seg) v))).
  all: try (intros v from to; destruct v; simpl; auto).
  all: try (destruct (from =? p); reflexivity).
  * destruct Lit_beq; reflexivity.
  * rewrite IHp1, IHp2, map_match_and_app. reflexivity.
  * revert l0. induction IHp; intros l0; destruct l0; simpl; try reflexivity.
    rewrite H, IHIHp, map_match_and_app. reflexivity.
  * revert l0. induction IHp; intros l0.
    - destruct l0 as [|[v1 v2] l0]; reflexivity.
    - destruct x as [p p0]; destruct H as [H_1 H_2]; simpl in H_1, H_2.
      destruct l0 as [|[v1 v2] l0]; simpl; [reflexivity|].
      rewrite H_1, H_2, IHIHp.
      rewrite map_match_and_app, map_match_and_app. reflexivity.
  * symmetry. apply (match_PBin_pidfree l from to).
    eapply Forall_impl; [exact IHp|]. intros seg Hseg v. apply Hseg.
  * constructor; auto.
  * constructor; auto.
  * constructor; auto.
  * constructor; auto.
  * constructor; auto.
  * constructor; auto.
Qed.

Proposition renamePID_match_pattern :
  forall p v vs', match_pattern p v = Matches vs' ->
    forall from to,
      match_pattern p (renamePIDVal from to v) = Matches (map (renamePIDVal from to) vs').
Proof.
  intros. rewrite renamePID_match_pattern_eq, H. reflexivity.
Qed.

Proposition renamePID_nomatch_pattern :
  forall p v, match_pattern p v = NotMatches ->
    forall from to,
      match_pattern p (renamePIDVal from to v) = NotMatches.
Proof.
  intros. rewrite renamePID_match_pattern_eq, H. reflexivity.
Qed.

Lemma renamePID_match_pattern_list_eq : forall lp vs from to,
  match_pattern_list lp (map (renamePIDVal from to) vs) =
  fmap (map (renamePIDVal from to)) (match_pattern_list lp vs).
Proof.
  induction lp; destruct vs; intros; simpl; try reflexivity.
  rewrite renamePID_match_pattern_eq.
  destruct (match_pattern a v) eqn:E1; simpl; try reflexivity.
  rewrite IHlp. destruct (match_pattern_list lp vs); simpl; try reflexivity.
  now rewrite map_app.
Qed.

Corollary renamePID_match_pattern_list :
  forall lp vs vs', match_pattern_list lp vs = Matches vs' ->
    forall from to,
      match_pattern_list lp (map (renamePIDVal from to) vs) = Matches (map (renamePIDVal from to) vs').
Proof.
  intros. rewrite renamePID_match_pattern_list_eq, H. reflexivity.
Qed.

Corollary renamePID_nomatch_pattern_list :
  forall lp vs, match_pattern_list lp vs = NotMatches ->
    forall from to,
      match_pattern_list lp (map (renamePIDVal from to) vs) = NotMatches.
Proof.
  intros. rewrite renamePID_match_pattern_list_eq, H. reflexivity.
Qed.

(** Renaming PIDs inside patterns (only the sizes of binary segments can
    contain values) does not influence matching: sizes only matter if they are
    literals, which are not changed by the renaming. *)
Lemma match_PBin_renamePIDPat : forall l from to,
  Forall (fun seg => forall v, match_pattern (renamePIDPat from to (val seg)) v =
                               match_pattern (val seg) v) l ->
  forall bits,
    match_pattern (renamePIDPat from to (PBin l)) (VBitstring bits) =
    match_pattern (PBin l) (VBitstring bits).
Proof.
  intros l from to H. induction H; intros bits; simpl.
  * reflexivity.
  * destruct x as [v s u t sg en]. simpl in *.
    destruct s; try reflexivity.
    all: try (simpl; destruct (from =? p); reflexivity).
    simpl. rewrite null_map.
    destruct (null l && Lit_beq l0 "all"%string) eqn:Hb.
    - destruct (decode_bits bits t (N.of_nat u) sg en) as [v0| |]; simpl; try rewrite H; reflexivity.
    - destruct l0 as [a|z]; [reflexivity|].
      destruct ((z <? 0)%Z || (bvn_n bits <? Z.to_N z * N.of_nat u)%N); [reflexivity|].
      rewrite IHForall.
      destruct (decode_bits (bv_extract (bvn_n bits - Z.to_N z * N.of_nat u) (Z.to_N z * N.of_nat u) (bvn_val bits)) t (N.of_nat u) sg en) as [v0| |];
        simpl; try rewrite H; reflexivity.
Qed.

Lemma renamePIDPat_match_pattern : forall p v from to,
  match_pattern (renamePIDPat from to p) v = match_pattern p v.
Proof.
  intros p. induction p using Pat_ind_weakened with
    (Q := Forall (fun p => forall v from to, match_pattern (renamePIDPat from to p) v = match_pattern p v))
    (R := Forall (PBoth (fun p => forall v from to, match_pattern (renamePIDPat from to p) v = match_pattern p v)))
    (T := Forall (fun seg => forall v from to, match_pattern (renamePIDPat from to (val seg)) v = match_pattern (val seg) v)).
  all: try (intros v from to; destruct v; simpl; auto).
  * rewrite IHp1, IHp2. reflexivity.
  * revert l0. induction IHp; intros l0; destruct l0; simpl; try reflexivity.
    rewrite H, IHIHp. reflexivity.
  * revert l0. induction IHp; intros l0.
    - destruct l0 as [|[v1 v2] l0]; reflexivity.
    - destruct x as [p p0]; destruct H as [H_1 H_2]; simpl in H_1, H_2.
      destruct l0 as [|[v1 v2] l0]; simpl; [reflexivity|].
      rewrite H_1, H_2, IHIHp. reflexivity.
  * apply match_PBin_renamePIDPat. eapply Forall_impl; [exact IHp|]. intros seg Hseg v. apply Hseg.
  * constructor; auto.
  * constructor; auto.
  * constructor; auto.
  * constructor; auto.
  * constructor; auto.
  * constructor; auto.
Qed.

Lemma renamePIDPat_match_pattern_list : forall lp vs from to,
  match_pattern_list (map (renamePIDPat from to) lp) vs = match_pattern_list lp vs.
Proof.
  induction lp; destruct vs; intros; simpl; try reflexivity.
  rewrite renamePIDPat_match_pattern, IHlp. reflexivity.
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
  * case_match; try reflexivity. congruence.
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
    all: repeat rewrite length_map in *.
    - rewrite Bool.orb_lazy_alt, Bool.andb_lazy_alt in IHIHv.
      repeat break_match_hyp; auto.
      + apply Nat.ltb_lt, Nat.succ_lt_mono, Nat.ltb_lt in Heqb0.
        rewrite Heqb0. auto.
      + apply Nat.ltb_nlt in Heqb0.
        assert (~S (length l) < S (length l0)) by lia.
        apply Nat.ltb_nlt in H0. rewrite H0. simpl. now rewrite IHIHv.
    - rewrite Bool.orb_lazy_alt, Bool.andb_lazy_alt in IHIHv.
      repeat break_match_hyp; auto.
      + apply Nat.ltb_lt, Nat.succ_lt_mono, Nat.ltb_lt in Heqb0.
        rewrite Heqb0. auto.
      + apply Nat.ltb_nlt in Heqb0.
        assert (~S (length l) < S (length l0)) by lia.
        apply Nat.ltb_nlt in H0. rewrite H0. simpl.
        apply H.
  * repeat rewrite length_map. do 3 f_equal. 2: f_equal.
    (* prove separately, by induction that list_equal and list_less are preserved *)
    {
      revert l0. induction IHv; intros; destruct l0; simpl.
      * reflexivity.
      * by destruct p.
      * by destruct x.
      * destruct p, x. inv H. simpl in *.
        rewrite <- H0.
        rewrite <- renamePID_Val_eqb_alt.
        rewrite IHIHv.
        reflexivity.
    }
    {
      revert l0. clear IHv. induction l; destruct l0; simpl.
      1-3: reflexivity.
      destruct a,p. simpl.
      by rewrite <- renamePID_Val_eqb_alt, IHl.
    }
    { (* basically the same as the 1st goal *)
      revert l0. induction IHv; intros; destruct l0; simpl.
      * reflexivity.
      * by destruct p.
      * by destruct x.
      * destruct p, x. inv H. simpl in *.
        rewrite <- H1.
        rewrite <- renamePID_Val_eqb_alt.
        rewrite IHIHv.
        reflexivity.
    }
Qed.

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
  all: repeat break_match_goal.
  all: try reflexivity.
  all: try erewrite (renamePID_Val_eqb_alt _ _ from to) in Heqb6;
       simpl in *; try congruence.
  all: try erewrite (renamePID_Val_eqb_alt _ _ from to) in Heqb5;
       simpl in *; try congruence.
  all: try erewrite (renamePID_Val_eqb_alt _ _ from to) in Heqb4;
       simpl in *; try congruence.
  all: try erewrite (renamePID_Val_eqb_alt _ _ from to) in Heqb3;
       simpl in *; try congruence.
  all: try erewrite (renamePID_Val_eqb_alt _ _ from to) in Heqb2;
       simpl in *; try congruence.
  all: try erewrite (renamePID_Val_eqb_alt _ _ from to) in Heqb1;
       simpl in *; try congruence.
  all: try erewrite (renamePID_Val_eqb_alt _ _ from to) in Heqb0;
       simpl in *; try congruence.
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
  all: destruct Val_eqb eqn:P; erewrite <- renamePID_Val_eqb_alt in P; rewrite P.
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
  all: destruct Val_ltb eqn:P; erewrite <- renamePID_Val_ltb in P; rewrite P.
  all: try reflexivity.
  all: simpl in *.
  all: destruct Val_eqb eqn:P0; erewrite <- renamePID_Val_eqb_alt in P0; rewrite P0.
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

Lemma renamePID_eval_bin_size :
  forall m f vs r,
    eval_bin_size m f vs = r ->
    forall from to,
      eval_bin_size m f (map (renamePIDVal from to) vs) = renamePIDRed from to r.
Proof.
  intros. unfold eval_bin_size in *.
  rewrite <- H. clear H.
  case_match; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  all: destruct v; simpl; try reflexivity.
  all: try (destruct (from =? p); reflexivity).
  all: try (repeat case_match; reflexivity).
Qed.

Lemma renamePID_meta_to_cons : forall l from to,
  renamePIDVal from to (meta_to_cons l) = meta_to_cons (map (renamePIDVal from to) l).
Proof.
  induction l; intros; simpl; auto. now rewrite IHl.
Qed.

Lemma renamePID_map_lit_integer : forall l from to,
  map (renamePIDVal from to) (map (VLit ∘ Integer) l) = map (VLit ∘ Integer) l.
Proof.
  induction l; intros; simpl; auto. now rewrite IHl.
Qed.

Lemma renamePID_eval_bin_to_list :
  forall m f vs r,
    eval_bin_to_list m f vs = r ->
    forall from to,
      eval_bin_to_list m f (map (renamePIDVal from to) vs) = renamePIDRed from to r.
Proof.
  intros. unfold eval_bin_to_list in *.
  rewrite <- H. clear H.
  case_match; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  all: destruct v; simpl; try reflexivity.
  all: try (destruct (from =? p); reflexivity).
  * destruct (_ =? 0)%N; simpl; [|reflexivity].
    now rewrite renamePID_meta_to_cons, renamePID_map_lit_integer.
  * rewrite renamePID_meta_to_cons, map_app, renamePID_map_lit_integer.
    destruct (_ =? 0)%N; reflexivity.
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
  by case_match; simpl.
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

Lemma renamePID_is_shallow_proper_list :
  forall v from to, is_shallow_proper_list v = is_shallow_proper_list (renamePIDVal from to v).
Proof.
  induction v; intros; simpl; try reflexivity.
  * by case_match.
  * by erewrite IHv2.
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
    generalize dependent v0. induction v; simpl; intros; auto.
    all: try destruct_eqb_in_if Heq; try reflexivity.
    rewrite IHv2. destruct eval_append; simpl; try reflexivity.
    * destruct vs; simpl; try reflexivity.
      destruct vs; try reflexivity.
    * destruct e, p. reflexivity.
  }
  {
    (* eval_subtract *)
    revert v0 from to v. induction v0; destruct v; simpl.
    all: try reflexivity.
    all: try destruct (Nat.eqb from p) eqn:P; eqb_to_eq; subst; simpl.
    all: try reflexivity.
    all: try destruct (Nat.eqb p p0) eqn:P1; eqb_to_eq; subst; simpl.
    all: try reflexivity.
    all: try destruct (Nat.eqb from p0) eqn:P2; eqb_to_eq; subst; simpl.
    all: try reflexivity.
    all: repeat rewrite andb_false_r; try reflexivity.
    3-4: simpl; try by rewrite Nat.eqb_refl.
    3: case_match; eqb_to_eq; subst; try reflexivity.
    3: congruence.
    all: repeat rewrite <- renamePID_is_shallow_proper_list.
    1: case_match; simpl; try reflexivity.
    1: simpl; by rewrite Nat.eqb_refl.
    1: case_match; simpl; try reflexivity.
    1: specialize (IHv0_2 from to VNil); simpl in *; by rewrite IHv0_2.
    (* inductive case *)
    case_match.
    2: reflexivity.
    repeat rewrite <- renamePID_Val_eqb_alt. case_match.
    1: by rewrite IHv0_2.
    simpl. rewrite <- IHv0_2. simpl.
    f_equal. f_equal.
    (* subtract_elem *)
    clear. revert v0_1. induction v2; intros; simpl; try reflexivity.
    * by case_match.
    * repeat rewrite <- renamePID_Val_eqb_alt. case_match. reflexivity.
      rewrite IHv2_2. by simpl.
  }
  {
    (* eval_split *)
    destruct v; simpl; try reflexivity.
    2: by case_match.
    destruct l. 2: case_match.
    1-2: reflexivity.
    remember (Z.to_nat _) as n.
    clear. revert v0. induction n; intros; simpl. reflexivity.
    destruct v0; simpl; try reflexivity.
    1: destruct Nat.eqb; reflexivity.
    destruct split_cons eqn:P.
    * destruct p. specialize (IHn v0_2). rewrite P in IHn.
      case_match. destruct p.
      all: by inv IHn.
    * specialize (IHn v0_2). rewrite P in IHn. case_match. destruct p.
      all: by inv IHn.
  }
Qed.

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
  all: remember (Nat.pred (Pos.to_nat p)) as n; clear Heqn.
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
  * destruct v; simpl; try reflexivity.
    break_match_goal; reflexivity.
    induction l; simpl; auto.
    inv IHl. now rewrite H0.
  * induction v; simpl; try reflexivity.
    destruct Nat.eqb; reflexivity.
    destruct v2; try reflexivity; simpl.
    1: destruct Nat.eqb; simpl; reflexivity.
    clear IHv1. simpl in IHv2.
    break_match_hyp; break_match_hyp; inv IHv2; try reflexivity.
Qed.

Lemma renamePID_mk_ascii_list :
  forall v from to,
    mk_ascii_list v = mk_ascii_list (renamePIDVal from to v).
Proof.
  intros. induction v; simpl; try reflexivity.
  * case_match; reflexivity.
  * rewrite IHv2. destruct v1; simpl; try reflexivity.
    destruct Nat.eqb; reflexivity.
Qed.

Lemma renamePID_string_to_vcons :
  forall s from to,
    renamePIDVal from to (string_to_vcons s) = string_to_vcons s.
Proof.
  induction s; intros; simpl.
  * reflexivity.
  * rewrite IHs; reflexivity.
Qed.

Lemma renamePID_convert_atom :
  forall m f vs r eff,
    eval_convert m f vs = (r, eff) ->
    forall from to,
      eval_convert m f (map (renamePIDVal from to) vs) =
      (renamePIDRed from to r, eff).
Proof.
  intros. unfold eval_convert in *.
  break_match_goal; inv H; try reflexivity; clear Heqb.
  all: destruct vs; simpl; try reflexivity.
  1,3: inv H1; cbn; reflexivity.
  all: destruct vs; simpl; try reflexivity.
  2,4: inv H1; cbn; reflexivity.
  * rewrite <- renamePID_mk_ascii_list.
    case_match; inv H1; cbn; reflexivity.
  * destruct v; simpl; inv H1; try reflexivity.
    - destruct l; simpl; inv H0; try reflexivity.
      simpl. by rewrite renamePID_string_to_vcons.
    - simpl. destruct (from =? p) eqn:P; try reflexivity.
Qed.

Lemma renamePID_convert_2 :
  forall m f vs r eff,
    eval_convert m f vs = (r, eff) ->
    forall from to,
      eval_convert m f (map (renamePIDVal from to) vs) =
      (renamePIDRed from to r, fmap (fun x => (fst x, map (renamePIDVal from to) (snd x))) eff).
Proof.
  intros. unfold eval_convert in *.
  break_match_goal; inv H; try reflexivity; clear Heqb.
  all: destruct vs; simpl; try reflexivity.
  1,3: inv H1; cbn; reflexivity.
  all: destruct vs; simpl; try reflexivity.
  2,4: inv H1; cbn; reflexivity.
  * rewrite <- renamePID_mk_ascii_list.
    case_match; inv H1; cbn; reflexivity.
  * destruct v; simpl; inv H1; try reflexivity.
    - destruct l; simpl; inv H0; try reflexivity.
      simpl. by rewrite renamePID_string_to_vcons.
    - simpl. destruct (from =? p) eqn:P; try reflexivity.
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
  * simpl. reflexivity.
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
  2: now rewrite length_map.
  all: now destruct Nat.eqb.
Qed.

Lemma renamePID_eval_io :
  forall m f vs r eff',
    eval_io m f vs = (r, eff') ->
    forall from to,
      eval_io m f (map (renamePIDVal from to) vs) =
        (renamePIDRed from to r, fmap (fun e => (fst e, map (renamePIDVal from to) (snd e))) eff').
Proof.
  intros. unfold eval_io in *. break_match_goal; inv H; clear Heqb; try reflexivity.
  all: rewrite length_map.
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

Lemma renamePID_eval_map_bifs :
  forall m f vs r,
    eval_map_bifs m f vs = r ->
    forall from to,
      eval_map_bifs m f (map (renamePIDVal from to) vs) = renamePIDRed from to r.
Proof.
  intros. unfold eval_map_bifs in *.
  rewrite <- H. clear H.
  case_match; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  2-3: destruct vs; simpl; try reflexivity.
  * destruct v0; try reflexivity.
    cbn. by destruct Nat.eqb eqn:P.
    simpl. induction l; simpl; try reflexivity.
    destruct a; simpl.
    repeat rewrite <- renamePID_Val_ltb. simpl.
    repeat rewrite <- renamePID_Val_eqb_alt.
    destruct (Val_ltb v0) eqn:P.
    - assumption.
    - destruct (Val_eqb v) eqn:P2; reflexivity.
  * destruct v0; try reflexivity.
    cbn. by destruct Nat.eqb eqn:P.
    simpl. induction l; simpl; try reflexivity.
    destruct a; simpl.
    repeat rewrite <- renamePID_Val_ltb. simpl.
    repeat rewrite <- renamePID_Val_eqb_alt.
    destruct (Val_ltb v0) eqn:P.
    - assumption.
    - destruct (Val_eqb v) eqn:P2; reflexivity.
  * destruct v1; try reflexivity.
    cbn. by destruct Nat.eqb eqn:P.
    simpl. repeat f_equal.
    induction l; simpl; try reflexivity.
    destruct a; simpl.
    repeat rewrite <- renamePID_Val_ltb. simpl.
    repeat rewrite <- renamePID_Val_eqb_alt.
    destruct (Val_ltb v) eqn:P.
    - repeat f_equal.
    - destruct (Val_eqb v) eqn:P2; repeat f_equal.
      cbn. f_equal. apply IHl.
Qed.

Proposition renamePID_eval :
  forall m f vs r eff',
    eval m f vs = Some (r, eff') ->
    forall from to,
      eval m f (map (renamePIDVal from to) vs) =
        Some (renamePIDRed from to r, fmap (fun e => (fst e, map (renamePIDVal from to) (snd e))) eff').
Proof.
  intros. unfold eval in *.
  break_match_hyp; try rewrite Heqb in *; inv H.
  all:
    try (erewrite renamePID_eval_arith; reflexivity);
    try (erewrite renamePID_eval_list_atom; reflexivity);
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
    try (erewrite renamePID_eval_check; reflexivity);
    try (erewrite renamePID_eval_bin_size; reflexivity);
    try (erewrite renamePID_eval_bin_to_list; reflexivity).
  1-2: erewrite renamePID_eval_io; try eassumption; reflexivity.
  1-2: erewrite renamePID_convert_2; try eassumption; reflexivity.
  1-3: break_match_hyp; try congruence; destruct e, p;
       eapply renamePID_eval_error in Heqo; rewrite Heqo; inv H1; reflexivity.
  1-7: break_match_hyp; try congruence; destruct e, p;
       eapply renamePID_eval_concurrent in Heqo; rewrite Heqo; inv H1; reflexivity.
  reflexivity.
  1-2: erewrite renamePID_eval_map_bifs; try eassumption; reflexivity.
Qed.

Proposition renamePID_primop_eval :
  forall f vs r eff',
    primop_eval f vs = Some (r, eff') ->
    forall from to,
      primop_eval f (map (renamePIDVal from to) vs) = Some (renamePIDRed from to r, fmap (fun e => (fst e, map (renamePIDVal from to) (snd e))) eff').
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

Lemma renamePID_construct_bitstring : forall vs from to,
  construct_bitstring (map (renamePIDVal from to) vs) = construct_bitstring vs.
Proof.
  induction vs; intros; simpl; auto.
  destruct a; simpl; try reflexivity.
  * destruct (from =? p); reflexivity.
  * now rewrite IHvs.
Qed.

Corollary renamePID_create_result :
  forall vs ident r eff',
    create_result ident vs = Some (r, eff') ->
    forall from to, create_result (renamePIDFrameId from to ident)
                                  (map (renamePIDVal from to) vs) =
                                  Some (renamePIDRed from to r, fmap (fun e => (fst e, map (renamePIDVal from to) (snd e))) eff').
Proof.
  intros. destruct ident; simpl in *.
  * now inv H.
  * now inv H.
  * inv H. cbn.
    now rewrite <- rename_subst_deflatten_list_val, renamePID_make_val_map.
  * rewrite renamePID_construct_bitstring.
    destruct (construct_bitstring vs); inv H; reflexivity.
  * destruct m, f; simpl in *; inv H; auto.
    all: try destruct l; try destruct l0; try inv H1; auto.
    all: try (destruct (from =? p) eqn:P; cbn; now try rewrite P).
    eapply renamePID_eval in H0. simpl in H0. exact H0.
  * eapply renamePID_primop_eval in H. exact H.
  * rewrite length_map.
    destruct v; simpl. all: try now inv H.
    - destruct Nat.eqb eqn:P; inv H; cbn; now rewrite P.
    - break_match_hyp; try now inv H.
      inv H. simpl. rewrite split_renamePID_subst_exp, renamePID_subst_list_subst.
      unfold convert_to_closlist. repeat f_equal.
      rewrite map_map, map_app. f_equal. rewrite map_map.
      f_equal. extensionality x. destruct x, p. cbn. f_equal.
Qed.

Lemma renamePID_segment_to_bitstring : forall v vsize unit type endian r from to,
  segment_to_bitstring v vsize unit type endian = Some r ->
  segment_to_bitstring (renamePIDVal from to v) (renamePIDVal from to vsize) unit type endian =
  Some (renamePIDRed from to r).
Proof.
  intros v vsize unit type endian r from to H.
  unfold segment_to_bitstring in *.
  destruct vsize; simpl in *; try (inv H; reflexivity).
  * destruct l as [a|z]; [inv H; reflexivity|].
    destruct (z <? 0)%Z; [inv H; reflexivity|].
    destruct type; try (inv H; reflexivity); try discriminate.
    all: destruct v; simpl in *; repeat case_match; try congruence; inv H; simpl;
         repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb a b) end;
         first [reflexivity | congruence].
  * inv H. simpl.
    repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb a b) end.
    all: reflexivity.
Qed.

Theorem renamePID_is_preserved :
  forall fs r fs' r', ⟨fs, r⟩ --> ⟨fs', r'⟩ ->
    forall from to,
      ⟨renamePIDStack from to fs, renamePIDRed from to r⟩ -->
      ⟨renamePIDStack from to fs', renamePIDRed from to r'⟩.
Proof.
  intros. inv H; cbn; try now constructor.
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
    constructor. now rewrite length_map.
  * repeat rewrite split_renamePID_subst_exp,
                   renamePID_subst_list_subst,
                   renamePID_subst_id.
    constructor. rewrite renamePIDPat_match_pattern_list.
    now apply renamePID_match_pattern_list.
  * econstructor. rewrite renamePIDPat_match_pattern_list.
    now apply renamePID_nomatch_pattern_list.
  * (* heating a segment *)
    destruct seg as [v s u t sg en]. simpl. constructor.
  * (* cooling a segment *)
    constructor. now apply renamePID_segment_to_bitstring.
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
    constructor. now rewrite length_map.
  * rewrite split_renamePID_subst_exp.
    pose proof (renamePID_subst_list_subst [exclass_to_value class; reason; details]).
    simpl in H. rewrite H.
    destruct class; cbn; constructor.
  * destruct exc, p. constructor.
    destruct F; auto.
Qed.

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
 | VNil                  => ∅
 | VLit l                => ∅
 | VPid p                => {[p]}
 | VCons hd tl           => usedPIDsVal hd ∪ usedPIDsVal tl
 | VTuple l              => flat_union usedPIDsVal l
 | VMap l                => flat_union (fun x => usedPIDsVal x.1 ∪ usedPIDsVal x.2) l
 | VVar n                => ∅
 | VFunId n              => ∅
 | VClos ext id params e => usedPIDsExp e ∪ flat_union (fun x => usedPIDsExp x.2) ext
 | VBitstring bits       => ∅
end

with usedPIDsNVal (n : NonVal) : gset PID :=
match n with
 | EFun vl e    => usedPIDsExp e
 | EValues el   => flat_union usedPIDsExp el
 | ECons hd tl  => usedPIDsExp hd ∪ usedPIDsExp tl
 | ETuple l     => flat_union usedPIDsExp l
 | EMap l       => flat_union (fun x => usedPIDsExp x.1 ∪ usedPIDsExp x.2) l
 | ECall m f l  => usedPIDsExp m ∪ usedPIDsExp f ∪ flat_union usedPIDsExp l
 | EPrimOp f l  => flat_union usedPIDsExp l
 | EApp exp l   => usedPIDsExp exp ∪ flat_union usedPIDsExp l
 | ECase e l    => usedPIDsExp e ∪ flat_union (fun x =>
     flat_union usedPIDsPat x.1.1 ∪ usedPIDsExp x.1.2 ∪ usedPIDsExp x.2) l
 | ELet l e1 e2 => usedPIDsExp e1 ∪ usedPIDsExp e2
 | ESeq e1 e2   => usedPIDsExp e1 ∪ usedPIDsExp e2
 | ELetRec l e  => usedPIDsExp e ∪ flat_union (fun x => usedPIDsExp x.2) l
 | ETry e1 vl1 e2 vl2 e3 => usedPIDsExp e1 ∪ usedPIDsExp e2 ∪ usedPIDsExp e3
 | EBin l       => flat_union usedPIDsExp l
 | ESeg seg     => usedPIDsExp (val seg) ∪ usedPIDsExp (Syntax.size seg)
end
with usedPIDsPat (p : Pat) : gset PID :=
match p with
 | PVar => ∅
 | PLit l        => ∅
 | PCons hd tl   => usedPIDsPat hd ∪ usedPIDsPat tl
 | PTuple l      => flat_union usedPIDsPat l
 | PMap l        => flat_union (fun x => usedPIDsPat x.1 ∪ usedPIDsPat x.2) l
 | PNil          => ∅
 | PBin segments => flat_union (fun x => usedPIDsPat (val x) ∪ usedPIDsVal (Syntax.size x)) segments
end
.

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
 | IBin => ∅
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
 | FCase1 l => flat_union (fun x => flat_union usedPIDsPat x.1.1 ∪ usedPIDsExp x.1.2 ∪ usedPIDsExp x.2) l
 | FCase2 lv ex le =>
   usedPIDsExp ex ∪
   flat_union usedPIDsVal lv ∪
   flat_union (fun x => flat_union usedPIDsPat x.1.1 ∪ usedPIDsExp x.1.2 ∪ usedPIDsExp x.2) le
 | FLet l e => usedPIDsExp e
 | FSeq e => usedPIDsExp e
 | FTry vl1 e2 vl2 e3 => usedPIDsExp e2 ∪ usedPIDsExp e3
 | FSeg1 size _ _ _ _ => usedPIDsExp size
 | FSeg2 val _ _ _ _  => usedPIDsVal val
end.

Definition usedPIDsStack (fs : FrameStack) : gset PID :=
  flat_union usedPIDsFrame fs.

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
  (forall e from to, from ∉ (usedPIDsVal e) -> renamePIDVal from to e = e) /\
  (forall p from to, from ∉ (usedPIDsPat p) -> renamePIDPat from to p = p).
Proof.
  apply Exp_ind with
    (PQ := fun l => Forall (fun p => forall from to, from ∉ (usedPIDsPat p) -> renamePIDPat from to p = p) l)
    (PR := fun l => Forall (fun '(p1, p2) => forall from to,
        (from ∉ (usedPIDsPat p1) -> renamePIDPat from to p1 = p1) /\
        (from ∉ (usedPIDsPat p2) -> renamePIDPat from to p2 = p2)) l)
    (PT := fun l => Forall (fun seg => forall from to,
        (from ∉ (usedPIDsPat (val seg)) -> renamePIDPat from to (val seg) = val seg) /\
        (from ∉ (usedPIDsVal (Syntax.size seg)) -> renamePIDVal from to (Syntax.size seg) = Syntax.size seg)) l)
    (QV := fun l => Forall (fun e => forall from to, from ∉ (usedPIDsVal e) -> renamePIDVal from to e = e) l)
    (Q := fun l => Forall (fun e => forall from to, from ∉ (usedPIDsExp e) -> renamePID from to e = e) l)
    (RV := fun l => Forall (fun '(e1, e2) => forall from to,
        (from ∉ (usedPIDsVal e1) -> renamePIDVal from to e1 = e1) /\
        (from ∉ (usedPIDsVal e2) -> renamePIDVal from to e2 = e2)) l)
    (R := fun l => Forall (fun '(e1, e2) => forall from to,
        (from ∉ (usedPIDsExp e1) -> renamePID from to e1 = e1) /\
        (from ∉ (usedPIDsExp e2) -> renamePID from to e2 = e2)) l)
    (W := fun l => Forall (fun '(p, g, e) => forall from to,
       (from ∉ (flat_union usedPIDsPat p) -> map (renamePIDPat from to) p = p) /\
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
    apply list_elem_of_In in H1. by apply H0 in H1.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext_in.
    rewrite List.Forall_forall in H. intros. eapply H in H1 as P. destruct a.
    simpl in H0.
    rewrite not_elem_of_flat_union in H0.
    apply list_elem_of_In in H1. apply H0 in H1.
    rewrite (proj1 (P _ _)), (proj2 (P _ _)). reflexivity.
    all: set_solver.
  * rewrite H0. 2: set_solver. f_equal.
    rewrite <- (map_id ext) at 2. apply map_ext_in. intros.
    rewrite List.Forall_forall in H. intros. eapply H in H2 as P.
    destruct a, p.
    apply not_elem_of_union in H1 as [_ ?].
    rewrite not_elem_of_flat_union in H1.
    apply list_elem_of_In in H2. apply H1 in H2.
    simpl in *. by rewrite P.
  * f_equal. rewrite <- (map_id el) at 2.
    apply map_ext_in.
    rewrite List.Forall_forall in H. intros. eapply H in H1 as P. now erewrite P.
    simpl in H0.
    rewrite not_elem_of_flat_union in H0.
    apply list_elem_of_In in H1. by apply H0 in H1.
  * rewrite H, H0. all: set_solver.
  * f_equal. rewrite <- (map_id l) at 2.
    apply map_ext_in.
    rewrite List.Forall_forall in H. intros. eapply H in H1 as P. now erewrite P.
    simpl in H0.
    rewrite not_elem_of_flat_union in H0.
    apply list_elem_of_In in H1. by apply H0 in H1.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext_in.
    rewrite List.Forall_forall in H. intros. eapply H in H1 as P. destruct a.
    simpl in H0.
    rewrite not_elem_of_flat_union in H0.
    apply list_elem_of_In in H1. apply H0 in H1.
    cbn. rewrite (proj1 (P _ _)), (proj2 (P _ _)). reflexivity.
    all: set_solver.
  * f_equal.
    - rewrite H; set_solver.
    - rewrite H0; set_solver.
    - rewrite <- (map_id l) at 2.
      apply map_ext_in.
      rewrite List.Forall_forall in H1. intros. eapply H1 in H3 as P. now erewrite P.
      simpl in H2. apply not_elem_of_union in H2 as [_ H2].
      rewrite not_elem_of_flat_union in H2.
      apply list_elem_of_In in H3. by apply H2 in H3.
  * f_equal. rewrite <- (map_id l) at 2.
    apply map_ext_in.
    rewrite List.Forall_forall in H. intros. eapply H in H1 as P. now erewrite P.
    simpl in H0.
    rewrite not_elem_of_flat_union in H0.
    apply list_elem_of_In in H1. by apply H0 in H1.
  * f_equal.
    - rewrite H; set_solver.
    - rewrite <- (map_id l) at 2.
      apply map_ext_in.
      rewrite List.Forall_forall in H0. intros. eapply H0 in H2 as P. now erewrite P.
      simpl in H1. apply not_elem_of_union in H1 as [_ H1].
      rewrite not_elem_of_flat_union in H1.
      apply list_elem_of_In in H2. by apply H1 in H2.
  * f_equal.
    - rewrite H; set_solver.
    - f_equal. rewrite <- (map_id l) at 2. apply map_ext_in.
      rewrite List.Forall_forall in H0. intros. eapply H0 in H2 as P. destruct a, p.
      simpl in H1. apply not_elem_of_union in H1 as [_ H1].
      rewrite not_elem_of_flat_union in H1.
      apply list_elem_of_In in H2. apply H1 in H2.
      simpl in H2. destruct_not_in.
      rewrite (proj1 (P _ _)), (proj1 (proj2 (P _ _))), (proj2 (proj2 (P _ _))).
      reflexivity.
      all: set_solver.
  * rewrite H, H0; set_solver.
  * rewrite H, H0; set_solver.
  * f_equal.
    - f_equal. rewrite <- (map_id l) at 2. apply map_ext_in.
      rewrite List.Forall_forall in H0. intros. eapply H0 in H2 as P. destruct a.
      simpl in H1. apply not_elem_of_union in H1 as [_ H1].
      rewrite not_elem_of_flat_union in H1.
      apply list_elem_of_In in H2. apply H1 in H2.
      rewrite P. reflexivity. set_solver.
    - rewrite H; set_solver.
  * rewrite H, H0, H1; set_solver.
  * (* EBin *)
    f_equal. rewrite <- (map_id l) at 2.
    apply map_ext_in.
    rewrite List.Forall_forall in H. intros. eapply H in H1 as P. now erewrite P.
    simpl in H0.
    rewrite not_elem_of_flat_union in H0.
    apply list_elem_of_In in H1. by apply H0 in H1.
  * (* ESeg *)
    destruct seg as [v s u t sg en]. simpl in *.
    rewrite H, H0; set_solver.
  * (* PCons *)
    rewrite H, H0; set_solver.
  * (* PTuple *)
    f_equal. rewrite <- (map_id l) at 2.
    apply map_ext_in.
    rewrite List.Forall_forall in H. intros. eapply H in H1 as P. now erewrite P.
    simpl in H0.
    rewrite not_elem_of_flat_union in H0.
    apply list_elem_of_In in H1. by apply H0 in H1.
  * (* PMap *)
    f_equal. rewrite <- (map_id l) at 2. apply map_ext_in.
    rewrite List.Forall_forall in H. intros. eapply H in H1 as P. destruct a.
    simpl in H0.
    rewrite not_elem_of_flat_union in H0.
    apply list_elem_of_In in H1. apply H0 in H1.
    cbn. rewrite (proj1 (P _ _)), (proj2 (P _ _)). reflexivity.
    all: set_solver.
  * (* PBin *)
    f_equal. rewrite <- (map_id l) at 2. apply map_ext_in.
    rewrite List.Forall_forall in H. intros. eapply H in H1 as P. destruct a as [v s u t sg en].
    simpl in H0.
    rewrite not_elem_of_flat_union in H0.
    apply list_elem_of_In in H1. apply H0 in H1.
    simpl in H1. cbn in P. cbn. rewrite (proj1 P), (proj2 P). reflexivity.
    all: set_solver.
  * (* clauses of ECase *)
    constructor; [|assumption].
    intros from to. split; [|split]; [| apply H0 | apply H1].
    intros Hn. rewrite <- (map_id l) at 2. apply map_ext_in.
    rewrite List.Forall_forall in H. intros a Ha.
    apply (H a Ha from to).
    rewrite not_elem_of_flat_union in Hn.
    apply list_elem_of_In in Ha. by apply Hn in Ha.
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

Corollary isNotUsed_renamePID_pat :
  (forall p from to, from ∉ (usedPIDsPat p) -> renamePIDPat from to p = p).
Proof.
  apply isNotUsed_renamePID_ind.
Qed.

Corollary isNotUsed_renamePID_pats :
  (forall l from to, from ∉ (flat_union usedPIDsPat l) -> map (renamePIDPat from to) l = l).
Proof.
  intros. rewrite <- (map_id l) at 2. apply map_ext_in. intros.
  rewrite not_elem_of_flat_union in H.
  apply list_elem_of_In in H0. apply H in H0.
  by rewrite isNotUsed_renamePID_pat.
Qed.

Corollary isNotUsed_renamePID_red :
  (forall e from to, from ∉ (usedPIDsRed e) -> renamePIDRed from to e = e).
Proof.
  destruct e; simpl; intros; auto.
  * now rewrite isNotUsed_renamePID_exp.
  * f_equal. rewrite <- (map_id vs) at 2.
    apply map_ext_in. intros.
    rewrite not_elem_of_flat_union in H.
    apply list_elem_of_In in H0. apply H in H0.
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
      apply list_elem_of_In in H0. apply H in H0.
      by rewrite isNotUsed_renamePID_val.
    - rewrite <- (map_id el) at 2.
      apply map_ext_in. intros.
      apply not_elem_of_union in H as [_ H].
      rewrite not_elem_of_flat_union in H.
      apply list_elem_of_In in H0. apply H in H0.
      by rewrite isNotUsed_renamePID_exp.
  * f_equal. rewrite <- (map_id l) at 2.
    apply map_ext_in. intros.
    rewrite not_elem_of_flat_union in H.
    apply list_elem_of_In in H0. apply H in H0.
    by rewrite isNotUsed_renamePID_exp.
  * f_equal.
    - rewrite isNotUsed_renamePID_exp; set_solver.
    - rewrite <- (map_id l) at 2.
      apply map_ext_in. intros.
      apply not_elem_of_union in H as [_ H].
      rewrite not_elem_of_flat_union in H.
      apply list_elem_of_In in H0. apply H in H0.
      by rewrite isNotUsed_renamePID_exp.
  * f_equal.
    - rewrite isNotUsed_renamePID_val; set_solver.
    - rewrite <- (map_id l) at 2.
      apply map_ext_in. intros.
      apply not_elem_of_union in H as [_ H].
      rewrite not_elem_of_flat_union in H.
      apply list_elem_of_In in H0. apply H in H0.
      by rewrite isNotUsed_renamePID_exp.
  * f_equal.
    rewrite <- (map_id l) at 2. apply map_ext_in. intros. destruct a, p.
    rewrite not_elem_of_flat_union in H.
    apply list_elem_of_In in H0. apply H in H0.
    rewrite isNotUsed_renamePID_pats, isNotUsed_renamePID_exp, isNotUsed_renamePID_exp. reflexivity.
    all: simpl in *; set_solver.
  * f_equal.
    - rewrite <- (map_id lv) at 2. apply map_ext_in. intros.
      apply not_elem_of_union in H as [H _].
      apply not_elem_of_union in H as [_ H].
      rewrite not_elem_of_flat_union in H.
      apply list_elem_of_In in H0. apply H in H0.
      rewrite isNotUsed_renamePID_val. reflexivity. set_solver.
    - rewrite isNotUsed_renamePID_exp; set_solver.
    - rewrite <- (map_id le) at 2. apply map_ext_in. intros.
      apply not_elem_of_union in H as [_ H]. destruct a, p.
      rewrite not_elem_of_flat_union in H.
      apply list_elem_of_In in H0. apply H in H0.
      rewrite isNotUsed_renamePID_pats, isNotUsed_renamePID_exp, isNotUsed_renamePID_exp. reflexivity.
      all: simpl in *; set_solver.
  * now rewrite isNotUsed_renamePID_exp.
  * now rewrite isNotUsed_renamePID_exp.
  * rewrite isNotUsed_renamePID_exp, isNotUsed_renamePID_exp; set_solver.
  * now rewrite isNotUsed_renamePID_exp.
  * now rewrite isNotUsed_renamePID_val.
Qed.

Corollary isNotUsed_renamePID_stack :
  forall fs from to, from ∉ (usedPIDsStack fs) -> renamePIDStack from to fs = fs.
Proof.
  intros. unfold renamePIDStack, usedPIDsStack in *.
  f_equal. rewrite <- (map_id fs) at 2.
  apply map_ext_in. intros.
  rewrite not_elem_of_flat_union in H.
  apply list_elem_of_In in H0. apply H in H0.
  by rewrite isNotUsed_renamePID_frame.
Qed.

Local Theorem double_PIDrenaming_ind :
  (forall e from to, to ∉ (usedPIDsExp e) -> e.⟦from ↦ to⟧.⟦to ↦ from⟧ = e) /\
  (forall e from to, to ∉ (usedPIDsNVal e) -> e.⟦from ↦ to⟧ₙ.⟦to ↦ from⟧ₙ = e) /\
  (forall e from to, to ∉ (usedPIDsVal e) -> e.⟦from ↦ to⟧ᵥ.⟦to ↦ from⟧ᵥ = e) /\
  (forall p from to, to ∉ (usedPIDsPat p) -> renamePIDPat to from (renamePIDPat from to p) = p).
Proof.
  apply Exp_ind with
    (PQ := fun l => Forall (fun p => forall from to, to ∉ (usedPIDsPat p) ->
        renamePIDPat to from (renamePIDPat from to p) = p) l)
    (PR := fun l => Forall (fun '(p1, p2) => forall from to,
        (to ∉ (usedPIDsPat p1) -> renamePIDPat to from (renamePIDPat from to p1) = p1) /\
        (to ∉ (usedPIDsPat p2) -> renamePIDPat to from (renamePIDPat from to p2) = p2)) l)
    (PT := fun l => Forall (fun seg => forall from to,
        (to ∉ (usedPIDsPat (val seg)) -> renamePIDPat to from (renamePIDPat from to (val seg)) = val seg) /\
        (to ∉ (usedPIDsVal (Syntax.size seg)) ->
           (Syntax.size seg).⟦from ↦ to⟧ᵥ.⟦to ↦ from⟧ᵥ = Syntax.size seg)) l)
    (QV := fun l => Forall (fun e => forall from to, to ∉ (usedPIDsVal e) -> e.⟦from ↦ to⟧ᵥ.⟦to ↦ from⟧ᵥ = e) l)
    (Q := fun l => Forall (fun e => forall from to, to ∉ (usedPIDsExp e) -> e.⟦from ↦ to⟧.⟦to ↦ from⟧ = e) l)
    (RV := fun l => Forall (fun '(e1, e2) => forall from to,
        (to ∉ (usedPIDsVal e1) -> e1.⟦from ↦ to⟧ᵥ.⟦to ↦ from⟧ᵥ = e1) /\
        (to ∉ (usedPIDsVal e2) -> e2.⟦from ↦ to⟧ᵥ.⟦to ↦ from⟧ᵥ = e2)) l)
    (R := fun l => Forall (fun '(e1, e2) => forall from to,
        (to ∉ (usedPIDsExp e1) -> e1.⟦from ↦ to⟧.⟦to ↦ from⟧ = e1) /\
        (to ∉ (usedPIDsExp e2) -> e2.⟦from ↦ to⟧.⟦to ↦ from⟧ = e2)) l)
    (W := fun l => Forall (fun '(p, g, e) => forall from to,
       (to ∉ (flat_union usedPIDsPat p) ->
          map (renamePIDPat to from) (map (renamePIDPat from to) p) = p) /\
       (to ∉ (usedPIDsExp g) -> g.⟦from ↦ to⟧.⟦to ↦ from⟧ = g) /\
       (to ∉ (usedPIDsExp e) -> e.⟦from ↦ to⟧.⟦to ↦ from⟧ = e)) l)
    (Z := fun l => Forall (fun '(n, e) => forall from to, to ∉ (usedPIDsExp e) -> e.⟦from ↦ to⟧.⟦to ↦ from⟧ = e) l)
   (VV := fun l => Forall
      (fun '(id, vl, e) => forall from to, to ∉ (usedPIDsExp e) -> e.⟦from ↦ to⟧.⟦to ↦ from⟧ = e) l); intros; simpl; try reflexivity; try now rewrite H.
  all: try now (constructor; auto).
  * break_match_goal; simpl. 2: break_match_goal; eqb_to_eq.
    - rewrite Nat.eqb_refl. eqb_to_eq. now subst.
    - subst. cbn in H. set_solver.
    - reflexivity.
  * rewrite H, H0; set_solver.
  * rewrite map_map. f_equal. rewrite <- map_id. apply map_ext_in.
    intros. simpl in H0. eapply List.Forall_forall in H. rewrite H; auto. 2: assumption.
    apply list_elem_of_In in H1.
    rewrite not_elem_of_flat_union in H0.
    by apply H0 in H1.
  * rewrite map_map. f_equal. rewrite <- map_id. apply map_ext_in.
    intros. simpl in H0. rewrite List.Forall_forall in H. destruct a.
    specialize (H (v, v0) H1 from to) as [H_1 H_2].
    rewrite H_1, H_2. reflexivity.
    all: apply list_elem_of_In in H1; rewrite not_elem_of_flat_union in H0;
         apply H0 in H1; set_solver.
  * rewrite map_map.
    simpl in H1. apply not_elem_of_union in H1 as [H1_1 H1_2].
    rewrite not_elem_of_flat_union in H1_2.
    f_equal. 2: now rewrite H0. rewrite <- map_id. apply map_ext_in.
    intros. rewrite List.Forall_forall in H.
    specialize (H a H1). destruct a,p.
    rewrite H; auto.
    apply list_elem_of_In in H1.
    by apply H1_2 in H1.
  * rewrite map_map. f_equal. rewrite <- map_id. apply map_ext_in.
    intros. simpl in H0. rewrite List.Forall_forall in H. rewrite H; auto.
    rewrite not_elem_of_flat_union in H0. apply list_elem_of_In in H1. set_solver.
  * rewrite H, H0; set_solver.
  * rewrite map_map. f_equal. rewrite <- map_id. apply map_ext_in.
    intros. simpl in H0. rewrite List.Forall_forall in H. rewrite H; auto.
    rewrite not_elem_of_flat_union in H0. apply list_elem_of_In in H1. set_solver.
  * rewrite map_map. f_equal. rewrite <- map_id. apply map_ext_in.
    intros. simpl in H0. rewrite List.Forall_forall in H. destruct a.
    specialize (H (e, e0) H1 from to) as [H_1 H_2].
    cbn. rewrite H_1, H_2. reflexivity.
    all: apply list_elem_of_In in H1; rewrite not_elem_of_flat_union in H0;
         apply H0 in H1; set_solver.
  * rewrite map_map. simpl in H2.
    apply not_elem_of_union in H2 as [? H2].
    rewrite not_elem_of_flat_union in H2.
    f_equal. 1: rewrite H; set_solver. 1: rewrite H0; set_solver.
    rewrite <- map_id. apply map_ext_in.
    intros. simpl in H0. rewrite List.Forall_forall in H1. rewrite H1; auto.
    apply list_elem_of_In in H4. set_solver.
  * rewrite map_map. f_equal. rewrite <- map_id. apply map_ext_in.
    intros. simpl in H0. rewrite List.Forall_forall in H. rewrite H; auto.
    rewrite not_elem_of_flat_union in H0.
    apply list_elem_of_In in H1. set_solver.
  * rewrite map_map. simpl in H1.
    apply not_elem_of_union in H1 as [H1_1 H1_2].
    rewrite not_elem_of_flat_union in H1_2.
    f_equal. 1: rewrite H; set_solver.
    rewrite <- map_id. apply map_ext_in.
    intros. simpl in H1_2. rewrite List.Forall_forall in H0. rewrite H0; auto.
    apply list_elem_of_In in H1; set_solver.
  * rewrite map_map. simpl in H1.
    apply not_elem_of_union in H1 as [H1_1 H1_2].
    rewrite not_elem_of_flat_union in H1_2.
    f_equal. 1: now rewrite H.
    rewrite <- map_id. apply map_ext_in.
    intros. rewrite List.Forall_forall in H0. specialize (H0 _ H1). destruct a, p.
    cbn. rewrite (proj1 (H0 _ _)), (proj1 (proj2 (H0 _ _))), (proj2 (proj2 (H0 _ _))); try reflexivity.
    all: apply list_elem_of_In in H1; apply H1_2 in H1; simpl in H1; set_solver.
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
    apply list_elem_of_In in H1. set_solver.
  * simpl in H2. apply not_elem_of_union in H2 as [H3 ?]. apply not_elem_of_union in H3 as [? ?].
    now rewrite H, H0, H1.
  * (* EBin *)
    rewrite map_map. f_equal. rewrite <- map_id. apply map_ext_in.
    intros. simpl in H0. rewrite List.Forall_forall in H. rewrite H; auto.
    rewrite not_elem_of_flat_union in H0. apply list_elem_of_In in H1. set_solver.
  * (* ESeg *)
    destruct seg as [v s u t sg en]. simpl in *.
    apply not_elem_of_union in H1 as [? ?]. now rewrite H, H0.
  * (* PCons *)
    simpl in H1. apply not_elem_of_union in H1 as [? ?].
    now rewrite H, H0.
  * (* PTuple *)
    rewrite map_map. f_equal. rewrite <- map_id. apply map_ext_in.
    intros. simpl in H0. rewrite List.Forall_forall in H. rewrite H; auto.
    rewrite not_elem_of_flat_union in H0. apply list_elem_of_In in H1. set_solver.
  * (* PMap *)
    rewrite map_map. f_equal. rewrite <- map_id. apply map_ext_in.
    intros. simpl in H0. rewrite List.Forall_forall in H. destruct a.
    specialize (H _ H1 from to) as [H_1 H_2].
    cbn. rewrite H_1, H_2. reflexivity.
    all: apply list_elem_of_In in H1; rewrite not_elem_of_flat_union in H0;
         apply H0 in H1; set_solver.
  * (* PBin *)
    rewrite map_map. f_equal. rewrite <- map_id. apply map_ext_in.
    intros. simpl in H0. rewrite List.Forall_forall in H. destruct a as [v s u t sg en].
    specialize (H _ H1 from to) as [H_1 H_2]. cbn in *.
    rewrite H_1, H_2. reflexivity.
    all: apply list_elem_of_In in H1; rewrite not_elem_of_flat_union in H0;
         apply H0 in H1; simpl in H1; set_solver.
  * (* clauses of ECase *)
    constructor; [|assumption].
    intros from to. split; [|split]; [| intros Hn; apply H0; exact Hn | intros Hn; apply H1; exact Hn].
    intros Hn. rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext_in.
    intros a Ha. rewrite List.Forall_forall in H. apply (H a Ha from to).
    rewrite not_elem_of_flat_union in Hn.
    apply list_elem_of_In in Ha. by apply Hn in Ha.
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

Corollary double_PIDrenaming_pat :
  forall p from to, to ∉ (usedPIDsPat p) ->
    renamePIDPat to from (renamePIDPat from to p) = p.
Proof.
  apply double_PIDrenaming_ind.
Qed.

Corollary double_PIDrenaming_pats :
  forall l from to, to ∉ (flat_union usedPIDsPat l) ->
    map (renamePIDPat to from) (map (renamePIDPat from to) l) = l.
Proof.
  intros. rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext_in. intros.
  rewrite not_elem_of_flat_union in H.
  apply list_elem_of_In in H0. apply H in H0.
  by rewrite double_PIDrenaming_pat.
Qed.

Corollary double_PIDrenaming_red :
  forall e from to, to ∉ (usedPIDsRed e) -> e.⟦from ↦ to⟧ᵣ.⟦to ↦ from⟧ᵣ = e.
Proof.
  destruct e; simpl; intros; auto.
  * now rewrite double_PIDrenaming_exp.
  * rewrite <- (map_id vs) at 2. f_equal. (* change to vseq equality *)
    rewrite map_map. apply map_ext_in. intros.
    apply list_elem_of_In in H0.
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
      apply list_elem_of_In in H0.
      rewrite double_PIDrenaming_val; set_solver.
    - rewrite <- (map_id el) at 2. rewrite map_map. apply map_ext_in. intros.
      apply not_elem_of_union in H as [_ H].
      rewrite not_elem_of_flat_union in H.
      apply list_elem_of_In in H0.
      rewrite double_PIDrenaming_exp; set_solver.
  * f_equal. rewrite <- (map_id l) at 2. rewrite map_map. apply map_ext_in. intros.
    rewrite not_elem_of_flat_union in H.
    apply list_elem_of_In in H0.
    rewrite double_PIDrenaming_exp; set_solver.
  * f_equal.
    - rewrite double_PIDrenaming_exp; set_solver.
    - rewrite <- (map_id l) at 2. rewrite map_map. apply map_ext_in. intros.
      apply not_elem_of_union in H as [_ H].
      rewrite not_elem_of_flat_union in H.
      apply list_elem_of_In in H0.
      rewrite double_PIDrenaming_exp; set_solver.
  * f_equal.
    - rewrite double_PIDrenaming_val; set_solver.
    - rewrite <- (map_id l) at 2. rewrite map_map. apply map_ext_in. intros.
      apply not_elem_of_union in H as [_ H].
      rewrite not_elem_of_flat_union in H.
      apply list_elem_of_In in H0.
      rewrite double_PIDrenaming_exp; set_solver.
  * f_equal.
    rewrite <- (map_id l) at 2. rewrite map_map. apply map_ext_in. intros.
    rewrite not_elem_of_flat_union in H.
    destruct a, p. simpl in *.
    apply list_elem_of_In in H0. apply H in H0.
    rewrite double_PIDrenaming_pats, double_PIDrenaming_exp, double_PIDrenaming_exp; try reflexivity.
    all: simpl in *; set_solver.
  * f_equal.
    - rewrite <- (map_id lv) at 2. rewrite map_map. apply map_ext_in. intros.
      apply not_elem_of_union in H as [H _].
      apply not_elem_of_union in H as [_ H].
      rewrite not_elem_of_flat_union in H.
      apply list_elem_of_In in H0. apply H in H0.
      rewrite double_PIDrenaming_val; set_solver.
    - rewrite double_PIDrenaming_exp; set_solver.
    - rewrite <- (map_id le) at 2. rewrite map_map. apply map_ext_in. intros.
      apply not_elem_of_union in H as [_ H].
      rewrite not_elem_of_flat_union in H.
      apply list_elem_of_In in H0. apply H in H0.
      destruct a, p.
      rewrite double_PIDrenaming_pats, double_PIDrenaming_exp, double_PIDrenaming_exp; try reflexivity.
      all: simpl in *; set_solver.
  * now rewrite double_PIDrenaming_exp.
  * now rewrite double_PIDrenaming_exp.
  * rewrite double_PIDrenaming_exp, double_PIDrenaming_exp; set_solver.
  * now rewrite double_PIDrenaming_exp.
  * now rewrite double_PIDrenaming_val.
Qed.

Corollary double_PIDrenaming_stack :
  forall fs from to, to ∉ (usedPIDsStack fs) -> fs.⟦from ↦ to⟧ₛₜ.⟦to ↦ from⟧ₛₜ = fs.
Proof.
  intros. unfold renamePIDStack, usedPIDsStack in *.
  rewrite <- (map_id fs) at 2. rewrite map_map. apply map_ext_in. intros.
  rewrite not_elem_of_flat_union in H.
  apply list_elem_of_In in H0.
  rewrite double_PIDrenaming_frame; set_solver.
Qed.

Lemma renamePID_implies_scope :
  (forall e Γ from to, EXP Γ ⊢ renamePID from to e -> EXP Γ ⊢ e) /\
  (forall e Γ from to, NVAL Γ ⊢ renamePIDNVal from to e -> NVAL Γ ⊢ e) /\
  (forall e Γ from to, VAL Γ ⊢ renamePIDVal from to e -> VAL Γ ⊢ e) /\
  (forall p Γ from to, PAT Γ ⊢ renamePIDPat from to p -> PAT Γ ⊢ p).
Proof.
  apply Exp_ind with
    (PQ := fun l => Forall (fun p => forall Γ from to, PAT Γ ⊢ renamePIDPat from to p -> PAT Γ ⊢ p) l)
    (PR := fun l => Forall (fun '(p1, p2) => forall Γ from to,
        (PAT Γ ⊢ renamePIDPat from to p1 -> PAT Γ ⊢ p1) /\
        (PAT Γ ⊢ renamePIDPat from to p2 -> PAT Γ ⊢ p2)) l)
    (PT := fun l => Forall (fun seg => forall Γ from to,
        (PAT Γ ⊢ renamePIDPat from to (val seg) -> PAT Γ ⊢ val seg) /\
        (VAL Γ ⊢ renamePIDVal from to (Syntax.size seg) -> VAL Γ ⊢ Syntax.size seg)) l)
    (Q := fun l => Forall (fun e => forall Γ from to, EXP Γ ⊢ renamePID from to e -> EXP Γ ⊢ e) l)
    (QV := fun l => Forall (fun e => forall Γ from to, VAL Γ ⊢ renamePIDVal from to e -> VAL Γ ⊢ e) l)
    (R := fun l => Forall (fun '(e1, e2) => forall Γ from to, (EXP Γ ⊢ renamePID from to e1 -> EXP Γ ⊢ e1) /\ (EXP Γ ⊢ renamePID from to e2 -> EXP Γ ⊢ e2)) l)
    (RV := fun l => Forall (fun '(e1, e2) => forall Γ from to, (VAL Γ ⊢ renamePIDVal from to e1 -> VAL Γ ⊢ e1) /\ (VAL Γ ⊢ renamePIDVal from to e2 -> VAL Γ ⊢ e2)) l)
    (VV := fun l => Forall (fun '(_, _, e) => forall Γ from to, EXP Γ ⊢ renamePID from to e -> EXP Γ ⊢ e) l)
    (W := fun l => Forall (fun '(p,g,e) =>
        Forall (fun pat => forall Γ from to, PAT Γ ⊢ renamePIDPat from to pat -> PAT Γ ⊢ pat) p /\
        forall Γ from to, (EXP Γ ⊢ renamePID from to g -> EXP Γ ⊢ g) /\ (EXP Γ ⊢ renamePID from to e -> EXP Γ ⊢ e)) l)
    (Z := fun l => Forall (fun '(_, e) => forall Γ from to, EXP Γ ⊢ renamePID from to e -> EXP Γ ⊢ e) l).
  all: intros.
  all: try now (constructor; auto).
  all: try now (constructor; [intros; split; firstorder|auto]).
  all: simpl in *; destruct_scopes; try (by (constructor; firstorder)).
  * rewrite Forall_nth in H. constructor. intros.
    eapply H; auto.
    rewrite <- map_nth. eapply H3. by rewrite length_map.
  * rewrite (Forall_nth) in H. Unshelve. 2: exact (VNil, VNil).
    constructor; intros.
    - apply H in H0 as H0'. rewrite length_map in *.
      apply H2 in H0. rewrite map_nth with (d := (VNil, VNil)).
      rewrite map_map, map_nth with (d := (VNil, VNil)) in H0. destruct (nth i l _).
      simpl in *. eapply (proj1 (H0' _ _ _)). apply H0.
    - apply H in H0 as H0'. rewrite length_map in *.
      apply H4 in H0. rewrite map_nth with (d := (VNil, VNil)).
      rewrite map_map, map_nth with (d := (VNil, VNil)) in H0. destruct (nth i l _).
      simpl in *. eapply (proj2 (H0' _ _ _)). apply H0.
  * rewrite (Forall_nth) in H. Unshelve. 2: exact (0,0, ˝VNil).
    constructor; intros.
    - apply H in H1 as H1'. rewrite length_map in *.
      apply H5 in H1. do 2 rewrite map_nth with (d := (0,0, ˝VNil)).
      do 2 rewrite map_map in H1.
      do 2 rewrite map_nth with (d := (0,0, ˝VNil)) in H1. destruct (nth i ext _).
      simpl in *. destruct p. eapply (H1' _ _ _). apply H1.
    - eapply H0. rewrite length_map in H8. eapply H8.
  * rewrite Forall_nth in H. constructor. intros.
    eapply H; auto.
    rewrite <- map_nth. eapply H3. by rewrite length_map.
  * rewrite Forall_nth in H. constructor. intros.
    eapply H; auto.
    rewrite <- map_nth. eapply H3. by rewrite length_map.
  * rewrite (Forall_nth) in H. Unshelve. 2: exact (˝VNil, ˝VNil).
    constructor; intros.
    - apply H in H0 as H0'. rewrite length_map in *.
      apply H2 in H0. rewrite map_nth with (d := (˝VNil, ˝VNil)).
      rewrite map_map, map_nth with (d := (˝VNil, ˝VNil)) in H0. destruct (nth i l _).
      simpl in *. eapply (proj1 (H0' _ _ _)). apply H0.
    - apply H in H0 as H0'. rewrite length_map in *.
      apply H4 in H0. rewrite map_nth with (d := (˝VNil, ˝VNil)).
      rewrite map_map, map_nth with (d := (˝VNil, ˝VNil)) in H0. destruct (nth i l _).
      simpl in *. eapply (proj2 (H0' _ _ _)). apply H0.
  * constructor.
    - rewrite Forall_nth in H1. intros.
      eapply H1; auto.
      rewrite <- map_nth. eapply H7. by rewrite length_map.
    - by eapply H.
    - by eapply H0.
  * rewrite Forall_nth in H. constructor. intros.
    eapply H; auto.
    rewrite <- map_nth. eapply H3. by rewrite length_map.
  * constructor.
    - by eapply H.
    - rewrite Forall_nth in H0. intros.
      eapply H0; auto.
      rewrite <- map_nth. eapply H6. by rewrite length_map.
  * (* ECase *)
    rewrite (Forall_nth) in H0. Unshelve. 2: exact ([], ˝VNil, ˝VNil).
    constructor.
    - by eapply H.
    - intros i Hi.
      specialize (H5 i ltac:(rewrite length_map; exact Hi)) as H5i. specialize (H0 i Hi) as H0i.
      do 2 rewrite map_map in H5i. do 2 rewrite map_nth with (d := ([], ˝VNil, ˝VNil)) in H5i.
      setoid_rewrite (map_nth (fst ∘ fst)) with (d := ([], ˝VNil, ˝VNil)).
      setoid_rewrite (map_nth (snd ∘ fst)) with (d := ([], ˝VNil, ˝VNil)).
      destruct (nth i l ([], ˝VNil, ˝VNil)) as [[ps g] b]. cbn in *.
      rewrite PatListVars_renamePID in H5i.
      destruct H0i as [_ Hg]. eapply (proj1 (Hg _ _ _)). exact H5i.
    - intros i Hi.
      specialize (H7 i ltac:(rewrite length_map; exact Hi)) as H7i. specialize (H0 i Hi) as H0i.
      do 2 rewrite map_map in H7i. do 2 rewrite map_nth with (d := ([], ˝VNil, ˝VNil)) in H7i.
      setoid_rewrite (map_nth (fst ∘ fst)) with (d := ([], ˝VNil, ˝VNil)).
      setoid_rewrite (map_nth snd) with (d := ([], ˝VNil, ˝VNil)).
      destruct (nth i l ([], ˝VNil, ˝VNil)) as [[ps g] b]. cbn in *.
      rewrite PatListVars_renamePID in H7i.
      destruct H0i as [_ Hg]. eapply (proj2 (Hg _ _ _)). exact H7i.
    - intros i Hi j Hj.
      pose proof (H0 i Hi) as H0i.
      specialize (H8 i ltac:(rewrite length_map; exact Hi) j) as H8ij.
      rewrite map_map in H8ij. rewrite map_nth with (d := ([], ˝VNil, ˝VNil)) in H8ij.
      setoid_rewrite (map_nth (fst ∘ fst)) with (d := ([], ˝VNil, ˝VNil)) in Hj.
      setoid_rewrite (map_nth (fst ∘ fst)) with (d := ([], ˝VNil, ˝VNil)).
      destruct (nth i l ([], ˝VNil, ˝VNil)) as [[ps g] b]. cbn in *.
      destruct H0i as [Hp _].
      rewrite length_map in H8ij. specialize (H8ij Hj).
      rewrite map_nth with (d := PNil) in H8ij.
      rewrite Forall_nth in Hp.
      eapply (Hp j Hj). exact H8ij.
  * constructor.
    - rewrite Forall_nth in H0. Unshelve. 2: exact (0, ˝VNil). intros.
      rewrite length_map in *.
      do 2 rewrite map_nth with (d := (0, ˝VNil)).
      apply H0 in H1 as P.
      apply H5 in H1.
      do 2 rewrite map_map in H1.
      do 2 rewrite map_nth with (d := (0, ˝VNil)) in H1. destruct nth.
      eapply P. apply H1.
    - eapply H. by rewrite length_map in H6.
  * (* EBin *)
    rewrite Forall_nth in H. constructor. intros.
    eapply H; auto.
    rewrite <- map_nth.
    apply H3; by rewrite length_map.
  * (* ESeg *)
    destruct seg as [v s u t sg en]. simpl in *. destruct_scopes.
    constructor; simpl; [eapply H | eapply H0]; eassumption.
  * (* PTuple *)
    rewrite Forall_nth in H. constructor. intros.
    eapply H; auto.
    rewrite <- map_nth.
    apply H3; by rewrite length_map.
  * (* PMap *)
    rewrite (Forall_nth) in H. Unshelve. 2: exact (PNil, PNil).
    constructor; intros.
    - apply H in H0 as H0'. rewrite length_map in *.
      apply H2 in H0. rewrite map_nth with (d := (PNil, PNil)).
      rewrite map_map, map_nth with (d := (PNil, PNil)) in H0. destruct (nth i l _).
      simpl in *. eapply (proj1 (H0' _ _ _)). apply H0.
    - apply H in H0 as H0'. rewrite length_map in *.
      apply H4 in H0. rewrite map_nth with (d := (PNil, PNil)).
      rewrite map_map, map_nth with (d := (PNil, PNil)) in H0. destruct (nth i l _).
      simpl in *. eapply (proj2 (H0' _ _ _)). apply H0.
  * (* PBin *)
    rewrite (Forall_nth) in H. Unshelve. 2: exact default_segment.
    constructor; intros.
    - pose proof (H i H0) as H0'. rewrite length_map in *.
      specialize (H2 i H0). rewrite map_map in H2. rewrite map_nth with (d := default_segment) in H2.
      rewrite map_nth with (d := default_segment). cbn in H2 |- *.
      eapply (proj1 (H0' _ _ _)). exact H2.
    - pose proof (H i H0) as H0'. rewrite length_map in *.
      specialize (H4 i H0). rewrite map_map in H4. rewrite map_nth with (d := default_segment) in H4.
      rewrite map_nth with (d := default_segment). cbn in H4 |- *.
      eapply (proj2 (H0' _ _ _)). exact H4.
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
  (forall e p, renamePIDVal p p e = e) /\
  (forall pt p, renamePIDPat p p pt = pt).
Proof.
  apply Exp_ind with
    (PQ := fun l => Forall (fun pt => forall p, renamePIDPat p p pt = pt) l)
    (PR := fun l => Forall (fun '(p1, p2) => forall p, (renamePIDPat p p p1 = p1) /\ (renamePIDPat p p p2 = p2)) l)
    (PT := fun l => Forall (fun seg => forall p, (renamePIDPat p p (val seg) = val seg) /\ (renamePIDVal p p (Syntax.size seg) = Syntax.size seg)) l)
    (Q := fun l => Forall (fun e => forall p, renamePID p p e = e) l)
    (QV := fun l => Forall (fun e => forall p, renamePIDVal p p e = e) l)
    (R := fun l => Forall (fun '(e1, e2) => forall p, (renamePID p p e1 = e1) /\ (renamePID p p e2 = e2)) l)
    (RV := fun l => Forall (fun '(e1, e2) => forall p, (renamePIDVal p p e1 = e1) /\ (renamePIDVal p p e2 = e2)) l)
    (VV := fun l => Forall (fun '(_, _, e) => forall p, renamePID p p e = e) l)
    (W := fun l => Forall (fun '(pl,g,e) => forall p, (map (renamePIDPat p p) pl = pl) /\ (renamePID p p g = g) /\ (renamePID p p e = e)) l)
    (Z := fun l => Forall (fun '(_, e) => forall p, renamePID p p e = e) l).
  all: try now (constructor; auto).
  all: intros; simpl; try reflexivity.
  all: try rewrite H; try rewrite H0; try rewrite H1; auto.
  * case_match; eqb_to_eq; auto.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext_in; intros.
    rewrite Forall_forall in H. apply list_elem_of_In in H0.
    eapply H in H0. eassumption.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext_in; intros.
    rewrite Forall_forall in H. apply list_elem_of_In in H0.
    eapply H in H0. destruct a; destruct_hyps. cbn.
    f_equal; apply H0.
  * f_equal. rewrite <- (map_id ext) at 2. apply map_ext_in; intros.
    rewrite Forall_forall in H. apply list_elem_of_In in H1.
    eapply H in H1. destruct a, p0. by rewrite H1.
  * f_equal. rewrite <- (map_id el) at 2. apply map_ext_in; intros.
    rewrite Forall_forall in H. apply list_elem_of_In in H0.
    eapply H in H0. eassumption.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext_in; intros.
    rewrite Forall_forall in H. apply list_elem_of_In in H0.
    eapply H in H0. eassumption.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext_in; intros.
    rewrite Forall_forall in H. apply list_elem_of_In in H0.
    eapply H in H0. destruct a; destruct_hyps. cbn.
    f_equal; apply H0.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext_in; intros.
    rewrite Forall_forall in H1. apply list_elem_of_In in H2.
    eapply H1 in H2. eassumption.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext_in; intros.
    rewrite Forall_forall in H. apply list_elem_of_In in H0.
    eapply H in H0. eassumption.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext_in; intros.
    rewrite Forall_forall in H0. apply list_elem_of_In in H1.
    eapply H0 in H1. eassumption.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext_in; intros.
    rewrite Forall_forall in H0. apply list_elem_of_In in H1.
    eapply H0 in H1. destruct a, p0. repeat f_equal; auto; apply H1.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext_in; intros.
    rewrite Forall_forall in H0. apply list_elem_of_In in H1.
    eapply H0 in H1. destruct a. f_equal; apply H1.
  * (* EBin *)
    f_equal. rewrite <- (map_id l) at 2. apply map_ext_in; intros.
    rewrite Forall_forall in H. apply list_elem_of_In in H0.
    eapply H in H0. eassumption.
  * (* ESeg *)
    destruct seg as [v s u t sg en]. simpl in *.
    now rewrite H, H0.
  * (* PTuple *)
    f_equal. rewrite <- (map_id l) at 2. apply map_ext_in; intros.
    rewrite Forall_forall in H. apply list_elem_of_In in H0.
    eapply H in H0. eassumption.
  * (* PMap *)
    f_equal. rewrite <- (map_id l) at 2. apply map_ext_in; intros.
    rewrite Forall_forall in H. apply list_elem_of_In in H0.
    eapply H in H0. destruct a; destruct_hyps. cbn.
    f_equal; apply H0.
  * (* PBin *)
    f_equal. rewrite <- (map_id l) at 2. apply map_ext_in; intros.
    rewrite Forall_forall in H. apply list_elem_of_In in H0.
    pose proof (H _ H0 p) as [H1 H2].
    destruct a as [v s u t sg en]. cbn in *.
    now rewrite H1, H2.
  * (* clauses of ECase *)
    constructor; [|assumption].
    intros p. split; [|split]; [| apply H0 | apply H1].
    rewrite <- (map_id l) at 2. apply map_ext_in; intros.
    rewrite Forall_forall in H. apply list_elem_of_In in H3.
    eapply H in H3. eassumption.
Qed.

Lemma renamePID_id_val :
  (forall e p, renamePIDVal p p e = e).
Proof.
  exact (proj1 (proj2 (proj2 renamePID_id))).
Qed.

Lemma renamePID_id_exp :
  (forall e p, renamePID p p e = e).
Proof.
  exact (proj1 renamePID_id).
Qed.

Lemma renamePID_id_pat :
  (forall pt p, renamePIDPat p p pt = pt).
Proof.
  exact (proj2 (proj2 (proj2 renamePID_id))).
Qed.

Lemma renamePID_id_pats :
  forall l p, map (renamePIDPat p p) l = l.
Proof.
  intros. rewrite <- (map_id l) at 2. apply map_ext. intros. apply renamePID_id_pat.
Qed.

Corollary renamePID_id_red :
  forall r p, renamePIDRed p p r = r.
Proof.
  destruct r; intros; cbn; auto.
  * f_equal. apply renamePID_id.
  * rewrite <- (map_id vs) at 2. f_equal. apply map_ext_in.
    intros. apply renamePID_id.
  * destruct e, p0.
    by do 2 rewrite renamePID_id_val.
Qed.

Lemma renamePID_id_frameId :
  forall i p, renamePIDFrameId p p i = i.
Proof.
  destruct i; simpl; intros; try reflexivity.
  * by do 2 rewrite renamePID_id_val.
  * by rewrite renamePID_id_val.
Qed.

Lemma renamePID_id_frame :
  forall f p, renamePIDFrame p p f = f.
Proof.
  destruct f; intros; simpl;
    try repeat rewrite (proj1 renamePID_id); try rewrite renamePID_id_val;
    try by reflexivity.
  * rewrite renamePID_id_frameId. f_equal.
    - rewrite <- (map_id vl) at 2. apply map_ext. intros. apply renamePID_id.
    - rewrite <- (map_id el) at 2. apply map_ext. intros. apply renamePID_id.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext. intros. apply renamePID_id.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext. intros. apply renamePID_id.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext. intros. apply renamePID_id.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext. intros.
    destruct a, p0. cbn. rewrite renamePID_id_pats. by do 2 rewrite (proj1 renamePID_id).
  * f_equal.
    - rewrite <- (map_id lv) at 2. apply map_ext. intros. apply renamePID_id.
    - rewrite <- (map_id le) at 2. apply map_ext. intros.
      destruct a, p0. cbn. rewrite renamePID_id_pats. by do 2 rewrite (proj1 renamePID_id).
Qed.

Lemma renamePID_id_stack :
  forall fs p, renamePIDStack p p fs = fs.
Proof.
  intros. rewrite <- (map_id fs) at 2. f_equal. apply map_ext_in.
  intros. by apply renamePID_id_frame.
Qed.

From stdpp Require Import fin_maps.

Corollary elem_of_map_iff :
  ∀ (A B : Type) (f : A → B) (l : list A) (y : B),
    y ∈ (map f l) ↔ (∃ x : A, f x = y ∧ x ∈ l).
Proof.
  intros. rewrite list_elem_of_In. split; intros.
  * apply in_map_iff in H. destruct_hyps. do 2 eexists. eassumption.
    by apply list_elem_of_In.
  * destruct_hyps. apply list_elem_of_In in H0.
    apply in_map_iff. set_solver.
Qed.

Local Lemma usedPIDsVal_flat_union_helper :
  forall l p p',
  (Forall (fun x => forall p p', usedPIDsVal (renamePIDVal p p' x) = if decide (p ∈ usedPIDsVal x)
                                        then {[p']} ∪ usedPIDsVal x ∖ {[p]}
                                        else usedPIDsVal x ∖ {[p]}) l) ->
  flat_union usedPIDsVal (map (renamePIDVal p p') l) =
  if (decide (p ∈ flat_union usedPIDsVal l))
  then {[p']} ∪ flat_union usedPIDsVal l ∖ {[p]}
  else flat_union usedPIDsVal l ∖ {[p]}.
Proof.
  induction l; intros; simpl. set_solver.
  rewrite Forall_forall in H.
  rewrite IHl, H. clear. repeat destruct decide; set_solver.
  set_solver.
  apply Forall_forall. intros. apply H. set_solver.
Qed.

Local Lemma usedPIDsExp_flat_union_helper :
  forall l p p',
  (Forall (fun x => forall p p', usedPIDsExp (renamePID p p' x) = if decide (p ∈ usedPIDsExp x)
                                        then {[p']} ∪ usedPIDsExp x ∖ {[p]}
                                        else usedPIDsExp x ∖ {[p]}) l) ->
  flat_union usedPIDsExp (map (renamePID p p') l) =
  if (decide (p ∈ flat_union usedPIDsExp l))
  then {[p']} ∪ flat_union usedPIDsExp l ∖ {[p]}
  else flat_union usedPIDsExp l ∖ {[p]}.
Proof.
  induction l; intros; simpl. set_solver.
  rewrite Forall_forall in H.
  rewrite IHl, H. clear. repeat destruct decide; set_solver.
  set_solver.
  apply Forall_forall. intros. apply H. set_solver.
Qed.

Local Lemma usedPIDsVal_flat_union_helper_prod :
  forall l p p',
  (Forall (fun '(x1, x2) => forall p p', (usedPIDsVal (renamePIDVal p p' x1) = if decide (p ∈ usedPIDsVal x1)
                                        then {[p']} ∪ usedPIDsVal x1 ∖ {[p]}
                                        else usedPIDsVal x1 ∖ {[p]}) /\
                                        (usedPIDsVal (renamePIDVal p p' x2) = if decide (p ∈ usedPIDsVal x2)
                                        then {[p']} ∪ usedPIDsVal x2 ∖ {[p]}
                                        else usedPIDsVal x2 ∖ {[p]})) l) ->
  flat_union (λ x, usedPIDsVal x.1 ∪ usedPIDsVal x.2)
  (map (λ '(x, y), (x .⟦ p ↦ p' ⟧ᵥ, y .⟦ p ↦ p' ⟧ᵥ)) l) =
  if (decide (p ∈ flat_union (fun x => usedPIDsVal x.1 ∪ usedPIDsVal x.2) l))
  then {[p']} ∪ flat_union (fun x => usedPIDsVal x.1 ∪ usedPIDsVal x.2) l ∖ {[p]}
  else flat_union (fun x => usedPIDsVal x.1 ∪ usedPIDsVal x.2) l ∖ {[p]}.
Proof.
  induction l; intros; simpl. set_solver.
  rewrite Forall_forall in H.
  rewrite IHl. destruct a. specialize (H (v, v0) ltac:(set_solver)).
  simpl in *. rewrite (proj1 (H _ _)), (proj2 (H _ _)).
  clear. repeat destruct decide; set_solver.
  apply Forall_forall. intros. apply H. set_solver.
Qed.

Local Lemma usedPIDsExp_flat_union_helper_prod :
forall l p p',
  (Forall (fun '(x1, x2) => forall p p', (usedPIDsExp (renamePID p p' x1) = if decide (p ∈ usedPIDsExp x1)
                                        then {[p']} ∪ usedPIDsExp x1 ∖ {[p]}
                                        else usedPIDsExp x1 ∖ {[p]}) /\
                                        (usedPIDsExp (renamePID p p' x2) = if decide (p ∈ usedPIDsExp x2)
                                        then {[p']} ∪ usedPIDsExp x2 ∖ {[p]}
                                        else usedPIDsExp x2 ∖ {[p]})) l) ->
  flat_union (λ x, usedPIDsExp x.1 ∪ usedPIDsExp x.2)
  (map (prod_map (renamePID p p') (renamePID p p')) l) =
  if (decide (p ∈ flat_union (fun x => usedPIDsExp x.1 ∪ usedPIDsExp x.2) l))
  then {[p']} ∪ flat_union (fun x => usedPIDsExp x.1 ∪ usedPIDsExp x.2) l ∖ {[p]}
  else flat_union (fun x => usedPIDsExp x.1 ∪ usedPIDsExp x.2) l ∖ {[p]}.
Proof.
  induction l; intros; simpl. set_solver.
  rewrite Forall_forall in H.
  rewrite IHl. destruct a. specialize (H (e, e0) ltac:(set_solver)).
  simpl in *. rewrite (proj1 (H _ _)), (proj2 (H _ _)).
  clear. repeat destruct decide; set_solver.
  apply Forall_forall. intros. apply H. set_solver.
Qed.

Local Lemma usedPIDsClos_flat_union_helper :
  forall l p p',
  (Forall (fun '(_, _, x) => forall p p', usedPIDsExp (renamePID p p' x) = if decide (p ∈ usedPIDsExp x)
                                        then {[p']} ∪ usedPIDsExp x ∖ {[p]}
                                        else usedPIDsExp x ∖ {[p]}) l) ->
  flat_union (λ x : nat * nat * Exp, usedPIDsExp x.2)
    (map (λ '(id0, vl0, e0), (id0, vl0, e0 .⟦ p ↦ p' ⟧)) l) =
  if (decide (p ∈ flat_union (λ x : nat * nat * Exp, usedPIDsExp x.2) l))
  then {[p']} ∪ flat_union (λ x : nat * nat * Exp, usedPIDsExp x.2) l ∖ {[p]}
  else flat_union (λ x : nat * nat * Exp, usedPIDsExp x.2) l ∖ {[p]}.
Proof.
  induction l; intros; simpl. set_solver.
  destruct a, p0; simpl.
  rewrite Forall_forall in H.
  rewrite IHl.
  rewrite (H (n, n0, e)). 2: set_solver.
  clear. repeat destruct decide; set_solver.
  apply Forall_forall. intros. apply H. set_solver.
Qed.

Local Lemma usedPIDsPat_flat_union_helper :
  forall l p p',
  (Forall (fun x => forall p p', usedPIDsPat (renamePIDPat p p' x) = if decide (p ∈ usedPIDsPat x)
                                        then {[p']} ∪ usedPIDsPat x ∖ {[p]}
                                        else usedPIDsPat x ∖ {[p]}) l) ->
  flat_union usedPIDsPat (map (renamePIDPat p p') l) =
  if (decide (p ∈ flat_union usedPIDsPat l))
  then {[p']} ∪ flat_union usedPIDsPat l ∖ {[p]}
  else flat_union usedPIDsPat l ∖ {[p]}.
Proof.
  induction l; intros; simpl. set_solver.
  rewrite Forall_forall in H.
  rewrite IHl, H. clear. repeat destruct decide; set_solver.
  set_solver.
  apply Forall_forall. intros. apply H. set_solver.
Qed.

Local Lemma usedPIDsPat_flat_union_helper_prod :
  forall l p p',
  (Forall (fun '(x1, x2) => forall p p', (usedPIDsPat (renamePIDPat p p' x1) = if decide (p ∈ usedPIDsPat x1)
                                        then {[p']} ∪ usedPIDsPat x1 ∖ {[p]}
                                        else usedPIDsPat x1 ∖ {[p]}) /\
                                        (usedPIDsPat (renamePIDPat p p' x2) = if decide (p ∈ usedPIDsPat x2)
                                        then {[p']} ∪ usedPIDsPat x2 ∖ {[p]}
                                        else usedPIDsPat x2 ∖ {[p]})) l) ->
  flat_union (λ x, usedPIDsPat x.1 ∪ usedPIDsPat x.2)
  (map (prod_map (renamePIDPat p p') (renamePIDPat p p')) l) =
  if (decide (p ∈ flat_union (fun x => usedPIDsPat x.1 ∪ usedPIDsPat x.2) l))
  then {[p']} ∪ flat_union (fun x => usedPIDsPat x.1 ∪ usedPIDsPat x.2) l ∖ {[p]}
  else flat_union (fun x => usedPIDsPat x.1 ∪ usedPIDsPat x.2) l ∖ {[p]}.
Proof.
  induction l; intros; simpl. set_solver.
  rewrite Forall_forall in H.
  rewrite IHl. destruct a. specialize (H (p0, p1) ltac:(set_solver)).
  simpl in *. rewrite (proj1 (H _ _)), (proj2 (H _ _)).
  clear. repeat destruct decide; set_solver.
  apply Forall_forall. intros. apply H. set_solver.
Qed.

Local Lemma usedPIDsPatSeg_flat_union_helper :
  forall l p p',
  (Forall (fun seg => forall p p',
      (usedPIDsPat (renamePIDPat p p' (val seg)) = if decide (p ∈ usedPIDsPat (val seg))
                                        then {[p']} ∪ usedPIDsPat (val seg) ∖ {[p]}
                                        else usedPIDsPat (val seg) ∖ {[p]}) /\
      (usedPIDsVal (renamePIDVal p p' (Syntax.size seg)) = if decide (p ∈ usedPIDsVal (Syntax.size seg))
                                        then {[p']} ∪ usedPIDsVal (Syntax.size seg) ∖ {[p]}
                                        else usedPIDsVal (Syntax.size seg) ∖ {[p]})) l) ->
  flat_union (fun x => usedPIDsPat (val x) ∪ usedPIDsVal (Syntax.size x))
    (map (fun seg => {| val := renamePIDPat p p' (val seg);
                        Syntax.size := renamePIDVal p p' (Syntax.size seg);
                        unit := unit seg;
                        type := type seg;
                        sign := sign seg;
                        endian := endian seg |}) l) =
  if (decide (p ∈ flat_union (fun x => usedPIDsPat (val x) ∪ usedPIDsVal (Syntax.size x)) l))
  then {[p']} ∪ flat_union (fun x => usedPIDsPat (val x) ∪ usedPIDsVal (Syntax.size x)) l ∖ {[p]}
  else flat_union (fun x => usedPIDsPat (val x) ∪ usedPIDsVal (Syntax.size x)) l ∖ {[p]}.
Proof.
  induction l; intros; simpl. set_solver.
  rewrite Forall_forall in H.
  rewrite IHl. specialize (H a ltac:(set_solver)).
  simpl in *. rewrite (proj1 (H _ _)), (proj2 (H _ _)).
  clear. repeat destruct decide; set_solver.
  apply Forall_forall. intros. apply H. set_solver.
Qed.

Local Lemma usedPIDsCase_flat_union_helper :
  forall l p p',
  (Forall
       (λ '(pl, g, e),
          ∀ p p' : PID,
            flat_union usedPIDsPat (map (renamePIDPat p p') pl) =
            (if decide (p ∈ flat_union usedPIDsPat pl)
             then {[p']} ∪ flat_union usedPIDsPat pl ∖ {[p]}
             else flat_union usedPIDsPat pl ∖ {[p]})
            ∧ usedPIDsExp g .⟦ p ↦ p' ⟧ =
            (if decide (p ∈ usedPIDsExp g)
             then {[p']} ∪ usedPIDsExp g ∖ {[p]}
             else usedPIDsExp g ∖ {[p]})
            ∧ usedPIDsExp e .⟦ p ↦ p' ⟧ =
              (if decide (p ∈ usedPIDsExp e)
               then {[p']} ∪ usedPIDsExp e ∖ {[p]}
               else usedPIDsExp e ∖ {[p]})) l) ->
  flat_union (λ x : list Pat * Exp * Exp,
                flat_union usedPIDsPat x.1.1 ∪ usedPIDsExp x.1.2 ∪ usedPIDsExp x.2)
    (map (λ '(p0, g, e0), (map (renamePIDPat p p') p0, g .⟦ p ↦ p' ⟧, e0 .⟦ p ↦ p' ⟧)) l) =
  if (decide (p ∈ flat_union (λ x : list Pat * Exp * Exp,
                flat_union usedPIDsPat x.1.1 ∪ usedPIDsExp x.1.2 ∪ usedPIDsExp x.2) l))
  then {[p']} ∪ flat_union (λ x : list Pat * Exp * Exp,
                flat_union usedPIDsPat x.1.1 ∪ usedPIDsExp x.1.2 ∪ usedPIDsExp x.2) l ∖ {[p]}
  else flat_union (λ x : list Pat * Exp * Exp,
                flat_union usedPIDsPat x.1.1 ∪ usedPIDsExp x.1.2 ∪ usedPIDsExp x.2) l ∖ {[p]}.
Proof.
  induction l; intros; simpl. set_solver.
  destruct a, p0; simpl.
  rewrite Forall_forall in H.
  rewrite IHl.
  specialize (H (l0, e0, e) ltac:(set_solver) p p') as X.
  simpl in X. destruct X as [X1 [X2 X3]]. rewrite X1, X2, X3.
  clear. repeat destruct decide; set_solver.
  apply Forall_forall. intros. apply H. set_solver.
Qed.

Local Lemma usedPIDsLetRec_flat_union_helper :
  forall l p p',
  (Forall
       (λ '(_, e),
          ∀ p p' : PID,
            usedPIDsExp e .⟦ p ↦ p' ⟧ =
            (if decide (p ∈ usedPIDsExp e)
             then {[p']} ∪ usedPIDsExp e ∖ {[p]}
             else usedPIDsExp e ∖ {[p]})) l) ->
  flat_union (λ x : nat * Exp, usedPIDsExp x.2)
    (map (λ '(vl, e0), (vl, e0 .⟦ p ↦ p' ⟧)) l) =
  if (decide (p ∈ flat_union (λ x : nat * Exp, usedPIDsExp x.2) l))
  then {[p']} ∪ flat_union (λ x : nat * Exp, usedPIDsExp x.2) l ∖ {[p]}
  else flat_union (λ x : nat * Exp, usedPIDsExp x.2) l ∖ {[p]}.
Proof.
  induction l; intros; simpl. set_solver.
  destruct a. simpl.
  rewrite Forall_forall in H.
  rewrite IHl.
  rewrite (H (n, e)). 2: set_solver.
  clear. repeat destruct decide; set_solver.
  apply Forall_forall. intros. apply H. set_solver.
Qed.

Lemma usedPIDs_rename_ind :
  (forall e p p',
    usedPIDsExp (renamePID p p' e) = if decide (p ∈ usedPIDsExp e)
                                        then {[p']} ∪ usedPIDsExp e ∖ {[p]}
                                        else usedPIDsExp e ∖ {[p]})
  /\
  (forall v p p',
    usedPIDsNVal (renamePIDNVal p p' v) = if decide (p ∈ usedPIDsNVal v)
                                        then {[p']} ∪ usedPIDsNVal v ∖ {[p]}
                                        else usedPIDsNVal v ∖ {[p]})
  /\
  (forall v p p',
    usedPIDsVal (renamePIDVal p p' v) = if decide (p ∈ usedPIDsVal v)
                                        then {[p']} ∪ usedPIDsVal v ∖ {[p]}
                                        else usedPIDsVal v ∖ {[p]})
  /\
  (forall pt p p',
    usedPIDsPat (renamePIDPat p p' pt) = if decide (p ∈ usedPIDsPat pt)
                                        then {[p']} ∪ usedPIDsPat pt ∖ {[p]}
                                        else usedPIDsPat pt ∖ {[p]}).
Proof.
  apply Exp_ind with
    (PQ := fun l => Forall (fun pt => forall p p',
    usedPIDsPat (renamePIDPat p p' pt) = if decide (p ∈ usedPIDsPat pt)
                                        then {[p']} ∪ usedPIDsPat pt ∖ {[p]}
                                        else usedPIDsPat pt ∖ {[p]}) l)
    (PR := fun l => Forall (fun '(p1, p2) => forall p p', (usedPIDsPat (renamePIDPat p p' p1) = if decide (p ∈ usedPIDsPat p1)
                                        then {[p']} ∪ usedPIDsPat p1 ∖ {[p]}
                                        else usedPIDsPat p1 ∖ {[p]}) /\ (usedPIDsPat (renamePIDPat p p' p2) = if decide (p ∈ usedPIDsPat p2)
                                        then {[p']} ∪ usedPIDsPat p2 ∖ {[p]}
                                        else usedPIDsPat p2 ∖ {[p]})) l)
    (PT := fun l => Forall (fun seg => forall p p',
      (usedPIDsPat (renamePIDPat p p' (val seg)) = if decide (p ∈ usedPIDsPat (val seg))
                                        then {[p']} ∪ usedPIDsPat (val seg) ∖ {[p]}
                                        else usedPIDsPat (val seg) ∖ {[p]}) /\
      (usedPIDsVal (renamePIDVal p p' (Syntax.size seg)) = if decide (p ∈ usedPIDsVal (Syntax.size seg))
                                        then {[p']} ∪ usedPIDsVal (Syntax.size seg) ∖ {[p]}
                                        else usedPIDsVal (Syntax.size seg) ∖ {[p]})) l)
    (Q := fun l => Forall (fun e => forall p p',
    usedPIDsExp (renamePID p p' e) = if decide (p ∈ usedPIDsExp e)
                                        then {[p']} ∪ usedPIDsExp e ∖ {[p]}
                                        else usedPIDsExp e ∖ {[p]}) l)
    (QV := fun l => Forall (fun e => forall p p',
    usedPIDsVal (renamePIDVal p p' e) = if decide (p ∈ usedPIDsVal e)
                                        then {[p']} ∪ usedPIDsVal e ∖ {[p]}
                                        else usedPIDsVal e ∖ {[p]}) l)
    (R := fun l => Forall (fun '(e1, e2) => forall p p', (usedPIDsExp (renamePID p p' e1) = if decide (p ∈ usedPIDsExp e1)
                                        then {[p']} ∪ usedPIDsExp e1 ∖ {[p]}
                                        else usedPIDsExp e1 ∖ {[p]}) /\ (usedPIDsExp (renamePID p p' e2) = if decide (p ∈ usedPIDsExp e2)
                                        then {[p']} ∪ usedPIDsExp e2 ∖ {[p]}
                                        else usedPIDsExp e2 ∖ {[p]})) l)
    (RV := fun l => Forall (fun '(e1, e2) => forall p p', (usedPIDsVal (renamePIDVal p p' e1) = if decide (p ∈ usedPIDsVal e1)
                                        then {[p']} ∪ usedPIDsVal e1 ∖ {[p]}
                                        else usedPIDsVal e1 ∖ {[p]}) /\ (usedPIDsVal (renamePIDVal p p' e2) = if decide (p ∈ usedPIDsVal e2)
                                        then {[p']} ∪ usedPIDsVal e2 ∖ {[p]}
                                        else usedPIDsVal e2 ∖ {[p]})) l)
    (VV := fun l => Forall (fun '(_, _, e) => forall p p',
    usedPIDsExp (renamePID p p' e) = if decide (p ∈ usedPIDsExp e)
                                        then {[p']} ∪ usedPIDsExp e ∖ {[p]}
                                        else usedPIDsExp e ∖ {[p]}) l)
    (W := fun l => Forall (fun '(pl,g,e) => forall p p',
      (flat_union usedPIDsPat (map (renamePIDPat p p') pl) = if decide (p ∈ flat_union usedPIDsPat pl)
                                        then {[p']} ∪ flat_union usedPIDsPat pl ∖ {[p]}
                                        else flat_union usedPIDsPat pl ∖ {[p]}) /\
      (usedPIDsExp (renamePID p p' g) = if decide (p ∈ usedPIDsExp g)
                                        then {[p']} ∪ usedPIDsExp g ∖ {[p]}
                                        else usedPIDsExp g ∖ {[p]}) /\ (usedPIDsExp (renamePID p p' e) = if decide (p ∈ usedPIDsExp e)
                                        then {[p']} ∪ usedPIDsExp e ∖ {[p]}
                                        else usedPIDsExp e ∖ {[p]})) l)
    (Z := fun l => Forall (fun '(_, e) => forall p p',
    usedPIDsExp (renamePID p p' e) = if decide (p ∈ usedPIDsExp e)
                                        then {[p']} ∪ usedPIDsExp e ∖ {[p]}
                                        else usedPIDsExp e ∖ {[p]}) l).
  all: try now (constructor; auto).
  all: simpl; intros.
  all: try rewrite H; try rewrite H0; try rewrite H1; try reflexivity.
  * set_solver.
  * set_solver.
  * case_match; eqb_to_eq; subst; simpl; destruct decide; try set_solver.
  * repeat destruct decide; set_solver.
  * rewrite usedPIDsVal_flat_union_helper. 2: assumption. set_solver.
  * rewrite usedPIDsVal_flat_union_helper_prod. 2: assumption. set_solver.
  * set_solver.
  * set_solver.
  * rewrite usedPIDsClos_flat_union_helper. 2: assumption.
    repeat destruct decide; set_solver.
  * set_solver.
  * rewrite usedPIDsExp_flat_union_helper. 2: assumption. set_solver.
  * clear H H0. repeat destruct decide.
    all: set_solver.
  * rewrite usedPIDsExp_flat_union_helper. 2: assumption. set_solver.
  * rewrite usedPIDsExp_flat_union_helper_prod. 2: assumption. set_solver.
  * rewrite usedPIDsExp_flat_union_helper. 2: assumption.
    repeat destruct decide; set_solver.
  * rewrite usedPIDsExp_flat_union_helper. 2: assumption. set_solver.
  * rewrite usedPIDsExp_flat_union_helper. 2: assumption.
    repeat destruct decide; set_solver.
  * rewrite usedPIDsCase_flat_union_helper. 2: assumption.
    repeat destruct decide; set_solver.
  * clear H H0. repeat destruct decide.
    all: set_solver.
  * clear H H0. repeat destruct decide.
    all: set_solver.
  * rewrite usedPIDsLetRec_flat_union_helper. 2: assumption.
    repeat destruct decide; set_solver.
  * clear H H0 H1. repeat destruct decide.
    all: set_solver.
  * (* EBin *)
    rewrite usedPIDsExp_flat_union_helper. 2: assumption. set_solver.
  * (* ESeg *)
    destruct seg as [v s u t sg en]. simpl in *.
    rewrite H, H0. repeat destruct decide; set_solver.
  * set_solver.
  * set_solver.
  * set_solver.
  * (* PCons *)
    clear H H0. repeat destruct decide.
    all: set_solver.
  * (* PTuple *)
    rewrite usedPIDsPat_flat_union_helper. 2: assumption. set_solver.
  * (* PMap *)
    rewrite usedPIDsPat_flat_union_helper_prod. 2: assumption. set_solver.
  * (* PBin *)
    rewrite usedPIDsPatSeg_flat_union_helper. 2: assumption. set_solver.
  * (* clauses of ECase *)
    constructor; [|assumption].
    intros p p'. split; [|split]; [| apply H0 | apply H1].
    apply usedPIDsPat_flat_union_helper. exact H.
Qed.

Corollary usedPIDsVal_rename :
  (forall v p p',
    usedPIDsVal (renamePIDVal p p' v) = if decide (p ∈ usedPIDsVal v)
                                        then {[p']} ∪ usedPIDsVal v ∖ {[p]}
                                        else usedPIDsVal v ∖ {[p]}).
Proof.
  apply usedPIDs_rename_ind.
Qed.

Corollary usedPIDsExp_rename :
  (forall e p p',
    usedPIDsExp (renamePID p p' e) = if decide (p ∈ usedPIDsExp e)
                                        then {[p']} ∪ usedPIDsExp e ∖ {[p]}
                                        else usedPIDsExp e ∖ {[p]}).
Proof.
  apply usedPIDs_rename_ind.
Qed.

Corollary usedPIDsPat_rename :
  (forall pt p p',
    usedPIDsPat (renamePIDPat p p' pt) = if decide (p ∈ usedPIDsPat pt)
                                        then {[p']} ∪ usedPIDsPat pt ∖ {[p]}
                                        else usedPIDsPat pt ∖ {[p]}).
Proof.
  apply usedPIDs_rename_ind.
Qed.

Lemma usedPIDsPat_flat_union :
  forall l p p',
  flat_union usedPIDsPat (map (renamePIDPat p p') l) =
  if (decide (p ∈ flat_union usedPIDsPat l))
  then {[p']} ∪ flat_union usedPIDsPat l ∖ {[p]}
  else flat_union usedPIDsPat l ∖ {[p]}.
Proof.
  induction l; intros; simpl. set_solver.
  rewrite IHl, usedPIDsPat_rename. repeat destruct decide; set_solver.
Qed.

Lemma usedPIDsVal_flat_union :
  forall l p p',
  flat_union usedPIDsVal (map (renamePIDVal p p') l) =
  if (decide (p ∈ flat_union usedPIDsVal l))
  then {[p']} ∪ flat_union usedPIDsVal l ∖ {[p]}
  else flat_union usedPIDsVal l ∖ {[p]}.
Proof.
  induction l; intros; simpl. set_solver.
  rewrite IHl, usedPIDsVal_rename. repeat destruct decide; set_solver.
Qed.

Corollary usedPIDsRed_rename :
  (forall r p p',
    usedPIDsRed (renamePIDRed p p' r) = if decide (p ∈ usedPIDsRed r)
                                        then {[p']} ∪ usedPIDsRed r ∖ {[p]}
                                        else usedPIDsRed r ∖ {[p]}).
Proof.
  destruct r; simpl; intros.
  * by rewrite usedPIDsExp_rename.
  * by rewrite usedPIDsVal_flat_union.
  * destruct e, p0.
    cbn. do 2 rewrite usedPIDsVal_rename. repeat destruct decide; set_solver.
  * set_solver.
Qed.

Corollary usedPIDsFrameId_rename :
  (forall i p p',
    usedPIDsFrameId (renamePIDFrameId p p' i) = if decide (p ∈ usedPIDsFrameId i)
                                        then {[p']} ∪ usedPIDsFrameId i ∖ {[p]}
                                        else usedPIDsFrameId i ∖ {[p]}).
Proof.
  destruct i; intros; simpl.
  all: try now set_solver.
  * do 2 rewrite usedPIDsVal_rename; repeat destruct decide; set_solver.
  * rewrite usedPIDsVal_rename; repeat destruct decide; set_solver.
Qed.

Corollary usedPIDsFrame_rename :
  (forall f p p',
    usedPIDsFrame (renamePIDFrame p p' f) = if decide (p ∈ usedPIDsFrame f)
                                        then {[p']} ∪ usedPIDsFrame f ∖ {[p]}
                                        else usedPIDsFrame f ∖ {[p]}).
Proof.
  destruct f; intros; simpl.
  * by rewrite usedPIDsExp_rename.
  * by rewrite usedPIDsVal_rename.
  * rewrite usedPIDsFrameId_rename.
    rewrite usedPIDsExp_flat_union_helper.
    rewrite usedPIDsVal_flat_union_helper.
    repeat destruct decide; set_solver.
    1: induction vl; constructor; auto.
    1: apply usedPIDsVal_rename.
    1: induction el; constructor; auto.
    1: apply usedPIDsExp_rename.
  * rewrite usedPIDsExp_flat_union_helper. set_solver.
    induction l; constructor; auto.
    apply usedPIDsExp_rename.
  * rewrite usedPIDsExp_rename, usedPIDsExp_flat_union_helper.
    repeat destruct decide; set_solver.
    1: induction l; constructor; auto.
    1: apply usedPIDsExp_rename.
  * rewrite usedPIDsVal_rename, usedPIDsExp_flat_union_helper.
    repeat destruct decide; set_solver.
    1: induction l; constructor; auto.
    1: apply usedPIDsExp_rename.
  * rewrite usedPIDsCase_flat_union_helper. set_solver.
    1: induction l; constructor; auto. destruct a, p0; intros.
    1: split; [apply usedPIDsPat_flat_union | split; apply usedPIDsExp_rename].
  * rewrite usedPIDsExp_rename, usedPIDsCase_flat_union_helper, usedPIDsVal_flat_union_helper.
    clear. repeat destruct decide; set_solver.
    1: induction lv; constructor; auto.
    1: apply usedPIDsVal_rename.
    1: induction le; constructor; auto. destruct a, p0; intros.
    1: split; [apply usedPIDsPat_flat_union | split; apply usedPIDsExp_rename].
  * by rewrite usedPIDsExp_rename.
  * by rewrite usedPIDsExp_rename.
  * do 2 rewrite usedPIDsExp_rename.
    repeat destruct decide; set_solver.
  * (* FSeg1 *)
    by rewrite usedPIDsExp_rename.
  * (* FSeg2 *)
    by rewrite usedPIDsVal_rename.
Qed.

Lemma usedPIDsFrame_flat_union :
  forall l p p',
  flat_union usedPIDsFrame (map (renamePIDFrame p p') l) =
  if (decide (p ∈ flat_union usedPIDsFrame l))
  then {[p']} ∪ flat_union usedPIDsFrame l ∖ {[p]}
  else flat_union usedPIDsFrame l ∖ {[p]}.
Proof.
  induction l; intros; simpl. set_solver.
  rewrite IHl, usedPIDsFrame_rename. repeat destruct decide; set_solver.
Qed.

Corollary usedPIDsStack_rename :
  (forall fs p p',
    usedPIDsStack (renamePIDStack p p' fs) = if decide (p ∈ usedPIDsStack fs)
                                        then {[p']} ∪ usedPIDsStack fs ∖ {[p]}
                                        else usedPIDsStack fs ∖ {[p]}).
Proof.
  intros. unfold renamePIDStack. by rewrite usedPIDsFrame_flat_union.
Qed.

Lemma renamePID_swap_ind :
  (forall e from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 ->
               renamePID from1 to1 (renamePID from2 to2 e) =
               renamePID from2 to2 (renamePID from1 to1 e)) /\
  (forall e from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 ->
               renamePIDNVal from1 to1 (renamePIDNVal from2 to2 e) =
               renamePIDNVal from2 to2 (renamePIDNVal from1 to1 e)) /\
  (forall e from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 ->
               renamePIDVal from1 to1 (renamePIDVal from2 to2 e) =
               renamePIDVal from2 to2 (renamePIDVal from1 to1 e)) /\
  (forall pt from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 ->
               renamePIDPat from1 to1 (renamePIDPat from2 to2 pt) =
               renamePIDPat from2 to2 (renamePIDPat from1 to1 pt)).
Proof.
  apply Exp_ind with
    (PQ := fun l => Forall (fun pt => forall from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 ->
               renamePIDPat from1 to1 (renamePIDPat from2 to2 pt) =
               renamePIDPat from2 to2 (renamePIDPat from1 to1 pt)) l)
    (PR := fun l => Forall (fun '(p1, p2) => forall from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 ->
               (renamePIDPat from1 to1 (renamePIDPat from2 to2 p1) =
                renamePIDPat from2 to2 (renamePIDPat from1 to1 p1)) /\
               (renamePIDPat from1 to1 (renamePIDPat from2 to2 p2) =
                renamePIDPat from2 to2 (renamePIDPat from1 to1 p2))) l)
    (PT := fun l => Forall (fun seg => forall from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 ->
               (renamePIDPat from1 to1 (renamePIDPat from2 to2 (val seg)) =
                renamePIDPat from2 to2 (renamePIDPat from1 to1 (val seg))) /\
               (renamePIDVal from1 to1 (renamePIDVal from2 to2 (Syntax.size seg)) =
                renamePIDVal from2 to2 (renamePIDVal from1 to1 (Syntax.size seg)))) l)
    (Q := fun l => Forall (fun e => forall from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 ->
               renamePID from1 to1 (renamePID from2 to2 e) =
               renamePID from2 to2 (renamePID from1 to1 e)) l)
    (QV := fun l => Forall (fun e => forall from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 ->
               renamePIDVal from1 to1 (renamePIDVal from2 to2 e) =
               renamePIDVal from2 to2 (renamePIDVal from1 to1 e)) l)
    (R := fun l => Forall (fun '(e1, e2) => forall from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 -> (renamePID from1 to1 (renamePID from2 to2 e1) =
               renamePID from2 to2 (renamePID from1 to1 e1)) /\ (renamePID from1 to1 (renamePID from2 to2 e2) =
               renamePID from2 to2 (renamePID from1 to1 e2))) l)
    (RV := fun l => Forall (fun '(e1, e2) => forall from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 -> (renamePIDVal from1 to1 (renamePIDVal from2 to2 e1) =
               renamePIDVal from2 to2 (renamePIDVal from1 to1 e1)) /\ (renamePIDVal from1 to1 (renamePIDVal from2 to2 e2) =
               renamePIDVal from2 to2 (renamePIDVal from1 to1 e2))) l)
    (VV := fun l => Forall (fun '(_, _, e) => forall from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 ->
               renamePID from1 to1 (renamePID from2 to2 e) =
               renamePID from2 to2 (renamePID from1 to1 e)) l)
    (W := fun l => Forall (fun '(pl,g,e) => forall from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 ->
               (map (renamePIDPat from1 to1) (map (renamePIDPat from2 to2) pl) =
                map (renamePIDPat from2 to2) (map (renamePIDPat from1 to1) pl)) /\
               (renamePID from1 to1 (renamePID from2 to2 g) =
               renamePID from2 to2 (renamePID from1 to1 g)) /\ (renamePID from1 to1 (renamePID from2 to2 e) =
               renamePID from2 to2 (renamePID from1 to1 e))) l)
    (Z := fun l => Forall (fun '(_, e) => forall from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 ->
               renamePID from1 to1 (renamePID from2 to2 e) =
               renamePID from2 to2 (renamePID from1 to1 e)) l).
  all: try now (constructor; auto).
  all: intros; simpl; try rewrite H; try rewrite H0; try rewrite H1; try reflexivity; try assumption.
  * repeat case_match; eqb_to_eq; subst; try lia.
    all: simpl; repeat case_match; eqb_to_eq; subst; try reflexivity; lia.
  * do 2 rewrite map_map. f_equal. apply map_ext_in_iff.
    intros. rewrite Forall_forall in H. apply list_elem_of_In in H3.
    eapply H in H3. exact H3. all: assumption.
  * do 2 rewrite map_map. f_equal. apply map_ext_in_iff.
    intros. rewrite Forall_forall in H. apply list_elem_of_In in H3.
    eapply H in H3. destruct a.
    erewrite (proj1 (H3 _ _ _ _ _ _ _)). erewrite (proj2 (H3 _ _ _ _ _ _ _)).
    reflexivity. Unshelve. all: lia.
  * rewrite H0; try assumption.
    f_equal.
    do 2 rewrite map_map. apply map_ext_in_iff.
    intros. rewrite Forall_forall in H. apply list_elem_of_In in H4.
    eapply H in H4. destruct a, p.
    rewrite H4. reflexivity. all: lia.
  * do 2 rewrite map_map. f_equal. apply map_ext_in_iff.
    intros. rewrite Forall_forall in H. apply list_elem_of_In in H3.
    eapply H in H3. exact H3. all: assumption.
  * do 2 rewrite map_map. f_equal. apply map_ext_in_iff.
    intros. rewrite Forall_forall in H. apply list_elem_of_In in H3.
    eapply H in H3. exact H3. all: assumption.
  * do 2 rewrite map_map. f_equal. apply map_ext_in_iff.
    intros. rewrite Forall_forall in H. apply list_elem_of_In in H3.
    eapply H in H3. destruct a. cbn.
    erewrite (proj1 (H3 _ _ _ _ _ _ _)). erewrite (proj2 (H3 _ _ _ _ _ _ _)).
    reflexivity. Unshelve. all: lia.
  * rewrite H, H0; try assumption.
    do 2 rewrite map_map. f_equal. apply map_ext_in_iff.
    intros. rewrite Forall_forall in H1. apply list_elem_of_In in H5.
    eapply H1 in H5. exact H5. all: lia.
  * do 2 rewrite map_map. f_equal. apply map_ext_in_iff.
    intros. rewrite Forall_forall in H. apply list_elem_of_In in H3.
    eapply H in H3. exact H3. all: assumption.
  * rewrite H; try assumption.
    do 2 rewrite map_map. f_equal. apply map_ext_in_iff.
    intros. rewrite Forall_forall in H0. apply list_elem_of_In in H4.
    eapply H0 in H4. exact H4. all: lia.
  * rewrite H; try assumption.
    f_equal.
    do 2 rewrite map_map. apply map_ext_in_iff.
    intros. rewrite Forall_forall in H0. apply list_elem_of_In in H4.
    eapply H0 in H4. destruct a, p.
    pose proof (H4 from1 from2 to1 to2 ltac:(lia) ltac:(lia) ltac:(lia)) as [Hp [Hg He]].
    cbn. rewrite Hp, Hg, He. reflexivity. all: lia.
  * rewrite H; try assumption.
    f_equal.
    do 2 rewrite map_map. apply map_ext_in_iff.
    intros. rewrite Forall_forall in H0. apply list_elem_of_In in H4.
    eapply H0 in H4. destruct a.
    rewrite H4. reflexivity. all: lia.
  * (* EBin *)
    do 2 rewrite map_map. f_equal. apply map_ext_in_iff.
    intros. rewrite Forall_forall in H. apply list_elem_of_In in H3.
    eapply H in H3. exact H3. all: assumption.
  * (* ESeg *)
    destruct seg as [v s u t sg en]. simpl in *.
    rewrite (H from1 from2 to1 to2), (H0 from1 from2 to1 to2) by lia.
    reflexivity.
  * (* PTuple *)
    do 2 rewrite map_map. f_equal. apply map_ext_in_iff.
    intros. rewrite Forall_forall in H. apply list_elem_of_In in H3.
    eapply H in H3. exact H3. all: assumption.
  * (* PMap *)
    do 2 rewrite map_map. f_equal. apply map_ext_in_iff.
    intros. rewrite Forall_forall in H. apply list_elem_of_In in H3.
    eapply H in H3. destruct a. cbn.
    erewrite (proj1 (H3 _ _ _ _ _ _ _)). erewrite (proj2 (H3 _ _ _ _ _ _ _)).
    reflexivity. Unshelve. all: lia.
  * (* PBin *)
    do 2 rewrite map_map. f_equal. apply map_ext_in_iff.
    intros. rewrite Forall_forall in H. apply list_elem_of_In in H3.
    pose proof (H _ H3 from1 from2 to1 to2 ltac:(lia) ltac:(lia) ltac:(lia)) as [Hp Hs].
    destruct a as [v s u t sg en]. cbn in *.
    rewrite Hp, Hs. reflexivity.
  * (* clauses of ECase *)
    constructor; [|assumption].
    intros from1 from2 to1 to2 N1 N2 N3.
    split; [|split]; [| apply H0; assumption | apply H1; assumption].
    do 2 rewrite map_map. apply map_ext_in_iff.
    intros a Ha. rewrite Forall_forall in H. apply list_elem_of_In in Ha.
    eapply H in Ha. exact Ha. all: assumption.
Qed.

Corollary renamePID_swap_exp :
  forall e from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 ->
               renamePID from1 to1 (renamePID from2 to2 e) =
               renamePID from2 to2 (renamePID from1 to1 e).
Proof.
  apply renamePID_swap_ind.
Qed.

Corollary renamePID_swap_val :
  forall v from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 ->
               renamePIDVal from1 to1 (renamePIDVal from2 to2 v) =
               renamePIDVal from2 to2 (renamePIDVal from1 to1 v).
Proof.
  apply renamePID_swap_ind.
Qed.

Corollary renamePID_swap_pat :
  forall pt from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 ->
               renamePIDPat from1 to1 (renamePIDPat from2 to2 pt) =
               renamePIDPat from2 to2 (renamePIDPat from1 to1 pt).
Proof.
  apply renamePID_swap_ind.
Qed.

Corollary renamePID_swap_pats :
  forall l from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 ->
               map (renamePIDPat from1 to1) (map (renamePIDPat from2 to2) l) =
               map (renamePIDPat from2 to2) (map (renamePIDPat from1 to1) l).
Proof.
  intros. do 2 rewrite map_map. apply map_ext_in_iff.
  intros. by rewrite renamePID_swap_pat.
Qed.

Corollary renamePID_swap_red :
  forall r from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 ->
               renamePIDRed from1 to1 (renamePIDRed from2 to2 r) =
               renamePIDRed from2 to2 (renamePIDRed from1 to1 r).
Proof.
  destruct r; intros; simpl.
  * by rewrite renamePID_swap_exp.
  * do 2 rewrite map_map. f_equal. apply map_ext_in_iff.
    intros. by rewrite renamePID_swap_val.
  * destruct e, p. simpl.
    by rewrite (renamePID_swap_val v), (renamePID_swap_val v0).
  * reflexivity.
Qed.

Corollary renamePID_swap_frameId :
  forall i from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 ->
               renamePIDFrameId from1 to1 (renamePIDFrameId from2 to2 i) =
               renamePIDFrameId from2 to2 (renamePIDFrameId from1 to1 i).
Proof.
  destruct i; intros; simpl; try reflexivity.
  * by rewrite (renamePID_swap_val m), (renamePID_swap_val f).
  * by rewrite renamePID_swap_val.
Qed.

Corollary renamePID_swap_frame :
  forall f from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 ->
               renamePIDFrame from1 to1 (renamePIDFrame from2 to2 f) =
               renamePIDFrame from2 to2 (renamePIDFrame from1 to1 f).
Proof.
  destruct f; intros; simpl; try reflexivity.
  * by rewrite renamePID_swap_exp.
  * by rewrite renamePID_swap_val.
  * rewrite renamePID_swap_frameId; try lia.
    f_equal.
    - do 2 rewrite map_map. apply map_ext_in_iff.
      intros. by rewrite renamePID_swap_val.
    - do 2 rewrite map_map. apply map_ext_in_iff.
      intros. by rewrite renamePID_swap_exp.
  * f_equal. do 2 rewrite map_map. apply map_ext_in_iff.
    intros. by rewrite renamePID_swap_exp.
  * rewrite renamePID_swap_exp; try lia. f_equal.
    do 2 rewrite map_map. apply map_ext_in_iff.
    intros. by rewrite renamePID_swap_exp.
  * rewrite renamePID_swap_val; try lia. f_equal.
    do 2 rewrite map_map. apply map_ext_in_iff.
    intros. by rewrite renamePID_swap_exp.
  * f_equal.
    do 2 rewrite map_map. apply map_ext_in_iff.
    intros. destruct a, p. cbn.
    by rewrite (renamePID_swap_pats l0), (renamePID_swap_exp e0), (renamePID_swap_exp e).
  * rewrite renamePID_swap_exp; try lia. f_equal.
    - do 2 rewrite map_map. apply map_ext_in_iff.
      intros. by rewrite renamePID_swap_val.
    - do 2 rewrite map_map. apply map_ext_in_iff.
      intros. destruct a, p. cbn.
      by rewrite renamePID_swap_pats, (renamePID_swap_exp e0), (renamePID_swap_exp e).
  * by rewrite renamePID_swap_exp.
  * by rewrite renamePID_swap_exp.
  * by rewrite (renamePID_swap_exp e2), (renamePID_swap_exp e3).
  * (* FSeg1 *)
    by rewrite renamePID_swap_exp.
  * (* FSeg2 *)
    by rewrite renamePID_swap_val.
Qed.

Corollary renamePID_swap_stack :
  forall fs from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 ->
               renamePIDStack from1 to1 (renamePIDStack from2 to2 fs) =
               renamePIDStack from2 to2 (renamePIDStack from1 to1 fs).
Proof.
  intros. unfold renamePIDStack.
  do 2 rewrite map_map. apply map_ext_in_iff.
  intros. by rewrite renamePID_swap_frame.
Qed.
