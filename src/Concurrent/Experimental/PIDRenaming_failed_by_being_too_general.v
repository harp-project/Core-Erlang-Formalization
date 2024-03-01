From CoreErlang.FrameStack Require Import SubstSemanticsLemmas.

Import ListNotations.

Definition PIDrenaming := PID -> PID.

Fixpoint renamePID (ρ : PIDrenaming) (e : Exp) : Exp :=
match e with
 | VVal e => VVal (renamePIDVal ρ e)
 | EExp e => EExp (renamePIDNVal ρ e)
end
with renamePIDVal (ρ : PIDrenaming) (v : Val) : Val :=
match v with
 | VNil => VNil
 | VLit l => VLit l
 | VPid p => VPid (ρ p)
 | VCons hd tl => VCons (renamePIDVal ρ hd) (renamePIDVal ρ tl)
 | VTuple l => VTuple (map (renamePIDVal ρ) l)
 | VMap l => VMap (map (fun '(x,y) => (renamePIDVal ρ x, renamePIDVal ρ y)) l)
 | VVar n => VVar n
 | VFunId n => VFunId n
 | VClos ext id params e => VClos (map (fun '(id, vl, e) => (id, vl, renamePID ρ e)) ext) id params (renamePID ρ e)
end
with renamePIDNVal (ρ : PIDrenaming) (n : NonVal) : NonVal :=
match n with
 | EFun vl e => EFun vl (renamePID ρ e)
 | EValues el => EValues (map (renamePID ρ) el)
 | ECons hd tl => ECons (renamePID ρ hd) (renamePID ρ tl)
 | ETuple l => ETuple (map (renamePID ρ) l)
 | EMap l => EMap (map (fun '(x,y) => (renamePID ρ x, renamePID ρ y)) l)
 | ECall m f l => ECall (renamePID ρ m) (renamePID ρ f) (map (renamePID ρ) l)
 | EPrimOp f l => EPrimOp f (map (renamePID ρ) l)
 | EApp exp l => EApp (renamePID ρ exp) (map (renamePID ρ) l)
 | ECase e l => ECase (renamePID ρ e)
                      (map (fun '(p, g, e) => (p, renamePID ρ g, renamePID ρ e)) l)
 | ELet l e1 e2 => ELet l (renamePID ρ e1) (renamePID ρ e2)
 | ESeq e1 e2 => ESeq (renamePID ρ e1) (renamePID ρ e2)
 | ELetRec l e => ELetRec (map (fun '(vl, e) => (vl, renamePID ρ e)) l)
                          (renamePID ρ e)
 | ETry e1 vl1 e2 vl2 e3 => ETry (renamePID ρ e1)
                                 vl1 (renamePID ρ e2)
                                 vl2 (renamePID ρ e3)
end.

Notation "e .[ 'pid' : ρ ]" := (renamePID ρ e) (at level 2).
Notation "e .[ 'pid' : ρ ]ᵥ" := (renamePIDVal ρ e) (at level 2).
Notation "e .[ 'pid' : ρ ]ₙ" := (renamePIDNVal ρ e) (at level 2).

Definition update {B : Type} (k : nat) (v : B) (f : nat -> B) : nat -> B :=
  fun x =>
    if x =? k
    then v
    else f x.

Definition update_list {B : Type} (f : nat -> B) (l : list (nat * B)) : nat -> B :=
  fold_left (fun acc '(k, v) => update k v acc) l f.

Definition renamePIDRed (ρ : PIDrenaming) (r : Redex) : Redex :=
match r with
 | RExp e => RExp (renamePID ρ e)
 | RValSeq vs => RValSeq (map (renamePIDVal ρ) vs)
 | RExc (class, reas, det) => RExc (class, renamePIDVal ρ reas,
                                           renamePIDVal ρ det)
 | RBox => RBox
end.

Notation "e .[ 'pid' : ρ ]ᵣ" := (renamePIDRed ρ e) (at level 2).

Definition renamePIDFrameId (ρ : PIDrenaming) (f : FrameIdent) : FrameIdent :=
match f with
 | IValues => f
 | ITuple => f
 | IMap => f
 | ICall m f => ICall (renamePIDVal ρ m) (renamePIDVal ρ f)
 | IPrimOp f => IPrimOp f
 | IApp v => IApp (renamePIDVal ρ v)
end.

Notation "e .[ 'pid' : ρ ]ᵢ" := (renamePIDFrameId ρ e) (at level 2).

Definition renamePIDFrame (ρ : PIDrenaming) (f : Frame) : Frame :=
match f with
 | FCons1 hd => FCons1 (renamePID ρ hd)
 | FCons2 tl => FCons2 (renamePIDVal ρ tl)
 | FParams ident vl el =>
     FParams (renamePIDFrameId ρ ident) (map (renamePIDVal ρ) vl)
                                                (map (renamePID ρ) el)
 | FApp1 l => FApp1 (map (renamePID ρ) l)
 | FCallMod f l => FCallMod (renamePID ρ f) (map (renamePID ρ) l)
 | FCallFun m l => FCallFun (renamePIDVal ρ m) (map (renamePID ρ) l)
 | FCase1 l => FCase1 (map (fun '(p, g, e) => (p, renamePID ρ g, renamePID ρ e)) l)
 | FCase2 lv ex le =>
   FCase2
     (map (renamePIDVal ρ) lv)
     (renamePID ρ ex)
     (map (fun '(p, g, e) => (p, renamePID ρ g, renamePID ρ e)) le)
 | FLet l e => FLet l (renamePID ρ e)
 | FSeq e => FSeq (renamePID ρ e)
 | FTry vl1 e2 vl2 e3 => FTry vl1 (renamePID ρ e2)
                              vl2 (renamePID ρ e3)
end.

Notation "e .[ 'pid' : ρ ]ᶠ" := (renamePIDFrame ρ e) (at level 2). (* couldn't find lower index f unicode *)

Definition renamePIDStack (ρ : PIDrenaming) (fs : FrameStack) :=
  map (renamePIDFrame ρ) fs.

Notation "e .[ 'pid' : ρ ]ₖ" := (renamePIDStack ρ e) (at level 2).

Lemma renamePID_preserves_scope :
  (forall Γ e, EXP Γ ⊢ e -> forall ρ, EXP Γ ⊢ renamePID ρ e) /\
  (forall Γ e, VAL Γ ⊢ e -> forall ρ, VAL Γ ⊢ renamePIDVal ρ e) /\
  (forall Γ e, NVAL Γ ⊢ e -> forall ρ, NVAL Γ ⊢ renamePIDNVal ρ e).
Proof.
  apply scoped_ind; intros; cbn; try now constructor.
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
                 (p, renamePID ρ g, renamePID ρ e3)))) (d := ([], ˝VNil, ˝VNil)).
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
                 (p, renamePID ρ g, renamePID ρ e3)))) (d := ([], ˝VNil, ˝VNil)).
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

Definition renamePID_subst (ρ : PIDrenaming) (σ : Substitution) : Substitution :=
  fun x =>
    match σ x with
    | inl val => inl (renamePIDVal ρ val)
    | r => r
    end.

Notation "σ >>>ₚ ρ" := (renamePID_subst ρ σ) (at level 2).

Theorem rename_renamePID :
  (forall e ρ ρₚ, rename ρ (renamePID ρₚ e) =
                      renamePID ρₚ (rename ρ e)) /\
  (forall e ρ ρₚ, renameNonVal ρ (renamePIDNVal ρₚ e) =
                      renamePIDNVal ρₚ (renameNonVal ρ e)) /\
  (forall e ρ ρₚ, renameVal ρ (renamePIDVal ρₚ e) =
                      renamePIDVal ρₚ (renameVal ρ e)).
Proof.
  eapply Exp_ind with
    (QV := fun l => Forall (fun e => forall ρ ρₚ, renameVal ρ (renamePIDVal ρₚ e) =
                      renamePIDVal ρₚ (renameVal ρ e)) l)
    (Q := fun l => Forall (fun e => forall ρ ρₚ, rename ρ (renamePID ρₚ e) =
                      renamePID ρₚ (rename ρ e)) l)
    (RV := fun l => Forall (fun '(e1, e2) => forall ρ ρₚ, renameVal ρ (renamePIDVal ρₚ e1) =
                      renamePIDVal ρₚ (renameVal ρ e1) /\
         renameVal ρ (renamePIDVal ρₚ e2) =
                      renamePIDVal ρₚ (renameVal ρ e2)) l)
    (R := fun l => Forall (fun '(e1, e2) => forall ρ ρₚ, rename ρ (renamePID ρₚ e1) =
                      renamePID ρₚ (rename ρ e1) /\
         rename ρ (renamePID ρₚ e2) =
                      renamePID ρₚ (rename ρ e2)) l)
    (W := fun l => Forall (fun '(p, g, e) => forall ρ ρₚ,
       rename ρ (renamePID ρₚ g) =
                      renamePID ρₚ (rename ρ g) /\
       rename ρ (renamePID ρₚ e) =
                      renamePID ρₚ (rename ρ e)) l)
    (Z := fun l => Forall (fun '(n, e) => forall ρ ρₚ, rename ρ (renamePID ρₚ e) =
                      renamePID ρₚ (rename ρ e)) l)
   (VV := fun l => Forall
      (fun '(id, vl, e) => forall ρ ρₚ, rename ρ (renamePID ρₚ e) =
                      renamePID ρₚ (rename ρ e)) l)
  ; intros.
  all: cbn; auto.
  1-2: now rewrite H.
  * now rewrite H, H0.
  * f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto.
  * f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto. destruct x.
    specialize (H ρ ρₚ) as [H_1 H_2]. now rewrite H_1, H_2.
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
    specialize (H ρ ρₚ) as [H_1 H_2]. now rewrite H_1, H_2.
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
      now rewrite (proj1 (H1 _ _)), (proj2 (H1 _ _)).
  * now rewrite H, H0.
  * now rewrite H, H0.
  * f_equal.
    - do 2 rewrite map_map. apply map_ext_Forall.
      rewrite Forall_nth in *. intros. eapply (H0 _ d) in H1. destruct nth.
      rewrite (H1 _ _). now rewrite map_length.
    - rewrite H. now rewrite map_length.
  * now rewrite H, H0, H1.
Qed.

Lemma renamePID_subst_up :
  forall σ ρ, up_subst (renamePID_subst ρ σ) =
                    renamePID_subst ρ (up_subst σ).
Proof.
  unfold renamePID_subst, up_subst. intros.
  extensionality x. destruct x; auto.
  unfold shift. destruct σ; auto.
  now rewrite (proj2 (proj2 rename_renamePID)).
Qed.

Corollary renamePID_upn :
  forall n σ ρ, upn n (renamePID_subst ρ σ) =
                      renamePID_subst ρ (upn n σ).
Proof.
  induction n; intros; simpl; auto.
  now rewrite IHn, renamePID_subst_up.
Qed.

Theorem split_renamePID_subst :
     (forall e ρ σ, renamePID ρ e.[σ] = 
       (renamePID ρ e).[renamePID_subst ρ σ])
  /\ (forall e ρ σ, renamePIDNVal ρ e.[σ]ₑ = 
       (renamePIDNVal ρ e).[renamePID_subst ρ σ]ₑ)
  /\ (forall e ρ σ, renamePIDVal ρ e.[σ]ᵥ = 
       (renamePIDVal ρ e).[renamePID_subst ρ σ]ᵥ).
Proof.
  eapply Exp_ind with
    (QV := fun l => Forall (fun e => forall ρ σ, renamePIDVal ρ e.[σ]ᵥ = 
       (renamePIDVal ρ e).[renamePID_subst ρ σ]ᵥ) l)
    (Q := fun l => Forall (fun e => forall ρ σ, renamePID ρ e.[σ] = 
       (renamePID ρ e).[renamePID_subst ρ σ]) l)
    (RV := fun l => Forall (fun '(e1, e2) => forall ρ σ, renamePIDVal ρ e1.[σ]ᵥ = 
       (renamePIDVal ρ e1).[renamePID_subst ρ σ]ᵥ /\
         renamePIDVal ρ e2.[σ]ᵥ = 
       (renamePIDVal ρ e2).[renamePID_subst ρ σ]ᵥ) l)
    (R := fun l => Forall (fun '(e1, e2) => forall ρ σ, renamePID ρ e1.[σ] = 
       (renamePID ρ e1).[renamePID_subst ρ σ] /\
         renamePID ρ e2.[σ] = 
       (renamePID ρ e2).[renamePID_subst ρ σ]) l)
    (W := fun l => Forall (fun '(p, g, e) => forall ρ σ,
       renamePID ρ g.[σ] =
       (renamePID ρ g).[(renamePID_subst ρ σ)] /\
       renamePID ρ e.[σ] = 
       (renamePID ρ e).[(renamePID_subst ρ σ)]) l)
    (Z := fun l => Forall (fun '(n, e) => forall ρ σ, renamePID ρ e.[σ] = 
       (renamePID ρ e).[(renamePID_subst ρ σ)]) l)
   (VV := fun l => Forall
      (fun '(id, vl, e) => forall ρ σ, renamePID ρ e.[σ] = 
       (renamePID ρ e).[(renamePID_subst ρ σ)]) l)
  ; intros.
  all: cbn; auto.
  1-2: now rewrite H.
  * now rewrite H, H0.
  * f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto.
  * f_equal. do 2 rewrite map_map. apply map_ext_Forall.
    induction H; constructor; auto. destruct x.
    specialize (H ρ σ) as [H_1 H_2]. now rewrite H_1, H_2.
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
    specialize (H ρ σ) as [H_1 H_2]. now rewrite H_1, H_2.
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
      rewrite (proj1 (H1 _ _)), (proj2 (H1 _ _)). now rewrite renamePID_upn.
  * rewrite H, H0. now rewrite renamePID_upn.
  * now rewrite H, H0.
  * f_equal.
    - do 2 rewrite map_map. apply map_ext_Forall.
      rewrite Forall_nth in *. intros. eapply (H0 _ d) in H1. destruct nth.
      rewrite (H1 _ _). now rewrite renamePID_upn, map_length.
    - rewrite H. now rewrite map_length, renamePID_upn.
  * rewrite H, H0, H1. now repeat rewrite renamePID_upn.
Qed.

Corollary split_renamePID_subst_exp :
  (forall e ρ σ, renamePID ρ e.[σ] = 
    (renamePID ρ e).[renamePID_subst ρ σ]).
Proof.
  apply split_renamePID_subst.
Qed.

Corollary split_renamePID_subst_val :
  (forall e ρ σ, renamePIDVal ρ e.[σ]ᵥ = 
       (renamePIDVal ρ e).[renamePID_subst ρ σ]ᵥ).
Proof.
  apply split_renamePID_subst.
Qed.

Proposition renamePID_subst_id :
  forall ρ, renamePID_subst ρ idsubst = idsubst.
Proof.
  now intros.
Qed.

Proposition renamePID_subst_list_subst :
  forall vs ρ σ,
    renamePID_subst ρ (list_subst vs σ) =
    list_subst (map (renamePIDVal ρ) vs) (renamePID_subst ρ σ).
Proof.
  induction vs; simpl; intros; auto.
  rewrite <- IHvs. clear. unfold scons, renamePID_subst.
  extensionality x. destruct x; auto.
Qed.

Proposition rename_subst_flatten_list :
  forall el ρ, 
    map (renamePID ρ) (flatten_list el) =
    flatten_list (map (fun '(x, y) => (renamePID ρ x, renamePID ρ y)) el).
Proof.
  induction el using list_length_ind; destruct el; intros; simpl; auto.
  destruct p. simpl. do 2 f_equal. rewrite H. reflexivity. slia.
Qed.

Proposition rename_subst_deflatten_list_val :
  forall el ρ, 
    map (fun '(x, y) => (renamePIDVal ρ x, renamePIDVal ρ y)) (deflatten_list el) =
    deflatten_list (map (renamePIDVal ρ) el).
Proof.
  induction el using list_length_ind; destruct el; intros; simpl; auto.
  destruct el; auto. simpl.
  do 2 f_equal. rewrite H. reflexivity. slia.
Qed.

Proposition renamePID_match_pattern :
  forall p v vs', match_pattern p v = Some vs' ->
    forall ρ,
      match_pattern p (renamePIDVal ρ v) = Some (map (renamePIDVal ρ) vs').
Proof.
  induction p using Pat_ind2
    with (Q := fun l => Forall (fun p => forall v vs', match_pattern p v = Some vs' ->
    forall ρ,
      match_pattern p (renamePIDVal ρ v) = Some (map (renamePIDVal ρ) vs')) l)
      (R := fun l => Forall (PBoth (fun p => forall v vs', match_pattern p v = Some vs' ->
    forall ρ,
      match_pattern p (renamePIDVal ρ v) = Some (map (renamePIDVal ρ) vs'))) l); try destruct v; simpl; intros; try inv H; simpl; auto.
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
    forall ρ,
      match_pattern p (renamePIDVal ρ v) = None.
Proof.
  induction p using Pat_ind2
    with (Q := fun l => Forall (fun p => forall v, match_pattern p v = None ->
    forall ρ,
      match_pattern p (renamePIDVal ρ v) = None) l)
      (R := fun l => Forall (PBoth (fun p => forall v, match_pattern p v = None ->
    forall ρ,
      match_pattern p (renamePIDVal ρ v) = None)) l); try destruct v; simpl; intros; try now (inv H; simpl; auto).
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
    forall ρ,
      match_pattern_list lp (map (renamePIDVal ρ) vs) = Some (map (renamePIDVal ρ) vs').
Proof.
  induction lp; destruct vs; simpl; intros; try congruence.
  * now inv H.
  * break_match_hyp. 2: congruence. break_match_hyp. 2: congruence.
    eapply renamePID_match_pattern in Heqo. rewrite Heqo. inv H.
    eapply IHlp in Heqo0. rewrite Heqo0. now rewrite map_app.
Qed.

Corollary renamePID_nomatch_pattern_list :
  forall lp vs, match_pattern_list lp vs = None ->
    forall ρ,
      match_pattern_list lp (map (renamePIDVal ρ) vs) = None.
Proof.
  induction lp; destruct vs; simpl; intros; try congruence.
  break_match_hyp. break_match_hyp. congruence.
  * eapply IHlp in Heqo0. eapply renamePID_match_pattern in Heqo.
    now rewrite Heqo, Heqo0.
  * eapply renamePID_nomatch_pattern in Heqo. now rewrite Heqo.
Qed.

Proposition renamePID_Val_eqb :
  forall v v' ρ, v =ᵥ v' = renamePIDVal ρ v =ᵥ renamePIDVal ρ v'.
Proof.
  valinduction; try destruct v'; intros; simpl; auto.
  all: try now destruct Nat.eqb eqn:P.
  * erewrite IHv1, IHv2. reflexivity.
  * revert l0. induction IHv; destruct l0; simpl; auto.
    now erewrite IHIHv, H.
  * revert l0. induction IHv; destruct l0; simpl; auto.
    - destruct x; auto.
    - destruct x; simpl. destruct H, p. simpl in *. now erewrite IHIHv, H, H0.
Qed.

Proposition renamePID_Val_ltb :
  forall v v' ρ, v <ᵥ v' = renamePIDVal ρ v <ᵥ renamePIDVal ρ v'.
Proof.
  valinduction; try destruct v'; intros; simpl; auto.
  all: try now destruct Nat.eqb eqn:P.
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
  forall vs ρ,
  map (fun '(x, y) => (renamePIDVal ρ x, renamePIDVal ρ y))
         (make_val_map vs) =
  make_val_map (map (fun '(x, y) => (renamePIDVal ρ x, renamePIDVal ρ y))
         vs).
Proof.
  induction vs; intros; simpl; auto.
  destruct a. specialize (IHvs ρ).
  rewrite <- IHvs. clear IHvs.
  (* map_insert *)
  remember (make_val_map vs) as vl. clear Heqvl vs.
  revert v v0 ρ.
  induction vl; intros; simpl; auto.
  destruct a. erewrite (renamePID_Val_eqb _ _ ρ), (renamePID_Val_ltb _ _ ρ).
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
    forall ρ,
      eval_arith m f (map (renamePIDVal ρ) vs) = renamePIDRed ρ r.
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
    forall ρ,
      eval_logical m f (map (renamePIDVal ρ) vs) = renamePIDRed ρ r.
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
    forall ρ,
      eval_equality m f (map (renamePIDVal ρ) vs) = renamePIDRed ρ r.
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
    forall ρ,
      eval_cmp m f (map (renamePIDVal ρ) vs) = renamePIDRed ρ r.
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
    forall ρ,
      eval_hd_tl m f (map (renamePIDVal ρ) vs) = renamePIDRed ρ r.
Proof.
  intros. unfold eval_hd_tl in *. break_match_goal; inv H; try reflexivity; clear Heqb.
  all: destruct vs; simpl; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  all: destruct v; try reflexivity; simpl; destruct Nat.eqb; try reflexivity.
Qed.

Lemma renamePID_eval_check :
  forall m f vs r,
    eval_check m f vs = r ->
    forall ρ,
      eval_check m f (map (renamePIDVal ρ) vs) = renamePIDRed ρ r.
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
    forall ρ,
      eval_funinfo (map (renamePIDVal ρ) vs) = renamePIDRed ρ r.
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
    all: break_match_hyp; erewrite renamePID_Val_eqb in Heqb; rewrite Heqb.
    all: cbn; try reflexivity.
Qed.

Lemma renamePID_eval_transform_list :
  forall m f vs r,
    eval_transform_list m f vs = r ->
    forall ρ,
      eval_transform_list m f (map (renamePIDVal ρ) vs) = renamePIDRed ρ r.
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
    forall ρ,
      eval_elem_tuple m f (map (renamePIDVal ρ) vs) = renamePIDRed ρ r.
Proof.
  intros. unfold eval_elem_tuple in *.
  break_match_goal; inv H; try reflexivity; clear Heqb.
  all: destruct vs; simpl; try reflexivity.
  all: destruct v; simpl; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  all: try destruct vs; simpl; try reflexivity.
  all: try destruct_eqb_in_if Heq; try reflexivity.
  all: try destruct vs; simpl; try reflexivity.
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
    forall ρ,
      eval_list_tuple m f (map (renamePIDVal ρ) vs) = renamePIDRed ρ r.
Proof.
  intros. unfold eval_list_tuple in *.
  break_match_goal; inv H; try reflexivity; clear Heqb.
  all: destruct vs; simpl; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  * clear H0. destruct v; simpl; try reflexivity.
    induction l; simpl; auto.
    inv IHl. now rewrite H0.
  * clear H0. induction v; simpl; try reflexivity.
    Opaque transform_list.
    destruct v2; try reflexivity; simpl.

    clear IHv1. simpl in IHv2.
    break_match_hyp; break_match_hyp; inv IHv2; try reflexivity.
    destruct e, p. congruence.
    destruct e0, p; inv H0. reflexivity.
    Transparent transform_list.
Qed.

Lemma renamePID_eval_length :
  forall vs r,
    eval_length vs = r ->
    forall ρ,
      eval_length (map (renamePIDVal ρ) vs) = renamePIDRed ρ r.
Proof.
  intros. unfold eval_length in *.
  rewrite <- H. clear H.
  all: destruct vs; simpl; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  induction v; simpl; try reflexivity.
  clear IHv1. destruct (_ (v2 .[ pid : ρ ]ᵥ)) eqn:P.
  break_match_hyp. all: inv IHv2.
  * now destruct z0.
  * break_match_hyp; inv H0. reflexivity.
Qed.

Lemma renamePID_eval_tuple_size :
  forall vs r,
    eval_tuple_size vs = r ->
    forall ρ,
      eval_tuple_size (map (renamePIDVal ρ) vs) = renamePIDRed ρ r.
Proof.
  intros. unfold eval_tuple_size in *.
  rewrite <- H. clear H.
  all: destruct vs; simpl; try reflexivity.
  all: destruct vs; simpl; try reflexivity.
  all: destruct v; try reflexivity.
  all: simpl.
  now rewrite map_length.
Qed.

Lemma renamePID_eval_io :
  forall m f vs eff r eff',
    eval_io m f vs eff = (r, eff') ->
    forall ρ,
      eval_io m f (map (renamePIDVal ρ) vs) (map (fun '(a, b) => (a, map (renamePIDVal ρ) b)) eff) =
        (renamePIDRed ρ r, map (fun '(a, b) => (a, map (renamePIDVal ρ) b)) eff').
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
    forall ρ,
      eval_concurrent m f (map (renamePIDVal ρ) vs) = Some (class, renamePIDVal ρ reas, renamePIDVal ρ det).
Proof.
  intros. unfold eval_concurrent in *. break_match_goal; inv H; clear Heqb; try reflexivity.
  all: destruct vs; inv H1; simpl; try reflexivity.
  all: destruct vs; inv H0; simpl; try reflexivity.
Qed.


Lemma renamePID_eval_error :
  forall m f vs class reas det,
    eval_error m f vs = Some (class, reas, det) ->
    forall ρ,
      eval_error m f (map (renamePIDVal ρ) vs) = Some (class, renamePIDVal ρ reas, renamePIDVal ρ det).
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
    forall ρ,
      eval m f (map (renamePIDVal ρ) vs) (map (fun '(a, b) => (a, map (renamePIDVal ρ) b)) eff) =
        Some (renamePIDRed ρ r, map (fun '(a, b) => (a, map (renamePIDVal ρ) b)) eff').
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
    forall ρ,
      primop_eval f (map (renamePIDVal ρ) vs) (map (fun '(a, b) => (a, map (renamePIDVal ρ) b)) eff) = Some (renamePIDRed ρ r, map (fun '(a, b) => (a, map (renamePIDVal ρ) b)) eff').
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
    forall ρ, create_result (renamePIDFrameId ρ ident)
                                  (map (renamePIDVal ρ) vs) (map (fun '(a, b) => (a, map (renamePIDVal ρ) b)) eff) =
                                  Some (renamePIDRed ρ r, map (fun '(a, b) => (a, map (renamePIDVal ρ) b)) eff').
Proof.
  intros. destruct ident; simpl in *.
  * now inv H.
  * now inv H.
  * inv H. cbn.
    now rewrite <- rename_subst_deflatten_list_val, renamePID_make_val_map.
  * destruct m, f; simpl in *; inv H; auto.
    all: try destruct l; try destruct l0; try inv H1; auto.
    eapply renamePID_eval in H0. simpl in H0. exact H0.
  * eapply renamePID_primop_eval in H. exact H.
  * rewrite map_length.
    destruct v; simpl. all: try now inv H.
    break_match_hyp; try now inv H.
    inv H. simpl. rewrite split_renamePID_subst_exp, renamePID_subst_list_subst.
    unfold convert_to_closlist. repeat f_equal.
    rewrite map_map, map_app. f_equal. rewrite map_map.
    f_equal. extensionality x. destruct x, p. cbn. f_equal.
Qed.

Theorem renamePID_is_preserved :
  forall fs r fs' r', ⟨fs, r⟩ --> ⟨fs', r'⟩ ->
    forall ρ,
      ⟨renamePIDStack ρ fs, renamePIDRed ρ r⟩ -->
      ⟨renamePIDStack ρ fs', renamePIDRed ρ r'⟩.
Proof.
  intros. inv H; cbn; try now constructor.
  * constructor. now apply renamePID_preserves_scope.
  * rewrite map_app. constructor.
  * constructor. destruct ident; cbn; congruence.
  * econstructor.
    - destruct ident; cbn; congruence.
    - eapply eq_sym, renamePID_create_result in H1. symmetry. eassumption.
  * econstructor.
    - replace (map (renamePIDVal ρ) vl ++ [renamePIDVal ρ v]) with
              (map (renamePIDVal ρ) (vl ++ [v])) by now rewrite map_app.
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

Fixpoint usedPIDsExp (e : Exp) : list PID :=
match e with
 | VVal e => usedPIDsVal e
 | EExp e => usedPIDsNVal e
end
with usedPIDsVal (v : Val) : list PID :=
match v with
 | VNil => []
 | VLit l => []
 | VPid p => [p]
 | VCons hd tl => usedPIDsVal hd ++ usedPIDsVal tl
 | VTuple l => fold_right (fun x acc => usedPIDsVal x ++ acc) [] l
 | VMap l =>
   fold_right (fun x acc => (usedPIDsVal x.1 ++ usedPIDsVal x.2) ++ acc) [] l
 | VVar n => []
 | VFunId n => []
 | VClos ext id params e => 
   fold_right (fun x acc => usedPIDsExp (snd x) ++ acc) (usedPIDsExp e) ext
end

with usedPIDsNVal (n : NonVal) : list PID :=
match n with
 | EFun vl e => usedPIDsExp e
 | EValues el => fold_right (fun x acc => usedPIDsExp x ++ acc) [] el
 | ECons hd tl => usedPIDsExp hd ++ usedPIDsExp tl
 | ETuple l => fold_right (fun x acc => usedPIDsExp x ++ acc) [] l
 | EMap l =>
   fold_right (fun x acc => (usedPIDsExp x.1 ++ usedPIDsExp x.2) ++ acc) [] l
 | ECall m f l => fold_right (fun x acc => usedPIDsExp x ++ acc)
                             (usedPIDsExp m ++ usedPIDsExp f) l
 | EPrimOp f l => fold_right (fun x acc => usedPIDsExp x ++ acc) [] l
 | EApp exp l => fold_right (fun x acc => usedPIDsExp x ++ acc) (usedPIDsExp exp) l
 | ECase e l => fold_right (fun x acc => (usedPIDsExp x.1.2 ++ usedPIDsExp x.2) ++ acc) (usedPIDsExp e) l
 | ELet l e1 e2 => usedPIDsExp e1 ++ usedPIDsExp e2
 | ESeq e1 e2 => usedPIDsExp e1 ++ usedPIDsExp e2
 | ELetRec l e => fold_right (fun x acc => usedPIDsExp x.2 ++ acc) (usedPIDsExp e) l
 | ETry e1 vl1 e2 vl2 e3 => usedPIDsExp e1 ++ usedPIDsExp e2 ++ usedPIDsExp e3
end.

Definition usedPIDsRed (r : Redex) : list PID :=
match r with
 | RExp e => usedPIDsExp e
 | RValSeq vs => fold_right (fun x acc => usedPIDsVal x ++ acc) [] vs
 | RExc e => usedPIDsVal e.1.2 ++ usedPIDsVal e.2
 | RBox => []
end.

Definition usedPIDsFrameId (i : FrameIdent) : list PID :=
match i with
 | IValues => []
 | ITuple => []
 | IMap => []
 | ICall m f => usedPIDsVal m ++ usedPIDsVal f
 | IPrimOp f => []
 | IApp v => usedPIDsVal v
end.

Definition usedPIDsFrame (f : Frame) : list PID :=
match f with
 | FCons1 hd => usedPIDsExp hd
 | FCons2 tl => usedPIDsVal tl
 | FParams ident vl el => usedPIDsFrameId ident ++
                          fold_right (fun x acc => usedPIDsVal x ++ acc) [] vl ++
                          fold_right (fun x acc => usedPIDsExp x ++ acc) [] el
 | FApp1 l => fold_right (fun x acc => usedPIDsExp x ++ acc) [] l
 | FCallMod f l => fold_right (fun x acc => usedPIDsExp x ++ acc) (usedPIDsExp f) l
 | FCallFun m l => fold_right (fun x acc => usedPIDsExp x ++ acc) (usedPIDsVal m) l
 | FCase1 l => fold_right (fun x acc => (usedPIDsExp x.1.2 ++ usedPIDsExp x.2) ++ acc)
                          [] l
 | FCase2 lv ex le =>
   fold_right (fun x acc => usedPIDsVal x ++ acc) [] lv ++
   fold_right (fun x acc => (usedPIDsExp x.1.2 ++ usedPIDsExp x.2) ++ acc)
              (usedPIDsExp ex) le
 | FLet l e => usedPIDsExp e
 | FSeq e => usedPIDsExp e
 | FTry vl1 e2 vl2 e3 => usedPIDsExp e2 ++ usedPIDsExp e3
end.

Definition usedPIDsStack (fs : FrameStack) : list PID :=
  fold_right (fun x acc => usedPIDsFrame x ++ acc) [] fs.

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

(*
Local Theorem isNotUsed_renamePID_ind :
  (forall e from ρ, ~In from (usedPIDsExp e) -> renamePID ρ e = e) /\
  (forall e ρ, ~In from (usedPIDsNVal e) -> renamePIDNVal ρ e = e) /\
  (forall e ρ, ~In from (usedPIDsVal e) -> renamePIDVal ρ e = e).
Proof.
  apply Exp_ind with
    (QV := fun l => Forall (fun e => forall ρ, ~In from (usedPIDsVal e) -> renamePIDVal ρ e = e) l)
    (Q := fun l => Forall (fun e => forall ρ, ~In from (usedPIDsExp e) -> renamePID ρ e = e) l)
    (RV := fun l => Forall (fun '(e1, e2) => forall ρ,
        (~In from (usedPIDsVal e1) -> renamePIDVal ρ e1 = e1) /\
        (~In from (usedPIDsVal e2) -> renamePIDVal ρ e2 = e2)) l)
    (R := fun l => Forall (fun '(e1, e2) => forall ρ,
        (~In from (usedPIDsExp e1) -> renamePID ρ e1 = e1) /\
        (~In from (usedPIDsExp e2) -> renamePID ρ e2 = e2)) l)
    (W := fun l => Forall (fun '(p, g, e) => forall ρ,
       (~In from (usedPIDsExp g) -> renamePID ρ g = g) /\
       (~In from (usedPIDsExp e) -> renamePID ρ e = e)) l)
    (Z := fun l => Forall (fun '(n, e) => forall ρ, ~In from (usedPIDsExp e) -> renamePID ρ e = e) l)
   (VV := fun l => Forall
      (fun '(id, vl, e) => forall ρ, ~In from (usedPIDsExp e) -> renamePID ρ e = e) l); intros; simpl; try reflexivity.
  all: try now intuition.
  all: try now (rewrite H; try rewrite H0; auto; simpl in *; auto).
  all: simpl in *; destruct_not_in.
  * simpl in H. break_match_goal. 2: reflexivity.
    apply Nat.eqb_eq in Heqb. subst. lia.
  * now rewrite H, H0.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext_in.
    rewrite Forall_forall in H. intros. eapply H in H1 as P. now erewrite P.
    simpl in H0.
    eapply foldr_not_in_Forall in H0 as [H0 _].
    rewrite Forall_forall in H0. now apply H0.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext_in.
    rewrite Forall_forall in H. intros. eapply H in H1 as P. destruct a.
    simpl in H0.
    eapply foldr_not_in_Forall in H0 as [H0 _].
    rewrite Forall_forall in H0. apply H0 in H1. destruct_not_in.
    erewrite (proj1 (P _ _)). erewrite (proj2 (P _ _)). reflexivity.
    all: assumption.
  * eapply foldr_not_in_Forall in H1 as [H1 H1D].
    rewrite H0. 2: assumption. f_equal.
    rewrite <- (map_id ext) at 2. apply map_ext_in. intros.
    rewrite Forall_forall in H1.
    rewrite Forall_forall in H. intros. eapply H in H2 as P.
    destruct a, p. simpl in *. rewrite P. reflexivity. now apply (H1 (n, n0, e0)).
  * f_equal. rewrite <- (map_id el) at 2. apply map_ext_in.
    rewrite Forall_forall in H. intros. eapply H in H1 as P. now erewrite P.
    simpl in H0. eapply foldr_not_in_Forall in H0 as [H0 _].
    rewrite Forall_forall in H0. now apply H0.
  * simpl in *. destruct_bools. now rewrite H, H0.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext_in.
    rewrite Forall_forall in H. intros. eapply H in H1 as P. now erewrite P.
    simpl in H0. eapply foldr_not_in_Forall in H0 as [H0 _].
    rewrite Forall_forall in H0. now apply H0.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext_in.
    rewrite Forall_forall in H. intros. eapply H in H1 as P. destruct a.
    simpl in H0.
    eapply foldr_not_in_Forall in H0 as [H0 _].
    rewrite Forall_forall in H0. apply H0 in H1. destruct_not_in.
    erewrite (proj1 (P _ _)). erewrite (proj2 (P _ _)). reflexivity.
    all: assumption.
  * eapply foldr_not_in_Forall in H2 as [H2 H2D]. destruct_not_in.
    rewrite H, H0 by assumption.
    f_equal. rewrite <- (map_id l) at 2. apply map_ext_in.
    rewrite Forall_forall in H1. intros. eapply H1 in H5 as P.
    rewrite P. reflexivity. rewrite Forall_forall in H2. now apply H2.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext_in.
    rewrite Forall_forall in H. intros. eapply H in H1 as P. now erewrite P.
    simpl in H0. eapply foldr_not_in_Forall in H0 as [H0 _].
    rewrite Forall_forall in H0. now apply H0.
  * eapply foldr_not_in_Forall in H1 as [H1 H1D]. rewrite H by assumption.
    f_equal. rewrite <- (map_id l) at 2. apply map_ext_in.
    rewrite Forall_forall in H1, H0. intros. eapply H0 in H1 as P; eauto.
  * eapply foldr_not_in_Forall in H1 as [H1 H1D]. rewrite H by assumption.
    f_equal. rewrite <- (map_id l) at 2. apply map_ext_in.
    rewrite Forall_forall in H1, H0. intros. eapply H0 in H2 as P; eauto.
    destruct a, p.
    rewrite (proj1 (P _ _)), (proj2 (P _ _)); eauto.
    all: specialize (H1 (l0, e1, e0) H2); now destruct_not_in.
  * now rewrite H, H0.
  * now rewrite H, H0.
  * eapply foldr_not_in_Forall in H1 as [H1 H1D]. destruct_not_in.
    rewrite H by assumption.
    f_equal. rewrite <- (map_id l) at 2. apply map_ext_in.
    rewrite Forall_forall in H0, H1. intros. eapply H0 in H2 as P. destruct a.
    rewrite P. reflexivity. now apply (H1  (n, e0)).
  * now rewrite H, H0, H1.
Qed.

Corollary isNotUsed_renamePID_exp :
  (forall e ρ, ~In from (usedPIDsExp e) -> renamePID ρ e = e).
Proof.
  apply isNotUsed_renamePID_ind.
Qed.

Corollary isNotUsed_renamePID_nval :
  (forall e ρ, ~In from (usedPIDsNVal e) -> renamePIDNVal ρ e = e).
Proof.
  apply isNotUsed_renamePID_ind.
Qed.

Corollary isNotUsed_renamePID_val :
  (forall e ρ, ~In from (usedPIDsVal e) -> renamePIDVal ρ e = e).
Proof.
  apply isNotUsed_renamePID_ind.
Qed.

Corollary isNotUsed_renamePID_red :
  (forall e ρ, ~In from (usedPIDsRed e) -> renamePIDRed ρ e = e).
Proof.
  destruct e; simpl; intros; auto.
  * now rewrite isNotUsed_renamePID_exp.
  * rewrite <- (map_id vs) at 2. f_equal. (* change to vseq equality *)
    apply map_ext_in. intros.
    eapply foldr_not_in_Forall in H as [H _].
    rewrite Forall_forall in H. apply H in H0.
    now rewrite isNotUsed_renamePID_val.
  * destruct e, p. destruct_not_in.
    now rewrite isNotUsed_renamePID_val, isNotUsed_renamePID_val.
Qed.

Corollary isNotUsed_renamePID_frameId :
  forall ident ρ, ~In from (usedPIDsFrameId ident) -> renamePIDFrameId ρ ident = ident.
Proof.
  destruct ident; auto; intros; simpl in *; destruct_not_in; now repeat rewrite isNotUsed_renamePID_val.
Qed.

Corollary isNotUsed_renamePID_frame :
  forall f ρ, ~In from (usedPIDsFrame f) -> renamePIDFrame ρ f = f.
Proof.
  destruct f; intros; simpl in *; destruct_not_in.
  * now rewrite isNotUsed_renamePID_exp.
  * now rewrite isNotUsed_renamePID_val.
  * rewrite isNotUsed_renamePID_frameId by assumption.
    f_equal.
    - rewrite <- (map_id vl) at 2. apply map_ext_in. intros.
      eapply foldr_not_in_Forall in H0 as [H0 _].
      rewrite Forall_forall in H0. apply H0 in H2.
      now rewrite isNotUsed_renamePID_val.
    - rewrite <- (map_id el) at 2. apply map_ext_in. intros.
      eapply foldr_not_in_Forall in H1 as [H1 _].
      rewrite Forall_forall in H1. apply H1 in H2.
      now rewrite isNotUsed_renamePID_exp.
  * f_equal. rewrite <- (map_id l) at 2. apply map_ext_in. intros.
    eapply foldr_not_in_Forall in H as [H _]. rewrite Forall_forall in H.
    apply H in H0.
    now rewrite isNotUsed_renamePID_exp.
  * apply foldr_not_in_Forall in H as [H HD].
    rewrite isNotUsed_renamePID_exp by assumption. f_equal.
    rewrite <- (map_id l) at 2. apply map_ext_in. intros.
    rewrite Forall_forall in H. apply H in H0.
    now rewrite isNotUsed_renamePID_exp.
  * apply foldr_not_in_Forall in H as [H HD].
    rewrite isNotUsed_renamePID_val by assumption. f_equal.
    rewrite <- (map_id l) at 2. apply map_ext_in. intros.
    rewrite Forall_forall in H. apply H in H0.
    now rewrite isNotUsed_renamePID_exp.
  * f_equal.
    rewrite <- (map_id l) at 2. apply map_ext_in. intros.
    eapply foldr_not_in_Forall in H as [H _]. rewrite Forall_forall in H.
    apply H in H0. destruct_not_in.
    destruct a, p. simpl in *.
    now rewrite isNotUsed_renamePID_exp, isNotUsed_renamePID_exp.
  * eapply foldr_not_in_Forall in H0 as [H0 H0D].
    eapply foldr_not_in_Forall in H as [H HD].
    rewrite isNotUsed_renamePID_exp by assumption.
    f_equal.
    - rewrite <- (map_id lv) at 2. apply map_ext_in. intros.
      rewrite Forall_forall in H. apply H in H1.
      now rewrite isNotUsed_renamePID_val.
    - rewrite <- (map_id le) at 2. apply map_ext_in. intros.
      rewrite Forall_forall in H0. apply H0 in H1.
      destruct_not_in. destruct a, p.
      now rewrite isNotUsed_renamePID_exp, isNotUsed_renamePID_exp.
  * now rewrite isNotUsed_renamePID_exp.
  * now rewrite isNotUsed_renamePID_exp.
  * now rewrite isNotUsed_renamePID_exp, isNotUsed_renamePID_exp.
Qed.

Corollary isNotUsed_renamePID_stack :
  forall fs ρ, ~In from (usedPIDsStack fs) -> renamePIDStack ρ fs = fs.
Proof.
  intros. unfold renamePIDStack, usedPIDsStack in *.
  rewrite <- (map_id fs) at 2. apply map_ext_in. intros.
  eapply foldr_not_in_Forall in H as [H _].
  rewrite Forall_forall in H. apply H in H0.
  now rewrite isNotUsed_renamePID_frame.
Qed.
*)

From stdpp Require Export base fin_maps gmap.

Definition inj_update p p' (f : nat -> nat) : nat -> nat :=
  fun x =>
    if x =? p   then p' else
    if x =? p'  then p  else
    f x.

Instance update_inj p p' ρ (Hfresh1 : ρ p' = p') (Hfresh2 : ρ p = p) (H : Inj eq eq ρ): Inj eq eq (inj_update p' p ρ).
Proof.
  unfold Inj. intros. unfold inj_update in *.
  repeat break_match_hyp; eqb_to_eq; auto; try congruence.
  * subst. apply H in Hfresh2. congruence.
  * subst. apply H in Hfresh1. congruence.
  * subst. apply H in Hfresh2. congruence.
  * subst. apply H in Hfresh1. congruence.
Qed.

(* Issue: when a the PID we want to rename to, is spawned. Then we need to rename this PID to another fresh PID, and then do the original renaming, but this is not injective.
Example:

  1 : P || 2 : Q || ∅ -[spawn 4]-> 1: P || 2: Q || 4: R || ∅
  rename 3 into 4
  1 : P || 2 : Q || ∅ -[spawn 5]-> 1: P || 2: Q || 5: R || ∅
 *)
Local Goal Inj eq eq (fun x => match x with
                               | 3 => 4
                               | 4 => 5
                               | y => y
                               end).
Proof.
  
Qed.
