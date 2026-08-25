From CoreErlang Require Export Auxiliaries.
From stdpp Require Export gmap.

Import Stdlib.Lists.List.
Import ListNotations.

Fixpoint Exp_eqb_strict (e1 e2 : Exp) : bool :=
  match e1, e2 with
  | VVal a, VVal a' => Val_eqb_strict a a'
  | EExp e1, EExp e2 => NonVal_eqb_strict e1 e2
  | _, _ => false
  end
with NonVal_eqb_strict (e1 e2 : NonVal) : bool :=
  match e1, e2 with
  | EValues l, EValues l' => list_eqb Exp_eqb_strict l l'
  | EFun vl e, EFun vl' e' => Nat.eqb vl vl' && Exp_eqb_strict e e'
  | ECons hd tl, ECons hd' tl' => Exp_eqb_strict hd hd' && Exp_eqb_strict tl tl'
  | ETuple l, ETuple l' => list_eqb Exp_eqb_strict l l'
  | ECall m f l, ECall m' f' l' => Exp_eqb_strict f f' && Exp_eqb_strict m m' &&
      list_eqb Exp_eqb_strict l l'
  | EPrimOp f l, EPrimOp f' l' => String.eqb f f' && list_eqb Exp_eqb_strict l l'
  | EApp exp l, EApp exp' l' => Exp_eqb_strict exp exp' && list_eqb Exp_eqb_strict l l'
  | ECase e l, ECase e' l' => Exp_eqb_strict e e' 
      && Nat.eqb (length l) (length l')
      && list_eqb (prod_eqb (prod_eqb (list_eqb Pat_eqb_strict) Exp_eqb_strict) Exp_eqb_strict) l l'
  | ELet l e1 e2, ELet l' e1' e2' => 
      Nat.eqb l l' && Exp_eqb_strict e1 e1' && Exp_eqb_strict e2 e2'
  | ESeq e1 e2, ESeq e1' e2' => andb (Exp_eqb_strict e1 e1') (Exp_eqb_strict e2 e2')
  | ELetRec l e, ELetRec l' e' => list_eqb (prod_eqb Nat.eqb Exp_eqb_strict) l l' && Exp_eqb_strict e e'
  | EMap l, EMap l' => list_eqb (prod_eqb Exp_eqb_strict Exp_eqb_strict) l l'
  | ETry e1 vl1 e2 vl2 e3, ETry e1' vl1' e2' vl2' e3' => 
      Nat.eqb vl1 vl1' && Nat.eqb vl2 vl2' &&
      Exp_eqb_strict e1 e1' && Exp_eqb_strict e2 e2' && Exp_eqb_strict e3 e3'
  | EBin l, EBin l'     => list_eqb Exp_eqb_strict l l'
  | ESeg seg, ESeg seg' => Segment_eqb Exp_eqb_strict Exp_eqb_strict seg seg'
  | _, _ => false
  end
with Val_eqb_strict (v1 v2 : Val) : bool :=
  match v1, v2 with
  | VNil, VNil => true
  | VLit l, VLit l' => Lit_beq l l'
  | VPid p, VPid p' => Nat.eqb p p'
  | VCons hd tl, VCons hd' tl' => Val_eqb_strict hd hd' && Val_eqb_strict tl tl'
  | VTuple l, VTuple l' => list_eqb Val_eqb_strict l l'
  | VMap l, VMap l' => list_eqb (prod_eqb Val_eqb_strict Val_eqb_strict) l l'
  | VVar v, VVar v' => Nat.eqb v v'
  | VFunId v, VFunId v' => funid_eqb v v'
  | VClos ext id vc e, VClos ext' id' vc' e' => 
      Nat.eqb id id' && Nat.eqb vc vc' && Exp_eqb_strict e e' &&
      list_eqb (prod_eqb (prod_eqb Nat.eqb Nat.eqb) Exp_eqb_strict) ext ext'
  | VBitstring bits, VBitstring bits' => if bvn_eq_dec bits bits' then true else false
  | _, _ => false
  end
with Pat_eqb_strict (p1 p2 : Pat) : bool :=
match p1, p2 with
| PVar, PVar => true
| PLit l, PLit l' => Lit_beq l l'
| PCons hd tl, PCons hd' tl' => Pat_eqb_strict hd hd' && Pat_eqb_strict tl tl'
| PTuple l, PTuple l' => list_eqb Pat_eqb_strict l l'
| PMap l, PMap l' => list_eqb (prod_eqb Pat_eqb_strict Pat_eqb_strict) l l'
| PNil, PNil => true
| PBin segs, PBin segs' => list_eqb (Segment_eqb Pat_eqb_strict Val_eqb_strict) segs segs'
| _, _ => false
end.

Theorem Private_eqb_strict_refl :
     (forall e, Exp_eqb_strict e e = true)
  /\ (forall e, NonVal_eqb_strict e e = true)
  /\ (forall v, Val_eqb_strict v v = true)
  /\ (forall p, Pat_eqb_strict p p = true).
Proof.
  apply Exp_ind with
    (Q := Forall (fun v => Exp_eqb_strict v v = true))
    (QV := Forall (fun v => Val_eqb_strict v v = true))
    (R  := Forall (PBoth (fun e => Exp_eqb_strict e e = true)))
    (RV := Forall (PBoth (fun v => Val_eqb_strict v v = true)))
    (VV := Forall (fun '(_,_,e) => Exp_eqb_strict e e = true))
    (W  := Forall (fun '(lp,e1,e2) => Forall (fun p => Pat_eqb_strict p p = true) lp
                    /\ Exp_eqb_strict e1 e1 = true /\ Exp_eqb_strict e2 e2 = true))
    (Z  := Forall (fun '(_,e) => Exp_eqb_strict e e = true))
    (PQ := Forall (fun p => Pat_eqb_strict p p = true))
    (PR := Forall (PBoth (fun p => Pat_eqb_strict p p = true)))
    (PT := Forall (fun seg : Segment Pat Val => Pat_eqb_strict (Syntax.val seg) (Syntax.val seg) = true
                    /\ Val_eqb_strict (Syntax.size seg) (Syntax.size seg) = true))
  ; simpl; auto; intros.
  (* Val *)
  * apply Lit_eqb_refl.
  * apply Nat.eqb_refl.
  * rewrite H, H0. reflexivity.
  * induction H; auto. simpl. rewrite H, IHForall. reflexivity.
  * induction H; auto. destruct x, H. simpl in *. simpl. rewrite H, H1, IHForall. reflexivity.
  * apply Nat.eqb_refl.
  * destruct n. simpl. now rewrite !Nat.eqb_refl.
  * rewrite H0, Nat.eqb_refl, Nat.eqb_refl. simpl.
    clear -H. induction H; auto.
    destruct x, p. simpl in H. simpl. rewrite IHForall, H, Nat.eqb_refl, Nat.eqb_refl. reflexivity.
  * destruct (bvn_eq_dec b b); [reflexivity | contradiction].
  (* NonVal *)
  * rewrite H, Nat.eqb_refl. reflexivity.
  * induction H; auto. simpl. rewrite H, IHForall. reflexivity.
  * rewrite H, H0. reflexivity.
  * induction H; auto. simpl. rewrite H, IHForall. reflexivity.
  * induction H; auto. destruct x, H. simpl in *. rewrite H, H1, IHForall. reflexivity.
  * rewrite H, H0. simpl.
    clear -H1. induction H1; auto. simpl. rewrite H, IHForall. reflexivity.
  * rewrite String.eqb_refl. simpl. induction H; auto. simpl. rewrite H, IHForall. reflexivity.
  * rewrite H. simpl.
    clear -H0. induction H0; auto. simpl. rewrite H, IHForall. reflexivity.
  * rewrite H, Nat.eqb_refl. simpl. induction H0; auto.
    destruct x as [[lp e1] e2]. destruct H0 as [Hlp [He1 He2]].
    assert (Hlpres : list_eqb Pat_eqb_strict lp lp = true).
    { clear -Hlp. induction Hlp; auto. simpl. rewrite H, IHHlp. reflexivity. }
    simpl. rewrite Hlpres, He1, He2, IHForall. reflexivity.
  * rewrite H, H0, Nat.eqb_refl. reflexivity.
  * rewrite H, H0. reflexivity.
  * assert (Hlres : list_eqb (prod_eqb Nat.eqb Exp_eqb_strict) l l = true).
    { clear -H0. induction H0; auto. destruct x. simpl in H0. simpl.
      rewrite Nat.eqb_refl, H, IHForall. reflexivity. }
    rewrite Hlres, H. reflexivity.
  * rewrite Nat.eqb_refl, Nat.eqb_refl, H, H0, H1. reflexivity.
  * induction H; auto. simpl. rewrite H, IHForall. reflexivity.
  * destruct seg; simpl in *; rewrite H, H0, Nat.eqb_refl, BinSign_eqb_refl, BinType_eqb_refl, BinEnd_eqb_refl.
    reflexivity.
  (* Pattern *)
  * apply Lit_eqb_refl.
  * rewrite H, H0. reflexivity.
  * induction H; auto. simpl. rewrite H, IHForall. reflexivity.
  * induction H; auto. destruct x, H. simpl in *. rewrite H, H1, IHForall. reflexivity.
  * induction H; auto. simpl. destruct H as [Hv Hs].
    destruct x; simpl in *; rewrite Hv, Hs, Nat.eqb_refl, BinSign_eqb_refl, BinType_eqb_refl, BinEnd_eqb_refl, IHForall.
    reflexivity.
Qed.

Corollary eqb_strict_refl : forall e, Exp_eqb_strict e e = true.
Proof. now apply Private_eqb_strict_refl. Qed.

Corollary eqb_strict_refl_nonval : forall e, NonVal_eqb_strict e e = true.
Proof. now apply Private_eqb_strict_refl. Qed.

Corollary eqb_strict_refl_val : forall v, Val_eqb_strict v v = true.
Proof. now apply Private_eqb_strict_refl. Qed.

Corollary eqb_strict_refl_pat : forall p, Pat_eqb_strict p p = true.
Proof. now apply Private_eqb_strict_refl. Qed.

Lemma Private_eqb_strict_eq_fwd :
     (forall e1 e2, Exp_eqb_strict e1 e2 = true -> e1 = e2)
  /\ (forall e1 e2, NonVal_eqb_strict e1 e2 = true -> e1 = e2)
  /\ (forall v1 v2, Val_eqb_strict v1 v2 = true -> v1 = v2)
  /\ (forall p1 p2, Pat_eqb_strict p1 p2 = true -> p1 = p2).
Proof.
  apply Exp_ind with
    (Q  := Forall (fun e1 => forall e2, Exp_eqb_strict e1 e2 = true -> e1 = e2))
    (QV := Forall (fun v1 => forall v2, Val_eqb_strict v1 v2 = true -> v1 = v2))
    (R  := Forall (PBoth (fun e1 => forall e2, Exp_eqb_strict e1 e2 = true -> e1 = e2)))
    (RV := Forall (PBoth (fun v1 => forall v2, Val_eqb_strict v1 v2 = true -> v1 = v2)))
    (VV := Forall (fun '(_,_,e1) => forall e2, Exp_eqb_strict e1 e2 = true -> e1 = e2))
    (W  := Forall (fun '(lp,e1,e1') =>
             Forall (fun p1 => forall p2, Pat_eqb_strict p1 p2 = true -> p1 = p2) lp
             /\ (forall e2, Exp_eqb_strict e1 e2 = true -> e1 = e2)
             /\ (forall e2, Exp_eqb_strict e1' e2 = true -> e1' = e2)))
    (Z  := Forall (fun '(_,e1) => forall e2, Exp_eqb_strict e1 e2 = true -> e1 = e2))
    (PQ := Forall (fun p1 => forall p2, Pat_eqb_strict p1 p2 = true -> p1 = p2))
    (PR := Forall (PBoth (fun p1 => forall p2, Pat_eqb_strict p1 p2 = true -> p1 = p2)))
    (PT := Forall (fun seg : Segment Pat Val =>
             (forall p2, Pat_eqb_strict (Syntax.val seg) p2 = true -> Syntax.val seg = p2)
             /\ (forall v2, Val_eqb_strict (Syntax.size seg) v2 = true -> Syntax.size seg = v2)))
  ; simpl; auto; intros.
  (* Exp/NonVal wrappers *)
  * destruct e2; try discriminate. apply H in H0. subst. reflexivity.
  * destruct e2; try discriminate. apply H in H0. subst. reflexivity.
  (* Val *)
  * destruct v2; try discriminate. reflexivity.
  * destruct v2; try discriminate. apply Lit_eqb_eq in H. subst. reflexivity.
  * destruct v2; try discriminate. apply Nat.eqb_eq in H. subst. reflexivity.
  * destruct v2; try discriminate. apply andb_prop in H1. destruct H1.
    apply H in H1. apply H0 in H2. subst. reflexivity.
  * destruct v2; try discriminate.
    assert (l = l0).
    { revert H0. revert l0. induction H; intros.
      - destruct l0; try discriminate. reflexivity.
      - destruct l0; try discriminate. simpl in H1. apply andb_prop in H1. destruct H1.
        apply H in H1. f_equal; auto. }
    subst. reflexivity.
  * destruct v2; try discriminate.
    assert (l = l0).
    { revert H0. revert l0. induction H; intros.
      - destruct l0; try discriminate. reflexivity.
      - destruct l0; try discriminate. destruct x, p.
        destruct H as [Hx Hy]. simpl in H1. apply andb_prop in H1. destruct H1.
        apply andb_prop in H. destruct H as [Ha Hb]. simpl in Hx, Hy.
        apply Hx in Ha. apply Hy in Hb. apply IHForall in H1.
        subst. reflexivity. }
    subst. reflexivity.
  * destruct v2; try discriminate. apply Nat.eqb_eq in H. subst. reflexivity.
  * destruct v2; try discriminate. unfold funid_eqb in H. destruct n, n0.
    apply andb_prop in H. destruct H. apply Nat.eqb_eq in H, H0. subst. reflexivity.
  * destruct v2; try discriminate.
    apply andb_prop in H1. destruct H1. apply andb_prop in H1. destruct H1.
    apply andb_prop in H1. destruct H1. apply Nat.eqb_eq in H1, H4.
    apply H0 in H3. subst id vl e.
    assert (ext = ext0).
    { revert H2. revert ext0. induction H; intros.
      - destruct ext0; try discriminate. reflexivity.
      - destruct ext0; try discriminate. destruct x, p, p0, p.
        simpl in H2. apply andb_prop in H2. destruct H2. apply andb_prop in H2. destruct H2.
        apply andb_prop in H2. destruct H2. apply Nat.eqb_eq in H2, H5.
        apply H in H4. apply IHForall in H3.
        subst. reflexivity. }
    subst. reflexivity.
  * destruct v2; try discriminate. destruct (bvn_eq_dec b bits); [subst; reflexivity | discriminate].
  (* NonVal *)
  * destruct e2; try discriminate. apply andb_prop in H0. destruct H0.
    apply Nat.eqb_eq in H0. apply H in H1. subst. reflexivity.
  * destruct e2; try discriminate.
    assert (el = el0).
    { revert H0. revert el0. induction H; intros.
      - destruct el0; try discriminate. reflexivity.
      - destruct el0; try discriminate. simpl in H1. apply andb_prop in H1. destruct H1.
        apply H in H1. f_equal; auto. }
    subst. reflexivity.
  * destruct e2; try discriminate. apply andb_prop in H1. destruct H1.
    apply H in H1. apply H0 in H2. subst. reflexivity.
  * destruct e2; try discriminate.
    assert (l = l0).
    { revert H0. revert l0. induction H; intros.
      - destruct l0; try discriminate. reflexivity.
      - destruct l0; try discriminate. simpl in H1. apply andb_prop in H1. destruct H1.
        apply H in H1. f_equal; auto. }
    subst. reflexivity.
  * destruct e2; try discriminate.
    assert (l = l0).
    { revert H0. revert l0. induction H; intros.
      - destruct l0; try discriminate. reflexivity.
      - destruct l0; try discriminate. destruct x, p.
        destruct H as [Hx Hy]. simpl in Hx, Hy. simpl in H1.
        apply andb_prop in H1. destruct H1. apply andb_prop in H. destruct H as [Ha Hb].
        apply Hx in Ha. apply Hy in Hb. apply IHForall in H1.
        subst. reflexivity. }
    subst. reflexivity.
  * destruct e2; try discriminate.
    apply andb_prop in H2. destruct H2. apply andb_prop in H2. destruct H2.
    apply H0 in H2. apply H in H4. subst f m.
    assert (l = l0).
    { clear -H1 H3. revert H3. revert l0. induction H1; intros.
      - destruct l0; try discriminate. reflexivity.
      - destruct l0; try discriminate. simpl in H3. apply andb_prop in H3. destruct H3.
        apply H in H0. f_equal; auto. }
    subst. reflexivity.
  * destruct e2; try discriminate. apply andb_prop in H0. destruct H0.
    apply String.eqb_eq in H0. subst f0.
    assert (l = l0).
    { clear -H H1. revert H1. revert l0. induction H; intros.
      - destruct l0; try discriminate. reflexivity.
      - destruct l0; try discriminate. simpl in H1. apply andb_prop in H1. destruct H1.
        apply H in H1. f_equal; auto. }
    subst. reflexivity.
  * destruct e2; try discriminate. apply andb_prop in H1. destruct H1.
    apply H in H1. subst e.
    assert (l = l0).
    { clear -H0 H2. revert H2. revert l0. induction H0; intros.
      - destruct l0; try discriminate. reflexivity.
      - destruct l0; try discriminate. simpl in H2. apply andb_prop in H2. destruct H2.
        apply H in H1. apply IHForall in H2.
        subst. reflexivity. }
    subst. reflexivity.
  * destruct e2; try discriminate.
    apply andb_prop in H1. destruct H1. apply andb_prop in H1. destruct H1.
    apply H in H1. subst e. clear H3.
    assert (l = l0).
    { clear -H0 H2. revert H2. revert l0. induction H0; intros.
      - destruct l0; try discriminate. reflexivity.
      - destruct l0; try discriminate. destruct x as [[lp e1] e1']. destruct p as [[lp' ea] eb].
        destruct H as [Hlp [He1 He1']]. simpl in H2. apply andb_prop in H2. destruct H2.
        apply andb_prop in H. destruct H. apply andb_prop in H. destruct H.
        apply He1 in H3. apply He1' in H2. apply IHForall in H1.
        assert (lp = lp').
        { clear -Hlp H. revert H. revert lp'. induction Hlp; intros.
          - destruct lp'; try discriminate. reflexivity.
          - destruct lp'; try discriminate. simpl in H0. apply andb_prop in H0. destruct H0.
            apply H in H0. f_equal; auto. }
        subst. reflexivity. }
    subst. reflexivity.
  * destruct e0; try discriminate.
    apply andb_prop in H1. destruct H1. apply andb_prop in H1. destruct H1.
    apply Nat.eqb_eq in H1. apply H in H3. apply H0 in H2. subst. reflexivity.
  * destruct e0; try discriminate. apply andb_prop in H1. destruct H1.
    apply H in H1. apply H0 in H2. subst. reflexivity.
  * destruct e2; try discriminate. apply andb_prop in H1. destruct H1.
    apply H in H2. subst e.
    assert (l = l0).
    { clear -H0 H1. revert H1. revert l0. induction H0; intros.
      - destruct l0; try discriminate. reflexivity.
      - destruct l0; try discriminate. destruct x, p.
        simpl in H1. apply andb_prop in H1. destruct H1. apply andb_prop in H1. destruct H1.
        apply Nat.eqb_eq in H1. apply H in H3. apply IHForall in H2.
        subst. reflexivity. }
    subst. reflexivity.
  * destruct e0; try discriminate.
    apply andb_prop in H2. destruct H2. apply andb_prop in H2. destruct H2.
    apply andb_prop in H2. destruct H2. apply andb_prop in H2. destruct H2.
    apply Nat.eqb_eq in H2, H6. apply H in H5. apply H0 in H4. apply H1 in H3.
    subst. reflexivity.
  * destruct e2; try discriminate.
    assert (l = l0).
    { clear -H H0. revert H0. revert l0. induction H; intros.
      - destruct l0; try discriminate. reflexivity.
      - destruct l0; try discriminate. simpl in H1. apply andb_prop in H1. destruct H1.
        apply H in H1. f_equal; auto. }
    subst. reflexivity.
  * destruct e2; try discriminate. destruct seg, seg0. simpl in *.
    repeat (apply andb_prop in H1; destruct H1).
    apply H in H1. apply H0 in H6. apply Nat.eqb_eq in H5.
    apply BinType_eqb_eq in H4. apply BinSign_eqb_eq in H3. apply BinEnd_eqb_eq in H2.
    subst. reflexivity.
  (* Pattern *)
  * destruct p2; try discriminate. reflexivity.
  * destruct p2; try discriminate. apply Lit_eqb_eq in H. subst. reflexivity.
  * destruct p2; try discriminate. reflexivity.
  * destruct p2; try discriminate. apply andb_prop in H1. destruct H1.
    apply H in H1. apply H0 in H2. subst. reflexivity.
  * destruct p2; try discriminate.
    assert (l = l0).
    { clear -H H0. revert H0. revert l0. induction H; intros.
      - destruct l0; try discriminate. reflexivity.
      - destruct l0; try discriminate. simpl in H1. apply andb_prop in H1. destruct H1.
        apply H in H1. f_equal; auto. }
    subst. reflexivity.
  * destruct p2; try discriminate.
    assert (l = l0).
    { clear -H H0. revert H0. revert l0. induction H; intros.
      - destruct l0; try discriminate. reflexivity.
      - destruct l0; try discriminate. destruct x, p.
        destruct H as [Hx Hy]. simpl in Hx, Hy. simpl in H1.
        apply andb_prop in H1. destruct H1. apply andb_prop in H. destruct H as [Ha Hb].
        apply Hx in Ha. apply Hy in Hb. apply IHForall in H1.
        subst. reflexivity. }
    subst. reflexivity.
  * destruct p2; try discriminate.
    assert (l = segments).
    { clear -H H0. revert H0. revert segments. induction H; intros.
      - destruct segments; try discriminate. reflexivity.
      - destruct segments; try discriminate. destruct x, H as [Hv Hs]. destruct s. simpl in *.
        repeat (apply andb_prop in H0; destruct H0).
        repeat (apply andb_prop in H1; destruct H1).
        repeat (apply andb_prop in H; destruct H).
        apply Hv in H. apply Hs in H6. apply Nat.eqb_eq in H5.
        apply BinType_eqb_eq in H4. apply BinSign_eqb_eq in H3. apply BinEnd_eqb_eq in H2.
        apply IHForall in H1.
        subst. reflexivity. }
    subst. reflexivity.
Qed.

Theorem Private_eqb_strict_eq :
     (forall e1 e2, Exp_eqb_strict e1 e2 = true <-> e1 = e2)
  /\ (forall e1 e2, NonVal_eqb_strict e1 e2 = true <-> e1 = e2)
  /\ (forall v1 v2, Val_eqb_strict v1 v2 = true <-> v1 = v2)
  /\ (forall p1 p2, Pat_eqb_strict p1 p2 = true <-> p1 = p2).
Proof.
  destruct Private_eqb_strict_eq_fwd as [F1 [F2 [F3 F4]]].
  destruct Private_eqb_strict_refl as [R1 [R2 [R3 R4]]].
  split; [| split; [| split]].
  - intros e1 e2. split. apply F1. intros; subst; apply R1.
  - intros e1 e2. split. apply F2. intros; subst; apply R2.
  - intros v1 v2. split. apply F3. intros; subst; apply R3.
  - intros p1 p2. split. apply F4. intros; subst; apply R4.
Qed.

Corollary eqb_strict_eq : forall e1 e2, Exp_eqb_strict e1 e2 = true <-> e1 = e2.
Proof. apply Private_eqb_strict_eq. Qed.

Corollary eqb_strict_eq_nonval : forall e1 e2, NonVal_eqb_strict e1 e2 = true <-> e1 = e2.
Proof. apply Private_eqb_strict_eq. Qed.

Corollary eqb_strict_eq_val : forall v1 v2, Val_eqb_strict v1 v2 = true <-> v1 = v2.
Proof. apply Private_eqb_strict_eq. Qed.

Corollary eqb_strict_eq_pat : forall p1 p2, Pat_eqb_strict p1 p2 = true <-> p1 = p2.
Proof. apply Private_eqb_strict_eq. Qed.

Lemma Val_eqb_strict_lit_eqb: forall v l, Val_eqb_strict v (VLit l) = Val_eqb v (VLit l).
Proof.
  intros. destruct v; reflexivity.
Qed.
