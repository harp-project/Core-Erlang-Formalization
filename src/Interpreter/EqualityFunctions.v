From CoreErlang.FrameStack Require Export Frames SubstSemantics.
From CoreErlang.Concurrent Require Export ProcessSemantics.

Import Coq.Lists.List.
Import ListNotations.

Fixpoint Exp_eqb_strict (e1 e2 : Exp) : bool :=
  match e1, e2 with
  | VVal a, VVal a' => Val_eqb_strict a a'
  | EExp (EValues l), EExp (EValues l') => 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | x::xs, x'::xs' => andb (Exp_eqb_strict x x') 
                                 (blist xs xs')
        | _, _ => false
        end) l l'
  | EExp (EFun vl e), EExp (EFun vl' e') => Nat.eqb vl vl' && Exp_eqb_strict e e'
  | EExp (ECons hd tl), EExp (ECons hd' tl') => Exp_eqb_strict hd hd' && Exp_eqb_strict tl tl'
  | EExp (ETuple l), EExp (ETuple l') => 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | x::xs, x'::xs' => andb (Exp_eqb_strict x x') (blist xs xs')
        | _, _ => false
        end) l l'
  | EExp (ECall m f l), EExp (ECall m' f' l') => Exp_eqb_strict f f' && Exp_eqb_strict m m' && 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | x::xs, x'::xs' => andb (Exp_eqb_strict x x') (blist xs xs')
        | _, _ => false
        end) l l'
  | EExp (EPrimOp f l), EExp (EPrimOp f' l') => String.eqb f f' && 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | x::xs, x'::xs' => andb (Exp_eqb_strict x x') (blist xs xs')
        | _, _ => false
        end) l l'
  | EExp (EApp exp l), EExp (EApp exp' l') => Exp_eqb_strict exp exp' && 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | x::xs, x'::xs' => andb (Exp_eqb_strict x x') (blist xs xs')
        | _, _ => false
        end) l l'
  | EExp (ECase e l), EExp (ECase e' l') => Exp_eqb_strict e e' 
      && Nat.eqb (length l) (length l') 
      && (fix blist l l' := match l, l' with
        | [], [] => true
        | (pl,y,z)::xs, (pl',y',z')::xs' => andb (
          (fix blist l l' := match l, l' with
          | [], [] => true
          | x::xs, x'::xs' => andb (Pat_eqb x x') (blist xs xs')
          | _, _ => false
          end) pl pl') 
          (andb (Exp_eqb_strict y y') (andb (Exp_eqb_strict z z') (blist xs xs')))
                                           | _, _ => false
                                           end) l l' 
  | EExp (ELet l e1 e2), EExp (ELet l' e1' e2') => 
      Nat.eqb l l' && Exp_eqb_strict e1 e1' && Exp_eqb_strict e2 e2'
  | EExp (ESeq e1 e2), EExp (ESeq e1' e2') => andb (Exp_eqb_strict e1 e1') (Exp_eqb_strict e2 e2')
  | EExp (ELetRec l e), EExp (ELetRec l' e') => 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | (x,y)::xs, (x',y')::xs' => 
        andb (Nat.eqb x x') (andb (Exp_eqb_strict y y') (blist xs xs'))
        | _, _ => false
        end) l l' && Exp_eqb_strict e e'
  | EExp (EMap l), EExp (EMap l') => 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | (x,y)::xs, (x',y')::xs' => 
        andb (Exp_eqb_strict x x') (andb (Exp_eqb_strict y y') (blist xs xs'))
        | _, _ => false
        end) l l'
  | EExp (ETry e1 vl1 e2 vl2 e3), EExp (ETry e1' vl1' e2' vl2' e3') => 
      Nat.eqb vl1 vl1' && Nat.eqb vl2 vl2' &&
      Exp_eqb_strict e1 e1' && Exp_eqb_strict e2 e2' && Exp_eqb_strict e3 e3'
  | _, _ => false
  end
with Val_eqb_strict (v1 v2 : Val) : bool :=
  match v1, v2 with
  | VNil, VNil => true
  | VLit l, VLit l' => Lit_beq l l'
  | VPid p, VPid p' => Nat.eqb p p'
  | VCons hd tl, VCons hd' tl' => Val_eqb_strict hd hd' && Val_eqb_strict tl tl'
  | VTuple l, VTuple l' => 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | x::xs, x'::xs' => andb (Val_eqb_strict x x') (blist xs xs')
        | _, _ => false
        end) l l'
  | VMap l, VMap l' => 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | (x,y)::xs, (x',y')::xs' => 
        andb (Val_eqb_strict x x') (andb (Val_eqb_strict y y') (blist xs xs'))
        | _, _ => false
        end) l l'
  | VVar v, VVar v' => Nat.eqb v v'
  | VFunId v, VFunId v' => funid_eqb v v'
  | VClos ext id vc e, VClos ext' id' vc' e' => 
      Nat.eqb id id' && Nat.eqb vc vc' && Exp_eqb_strict e e' &&
      (fix blist l l' := match l, l' with
        | [], [] => true
        | (n1,n2,e)::xs, (n1',n2',e')::xs' => 
        andb (Exp_eqb_strict e e') (andb (Nat.eqb n1 n1') (andb (Nat.eqb n2 n2') (blist xs xs')))
        | _, _ => false
        end) ext ext'
  | _, _ => false
  end.

Lemma Pat_eqb_refl: forall p, Pat_eqb p p = true.
Proof.
  induction p using Pat_ind2 with
  (Q := Forall (fun p => Pat_eqb p p = true))
  (R := Forall (PBoth (fun p => Pat_eqb p p = true))); simpl; auto.
  * apply Lit_eqb_refl.
  * now rewrite IHp1, IHp2.
  * induction IHp; auto. now rewrite H, IHIHp.
  * induction IHp; auto. destruct x, H. simpl in *. now rewrite H, H0, IHIHp.
Qed.

Lemma Pat_eqb_eq: forall p1 p2, Pat_eqb p1 p2 = true <-> p1 = p2.
Proof.
  intros. split.
  * revert p2.
    induction p1 using Pat_ind2 with
    (Q := Forall (fun p => forall p2, Pat_eqb p p2 = true -> p = p2))
    (R := Forall (PBoth (fun p => forall p2, Pat_eqb p p2 = true -> p = p2))); auto; intros.
    + simpl in H. destruct p2; try discriminate. reflexivity.
    + simpl in H. destruct p2; try discriminate. apply Lit_eqb_eq in H. subst. reflexivity.
    + simpl in H. destruct p2; try discriminate. reflexivity.
    + simpl in H. destruct p2; try discriminate.
      apply andb_prop in H. destruct H.
      apply IHp1_1 in H. apply IHp1_2 in H0. subst. reflexivity.
    + simpl in H. destruct p2; try discriminate.
      revert H IHp1. revert l0.
      induction l; intros.
      - destruct l0. reflexivity. discriminate.
      - destruct l0. discriminate.
        apply andb_prop in H. destruct H.
        inv IHp1. apply H3 in H. subst a.
        specialize (IHl l0 H0 H4). inv IHl. reflexivity.
    + simpl in H. destruct p2; try discriminate.
      revert H IHp1. revert l0.
      induction l; intros.
      - destruct l0. reflexivity. discriminate.
      - destruct a. destruct l0. discriminate.
        destruct p1. apply andb_prop in H. destruct H. apply andb_prop in H. destruct H.
        inv IHp1. inv H4. apply H2 in H. apply H3 in H1. simpl in H, H1. subst.
        specialize (IHl l0 H0 H5). inv IHl. reflexivity.
  * intros. subst. apply Pat_eqb_refl.
Qed.

Lemma Exp_eqb_strict_refl: forall e, Exp_eqb_strict e e = true.
Proof.
  induction e using Exp_ind2 with
    (PV := fun v => Val_eqb_strict v v = true)
    (PE := fun e => Exp_eqb_strict e e = true)
    (Q  := Forall (fun e => Exp_eqb_strict e e = true))
    (QV := Forall (fun v => Val_eqb_strict v v = true))
    (R  := Forall (PBoth (fun e => Exp_eqb_strict e e = true)))
    (RV := Forall (PBoth (fun v => Val_eqb_strict v v = true)))
    (VV := Forall (fun e => Exp_eqb_strict e.2 e.2 = true))
    (W  := Forall (fun '(e1, e2, e3) => Exp_eqb_strict e3 e3 = true 
                    /\ Exp_eqb_strict e2 e2 = true
                    /\ Forall (fun p => Pat_eqb p p = true) e1))
    (Z  := Forall (fun e => Exp_eqb_strict e.2 e.2 = true)); simpl; auto.
  * apply Lit_eqb_refl.
  * apply Nat.eqb_refl.
  * rewrite IHe, IHe0. reflexivity.
  * induction IHe; auto. rewrite H, IHIHe. reflexivity.
  * induction IHe; auto. destruct x, H. simpl in *. rewrite H, H0, IHIHe. reflexivity.
  * apply Nat.eqb_refl.
  * destruct n. simpl. do 2 rewrite Nat.eqb_refl. reflexivity.
  * rewrite IHe0, Nat.eqb_refl, Nat.eqb_refl. simpl.
    clear -IHe. induction IHe; auto.
    destruct x, p. simpl in H. rewrite IHIHe, H, Nat.eqb_refl, Nat.eqb_refl. reflexivity.
  * now rewrite IHe, Nat.eqb_refl.
  * induction IHe; auto. now rewrite H, IHIHe.
  * now rewrite IHe1, IHe2.
  * induction IHe; auto. now rewrite H, IHIHe.
  * induction IHe; auto. destruct x, H. simpl in *. now rewrite H, H0, IHIHe.
  * rewrite IHe1, IHe2. simpl.
    clear -IHe3. induction IHe3; auto. now rewrite H, IHIHe3.
  * rewrite String.eqb_refl. simpl. induction IHe; auto.
    now rewrite H, IHIHe.
  * rewrite IHe. simpl.
    clear -IHe0. induction IHe0; auto. now rewrite H, IHIHe0.
  * rewrite IHe, Nat.eqb_refl. simpl. induction IHe0; auto.
    destruct x, p, H, H0. simpl in *. rewrite H, H0. simpl. rewrite IHIHe0.
    clear -H1. induction H1; auto. rewrite H. simpl. rewrite IHForall. reflexivity.
  * now rewrite IHe1, IHe2, Nat.eqb_refl.
  * now rewrite IHe1, IHe2.
  * rewrite IHe. induction IHe0; auto. destruct x. simpl in H.
    rewrite Nat.eqb_refl. simpl in *. rewrite H. simpl. rewrite IHIHe0. reflexivity.
  * now rewrite Nat.eqb_refl, Nat.eqb_refl, IHe1, IHe2, IHe3.
  * constructor; auto.
    split. auto. split. auto.
    induction l; constructor. apply Pat_eqb_refl. apply IHl.
Qed.

Lemma Val_eqb_strict_refl: forall v, Val_eqb_strict v v = true.
Proof.
  induction v using Val_ind2 with
    (P  := fun v => Exp_eqb_strict v v = true)
    (PE := fun e => Exp_eqb_strict e e = true)
    (Q  := Forall (fun e => Exp_eqb_strict e e = true))
    (QV := Forall (fun v => Val_eqb_strict v v = true))
    (R  := Forall (PBoth (fun e => Exp_eqb_strict e e = true)))
    (RV := Forall (PBoth (fun v => Val_eqb_strict v v = true)))
    (VV := Forall (fun e => Exp_eqb_strict e.2 e.2 = true))
    (W  := Forall (fun '(e1, e2, e3) => Exp_eqb_strict e3 e3 = true 
                    /\ Exp_eqb_strict e2 e2 = true
                    /\ Forall (fun p => Pat_eqb p p = true) e1))
    (Z  := Forall (fun e => Exp_eqb_strict e.2 e.2 = true)); simpl; auto.
  * apply Lit_eqb_refl.
  * apply Nat.eqb_refl.
  * rewrite IHv1, IHv2. reflexivity.
  * induction IHv; auto. rewrite H, IHIHv. reflexivity.
  * induction IHv; auto. destruct x, H. simpl in *. rewrite H, H0, IHIHv. reflexivity.
  * apply Nat.eqb_refl.
  * destruct n. simpl. do 2 rewrite Nat.eqb_refl. reflexivity.
  * rewrite IHv0, Nat.eqb_refl, Nat.eqb_refl. simpl.
    clear -IHv. induction IHv; auto.
    destruct x, p. simpl in H. rewrite IHIHv, H, Nat.eqb_refl, Nat.eqb_refl. reflexivity.
  * now rewrite IHv, Nat.eqb_refl.
  * induction IHv; auto. now rewrite H, IHIHv.
  * now rewrite IHv, IHv0.
  * induction IHv; auto. now rewrite H, IHIHv.
  * induction IHv; auto. destruct x, H. simpl in *. now rewrite H, H0, IHIHv.
  * rewrite IHv, IHv0. simpl.
    clear -IHv1. induction IHv1; auto. now rewrite H, IHIHv1.
  * rewrite String.eqb_refl. simpl. induction IHv; auto.
    now rewrite H, IHIHv.
  * rewrite IHv. simpl.
    clear -IHv0. induction IHv0; auto. now rewrite H, IHIHv0.
  * rewrite IHv, Nat.eqb_refl. simpl. induction IHv0; auto.
    destruct x, p, H, H0. simpl in *. rewrite H, H0. simpl. rewrite IHIHv0.
    clear -H1. induction H1; auto. rewrite H. simpl. rewrite IHForall. reflexivity.
  * now rewrite IHv, IHv0, Nat.eqb_refl.
  * now rewrite IHv, IHv0.
  * rewrite IHv. induction IHv0; auto. destruct x. simpl in H.
    rewrite Nat.eqb_refl. simpl in *. rewrite H. simpl. rewrite IHIHv0. reflexivity.
  * now rewrite Nat.eqb_refl, Nat.eqb_refl, IHv, IHv0, IHv1.
  * constructor; auto.
    split. auto. split. auto.
    induction l; constructor. apply Pat_eqb_refl. apply IHl.
Qed.

Lemma Val_eqb_strict_eq: forall v1 v2, Val_eqb_strict v1 v2 = true <-> v1 = v2.
Proof.
  intros. split.
  * revert v2.
    induction v1 using Val_ind2 with
      (P  := fun e => forall e2, Exp_eqb_strict e e2 = true -> e = e2)
      (PE := fun e => forall e2, Exp_eqb_strict e e2 = true -> e = e2)
      (Q  := Forall (fun e => forall e2, Exp_eqb_strict e e2 = true -> e = e2))
      (QV := Forall (fun v => forall v2, Val_eqb_strict v v2 = true -> v = v2))
      (R  := Forall (PBoth (fun e => forall e2, Exp_eqb_strict e e2 = true -> e = e2)))
      (RV := Forall (PBoth (fun v => forall v2, Val_eqb_strict v v2 = true -> v = v2)))
      (VV := Forall (fun '(_, e) => forall e2, Exp_eqb_strict e e2 = true -> e = e2 ))
      (W  := Forall (fun '(_, e, e') => (forall e2,  Exp_eqb_strict e  e2  = true -> e  = e2) /\
                                        (forall e2', Exp_eqb_strict e' e2' = true -> e' = e2')))
      (Z  := Forall (fun '(_, e) => forall e2, Exp_eqb_strict e e2 = true -> e = e2)); auto.
    + intros. simpl in H. destruct e2; try discriminate.
      apply IHv1 in H. subst. reflexivity.
    + intros. simpl in H. destruct v2; try discriminate. reflexivity.
    + intros. simpl in H. destruct v2; try discriminate. apply Lit_eqb_eq in H. subst. reflexivity.
    + intros. simpl in H. destruct v2; try discriminate. apply Nat.eqb_eq in H. subst. reflexivity.
    + intros. simpl in H. destruct v2; try discriminate.
      apply andb_prop in H. destruct H.
      apply IHv1_1 in H. apply IHv1_2 in H0. subst. reflexivity.
    + intros. simpl in H. destruct v2; try discriminate.
      revert H IHv1. revert l0. revert l. induction l; intros.
      - destruct l0. reflexivity. discriminate.
      - destruct l0. discriminate.
        apply andb_prop in H. destruct H.
        inv IHv1. apply H3 in H. subst a.
        specialize (IHl l0 H0 H4). inv IHl. reflexivity.
    + intros. simpl in H. destruct v2; try discriminate.
      revert H IHv1. revert l0. revert l. induction l; intros.
      - destruct l0. reflexivity. discriminate.
      - destruct l0. destruct a. discriminate.
        destruct a, p.
        apply andb_prop in H. destruct H. apply andb_prop in H0. destruct H0.
        inv IHv1. inv H4. simpl in H2, H3. apply H2 in H. apply H3 in H0. subst v v0.
        specialize (IHl l0 H1 H5). inv IHl. reflexivity.
    + intros. simpl in H. destruct v2; try discriminate. apply Nat.eqb_eq in H. subst. reflexivity.
    + intros. simpl in H. destruct v2; try discriminate. unfold funid_eqb in H. destruct n, n0.
      apply andb_prop in H. destruct H. apply Nat.eqb_eq in H, H0. subst. reflexivity.
    + intros. simpl in H. destruct v2; try discriminate. apply andb_prop in H. destruct H.
      apply andb_prop in H. destruct H. apply andb_prop in H. destruct H.
      apply Nat.eqb_eq in H, H2. apply IHv0 in H1. subst id vl e.
      revert H0 IHv1. revert ext0.
      induction ext; intros.
      - destruct ext0. reflexivity. discriminate.
      - destruct a, p. destruct ext0. discriminate.
        destruct p, p. apply andb_prop in H0. destruct H0.
        apply andb_prop in H0. destruct H0. apply andb_prop in H1. destruct H1.
        apply Nat.eqb_eq in H0, H1. inv IHv1. apply H5 in H. subst e.
        specialize (IHext ext0 H2 H6). inv IHext. reflexivity.
    + intros. simpl in H. destruct e2; try discriminate. destruct e0; try discriminate.
      apply andb_prop in H. destruct H. apply Nat.eqb_eq in H.
      apply IHv1 in H0. subst. reflexivity.
    + intros. simpl in H. destruct e2; try discriminate. destruct e; try discriminate.
      revert H IHv1. revert el0. revert el.
      induction el; intros.
      - destruct el0. reflexivity. discriminate.
      - destruct el0. discriminate.
        apply andb_prop in H. destruct H.
        inv IHv1. apply H3 in H. subst a.
        specialize (IHel el0 H0 H4). inv IHel. reflexivity.
    + intros. simpl in H. destruct e2; try discriminate. destruct e; try discriminate.
      apply andb_prop in H. destruct H.
      apply IHv1 in H. apply IHv0 in H0. subst. reflexivity.
    + intros. simpl in H. destruct e2; try discriminate. destruct e; try discriminate.
      revert H IHv1. revert l0. revert l.
      induction l; intros.
      - destruct l0. reflexivity. discriminate.
      - destruct l0. discriminate.
        apply andb_prop in H. destruct H.
        inv IHv1. apply H3 in H. subst a.
        specialize (IHl l0 H0 H4). inv IHl. reflexivity.
    + intros. simpl in H. destruct e2; try discriminate. destruct e; try discriminate.
      revert H IHv1. revert l0.
      induction l; intros.
      - destruct l0. reflexivity. discriminate.
      - destruct a. destruct l0. discriminate.
        destruct p. apply andb_prop in H. destruct H. apply andb_prop in H0. destruct H0.
        inv IHv1. inv H4. simpl in H2, H3. apply H2 in H. apply H3 in H0. subst e e0.
        specialize (IHl l0 H1 H5). inv IHl. reflexivity.
    + intros. simpl in H. destruct e2; try discriminate. destruct e; try discriminate.
      apply andb_prop in H. destruct H. apply andb_prop in H. destruct H.
      apply IHv1 in H1. apply IHv0 in H. subst f m.
      revert H0 IHv2 IHv0 IHv1. revert l0.
      induction l; intros.
      - destruct l0. reflexivity. discriminate.
      - destruct l0. discriminate.
        apply andb_prop in H0. destruct H0. inv IHv2. apply H3 in H. subst a.
        specialize (IHl l0 H0 H4 IHv0 IHv1). inv IHl. reflexivity.
    + intros. simpl in H. destruct e2; try discriminate. destruct e; try discriminate.
      apply andb_prop in H. destruct H.
      apply String.eqb_eq in H. subst f.
      revert H0 IHv1. revert l0.
      induction l; intros.
      - destruct l0. reflexivity. discriminate.
      - destruct l0. discriminate.
        apply andb_prop in H0. destruct H0. inv IHv1. apply H3 in H. subst a.
        specialize (IHl l0 H0 H4). inv IHl. reflexivity.
    + intros. simpl in H. destruct e2; try discriminate. destruct e0; try discriminate.
      apply andb_prop in H. destruct H. apply IHv1 in H. subst e.
      revert H0 IHv0. revert l0.
      induction l; intros.
      - destruct l0. reflexivity. discriminate.
      - destruct l0. discriminate.
        apply andb_prop in H0. destruct H0. inv IHv0. apply H3 in H. subst a.
        specialize (IHl l0 H0 H4). inv IHl. reflexivity.
    + intros. simpl in H. destruct e2; try discriminate. destruct e0; try discriminate.
      apply andb_prop in H. destruct H. apply andb_prop in H. destruct H.
      apply IHv1 in H. subst e.
      revert H0 IHv0 H1. revert l0.
      induction l; intros.
      - destruct l0. reflexivity. discriminate.
      - destruct l0. discriminate.
        destruct a, p0, p, p.
        apply andb_prop in H0. destruct H0. apply andb_prop in H0. destruct H0.
        apply andb_prop in H2. destruct H2. inv IHv0. destruct H6.
        apply H4 in H0. apply H5 in H2. subst e e1.
        specialize (IHl l0 H3 H7 H1). inv IHl.
        clear H3. clear -H.
        revert H. revert l2.
        induction l1; intros.
        ** destruct l2. reflexivity. discriminate. 
        ** destruct l2. discriminate.
           apply andb_prop in H. destruct H. apply Pat_eqb_eq in H. subst a.
           specialize (IHl1 l2 H0). inv IHl1. reflexivity.
    + intros. simpl in H. destruct e0; try discriminate. destruct e; try discriminate.
      apply andb_prop in H. destruct H. apply andb_prop in H. destruct H.
      apply Nat.eqb_eq in H. apply IHv1 in H1. apply IHv0 in H0. subst. reflexivity.
    + intros. simpl in H. destruct e0; try discriminate. destruct e; try discriminate.
      apply andb_prop in H. destruct H.
      apply IHv1 in H. apply IHv0 in H0. subst. reflexivity.
    + intros. simpl in H. destruct e2; try discriminate. destruct e0; try discriminate.
      apply andb_prop in H. destruct H. apply IHv1 in H0. subst e.
      revert H IHv0. revert l0.
      induction l; intros.
      - destruct l0. reflexivity. discriminate.
      - destruct a. destruct l0. discriminate.
        destruct p. apply andb_prop in H. destruct H. apply andb_prop in H0. destruct H0.
        apply Nat.eqb_eq in H. subst n. inv IHv0. apply H3 in H0. subst e.
        specialize (IHl l0 H1 H4). inv IHl. reflexivity. 
    + intros. simpl in H. destruct e0; try discriminate. destruct e; try discriminate.
      apply andb_prop in H. destruct H. apply andb_prop in H. destruct H.
      apply andb_prop in H. destruct H. apply andb_prop in H. destruct H.
      apply Nat.eqb_eq in H, H3. apply IHv1 in H2. apply IHv0 in H1. apply IHv2 in H0.
      subst. reflexivity.
  * intro. rewrite H. apply Val_eqb_strict_refl.
Qed.

Lemma Exp_eqb_strict_eq: forall e1 e2, Exp_eqb_strict e1 e2 = true <-> e1 = e2.
Proof.
  intros. split.
  * revert e2.
    induction e1 using Exp_ind2 with
    (PV := fun _ => True)
    (PE := fun e => forall e2, Exp_eqb_strict e e2 = true -> e = e2)
    (Q  := Forall (fun e => forall e2, Exp_eqb_strict e e2 = true -> e = e2))
    (QV := fun _ => True)
    (R  := Forall (PBoth (fun e => forall e2, Exp_eqb_strict e e2 = true -> e = e2)))
    (RV := fun _ => True)
    (VV := fun _ => True)
    (W  := Forall (fun '(_, e, e') => (forall e2,  Exp_eqb_strict e  e2  = true -> e  = e2) /\
                                        (forall e2', Exp_eqb_strict e' e2' = true -> e' = e2')))
    (Z  := Forall (fun '(_, e) => forall e2, Exp_eqb_strict e e2 = true -> e = e2)); auto.
    + intros. simpl in H. destruct e2; try discriminate.
      apply Val_eqb_strict_eq in H. subst. reflexivity.
    + intros. simpl in H. destruct e2; try discriminate. destruct e; try discriminate.
      apply andb_prop in H. destruct H.
      apply Nat.eqb_eq in H. apply IHe1 in H0. subst. reflexivity.
    + intros. simpl in H. destruct e2; try discriminate. destruct e; try discriminate.
      revert H IHe1. revert el0.
      induction el; intros.
      - destruct el0; try discriminate. reflexivity.
      - destruct el0. discriminate.
        apply andb_prop in H. destruct H.
        inv IHe1. apply H3 in H. subst a.
        specialize (IHel el0 H0 H4). inv IHel. reflexivity.
    + intros. simpl in H. destruct e2; try discriminate. destruct e; try discriminate.
      apply andb_prop in H. destruct H.
      apply IHe1_1 in H. apply IHe1_2 in H0. subst. reflexivity.
    + intros. simpl in H. destruct e2; try discriminate. destruct e; try discriminate.
      revert H IHe1. revert l0.
      induction l; intros.
      - destruct l0; try discriminate. reflexivity.
      - destruct l0. discriminate.
        apply andb_prop in H. destruct H.
        inv IHe1. apply H3 in H. subst a.
        specialize (IHl l0 H0 H4). inv IHl. reflexivity.
    + intros. simpl in H. destruct e2; try discriminate. destruct e; try discriminate.
      revert H IHe1. revert l0.
      induction l; intros.
      - destruct l0; try discriminate. reflexivity.
      - destruct a. destruct l0. discriminate.
        destruct p. apply andb_prop in H. destruct H. apply andb_prop in H0. destruct H0.
        inv IHe1. inv H4. apply H2 in H. apply H3 in H0. subst e1 e2.
        specialize (IHl l0 H1 H5). inv IHl. reflexivity.
    + intros. simpl in H. destruct e2; try discriminate. destruct e; try discriminate.
      apply andb_prop in H. destruct H. apply andb_prop in H. destruct H.
      apply IHe1_2 in H. apply IHe1_1 in H1. subst f m.
      revert H0 IHe1_3. revert l0.
      induction l; intros.
      - destruct l0; try discriminate. reflexivity.
      - destruct l0. discriminate.
        apply andb_prop in H0. destruct H0.
        inv IHe1_3. apply H3 in H. subst a.
        specialize (IHl l0 H0 H4). inv IHl. reflexivity.
    + intros. simpl in H. destruct e2; try discriminate. destruct e; try discriminate.
      apply andb_prop in H. destruct H.
      apply String.eqb_eq in H. subst f.
      revert H0 IHe1. revert l0.
      induction l; intros.
      - destruct l0; try discriminate. reflexivity.
      - destruct l0. discriminate.
        apply andb_prop in H0. destruct H0.
        inv IHe1. apply H3 in H. subst a.
        specialize (IHl l0 H0 H4). inv IHl. reflexivity.
    + intros. simpl in H. destruct e2; try discriminate. destruct e; try discriminate.
      apply andb_prop in H. destruct H.
      apply IHe1 in H. subst e1.
      revert H0 IHe0. revert l0.
      induction l; intros.
      - destruct l0; try discriminate. reflexivity.
      - destruct l0. discriminate.
        apply andb_prop in H0. destruct H0.
        inv IHe0. apply H3 in H. subst a.
        specialize (IHl l0 H0 H4). inv IHl. reflexivity.
    + intros. simpl in H. destruct e2; try discriminate. destruct e; try discriminate.
      apply andb_prop in H. destruct H. apply andb_prop in H. destruct H. clear H1.
      apply IHe1 in H. subst e.
      revert H0 IHe0. revert l0.
      induction l; intros.
      - destruct l0; try discriminate. reflexivity.
      - destruct a, p. destruct l0. discriminate.
        destruct p, p.
        apply andb_prop in H0. destruct H0. apply andb_prop in H0. destruct H0.
        apply andb_prop in H1. destruct H1.
        inv IHe0. destruct H5.
        apply H3 in H0. apply H4 in H1. subst e0 e.
        specialize (IHl l0 H2 H6). inv IHl.
        clear -H. revert H. revert l2.
        induction l1; intros.
        ** destruct l2; try discriminate. reflexivity. 
        ** destruct l2. discriminate.
           apply andb_prop in H. destruct H.
           apply Pat_eqb_eq in H. subst a.
           specialize (IHl1 l2 H0). inv IHl1. reflexivity.
    + intros. simpl in H. destruct e2;try discriminate. destruct e; try discriminate.
      apply andb_prop in H. destruct H. apply andb_prop in H. destruct H.
      apply IHe1_1 in H1. apply IHe1_2 in H0. apply Nat.eqb_eq in H. subst. reflexivity.
    + intros. simpl in H. destruct e2; try discriminate. destruct e; try discriminate.
      apply andb_prop in H. destruct H. apply IHe1_1 in H. apply IHe1_2 in H0.
      subst. reflexivity.
    + intros. simpl in H. destruct e2; try discriminate. destruct e; try discriminate.
      revert H IHe0. revert l0.
      induction l; intros.
      - destruct l0; try discriminate.
        simpl in H. apply IHe1 in H. subst. reflexivity.
      - destruct a. destruct l0. discriminate.
        destruct p. apply andb_prop in H. destruct H. apply andb_prop in H. destruct H.
        apply andb_prop in H1. destruct H1.
        apply IHe1 in H0. apply Nat.eqb_eq in H.
        inv IHe0. apply H5 in H1. subst.
        setoid_rewrite Exp_eqb_strict_refl in IHl.
        setoid_rewrite andb_comm in IHl. simpl in IHl.
        specialize (IHl l0 H2 H6). inv IHl. reflexivity.
    + intros. simpl in H. destruct e2; try discriminate. destruct e; try discriminate.
      apply andb_prop in H. destruct H. apply andb_prop in H. destruct H.
      apply andb_prop in H. destruct H. apply andb_prop in H. destruct H.
      apply IHe1_1 in H2. apply IHe1_2 in H1. apply IHe1_3 in H0.
      apply Nat.eqb_eq in H, H3. subst. reflexivity.
  * intro. rewrite H. apply Exp_eqb_strict_refl.
Qed.

Definition Signal_eqb_strict (sig1 sig2 : Signal) : bool :=
  match sig1, sig2 with
  | SMessage v1, SMessage v2 => Val_eqb_strict v1 v2
  | SExit v1 b1, SExit v2 b2 => Val_eqb_strict v1 v2 && Bool.eqb b1 b2
  | SLink, SLink => true
  | SUnlink, SUnlink => true
  | _, _ => false
  end.

Lemma Signal_eqb_strict_refl: forall sig, Signal_eqb_strict sig sig = true.
Proof.
  intros. destruct sig; simpl; auto.
  * apply Val_eqb_strict_refl.
  * rewrite Val_eqb_strict_refl. simpl. apply eqb_reflx.
Qed.

Lemma Signal_eqb_strict_eq: forall sig1 sig2, Signal_eqb_strict sig1 sig2 = true <-> sig1 = sig2.
Proof.
  intros. split; intro.
  * unfold Signal_eqb_strict in H. destruct sig1 eqn:Hs1.
    + destruct sig2 eqn:Hs2; try discriminate.
      apply Val_eqb_strict_eq in H. subst. reflexivity.
    + destruct sig2 eqn:Hs2; try discriminate.
      symmetry in H. apply andb_true_eq in H. destruct H.
      symmetry in H0, H. apply eqb_prop in H0. apply Val_eqb_strict_eq in H.
      subst. reflexivity.
    + destruct sig2 eqn:Hs2; try discriminate. reflexivity.
    + destruct sig2 eqn:Hs2; try discriminate. reflexivity.
  * rewrite H. apply Signal_eqb_strict_refl.
Qed.