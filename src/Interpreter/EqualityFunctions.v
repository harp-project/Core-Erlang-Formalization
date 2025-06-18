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
  * revert v1 v2. induction v1; intros.
    + destruct v2; try discriminate. reflexivity.
    + destruct v2; try discriminate. simpl in H. apply Lit_eqb_eq in H. rewrite H. reflexivity.
    + destruct v2; try discriminate. simpl in H. apply Nat.eqb_eq in H. rewrite H. reflexivity.
    + destruct v2; try discriminate. simpl in H. apply andb_true_iff in H. destruct H.
      apply IHv1_1 in H. apply IHv1_2 in H0. rewrite H, H0. reflexivity.
    + destruct v2; try discriminate. simpl in H. admit.
    + destruct v2; try discriminate. simpl in H. admit.
    + destruct v2; try discriminate. simpl in H. apply Nat.eqb_eq in H. rewrite H. reflexivity.
    + destruct v2; try discriminate. simpl in H. unfold funid_eqb in H. destruct n, n0.
      apply andb_true_iff in H. destruct H. apply Nat.eqb_eq in H, H0. rewrite H, H0. reflexivity.
    + destruct v2; try discriminate. simpl in H. admit.
  * intro. rewrite H. apply Val_eqb_strict_refl.
Admitted.

Print Signal.

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



















