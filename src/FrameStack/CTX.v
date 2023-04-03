From CoreErlang.FrameStack Require Export CIU.

Import ListNotations.

Definition Adequate (R : nat -> Exp -> Exp -> Prop) :=
  forall p1 p2, R 0 p1 p2 -> |[], p1| ↓ -> |[], p2| ↓.

Definition IsReflexive (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ p,
  EXP Γ ⊢ p -> R Γ p p.


(*---------------------------- Non Value Expr Comp ------------------------------------------------------*)

Definition CompatibleFun (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ vl vl' e1 e2, vl = vl' ->
    EXP (vl + Γ) ⊢ e1 -> EXP (vl' + Γ) ⊢ e2 -> 
    R (vl + Γ) e1 e2 ->
    R Γ (EFun vl e1) (EFun vl' e2).

Definition CompatibleValues (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ el el', length el = length el' ->
    Forall (fun e => EXP Γ ⊢ e) el ->
    Forall (fun e => EXP Γ ⊢ e) el' ->
    list_biforall (R Γ) el el' ->
    R Γ (EValues el) (EValues el').

Definition CompatibleCons (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ e1 e1' e2 e2',
    EXP Γ ⊢ e1 -> EXP Γ ⊢ e1' -> 
    EXP Γ ⊢ e2 -> EXP Γ ⊢ e2' ->
    R Γ e1 e1' -> 
    R Γ e2 e2' ->
    R Γ (ECons e1 e2) (ECons e1' e2').

Definition CompatibleTuple (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ el el', length el = length el' ->
    Forall (fun e => EXP Γ ⊢ e) el ->
    Forall (fun e => EXP Γ ⊢ e) el' ->
    list_biforall (R Γ) el el' ->
    R Γ (ETuple el) (ETuple el').

Definition CompatibleMap (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ l l', length l = length l' ->
    Forall (PBoth (fun e => EXP Γ ⊢ e)) l ->
    Forall (PBoth (fun e => EXP Γ ⊢ e)) l' ->
    list_biforall (fun '(v1, v2) '(v1', v2') => R Γ v1 v1' /\ R Γ v2 v2') l l' ->
    R Γ (EMap l) (EMap l').

Definition CompatibleCall (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ m m' f f' el el', m = m' -> f = f' -> length el = length el' ->
  Forall (fun e => EXP Γ ⊢ e) el ->
  Forall (fun e => EXP Γ ⊢ e) el' ->
  list_biforall (R Γ) el el' ->
    R Γ (ECall m f el) (ECall m' f' el').

Definition CompatiblePrimOp (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ f f' el el', f = f' -> length el = length el' ->
    Forall (fun e => EXP Γ ⊢ e) el ->
    Forall (fun e => EXP Γ ⊢ e) el' ->
    list_biforall (R Γ) el el' ->
    R Γ (EPrimOp f el) (EPrimOp f' el').

Definition CompatibleApp (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ e e' el el', length el = length el' ->
    EXP Γ ⊢ e ->
    EXP Γ ⊢ e' ->
    Forall (fun e => EXP Γ ⊢ e) el ->
    Forall (fun e => EXP Γ ⊢ e) el' ->
    R Γ e e' ->
    list_biforall (R Γ) el el' ->
    R Γ (EApp e el) (EApp e' el').

Definition CompatibleCase (R : nat -> Exp -> Exp -> Prop) := (* TODO: l or l' in places? *)
  forall Γ e e' l l', length l = length l' ->
    EXP Γ ⊢ e ->
    EXP Γ ⊢ e' ->
    Forall (fun '(p, g, e) => EXP PatListScope p + Γ ⊢ g /\ EXP PatListScope p + Γ ⊢ e) l ->
    Forall (fun '(p, g, e) => EXP PatListScope p + Γ ⊢ g /\ EXP PatListScope p + Γ ⊢ e) l' ->
    R Γ e e' ->
    list_biforall (
      fun '(p, g, e) '(p', g', e') =>
        p = p' /\ R (PatListScope p + Γ) g g' /\
        R (PatListScope p + Γ) e e'
    ) l l' ->
    R Γ (ECase e l) (ECase e' l').

Definition CompatibleLet (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ l e1 e2 l' e1' e2', l = l' ->
    EXP Γ ⊢ e1  ->
    EXP Γ ⊢ e1' ->
    EXP (l  + Γ) ⊢ e2  ->
    EXP (l' + Γ) ⊢ e2' ->
    R Γ       e1 e1' ->
    R (l + Γ) e2 e2' ->
    R Γ (ELet l e1 e2) (ELet l' e1' e2').

Definition CompatibleSeq (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ e1 e2 e1' e2',
    EXP Γ ⊢ e1  ->
    EXP Γ ⊢ e1' ->
    EXP Γ ⊢ e2  ->
    EXP Γ ⊢ e2' ->
    R Γ e1 e1' ->
    R Γ e2 e2' ->
    R Γ (ESeq e1 e2) (ESeq e1' e2').

Definition CompatibleLetRec (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ e l e' l', length l = length l' ->
    EXP (length l  + Γ) ⊢ e  ->
    EXP (length l' + Γ) ⊢ e' ->
    Forall (fun '(vl, e) => EXP length l + vl + Γ ⊢ e) l  ->
    Forall (fun '(vl, e) => EXP length l' + vl + Γ ⊢ e) l' -> 
    list_biforall (fun '(v, e) '(v', e') =>
      v = v' /\ R (length l + v + Γ) e e'
    ) l l' ->
    R (length l + Γ) e e' ->
    R Γ (ELetRec l e) (ELetRec l' e').

Definition CompatibleTry (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ e1 vl1 e2 vl2 e3 e1' vl1' e2' vl2' e3', 
    vl1 = vl1' -> vl2 = vl2' ->
    EXP Γ ⊢ e1  ->
    EXP Γ ⊢ e1' ->
    EXP (vl1  + Γ) ⊢ e2  ->
    EXP (vl1' + Γ) ⊢ e2' ->
    EXP (vl2  + Γ) ⊢ e3  ->
    EXP (vl2' + Γ) ⊢ e3' ->
    R Γ e1 e1' ->
    R (vl1 + Γ) e2 e2' ->
    R (vl2 + Γ) e3 e3' ->
    R Γ (ETry e1 vl1 e2 vl2 e3) (ETry e1' vl1' e2' vl2' e3').

(*------------------------------ Value Expr Comp --------------------------------------------------------*)

Definition CompatibleNil (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ,
    R Γ (VVal VNil) (VVal VNil).

Definition CompatibleLit (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ l l',
    l = l' ->
    R Γ (VVal (VLit l)) (VVal (VLit l')).

Definition VCompatibleCons (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ e1 e1' e2 e2',
    VAL Γ ⊢ e1 -> VAL Γ ⊢ e1' -> 
    VAL Γ ⊢ e2 -> VAL Γ ⊢ e2' ->
    R Γ (VVal e1) (VVal e1') -> 
    R Γ (VVal e2) (VVal e2') ->
    R Γ (VVal (VCons e1 e2)) (VVal (VCons e1' e2')).

Definition VCompatibleTuple (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ el el', length el = length el' ->
    Forall (fun e => VAL Γ ⊢ e) el ->
    Forall (fun e => VAL Γ ⊢ e) el' ->
    list_biforall (R Γ) (map VVal el) (map VVal el') ->
    R Γ (VVal (VTuple el)) (VVal (VTuple el')).

Definition VCompatibleMap (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ l l', length l = length l' ->
    Forall (PBoth (fun e => VAL Γ ⊢ e)) l ->
    Forall (PBoth (fun e => VAL Γ ⊢ e)) l' ->
    list_biforall (fun '(v1, v2) '(v1', v2') => R Γ v1 v1' /\ R Γ v2 v2')
      (map (fun '(x, y) => (VVal x, VVal y)) l)
      (map (fun '(x, y) => (VVal x, VVal y)) l') ->
    R Γ (VVal (VMap l)) (VVal (VMap l')).

Definition CompatibleVar (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ n n',
    n = n' ->
    n  > Γ ->
    n' > Γ ->
    R Γ (VVal (VVar n)) (VVal (VVar n')).

Definition CompatibleFunId (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ n n' a a',
    n = n' -> a = a' ->
    n  > Γ ->
    n' > Γ ->
    R Γ (VVal (VFunId (n, a))) (VVal (VFunId (n', a'))).

Definition CompatibleClos (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ ext id vl e ext' id' vl' e',
    length ext = length ext' ->
    id = id' -> vl = vl' ->
    EXP (length ext  + vl  + Γ) ⊢ e  -> 
    EXP (length ext' + vl' + Γ) ⊢ e' -> 
    Forall (fun '(i, v, e) => EXP length ext + v + Γ ⊢ e) ext ->
    Forall (fun '(i, v, e) => EXP length ext + v + Γ ⊢ e) ext' ->
    R (length ext + vl + Γ) e e' ->
    list_biforall (fun '(i, v, e) '(i2, v2, e2) => 
      v = v2 /\ i = i2 /\ R (length ext + v + Γ) e e2) ext ext' ->
    R Γ (VVal (VClos ext id vl e)) (VVal (VClos ext' id' vl' e')).

(*---------------------------- Meta Defs ------------------------------------------------------*)

Definition IsPreCtxRel (R : nat -> Exp -> Exp -> Prop) :=
  (forall Γ p1 p2, R Γ p1 p2 -> EXP Γ ⊢ p1 /\ EXP Γ ⊢ p2) /\
  Adequate R /\ IsReflexive R /\
  (forall Γ, Transitive (R Γ)) /\
  CompatibleFun R /\
  CompatibleValues R /\
  CompatibleCons R /\
  CompatibleTuple R /\
  CompatibleMap R /\
  CompatibleCall R /\
  CompatiblePrimOp R /\
  CompatibleApp R /\
  CompatibleCase R /\
  CompatibleLet R /\
  CompatibleSeq R /\
  CompatibleLetRec R /\
  CompatibleTry R /\
  CompatibleNil R /\
  CompatibleLit R /\
  VCompatibleCons R /\
  VCompatibleTuple R /\
  VCompatibleMap R /\
  CompatibleVar R /\
  CompatibleFunId R /\
  CompatibleClos R.

Definition IsCtxRel (R : nat -> Exp -> Exp -> Prop) :=
  IsPreCtxRel R /\
  forall R', IsPreCtxRel R' ->
    forall Γ p1 p2, R' Γ p1 p2 -> R Γ p1 p2.








Lemma bigger_implies_IsCtxRel : forall E R,
    IsCtxRel R ->
    IsPreCtxRel E ->
    (forall Γ e1 e2, R Γ e1 e2 -> E Γ e1 e2) ->
    IsCtxRel E.
Proof.
  intros.
  split; auto.
  intros.
  apply H1.
  destruct H.
  eapply H4.
  - exact H2.
  - auto.
Qed.

Theorem Erel_IsPreCtxRel : IsPreCtxRel Erel_open.
Proof.
  unfold IsPreCtxRel.
  intuition.
  1-2: apply Erel_open_scope in H; apply H.
  * unfold Adequate.
    intros.
    assert (Rrel_open 0 p1 p2). { auto. }
    apply CIU_iff_Rrel in H1.
    unfold CIU_open, CIU in H1.
    specialize (H1 idsubst (scope_idsubst 0)).
    destruct H1 as [_ [_ H1]]. simpl in H1. do 2 rewrite idsubst_is_id_exp in H1.
    apply H1.
    now constructor. auto.
  * unfold IsReflexive.
    intros.
    apply Erel_Fundamental.
    auto.
  * unfold Transitive.
    intros.
    assert (Rrel_open Γ x y). { auto. }
    assert (Rrel_open Γ y z). { auto. }
    apply Rrel_exp_compat_reverse.
    apply CIU_iff_Rrel.
    apply CIU_iff_Rrel in H1.
    apply CIU_iff_Rrel in H2.
    unfold CIU_open in *.
    intros.
    specialize (H1 ξ H3).
    specialize (H2 ξ H3).
    unfold CIU in *.
    intuition idtac.
    specialize (H7 F H6).
    specialize (H8 F H6).
    auto.
  * unfold CompatibleFun.
    intros.
    auto.
  * unfold CompatibleValues.
    intros.
    auto.
  * unfold CompatibleCons.
    intros.
    auto.
  * unfold CompatibleTuple.
    intros.
    auto.
  * unfold CompatibleMap.
    intros.
    auto.
  * unfold CompatibleCall.
    intros.
    auto.
  * unfold CompatiblePrimOp.
    intros.
    auto.
  * unfold CompatibleApp.
    intros.
    auto.
  * unfold CompatibleCase.
    intros.
    auto.
  * unfold CompatibleLet.
    intros.
    apply Erel_Let_compat; auto.
  * unfold CompatibleSeq.
    intros.
    auto.
  * unfold CompatibleLetRec.
    intros.
    auto.
  * unfold CompatibleTry.
    intros.
    auto.
  * unfold CompatibleNil. auto.
  * unfold CompatibleLit. intros. subst. auto.
  * unfold VCompatibleCons. intros.
    assert (Rrel_open Γ (` e1) (` e1')) by auto.
    assert (Rrel_open Γ (` e2) (` e2')) by auto.
    apply CIU_iff_Rrel in H5, H6.
    apply Rrel_exp_compat_reverse, CIU_iff_Rrel.

Qed.

Corollary CIU_IsPreCtxRel : IsPreCtxRel CIU_open.


Inductive Ctx :=
| CHole
| CFun     (vl : nat) (c : Ctx)
| CValues  (el : list Exp) (c : Ctx) (el' : list Exp)
| CCons1   (c : Ctx) (tl : Exp)
| CCons2   (hd : Exp) (c : Ctx)
| CTuple   (l : list Exp) (c : Ctx) (l' : list Exp)
| CMap1    (l : list (Exp * Exp)) (c : Ctx) (e2 : Exp) (l' : list (Exp * Exp))
| CMap2    (l : list (Exp * Exp)) (e1 : Exp) (c : Ctx) (l' : list (Exp * Exp))
| CCall    (m f : string)    (l : list Exp) (c : Ctx) (l' : list Exp)
| CPrimOp  (f : string)    (l : list Exp) (c : Ctx) (l' : list Exp)
| CApp1    (c : Ctx) (l : list Exp)
| CApp2    (exp: Exp) (l : list Exp) (c : Ctx) (l' : list Exp)
| CCase1   (c : Ctx) (l : list ((list Pat) * Exp * Exp))
| CCase2   (e : Exp) (l : list ((list Pat) * Exp * Exp)) (lp : (list Pat)) (c : Ctx) (e2 : Exp) (l' : list ((list Pat) * Exp * Exp))
| CCase3   (e : Exp) (l : list ((list Pat) * Exp * Exp)) (lp : (list Pat)) (e1 : Exp) (c : Ctx) (l' : list ((list Pat) * Exp * Exp))
| CLet1    (l : nat) (c : Ctx) (e2 : Exp)
| CLet2    (l : nat) (e1: Exp) (c : Ctx)
| CSeq1    (c : Ctx) (e2 : Exp)
| CSeq2    (e1 : Exp) (c : Ctx)
| CLetRec1 (l : list (nat * Exp)) (n : nat) (c : Ctx) (l' : list (nat * Exp)) (e : Exp)
| CLetRec2 (l : list (nat * Exp)) (c : Ctx)
| CTry1    (c : Ctx) (vl1 : nat) (e2 : Exp) (vl2 : nat) (e3 : Exp)
| CTry2    (e1 : Exp) (vl1 : nat) (c : Ctx) (vl2 : nat) (e3 : Exp)
| CTry3    (e1 : Exp) (vl1 : nat) (e2 : Exp) (vl2 : nat) (c : Ctx)
.

Fixpoint plug (C : Ctx) (p : Exp) :=
match C with
| CHole              => p
| CFun    vl c       => EExp ( EFun vl (plug c p) )
| CValues el c el'   => EExp ( EValues (el ++ [(plug c p)] ++ el') )
| CCons1  c tl       => EExp ( ECons (plug c p) tl )
| CCons2  hd c       => EExp ( ECons hd (plug c p) )
| CTuple  l c l'     => EExp ( ETuple (l ++ [(plug c p)] ++ l') )
| CMap1   l c e2 l'  => EExp ( EMap (l ++ [((plug c p), e2)] ++ l') )
| CMap2   l e1 c l'  => EExp ( EMap (l ++ [(e1, (plug c p))] ++ l') )
| CCall   m f l c l'   => EExp ( ECall m f (l ++ [(plug c p)] ++ l') )
| CPrimOp f l c l'   => EExp ( EPrimOp f (l ++ [(plug c p)] ++ l') )
| CApp1   c l        => EExp ( EApp (plug c p) l )
| CApp2   exp l c l' => EExp ( EApp exp (l ++ [(plug c p)] ++ l') )
| CCase1  c l        => EExp ( ECase (plug c p) l )
| CCase2  e l lp c e2 l' => EExp ( ECase e (l ++ [(lp, (plug c p), e2)] ++ l') )
| CCase3  e l lp e1 c l' => EExp ( ECase e (l ++ [(lp, e1, (plug c p))] ++ l') )
| CLet1   l c e2     => EExp ( ELet l (plug c p) e2 )
| CLet2   l e1 c     => EExp ( ELet l e1 (plug c p) )
| CSeq1   c e2       => EExp ( ESeq (plug c p) e2 )
| CSeq2   e1 c       => EExp ( ESeq e1 (plug c p) )
| CLetRec1 l n c l' e => EExp ( ELetRec (l ++ [(n, (plug c p))] ++ l') e )
| CLetRec2 l c     => EExp ( ELetRec l (plug c p) )
| CTry1   c vl1 e2 vl2 e3  => EExp ( ETry (plug c p) vl1 e2 vl2 e3 )
| CTry2   e1 vl1 c vl2 e3  => EExp ( ETry e1 vl1 (plug c p) vl2 e3 )
| CTry3   e1 vl1 e2 vl2 c  => EExp ( ETry e1 vl1 e2 vl2 (plug c p) )
end.

Fixpoint plugc (C : Ctx) (p : Ctx) :=
match C with
| CHole             => p
| CFun    vl c      => CFun vl (plugc c p)
| CValues el c el'  => CValues el (plugc c p) el'
| CCons1  c tl      => CCons1 (plugc c p) tl
| CCons2  hd c      => CCons2 hd (plugc c p)
| CTuple  l c l'    => CTuple l (plugc c p) l'
| CMap1   l c e2 l' => CMap1 l (plugc c p) e2 l'
| CMap2   l e1 c l' => CMap2 l e1 (plugc c p) l'
| CCall   m f l c l'  => CCall m f l (plugc c p) l'
| CPrimOp f l c l'  => CPrimOp f l (plugc c p) l'
| CApp1   c l       => CApp1 (plugc c p) l
| CApp2   exp l c l' => CApp2 exp l (plugc c p) l'
| CCase1  c l       => CCase1 (plugc c p) l
| CCase2  e l lp c e2 l' => CCase2 e l lp (plugc c p) e2 l'
| CCase3  e l lp e1 c l' => CCase3 e l lp e1 (plugc c p) l'
| CLet1   l c e2    => CLet1 l (plugc c p) e2
| CLet2   l e1 c    => CLet2 l e1 (plugc c p)
| CSeq1   c e2      => CSeq1 (plugc c p) e2
| CSeq2   e1 c      => CSeq2 e1 (plugc c p)
| CLetRec1 l n c l' e => CLetRec1 l n (plugc c p) l' e
| CLetRec2 l c      => CLetRec2 l (plugc c p)
| CTry1   c vl1 e2 vl2 e3  => CTry1 (plugc c p) vl1 e2 vl2 e3
| CTry2   e1 vl1 c vl2 e3  => CTry2 e1 vl1 (plugc c p) vl2 e3
| CTry3   e1 vl1 e2 vl2 c  => CTry3 e1 vl1 e2 vl2 (plugc c p)
end.


Lemma plug_assoc : forall C1 C2 e,
    plug C1 (plug C2 e) =
    plug (plugc C1 C2) e.
Proof.
  induction C1;
    intros;
    cbn;
    auto;
    rewrite IHC1;
    auto.
Qed.

Reserved Notation "'EECTX' Γh ⊢ C ∷ Γ" (at level 60).
(* Reserved Notation "'VECTX' Γh ⊢ C ∷ Γ" (at level 60). *)

Inductive EECtxScope (Γh : nat) : nat -> Ctx -> Prop :=

| CEScope_Hole : (EECTX Γh ⊢ CHole ∷ Γh)

| CEScope_CFun : forall Γ vl c,
  EECTX Γh ⊢ c ∷ (vl + Γ) -> 
  EECTX Γh ⊢ (CFun vl c) ∷ Γ

| CEScope_CValues : forall Γ el c el',
  Forall (fun e => EXP Γ ⊢ e) el ->
  EECTX Γh ⊢ c ∷ Γ ->
  Forall (fun e => EXP Γ ⊢ e) el' ->
  EECTX Γh ⊢ (CValues el c el') ∷ Γ

| CEScope_CCons1 : forall Γ c tl,
  EECTX Γh ⊢ c ∷ Γ ->
  EXP Γ ⊢ tl ->
  EECTX Γh ⊢ (CCons1 c tl) ∷ Γ

| CEScope_CCons2 : forall Γ hd c,
  EXP Γ ⊢ hd ->
  EECTX Γh ⊢ c ∷ Γ ->
  EECTX Γh ⊢ (CCons2 hd c) ∷ Γ

| CEScope_CTuple : forall Γ l c l',
  Forall (fun e => EXP Γ ⊢ e) l ->
  EECTX Γh ⊢ c ∷ Γ ->
  Forall (fun e => EXP Γ ⊢ e) l' ->
  EECTX Γh ⊢ (CTuple l c l') ∷ Γ

| CEScope_CMap1 : forall Γ l c e2 l',
  Forall (PBoth (fun e => EXP Γ ⊢ e)) l ->
  Forall (PBoth (fun e => EXP Γ ⊢ e)) l' ->
  EECTX Γh ⊢ c ∷ Γ ->
  EXP Γ ⊢ e2 ->
  EECTX Γh ⊢ (CMap1 l c e2 l') ∷ Γ

| CEScope_CMap2 : forall Γ l e1 c l',
  Forall (PBoth (fun e => EXP Γ ⊢ e)) l ->
  Forall (PBoth (fun e => EXP Γ ⊢ e)) l' ->
  EXP Γ ⊢ e1 ->
  EECTX Γh ⊢ c ∷ Γ ->
  EECTX Γh ⊢ (CMap2 l e1 c l') ∷ Γ

| CEScope_CCall : forall Γ m f l c l',
  Forall (fun e => EXP Γ ⊢ e) l ->
  EECTX Γh ⊢ c ∷ Γ ->
  Forall (fun e => EXP Γ ⊢ e) l' ->
  EECTX Γh ⊢ (CCall m f l c l') ∷ Γ

| CEScope_CPrimOp : forall Γ f l c l',
  Forall (fun e => EXP Γ ⊢ e) l ->
  EECTX Γh ⊢ c ∷ Γ ->
  Forall (fun e => EXP Γ ⊢ e) l' ->
  EECTX Γh ⊢ (CPrimOp f l c l') ∷ Γ

| CEScope_CApp1 : forall Γ c l,
  EECTX Γh ⊢ c ∷ Γ ->
  Forall (fun e => EXP Γ ⊢ e) l ->
  EECTX Γh ⊢ (CApp1 c l) ∷ Γ

| CEScope_CApp2 : forall Γ exp l c l',
  EXP Γ ⊢ exp ->
  Forall (fun e => EXP Γ ⊢ e) l ->
  EECTX Γh ⊢ c ∷ Γ ->
  Forall (fun e => EXP Γ ⊢ e) l' ->
  EECTX Γh ⊢ (CApp2 exp l c l') ∷ Γ

| CEScope_CCase1 : forall Γ c l,
  EECTX Γh ⊢ c ∷ Γ ->
  Forall (fun '(p, g, e) => EXP PatListScope p + Γ ⊢ g /\ EXP PatListScope p + Γ ⊢ e) l ->
  EECTX Γh ⊢ (CCase1 c l) ∷ Γ


| CEScope_CCase2 : forall Γ e l lp c e2 l',
  EXP Γ ⊢ e ->
  EXP PatListScope lp + Γ ⊢ e2 ->
  Forall (fun '(p, g, e) => EXP PatListScope p + Γ ⊢ g /\ EXP PatListScope p + Γ ⊢ e) l ->
  Forall (fun '(p, g, e) => EXP PatListScope p + Γ ⊢ g /\ EXP PatListScope p + Γ ⊢ e) l' ->
  EECTX Γh ⊢ c ∷ ((PatListScope lp) + Γ) ->
  EECTX Γh ⊢ (CCase2 e l lp c e2 l') ∷ Γ

| CEScope_CCase3 : forall Γ e l lp e1 c l',
  EXP Γ ⊢ e ->
  EXP (PatListScope lp + Γ) ⊢ e1 ->
  Forall (fun '(p, g, e) => EXP PatListScope p + Γ ⊢ g /\ EXP PatListScope p + Γ ⊢ e) l ->
  Forall (fun '(p, g, e) => EXP PatListScope p + Γ ⊢ g /\ EXP PatListScope p + Γ ⊢ e) l' ->
  EECTX Γh ⊢ c ∷ ((PatListScope lp) + Γ) ->
  EECTX Γh ⊢ (CCase3 e l lp e1 c l') ∷ Γ

| CEScope_CLet1 : forall Γ l c e2,
  EECTX Γh ⊢ c ∷ Γ ->
  EXP (l + Γ) ⊢ e2 ->
  EECTX Γh ⊢ (CLet1 l c e2) ∷ Γ

| CEScope_CLet2 : forall Γ l e1 c,
  EXP Γ ⊢ e1 ->
  EECTX Γh ⊢ c ∷ (l + Γ) ->
  EECTX Γh ⊢ (CLet2 l e1 c) ∷ Γ

| CEScope_CSeq1 : forall Γ c e2,
  EECTX Γh ⊢ c ∷ Γ ->
  EXP Γ ⊢ e2 ->
  EECTX Γh ⊢ (CSeq1 c e2) ∷ Γ

| CEScope_CSeq2 : forall Γ e1 c,
  EXP Γ ⊢ e1 ->
  EECTX Γh ⊢ c ∷ Γ ->
  EECTX Γh ⊢ (CSeq2 e1 c) ∷ Γ

| CEScope_CLetRec1 : forall Γ l n c l' e,
  Forall (fun '(vl, e) => EXP length l + S (length l') + vl + Γ ⊢ e) l  ->
  EECTX Γh ⊢ c ∷ ((length l) + S (length l') + n + Γ) ->
  Forall (fun '(vl, e) => EXP length l + S (length l') + vl + Γ ⊢ e) l'  ->
  EXP (length l + S (length l') + Γ) ⊢ e ->
  EECTX Γh ⊢ (CLetRec1 l n c l' e) ∷ Γ

| CEScope_CLetRec2 : forall Γ l c,
  Forall (fun '(vl, e) => EXP length l + vl + Γ ⊢ e) l  ->
  EECTX Γh ⊢ c ∷ (length l + Γ) ->
  EECTX Γh ⊢ (CLetRec2 l c) ∷ Γ

| CEScope_CTry1 : forall Γ c vl1 e2 vl2 e3,
  EECTX Γh ⊢ c ∷ Γ ->
  EXP (vl1 + Γ) ⊢ e2 ->
  EXP (vl2 + Γ) ⊢ e3 ->
  EECTX Γh ⊢ (CTry1 c vl1 e2 vl2 e3) ∷ Γ

| CEScope_CTry2 : forall Γ e1 vl1 c vl2 e3,
  EXP Γ ⊢ e1 ->
  EECTX Γh ⊢ c ∷ (vl1 + Γ) ->
  EXP (vl2 + Γ) ⊢ e3 ->
  EECTX Γh ⊢ (CTry2 e1 vl1 c vl2 e3) ∷ Γ

| CEScope_CTry3 : forall Γ e1 vl1 e2 vl2 c,
  EXP Γ ⊢ e1 ->
  EXP (vl1 + Γ) ⊢ e2 ->
  EECTX Γh ⊢ c ∷ (vl2 + Γ) ->
  EECTX Γh ⊢ (CTry3 e1 vl1 e2 vl2 c) ∷ Γ

where
"'EECTX' Γh ⊢ C ∷ Γ" := (EECtxScope Γh Γ C)
.


Ltac solve_inversion :=
  match goal with
  | [ H : _ |- _ ] => solve [inv H]
  end.

(* Basics.v *)
Lemma PBoth_left :
  forall {A : Set} (l : list (A * A)) (P : A -> Prop), Forall (PBoth P) l -> Forall P (map fst l).
Proof.
  intros. induction H; simpl; constructor.
  now inv H.
  auto.
Qed.

(* Basics.v *)
Lemma PBoth_right :
  forall {A : Set} (l : list (A * A)) (P : A -> Prop), Forall (PBoth P) l -> Forall P (map snd l).
Proof.
  intros. induction H; simpl; constructor.
  now inv H.
  auto.
Qed.

Lemma plug_preserves_scope_exp : forall {Γh C Γ e},
    (EECTX Γh ⊢ C ∷ Γ ->
     EXP Γh ⊢ e ->
     EXP Γ ⊢ plug C e).
Proof.
  induction C; intros; inv H; subst; simpl; try (now (do 2 constructor; auto)); auto.
  * do 2 constructor. apply indexed_to_forall.
    apply Forall_app; split; auto.
  * do 2 constructor. apply indexed_to_forall.
    apply Forall_app; split; auto.
  * do 2 constructor.
    - apply PBoth_left in H6, H7.
      intros. apply indexed_to_forall. 2: auto.
      rewrite map_app. apply Forall_app; split; auto.
      constructor; auto. simpl. now apply IHC.
      now rewrite map_length.
    - apply PBoth_right in H6, H7.
      intros. apply indexed_to_forall. 2: auto.
      rewrite map_app. apply Forall_app; split; auto.
      constructor; auto. now rewrite map_length.
  * do 2 constructor.
    - apply PBoth_left in H6, H7.
      intros. apply indexed_to_forall. 2: auto.
      rewrite map_app. apply Forall_app; split; auto.
      constructor; auto. now rewrite map_length.
    - apply PBoth_right in H6, H7.
      intros. apply indexed_to_forall. 2: auto.
      rewrite map_app. apply Forall_app; split; auto.
      constructor; auto. simpl. now apply IHC. now rewrite map_length.
  * do 2 constructor. apply indexed_to_forall.
    apply Forall_app; split; auto.
  * do 2 constructor. apply indexed_to_forall.
    apply Forall_app; split; auto.
  * do 2 constructor. now apply IHC.
    now apply indexed_to_forall.
  * do 2 constructor; auto. apply indexed_to_forall.
    apply Forall_app; split; auto.
  * do 2 constructor.
    - now apply IHC.
    - rewrite indexed_to_forall with (def := ([], `VNil, `VNil)) in H5.
      intros. rewrite map_nth with (d := ([], `VNil, `VNil)).
      extract_map_fun F. replace [] with (F ([], `VNil, `VNil)) at 1 by now subst F.
      rewrite map_nth. subst F. apply H5 in H. destruct nth, p. cbn. apply H.
    - rewrite indexed_to_forall with (def := ([], `VNil, `VNil)) in H5.
      intros. rewrite map_nth with (d := ([], `VNil, `VNil)).
      extract_map_fun F. replace [] with (F ([], `VNil, `VNil)) at 1 by now subst F.
      rewrite map_nth. subst F. apply H5 in H. destruct nth, p. cbn. apply H.
  * do 2 constructor; auto; rewrite indexed_to_forall with (def := ([], `VNil, `VNil)) in H11, H10.
    all: intros; rewrite map_nth with (d := ([], `VNil, `VNil));
    extract_map_fun F; replace [] with (F ([], `VNil, `VNil)) at 1 by now subst F.
    rewrite map_nth. 2: rewrite map_nth. (* this does not wotk in `all:` somewhy... *)
    all: subst F.
    all: apply nth_possibilities_alt with (def := ([], `VNil, `VNil)) in H; intuition.
    - apply H10 in H2. destruct nth, p, nth, p. inv H. cbn. apply H2.
    - simpl in H1. rewrite app_nth2; auto. remember (i - length l) as i'.
      destruct i'; cbn. now apply IHC.
      specialize (H11 i' ltac:(lia)). destruct nth, p. apply H11.
    - rewrite app_nth1; auto. specialize (H10 i ltac:(lia)). destruct nth, p. apply H10.
    - simpl in H1. rewrite app_nth2; auto. remember (i - length l) as i'.
      destruct i'; cbn. auto. 
      specialize (H11 i' ltac:(lia)). destruct nth, p. apply H11.
  * do 2 constructor; auto; rewrite indexed_to_forall with (def := ([], `VNil, `VNil)) in H11, H10.
    all: intros; rewrite map_nth with (d := ([], `VNil, `VNil));
    extract_map_fun F; replace [] with (F ([], `VNil, `VNil)) at 1 by now subst F.
    rewrite map_nth. 2: rewrite map_nth. (* this does not wotk in `all:` somewhy... *)
    all: subst F.
    all: apply nth_possibilities_alt with (def := ([], `VNil, `VNil)) in H; intuition.
    - apply H10 in H2. destruct nth, p, nth, p. inv H. cbn. apply H2.
    - simpl in H1. rewrite app_nth2; auto. remember (i - length l) as i'.
      destruct i'; cbn. auto.
      specialize (H11 i' ltac:(lia)). destruct nth, p. apply H11.
    - rewrite app_nth1; auto. specialize (H10 i ltac:(lia)). destruct nth, p. apply H10.
    - simpl in H1. rewrite app_nth2; auto. remember (i - length l) as i'.
      destruct i'; cbn. now apply IHC.
      specialize (H11 i' ltac:(lia)). destruct nth, p. apply H11.
  * do 2 constructor; auto; rewrite indexed_to_forall with (def := (0, `VNil)) in H6, H9.
    2: rewrite app_length; simpl; assumption.
    intros. do 2 rewrite map_nth with (d := (0, `VNil)).
    apply nth_possibilities_alt with (def := (0, `VNil)) in H; intuition.
    - rewrite app_nth1; auto. apply H6 in H2. rewrite app_length. simpl.
      now destruct (nth i l (0, `VNil)).
    - simpl in H1. rewrite app_nth2; auto. remember (i - length l) as i'.
      destruct i'; cbn. rewrite app_length. now apply IHC.
      specialize (H9 i' ltac:(lia)). rewrite app_length. destruct nth. apply H9.
  * do 2 constructor. 2: now apply IHC.
    intros. rewrite indexed_to_forall with (def := (0, `VNil)) in H4. apply H4 in H.
    do 2 rewrite map_nth with (d := (0, `VNil)). now destruct nth.
Qed.

Lemma plugc_preserves_scope_exp : forall {Γh Couter Γ Cinner Γ'},
    (EECTX Γ' ⊢ Couter ∷ Γ ->
     EECTX Γh ⊢ Cinner ∷ Γ' ->
     EECTX Γh ⊢ plugc Couter Cinner ∷ Γ).
Proof.
  induction Couter;
    intros;
    inversion H; subst;
    cbn;
    try solve_inversion;
    auto;
    constructor;
    firstorder idtac.
Qed.


(* In CTX, we only care about syntax, thus only expressions can be considered as
   equivalent. However, in CIU/LogRel, we have the possibility to do that for exceptions
   too. This also can be expressed with CTX by ECall "erlang" "error" [reason;details] *)
Definition CTX (Γ : nat) (e1 e2 : Exp) :=
  (EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2) /\
  (forall (C : Ctx),
      EECTX Γ ⊢ C ∷ 0 -> | [], RExp (plug C e1) | ↓ -> | [], RExp (plug C e2) | ↓).

Lemma IsReflexiveList : forall R' l Γ',
  IsReflexive R' -> Forall (fun r => RED Γ' ⊢ r) l ->
  Forall (fun '(e0, e3) => R' Γ' e0 e3) (combine l l).
Proof.
  induction l; intros; constructor.
  * apply H. inversion H0. auto.
  * inversion H0. apply IHl; auto.
Qed.

Lemma CTX_bigger : forall R' : nat -> Redex -> Redex -> Prop,
    IsPreCtxRel R' -> forall (Γ : nat) (e1 e2 : Exp), R' Γ e1 e2 -> CTX Γ e1 e2.
Proof.
  intros R' HR.
  destruct HR as [Rscope [Radequate [Rrefl [Rtrans [RFun [RApp [RLet [RLetRec  [ RCase [ RCons [RBIF RReceive ] ] ] ] ] ] ] ] ] ] ].
  unfold CTX.
  intros.
  destruct (Rscope _ _ _ H) as [Hscope_e1 Hscope_e2].
  intuition idtac. eapply Radequate; eauto.
  assert (forall Γ', EECTX Γ ⊢ C ∷ Γ' -> 
                     R' Γ' (plug C e1) (plug C e2)).
  { clear H0 H1.
    induction C;
      intros;
      inversion H0;
      subst;
      cbn;
      try solve_inversion;
      auto.
    - apply RFun. reflexivity.
      apply IHC; auto.
      now inversion H1.
    - apply RApp; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. inversion H0. subst. auto. inversion H1.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. inversion H0. subst. auto. inversion H1.
      + apply forall_biforall_refl.
        apply Forall_forall. rewrite Forall_forall in H5. intros. apply Rrefl. auto.
    - apply RApp; auto.
      + rewrite indexed_to_forall. intros.
        epose (nth_possibilities _ _ _ _ H1). destruct o.
        * destruct H2. rewrite H2 in *. rewrite indexed_to_forall in H7. apply H7. auto.
        * destruct H2. rewrite H2 in *. rewrite indexed_to_forall in H8.
          remember (i - length l1) as i'. destruct i'.
          -- simpl. eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
             simpl in H0. inversion H0. subst. 2: inversion H4.
             epose (H11 (length l1) _). rewrite nth_middle in e. auto.
             Unshelve. 1-2: exact (ELit 0%Z). rewrite app_length. lia.
          -- simpl. apply H8. simpl in H3. lia.
      + rewrite indexed_to_forall. intros.
        epose (nth_possibilities _ _ _ _ H1). destruct o.
        * destruct H2. rewrite H2 in *. rewrite indexed_to_forall in H7. apply H7. auto.
        * destruct H2. rewrite H2 in *. rewrite indexed_to_forall in H8.
          remember (i - length l1) as i'. destruct i'.
          -- simpl. eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
             simpl in H0. inversion H0. subst. 2: inversion H4.
             epose (H11 (length l1) _). rewrite nth_middle in e. auto.
             Unshelve. 1-2: exact (ELit 0%Z). rewrite app_length. lia.
          -- simpl. apply H8. simpl in H3. lia.
      + apply biforall_app. 2: constructor.
        ** apply forall_biforall_refl, Forall_forall. rewrite Forall_forall in H7. auto.
        ** simpl. apply IHC. auto.
        ** apply forall_biforall_refl, Forall_forall. rewrite Forall_forall in H8. auto.
    - apply RLet; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
    - apply RLet; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
    - apply RLetRec; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
    - apply RLetRec; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
    - apply RCase; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
    - apply RCase; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
    - apply RCase; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
    - apply RCons; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
    - apply RCons; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. inversion H0. auto. inversion H1.
    - apply RBIF; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
        simpl in H0. inversion H0. subst. auto. inversion H1.
      + eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
        simpl in H0. inversion H0. subst. auto. inversion H1.
      + apply forall_biforall_refl.
        apply Forall_forall. rewrite Forall_forall in H5. intros. apply Rrefl. auto.
    - apply RBIF; auto.
      + rewrite indexed_to_forall. intros.
        epose (nth_possibilities _ _ _ _ H1). destruct o.
        * destruct H2. rewrite H2 in *. rewrite indexed_to_forall in H7. apply H7. auto.
        * destruct H2. rewrite H2 in *. rewrite indexed_to_forall in H8.
          remember (i - length l1) as i'. destruct i'.
          -- simpl. eapply @plug_preserves_scope_exp with (e := e1) in H0; eauto 2.
             simpl in H0. inversion H0. subst. 2: inversion H4.
             epose (H11 (length l1) _). rewrite nth_middle in e. auto.
             Unshelve. 1-2: exact (ELit 0%Z). rewrite app_length. lia.
          -- simpl. apply H8. simpl in H3. lia.
      + rewrite indexed_to_forall. intros.
        epose (nth_possibilities _ _ _ _ H1). destruct o.
        * destruct H2. rewrite H2 in *. rewrite indexed_to_forall in H7. apply H7. auto.
        * destruct H2. rewrite H2 in *. rewrite indexed_to_forall in H8.
          remember (i - length l1) as i'. destruct i'.
          -- simpl. eapply @plug_preserves_scope_exp with (e := e2) in H0; eauto 2.
             simpl in H0. inversion H0. subst. 2: inversion H4.
             epose (H11 (length l1) _). rewrite nth_middle in e. auto.
             Unshelve. 1-2: exact (ELit 0%Z). rewrite app_length. lia.
          -- simpl. apply H8. simpl in H3. lia.
      + apply biforall_app. 2: constructor.
        ** apply forall_biforall_refl, Forall_forall. rewrite Forall_forall in H7. auto.
        ** simpl. apply IHC. auto.
        ** apply forall_biforall_refl, Forall_forall. rewrite Forall_forall in H8. auto.
    - apply RReceive; auto.
      + apply Forall_app; split. 2: constructor.
        1,3: rewrite (indexed_to_forall _ _ (PNil, ELit 0%Z)); intros.
        * apply H7 in H1.
          replace (ELit 0%Z) with (snd (PNil, ELit 0%Z)) in H1 by auto.
          replace 0 with ((fst >>> pat_vars) (PNil, ELit 0%Z)) in H1 by auto.
          do 2 rewrite map_nth in H1. break_match_goal. exact H1.
        * apply H8 in H1.
          replace (ELit 0%Z) with (snd (PNil, ELit 0%Z)) in H1 by auto.
          replace 0 with ((fst >>> pat_vars) (PNil, ELit 0%Z)) in H1 by auto.
          do 2 rewrite map_nth in H1. break_match_goal. exact H1.
        * eapply @plug_preserves_scope_exp with (e := e1) in H5; eauto 2.
      + apply Forall_app; split. 2: constructor.
        1,3: rewrite (indexed_to_forall _ _ (PNil, ELit 0%Z)); intros.
        * apply H7 in H1.
          replace (ELit 0%Z) with (snd (PNil, ELit 0%Z)) in H1 by auto.
          replace 0 with ((fst >>> pat_vars) (PNil, ELit 0%Z)) in H1 by auto.
          do 2 rewrite map_nth in H1. break_match_goal. exact H1.
        * apply H8 in H1.
          replace (ELit 0%Z) with (snd (PNil, ELit 0%Z)) in H1 by auto.
          replace 0 with ((fst >>> pat_vars) (PNil, ELit 0%Z)) in H1 by auto.
          do 2 rewrite map_nth in H1. break_match_goal. exact H1.
        * eapply @plug_preserves_scope_exp with (e := e2) in H5; eauto 2.
      + apply biforall_app. 2: constructor.
        * clear H0. (* biforall_refl not sufficient, bc preconditions *)
          induction l1; constructor; auto. 2: apply IHl1; auto.
          destruct a. split; auto. apply Rrefl. apply (H7 0). simpl. lia.
          intros. apply (H7 (S i)). simpl. lia.
        * split; auto.
        * clear H0. induction l2; constructor; auto. 2: apply IHl2; auto.
          destruct a. split; auto. apply Rrefl. apply (H8 0). simpl. lia.
          intros. apply (H8 (S i)). simpl. lia.
  }
  now apply H2.
Qed.

Theorem CTX_refl Γ e : EXP Γ ⊢ e -> CTX Γ e e.
Proof.
  unfold CTX. intros. split; auto.
Qed.



