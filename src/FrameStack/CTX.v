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
  forall Γ el el',
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
  forall Γ el el',
    Forall (fun e => EXP Γ ⊢ e) el ->
    Forall (fun e => EXP Γ ⊢ e) el' ->
    list_biforall (R Γ) el el' ->
    R Γ (ETuple el) (ETuple el').

Definition CompatibleMap (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ l l',
    Forall (PBoth (fun e => EXP Γ ⊢ e)) l ->
    Forall (PBoth (fun e => EXP Γ ⊢ e)) l' ->
    list_biforall (fun '(v1, v2) '(v1', v2') => R Γ v1 v1' /\ R Γ v2 v2') l l' ->
    R Γ (EMap l) (EMap l').

Definition CompatibleCall (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ m m' f f' el el',
  EXP Γ ⊢ m -> EXP Γ ⊢ m' ->
  EXP Γ ⊢ f -> EXP Γ ⊢ f' ->
  R Γ m m' -> R Γ f f' ->
  Forall (fun e => EXP Γ ⊢ e) el ->
  Forall (fun e => EXP Γ ⊢ e) el' ->
  list_biforall (R Γ) el el' ->
    R Γ (ECall m f el) (ECall m' f' el').

Definition CompatiblePrimOp (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ f f' el el', f = f' ->
    Forall (fun e => EXP Γ ⊢ e) el ->
    Forall (fun e => EXP Γ ⊢ e) el' ->
    list_biforall (R Γ) el el' ->
    R Γ (EPrimOp f el) (EPrimOp f' el').

Definition CompatibleApp (R : nat -> Exp -> Exp -> Prop) :=
  forall Γ e e' el el',
    EXP Γ ⊢ e ->
    EXP Γ ⊢ e' ->
    Forall (fun e => EXP Γ ⊢ e) el ->
    Forall (fun e => EXP Γ ⊢ e) el' ->
    R Γ e e' ->
    list_biforall (R Γ) el el' ->
    R Γ (EApp e el) (EApp e' el').

Definition CompatibleCase (R : nat -> Exp -> Exp -> Prop) := (* TODO: l or l' in places? *)
  forall Γ e e' l l',
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
  forall Γ e l e' l',
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
(*
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
*)
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
  CompatibleTry R.

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
    apply Erel_LetRec_compat; auto.
    now apply biforall_length in H3.
  * unfold CompatibleTry.
    intros.
    auto.
Qed.

Corollary CIU_IsPreCtxRel : IsPreCtxRel CIU_open.
Proof.
  unfold IsPreCtxRel.
  intuition.
  * apply CIU_open_scope_l in H. now destruct_scopes.
  * apply CIU_open_scope_r in H. now destruct_scopes.
  * intros ?; intros.
    eapply Erel_IsPreCtxRel; eauto.
    apply CIU_iff_Rrel in H; now apply Rrel_exp_compat_reverse in H.
  * intros ?; intros.
    apply CIU_iff_Rrel. apply Rrel_exp_compat. now apply Erel_IsPreCtxRel.
  * intros ?; intros.
    apply CIU_iff_Rrel. apply Rrel_exp_compat.
    apply CIU_iff_Rrel, Rrel_exp_compat_reverse in H, H0.
    assert (Transitive (Erel_open Γ)) by apply Erel_IsPreCtxRel.
    eapply H1; eauto.
  * intros ?; intros.
    apply CIU_iff_Rrel. apply Rrel_exp_compat.
    apply CIU_iff_Rrel, Rrel_exp_compat_reverse in H2. now apply Erel_IsPreCtxRel.
  * intros ?; intros.
    apply CIU_iff_Rrel. apply Rrel_exp_compat.
    eapply biforall_impl in H1. 2: { intros; apply CIU_iff_Rrel, Rrel_exp_compat_reverse in H2. exact H2. }
    now apply Erel_IsPreCtxRel.
  * intros ?; intros.
    apply CIU_iff_Rrel. apply Rrel_exp_compat.
    apply CIU_iff_Rrel, Rrel_exp_compat_reverse in H3, H4. now apply Erel_IsPreCtxRel.
  * intros ?; intros.
    apply CIU_iff_Rrel. apply Rrel_exp_compat.
    eapply biforall_impl in H1. 2: { intros; apply CIU_iff_Rrel, Rrel_exp_compat_reverse in H2. exact H2. }
    now apply Erel_IsPreCtxRel.
  * intros ?; intros.
    apply CIU_iff_Rrel. apply Rrel_exp_compat.
    apply biforall_impl with (Q := fun '(v1, v2) '(v1', v2') => Erel_open Γ v1 v1' /\ Erel_open Γ v2 v2') in H1. 2: { intros. destruct x, y, H2.
    apply CIU_iff_Rrel, Rrel_exp_compat_reverse in H2, H3.
    pose proof (conj H2 H3). exact H4. }
    now apply Erel_IsPreCtxRel.
  * intros ?; intros.
    apply CIU_iff_Rrel, Rrel_exp_compat_reverse in H3, H4.
    apply CIU_iff_Rrel. apply Rrel_exp_compat.
    eapply biforall_impl in H7. 2: { intros. apply CIU_iff_Rrel, Rrel_exp_compat_reverse in H8. exact H8. }
    now apply Erel_IsPreCtxRel.
  * intros ?; intros.
    apply CIU_iff_Rrel. apply Rrel_exp_compat.
    eapply biforall_impl in H2. 2: { intros; apply CIU_iff_Rrel, Rrel_exp_compat_reverse in H3. exact H3. }
    now apply Erel_IsPreCtxRel.
  * intros ?; intros.
    apply CIU_iff_Rrel. apply Rrel_exp_compat.
    apply CIU_iff_Rrel, Rrel_exp_compat_reverse in H3.
    eapply biforall_impl in H4. 2: { intros; apply CIU_iff_Rrel, Rrel_exp_compat_reverse in H5. exact H5. }
    now apply Erel_IsPreCtxRel.
  * intros ?; intros.
    apply CIU_iff_Rrel. apply Rrel_exp_compat.
    apply CIU_iff_Rrel, Rrel_exp_compat_reverse in H3.
    apply biforall_impl with (Q := fun '(p, g, e) '(p', g', e') =>
        p = p' /\ Erel_open (PatListScope p + Γ) g g' /\ Erel_open (PatListScope p + Γ) e e') in H4. 2: { intros. destruct x, p, y, p, H5, H6.
    apply CIU_iff_Rrel, Rrel_exp_compat_reverse in H6, H7.
    intuition. }
    now apply Erel_IsPreCtxRel.
  * intros ?; intros.
    apply CIU_iff_Rrel. apply Rrel_exp_compat.
    apply CIU_iff_Rrel, Rrel_exp_compat_reverse in H5, H4. now apply Erel_IsPreCtxRel.
  * intros ?; intros.
    apply CIU_iff_Rrel. apply Rrel_exp_compat.
    apply CIU_iff_Rrel, Rrel_exp_compat_reverse in H3, H4. now apply Erel_IsPreCtxRel.
  * intros ?; intros.
    apply CIU_iff_Rrel. apply Rrel_exp_compat.
    apply CIU_iff_Rrel, Rrel_exp_compat_reverse in H4.
    apply biforall_impl with (Q := fun '(v, e) '(v', e') => v = v' /\ Erel_open (Datatypes.length l + v + Γ) e e') in H3. 2: { intros. destruct x, y, H5.
    apply CIU_iff_Rrel, Rrel_exp_compat_reverse in H6. intuition. }
    now apply Erel_IsPreCtxRel.
  * intros ?; intros.
    apply CIU_iff_Rrel. apply Rrel_exp_compat.
    apply CIU_iff_Rrel, Rrel_exp_compat_reverse in H7, H8, H9.
    now apply Erel_IsPreCtxRel.
Qed.

Inductive CtxIdent :=
| CValues
| CTuple
| CMap
| CCall (e1 e2 : Exp)
| CPrimOp (f : string)
| CApp (e : Exp).

Inductive Ctx :=
| CHole
| CFun     (vl : nat) (c : Ctx)
| CParams  (ident : CtxIdent) (el : list Exp) (c : Ctx) (el' : list Exp)
| CCons1   (c : Ctx) (tl : Exp)
| CCons2   (hd : Exp) (c : Ctx)
| CCallMod (c : Ctx) (f : Exp) (l : list Exp)
| CCallFun (m : Exp) (c : Ctx) (l : list Exp)
| CApp1    (c : Ctx) (l : list Exp)
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

Definition create_exp (ident : CtxIdent) (l : list Exp) :=
match ident with
 | CValues => EValues l
 | CTuple => ETuple l
 | CMap => EMap (deflatten_list l)
 | CCall e1 e2 => ECall e1 e2 l
 | CPrimOp f => EPrimOp f l
 | CApp e => EApp e l
end.


Fixpoint plug (C : Ctx) (p : Exp) :=
match C with
| CHole              => p
| CFun    vl c       => EExp ( EFun vl (plug c p) )
| CCons1  c tl       => EExp ( ECons (plug c p) tl )
| CCons2  hd c       => EExp ( ECons hd (plug c p) )
| CParams ident l c l'
                     => EExp ( create_exp ident (l ++ [(plug c p)] ++ l') )
| CCallMod c f l     => EExp ( ECall (plug c p) f l )
| CCallFun m c l     => EExp ( ECall m (plug c p) l )
| CApp1   c l        => EExp ( EApp (plug c p) l )
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
| CCons1  c tl      => CCons1 (plugc c p) tl
| CCons2  hd c      => CCons2 hd (plugc c p)
| CParams ident l c l' => CParams ident l (plugc c p) l'
| CCallMod c f l    => CCallMod (plugc c p) f l
| CCallFun m c l    => CCallFun m (plugc c p) l
| CApp1   c l       => CApp1 (plugc c p) l
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
    try rewrite IHC1;
    auto.
Qed.

Reserved Notation "'EECTX' Γh ⊢ C ∷ Γ" (at level 60).
Reserved Notation "'EECTXID' Γh ⊢ C ∷ Γ" (at level 60).
(* Reserved Notation "'VECTX' Γh ⊢ C ∷ Γ" (at level 60). *)

Inductive EECtxIdentScope (Γh : nat) : CtxIdent -> nat -> Prop :=

| CEScope_CValues Γ : EECTXID Γh ⊢ CValues ∷ Γ

| CEScope_CTuple Γ : EECTXID Γh ⊢ CTuple ∷ Γ

| CEScope_CMap Γ : EECTXID Γh ⊢ CMap ∷ Γ

| CEScope_CPrimOp Γ f : EECTXID Γh ⊢ CPrimOp f ∷ Γ

| CEScope_CCall Γ m f : EXP Γ ⊢ m -> EXP Γ ⊢ f ->
                        EECTXID Γh ⊢ CCall m f ∷ Γ

| CEScope_CApp Γ e : EXP Γ ⊢ e -> EECTXID Γh ⊢ CApp e ∷ Γ

where "'EECTXID' Γh ⊢ C ∷ Γ" := (EECtxIdentScope Γh C Γ).

Inductive EECtxScope (Γh : nat) : nat -> Ctx -> Prop :=

| CEScope_Hole : (EECTX Γh ⊢ CHole ∷ Γh)

| CEScope_CFun : forall Γ vl c,
  EECTX Γh ⊢ c ∷ (vl + Γ) -> 
  EECTX Γh ⊢ (CFun vl c) ∷ Γ

| CEScope_CCons1 : forall Γ c tl,
  EECTX Γh ⊢ c ∷ Γ ->
  EXP Γ ⊢ tl ->
  EECTX Γh ⊢ (CCons1 c tl) ∷ Γ

| CEScope_CCons2 : forall Γ hd c,
  EXP Γ ⊢ hd ->
  EECTX Γh ⊢ c ∷ Γ ->
  EECTX Γh ⊢ (CCons2 hd c) ∷ Γ

| CEScope_CParams : forall Γ ident l c l',
  (ident = CMap -> exists n, length l + length l' = 1 + 2 * n) ->
  Forall (fun e => EXP Γ ⊢ e) l ->
  EECTX Γh ⊢ c ∷ Γ ->
  Forall (fun e => EXP Γ ⊢ e) l' ->
  EECTXID Γh ⊢ ident ∷ Γ ->
  EECTX Γh ⊢ (CParams ident l c l') ∷ Γ

| CEScope_CCallMod : forall Γ c f l,
  EECTX Γh ⊢ c ∷ Γ ->
  EXP Γ ⊢ f ->
  Forall (fun e => EXP Γ ⊢ e) l ->
  EECTX Γh ⊢ CCallMod c f l ∷ Γ

| CEScope_CCallFun : forall Γ m c l,
  EXP Γ ⊢ m ->
  EECTX Γh ⊢ c ∷ Γ ->
  Forall (fun e => EXP Γ ⊢ e) l ->
  EECTX Γh ⊢ CCallFun m c l ∷ Γ

| CEScope_CApp1 : forall Γ c l,
  EECTX Γh ⊢ c ∷ Γ ->
  Forall (fun e => EXP Γ ⊢ e) l ->
  EECTX Γh ⊢ (CApp1 c l) ∷ Γ

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

Lemma plug_preserves_scope_exp : forall {Γh C Γ e},
    (EECTX Γh ⊢ C ∷ Γ ->
     EXP Γh ⊢ e ->
     EXP Γ ⊢ plug C e).
Proof.
  induction C; intros; inv H; subst; simpl; try (now (do 2 constructor; auto)); auto.
  * destruct ident; inv H10; do 2 constructor; try (apply indexed_to_forall;
    apply Forall_app; split; auto); auto.
    all: erewrite <- map_length; apply indexed_to_forall; apply List.Forall_map.
    all: apply Forall_impl with (P := fun '(x, y) => EXP Γ ⊢ x /\ EXP Γ ⊢ y); [destruct a; intro G; now destruct G|].
    all: apply deflatten_keeps_prop_match.
    all: apply Forall_app; split; auto.
  * do 2 constructor. apply indexed_to_forall. all: auto.
  * do 2 constructor. apply indexed_to_forall. all: auto.
  * do 2 constructor. 2: apply indexed_to_forall. all: auto.
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
    inv H;
    try solve_inversion;
    auto;
    constructor;
    firstorder idtac.
  inv H10; now constructor.
Qed.


(* In CTX, we only care about syntax, thus only expressions can be considered as
   equivalent. However, in CIU/LogRel, we have the possibility to do that for exceptions
   too. This also can be expressed with CTX by ECall "erlang" "error" [reason;details] *)
Definition CTX (Γ : nat) (e1 e2 : Exp) :=
  (EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2) /\
  (forall (C : Ctx),
      EECTX Γ ⊢ C ∷ 0 -> | [], RExp (plug C e1) | ↓ -> | [], RExp (plug C e2) | ↓).

Lemma IsReflexiveList : forall R' l Γ',
  IsReflexive R' -> Forall (fun r => EXP Γ' ⊢ r) l ->
  Forall (fun '(e0, e3) => R' Γ' e0 e3) (combine l l).
Proof.
  induction l; intros; constructor.
  * apply H. inversion H0. auto.
  * inversion H0. apply IHl; auto.
Qed.

Lemma biforall_IsReflexive :
  forall (R : nat -> Exp -> Exp -> Prop), IsReflexive R ->
  forall l Γ, Forall (fun e : Exp => EXP Γ ⊢ e) l -> list_biforall (R Γ) l l.
Proof.
  induction l; constructor; auto.
  inv H0. now apply H. inv H0. now apply IHl.
Qed.

Lemma CTX_bigger : forall R' : nat -> Exp -> Exp -> Prop,
    IsPreCtxRel R' -> forall (Γ : nat) (e1 e2 : Exp), R' Γ e1 e2 -> CTX Γ e1 e2.
Proof.
  intros R' HR.
  destruct HR as [Rscope [Radequate [Rrefl [Rtrans [RFun [ RValues [RCons [RTuple [RMap  [ RCall [ RPrimOp [RApp [RCase [RLet [RSeq [RLetRec RTry ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ].
  unfold CTX.
  intros.
  destruct (Rscope _ _ _ H) as [Hscope_e1 Hscope_e2].
  intuition idtac. eapply Radequate; eauto.
  assert (forall Γ', EECTX Γ ⊢ C ∷ Γ' -> 
                     R' Γ' (plug C e1) (plug C e2)).
  { clear H0 H1.
    induction C;
      intros;
      inv H0;
      cbn;
      try solve_inversion;
      auto.
    - apply RFun. reflexivity.
      1-2: eapply plug_preserves_scope_exp; eauto.
      apply IHC; auto.
    - inv H10; [apply RValues | apply RTuple | apply RMap | apply RPrimOp | apply RCall | apply RApp ]; auto.
      all: try (try apply deflatten_keeps_prop; apply Forall_app; split; auto; constructor; auto).
      all: try (eapply plug_preserves_scope_exp; eauto).
      3: apply deflatten_keeps_biprop_match.
      all: apply biforall_app; [now apply biforall_IsReflexive | constructor; [|now apply biforall_IsReflexive]].
      all: now apply IHC.
    - apply RCons; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H4; eauto 2.
      + eapply @plug_preserves_scope_exp with (e := e2) in H4; eauto 2.
    - apply RCons; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H5; eauto 2.
      + eapply @plug_preserves_scope_exp with (e := e2) in H5; eauto 2.
    - apply RCall; auto.
      1-2: eapply plug_preserves_scope_exp; eauto.
      apply forall_biforall_refl, Forall_forall. intros.
      rewrite Forall_forall in H7. now apply Rrefl, H7.
    - apply RCall; auto.
      1-2: eapply plug_preserves_scope_exp; eauto.
      apply forall_biforall_refl, Forall_forall. intros.
      rewrite Forall_forall in H7. now apply Rrefl, H7.
    - apply RApp; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H4; eauto 2.
      + eapply @plug_preserves_scope_exp with (e := e2) in H4; eauto 2.
      + apply forall_biforall_refl.
        apply Forall_forall. rewrite Forall_forall in H5. intros. apply Rrefl. auto.
    - apply RCase; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H4; eauto 2.
      + eapply @plug_preserves_scope_exp with (e := e2) in H4; eauto 2.
      + apply forall_biforall_refl.
        apply Forall_forall. rewrite Forall_forall in H5. intros.
        destruct x, p. split. 2: split. reflexivity.
        all: apply Rrefl; now apply H5 in H0.
    - apply RCase; auto.
      1-2: apply Forall_app; split; auto; constructor; auto.
      1-2: simpl; split; try eapply plug_preserves_scope_exp; eauto.
      apply biforall_app. 2: constructor.
      + apply forall_biforall_refl, Forall_forall. intros.
        rewrite Forall_forall in H10. destruct x, p. split. 2: split.
        reflexivity.
        all: apply Rrefl; now apply H10 in H0.
      + split; auto.
      + apply forall_biforall_refl, Forall_forall. intros.
        rewrite Forall_forall in H11. destruct x, p. split. 2: split.
        reflexivity.
        all: apply Rrefl; now apply H11 in H0.
    - apply RCase; auto.
      1-2: apply Forall_app; split; auto; constructor; auto.
      1-2: simpl; split; try eapply plug_preserves_scope_exp; eauto.
      apply biforall_app. 2: constructor.
      + apply forall_biforall_refl, Forall_forall. intros.
        rewrite Forall_forall in H10. destruct x, p. split. 2: split.
        reflexivity.
        all: apply Rrefl; now apply H10 in H0.
      + split; auto.
      + apply forall_biforall_refl, Forall_forall. intros.
        rewrite Forall_forall in H11. destruct x, p. split. 2: split.
        reflexivity.
        all: apply Rrefl; now apply H11 in H0.
    - apply RLet; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H4; eauto 2.
      + eapply @plug_preserves_scope_exp with (e := e2) in H4; eauto 2.
    - apply RLet; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H6; eauto 2.
      + eapply @plug_preserves_scope_exp with (e := e2) in H6; eauto 2.
    - apply RSeq; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H4; eauto 2.
      + eapply @plug_preserves_scope_exp with (e := e2) in H4; eauto 2.
    - apply RSeq; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H5; eauto 2.
      + eapply @plug_preserves_scope_exp with (e := e2) in H5; eauto 2.
    - apply RLetRec; auto.
      + rewrite app_length. eauto.
      + rewrite app_length. eauto.
      + apply Forall_app. split. rewrite app_length. exact H6.
        constructor. eapply plug_preserves_scope_exp. rewrite app_length.
        exact H8. auto.
        rewrite app_length. exact H9.
      + apply Forall_app. split. rewrite app_length. exact H6.
        constructor. eapply plug_preserves_scope_exp. rewrite app_length.
        exact H8. auto.
        rewrite app_length. exact H9.
      + rewrite app_length in *. apply biforall_app. 2: constructor.
        ** apply forall_biforall_refl, Forall_forall. intros.
           rewrite Forall_forall in H6. destruct x. split. reflexivity.
           apply Rrefl; now apply H6 in H0.
        ** split; auto.
        ** apply forall_biforall_refl, Forall_forall. intros.
           rewrite Forall_forall in H9. destruct x. split. reflexivity.
           apply Rrefl; now apply H9 in H0.
      + apply Rrefl. rewrite app_length; auto.
    - apply RLetRec; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H5; eauto 2.
      + eapply @plug_preserves_scope_exp with (e := e2) in H5; eauto 2.
      + apply forall_biforall_refl, Forall_forall. intros.
        rewrite Forall_forall in H4. destruct x. split. reflexivity.
        apply Rrefl; now apply H4 in H0.
    - apply RTry; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H5; eauto 2.
      + eapply @plug_preserves_scope_exp with (e := e2) in H5; eauto 2.
    - apply RTry; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H8; eauto 2.
      + eapply @plug_preserves_scope_exp with (e := e2) in H8; eauto 2.
    - apply RTry; auto.
      + eapply @plug_preserves_scope_exp with (e := e1) in H9; eauto 2.
      + eapply @plug_preserves_scope_exp with (e := e2) in H9; eauto 2.
  }
  now apply H2.
Qed.

Corollary CIU_implies_CTX :
  forall Γ (e1 e2 : Exp), CIU_open Γ e1 e2 -> CTX Γ e1 e2.
Proof.
  intros. eapply CTX_bigger. apply CIU_IsPreCtxRel. assumption.
Qed.


Theorem CTX_refl Γ e : EXP Γ ⊢ e -> CTX Γ e e.
Proof.
  unfold CTX. intros. split; auto.
Qed.

Theorem CTX_isPreCtxRel_CParams Γ tl tl' hd hds :
  EXP Γ ⊢ hd ->
  list_biforall
       (fun e1 e2 : Exp =>
        (EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2) /\
        (forall C : Ctx,
         EECTX Γ ⊢ C ∷ 0 -> | [], plug C e1 | ↓ -> | [], plug C e2 | ↓)) tl tl' ->
  Forall (ExpScoped Γ) hds ->
  forall C ident, EECTX Γ ⊢ C ∷ 0 ->
  (ident = CMap ->
   exists n : nat, Datatypes.length hds + Datatypes.length tl = 1 + 2 * n) ->
   EECTXID Γ ⊢ ident ∷ Γ ->
  | [], plug (plugc C (CParams ident hds CHole tl)) hd | ↓ ->
  | [], plug (plugc C (CParams ident hds CHole tl')) hd | ↓.
Proof.
  intros H IH. revert hds hd H. induction IH; intros.
  * (* base case is also inductive *)
    assumption.
  * replace (plug (plugc C (CParams ident hds CHole (hd :: tl))) hd0) with
            (plug (plugc C (CParams ident (hds ++ [hd0]) CHole tl)) hd) in H5.
    2: {
      do 2 rewrite <- plug_assoc. simpl. rewrite <- app_assoc. now simpl.
    }
    replace (plug (plugc C (CParams ident hds CHole (hd' :: tl'))) hd0) with
            (plug (plugc C (CParams ident (hds ++ [hd0]) CHole tl')) hd').
    2: {
      do 2 rewrite <- plug_assoc. simpl. rewrite <- app_assoc. now simpl.
    }
    destruct H as [[Hcl1 Hcl2] IHH].
    eapply IHIH. 6: { 
      apply IHH. 2: eassumption.
      eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      * intros P; apply H3 in P; destruct P; rewrite app_length.
        simpl. exists x. simpl in H. lia.
      * apply Forall_app; auto.
      * constructor.
      * clear -IH. induction IH; constructor; intuition; auto.
    } all: auto.
    2: { intros P; apply H3 in P; destruct P; rewrite app_length.
         simpl. exists x. simpl in H. lia.
       }
    apply Forall_app; auto.
Qed.

Lemma CTX_IsPreCtxRel : IsPreCtxRel CTX.
Proof.
  unfold IsPreCtxRel.
  intuition idtac;
    try solve
        [unfold CTX in H; intuition idtac
        |inversion H; [|constructor]; apply H0].
  * unfold Adequate.
    intros.
    unfold CTX in H.
    intuition idtac.
    - apply (H2 CHole); auto.
      constructor.
  * unfold IsReflexive.
    intros.
    unfold CTX.
    intuition (auto using Rbar_le_refl).
  * unfold Transitive.
    intros.
    unfold CTX in *.
    intuition idtac.
    auto.
  * unfold CompatibleFun.
    intros.
    unfold CTX in *.
    intuition auto.
    specialize (H4 (plugc C (CFun vl' CHole))).
    repeat rewrite <- plug_assoc in H4.
    cbn in H4.
    apply H4.
    eapply plugc_preserves_scope_exp; eauto.
    constructor. subst. constructor. now subst.
  * unfold CompatibleValues.
    intros. unfold CTX in *.
    intuition auto.
    1-2: do 2 constructor; rewrite <- indexed_to_forall; eassumption.
    inv H1.
    - assumption.
    - replace (plug C (° EValues (hd :: tl))) with
              (plug (plugc C (CParams CValues [] CHole tl)) hd) in H3
           by now rewrite <- plug_assoc.
      replace (plug C (° EValues (hd' :: tl'))) with
              (plug (plugc C (CParams CValues [] CHole tl')) hd')
           by now rewrite <- plug_assoc.
      destruct H4 as [[Hcl1 Hcl2] D].
      eapply CTX_isPreCtxRel_CParams in H3; eauto.
      2: congruence.
      2: constructor.
      apply D in H3. assumption.
      eapply plugc_preserves_scope_exp; eauto.
      constructor; auto. congruence. 1,3: constructor.
      now inv H0.
  * unfold CompatibleCons. intros. unfold CTX in *. intuition.
    replace (plug C (° ECons e1 e2)) with
            (plug (plugc C (CCons1 CHole e2)) e1) in H10 by now rewrite <- plug_assoc.
    apply H6 in H10.
    2: eapply plugc_preserves_scope_exp; eauto; constructor; auto; constructor.
    replace (plug (plugc C (CCons1 CHole e2)) e1') with
            (plug (plugc C (CCons2 e1' CHole)) e2) in H10.
    2: { repeat rewrite <- plug_assoc. now simpl. }
    apply H7 in H10. now rewrite <- plug_assoc in H10.
    eapply plugc_preserves_scope_exp; eauto; constructor; auto; constructor.
  * unfold CompatibleTuple.
    intros. unfold CTX in *.
    intuition auto.
    1-2: do 2 constructor; rewrite <- indexed_to_forall; eassumption.
    inv H1.
    - assumption.
    - replace (plug C (° ETuple (hd :: tl))) with
              (plug (plugc C (CParams CTuple [] CHole tl)) hd) in H3
           by now rewrite <- plug_assoc.
      replace (plug C (° ETuple (hd' :: tl'))) with
              (plug (plugc C (CParams CTuple [] CHole tl')) hd')
           by now rewrite <- plug_assoc.
      destruct H4 as [[Hcl1 Hcl2] D].
      eapply CTX_isPreCtxRel_CParams in H3; eauto.
      2: congruence.
      2: constructor.
      apply D in H3. assumption.
      eapply plugc_preserves_scope_exp; eauto.
      constructor; auto. congruence. 1,3: constructor.
      now inv H0.
  * unfold CompatibleMap.
    intros. unfold CTX in *.
    intuition auto.
    {
      apply PBoth_left in H as H'.
      apply PBoth_right in H. rewrite indexed_to_forall in H', H.
      rewrite map_length in H', H.
      do 2 constructor; intros; [apply H' in H2 | apply H in H2]; try eassumption.
    }
    {
      apply PBoth_left in H0 as H0'.
      apply PBoth_right in H0. rewrite indexed_to_forall in H0', H0.
      rewrite map_length in H0', H0.
      do 2 constructor; intros; [apply H0' in H2 | apply H0 in H2]; try eassumption.
    }
    inv H1.
    - assumption.
    - destruct hd, hd'. intuition.
      replace (plug C (° EMap ((e, e0) :: tl))) with
              (plug (plugc C (CParams CMap [] CHole (e0 :: flatten_list tl))) e) in H3.
      2: {
        rewrite <- plug_assoc. simpl. now rewrite flatten_deflatten.
      }
      replace (plug C (° EMap ((e1, e2) :: tl'))) with
              (plug (plugc C (CParams CMap [] CHole (e2 :: flatten_list tl'))) e1).
      2: {
        rewrite <- plug_assoc. simpl. now rewrite flatten_deflatten.
      }
      eapply CTX_isPreCtxRel_CParams with (tl' := e2 :: flatten_list tl') in H3; eauto.
      4: constructor.
      3: { intros. simpl. rewrite length_flatten_list. exists (length tl). lia. }
      2: {
        constructor; auto.
        Search list_biforall flatten_list. clear -H5.
        induction H5; auto.
        simpl. destruct hd, hd'. intuition.
      }
      apply H7 in H3. assumption.
      eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      1: { intros. simpl. rewrite length_flatten_list. exists (length tl'). lia. }
      1,3: constructor.
      constructor; auto. clear -H5. induction H5; simpl; intuition.
      destruct hd', hd. intuition.
  * unfold CompatibleCall.
    intros. unfold CTX in *.
    intuition auto.
    1-2: do 2 constructor; auto; rewrite <- indexed_to_forall; eassumption.
    replace (plug C (° ECall m f el)) with
            (plug (plugc C (CCallMod CHole f el)) m) in H13 by now rewrite <- plug_assoc.
    apply H9 in H13. 2: {
      eapply plugc_preserves_scope_exp; eauto.
      constructor; auto. constructor.
    }
    replace (plug (plugc C (CCallMod CHole f el)) m') with
            (plug (plugc C (CCallFun m' CHole el)) f) in H13
      by now do 2 rewrite <- plug_assoc.
    apply H10 in H13.
    2: {
      eapply plugc_preserves_scope_exp; eauto.
      constructor; auto. constructor.
    }
    inv H7.
    - rewrite <- plug_assoc in H13. assumption.
    - replace (plug (plugc C (CCallFun m' CHole (hd :: tl))) f') with
              (plug (plugc C (CParams (CCall m' f') [] CHole tl)) hd) in H13
           by now do 2 rewrite <- plug_assoc.
      destruct H14 as [[Hcl1 Hcl2] D].
      eapply CTX_isPreCtxRel_CParams in H13; eauto.
      2: congruence.
      2: constructor.
      2-3: auto.
      apply D in H13. rewrite <- plug_assoc in H13. assumption.
      eapply plugc_preserves_scope_exp; eauto.
      constructor; auto. congruence. 1,3: constructor.
      1-2: auto.
      now inv H6.
  * unfold CompatiblePrimOp.
    intros. unfold CTX in *.
    intuition auto.
    1-2: do 2 constructor; rewrite <- indexed_to_forall; eassumption.
    subst. inv H2.
    - assumption.
    - replace (plug C (° EPrimOp f' (hd :: tl))) with
              (plug (plugc C (CParams (CPrimOp f') [] CHole tl)) hd) in H4
           by now rewrite <- plug_assoc.
      destruct H as [[Hcl1 Hcl2] D].
      eapply CTX_isPreCtxRel_CParams in H4; eauto.
      2: congruence.
      2: constructor.
      apply D in H4. rewrite <- plug_assoc in H4. assumption.
      eapply plugc_preserves_scope_exp; eauto.
      constructor; auto. congruence. 1,3: constructor.
      now inv H1.
  * unfold CompatibleApp.
    intros. unfold CTX in *.
    intuition auto.
    1-2: do 2 constructor; auto; rewrite <- indexed_to_forall; eassumption.
    replace (plug C (° EApp e el)) with
            (plug (plugc C (CApp1 CHole el)) e) in H8
      by now rewrite <- plug_assoc.
    apply H6 in H8. 2: {
      eapply plugc_preserves_scope_exp; eauto.
      constructor; auto. constructor.
    }
    inv H4.
    - rewrite <- plug_assoc in H8. assumption.
    - replace (plug (plugc C (CApp1 CHole (hd :: tl))) e') with
              (plug (plugc C (CParams (CApp e') [] CHole tl)) hd) in H8
           by now do 2 rewrite <- plug_assoc.
      destruct H9 as [[Hcl1 Hcl2] H9].
      eapply CTX_isPreCtxRel_CParams in H8; eauto.
      2: congruence.
      2: constructor.
      2: auto.
      apply H9 in H8. rewrite <- plug_assoc in H8. assumption.
      eapply plugc_preserves_scope_exp; eauto.
      constructor; auto. congruence. 1,3: constructor.
      auto.
      now inv H2.
  * admit.
  * unfold CompatibleLet. intros. subst. unfold CTX in *. intuition.
    replace (plug C (° ELet l' e1 e2)) with
            (plug (plugc C (CLet1 l' CHole e2)) e1) in H10 by now rewrite <- plug_assoc.
    apply H6 in H10.
    2: eapply plugc_preserves_scope_exp; eauto; constructor; auto; constructor.
    replace (plug (plugc C (CLet1 l' CHole e2)) e1') with
            (plug (plugc C (CLet2 l' e1' CHole)) e2) in H10.
    2: { repeat rewrite <- plug_assoc. now simpl. }
    apply H7 in H10. now rewrite <- plug_assoc in H10.
    eapply plugc_preserves_scope_exp; eauto; constructor; auto; constructor.
  * unfold CompatibleSeq. intros. unfold CTX in *. intuition.
    replace (plug C (° ESeq e1 e2)) with
            (plug (plugc C (CSeq1 CHole e2)) e1) in H10 by now rewrite <- plug_assoc.
    apply H6 in H10.
    2: eapply plugc_preserves_scope_exp; eauto; constructor; auto; constructor.
    replace (plug (plugc C (CSeq1 CHole e2)) e1') with
            (plug (plugc C (CSeq2 e1' CHole)) e2) in H10.
    2: { repeat rewrite <- plug_assoc. now simpl. }
    apply H7 in H10. now rewrite <- plug_assoc in H10.
    eapply plugc_preserves_scope_exp; eauto; constructor; auto; constructor.
  * unfold CompatibleLetRec. intros. unfold CTX in *. intuition.
    all: admit.
  * unfold CompatibleTry. intros. unfold CTX in *. intuition.
    replace (plug C (° ETry e1 vl1 e2 vl2 e3)) with
            (plug (plugc C (CTry1 CHole vl1 e2 vl2 e3)) e1) in H17 by now rewrite <- plug_assoc.
    apply H11 in H17.
    2: eapply plugc_preserves_scope_exp; eauto; constructor; auto; constructor.
    replace (plug (plugc C (CTry1 CHole vl1 e2 vl2 e3)) e1') with
            (plug (plugc C (CTry2 e1' vl1 CHole vl2 e3)) e2) in H17.
    2: { repeat rewrite <- plug_assoc. now simpl. }
    apply H12 in H17.
    2: eapply plugc_preserves_scope_exp; eauto; constructor; auto; constructor.
    replace (plug (plugc C (CTry2 e1' vl1 CHole vl2 e3)) e2') with
            (plug (plugc C (CTry3 e1' vl1 e2' vl2 CHole)) e3) in H17.
    2: { repeat rewrite <- plug_assoc. now simpl. }
    apply H13 in H17.
    rewrite <- plug_assoc in H17. simpl in H17. now subst.
    eapply plugc_preserves_scope_exp; eauto; constructor; auto; constructor.
Admitted.

(* generalize dependent C. induction H1; intros.
    - assumption.
    - replace (plug C (° EValues (hd :: tl))) with
              (plug (plugc C (CValues [] CHole tl)) hd) in H3 
        by now rewrite <- plug_assoc.
      destruct H. apply H0 in H3.
      
  * unfold CompatibleApp.
    intros.
    unfold CTX in *.
    intuition auto.
    1-2: rewrite indexed_to_forall in H, H0; constructor; auto.
    clear H3 H7.
    assert (EECTX Γ ⊢ plugc C (CAppFun CHole vals1) ∷ 0) as HC_e1.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H6 in HC_e1. 2: rewrite <- plug_assoc in *; simpl; auto.
    apply biforall_length in H4 as LL. rewrite <- plug_assoc in HC_e1.
    destruct vals1; intros.
    - inversion H4. now subst.
    - inversion H4. subst. destruct H9, H3. inversion H. inversion H0. subst.
      assert (EECTX Γ ⊢ plugc C (CAppParam f2 [] CHole vals1) ∷ 0). {
        eapply plugc_preserves_scope_exp; eauto.
        constructor; auto.
        constructor.
      }
      apply H7 in H10. 2: now rewrite <- plug_assoc.
      replace (hd' :: tl') with ([] ++ [hd'] ++ tl') by auto.
      eapply PreCTX_app_helper; eauto.
      now rewrite plug_assoc.
  * unfold CompatibleLet.
    intros.
    unfold CTX in *.
    intuition auto.
    clear H5 H9 H4 H8.
    assert (EECTX Γ ⊢ plugc C (CLet1 x CHole e2) ∷ 0) as HC_e1.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    assert (EECTX S Γ ⊢ plugc C (CLet2 x e1' CHole) ∷ 0) as HC_e2.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H6 in HC_e1. 2: rewrite <- plug_assoc in *; simpl; auto.
    apply H7 in HC_e2. 2: rewrite <- plug_assoc in *; simpl; auto.
    rewrite <- plug_assoc in HC_e2. simpl in HC_e2.
    shelve.
  * unfold CompatibleLetRec.
    intros.
    unfold CTX in *.
    intuition auto.
    rewrite H in H1; constructor; auto.
    clear H5 H9 H6 H10.
    assert (EECTX S (length vl) + Γ ⊢ plugc C (CLetRec1 f vl CHole e2) ∷ 0) as HC_e1.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    assert (EECTX S Γ ⊢ plugc C (CLetRec2 f vl b1' CHole) ∷ 0) as HC_e2.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H7 in HC_e1. 2: rewrite <- plug_assoc in *; simpl; auto.
    apply H8 in HC_e2. 2: rewrite <- plug_assoc in *; simpl; auto.
    rewrite <- plug_assoc in HC_e2. simpl in HC_e2.
    shelve.
  * unfold CompatibleCase.
    intros.
    unfold CTX in *.
    intuition auto.
    clear H7 H12 H8 H13 H5 H14.
    assert (EECTX Γ ⊢ plugc C (CCase1 CHole p e2 e3) ∷ 0) as HC_e1.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H9 in HC_e1. 2: rewrite <- plug_assoc; simpl; auto.
    assert (EECTX pat_vars p + Γ ⊢ plugc C (CCase2 e1' p CHole e3) ∷ 0) as HC_e2.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H10 in HC_e2. 2: { rewrite <- plug_assoc in *; simpl in *; auto. }
    assert (EECTX Γ ⊢ plugc C (CCase3 e1' p e2' CHole) ∷ 0) as HC_e3.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H11 in HC_e3. 2: { rewrite <- plug_assoc in *; simpl in *; auto. }
    rewrite <- plug_assoc in HC_e3. simpl in HC_e3. auto.
  * unfold CompatibleCons.
    intros.
    unfold CTX in *.
    intuition auto.
    clear H4 H8 H5 H9.
    assert (EECTX Γ ⊢ plugc C (CCons1 e1 CHole) ∷ 0) as HC_e1.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H7 in HC_e1. 2: rewrite <- plug_assoc; simpl; auto.
    assert (EECTX Γ ⊢ plugc C (CCons2 CHole e2') ∷ 0) as HC_e2.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H6 in HC_e2. 2: rewrite <- plug_assoc in *; simpl; auto.
    rewrite <- plug_assoc in HC_e2. simpl in HC_e2; auto.
  * unfold CompatibleBIF.
    intros.
    unfold CTX in *.
    intuition auto.
    1-2: rewrite indexed_to_forall in H, H0; constructor; auto.
    clear H3 H7.
    assert (EECTX Γ ⊢ plugc C (CBIFFun CHole vals1) ∷ 0) as HC_e1.
    { eapply plugc_preserves_scope_exp; eauto.
      constructor; auto.
      constructor.
    }
    apply H6 in HC_e1. 2: rewrite <- plug_assoc in *; simpl; auto.
    apply biforall_length in H4 as LL. rewrite <- plug_assoc in HC_e1.
    destruct vals1; intros.
    - inversion H4. now subst.
    - inversion H4. subst. destruct H9, H3. inversion H. inversion H0. subst.
      assert (EECTX Γ ⊢ plugc C (CBIFParam f2 [] CHole vals1) ∷ 0). {
        eapply plugc_preserves_scope_exp; eauto.
        constructor; auto.
        constructor.
      }
      apply H7 in H10. 2: now rewrite <- plug_assoc.
      replace (hd' :: tl') with ([] ++ [hd'] ++ tl') by auto.
      eapply PreCTX_BIF_helper; eauto.
      now rewrite plug_assoc.
  * unfold CompatibleReceive.
    intros.
    unfold CTX in *.
    split. split.
    (** TODO: will be changed *)
    3: { intros. destruct l, l2. 2-3: inversion H1.
         auto.
         destruct p, p0. inversion H1. subst. destruct H7 as [H7_1 [ [H7_21 H7_22] H7_3]].
         pose proof (PreCTX_rec_helper l l2 C Γ e p [] H2 ltac:(constructor) H3 H9 H7_21).
         simpl in H4. subst.
         epose proof (P := H7_3 (plugc C (CReceive [] p0 CHole l2)) _). do 2 rewrite <- plug_assoc in P.
         simpl in P. apply P. auto.
        }
    all: shelve.
Unshelve.
    9-10: rewrite (indexed_to_forall _ _ (PNil, ELit 0%Z)) in H;
         rewrite (indexed_to_forall _ _ (PNil, ELit 0%Z)) in H0;
         constructor; intros.
    9-10: replace (ELit 0%Z) with (snd (PNil, ELit 0%Z)) by auto.
    9-10: replace 0 with ((fst >>> pat_vars) (PNil, ELit 0%Z)) by auto.
    9-10: do 2 rewrite map_nth.
    9: apply H in H2. 10: apply H0 in H2. 9-10: break_match_hyp; apply H2.
  2-3, 6-7: exact (ELit 0%Z).
  apply alpha_eval in H4; apply alpha_eval; rewrite default_context in *;
       simpl in *; rewrite map_const in *; rewrite <- H; auto.

  apply alpha_eval. apply alpha_eval in HC_e2. rewrite default_context in *. exact HC_e2.

  apply alpha_eval. apply alpha_eval in HC_e2. rewrite default_context in *.
  simpl in *; rewrite map_const in *; rewrite <- H; auto.

  eapply plugc_preserves_scope_exp. exact H2. constructor. constructor.
  intros. inversion H5.
  intros. rewrite (indexed_to_forall _ _ (PNil, ELit 0%Z)) in H0.
  specialize (H0 (S i) ltac:(simpl;lia)).
  simpl in H0.
  replace (ELit 0%Z) with (snd (PNil, ELit 0%Z)) by auto.
  replace 0 with ((fst >>> pat_vars) (PNil, ELit 0%Z)) by auto.
  do 2 rewrite map_nth.
  break_match_hyp; cbn. auto. *)
Admitted.

Lemma CTX_IsCtxRel : IsCtxRel CTX.
Proof.
  unfold IsCtxRel.
  split.
  - apply CTX_IsPreCtxRel.
  - intros.
    eapply CTX_bigger; eauto.
Qed.

Global Hint Resolve CTX_IsCtxRel : core.
Global Hint Resolve CTX_IsPreCtxRel : core.
Global Hint Resolve CIU_implies_CTX : core.

Lemma exists_CTX : exists R, IsCtxRel R.
Proof.
  exists CTX.
  apply CTX_IsCtxRel.
Qed.


Lemma CIU_beta_value : forall {Γ e2 v},
    EXP S Γ ⊢ e2 -> VAL Γ ⊢ v ->
    (CIU_open Γ e2.[v/] (ELet 1 (`v) e2) /\ 
     CIU_open Γ (ELet 1 (`v) e2) e2.[v/]).
Proof.
  unfold CIU_open.
  intros.
  unfold CIU.
  intuition idtac.
  1,5: constructor; apply -> subst_preserves_scope_exp; try eassumption;
    apply -> subst_preserves_scope_exp; eauto.
  1,3: simpl; do 3 constructor; [ constructor; apply -> subst_preserves_scope_val; eauto |
                             apply -> subst_preserves_scope_exp; eauto ].
  destruct H3. exists (3 + x). simpl. do 2 constructor.
  now apply (subst_preserves_scope_val Γ v). constructor; auto.
  simpl. rewrite subst_comp_exp, subst_extend. simpl in H3.
  now rewrite subst_comp_exp, scons_substcomp, substcomp_id_l in H3.

  destruct H3. simpl in H3. inv H3. 2: inv_val. repeat deriv.
  simpl in *. rewrite subst_comp_exp, subst_extend in H11.
  rewrite subst_comp_exp, scons_substcomp, substcomp_id_l. eexists. exact H11.
Qed.

Lemma CTX_closed_under_substitution : forall {Γ e1 e2 v R},
    IsCtxRel R ->
    VAL Γ ⊢ v ->
    R (S Γ) e1 e2 ->
    R Γ e1.[v/] e2.[v/].
Proof.
  intros Γ e1 e2 v R HCtx Hscope_v HCtx_e1e2.
  destruct HCtx as [HCtx Hbiggest].
  destruct HCtx as [Rscope [Radequate [Rrefl [Rtrans [RFun [RValues [RCons [RTuple [RMap [RCall [RPrimOp [RApp [RCase [RLet _]]]]]]]]]]]]]].
  destruct (Rscope _ _ _ HCtx_e1e2) as [Hscope_e1 Hscope_e2].
  epose proof (@CIU_beta_value Γ e1 v Hscope_e1 _).
  epose proof (@CIU_beta_value Γ e2 v Hscope_e2 _).
  destruct H as [? _].
  destruct H0 as [_ ?].
  apply CIU_iff_Rrel, Rrel_exp_compat_reverse in H.
  apply CIU_iff_Rrel, Rrel_exp_compat_reverse in H0.
  eapply Hbiggest in H; auto using Erel_IsPreCtxRel.
  eapply Hbiggest in H0; auto using Erel_IsPreCtxRel.
  eapply Rtrans in H.
  eapply H.
  eapply Rtrans; revgoals.
  eapply H0.
  apply RLet.
  all: auto.
Unshelve.
  all: auto.
Qed.

(* Scoping.v *)
Lemma Valscope_lift :
  forall Γ l, Forall (ValScoped Γ) l ->
    Forall (ExpScoped Γ) (map VVal l).
Proof.
  intros. induction H; simpl; auto.
Qed.

(* Maps.v *)
Lemma deflatten_PBoth :
  forall {T} P (l : list T), Forall P l ->
    Forall (PBoth P) (deflatten_list l).
Proof.
  induction l using list_length_ind; intros.
  destruct l; auto. inv H0. inv H4. auto.
  simpl. constructor. 2: apply H; auto; slia.
  now constructor.
Qed.


(* NOTE: this is not going to work:

Lemma EECTX_loosen_scope :
  forall C Γ Δ, EECTX Γ ⊢ C ∷ Δ ->
    forall Γ', EECTX Γ - Γ' ⊢ C ∷ Δ - Γ'.
Proof.
  intros C Γ Δ H. induction H; intros; try constructor; auto.
  2: {
  try eapply loosen_scope_exp; try eassumption; try lia.
Qed.

Lemma CTX_loosen_scope :
  forall Γ e1 e2, CTX Γ e1 e2 ->
    forall Γ', Γ' >= Γ -> CTX Γ' e1 e2.
Proof.
  intros. destruct H as [[Hcl1 Hcl2] H]. split. split.
  1-2: eapply loosen_scope_exp; eassumption.
  intros; apply H; auto.
Qed. *)

Theorem CIU_IsCtxRel : IsCtxRel CIU_open.
Proof.
  destruct exists_CTX as [R' HR'].
  eapply bigger_implies_IsCtxRel. 2: eauto using CIU_IsPreCtxRel. apply CTX_IsCtxRel.
  induction Γ; revgoals.
  - unfold CIU_open.
    intros.
    pose proof (H0 0 ltac:(lia)). break_match_hyp. 2: inversion H1.
    simpl.
    replace e1.[ξ] with e1.[v/].[(fun n => n + 1) >>> ξ]; revgoals.
    {
      rewrite subst_comp_exp. rewrite scons_substcomp_core.
      rewrite (vclosed_ignores_sub v); auto.
      rewrite <- substcomp_scons, idsubst_up, substcomp_id_l.
      now rewrite subst_ren_scons.
    }
    replace e2.[ξ] with e2.[v/].[(fun n => n + 1) >>> ξ]; revgoals.
    {
      rewrite subst_comp_exp. rewrite scons_substcomp_core.
      rewrite (vclosed_ignores_sub v); auto.
      rewrite <- substcomp_scons, idsubst_up, substcomp_id_l.
      now rewrite subst_ren_scons.
    }
    simpl. apply IHΓ. 2: unfold subscoped; intros; apply H0; lia.
    apply CTX_closed_under_substitution; auto; revgoals.
    + eapply loosen_scope_val. 2: eassumption. lia.
  - unfold CIU_open.
    intros.
    unfold CIU.
    intuition idtac.
    + constructor. apply -> subst_preserves_scope_exp; eauto. destruct HR'.
      eapply H.
    + constructor. apply -> subst_preserves_scope_exp; eauto 3.
      eapply H.
    + simpl in *. replace e1.[ξ] with e1 in H2; revgoals.
      { replace ξ with (upn 0 ξ) by auto.
        rewrite escoped_ignores_sub; auto. destruct HR'.
        eapply H.
      }
      replace e2.[ξ] with e2; revgoals.
      { replace ξ with (upn 0 ξ) by auto.
        rewrite escoped_ignores_sub; auto. destruct HR'.
        eapply H.
      }
      clear H0.
      generalize dependent e2. generalize dependent e1. generalize dependent F.
      induction F; intros.
      * destruct HR'. destruct H, H. apply (H4 CHole); auto. constructor.
      * inversion H1. subst.
        assert (EXPCLOSED e1) as EC1 by apply H.
        assert (EXPCLOSED e2) as EC2 by apply H.
        apply put_back in H2; auto. destruct H2. apply put_back_rev; auto.
        eapply IHF; auto. exists x. exact H0.
        destruct HR'. inversion H. clear H6.
        destruct a; inversion H4; subst.
        -- simpl. apply CTX_IsPreCtxRel; auto. now apply CTX_refl.
        -- simpl. apply CTX_IsPreCtxRel; auto. inv H4. apply CTX_refl.
           scope_solver.
        -- simpl. destruct ident; simpl; apply CTX_IsPreCtxRel; auto; destruct_scopes.
           all: try apply deflatten_PBoth.
           all: try (apply Forall_app; split; try constructor); auto.
           all: try now apply Valscope_lift.
           all: try apply CTX_refl;
             repeat match goal with
             | [ H : ICLOSED _ |- _ ] => inv H
             end; auto.
           3: apply deflatten_keeps_biprop_match.
           all: apply biforall_app; [ apply biforall_IsReflexive | constructor; [| apply biforall_IsReflexive]]; auto; try now apply Valscope_lift.
           all: intros ???; now apply CTX_refl.
        -- simpl. apply CTX_IsPreCtxRel; auto.
           apply forall_biforall_refl. apply Forall_forall. intros. apply CTX_refl. rewrite Forall_forall in H8.
           now apply H8.
        -- simpl. apply CTX_IsPreCtxRel; auto.
           now apply CTX_refl.
           apply forall_biforall_refl. apply Forall_forall. intros. apply CTX_refl. rewrite Forall_forall in H10.
           now apply H10.
        -- simpl. apply CTX_IsPreCtxRel; auto.
           apply CTX_refl; now constructor.
           apply forall_biforall_refl. apply Forall_forall. intros. apply CTX_refl. rewrite Forall_forall in H10.
           now apply H10.
        -- simpl. apply CTX_IsPreCtxRel; auto.
           1-2: eapply indexed_to_forall with (def := ([], `VNil, `VNil));
                intros i Hlt;
                specialize (H8 _ Hlt);
                specialize (H9 _ Hlt);
                rewrite map_nth with (d := ([], `VNil, `VNil)) in H8, H9.
           1-2: setoid_rewrite (map_nth (fst ∘ fst) l ([], `VNil, `VNil) i) in H8;
                setoid_rewrite (map_nth (snd) l ([], `VNil, `VNil) i) in H9;
            destruct nth, p; cbn in *; split; now rewrite Nat.add_0_r.
            clear -H8 H9. induction l; constructor.
            {
              destruct a, p. split; auto.
              split; apply CTX_refl; rewrite Nat.add_0_r;
              try apply (H8 0); try apply (H9 0); slia.
            }
            {
              apply IHl; intros; try apply (H8 (S i)); try apply (H9 (S i)); slia.
            }
        -- simpl. destruct_scopes. apply CTX_IsPreCtxRel; auto.
           5: apply CTX_refl.
           1-2,5: scope_solver.
           1-2: do 2 constructor; simpl; try apply indexed_to_forall; auto.
           1-2: split; do 2 constructor.
           1,4: do 2 constructor; now apply indexed_to_forall, Valscope_lift.
           1-4: intros; repeat rewrite Nat.add_0_r.
           1-4: try apply H20; now try apply H21.
           constructor. split; auto. split; simpl; auto.
           now apply CTX_refl. constructor; auto.
           split; auto. split; simpl; apply CTX_refl; auto.
           1: scope_solver.
           do 2 constructor.
           1: do 2 constructor; now apply indexed_to_forall, Valscope_lift.
           1-2: intros; rewrite Nat.add_0_r; try apply H20; now try apply H21.
        -- simpl. apply CTX_IsPreCtxRel; auto.
           all: rewrite Nat.add_0_r; auto. all: now apply CTX_refl.
        -- simpl. apply CTX_IsPreCtxRel; auto. now apply CTX_refl.
        -- simpl. apply CTX_IsPreCtxRel; auto.
           all: rewrite Nat.add_0_r; auto. all: now apply CTX_refl.
Qed.

Theorem Erel_IsCtxRel : IsCtxRel Erel_open.
Proof.
  unfold IsCtxRel.
  split.
  apply Erel_IsPreCtxRel.
  intros.
  apply Rrel_exp_compat_reverse, CIU_iff_Rrel.
  pose proof CIU_IsCtxRel.
  unfold IsCtxRel in H1.
  destruct H1.
  eapply H2. 2: exact H0. assumption.
Qed.

Corollary CTX_implies_CIU :
  forall e1 e2 Γ, CTX Γ e1 e2 -> CIU_open Γ e1 e2.
Proof.
  intros. eapply CIU_IsCtxRel. 2: exact H. auto.
Qed.

Global Hint Resolve CTX_implies_CIU : core.

Corollary CIU_iff_CTX :
  forall e1 e2 Γ, CTX Γ e1 e2 <-> CIU_open Γ e1 e2.
Proof.
  intros. split; auto.
Qed.

Corollary Rrel_iff_CTX :
  forall e1 e2 Γ, CTX Γ e1 e2 <-> Rrel_open Γ e1 e2.
Proof.
  intros. split; intros.
  * apply CIU_iff_Rrel. auto.
  * apply CIU_iff_Rrel in H. auto.
Qed.

Corollary Erel_iff_CTX :
  forall e1 e2 Γ, CTX Γ e1 e2 <-> Erel_open Γ e1 e2.
Proof.
  intros. split; intros.
  * apply Rrel_exp_compat_reverse, CIU_iff_Rrel. auto.
  * apply Rrel_exp_compat in H. apply CIU_iff_Rrel in H. auto.
Qed.
