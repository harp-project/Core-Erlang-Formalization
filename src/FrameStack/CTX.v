From CoreErlang.FrameStack Require Export CIU.

Import ListNotations.

Definition Adequate (R : nat -> Redex -> Redex -> Prop) :=
  forall p1 p2, R 0 p1 p2 -> |[], p1| ↓ -> |[], p2| ↓.

Definition IsReflexive (R : nat -> Redex -> Redex -> Prop) :=
  forall Γ p,
  RED Γ ⊢ p -> R Γ p p.


(*---------------------------- Non Value Expr Comp ------------------------------------------------------*)

Definition CompatibleEFun (R : nat -> Redex -> Redex -> Prop) :=
  forall Γ vl vl' e1 e2, vl = vl' ->
    EXP (vl + Γ) ⊢ e1 -> EXP (vl' + Γ) ⊢ e2 -> 
    R (vl + Γ) e1 e2 ->
    R Γ (EFun vl e1) (EFun vl' e2).

Definition CompatibleEValues (R : nat -> Redex -> Redex -> Prop) :=
  forall Γ el el', length el = length el' ->
    Forall (fun e => EXP Γ ⊢ e) el ->
    Forall (fun e => EXP Γ ⊢ e) el' ->
    list_biforall (R Γ) (map RExp el) (map RExp el') ->
    R Γ (EValues el) (EValues el').

Definition CompatibleECons (R : nat -> Redex -> Redex -> Prop) :=
  forall Γ e1 e1' e2 e2',
    EXP Γ ⊢ e1 -> EXP Γ ⊢ e1' -> 
    EXP Γ ⊢ e2 -> EXP Γ ⊢ e2' ->
    R Γ (RExp e1) (RExp e1') -> 
    R Γ (RExp e2) (RExp e2') ->
    R Γ (RExp (ECons e1 e2)) (RExp (ECons e1' e2')).

Definition CompatibleETuple (R : nat -> Redex -> Redex -> Prop) :=
  forall Γ el el', length el = length el' ->
    Forall (fun e => EXP Γ ⊢ e) el ->
    Forall (fun e => EXP Γ ⊢ e) el' ->
    list_biforall (R Γ) (map RExp el) (map RExp el') ->
    R Γ (ETuple el) (ETuple el').

Definition CompatibleEMap (R : nat -> Redex -> Redex -> Prop) :=
  forall Γ l l', length l = length l' ->
    Forall (PBoth (fun e => EXP Γ ⊢ e)) l ->
    Forall (PBoth (fun e => EXP Γ ⊢ e)) l' ->
    list_biforall (fun '(v1, v2) '(v1', v2') => R Γ v1 v1' /\ R Γ v2 v2')
      (map (fun '(x, y) => (RExp x, RExp y)) l) (map (fun '(x, y) => (RExp x, RExp y)) l') ->
    R Γ (EMap l) (EMap l').

Definition CompatibleECall (R : nat -> Redex -> Redex -> Prop) :=
  forall Γ m m' f f' el el', m = m' -> f = f' -> length el = length el' ->
  Forall (fun e => EXP Γ ⊢ e) el ->
  Forall (fun e => EXP Γ ⊢ e) el' ->
  list_biforall (R Γ) (map RExp el) (map RExp el') ->
    R Γ (ECall m f el) (ECall m' f' el').

Definition CompatibleEPrimOp (R : nat -> Redex -> Redex -> Prop) :=
  forall Γ f f' el el', f = f' -> length el = length el' ->
    Forall (fun e => EXP Γ ⊢ e) el ->
    Forall (fun e => EXP Γ ⊢ e) el' ->
    list_biforall (R Γ) (map RExp el) (map RExp el') ->
    R Γ (EPrimOp f el) (EPrimOp f' el').

Definition CompatibleEApp (R : nat -> Redex -> Redex -> Prop) :=
  forall Γ e e' el el', length el = length el' ->
    EXP Γ ⊢ e ->
    EXP Γ ⊢ e' ->
    Forall (fun e => EXP Γ ⊢ e) el ->
    Forall (fun e => EXP Γ ⊢ e) el' ->
    R Γ (RExp e) (RExp e') ->
    list_biforall (R Γ) (map RExp el) (map RExp el') ->
    R Γ (EApp e el) (EApp e' el').

Definition CompatibleECase (R : nat -> Redex -> Redex -> Prop) := (* TODO: l or l' in places? *)
  forall Γ e e' l l', length l = length l' ->
    EXP Γ ⊢ e ->
    EXP Γ ⊢ e' ->
    Forall (fun '(p, g, e) => EXP PatListScope p + Γ ⊢ g /\ EXP PatListScope p + Γ ⊢ e) l ->
    Forall (fun '(p, g, e) => EXP PatListScope p + Γ ⊢ g /\ EXP PatListScope p + Γ ⊢ e) l' ->
    R Γ e e' ->
    list_biforall (
      fun '(p, g, e) '(p', g', e') =>
        p = p' /\ R (PatListScope p + Γ) (RExp g) (RExp g') /\
        R (PatListScope p + Γ) (RExp e) (RExp e')
    ) l l' ->
    R Γ (ECase e l) (ECase e' l').

Definition CompatibleELet (R : nat -> Redex -> Redex -> Prop) :=
  forall Γ l e1 e2 l' e1' e2', l = l' ->
    EXP Γ ⊢ e1  ->
    EXP Γ ⊢ e1' ->
    EXP (l  + Γ) ⊢ e2  ->
    EXP (l' + Γ) ⊢ e2' ->
    R Γ       (RExp e1) (RExp e1') ->
    R (l + Γ) (RExp e2) (RExp e2') ->
    R Γ (ELet l e1 e2) (ELet l' e1' e2').

Definition CompatibleESeq (R : nat -> Redex -> Redex -> Prop) :=
  forall Γ e1 e2 e1' e2',
    EXP Γ ⊢ e1  ->
    EXP Γ ⊢ e1' ->
    EXP Γ ⊢ e2  ->
    EXP Γ ⊢ e2' ->
    R Γ (RExp e1) (RExp e1') ->
    R Γ (RExp e2) (RExp e2') ->
    R Γ (ESeq e1 e2) (ESeq e1' e2').

Definition CompatibleELetRec (R : nat -> Redex -> Redex -> Prop) :=
  forall Γ e l e' l', length l = length l' ->
    EXP (length l  + Γ) ⊢ e  ->
    EXP (length l' + Γ) ⊢ e' ->
    Forall (fun '(vl, e) => EXP length l + vl + Γ ⊢ e) l  ->
    Forall (fun '(vl, e) => EXP length l' + vl + Γ ⊢ e) l' -> 
    list_biforall (fun '(v, e) '(v', e') =>
      v = v' /\ R (length l + v + Γ) (RExp e) (RExp e')
    ) l l' ->
    R (length l + Γ) (RExp e) (RExp e') ->
    R Γ (ELetRec l e) (ELetRec l' e').

Definition CompatibleETry (R : nat -> Redex -> Redex -> Prop) :=
  forall Γ e1 vl1 e2 vl2 e3 e1' vl1' e2' vl2' e3', 
    vl1 = vl1' -> vl2 = vl2' ->
    EXP Γ ⊢ e1  ->
    EXP Γ ⊢ e1' ->
    EXP (vl1  + Γ) ⊢ e2  ->
    EXP (vl1' + Γ) ⊢ e2' ->
    EXP (vl2  + Γ) ⊢ e3  ->
    EXP (vl2' + Γ) ⊢ e3' ->
    R Γ (RExp e1) (RExp e1') ->
    R Γ (RExp e2) (RExp e2') ->
    R Γ (RExp e3) (RExp e3') ->
    R Γ (ETry e1 vl1 e2 vl2 e3) (ETry e1' vl1' e2' vl2' e3').

(*------------------------------ Value Expr Comp --------------------------------------------------------*)

Definition CompatibleVNil (R : nat -> Redex -> Redex -> Prop) :=
  forall Γ,
    R Γ (RExp (VVal VNil)) (RExp (VVal VNil)).

Definition CompatibleVLit (R : nat -> Redex -> Redex -> Prop) :=
  forall Γ l l',
    l = l' ->
    R Γ (RExp (VVal (VLit l))) (RExp (VVal (VLit l'))).

Definition CompatibleVCons (R : nat -> Redex -> Redex -> Prop) :=
  forall Γ e1 e1' e2 e2',
    VAL Γ ⊢ e1 -> VAL Γ ⊢ e1' -> 
    VAL Γ ⊢ e2 -> VAL Γ ⊢ e2' ->
    R Γ (RExp (VVal e1)) (RExp (VVal e1')) -> 
    R Γ (RExp (VVal e2)) (RExp (VVal e2')) ->
    R Γ (RExp (VVal (VCons e1 e2))) (RExp (VVal (VCons e1' e2'))).

Definition CompatibleVTuple (R : nat -> Redex -> Redex -> Prop) :=
  forall Γ el el', length el = length el' ->
    Forall (fun e => VAL Γ ⊢ e) el ->
    Forall (fun e => VAL Γ ⊢ e) el' ->
    list_biforall (R Γ) (map (RExp ∘ VVal) el) (map (RExp ∘ VVal) el') ->
    R Γ (RExp (VVal (VTuple el))) (RExp (VVal (VTuple el'))).

Definition CompatibleVMap (R : nat -> Redex -> Redex -> Prop) :=
  forall Γ l l', length l = length l' ->
    Forall (PBoth (fun e => VAL Γ ⊢ e)) l ->
    Forall (PBoth (fun e => VAL Γ ⊢ e)) l' ->
    list_biforall (fun '(v1, v2) '(v1', v2') => R Γ v1 v1' /\ R Γ v2 v2')
      (map (fun '(x, y) => (RExp (VVal x), RExp (VVal y))) l)
      (map (fun '(x, y) => (RExp (VVal x), RExp (VVal y))) l') ->
    R Γ (RExp (VVal (VMap l))) (RExp (VVal (VMap l'))).

Definition CompatibleVVar (R : nat -> Redex -> Redex -> Prop) :=
  forall Γ n n',
    n = n' ->
    n  > Γ ->
    n' > Γ ->
    R Γ (RExp (VVal (VVar n))) (RExp (VVal (VVar n'))).

Definition CompatibleVFunId (R : nat -> Redex -> Redex -> Prop) :=
  forall Γ n n' a a',
    n = n' -> a = a' ->
    n  > Γ ->
    n' > Γ ->
    R Γ (RExp (VVal (VFunId (n, a)))) (RExp (VVal (VFunId (n', a')))).

Definition CompatibleVClos (R : nat -> Redex -> Redex -> Prop) :=
  forall Γ ext id vl e ext' id' vl' e',
    length ext = length ext' ->
    id = id' -> vl = vl' ->
    EXP (length ext  + vl  + Γ) ⊢ e  -> 
    EXP (length ext' + vl' + Γ) ⊢ e' -> 
    Forall (fun '(i, v, e) => EXP length ext + v + Γ ⊢ e) ext ->
    Forall (fun '(i, v, e) => EXP length ext + v + Γ ⊢ e) ext' ->
    R (length ext + vl + Γ) (RExp e) (RExp e') ->
    list_biforall (fun '(i, v, e) '(i2, v2, e2) => 
      v = v2 /\ i = i2 /\ R (length ext + v + Γ) (RExp e) (RExp e2)) ext ext' ->
    R Γ (RExp (VVal (VClos ext id vl e))) (RExp (VVal (VClos ext' id' vl' e'))).

(*---------------------------- Meta Defs ------------------------------------------------------*)

Definition IsPreCtxRel (R : nat -> Redex -> Redex -> Prop) :=
  (forall Γ p1 p2, R Γ p1 p2 -> RED Γ ⊢ p1 /\ RED Γ ⊢ p2) /\
  Adequate R /\ IsReflexive R /\
  (forall Γ, Transitive (R Γ)) /\
  CompatibleEFun R /\
  CompatibleEValues R /\
  CompatibleECons R /\
  CompatibleETuple R /\
  CompatibleEMap R /\
  CompatibleECall R /\
  CompatibleEPrimOp R /\
  CompatibleEApp R /\
  CompatibleECase R /\
  CompatibleELet R /\
  CompatibleESeq R /\
  CompatibleELetRec R /\
  CompatibleETry R /\
  CompatibleVNil R /\
  CompatibleVLit R /\
  CompatibleVCons R /\
  CompatibleVTuple R /\
  CompatibleVMap R /\
  CompatibleVVar R /\
  CompatibleVFunId R /\
  CompatibleVClos R.

Definition IsCtxRel (R : nat -> Redex -> Redex -> Prop) :=
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

(* Theorem Erel_IsPreCtxRel : IsPreCtxRel Erel_open. *)

(* Corollary CIU_IsPreCtxRel : IsPreCtxRel CIU_open. *)


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
  Forall (fun '(p, g, e) => EXP PatListScope p + Γ ⊢ g /\ EXP PatListScope p + Γ ⊢ e) l ->
  Forall (fun '(p, g, e) => EXP PatListScope p + Γ ⊢ g /\ EXP PatListScope p + Γ ⊢ e) l' ->
  EECTX Γh ⊢ c ∷ ((PatListScope lp) + Γ) ->
  EECTX Γh ⊢ (CCase2 e l lp c e2 l') ∷ Γ

| CEScope_CCase3 : forall Γ e l lp e1 c l',
  EXP Γ ⊢ e ->
  Forall (fun '(p, g, e) => EXP PatListScope p + Γ ⊢ g /\ EXP PatListScope p + Γ ⊢ e) l ->
  Forall (fun '(p, g, e) => EXP PatListScope p + Γ ⊢ g /\ EXP PatListScope p + Γ ⊢ e) l' ->
  EXP ((PatListScope lp) + Γ) ⊢ e1 ->
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
  Forall (fun '(vl, e) => EXP 1 + length l + vl + Γ ⊢ e) l  ->
  EECTX Γh ⊢ c ∷ (1 + (length l) + (length l') + n + Γ) ->
  Forall (fun '(vl, e) => EXP 1 + length l + vl + Γ ⊢ e) l'  ->
  EXP (1 + length l + length l' + Γ) ⊢ e ->
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

(* Basics.v *)
Lemma fst_indexed_to_forall :
  forall {A : Set} (P : A -> Prop) (l : list (A * A)),
  Forall P (map fst l) <->
  (forall i d, i < length l -> P (nth i (map fst l) d)).
Proof.
  intros. split.
  {
    intro. dependent induction H; intros.
    * destruct l. 2: inv x. inv H.
    * destruct l; inv x. simpl in *.
      destruct i; auto.
      apply IHForall; auto. lia.
  }
  {
    induction l; intros; simpl in *; constructor.
    * apply (H 0). exact (fst a). lia.
    * apply IHl. intros. apply (H (S i)). lia.
  }
Qed.

(* Basics.v *)
Lemma snd_indexed_to_forall :
  forall {A : Set} (P : A -> Prop) (l : list (A * A)),
  Forall P (map snd l) <->
  (forall i d, i < length l -> P (nth i (map snd l) d)).
Proof.
  intros. split.
  {
    intro. dependent induction H; intros.
    * destruct l. 2: inv x. inv H.
    * destruct l; inv x. simpl in *.
      destruct i; auto.
      apply IHForall; auto. lia.
  }
  {
    induction l; intros; simpl in *; constructor.
    * apply (H 0). exact (fst a). lia.
    * apply IHl. intros. apply (H (S i)). lia.
  }
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
      intros. apply fst_indexed_to_forall. 2: auto.
      rewrite map_app. apply Forall_app; split; auto.
      constructor; auto. simpl. now apply IHC.
    - apply PBoth_right in H6, H7.
      intros. apply snd_indexed_to_forall. 2: auto.
      rewrite map_app. apply Forall_app; split; auto.
      constructor; auto.
  * do 2 constructor.
    - apply PBoth_left in H6, H7.
      intros. apply fst_indexed_to_forall. 2: auto.
      rewrite map_app. apply Forall_app; split; auto.
      constructor; auto.
    - apply PBoth_right in H6, H7.
      intros. apply snd_indexed_to_forall. 2: auto.
      rewrite map_app. apply Forall_app; split; auto.
      constructor; auto. simpl. now apply IHC.
  * do 2 constructor. apply indexed_to_forall.
    apply Forall_app; split; auto.
  * do 2 constructor. apply indexed_to_forall.
    apply Forall_app; split; auto.
  * do 2 constructor. now apply IHC.
    now apply indexed_to_forall.
  * do 2 constructor; auto. apply indexed_to_forall.
    apply Forall_app; split; auto.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
Qed.

(* Lemma plugc_preserves_scope_exp *)

(*V1*)
Definition CTX (Γ : nat) (e1 e2 : Exp) :=
  (EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2) /\
  (forall (C : Ctx),
      EECTX Γ ⊢ C ∷ 0 -> | [], RExp (plug C e1) | ↓ -> | [], RExp (plug C e2) | ↓).









