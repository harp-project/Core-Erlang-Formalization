Require Export CIU.

Import ListNotations.

Definition Adequate (R : nat -> ProgResult -> ProgResult -> Prop) :=
  forall p1 p2, R 0 p1 p2 -> |[], p1| ↓ -> |[], p2| ↓.

Definition IsReflexive (R : nat -> ProgResult -> ProgResult -> Prop) :=
  forall Γ p,
  PROG Γ ⊢ p -> R Γ p p.


(*---------------------------- Non Value Expr Comp ------------------------------------------------------*)

Definition CompatibleEFun (R : nat -> ProgResult -> ProgResult -> Prop) :=
  forall Γ vl vl' e1 e2, vl = vl' ->
    EXP (vl + Γ) ⊢ e1 -> EXP (vl' + Γ) ⊢ e2 -> 
    R (vl + Γ) (ExpRes e1) (ExpRes e2) -> (* TODO: S vl or is it just vl? *)
    R Γ (ExpRes (Exp (EFun vl e1))) (ExpRes (Exp (EFun vl' e2))).

Definition CompatibleEValues (R : nat -> ProgResult -> ProgResult -> Prop) :=
  forall Γ el el', length el = length el' ->
    (forall i, i < length el  -> EXP Γ ⊢ (nth i el (Val VNil))) ->
    (forall i, i < length el' -> EXP Γ ⊢ (nth i el' (Val VNil))) ->
    (forall i, i < length el  -> 
    R Γ (ExpRes (nth i el (Val VNil))) (ExpRes (nth i el' (Val VNil)))) ->
    R Γ (ExpRes (Exp (EValues el))) (ExpRes (Exp (EValues el'))).

Definition CompatibleECons (R : nat -> ProgResult -> ProgResult -> Prop) :=
  forall Γ e1 e1' e2 e2',
    EXP Γ ⊢ e1 -> EXP Γ ⊢ e1' -> 
    EXP Γ ⊢ e2 -> EXP Γ ⊢ e2' ->
    R Γ (ExpRes e1) (ExpRes e1') -> 
    R Γ (ExpRes e2) (ExpRes e2') ->
    R Γ (ExpRes (Exp (ECons e1 e2))) (ExpRes (Exp (ECons e1' e2'))).

Definition CompatibleETuple (R : nat -> ProgResult -> ProgResult -> Prop) :=
  forall Γ el el', length el = length el' ->
    (forall i, i < length el  -> EXP Γ ⊢ (nth i el (Val VNil))) ->
    (forall i, i < length el' -> EXP Γ ⊢ (nth i el' (Val VNil))) ->
    (forall i, i < length el -> 
    R Γ (ExpRes (nth i el (Val VNil))) (ExpRes (nth i el' (Val VNil)))) ->
    R Γ (ExpRes (Exp (ETuple el))) (ExpRes (Exp (ETuple el'))).

Definition CompatibleEMap (R : nat -> ProgResult -> ProgResult -> Prop) :=
  forall Γ l l', length l = length l' ->
    (forall i, i < length l  -> EXP Γ ⊢ (nth i (map fst l) (Val VNil))) ->
    (forall i, i < length l' -> EXP Γ ⊢ (nth i (map fst l') (Val VNil))) ->
    (forall i, i < length l  -> EXP Γ ⊢ (nth i (map snd l) (Val VNil))) ->
    (forall i, i < length l' -> EXP Γ ⊢ (nth i (map snd l') (Val VNil))) ->
    (forall i, i < length l -> 
    R Γ (ExpRes (nth i (map fst l) (Val VNil))) (ExpRes (nth i (map fst l') (Val VNil)))) ->
    (forall i, i < length l -> 
    R Γ (ExpRes (nth i (map snd l) (Val VNil))) (ExpRes (nth i (map snd l') (Val VNil)))) ->
    R Γ (ExpRes (Exp (EMap l))) (ExpRes (Exp (EMap l'))).

Definition CompatibleECall (R : nat -> ProgResult -> ProgResult -> Prop) :=
  forall Γ f f' el el', f = f' -> length el = length el' ->
    (forall i, i < length el  -> EXP Γ ⊢ (nth i el (Val VNil))) ->
    (forall i, i < length el' -> EXP Γ ⊢ (nth i el' (Val VNil))) ->
    (forall i, i < length el -> 
    R Γ (ExpRes (nth i el (Val VNil))) (ExpRes (nth i el' (Val VNil)))) ->
    R Γ (ExpRes (Exp (ECall f el))) (ExpRes (Exp (ECall f' el'))).

Definition CompatibleEPrimOp (R : nat -> ProgResult -> ProgResult -> Prop) :=
  forall Γ f f' el el', f = f' -> length el = length el' ->
    (forall i, i < length el  -> EXP Γ ⊢ (nth i el (Val VNil))) ->
    (forall i, i < length el' -> EXP Γ ⊢ (nth i el' (Val VNil))) ->
    (forall i, i < length el -> 
    R Γ (ExpRes (nth i el (Val VNil))) (ExpRes (nth i el' (Val VNil)))) ->
    R Γ (ExpRes (Exp (EPrimOp f el))) (ExpRes (Exp (EPrimOp f' el'))).

Definition CompatibleEApp (R : nat -> ProgResult -> ProgResult -> Prop) :=
  forall Γ e e' el el', length el = length el' ->
    EXP Γ ⊢ e ->
    EXP Γ ⊢ e' ->
    (forall i, i < length el  -> EXP Γ ⊢ (nth i el (Val VNil))) ->
    (forall i, i < length el' -> EXP Γ ⊢ (nth i el' (Val VNil))) ->
    R Γ (ExpRes e) (ExpRes e') ->
    (forall i, i < length el -> 
    R Γ (ExpRes (nth i el (Val VNil))) (ExpRes (nth i el' (Val VNil)))) ->
    R Γ (ExpRes (Exp (EApp e el))) (ExpRes (Exp (EApp e' el'))).

Definition CompatibleECase (R : nat -> ProgResult -> ProgResult -> Prop) := (* TODO: l or l' in places? *)
  forall Γ e e' l l', length l = length l' ->
    EXP Γ ⊢ e ->
    EXP Γ ⊢ e' ->
    (forall i, i < length l -> 
    EXP ((patternListScope (nth i (map fst (map fst l)) nil)) + Γ) ⊢ (nth i (map snd (map fst l)) (Val VNil))) ->
    (forall i, i < length l' -> 
    EXP ((patternListScope (nth i (map fst (map fst l)) nil)) + Γ) ⊢ (nth i (map snd (map fst l')) (Val VNil))) ->
    (forall i, i < length l -> 
    EXP ((patternListScope (nth i (map fst (map fst l)) nil)) + Γ) ⊢ (nth i (map snd l) (Val VNil))) ->
    (forall i, i < length l' -> 
    EXP ((patternListScope (nth i (map fst (map fst l)) nil)) + Γ) ⊢ (nth i (map snd l') (Val VNil))) ->
    (forall i, i < length l ->
    R ((patternListScope (nth i (map fst (map fst l)) nil)) + Γ)
    (ExpRes (nth i (map snd (map fst l)) (Val VNil))) (ExpRes (nth i (map snd (map fst l')) (Val VNil)))) ->
    (forall i, i < length l ->
    R ((patternListScope (nth i (map fst (map fst l)) nil)) + Γ)
    (ExpRes (nth i (map snd l) (Val VNil))) (ExpRes (nth i (map snd l') (Val VNil)))) ->
    R Γ (ExpRes (Exp (ECase e l))) (ExpRes (Exp (ECase e' l'))).

Definition CompatibleELet (R : nat -> ProgResult -> ProgResult -> Prop) :=
  forall Γ l e1 e2 l' e1' e2', l = l' ->
    EXP Γ ⊢ e1  ->
    EXP Γ ⊢ e1' ->
    EXP (l  + Γ) ⊢ e2  ->
    EXP (l' + Γ) ⊢ e2' ->
    R Γ       (ExpRes e1) (ExpRes e1') ->
    R (l + Γ) (ExpRes e2) (ExpRes e2') ->
    R Γ (ExpRes (Exp (ELet l e1 e2))) (ExpRes (Exp (ELet l' e1' e2'))).

Definition CompatibleESeq (R : nat -> ProgResult -> ProgResult -> Prop) :=
  forall Γ e1 e2 e1' e2',
    EXP Γ ⊢ e1  ->
    EXP Γ ⊢ e1' ->
    EXP Γ ⊢ e2  ->
    EXP Γ ⊢ e2' ->
    R Γ (ExpRes e1) (ExpRes e1') ->
    R Γ (ExpRes e2) (ExpRes e2') ->
    R Γ (ExpRes (Exp (ESeq e1 e2))) (ExpRes (Exp (ESeq e1' e2'))).

Definition CompatibleELetRec (R : nat -> ProgResult -> ProgResult -> Prop) :=
  forall Γ e l e' l', length l = length l' ->
    EXP (length l  + Γ) ⊢ e  ->
    EXP (length l' + Γ) ⊢ e' ->
    (forall i, i < length l  -> EXP ((length l)  + (nth i (map fst l)  0) + Γ) ⊢ (nth i (map snd l)  (Val VNil))) ->
    (forall i, i < length l' -> EXP ((length l') + (nth i (map fst l') 0) + Γ) ⊢ (nth i (map snd l') (Val VNil))) ->
    R Γ (ExpRes e) (ExpRes e') ->
    (forall i, i < length l  ->
    R ((length l)  + (nth i (map fst l)  0) + Γ)
    (ExpRes (nth i (map snd l) (Val VNil))) (ExpRes (nth i (map snd l') (Val VNil)))) ->
    R Γ (ExpRes (Exp (ELetRec l e))) (ExpRes (Exp (ELetRec l' e'))).

Definition CompatibleETry (R : nat -> ProgResult -> ProgResult -> Prop) :=
  forall Γ e1 vl1 e2 vl2 e3 e1' vl1' e2' vl2' e3', 
    vl1 = vl1' -> vl2 = vl2' ->
    EXP Γ ⊢ e1  ->
    EXP Γ ⊢ e1' ->
    EXP (vl1  + Γ) ⊢ e2  ->
    EXP (vl1' + Γ) ⊢ e2' ->
    EXP (vl2  + Γ) ⊢ e3  ->
    EXP (vl2' + Γ) ⊢ e3' ->
    R Γ (ExpRes e1) (ExpRes e1') ->
    R Γ (ExpRes e2) (ExpRes e2') ->
    R Γ (ExpRes e3) (ExpRes e3') ->
    R Γ (ExpRes (Exp (ETry e1 vl1 e2 vl2 e3))) (ExpRes (Exp (ETry e1' vl1' e2' vl2' e3'))).

(*------------------------------ Value Expr Comp --------------------------------------------------------*)

Definition CompatibleVNil (R : nat -> ProgResult -> ProgResult -> Prop) :=
  forall Γ,
    R Γ (ExpRes (Val VNil)) (ExpRes (Val VNil)).

Definition CompatibleVLit (R : nat -> ProgResult -> ProgResult -> Prop) :=
  forall Γ l l',
    l = l' -> (* TODO: Is this ok for literals? *)
    R Γ (ExpRes (Val (VLit l))) (ExpRes (Val (VLit l'))).

Definition CompatibleVCons (R : nat -> ProgResult -> ProgResult -> Prop) :=
  forall Γ e1 e1' e2 e2',
    VAL Γ ⊢ e1 -> VAL Γ ⊢ e1' -> 
    VAL Γ ⊢ e2 -> VAL Γ ⊢ e2' ->
    R Γ (ExpRes (Val e1)) (ExpRes (Val e1')) -> 
    R Γ (ExpRes (Val e2)) (ExpRes (Val e2')) ->
    R Γ (ExpRes (Val (VCons e1 e2))) (ExpRes (Val (VCons e1' e2'))).

Definition CompatibleVTuple (R : nat -> ProgResult -> ProgResult -> Prop) :=
  forall Γ el el', length el = length el' ->
    (forall i, i < length el  -> VAL Γ ⊢ (nth i el VNil)) ->
    (forall i, i < length el' -> VAL Γ ⊢ (nth i el' VNil)) ->
    (forall i, i < length el -> 
    R Γ (ExpRes (Val (nth i el VNil))) (ExpRes (Val (nth i el' VNil)))) ->
    R Γ (ExpRes (Val (VTuple el))) (ExpRes (Val (VTuple el'))).

Definition CompatibleVMap (R : nat -> ProgResult -> ProgResult -> Prop) :=
  forall Γ l l', length l = length l' ->
    (forall i, i < length l  -> VAL Γ ⊢ (nth i (map fst l)  VNil)) ->
    (forall i, i < length l' -> VAL Γ ⊢ (nth i (map fst l') VNil)) ->
    (forall i, i < length l  -> VAL Γ ⊢ (nth i (map snd l)  VNil)) ->
    (forall i, i < length l' -> VAL Γ ⊢ (nth i (map snd l') VNil)) ->
    (forall i, i < length l -> 
    R Γ (ExpRes (Val (nth i (map fst l) VNil))) (ExpRes (Val (nth i (map fst l') VNil)))) ->
    (forall i, i < length l -> 
    R Γ (ExpRes (Val (nth i (map snd l) VNil))) (ExpRes (Val (nth i (map snd l') VNil)))) ->
    R Γ (ExpRes (Val (VMap l))) (ExpRes (Val (VMap l'))).

Definition CompatibleVVar (R : nat -> ProgResult -> ProgResult -> Prop) :=
  forall Γ n n',
    n = n' ->
    n  > Γ ->
    n' > Γ ->
    R Γ (ExpRes (Val (VVar n))) (ExpRes (Val (VVar n'))).

Definition CompatibleVFunId (R : nat -> ProgResult -> ProgResult -> Prop) :=
  forall Γ n n',
    n = n' ->
    n  > Γ ->
    n' > Γ ->
    R Γ (ExpRes (Val (VFunId n))) (ExpRes (Val (VFunId n'))).

Definition CompatibleVClos (R : nat -> ProgResult -> ProgResult -> Prop) :=
  forall Γ ext id vc e ext' id' vc' e',
    length ext = length ext' ->
    id = id' -> vc = vc' ->
    EXP (length ext  + vc  + Γ) ⊢ e  -> 
    EXP (length ext' + vc' + Γ) ⊢ e' -> 
    (forall i, i < length ext  -> 
    EXP (length ext  + (nth i (map snd (map fst ext))  0) + Γ) ⊢ (nth i (map snd ext)  (Val VNil))) ->
    (forall i, i < length ext' -> 
    EXP (length ext' + (nth i (map snd (map fst ext')) 0) + Γ) ⊢ (nth i (map snd ext') (Val VNil))) ->
    R (length ext  + vc  + Γ) (ExpRes e) (ExpRes e') ->
    (forall i, i < length ext ->
    R (length ext  + (nth i (map snd (map fst ext))  0) + Γ)
    (ExpRes (nth i (map snd ext)  (Val VNil))) (ExpRes (nth i (map snd ext') (Val VNil)))) ->
    R Γ (ExpRes (Val (VClos ext id vc e))) (ExpRes (Val (VClos ext' id' vc' e'))).

(*---------------------------- Meta Defs ------------------------------------------------------*)

Definition IsPreCtxRel (R : nat -> ProgResult -> ProgResult -> Prop) :=
  (forall Γ p1 p2, R Γ p1 p2 -> PROG Γ ⊢ p1 /\ PROG Γ ⊢ p2) /\
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

Definition IsCtxRel (R : nat -> ProgResult -> ProgResult -> Prop) :=
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
| CFun    (vl : nat) (c : Ctx)
| CValues (el : list Expression) (c : Ctx) (el' : list Expression)
| CCons1  (c : Ctx) (tl : Expression)
| CCons2  (hd : Expression) (c : Ctx)
| CTuple  (l : list Expression) (c : Ctx) (l' : list Expression)
| CMap1    (l : list (Expression * Expression)) (c : Ctx) (e2 : Expression) (l' : list (Expression * Expression))
| CMap2    (l : list (Expression * Expression)) (e1 : Expression) (c : Ctx) (l' : list (Expression * Expression))
| CCall   (f : string)    (l : list Expression) (c : Ctx) (l' : list Expression)
| CPrimOp (f : string)    (l : list Expression) (c : Ctx) (l' : list Expression)
| CApp1    (c : Ctx) (l : list Expression)
| CApp2    (exp: Expression) (l : list Expression) (c : Ctx) (l' : list Expression)
| CCase1   (c : Ctx) (l : list ((list Pattern) * Expression * Expression))
| CCase2   (e : Expression) (l : list ((list Pattern) * Expression * Expression)) (lp : (list Pattern)) (c : Ctx) (e2 : Expression) (l' : list ((list Pattern) * Expression * Expression))
| CCase3   (e : Expression) (l : list ((list Pattern) * Expression * Expression)) (lp : (list Pattern)) (e1 : Expression) (c : Ctx) (l' : list ((list Pattern) * Expression * Expression))
| CLet1    (l : nat) (c : Ctx) (e2 : Expression)
| CLet2    (l : nat) (e1: Expression) (c : Ctx)
| CSeq1    (c : Ctx) (e2 : Expression)
| CSeq2    (e1 : Expression) (c : Ctx)
| CLetRec1 (l : list (nat * Expression)) (n : nat) (c : Ctx) (l' : list (nat * Expression)) (e : Expression)
| CLetRec2 (l : list (nat * Expression)) (c : Ctx)
| CTry1   (c : Ctx) (vl1 : nat) (e2 : Expression) (vl2 : nat) (e3 : Expression)
| CTry2   (e1 : Expression) (vl1 : nat) (c : Ctx) (vl2 : nat) (e3 : Expression)
| CTry3   (e1 : Expression) (vl1 : nat) (e2 : Expression) (vl2 : nat) (c : Ctx)
.

Fixpoint plug (C : Ctx) (p : Expression) :=
match C with
| CHole             => p
| CFun    vl c      => Exp ( EFun vl (plug c p) )
| CValues el c el'  => Exp ( EValues (el ++ [(plug c p)] ++ el') )
| CCons1  c tl      => Exp ( ECons (plug c p) tl )
| CCons2  hd c      => Exp ( ECons hd (plug c p) )
| CTuple  l c l'    => Exp ( ETuple (l ++ [(plug c p)] ++ l') )
| CMap1   l c e2 l' => Exp ( EMap (l ++ [((plug c p), e2)] ++ l') )
| CMap2   l e1 c l' => Exp ( EMap (l ++ [(e1, (plug c p))] ++ l') )
| CCall   f l c l'  => Exp ( ECall f (l ++ [(plug c p)] ++ l') )
| CPrimOp f l c l'  => Exp ( EPrimOp f (l ++ [(plug c p)] ++ l') )
| CApp1   c l       => Exp ( EApp (plug c p) l )
| CApp2   exp l c l' => Exp ( EApp exp (l ++ [(plug c p)] ++ l') )
| CCase1  c l       => Exp ( ECase (plug c p) l )
| CCase2  e l lp c e2 l' => Exp ( ECase e (l ++ [(lp, (plug c p), e2)] ++ l') )
| CCase3  e l lp e1 c l' => Exp ( ECase e (l ++ [(lp, e1, (plug c p))] ++ l') )
| CLet1   l c e2    => Exp ( ELet l (plug c p) e2 )
| CLet2   l e1 c    => Exp ( ELet l e1 (plug c p) )
| CSeq1   c e2      => Exp ( ESeq (plug c p) e2 )
| CSeq2   e1 c      => Exp ( ESeq e1 (plug c p) )
| CLetRec1 l n c l' e => Exp ( ELetRec (l ++ [(n, (plug c p))] ++ l') e )
| CLetRec2 l c     => Exp ( ELetRec l (plug c p) )
| CTry1   c vl1 e2 vl2 e3  => Exp ( ETry (plug c p) vl1 e2 vl2 e3 )
| CTry2   e1 vl1 c vl2 e3  => Exp ( ETry e1 vl1 (plug c p) vl2 e3 )
| CTry3   e1 vl1 e2 vl2 c  => Exp ( ETry e1 vl1 e2 vl2 (plug c p) )
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
| CCall   f l c l'  => CCall f l (plugc c p) l'
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
  (forall i, i < length el  -> EXP Γ ⊢ (nth i el  (Val VNil))) ->
  EECTX Γh ⊢ c ∷ Γ ->
  (forall i, i < length el' -> EXP Γ ⊢ (nth i el' (Val VNil))) ->
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
  (forall i, i < length l  -> EXP Γ ⊢ (nth i l  (Val VNil))) ->
  EECTX Γh ⊢ c ∷ Γ ->
  (forall i, i < length l' -> EXP Γ ⊢ (nth i l' (Val VNil))) ->
  EECTX Γh ⊢ (CTuple l c l') ∷ Γ

| CEScope_CMap1 : forall Γ l c e2 l',
  (forall i, i < length l  -> EXP Γ ⊢ (nth i (map fst l)  (Val VNil))) ->
  (forall i, i < length l  -> EXP Γ ⊢ (nth i (map snd l)  (Val VNil))) ->
  EECTX Γh ⊢ c ∷ Γ ->
  EXP Γ ⊢ e2 ->
  (forall i, i < length l' -> EXP Γ ⊢ (nth i (map fst l') (Val VNil))) ->
  (forall i, i < length l' -> EXP Γ ⊢ (nth i (map snd l') (Val VNil))) ->
  EECTX Γh ⊢ (CMap1 l c e2 l') ∷ Γ

| CEScope_CMap2 : forall Γ l e1 c l',
  (forall i, i < length l  -> EXP Γ ⊢ (nth i (map fst l)  (Val VNil))) ->
  (forall i, i < length l  -> EXP Γ ⊢ (nth i (map snd l)  (Val VNil))) ->
  EXP Γ ⊢ e1 ->
  EECTX Γh ⊢ c ∷ Γ ->
  (forall i, i < length l' -> EXP Γ ⊢ (nth i (map fst l') (Val VNil))) ->
  (forall i, i < length l' -> EXP Γ ⊢ (nth i (map snd l') (Val VNil))) ->
  EECTX Γh ⊢ (CMap2 l e1 c l') ∷ Γ

| CEScope_CCall : forall Γ f l c l',
  (forall i, i < length l  -> EXP Γ ⊢ (nth i l  (Val VNil))) ->
  EECTX Γh ⊢ c ∷ Γ ->
  (forall i, i < length l' -> EXP Γ ⊢ (nth i l' (Val VNil))) ->
  EECTX Γh ⊢ (CCall f l c l') ∷ Γ

| CEScope_CPrimOp : forall Γ f l c l',
  (forall i, i < length l  -> EXP Γ ⊢ (nth i l  (Val VNil))) ->
  EECTX Γh ⊢ c ∷ Γ ->
  (forall i, i < length l' -> EXP Γ ⊢ (nth i l' (Val VNil))) ->
  EECTX Γh ⊢ (CPrimOp f l c l') ∷ Γ

| CEScope_CApp1 : forall Γ c l,
  EECTX Γh ⊢ c ∷ Γ ->
  (forall i, i < length l  -> EXP Γ ⊢ (nth i l  (Val VNil))) ->
  EECTX Γh ⊢ (CApp1 c l) ∷ Γ

| CEScope_CApp2 : forall Γ exp l c l',
  EXP Γ ⊢ exp ->
  (forall i, i < length l  -> EXP Γ ⊢ (nth i l  (Val VNil))) ->
  EECTX Γh ⊢ c ∷ Γ ->
  (forall i, i < length l' -> EXP Γ ⊢ (nth i l' (Val VNil))) ->
  EECTX Γh ⊢ (CApp2 exp l c l') ∷ Γ

| CEScope_CCase1 : forall Γ c l,
  EECTX Γh ⊢ c ∷ Γ ->
  (forall i, i < length l -> 
  EXP ((patternListScope (nth i (map fst (map fst l)) nil)) + Γ) ⊢ (nth i (map snd (map fst l)) (Val VNil))) ->
  (forall i, i < length l -> 
  EXP ((patternListScope (nth i (map fst (map fst l)) nil)) + Γ) ⊢ (nth i (map snd l) (Val VNil))) ->
  EECTX Γh ⊢ (CCase1 c l) ∷ Γ


| CEScope_CCase2 : forall Γ e l lp c e2 l',
  EXP Γ ⊢ e ->
  (forall i, i < length l -> 
  EXP ((patternListScope (nth i (map fst (map fst l)) nil)) + Γ) ⊢ (nth i (map snd (map fst l)) (Val VNil))) ->
  (forall i, i < length l -> 
  EXP ((patternListScope (nth i (map fst (map fst l)) nil)) + Γ) ⊢ (nth i (map snd l) (Val VNil))) ->
  EECTX Γh ⊢ c ∷ ((patternListScope lp) + Γ) ->
  EXP ((patternListScope lp) + Γ) ⊢ e2 ->
  (forall i, i < length l' -> 
  EXP ((patternListScope (nth i (map fst (map fst l')) nil)) + Γ) ⊢ (nth i (map snd (map fst l')) (Val VNil))) ->
  (forall i, i < length l' -> 
  EXP ((patternListScope (nth i (map fst (map fst l')) nil)) + Γ) ⊢ (nth i (map snd l') (Val VNil))) ->
  EECTX Γh ⊢ (CCase2 e l lp c e2 l') ∷ Γ

| CEScope_CCase3 : forall Γ e l lp e1 c l',
  EXP Γ ⊢ e ->
  (forall i, i < length l -> 
  EXP ((patternListScope (nth i (map fst (map fst l)) nil)) + Γ) ⊢ (nth i (map snd (map fst l)) (Val VNil))) ->
  (forall i, i < length l -> 
  EXP ((patternListScope (nth i (map fst (map fst l)) nil)) + Γ) ⊢ (nth i (map snd l) (Val VNil))) ->
  EXP ((patternListScope lp) + Γ) ⊢ e1 ->
  EECTX Γh ⊢ c ∷ ((patternListScope lp) + Γ) ->
  (forall i, i < length l' -> 
  EXP ((patternListScope (nth i (map fst (map fst l')) nil)) + Γ) ⊢ (nth i (map snd (map fst l')) (Val VNil))) ->
  (forall i, i < length l' -> 
  EXP ((patternListScope (nth i (map fst (map fst l')) nil)) + Γ) ⊢ (nth i (map snd l') (Val VNil))) ->
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
  (forall i, i < length l  -> 
  EXP (1 + (length l) + (length l') + (nth i (map fst l)  0) + Γ) ⊢ (nth i (map snd l)  (Val VNil))) ->
  EECTX Γh ⊢ c ∷ (1 + (length l) + (length l') + n + Γ) ->
  (forall i, i < length l' -> 
  EXP (1 + (length l) + (length l') + (nth i (map fst l') 0) + Γ) ⊢ (nth i (map snd l') (Val VNil))) ->
  EXP (1 + length l + length l' + Γ) ⊢ e ->
  EECTX Γh ⊢ (CLetRec1 l n c l' e) ∷ Γ

| CEScope_CLetRec2 : forall Γ l c,
  (forall i, i < length l  -> EXP ((length l)+ (nth i (map fst l)  0) + Γ) ⊢ (nth i (map snd l)  (Val VNil))) ->
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
  | [ H : _ |- _ ] => solve [inversion H]
  end.


Lemma plug_preserves_scope_exp : forall {Γh C Γ e},
    (EECTX Γh ⊢ C ∷ Γ ->
     EXP Γh ⊢ e ->
     EXP Γ ⊢ plug C e).
Proof.
  induction C; intros; inversion H; subst.
  * simpl. auto.
  * specialize (IHC (vl + Γ) e H3 H0).
    simpl. constructor. constructor. auto.
  * specialize (IHC Γ e H6 H0).
    simpl. constructor. constructor.
    Check indexed_to_forall.
    rewrite <- (indexed_to_forall _ (fun e => EXP Γ ⊢ e) _).
    apply Forall_app. split.
    - rewrite (indexed_to_forall _ _ (Val VNil)). auto.
    - replace (plug C e :: el') with ([plug C e] ++ el') by (simpl; auto).
      apply Forall_app. split.
      + auto.
      + rewrite (indexed_to_forall _ _ (Val VNil)). auto.
  * simpl. constructor. constructor; auto.
  * simpl. constructor. constructor; auto.
  * simpl. constructor. constructor.
    rewrite <- (indexed_to_forall _ (fun e => EXP Γ ⊢ e) _). apply Forall_app. split.
    - rewrite (indexed_to_forall _ _ (Val VNil)). auto.
    - replace (plug C e :: l') with ([plug C e] ++ l') by (simpl; auto).
      apply Forall_app. split.
      + auto.
      + rewrite (indexed_to_forall _ _ (Val VNil)). auto.
  * simpl. constructor. constructor.
    - Check indexed_to_forall. Check map_nth.
      (* this section brings the fst to the front of the nth exp *)
      intros.
      replace (Val VNil) with (fst (Val VNil, Val VNil)) by (simpl;auto).
      rewrite map_nth. generalize H1. generalize i. clear i H1.
      
      rewrite <- (indexed_to_forall _ (fun e => EXP Γ ⊢ fst e) (Val VNil, Val VNil)).
      apply Forall_app. split.
      + rewrite (indexed_to_forall _ _ (Val VNil, Val VNil)). intros.
        specialize (H5 i H1). rewrite <- map_nth. simpl. auto.
      + replace ((plug C e, e2):: l') with ([(plug C e, e2)] ++ l') by (simpl; auto).
        apply Forall_app. split.
        ** rewrite (indexed_to_forall _ _ (Val VNil, Val VNil)). intros. inversion H1.
           -- subst. simpl. auto.
           -- lia.
        ** rewrite (indexed_to_forall _ _ (Val VNil, Val VNil)). intros.
           specialize (H10 i H1). rewrite <- map_nth. simpl. auto.
  - (* this section brings the fst to the front of the nth exp *)
    intros.
    replace (Val VNil) with (snd (Val VNil, Val VNil)) by (simpl;auto).
    rewrite map_nth. generalize H1. generalize i. clear i H1.
    
    rewrite <- (indexed_to_forall _ (fun e => EXP Γ ⊢ snd e) (Val VNil, Val VNil)).
    apply Forall_app. split.
    + rewrite (indexed_to_forall _ _ (Val VNil, Val VNil)). intros.
        specialize (H6 i H1). rewrite <- map_nth. simpl. auto.
      + replace ((plug C e, e2):: l') with ([(plug C e, e2)] ++ l') by (simpl; auto).
        apply Forall_app. split.
        ** rewrite (indexed_to_forall _ _ (Val VNil, Val VNil)). intros. inversion H1.
           -- subst. simpl. auto.
           -- lia.
        ** rewrite (indexed_to_forall _ _ (Val VNil, Val VNil)). intros.
           specialize (H11 i H1). rewrite <- map_nth. simpl. auto.
  * simpl. constructor. constructor.
    -(* this section brings the fst to the front of the nth exp *)
      intros.
      replace (Val VNil) with (fst (Val VNil, Val VNil)) by (simpl;auto).
      rewrite map_nth. generalize H1. generalize i. clear i H1.
      
      rewrite <- (indexed_to_forall _ (fun e => EXP Γ ⊢ fst e) (Val VNil, Val VNil)).
      apply Forall_app. split.
      + rewrite (indexed_to_forall _ _ (Val VNil, Val VNil)). intros.
        specialize (H5 i H1). rewrite <- map_nth. simpl. auto.
      + replace ((e1, plug C e):: l') with ([(e1, plug C e)] ++ l') by (simpl; auto).
        apply Forall_app. split.
        ** rewrite (indexed_to_forall _ _ (Val VNil, Val VNil)). intros. inversion H1.
           -- subst. simpl. auto.
           -- lia.
        ** rewrite (indexed_to_forall _ _ (Val VNil, Val VNil)). intros.
           specialize (H10 i H1). rewrite <- map_nth. simpl. auto.
  - (* this section brings the fst to the front of the nth exp *)
    intros.
    replace (Val VNil) with (snd (Val VNil, Val VNil)) by (simpl;auto).
    rewrite map_nth. generalize H1. generalize i. clear i H1.
    
    rewrite <- (indexed_to_forall _ (fun e => EXP Γ ⊢ snd e) (Val VNil, Val VNil)).
    apply Forall_app. split.
    + rewrite (indexed_to_forall _ _ (Val VNil, Val VNil)). intros.
        specialize (H6 i H1). rewrite <- map_nth. simpl. auto.
      + replace ((e1, plug C e):: l') with ([(e1, plug C e)] ++ l') by (simpl; auto).
        apply Forall_app. split.
        ** rewrite (indexed_to_forall _ _ (Val VNil, Val VNil)). intros. inversion H1.
           -- subst. simpl. auto.
           -- lia.
        ** rewrite (indexed_to_forall _ _ (Val VNil, Val VNil)). intros.
           specialize (H11 i H1). rewrite <- map_nth. simpl. auto.
  * simpl. constructor. constructor.
     rewrite <- (indexed_to_forall _ (fun e => EXP Γ ⊢ e) _). apply Forall_app. split.
    - rewrite (indexed_to_forall _ _ (Val VNil)). auto.
    - replace (plug C e :: l') with ([plug C e] ++ l') by (simpl; auto).
      apply Forall_app. split.
      + auto.
      + rewrite (indexed_to_forall _ _ (Val VNil)). auto.
  * simpl. constructor. constructor.
    rewrite <- (indexed_to_forall _ (fun e => EXP Γ ⊢ e) _). apply Forall_app. split.
    - rewrite (indexed_to_forall _ _ (Val VNil)). auto.
    - replace (plug C e :: l') with ([plug C e] ++ l') by (simpl; auto).
      apply Forall_app. split.
      + auto.
      + rewrite (indexed_to_forall _ _ (Val VNil)). auto.
  * simpl. constructor. constructor.
    - auto.
    - auto.
  * simpl. constructor. constructor.
    - auto.
    - rewrite <- (indexed_to_forall _ (fun e => EXP Γ ⊢ e) _). apply Forall_app. split.
      + rewrite (indexed_to_forall _ _ (Val VNil)). auto.
      + replace (plug C e :: l') with ([plug C e] ++ l') by (simpl; auto).
        apply Forall_app. split.
        ** auto.
        ** rewrite (indexed_to_forall _ _ (Val VNil)). auto.
  * simpl. constructor. constructor.
    - auto.
    - auto. 
    - auto. 
  * simpl. constructor. constructor.
    - auto.
    - (* this section brings the snd fst to the front of the nth exp *)
      intros. rewrite map_map.
      remember (fun x : list Pattern * Expression * Expression => snd (fst x)) as F.
      replace (Val VNil) with (F ([], Val VNil, Val VNil)) by (subst;simpl;auto).
      rewrite map_nth. subst.
      (* this section brings the fst fst to the front of the nth exp *)
      rewrite map_map. remember (fun x : list Pattern * Expression * Expression =>
      fst (fst x)) as F. remember (nth i (map F (l ++ (lp, plug C e0, e2) :: l')) []) as T.
      replace [] with (F ([], Val VNil, Val VNil)) in HeqT by (subst;simpl;auto).
      rewrite map_nth in HeqT. subst.
      generalize H1. generalize i. clear i H1. 
      
      rewrite <- (indexed_to_forall _ (fun e => 
      EXP (patternListScope (fst (fst e)) + Γ) ⊢ snd (fst e)) _).
      apply Forall_app. split.
      + (* Here I just need to bring H9 to the same format*)
        rewrite (indexed_to_forall _ _ ([], Val VNil, Val VNil)).
        intros. specialize (H9 i H1).
        do 2 rewrite map_map in H9.
        remember (fun x : list Pattern * Expression * Expression => snd (fst x)) as F.
        replace (Val VNil) with (F ([], Val VNil, Val VNil)) in H9 by (subst;simpl;auto).
        rewrite map_nth in H9. subst.
        remember (fun x : list Pattern * Expression * Expression =>
        fst (fst x)) as F. remember (nth i (map F l) []) as T.
        replace [] with (F ([], Val VNil, Val VNil)) in HeqT by (subst;simpl;auto).
        rewrite map_nth in HeqT. subst. auto.
      + replace ((lp, plug C e0, e2) :: l') with ([(lp, plug C e0, e2)] ++ l') 
        by (simpl; auto). apply Forall_app. split.
        ** rewrite (indexed_to_forall _ _ ([], Val VNil, Val VNil)). intros.
           inversion H1.
           -- subst. simpl. auto.
           -- lia.
        ** (* Here I just need to bring H13 to the same format*)
           rewrite (indexed_to_forall _ _ ([], Val VNil, Val VNil)).
           intros. specialize (H13 i H1).
           do 2 rewrite map_map in H13.
           remember (fun x : list Pattern * Expression * Expression => snd (fst x)) as F.
           replace (Val VNil) with (F ([], Val VNil, Val VNil)) in H13 by (subst;simpl;auto).
           rewrite map_nth in H13. subst.
           remember (fun x : list Pattern * Expression * Expression =>
           fst (fst x)) as F. remember (nth i (map F l') []) as T.
           replace [] with (F ([], Val VNil, Val VNil)) in HeqT by (subst;simpl;auto).
           rewrite map_nth in HeqT. subst. auto.
    - (* this section brings the snd fst to the front of the nth exp *)
      intros. rewrite map_map.
      remember (fun x : list Pattern * Expression * Expression => snd (x)) as F.
      replace (Val VNil) with (F ([], Val VNil, Val VNil)) by (subst;simpl;auto).
      rewrite map_nth. subst.
      (* this section brings the fst fst to the front of the nth exp *)
      remember (fun x : list Pattern * Expression * Expression =>
      fst (fst x)) as F. remember (nth i (map F (l ++ (lp, plug C e0, e2) :: l')) []) as T.
      replace [] with (F ([], Val VNil, Val VNil)) in HeqT by (subst;simpl;auto).
      rewrite map_nth in HeqT. subst.
      generalize H1. generalize i. clear i H1. 
      
      rewrite <- (indexed_to_forall _ (fun e => 
      EXP (patternListScope (fst (fst e)) + Γ) ⊢ snd (e)) _).
      apply Forall_app. split.
      + (* Here I just need to bring H10 to the same format*)
        rewrite (indexed_to_forall _ _ ([], Val VNil, Val VNil)).
        intros. specialize (H10 i H1).
        rewrite map_map in H10.
        remember (fun x : list Pattern * Expression * Expression => snd (x)) as F.
        replace (Val VNil) with (F ([], Val VNil, Val VNil)) in H10 by (subst;simpl;auto).
        rewrite map_nth in H10. subst.
        remember (fun x : list Pattern * Expression * Expression =>
        fst (fst x)) as F. remember (nth i (map F l) []) as T.
        replace [] with (F ([], Val VNil, Val VNil)) in HeqT by (subst;simpl;auto).
        rewrite map_nth in HeqT. subst. auto.
      + replace ((lp, plug C e0, e2) :: l') with ([(lp, plug C e0, e2)] ++ l') 
        by (simpl; auto). apply Forall_app. split.
        ** rewrite (indexed_to_forall _ _ ([], Val VNil, Val VNil)). intros.
           inversion H1.
           -- subst. simpl. auto.
           -- lia.
        ** (* Here I just need to bring H14 to the same format*)
           rewrite (indexed_to_forall _ _ ([], Val VNil, Val VNil)).
           intros. specialize (H14 i H1).
           rewrite map_map in H14.
           remember (fun x : list Pattern * Expression * Expression => snd (x)) as F.
           replace (Val VNil) with (F ([], Val VNil, Val VNil)) in H14 by (subst;simpl;auto).
           rewrite map_nth in H14. subst.
           remember (fun x : list Pattern * Expression * Expression =>
           fst (fst x)) as F. remember (nth i (map F l') []) as T.
           replace [] with (F ([], Val VNil, Val VNil)) in HeqT by (subst;simpl;auto).
           rewrite map_nth in HeqT. subst. auto.
  * simpl. constructor. constructor.
    - auto.
    - (* this section brings the snd fst to the front of the nth exp *)
      intros. rewrite map_map.
      remember (fun x : list Pattern * Expression * Expression => snd (fst x)) as F.
      replace (Val VNil) with (F ([], Val VNil, Val VNil)) by (subst;simpl;auto).
      rewrite map_nth. subst.
      (* this section brings the fst fst to the front of the nth exp *)
      rewrite map_map. remember (fun x : list Pattern * Expression * Expression =>
      fst (fst x)) as F. remember (nth i (map F (l ++ (lp, e1, plug C e0) :: l')) []) as T.
      replace [] with (F ([], Val VNil, Val VNil)) in HeqT by (subst;simpl;auto).
      rewrite map_nth in HeqT. subst.
      generalize H1. generalize i. clear i H1. 
      
      rewrite <- (indexed_to_forall _ (fun e => 
      EXP (patternListScope (fst (fst e)) + Γ) ⊢ snd (fst e)) _).
      apply Forall_app. split.
      + (* Here I just need to bring H9 to the same format*)
        rewrite (indexed_to_forall _ _ ([], Val VNil, Val VNil)).
        intros. specialize (H9 i H1).
        do 2 rewrite map_map in H9.
        remember (fun x : list Pattern * Expression * Expression => snd (fst x)) as F.
        replace (Val VNil) with (F ([], Val VNil, Val VNil)) in H9 by (subst;simpl;auto).
        rewrite map_nth in H9. subst.
        remember (fun x : list Pattern * Expression * Expression =>
        fst (fst x)) as F. remember (nth i (map F l) []) as T.
        replace [] with (F ([], Val VNil, Val VNil)) in HeqT by (subst;simpl;auto).
        rewrite map_nth in HeqT. subst. auto.
      + replace ((lp, e1, plug C e0) :: l') with ([(lp, e1, plug C e0)] ++ l') 
        by (simpl; auto). apply Forall_app. split.
        ** rewrite (indexed_to_forall _ _ ([], Val VNil, Val VNil)). intros.
           inversion H1.
           -- subst. simpl. auto.
           -- lia.
        ** (* Here I just need to bring H13 to the same format*)
           rewrite (indexed_to_forall _ _ ([], Val VNil, Val VNil)).
           intros. specialize (H13 i H1).
           do 2 rewrite map_map in H13.
           remember (fun x : list Pattern * Expression * Expression => snd (fst x)) as F.
           replace (Val VNil) with (F ([], Val VNil, Val VNil)) in H13 by (subst;simpl;auto).
           rewrite map_nth in H13. subst.
           remember (fun x : list Pattern * Expression * Expression =>
           fst (fst x)) as F. remember (nth i (map F l') []) as T.
           replace [] with (F ([], Val VNil, Val VNil)) in HeqT by (subst;simpl;auto).
           rewrite map_nth in HeqT. subst. auto.
    - (* this section brings the snd fst to the front of the nth exp *)
      intros. rewrite map_map.
      remember (fun x : list Pattern * Expression * Expression => snd (x)) as F.
      replace (Val VNil) with (F ([], Val VNil, Val VNil)) by (subst;simpl;auto).
      rewrite map_nth. subst.
      (* this section brings the fst fst to the front of the nth exp *)
      remember (fun x : list Pattern * Expression * Expression =>
      fst (fst x)) as F. remember (nth i (map F (l ++ (lp, e1, plug C e0) :: l')) []) as T.
      replace [] with (F ([], Val VNil, Val VNil)) in HeqT by (subst;simpl;auto).
      rewrite map_nth in HeqT. subst.
      generalize H1. generalize i. clear i H1. 
      
      rewrite <- (indexed_to_forall _ (fun e => 
      EXP (patternListScope (fst (fst e)) + Γ) ⊢ snd (e)) _).
      apply Forall_app. split.
      + (* Here I just need to bring H10 to the same format*)
        rewrite (indexed_to_forall _ _ ([], Val VNil, Val VNil)).
        intros. specialize (H10 i H1).
        rewrite map_map in H10.
        remember (fun x : list Pattern * Expression * Expression => snd (x)) as F.
        replace (Val VNil) with (F ([], Val VNil, Val VNil)) in H10 by (subst;simpl;auto).
        rewrite map_nth in H10. subst.
        remember (fun x : list Pattern * Expression * Expression =>
        fst (fst x)) as F. remember (nth i (map F l) []) as T.
        replace [] with (F ([], Val VNil, Val VNil)) in HeqT by (subst;simpl;auto).
        rewrite map_nth in HeqT. subst. auto.
      + replace ((lp, e1, plug C e0) :: l') with ([(lp, e1, plug C e0)] ++ l') 
        by (simpl; auto). apply Forall_app. split.
        ** rewrite (indexed_to_forall _ _ ([], Val VNil, Val VNil)). intros.
           inversion H1.
           -- subst. simpl. auto.
           -- lia.
        ** (* Here I just need to bring H14 to the same format*)
           rewrite (indexed_to_forall _ _ ([], Val VNil, Val VNil)).
           intros. specialize (H14 i H1).
           rewrite map_map in H14.
           remember (fun x : list Pattern * Expression * Expression => snd (x)) as F.
           replace (Val VNil) with (F ([], Val VNil, Val VNil)) in H14 by (subst;simpl;auto).
           rewrite map_nth in H14. subst.
           remember (fun x : list Pattern * Expression * Expression =>
           fst (fst x)) as F. remember (nth i (map F l') []) as T.
           replace [] with (F ([], Val VNil, Val VNil)) in HeqT by (subst;simpl;auto).
           rewrite map_nth in HeqT. subst. auto.
  * simpl. constructor. constructor; auto.
  * simpl. constructor. constructor; auto.
  * simpl. constructor. constructor; auto.
  * simpl. constructor. constructor; auto.
  * simpl. constructor. constructor.
    - (* this section brings the fst to the front of the nth exp *)
      intros. replace 0 with (fst (0, Val VNil)) by (simpl;auto).
      rewrite map_nth.
      (* this section brings the snd to the front of the nth exp *)
      remember (nth i (map snd (l ++ (n, plug C e0) :: l')) (Val VNil)) as T.
      replace (Val VNil) with (snd (0, Val VNil)) in HeqT by (simpl;auto).
      rewrite map_nth in HeqT. subst.
      generalize H1. generalize i. clear i H1.
      rewrite <- (indexed_to_forall _ (fun e => 
      EXP ( length (l ++ (n, plug C e0) :: l') + (fst e) + Γ) ⊢ snd  e) _).
      apply Forall_app. split.
      + (* Here I just need to bring H6 to the same format*)
        rewrite (indexed_to_forall _ _ (0, Val VNil)). intros.
        specialize (H6 i H1).
        remember (nth i (map fst l) 0) as T.
        replace 0 with (fst (0, Val VNil)) in HeqT by (simpl;auto).
        rewrite map_nth in HeqT. subst.
        remember (nth i (map snd l) (Val VNil)) as T in H6.
        replace (Val VNil) with (snd (0, Val VNil)) in HeqT by (simpl;auto).
        rewrite map_nth in HeqT. subst.
        replace (Datatypes.length (l ++ (n, plug C e0) :: l')) with
        (1 + Datatypes.length l + Datatypes.length l').
        ** auto.
        ** clear. rewrite app_length. replace ((n, plug C e0) :: l') with
           ([(n, plug C e0)] ++ l') by (simpl;auto). rewrite app_length. simpl. auto.
    + replace ((n, plug C e0) :: l') with ([(n, plug C e0)] ++ l') by (simpl;auto).
      apply Forall_app. split.
      ** rewrite (indexed_to_forall _ _ (0, Val VNil)). intros. inversion H1.
         -- subst. simpl. replace (Datatypes.length (l ++ (n, plug C e0) :: l')) with
            (1 + Datatypes.length l + Datatypes.length l').
            ++ auto.
            ++ clear. rewrite app_length. replace ((n, plug C e0) :: l') with
              ([(n, plug C e0)] ++ l') by (simpl;auto). rewrite app_length. simpl. auto.
         -- lia.
      ** (* Here I just need to bring H9 to the same format*)
          rewrite (indexed_to_forall _ _ (0, Val VNil)). intros.
          specialize (H9 i H1).
          remember (nth i (map fst l') 0) as T.
          replace 0 with (fst (0, Val VNil)) in HeqT by (simpl;auto).
          rewrite map_nth in HeqT. subst.
          remember (nth i (map snd l') (Val VNil)) as T in H9.
          replace (Val VNil) with (snd (0, Val VNil)) in HeqT by (simpl;auto).
          rewrite map_nth in HeqT. subst.
          replace (Datatypes.length (l ++ [(n, plug C e0)] ++ l')) with
          (1 + Datatypes.length l + Datatypes.length l').
          -- auto.
          -- clear. rewrite app_length. replace ((n, plug C e0) :: l') with
             ([(n, plug C e0)] ++ l') by (simpl;auto). rewrite app_length. simpl. auto.
    - replace (Datatypes.length (l ++ (n, plug C e0) :: l')) with
      (1 + Datatypes.length l + Datatypes.length l').
      -- auto.
      -- clear. rewrite app_length. replace ((n, plug C e0) :: l') with
         ([(n, plug C e0)] ++ l') by (simpl;auto). rewrite app_length. simpl. auto.
  * simpl. constructor. constructor; auto.
  * simpl. constructor. constructor; auto.
  * simpl. constructor. constructor; auto.
  * simpl. constructor. constructor; auto.
Qed.

(* Lemma plugc_preserves_scope_exp *)

(*V1*)
Definition CTX (Γ : nat) (e1 e2 : Expression) :=
  (EXP Γ ⊢ e1 /\ EXP Γ ⊢ e2) /\
  (forall (C : Ctx),
      EECTX Γ ⊢ C ∷ 0 -> | [], ExpRes (plug C e1) | ↓ -> | [], ExpRes (plug C e2) | ↓).









