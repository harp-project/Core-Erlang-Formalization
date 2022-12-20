From CoreErlang Require Export Syntax.
Import ListNotations.

Fixpoint PatScope (p : Pat) : nat :=
match p with
 (*| PVar v => 1*)
 | PVar   => 1
 | PLit l => 0
 | PCons hd tl => PatScope hd + PatScope tl
 | PTuple l => fold_right (fun x y => (PatScope x) + y) 0 l
 | PMap l => fold_right (fun '(a,b) y => (PatScope a) + (PatScope b) + y) 0 l
 | PNil => 0
end.

Definition PatListScope (pl : list Pat) : nat :=
  fold_right (fun x y => (PatScope x) + y) 0 pl.

Reserved  Notation "'NVAL' Γ ⊢ e" (at level 69, no associativity).
Reserved Notation "'VAL' Γ ⊢ v" (at level 69, no associativity).
Reserved Notation "'EXP' Γ ⊢ e" (at level 69, no associativity).

Open Scope program_scope.

(** For language elements involving lists (e.g. tuples) we originally used Forall in the constructors (which lead to nested induction), this was easier to read, but Coq can not generate strong enough induction hypothesises for proofs, so we ended up using indexing witch is a bit harder to read in the definition, but Coq can use it to generate the needed hypothesises. *)
Inductive ExpScoped : nat -> Exp -> Prop :=
| scoped_val (v : Val) (Γ : nat):
  VAL Γ ⊢ v -> EXP Γ ⊢ (VVal v)

| scoped_exp (e : NonVal) (Γ : nat):
  NVAL Γ ⊢ e -> EXP Γ ⊢ (EExp e)

where "'EXP' Γ ⊢ e" := (ExpScoped Γ e)

with ValScoped : nat -> Val -> Prop :=
| scoped_nil (n : nat): VAL n ⊢ VNil

| scoped_lit (l : Lit) (n : nat): VAL n ⊢ (VLit l)

| scoped_var (v : Var) (n : nat): n > v -> VAL n ⊢ (VVar v)

| scoped_funId (fi : FunId) (n : nat): n > fst fi -> VAL n ⊢ (VFunId fi)

| scoped_vtuple (l : list Val) (n : nat):
  (forall i, i < length l -> VAL n ⊢ (nth i l VNil))
-> 
  VAL n ⊢ (VTuple l)
| scoped_vcons (hd tl : Val) (n : nat):
  VAL n ⊢ hd -> VAL n ⊢ tl
->
  VAL n ⊢ (VCons hd tl)

| scoped_vmap (l : list (Val * Val)) (n : nat) : 
  (forall i, i < length l -> VAL n ⊢ (nth i (map fst l) VNil)) ->
  (forall i, i < length l -> VAL n ⊢ (nth i (map snd l) VNil))
  ->
  VAL n ⊢ (VMap l)

| scoped_vclos (ext : list (nat * nat * Exp)) (id : nat) (vl : nat) (e : Exp) (n : nat) :
  (forall i, i < length ext ->
  EXP (length ext + (nth i (map (snd ∘ fst) ext) 0) + n) ⊢ 
      (nth i (map snd ext) (VVal VNil))) ->
  EXP (length ext + vl + n) ⊢ e->
  VAL n ⊢ (VClos ext id vl e)
where "'VAL' Γ ⊢ e" := (ValScoped Γ e)

with NonValScoped : nat -> NonVal -> Prop :=
| scoped_efun (vl : nat) (e : Exp) (n : nat):
  EXP vl + n ⊢ e -> NVAL n ⊢ EFun vl e

| scoped_etuple (l : list Exp) (n : nat) :
  (forall i, i < length l -> EXP n ⊢ (nth i l (VVal VNil)))
->
  NVAL n ⊢ (ETuple l)

| scoped_econs (hd tl : Exp) (n : nat):
  EXP n ⊢ hd -> EXP n ⊢ tl
->
  NVAL n ⊢ (ECons hd tl)

| scoped_emap (l : list (Exp * Exp)) (n : nat): 
  (forall i, i< length l -> EXP n ⊢ (nth i (map fst l) (VVal VNil))) ->
  (forall i, i< length l -> EXP n ⊢ (nth i (map snd l) (VVal VNil)))
->
  NVAL n ⊢ (EMap l)

| scoped_evalues (el : list Exp) (n : nat):
  (forall i, i < length el -> EXP n ⊢ (nth i el (VVal VNil)))
->
  NVAL n ⊢ (EValues el)

| scoped_call (f : string) (l : list Exp) (n : nat):
  (forall i, i < length l -> EXP n ⊢ (nth i l (VVal VNil)))
->
  NVAL n ⊢ (ECall f l)

| scoped_primOp (f : string) (l : list Exp) (n : nat):
  (forall i, i < length l -> EXP n ⊢ (nth i l (VVal VNil)))
->
  NVAL n ⊢ (EPrimOp f l)

| scoped_app (exp: Exp) (l : list Exp) (n : nat)  :
  EXP n ⊢ exp ->
  (forall i, i < length l -> EXP n ⊢ (nth i l (VVal VNil)))
->
  NVAL n ⊢ (EApp exp l)

| scoped_case (e : Exp) (l : list ((list Pat) * Exp * Exp)) (n : nat) : 
  EXP n ⊢ e ->
  (* todo:  *)
  (forall i, i < length l ->
    EXP (PatListScope (nth i (map (fst ∘ fst) l) [])) + n ⊢
        nth i (map (snd ∘ fst) l) (VVal VNil)) ->
  (forall i, i < length l ->
    EXP (PatListScope (nth i (map (fst ∘ fst) l) [])) + n ⊢
        (nth i (map snd l) (VVal VNil)))
->
  NVAL n ⊢ (ECase e l)

  | scoped_let (l : nat) (e1 e2 : Exp) (n : nat) : 
  EXP n ⊢ e1 -> EXP l + n ⊢ e2
->
  NVAL n ⊢ (ELet l e1 e2)

| scoped_seq (e1 e2 : Exp) (n : nat) :
  EXP n ⊢ e1 -> EXP n ⊢ e2
->
  NVAL n ⊢ (ESeq e1 e2)
  
| scoped_letRec (l : list (nat * Exp)) (e : Exp) (n : nat) :
  (forall i, i < length l ->
    EXP (length l) + (nth i (map fst l) 0) + n ⊢ 
        nth i (map snd l) (VVal VNil)) ->
  EXP (length l) + n ⊢ e
->
  NVAL n ⊢ (ELetRec l e)
  
| scoped_try (e1 : Exp) (vl1 : nat) (e2 : Exp) (vl2 : nat) (e3 : Exp) (n : nat) : 
  EXP n ⊢ e1 -> 
  EXP vl1 + n ⊢  e2 ->
  EXP vl2 + n ⊢  e3 
->
  NVAL n ⊢ (ETry e1 vl1 e2 vl2 e3)
where "'NVAL' Γ ⊢ e" := (NonValScoped Γ e).

Notation "'EXPCLOSED' e"    := (EXP 0 ⊢ e) (at level 5).
Notation "'VALCLOSED' v"    := (VAL 0 ⊢ v) (at level 5).
Notation "'NONVALCLOSED' v" := (NVAL 0 ⊢ v) (at level 5).

Scheme ExpScoped_ind2     := Induction for ExpScoped Sort Prop
  with ValScoped_ind2     := Induction for ValScoped Sort Prop
  with NonValScoped_ind2  := Induction for NonValScoped Sort Prop.
Combined Scheme scoped_ind from ExpScoped_ind2, ValScoped_ind2, NonValScoped_ind2.
