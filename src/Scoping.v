(**
  This file contains the definition of variable scopes. Scoping (closedness)
  is heavily used in the frame stack semantics, and in the equivalence
  relations.
*)

From CoreErlang Require Export Syntax.
Import ListNotations.

(** A pattern's scope is the sum of its variables. *)
Fixpoint PatVars (p : Pat) : nat :=
match p with
 (*| PVar v => 1*)
 | PVar   => 1
 | PLit l => 0
(*  | PPid p => 0 *)
 | PCons hd tl => PatVars hd + PatVars tl
 | PTuple l => foldr (fun x y => (PatVars x) + y) 0 l
 | PMap l => foldr (fun '(a,b) y => (PatVars a) + (PatVars b) + y) 0 l
 | PNil => 0
 | PBin l => foldr (fun seg acc => (PatVars (val seg)) + acc) 0 l
end.

(** Pattern list scopes for `case` expressions. *)
Definition PatListVars (pl : list Pat) : nat :=
  foldr (fun x y => (PatVars x) + y) 0 pl.


Reserved Notation "'NVAL' Γ ⊢ e" (at level 69, no associativity).
Reserved Notation "'VAL' Γ ⊢ v" (at level 69, no associativity).
Reserved Notation "'EXP' Γ ⊢ e" (at level 69, no associativity).
Reserved Notation "'PAT' Γ ⊢ e" (at level 69, no associativity).
Open Scope program_scope. (* needed for "∘" *)

(** For language elements involving lists (e.g. tuples) we originally used
    Forall in the constructors (which lead to nested induction). This was
    easier to read, but Rocq failed to generate strong enough induction
    hypotheses for proofs, thus we use indexing to mitigate this issue.
 *)
Inductive ExpScoped : nat -> Exp -> Prop :=
| scoped_val (v : Val) (Γ : nat):
  VAL Γ ⊢ v -> EXP Γ ⊢ (VVal v)

| scoped_exp (e : NonVal) (Γ : nat):
  NVAL Γ ⊢ e -> EXP Γ ⊢ (EExp e)

where "'EXP' Γ ⊢ e" := (ExpScoped Γ e)

with ValScoped : nat -> Val -> Prop :=
| scoped_nil (n : nat): VAL n ⊢ VNil

| scoped_lit (l : Lit) (n : nat): VAL n ⊢ (VLit l)

| scoped_pid (p : PID) (Γ : nat): VAL Γ ⊢ VPid p

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

| scoped_vbitstring n (b : bvn) :
  VAL n ⊢ VBitstring b

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

| scoped_call (m f : Exp) (l : list Exp) (n : nat):
  (forall i, i < length l -> EXP n ⊢ (nth i l (VVal VNil))) ->
  EXP n ⊢ m ->
  EXP n ⊢ f
->
  NVAL n ⊢ (ECall m f l)

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
  (forall i, i < length l ->
    EXP (PatListVars (nth i (map (fst ∘ fst) l) [])) + n ⊢
        nth i (map (snd ∘ fst) l) (VVal VNil)) ->
  (forall i, i < length l ->
    EXP (PatListVars (nth i (map (fst ∘ fst) l) [])) + n ⊢
        (nth i (map snd l) (VVal VNil))) ->
  (forall i, i < length l -> forall j, j < length (nth i (map (fst ∘ fst) l) []) ->
    PAT n ⊢ nth j (nth i (map (fst ∘ fst) l) []) PNil)
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

| scoped_ebin (n : nat) (l : list Exp) :
  (forall i, i < length l -> EXP n ⊢ (nth i l (VVal VNil)))
->
  NVAL n ⊢ EBin l

| scoped_eseg (n : nat) (seg : Segment Exp Exp) :
  EXP n ⊢ val seg -> EXP n ⊢ size seg
->
  NVAL n ⊢ ESeg seg

where "'NVAL' Γ ⊢ e" := (NonValScoped Γ e)
with PatScoped : nat -> Pat -> Prop :=

| scoped_pvar Γ : PAT Γ ⊢ PVar

| scoped_plit Γ l : PAT Γ ⊢ PLit l

| scoped_pnil Γ : PAT Γ ⊢ PNil

| scoped_pcons Γ p1 p2 : PAT Γ ⊢ p1 -> PAT Γ ⊢ p2 -> PAT Γ ⊢ PCons p1 p2

| scoped_ptuple Γ l :
  (forall i, i < length l -> PAT Γ ⊢ nth i l PNil)
->
  PAT Γ ⊢ PTuple l

| scoped_pmap Γ l:
  (forall i, i < length l -> PAT Γ ⊢ (nth i (map fst l) PNil)) ->
  (forall i, i < length l -> PAT Γ ⊢ (nth i (map snd l) PNil))
->
  PAT Γ ⊢ PMap l

| scoped_pbin Γ (l : list (Segment Pat Exp)) :
  (forall i, i < length l -> PAT Γ ⊢ nth i (map val l) PNil) ->
  (forall i, i < length l -> EXP Γ ⊢ nth i (map size l) (˝VNil))
->
  PAT Γ ⊢ PBin l

where "'PAT' Γ ⊢ e" := (PatScoped Γ e).

(** Special notations for closed *)
Notation "'EXPCLOSED' e"    := (EXP 0 ⊢ e) (at level 5).
Notation "'VALCLOSED' v"    := (VAL 0 ⊢ v) (at level 5).
Notation "'NVALCLOSED' v" := (NVAL 0 ⊢ v) (at level 5).
Notation "'PATCLOSED' p"    := (PAT 0 ⊢ p) (at level 5).

(** Mutual induction scheme for the expression/value/non-value scopes *)
Scheme ExpScoped_ind2     := Induction for ExpScoped Sort Prop
  with ValScoped_ind2     := Induction for ValScoped Sort Prop
  with NonValScoped_ind2  := Induction for NonValScoped Sort Prop
  with PatScoped_ind2     := Induction for PatScoped Sort Prop.
Combined Scheme scoped_ind from ExpScoped_ind2, ValScoped_ind2, NonValScoped_ind2.

(** Scopes extended for redexes *)
Reserved Notation "'RED' Γ ⊢ e" (at level 69, no associativity).
Inductive RedexScope : Redex -> nat -> Prop :=
| boxScope Γ : RED Γ ⊢ RBox
| expScope Γ e : EXP Γ ⊢ e -> RED Γ ⊢ RExp e
| excScope Γ class reason details :
  VAL Γ ⊢ reason -> VAL Γ ⊢ details
->
  RED Γ ⊢ RExc (class,reason,details)
| valSeqScope Γ vl :
  Forall (fun v => VAL Γ ⊢ v) vl
->
  RED Γ ⊢ RValSeq vl
where "'RED' Γ ⊢ e" := (RedexScope e Γ).

Notation "'REDCLOSED' v" := (RED 0 ⊢ v) (at level 5).

Coercion RExp : Exp >-> Redex.
Coercion RValSeq : ValSeq  >-> Redex. (* This only seems to work for printing *)
Coercion RExc : Exception >-> Redex.

#[global]
Hint Constructors RedexScope : core. 

Lemma forall_cons {A : Type} :
  forall (P : A -> Prop) (l : list A) (x : A) (d : A),
  (forall i, i < length (x::l) -> P (nth i (x::l) d)) ->
  (forall i, i < length l -> P (nth i l d)).
Proof.
  intros. by specialize (H (S i) ltac:(slia)).
Qed.


Ltac specialize_indices x H :=
  let Spec := fresh "Spec" in
  tryif pose proof (H x ltac:(lia)) as Spec
  then (simpl in Spec; specialize_indices (S x) H)
  else (clear H).

Ltac specialize_forall :=
  match goal with
  | [H : forall i, i < length (_ :: ?l) -> ?P |- _] =>
    simpl in H; specialize_forall
  | [H : forall i, i < S ?n -> ?P |- _] =>
    specialize_indices 0 H
  | [H : forall i, i < length [] -> _ |- _] => clear H
  | [H : forall i, i < 0 -> _ |- _] => clear H
  end.

(** Scope deconstruction tactics: *)
Ltac destruct_redex_scope :=
  match goal with
  | [H : RED _ ⊢ (RExp _) |- _] => inversion H; subst; clear H
  | [H : RED _ ⊢ (RValSeq _) |- _] => inversion H; subst; clear H
  | [H : RED _ ⊢ (RExc _) |- _] => inversion H; subst; clear H
  | [H : RED _ ⊢ RBox |- _] => clear H
  | [H : EXP _ ⊢ VVal _ |- _] => inversion H; subst; clear H
  | [H : EXP _ ⊢ EExp _ |- _] => inversion H; subst; clear H
  | [H : VAL _ ⊢ VNil |- _] => clear H
  | [H : VAL _ ⊢ VLit _ |- _] => clear H
  | [H : VAL _ ⊢ VPid _ |- _] => clear H
  | [H : VAL _ ⊢ VCons _ _ |- _] => inversion H; subst; clear H
  | [H : VAL _ ⊢ VTuple _ |- _] => inversion H; subst; clear H
  | [H : VAL _ ⊢ VMap _ |- _] => inversion H; subst; clear H
  | [H : VAL _ ⊢ VVar _ |- _] => inversion H; subst; clear H
  | [H : VAL _ ⊢ VFunId _ |- _] => inversion H; subst; clear H
  | [H : VAL _ ⊢ VClos _ _ _ _ |- _] => inversion H; subst; clear H
  | [H : VAL _ ⊢ VBitstring _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ EFun _ _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ EValues _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ ECons _ _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ ETuple _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ EMap _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ ECall _ _ _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ EPrimOp _ _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ EApp _ _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ ECase _ _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ ELet _ _ _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ ESeq _ _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ ELetRec _ _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ ETry _ _ _ _ _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ ESeg _ |- _] => inversion H; subst; clear H
  | [H : NVAL _ ⊢ EBin _ |- _] => inversion H; subst; clear H
  | [H : PAT _ ⊢ PVar |- _] => clear H
  | [H : PAT _ ⊢ PLit _ |- _] => clear H
  | [H : PAT _ ⊢ PNil |- _] => clear H
  | [H : PAT _ ⊢ PCons _ _ |- _] => inversion H; subst; clear H
  | [H : PAT _ ⊢ PTuple _ |- _] => inversion H; subst; clear H
  | [H : PAT _ ⊢ PMap _ |- _] => inversion H; subst; clear H
  | [H : PAT _ ⊢ PBin _ |- _] => inversion H; subst; clear H
  end.

Ltac destruct_redex_scopes :=
  repeat (
    repeat destruct_redex_scope;
    repeat specialize_forall
  ).

Section tests.

  Local Definition t1 e1 e2 e3 e4 e5 e6:=
    ECase (ETuple [°ECons (˝VNil) (˝VNil); e1; °ELet 1 e2 e3])
      [([PBin [{| val := PCons PVar PVar; size := e6;
                  unit := 1; type := IntType; sign := Signed;
                  endian := LittleEndian |}]], e4, e5)
      ].

  Goal forall Γ e1 e2 e3 e4 e5 e6,
    EXP Γ ⊢ t1 e1 e2 e3 e4 e5 e6 -> True.
  Proof.
    unfold t1. intros.
    destruct_redex_scopes.
    trivial.
  Qed.

End tests.

#[global]
Hint Constructors ValScoped : core.
#[global]
Hint Constructors ExpScoped : core.
#[global]
Hint Constructors NonValScoped : core.


(** We define which redexes are valid results (value sequences, exceptions). *)
Inductive is_result : Redex -> Prop :=
| exception_is_result cl v1 v2 : (* VALCLOSED v1 -> VALCLOSED v2 -> *) is_result (RExc (cl, v1, v2))
| valseq_is_result vs : (* Forall (fun v => VALCLOSED v) vs -> *) is_result (RValSeq vs).

#[global]
Hint Constructors is_result : core.

(** Inversion tactic for `is_result` *)
Ltac inv_result :=
  match goal with
  | [H : is_result RBox |- _] => inv H
  | [H : is_result (RExp _) |- _] => inv H
  end.

Definition is_closed_result (r : Redex) :=
  REDCLOSED r /\ is_result r.

