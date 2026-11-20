(**
  This file contains the definition of variable scopes. Scoping (closedness)
  is heavily used in the frame stack semantics, and in the equivalence
  relations.
*)

From CoreErlang Require Export Syntax.
Import ListNotations.

(** The number of variables bound by a pattern (i.e., the number of `PVar`s in
    it). The sizes of binary segments do not bind variables, thus they are not
    counted. *)
Fixpoint PatVars (p : Pat) : nat :=
match p with
 | PVar   => 1
 | PLit l => 0
 | PCons hd tl => PatVars hd + PatVars tl
 | PTuple l => foldr (fun x y => (PatVars x) + y) 0 l
 | PMap l => foldr (fun '(a,b) y => (PatVars a) + (PatVars b) + y) 0 l
 | PNil => 0
 | PBin l => foldr (fun seg acc => (PatVars (seg_val seg)) + acc) 0 l
end.

(** The number of variables bound by a list of patterns (e.g., the patterns of a
    `case` clause). *)
Definition PatListVars (pl : list Pat) : nat :=
  foldr (fun x y => (PatVars x) + y) 0 pl.


Reserved Notation "'NVAL' Γ ⊢ e" (at level 69, no associativity).
Reserved Notation "'VAL' Γ ⊢ v" (at level 69, no associativity).
Reserved Notation "'EXP' Γ ⊢ e" (at level 69, no associativity).
Reserved Notation "'PAT' Γ ⊢ e" (at level 69, no associativity).

(** The static semantics (scoping judgements) of expressions, values,
    non-value expressions and patterns. `EXP Γ ⊢ e` (resp. `VAL`, `NVAL`,
    `PAT`) expresses that `e` is well-scoped in a context of `Γ` variables,
    i.e., all of its free variables (and function identifiers) are de Bruijn
    indices less than `Γ`. Binders (e.g., `fun`, `let`, `case` clauses,
    `letrec`) extend the context with the number of variables they bind.

    For language elements involving lists (e.g. tuples) we originally used
    Forall in the constructors (which led to nested induction). This was
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

| scoped_vbitstring (b : bvn) n :
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

| scoped_ebin (l : list Exp) (n : nat) :
  (forall i, i < length l -> EXP n ⊢ (nth i l (VVal VNil)))
->
  NVAL n ⊢ EBin l

| scoped_eseg (seg : Segment Exp Exp) (n : nat) :
  EXP n ⊢ seg_val seg -> EXP n ⊢ seg_size seg
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

| scoped_pbin Γ (l : list (Segment Pat Val)) :
  (forall i, i < length l -> PAT Γ ⊢ nth i (map seg_val l) PNil) ->
  (forall i, i < length l -> VAL Γ ⊢ nth i (map seg_size l) VNil)
->
  PAT Γ ⊢ PBin l

where "'PAT' Γ ⊢ e" := (PatScoped Γ e).

(** Special notations for closed (i.e., scoped in the empty context) syntax. *)
Notation "'EXPCLOSED' e"    := (EXP 0 ⊢ e) (at level 5).
Notation "'VALCLOSED' v"    := (VAL 0 ⊢ v) (at level 5).
Notation "'NVALCLOSED' v" := (NVAL 0 ⊢ v) (at level 5).
Notation "'PATCLOSED' p"    := (PAT 0 ⊢ p) (at level 5).

(** Mutual induction scheme for the expression/value/non-value/pattern scopes *)
Scheme ExpScoped_ind2     := Induction for ExpScoped Sort Prop
  with ValScoped_ind2     := Induction for ValScoped Sort Prop
  with NonValScoped_ind2  := Induction for NonValScoped Sort Prop
  with PatScoped_ind2     := Induction for PatScoped Sort Prop.
Combined Scheme scoped_ind from ExpScoped_ind2,
                                ValScoped_ind2,
                                NonValScoped_ind2,
                                PatScoped_ind2.

(** Scopes extended for redexes *)
Reserved Notation "'RED' Γ ⊢ e" (at level 69, no associativity).
Inductive RedexScope : nat -> Redex -> Prop :=
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
where "'RED' Γ ⊢ e" := (RedexScope Γ e).

Notation "'REDCLOSED' v" := (RED 0 ⊢ v) (at level 5).

#[global]
Hint Constructors RedexScope : core.

(** `specialize_indices x H` instantiates an indexed hypothesis
    `H : forall i, i < k -> P i` (with a concrete bound `k`) for all indices
    from `x` to `k - 1`, then clears `H`. *)
Ltac specialize_indices x H :=
  let Spec := fresh "Spec" in
  tryif pose proof (H x ltac:(lia)) as Spec
  then (simpl in Spec; specialize_indices (S x) H)
  else (clear H).

(** `specialize_forall` finds an indexed hypothesis (as in the scoping
    judgements) over a list of known length, and instantiates it for all
    indices with `specialize_indices`. Hypotheses over empty lists are
    cleared. *)
Ltac specialize_forall :=
  match goal with
  | [H : forall i, i < length (_ :: ?l) -> ?P |- _] =>
    simpl in H; specialize_forall
  | [H : forall i, i < S ?n -> ?P |- _] =>
    specialize_indices 0 H
  | [H : forall i, i < length [] -> _ |- _] => clear H
  | [H : forall i, i < 0 -> _ |- _] => clear H
  end.

(** Scope deconstruction tactics: `destruct_redex_scope` inverts one scoping
    hypothesis of a known syntactic shape (hypotheses without premises are
    cleared). *)
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
  | [H : VAL _ ⊢ VBitstring _ |- _] => clear H
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

(** `destruct_redex_scopes` deconstructs all scoping hypotheses as far as
    possible: it alternates `destruct_redex_scope` and `specialize_forall` (to
    access the scoping of list elements) until neither makes progress. *)
Ltac destruct_redex_scopes :=
  repeat (
    repeat destruct_redex_scope;
    repeat specialize_forall
  ).

(** A test for `destruct_redex_scopes`: it should deconstruct the scoping of
    every subexpression of a nested expression. *)
Section tests.

  Local Definition t1 e1 e2 e3 e4 e5 e6:=
    ECase (ETuple [°ECons (˝VNil) (˝VNil); e1; °ELet 1 e2 e3])
      [([PBin [{| seg_val := PCons PVar PVar; seg_size := e6;
                  seg_unit := 1; seg_type := IntType; seg_sign := Signed;
                  seg_endian := LittleEndian |}]], e4, e5)
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
#[global]
Hint Constructors PatScoped : core.


(** We define which redexes are valid results (value sequences, exceptions). *)
Inductive is_result : Redex -> Prop :=
| exception_is_result cl v1 v2 : (* VALCLOSED v1 -> VALCLOSED v2 -> *) is_result (RExc (cl, v1, v2))
| valseq_is_result vs : (* Forall (fun v => VALCLOSED v) vs -> *) is_result (RValSeq vs).

#[global]
Hint Constructors is_result : core.

(** Inversion tactic for `is_result`: it eliminates impossible `is_result`
    hypotheses (about `RBox` and `RExp`). *)
Ltac inv_result :=
  match goal with
  | [H : is_result RBox |- _] => inv H
  | [H : is_result (RExp _) |- _] => inv H
  end.

(** Closed results: results that do not contain free variables. *)
Definition is_closed_result (r : Redex) :=
  REDCLOSED r /\ is_result r.

