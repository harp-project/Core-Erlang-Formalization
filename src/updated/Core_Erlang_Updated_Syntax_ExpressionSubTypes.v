From Coq Require ZArith.BinInt.
From Coq Require Strings.String.

(*Require Import Utf8.*)

Export ZArith.BinInt.
Export Strings.String.
Export Lists.List.

Import ListNotations.

Definition Var : Set := string.

Inductive Literal : Set :=
| Atom (s: string)
| Integer (x : Z)
(* | Float (q : R) *).


Inductive Pattern : Set :=
| PVar     (v : Var)
| PLit (l : Literal)
| PCons  (hd tl : Pattern)
| PTuple (l : list Pattern)
| PMap (l : list (Pattern * Pattern))
| PNil.

Definition FunctionIdentifier : Set := nat * nat.

Inductive Expression : Set :=
| Val (e : ValueExpression)
| Exp (e : NonValueExpression)

with ValueExpression : Set := 
| VNil
| VLit    (l : Literal)
| VFun    (vl : nat) (e : Expression)
| VCons   (hd tl : ValueExpression)
| VTuple  (l : list ValueExpression)
| VMap    (l : list (ValueExpression * ValueExpression))
| VValues (el : list ValueExpression)
| EVar    (n : nat)
| EFunId  (n : nat)

with NonValueExpression : Set :=
| EValues (el : list Expression)
| ECons   (hd tl : Expression)
| ETuple  (l : list Expression)
| EMap    (l : list (Expression * Expression))
| ECall   (f : string)    (l : list Expression)
| EPrimOp (f : string)    (l : list Expression)
| EApp    (exp: Expression)     (l : list Expression)
| ECase   (e : Expression) (l : list ((list Pattern) * Expression * Expression))
| ELet    (l : nat) (e1 e2 : Expression)
| ESeq    (e1 e2 : Expression)
(*| ELetRec (l : list (FunctionIdentifier * ((list Var) * Expression))) (e : Expression) *)
| ELetRec (l : list (nat * Expression)) (e : Expression)
| ETry    (e1 : Expression) (vl1 : nat) (e2 : Expression) (vl2 : nat) (e3 : Expression)
.

Scheme Expression_ind2         := Induction for Expression Sort Prop
  with ValueExpression_ind2    := Induction for ValueExpression Sort Prop
  with NonValueExpression_ind2 := Induction for NonValueExpression Sort Prop
.

Combined Scheme Expression_ind3 from Expression_ind2, ValueExpression_ind2, NonValueExpression_ind2.
Check Expression_ind3.

Check  VLit ( Integer 10 ).
Check  Val ( VLit ( Integer 10 ) ).
Check  ESeq (Val (VLit ( Integer 10 ))) (Val (VLit ( Integer 10 ))).
Check  Exp ( ESeq (Val (VLit ( Integer 10 ))) (Val (VLit ( Integer 10 ))) ) .

Fixpoint patternScope (p : Pattern) : nat :=
match p with
 | PVar v => 1
 | PLit l => 0
 | PCons hd tl => patternScope hd + patternScope tl
 | PTuple l => fold_right (fun x y => (patternScope x) + y) 0 l
 | PMap l => fold_right (fun '(a,b) y => (patternScope a) + (patternScope b) + y) 0 l
 | PNil => 0
end
.

Definition patternListScope (pl : list Pattern) : nat :=
fold_right (fun x y => (patternScope x) + y) 0 pl
.

Inductive ExpScoped : Expression -> nat -> Prop :=
| scoped_val (v : ValueExpression) (n : nat)    : ValExpScoped v n    -> ExpScoped (Val v) n
| scoped_exp (e : NonValueExpression) (n : nat) : NonValExpScoped e n -> ExpScoped (Exp e) n

with ValExpScoped : ValueExpression -> nat -> Prop :=
| scoped_nil (n : nat)                                : ValExpScoped VNil n
| scoped_lit (l : Literal) (n : nat)                  : ValExpScoped (VLit l) n
| scoped_var (v : nat) (n : nat)                      : n > v -> ValExpScoped (EVar v) n
| scoped_funId (fi : nat) (n : nat)                   : n > fi -> ValExpScoped (EFunId fi) n
| scoped_vtuple (l : list ValueExpression) (n : nat)  : Forall (fun x => ValExpScoped x n) l -> ValExpScoped (VTuple l) (n)
| scoped_vcons (hd tl : ValueExpression) (n : nat)    : ValExpScoped hd n -> ValExpScoped tl n -> ValExpScoped (VCons hd tl) (n)
| scoped_vmap (l : list (ValueExpression * ValueExpression)) (n : nat) : 
  Forall (fun x => ValExpScoped x n) (map (fun '(x,y) => x) l) ->
  Forall (fun x => ValExpScoped x n) (map (fun '(x,y) => y) l)
  -> ValExpScoped (VMap l) n
| scoped_vvalues (el : list ValueExpression) (n : nat)   : Forall (fun x => ValExpScoped x n) el -> ValExpScoped (VValues el) (n)
| scoped_fun (vl : nat) (e : Expression) (n : nat)  : ExpScoped e (S(vl) + n) -> ValExpScoped (VFun vl e) (n)

with NonValExpScoped : NonValueExpression -> nat -> Prop :=
| scoped_etuple (l : list Expression) (n : nat) : Forall (fun x => ExpScoped x n) l -> NonValExpScoped (ETuple l) (n)
| scoped_econs (hd tl : Expression) (n : nat)   : ExpScoped hd n -> ExpScoped tl n -> NonValExpScoped (ECons hd tl) (n)
| scoped_emap (l : list (Expression * Expression)) (n : nat) : 
  Forall (fun x => ExpScoped x n) (map (fun '(x,y) => x) l) ->
  Forall (fun x => ExpScoped x n) (map (fun '(x,y) => y) l)
  -> NonValExpScoped (EMap l) n
| scoped_evalues (el : list Expression) (n : nat)   : Forall (fun x => ExpScoped x n) el -> NonValExpScoped (EValues el) (n)
| scoped_call (f : string) (l : list Expression) (n : nat)      : Forall (fun x => ExpScoped x n) l -> NonValExpScoped (ECall f l) (n)
| scoped_primOp (f : string) (l : list Expression) (n : nat)    : Forall (fun x => ExpScoped x n) l -> NonValExpScoped (EPrimOp f l) (n)
| scoped_app (exp: Expression) (l : list Expression) (n : nat)  : ExpScoped exp n -> Forall (fun x => ExpScoped x n) l -> NonValExpScoped (EApp exp l) (n)
| scoped_case (e : Expression) (l : list ((list Pattern) * Expression * Expression)) (m n : nat) : 
  ExpScoped e n -> 
  Forall (fun x => patternListScope x <= m) (map (fun '(x,y,z) => x) l) ->
  Forall (fun x => ExpScoped x (m+n))       (map (fun '(x,y,z) => y) l) ->
  Forall (fun x => ExpScoped x (m+n))       (map (fun '(x,y,z) => z) l)
  -> NonValExpScoped (ECase e l) (n)
| scoped_let (l : nat) (e1 e2 : Expression) (n : nat) : 
  ExpScoped e1 n -> ExpScoped e2 (l+n)
  -> NonValExpScoped (ELet l e1 e2) n
| scoped_seq (e1 e2 : Expression) (n : nat) : ExpScoped e1 n -> ExpScoped e2 n -> NonValExpScoped (ESeq e1 e2) n
| scoped_letRec (l : list (nat * Expression)) (e : Expression) (m n : nat) :
  Forall (fun x => x <= m) (map (fun '(x,y) => x) l) ->
  Forall (fun x => ExpScoped x (S(m) + n)) (map (fun '(x,y) => y) l) -> (*in m + n we may need +(length l) as well because of function definitions in letRec *)
  ExpScoped e (n + (length l))
  -> NonValExpScoped (ELetRec l e) n
| scoped_try (e1 : Expression) (vl1 : nat) (e2 : Expression) (vl2 : nat) (e3 : Expression) (n : nat) : 
  ExpScoped e1 n -> 
  ExpScoped e2 (n + vl1) ->
  ExpScoped e3 (n + vl2)
  -> NonValExpScoped (ETry e1 vl1 e2 vl2 e3) n
.

Definition Renaming : Type := nat -> nat.

Definition upren (ρ : Renaming) : Renaming :=
  fun n =>
    match n with
    | 0 => 0
    | S n' => S (ρ n')
    end.

Fixpoint iterate {A : Type} (f : A -> A) n a :=
  match n with
    | 0 => a
    | S n' => f (iterate f n' a)
  end.

Notation uprenn := (iterate upren).

Check Renaming.
Check upren.
Check iterate.
Check uprenn.

Fixpoint rename (ρ : Renaming) (ex : Expression) : Expression :=
match ex with
 | Val e => Val (renameValue ρ e)
 | Exp e => Exp (renameNonValue ρ e)
end
with renameValue (ρ : Renaming) (ex : ValueExpression) : ValueExpression :=
match ex with
 | VNil         => ex
 | VLit l       => ex
 | VFun vl e    => VFun vl (rename (uprenn (S(vl)) ρ) e)
 | VCons hd tl  => VCons (renameValue ρ hd) (renameValue ρ tl)
 | VTuple l     => VTuple (map (fun x => renameValue ρ x) l)
 | VMap l       => VMap (map (fun '(x,y) => (renameValue ρ x, renameValue ρ y)) l)
 | VValues el   => VValues (map (fun x => renameValue ρ x) el)
 | EVar n       => EVar (ρ n)
 | EFunId n     => EFunId (ρ n)
end
with renameNonValue (ρ : Renaming) (ex : NonValueExpression) : NonValueExpression :=
match ex with
 | EValues el       => EValues (map (fun x => rename ρ x) el)
 | ECons   hd tl    => ECons (rename ρ hd) (rename ρ tl)
 | ETuple  l        => ETuple (map (fun x => rename ρ x) l)
 | EMap    l        => EMap (map (fun '(x,y) => (rename ρ x, rename ρ y)) l)
 | ECall   f l      => ECall f (map (fun x => rename ρ x) l)
 | EPrimOp f l      => EPrimOp f (map (fun x => rename ρ x) l)
 | EApp    e l      => EApp (rename ρ e) (map (fun x => rename ρ x) l)
 | ECase   e l      => ECase (rename ρ e) (map (fun '(p,x,y) => (p, rename (uprenn(patternListScope p) ρ) x, rename (uprenn(patternListScope p) ρ) y)) l)
 | ELet    l e1 e2  => ELet l (rename ρ e1) (rename (uprenn (l) ρ) e2)
 | ESeq    e1 e2    => ESeq (rename ρ e1) (rename ρ e2)
 | ELetRec l e      => ELetRec (map (fun '(n,x) => (n, rename (uprenn (S(n)) ρ) x)) l) (rename (uprenn (length l) ρ) e)
 | ETry    e1 vl1 e2 vl2 e3 => ETry (rename ρ e1) vl1 (rename (uprenn (vl1) ρ) e2) vl2 (rename (uprenn (vl2) ρ) e3)
end
.


Definition Substitution := nat -> ValueExpression + nat. (** We need to have the names for the
                                                  identity elements explicitly, because 
                                                  of the shiftings (up, upn) *)
Definition idsubst : Substitution := fun x => inr x.

Definition shift (ξ : Substitution) : Substitution := 
fun s =>
  match ξ s with
  | inl exp => inl (renameValue (fun n => S n) exp)
  | inr num => inr (S num)
  end.

Definition up_subst (ξ : Substitution) : Substitution :=
  fun x =>
    match x with
    | 0 => inr 0
    | S x' => shift ξ x'
    end.

Notation upn := (iterate up_subst).

Check Substitution.
Check up_subst.
Check upn.

Fixpoint subst (ξ : Substitution) (base : Expression) : Expression :=
match base with
  | Val v => Val (substVal ξ v)
  | Exp e => Exp (substNonVal ξ e)
end
with substVal (ξ : Substitution) (ex : ValueExpression) : ValueExpression :=
match ex with
 | VNil         => ex
 | VLit l       => ex
 | VFun vl e    => VFun vl (subst (upn (S(vl)) ξ) e)
 | VCons hd tl  => VCons (substVal ξ hd) (substVal ξ tl)
 | VTuple l     => VTuple (map (fun x => substVal ξ x) l)
 | VMap l       => VMap (map (fun '(x,y) => (substVal ξ x, substVal ξ y)) l)
 | VValues el   => VValues (map (fun x => substVal ξ x) el)
 | EVar n       => match ξ n with
                     | inl exp => exp
                     | inr num => EVar num
                     end
 | EFunId n     => match ξ n with
                     | inl exp => exp
                     | inr num => EFunId num
                     end
end
with substNonVal (ξ : Substitution) (ex : NonValueExpression) : NonValueExpression :=
match ex with
 | EValues el       => EValues (map (fun x => subst ξ x) el)
 | ECons   hd tl    => ECons (subst ξ hd) (subst ξ tl)
 | ETuple  l        => ETuple (map (fun x => subst ξ x) l)
 | EMap    l        => EMap (map (fun '(x,y) => (subst ξ x, subst ξ y)) l)
 | ECall   f l      => ECall f (map (fun x => subst ξ x) l)
 | EPrimOp f l      => EPrimOp f (map (fun x => subst ξ x) l)
 | EApp    e l      => EApp (subst ξ e) (map (fun x => subst ξ x) l)
 | ECase   e l      => ECase (subst ξ e) (map (fun '(p,x,y) => (p, subst (upn(patternListScope p) ξ) x, subst (upn(patternListScope p) ξ) y)) l)
 | ELet    l e1 e2  => ELet l (subst ξ e1) (subst (upn (l) ξ) e2)
 | ESeq    e1 e2    => ESeq (subst ξ e1) (subst ξ e2)
 | ELetRec l e      => ELetRec (map (fun '(n,x) => (n, subst (upn (S(n)) ξ) x)) l) (subst (upn (length l) ξ) e)
 | ETry    e1 vl1 e2 vl2 e3 => ETry (subst ξ e1) vl1 (subst (upn (vl1) ξ) e2) vl2 (subst (upn (vl2) ξ) e3)
end
.