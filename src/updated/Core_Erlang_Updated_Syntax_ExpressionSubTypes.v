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
| scoped_fun (vl : nat) (e : Expression) (n : nat)  : ExpScoped e (vl + n) -> ValExpScoped (VFun vl e) (n)

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
  Forall (fun x => ExpScoped x (m + n)) (map (fun '(x,y) => y) l) -> (*in m + n we may need +(length l) as well because of function definitions in letRec *)
  ExpScoped e (n + (length l))
  -> NonValExpScoped (ELetRec l e) n
| scoped_try (e1 : Expression) (vl1 : nat) (e2 : Expression) (vl2 : nat) (e3 : Expression) (n : nat) : 
  ExpScoped e1 n -> 
  ExpScoped e2 (n + vl1) ->
  ExpScoped e3 (n + vl1)
  -> NonValExpScoped (ETry e1 vl1 e2 vl2 e3) n
.
