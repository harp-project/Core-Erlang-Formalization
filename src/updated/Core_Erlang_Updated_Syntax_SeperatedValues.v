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
(*All Vals*)
| ENil
| ELit    (l : Literal)
| EFun    (vl : nat) (e : Expression)
| ECons   (hd tl : Expression)
| ETuple  (l : list Expression)
| EMap    (l : list (Expression * Expression))
| EValues (el : list Expression)
| EVar    (n : nat)
| EFunId  (n : nat)
(** Initially: for built-in functions : *)
| ECall   (f : string)    (l : list Expression)
| EPrimOp (f : string)    (l : list Expression)
(** For function applications: *)
| EApp    (exp: Expression)     (l : list Expression)
| ECase   (e : Expression) (l : list ((list Pattern) * Expression * Expression))
| ELet    (l : nat) (e1 e2 : Expression)
(** For sequencing: do expressions (ESeq) *)
| ESeq    (e1 e2 : Expression)
(*| ELetRec (l : list (FunctionIdentifier * ((list Var) * Expression))) (e : Expression) *)
| ELetRec (l : list (nat * Expression)) (e : Expression)
| ETry    (e1 : Expression) (vl1 : nat) (e2 : Expression) (vl2 : nat) (e3 : Expression)
.

Inductive Value : Set :=
| VNil
| VLit    (l : Literal)
| VVar    (n : nat)
| VFunId  (n : nat)
| VFun    (vl : nat) (e : Expression)
| VCons   (hd tl : Value)
| VTuple  (l : list Value)
| VMap    (l : list (Value * Value))
| VValues (el : list Value)
.

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
| scoped_enil (n : nat)                              : ExpScoped ENil n
| scoped_elit (l : Literal) (n : nat)                : ExpScoped (ELit l) n
| scoped_efunId (fi : nat) (n : nat)                 : n > fi -> ExpScoped (EFunId fi) n
| scoped_evar (v : nat) (n : nat)                    : n > v -> ExpScoped (EVar v) n
| scoped_etuple (l : list Expression) (n : nat)     : Forall (fun x => ExpScoped x n) l -> ExpScoped (ETuple l) (n)
| scoped_econs (hd tl : Expression) (n : nat)       : ExpScoped hd n -> ExpScoped tl n -> ExpScoped (ECons hd tl) (n)
| scoped_emap (l : list (Expression * Expression)) (n : nat) : 
  Forall (fun x => ExpScoped x n) (map (fun '(x,y) => x) l) ->
  Forall (fun x => ExpScoped x n) (map (fun '(x,y) => y) l)
  -> ExpScoped (EMap l) n
| scoped_evalues (el : list Expression) (n : nat)   : Forall (fun x => ExpScoped x n) el -> ExpScoped (EValues el) (n)
| scoped_efun (vl : nat) (e : Expression) (n : nat)  : ExpScoped e (S(vl) + n) -> ExpScoped (EFun vl e) (n)
| scoped_call (f : string) (l : list Expression) (n : nat) : Forall (fun x => ExpScoped x n) l -> ExpScoped (ECall f l) (n)
| scoped_primOp (f : string) (l : list Expression) (n : nat) : Forall (fun x => ExpScoped x n) l -> ExpScoped (EPrimOp f l) (n)
| scoped_app (exp: Expression) (l : list Expression) (n : nat) : ExpScoped exp n -> Forall (fun x => ExpScoped x n) l -> ExpScoped (EApp exp l) (n)
| scoped_case (e : Expression) (l : list ((list Pattern) * Expression * Expression)) (m n : nat) : 
  ExpScoped e n -> 
  Forall (fun x => patternListScope x <= m) (map (fun '(x,y,z) => x) l) ->
  Forall (fun x => ExpScoped x (m+n))       (map (fun '(x,y,z) => y) l) ->
  Forall (fun x => ExpScoped x (m+n))       (map (fun '(x,y,z) => z) l)
  -> ExpScoped (ECase e l) (n)
| scoped_let (l : nat) (e1 e2 : Expression) (n : nat) : 
  ExpScoped e1 n -> ExpScoped e2 (l+n)
  -> ExpScoped (ELet l e1 e2) n
| scoped_seq (e1 e2 : Expression) (n : nat) : ExpScoped e1 n -> ExpScoped e2 n -> ExpScoped (ESeq e1 e2) n
| scoped_letRec (l : list (nat * Expression)) (e : Expression) (m n : nat) :
  Forall (fun x => x <= m) (map (fun '(x,y) => x) l) ->
  Forall (fun x => ExpScoped x (S(m) + n)) (map (fun '(x,y) => y) l) -> (*in m + n we may need +(length l) as well because of function definitions in letRec *)
  ExpScoped e (n + (length l))
  -> ExpScoped (ELetRec l e) n
| scoped_try (e1 : Expression) (vl1 : nat) (e2 : Expression) (vl2 : nat) (e3 : Expression) (n : nat) : 
  ExpScoped e1 n -> 
  ExpScoped e2 (n + vl1) ->
  ExpScoped e3 (n + vl2)
  -> ExpScoped (ETry e1 vl1 e2 vl2 e3) n
.

Inductive ValScoped : Value -> nat -> Prop :=
(*Exp re a func nál hivatkozok*)
| scoped_vnil (n : nat)                              : ValScoped VNil n
| scoped_vlit (l : Literal) (n : nat)                : ValScoped (VLit l) n
| scoped_vfunId (fi : nat) (n : nat)                 : n > fi -> ValScoped (VFunId fi) n
| scoped_vvar (v : nat) (n : nat)                    : n > v -> ValScoped (VVar v) n
| scoped_vtuple (l : list Value) (n : nat)     : Forall (fun x => ValScoped x n) l -> ValScoped (VTuple l) (n)
| scoped_vcons (hd tl : Value) (n : nat)       : ValScoped hd n -> ValScoped tl n -> ValScoped (VCons hd tl) (n)
| scoped_vmap (l : list (Value * Value)) (n : nat) : 
  Forall (fun x => ValScoped x n) (map (fun '(x,y) => x) l) ->
  Forall (fun x => ValScoped x n) (map (fun '(x,y) => y) l)
  -> ValScoped (VMap l) n
| scoped_vvalues (el : list Value) (n : nat) : Forall (fun x => ValScoped x n) el -> ValScoped (VValues el) (n)
| scoped_vfun (vl : nat) (e : Expression) (n : nat)  : ExpScoped e (S(vl) + n) -> ValScoped (VFun vl e) (n)
.

