From Coq Require ZArith.BinInt.
From Coq Require Strings.String.

(*Require Import Utf8.*)

Export ZArith.BinInt.
Export Strings.String.
Export Lists.List.

Import ListNotations.

Definition Var : Type := string.

Inductive Literal : Type :=
| Atom (s: string)
| Integer (x : Z)
(* | Float (q : R) *).


Inductive Pattern : Type :=
| PVar     (v : Var)
| PLit (l : Literal)
| PCons  (hd tl : Pattern)
| PTuple (l : list Pattern)
| PMap (l : list (Pattern * Pattern))
| PNil.

(*
Definition PEmptyTuple : Pattern := PTuple [].
*)

Definition FunctionIdentifier : Type := nat * nat.


Inductive Expression : Type :=
| EValues (el : list Expression)
| ENil                      (*is val*)
| ELit    (l : Literal)     (*is val*)
| EVar    (n : nat)
| EFunId  (n : nat)
| EFun    (vl : nat) (e : Expression)  (*is val*)
| ECons   (hd tl : Expression)              (*is val*)
| ETuple  (l : list Expression)             (*is val*)
(** Initially: for built-in functions : *)
| ECall   (f : string)    (l : list Expression)
| EPrimOp (f : string)    (l : list Expression)
(** For function applications: *)
| EApp    (exp: Expression)     (l : list Expression)
| ECase   (e : Expression) (l : list ((list Pattern) * Expression * Expression))
| ELet    (l : list Var) (e1 e2 : Expression)
(** For sequencing: do expressions (ESeq) *)
| ESeq    (e1 e2 : Expression)
| ELetRec (l : list (FunctionIdentifier * ((list Var) * Expression))) (e : Expression)
| EMap    (l : list (Expression * Expression))
| ETry    (e1 : Expression) (vl1 : list Var) (e2 : Expression) (vl2 : list Var) (e2 : Expression)
.

(*
Check Forall.
Check In.
*)

(*Goal Forall (Forall (fun x => x=2) ) [[2];[2]].
Proof.
apply Forall_cons.
trivial.
apply Forall_cons.
trivial.
apply Forall_nil.

Goal Forall (fun x => x=2) [2;2].
Proof.
apply Forall_cons.
trivial.
apply Forall_cons.
trivial.
apply Forall_nil.
*)

Inductive is_value : Expression -> Prop :=
| ENil_val : is_value ENil
| ELit_val (l : Literal) : is_value( ELit l )
| ETuple_val (le : list Expression): Forall is_value le -> is_value ( ETuple(le) )
(*
| ETuple_val (le : list Expression): (forall e, In e le -> is_value(e)) -> is_value ( ETuple(le) )
*)
(*
| ETuple_val : forall le : list Expression, forall e, in le is_value e -> is_value( ETuple(le) )
*)
(*
| ETuple_val (le : list Expression): forall e, in le is_value(e) -> is_value ( ETuple(le) )
*)
(*
| ETuple_val (e : Expression) (le : list e): is_value e -> is_value ( ETuple(le) )
*)
(*
| ETuple_val (e : Expression): is_value e -> is_value ( ETuple(list e) )
*)
(*
| ETuple_val : forall e, is_value e -> is_value ( ETuple(list e) )
*)
(*
| ETuple_val (l : Literal) (el : ELit l) (ls : list el) : is_value( ETuple ls )
*)
(*
| ETuple_val (l : Literal) (el : ELit l) (ls : list (ELit l)) : is_value( ETuple ls )
*)
| ECons_val (hd tl : Expression): is_value hd -> is_value tl -> is_value ( ECons hd tl )
| EFun_val (vl : nat) (e : Expression): is_value ( EFun vl e )
.


Inductive ExpScoped : Expression -> nat -> Prop :=
| scoped_nil (n : nat)                : ExpScoped ENil n
| scoped_lit (l : Literal) (n : nat)  : ExpScoped (ELit l) n
| scoped_var (v : nat) (n : nat)      : n > v -> ExpScoped (EVar v) n
| scoped_funId (n : nat) (n : nat)    : ExpScoped (EFunId n) n
| scoped_fun (vl : nat) (e : Expression) (n : nat)  : ExpScoped e n -> ExpScoped (EFun vl e) (n + vl)
(* Placeholder not correct, I think we need the vl + n where: ExpScoped e n, and n does not count what we counted in vl*)
| scoped_cons (hd tl : Expression) (n m : nat)      : ExpScoped hd n -> ExpScoped tl m -> ExpScoped (ECons hd tl) (n + m)
(*| scoped_tuple  (l : list Expression) (sum : nat)  : *)
.


Check Forall.

Type 10.
Type Integer 10.
Type ELit ( Integer 10 ).
Type [ ELit ( Integer 10 ); ELit ( Integer 10 ) ].
Type ETuple [ ELit ( Integer 10 ); ELit ( Integer 10 ) ].
Type is_value (ELit ( Integer 10 )).
Type is_value (ETuple [ ELit ( Integer 10 ); ELit ( Integer 10 ) ]).
Check 10.
Check Integer 10.
Check 1 + 2.

