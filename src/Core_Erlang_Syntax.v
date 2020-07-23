From Coq Require ZArith.BinInt.
From Coq Require Strings.String.
From Coq Require Structures.OrderedTypeEx.

Module Syntax.

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

Definition PEmptyTuple : Pattern := PTuple [].

Definition FunctionIdentifier : Type := string * nat.

Inductive Expression : Type :=
| ENil
| ELit (l : Literal)
| EVar     (v : Var)
| EFunId  (f : FunctionIdentifier)
| EFun     (vl : list Var) (e : Expression)
| ECons  (hd tl : Expression)
| ETuple (l : list Expression)
(** Initially: for built-in functions and primitive operations : *)
| ECall  (f: string)     (l : list Expression)
(** For function applications: *)
| EApp (exp: Expression)     (l : list Expression)
| ECase  (e: Expression) (l : list (Pattern * Expression * Expression))
| ELet   (l : list (Var * Expression)) (e : Expression)
| ELetRec (l : list (FunctionIdentifier * ((list Var) * Expression))) (e : Expression)
| EMap   (l : list (Expression * Expression))
(** Try binds only one variable when no exception occured, and three otherwise *)
| ETry   (el : list (Expression * Var)) (e1 e2 : Expression) (vex1 vex2 vex3 : Var).

Definition EEmptyMap : Expression := EMap [].
Definition EEmptyTuple : Expression := ETuple [].

(** In the future to simulate modules: *)
Inductive ErlFunction : Type := TopLevelFun (id : FunctionIdentifier) (vl : list Var) (body :  Expression).

Inductive ErlModule : Type := ErlMod (name : string) (fl : list ErlFunction).

Definition FunctionExpression : Type := list Var * Expression.

(** What expressions are in normal form *)
Inductive Value : Type :=
| VNil
| VLit     (l : Literal)
| VClos    (env : list ((Var + FunctionIdentifier) * Value))
           (ext : list (nat * FunctionIdentifier * FunctionExpression))
           (id : nat)
           (vl : list Var)
           (e : Expression)
| VCons    (vhd vtl : Value)
| VTuple   (vl : list Value)
| VMap     (l : list (Value * Value)).

(** Helper definitions *)
Definition VEmptyMap : Value := VMap [].
Definition VEmptyTuple : Value := VTuple [].

Definition ErrorValue : Value := (VLit (Atom "error"%string)).
Definition ErrorExp : Expression := (ELit (Atom "error"%string)).
Definition ErrorPat : Pattern := PLit(Atom "error"%string).
Definition ttrue : Value := VLit (Atom "true").
Definition ffalse : Value := VLit (Atom "false").
Definition ok : Value := VLit (Atom "ok").

(** Exception representation *)
Inductive ExceptionClass : Type :=
| Error | Throw | Exit.

(** Exception class to value converter *)
Fixpoint exclass_to_value (ex : ExceptionClass) : Value :=
match ex with
| Error => VLit (Atom "error"%string)
| Throw => VLit (Atom "throw"%string)
| Exit => VLit (Atom "exit"%string)
end.


(** Exception class, 1st Value : cause, 2nd Value : further details *)
Definition Exception : Type := ExceptionClass * Value * Value.

Definition badarith (v : Value) : Exception :=
  (Error, VLit (Atom "badarith"%string), v).
Definition badarg (v : Value) : Exception :=
  (Error, VLit (Atom "badarg"%string), v).
Definition novar : Exception := (Throw, VLit (Atom "novar"%string), ErrorValue).
Definition undef (v : Value) : Exception :=
  (Error, VLit (Atom "undef"%string), v).
Definition badfun (v : Value) : Exception := 
  (Error,VLit (Atom "badfun"%string), v).
Definition badarity (v : Value) : Exception := 
  (Error,VLit (Atom "badarity"%string), v).
Definition if_clause (v : Value) : Exception := 
  (Error, VLit (Atom "if_clause"%string), v).


End Syntax.