From Coq Require ZArith.BinInt.
From Coq Require Reals.
From Coq Require Init.Nat.
From Coq Require Strings.String.
From Coq Require FSets.FMapList.
From Coq Require Structures.OrderedTypeEx.
Require Import Omega.

Module Core_Erlang_Syntax.

Import ZArith.BinInt.
Import Reals.
Import Strings.String.
Import Lists.List.
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
| PNil.

Definition PEmptyTuple : Pattern := PTuple [].

Definition FunctionIdentifier : Type := string * nat.

Inductive Expression : Type :=
| ENil
| ELit (l : Literal)
| EVar     (v : Var)
| EFunId   (f : FunctionIdentifier)
| EFun     (vl : list Var) (e : Expression)
| ECons    (hd tl : Expression)
| ETuple   (l : list Expression)
(** Initially: for built-in functions and primitive operations : *)
| ECall    (f: string)              (l : list Expression)
(** For function applications: *)
| EApp     (exp: Expression)        (l : list Expression)
| ECase    (e: Expression)          (pl : list Pattern) (** The case pattern list *)
                                    (gl : list Expression) (** guard list *)
                                    (bl : list Expression) (** body list *)
| ELet     (s : list Var)           (el : list Expression) (e : Expression)
| ELetRec  (fids : list FunctionIdentifier) (** defined identifiers *)
           (varlists : list (list Var))     (** variable lists *)
           (bodylists : list Expression)    (** body list *)
           (e : Expression)
| EMap     (kl vl : list Expression)
(** Try binds only one variable when no exception occured, and three otherwise *)
| ETry     (e e1 e2 : Expression)   (v1 vex1 vex2 vex3 : Var).

Definition EEmptyMap : Expression := EMap [] [].
Definition EEmptyTuple : Expression := ETuple [].

(** In the future to simulate modules: *)
Inductive ErlFunction : Type := TopLevelFun (n : FunctionIdentifier) (f : ((list Var) * Expression)).

Inductive ErlModule : Type := ErlMod (a : string) (fl : list ErlFunction).

Definition FunctionExpression : Type := list Var * Expression.

(** What expressions are in normal form *)
Inductive Value : Type :=
| VNil
| VLit (l : Literal)
| VClos (env : list ((Var + FunctionIdentifier) * Value))
           (ext : list (nat * FunctionIdentifier * FunctionExpression))
           (id : nat)
           (vl : list Var)
           (e : Expression)
| VCons    (vhd vtl : Value)
| VTuple   (vl : list Value)
| VMap     (kl vl : list Value).

(** Helper definitions *)
Definition VEmptyMap : Value := VMap [] [].
Definition VEmptyTuple : Value := VTuple [].

Definition ErrorValue : Value := (VLit (Atom "error"%string)).
Definition ErrorExp : Expression := (ELit (Atom "error"%string)).
Definition ErrorPat : Pattern := PLit (Atom "error"%string).
Definition ttrue : Value := VLit (Atom "true").
Definition ffalse : Value := VLit (Atom "false").
Definition ok : Value := VLit (Atom "ok").

(** Exception representation *)
Inductive ExceptionClass : Type :=
| Error | Throw | Exit.

(** Exception class to value converter *)
Fixpoint exclass_to_value (ex : ExceptionClass) : Value :=
match ex with
| Error => VLit (Atom "Error"%string)
| Throw => VLit (Atom "Throw"%string)
| Exit => VLit (Atom "Exit"%string)
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


End Core_Erlang_Syntax.