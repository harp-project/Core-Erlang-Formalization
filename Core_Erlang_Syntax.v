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



(** Patterns are not expressions, because there are expressions that 
    are not patterns and patters that are not expressions (these are not implemented yet) *)
Inductive Pattern : Type :=
| PVar     (v : Var)
| PLiteral (l : Literal)
| PList  (hd tl : Pattern)
| PTuple (l : list Pattern)
| PEmptyList.

Definition PEmptyTuple : Pattern := PTuple [].

Definition FunctionIdentifier : Type := string * nat.

Inductive Expression : Type :=
| EEmptyList
| ELiteral (l : Literal)
| EVar     (v : Var)
| EFunId   (f : FunctionIdentifier)
| EFun     (vl : list Var) (e : Expression)
| EList    (hd tl : Expression)
| ETuple   (l : list Expression)
(** For built-in functions and primitive operations : *)
| ECall    (f: string)              (l : list Expression)
(** For function applications: *)
| EApply   (exp: Expression)        (l : list Expression)
| ECase    (e: Expression)          (pl : list Pattern) (** The case pattern list *)
                                    (gl : list Expression) (** guard list *)
                                    (bl : list Expression) (** body list *)
| ELet     (s : list Var)           (el : list Expression) (e : Expression)
| ELetrec  (fids : list FunctionIdentifier) (** defined identifiers *)
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
| VEmptyList
| VLiteral (l : Literal)
| VClosure (env : list ((Var + FunctionIdentifier) * Value))
           (ext : list (FunctionIdentifier * FunctionExpression))
           (vl : list Var)
           (e : Expression)
| VList    (vhd vtl : Value)
| VTuple   (vl : list Value)
| VMap     (kl vl : list Value).

(** Helper definitions *)
Definition VEmptyMap : Value := VMap [] [].
Definition VEmptyTuple : Value := VTuple [].

Definition ErrorValue : Value := (VLiteral (Atom "error"%string)).
Definition ErrorExp : Expression := (ELiteral (Atom "error"%string)).
Definition ErrorPat : Pattern := PLiteral (Atom "error"%string).
Definition ttrue : Value := VLiteral (Atom "true").
Definition ffalse : Value := VLiteral (Atom "false").
Definition ok : Value := VLiteral (Atom "ok").

(** Exception representation *)
Inductive ExceptionClass : Type :=
| Error | Throw | Exit.

(** Exception class to value converter *)
Fixpoint exclass_to_value (ex : ExceptionClass) : Value :=
match ex with
| Error => VLiteral (Atom "Error"%string)
| Throw => VLiteral (Atom "Throw"%string)
| Exit => VLiteral (Atom "Exit"%string)
end.


(** Exception class, 1st Value : cause, 2nd Value : further details *)
Definition Exception : Type := ExceptionClass * Value * Value.

Definition badarith (v : Value) : Exception :=
  (Error, VLiteral (Atom "badarith"%string), v).
Definition badarg (v : Value) : Exception :=
  (Error, VLiteral (Atom "badarg"%string), v).
Definition novar : Exception := (Throw, VLiteral (Atom "Variable error"%string), ErrorValue).
Definition undef (v : Value) : Exception :=
  (Error, VLiteral (Atom "undefined function"%string), v).
Definition noclosure (v : Value) : Exception := 
  (Error,VLiteral (Atom "not a closure"%string), v).
Definition args (v : Value) : Exception := 
  (Error,VLiteral (Atom "Not enough/too many arguments"%string), v).
Definition noclause (v : Value) : Exception := 
  (Error,VLiteral (Atom "No mathcing clause"%string), v).


End Core_Erlang_Syntax.