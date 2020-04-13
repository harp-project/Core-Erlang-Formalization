From Coq Require ZArith.BinInt.
From Coq Require Reals.
From Coq Require Init.Nat.
From Coq Require Strings.String.
From Coq Require FSets.FMapList.
Require Import Omega.


From Coq Require Structures.OrderedTypeEx.

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
| EApply   (exp: Expression)        (l : list Expression)
| ECase    (e: Expression)          (pl : list Pattern) (** The case pattern list *)
                                    (gl : list Expression) (** guard list *)
                                    (bl : list Expression) (** body list *)
| ELet     (s : list Var)           (el : list Expression) (e : Expression)
| ELetrec  (fids : list FunctionIdentifier)
           (varlists : list (list Var))
           (bodylists : list Expression)
           (e : Expression)
| EMap     (kl vl : list Expression)
| ETry     (e e1 e2 : Expression)   (v1 vex1 vex2 vex3 : Var).

Definition EEmptyMap : Expression := EMap [] [].
Definition EEmptyTuple : Expression := ETuple [].


Inductive ErlFunction : Type := TopLevelFun (n : FunctionIdentifier) (f : ((list Var) * Expression)).

Inductive ErlModule : Type := ErlMod (a : string) (fl : list ErlFunction).

Definition FunctionalExpression : Type := list Var * Expression.

(** What should we call a value *)
Inductive Value : Type :=
| VEmptyList
| VLiteral (l : Literal)
| VClosure (env : list ((Var + FunctionIdentifier) * Value))
           (ext : list (FunctionIdentifier* FunctionalExpression))
           (vl : list Var)
           (e : Expression)
| VList    (vhd vtl : Value)
| VTuple   (vl : list Value)
| VMap     (kl vl : list Value).

Definition VEmptyMap : Value := VMap [] [].
Definition VEmptyTuple : Value := VTuple [].

Inductive ExceptionClass : Type :=
| Error | Throw | Exit.

Fixpoint exclass_to_value (ex : ExceptionClass) : Value :=
match ex with
| Error => VLiteral (Atom "Error"%string)
| Throw => VLiteral (Atom "Throw"%string)
| Exit => VLiteral (Atom "Exit"%string)
end.


(** Expression, 1st Value : cause, 2nd Value : further details *)
Definition Exception : Type := ExceptionClass * Value * Value.

Definition ErrorValue : Value := (VLiteral (Atom "error"%string)).
Definition ErrorExp : Expression := (ELiteral (Atom "error"%string)).
Definition ErrorPat : Pattern := PLiteral (Atom "error"%string).
Definition ttrue : Value := VLiteral (Atom "true").
Definition ffalse : Value := VLiteral (Atom "false").
Definition ok : Value := VLiteral (Atom "ok").

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


End Core_Erlang_Syntax.