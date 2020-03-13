From Coq Require ZArith.BinInt.
From Coq Require Reals.
From Coq Require Init.Nat.
From Coq Require Strings.String.

Module Core_Erlang_Syntax.

Import ZArith.BinInt.
Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.

Definition Var : Type := string.

Inductive Literal : Type :=
| Atom (s: string) (* TODO: How could we define these? Atom vs string, finite number of Atoms... id vs string *)
| Integer (x : Z)
(* | Float (q : R) *)
| EmptyList
| EmptyTuple
| EmptyMap.

(* Patterns are not expressions, because there are expressions that are not patterns and patters that are not expressions (these are not implemented yet) *)
Inductive Pattern : Type :=
| PVar     (v : Var)
| PLiteral (l : Literal)
| PList  (hd tl : Pattern)
| PTuple (l : list Pattern).

Definition FunctionSignature : Type := string * nat.

Inductive Expression : Type :=
| ELiteral (l : Literal)
| EVar     (v : Var)
| EFunSig  (f : FunctionSignature)
| EFun     (vl : list Var) (e : Expression)
| EList  (hd tl : Expression)
| ETuple (l : list Expression) (* maybe vector is more appropriate, or * (product) *)
(* | ETuple            (n: nat) (l : t Expression n)  (* vectorial implementation for tuples *) *)
| ECall  (f: string)     (l : list Expression) (* For built-in functions and primitive operations *)
| EApply (exp: Expression)     (l : list Expression)
| ECase  (e: Expression)            (l : list Clause)
| ELet   (s : list Var)             (el : list Expression) (e : Expression)
| ELetrec (fnames : list FunctionSignature) (fs : list ((list Var) * Expression)) (e : Expression)
| EMap   (kl vl : list Expression)   (* maybe map would be better *)
(* | ETry   (e ex : Expression) (v1 v2 : Var) *)
 with Clause : Type :=
 | CCons (p: Pattern)   (guard e : Expression).


Inductive ErlFunction : Type := TopLevelFun (n : FunctionSignature) (f : ((list Var) * Expression)).

Inductive ErlModule : Type := ErlMod (a : string) (fl : list ErlFunction).

(* What should we call a value *)
Inductive Value : Type :=
| VLiteral (l : Literal)
| VClosure (env : list ((Var + FunctionSignature) * Value) + (FunctionSignature)) (vl : list Var) (e : Expression)
| VList (vhd vtl : Value)
| VTuple (vl : list Value)
| VMap (kl vl : list Value).

(* Fixpoint is_expression_value (e : Expression) : bool :=
match e with
 | ELiteral l => true
 | EVar v => false
 | EFunName f => false
 | EFun vl e => false
 | EList hd tl => is_expression_value hd && is_expression_value tl
 | ETuple l => fold_right andb true (map is_expression_value l)
 | ECall f l => false
 | EApply exp l => false
 | ECase e l => false
 | ELet s el e => false
 | ELetrec fnames fs e => false
 | EMap kl vl => fold_right andb true (map is_expression_value kl) && fold_right andb true (map is_expression_value vl)
end
. *)

Definition ErrorValue : Value := (VLiteral (Atom "error"%string)).
Definition ErrorExp : Expression := (ELiteral (Atom "error"%string)).
Definition ErrorPat : Pattern := PLiteral (Atom "error"%string).
Definition ttrue : Value := VLiteral (Atom "true").
Definition ffalse : Value := VLiteral (Atom "false").
Definition ok : Value := VLiteral (Atom "ok").

(* Fixpoint value_to_expression (v : Value) : Expression :=
match v with
 | VLiteral l => ELiteral l
 | VClosure env vl e => ErrorExp
 | VList v1 v2 => EList (value_to_expression v1) (value_to_expression v2)
 | VTuple vl => ETuple (map value_to_expression vl)
 | VMap kl vl => EMap (map value_to_expression kl) (map value_to_expression vl)
end. *)


End Core_Erlang_Syntax.