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
| Atom (s: string) (* TODO: How could we define these? Atom vs string, mindkettő string belső reprezentációval? Atomok száma véges... Később id lehetne a string helyett *)
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
| PTuple (t : Tuple)
with Tuple : Type :=
| TNil 
| TCons (hd : Pattern) (tl : Tuple).

Notation "[[ ]]" := TNil (format "[[ ]]").
Notation "[[ x ]]" := (TCons x TNil).
Notation "[[ x ; y ; .. ; z ]]" := (TCons x (TCons y .. (TCons z TNil) ..)).

Definition FunctionSignature : Type := string * nat.

Inductive Expression : Type :=
| ELiteral (l : Literal)
| EVar     (v : Var)
| EFunction (f : Fun)
| EList  (hd tl : Expression)
| ETuple (l : list Expression) (* maybe vector is more appropriate, or * (product) *)
(* | ETuple            (n: nat) (l : t Expression n)  (* vectorial implementation for tuples *) *)
| ECall  (f: FunctionSignature)     (l : list Expression) (* For built-in functions and primitive operations *)
| EApply (f: Var)     (l : list Expression)
| EApplyTopLevel (f : FunctionSignature) (l : list Expression)
| ECase  (e: Expression)            (l : list Clause)
| ELet   (s : list Var)             (el : list Expression) (e : Expression)
| ELetrec (fnames : list FunctionSignature) (fs : list Fun) (e : Expression)
| EMap   (kl vl : list Expression)   (* maybe map would be better *)
(* | ETry   (e ex : Expression) (v1 v2 : Var) *)
 with Clause : Type :=
 | CCons (p: Pattern)   (guard e : Expression)
 with Fun : Type := (* Restriction because of the Letrec -> here only functions can be defined *)
 | FunDecl (vl : list Var) (e : Expression).


Inductive ErlFunction : Type := TopLevelFun (n : FunctionSignature) (f : Fun).

Inductive ErlModule : Type := ErlMod (a : string) (fl : list ErlFunction).

(* What should we call a value *)
Reserved Notation "t 'val'" (at level 1).
Inductive ValueJudgement : Expression -> Prop :=
| VJ_Literal e : (ELiteral e) val
| VJ_Function f : (EFunction f) val
| VJ_List hd tl: hd val -> tl val -> (EList hd tl) val
| VJ_Tuple (exprs : list Expression) : (forall exp : Expression, In exp exprs -> exp val) -> (ETuple exprs) val
| VJ_Map kl vl : (forall exp : Expression, In exp vl -> exp val) -> (EMap kl vl) val
where "t 'val'" := (ValueJudgement t).

Fixpoint value_fix (e : Expression) : bool :=
match e with
 | ELiteral l => true
 | EVar v => false
 | EFunction f => true
 | EList hd tl => value_fix hd && value_fix tl
 | ETuple l => fold_right andb false (map value_fix l)
 | EMap kl vl => fold_right andb false (map value_fix kl) && fold_right andb false (map value_fix vl)
 | _ => false
end
.

(*Section value_induct.

  Variable P : Expression -> Prop.

  Hypothesis VJ_lit_case : 

End value_induct.*)

Definition Value : Type := { e : Expression | e val }.
Notation "e p: t" := (exist _ e t) (at level 45).

(* To describe faults *)

Definition ErrorValue : Value := exist _ (ELiteral (Atom "error"%string)) (VJ_Literal _).
Definition ErrorExp : Expression := (ELiteral (Atom "error"%string)).
Definition ErrorPat : Pattern := PLiteral (Atom "error"%string).
Definition tt : Expression := ELiteral (Atom "true").
Definition ff : Expression := ELiteral (Atom "false").

End Core_Erlang_Syntax.