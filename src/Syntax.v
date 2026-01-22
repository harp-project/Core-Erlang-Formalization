(**
  This file includes the abstract syntax of Core Erlang. It defines a number
  of notations and shorthands on top of this syntax. The syntax is defined in
  nameless variable representation.
 *)
(* Check CoreErlang. *)

From Stdlib Require ZArith.BinInt.
From Stdlib Require Strings.String.
From Stdlib Require Export FunctionalExtensionality.

(*Require Import Utf8.*)

Export ZArith.BinInt.
Export Strings.String.
Export Lists.List.
Require Export Stdlib.Structures.OrderedType.
Require Export Stdlib.micromega.Lia
               Stdlib.Lists.List
               Stdlib.Arith.PeanoNat.

From CoreErlang Require Export Basics.

Import ListNotations.

(** We use nats for process identifiers for simplicity. *)
Definition PID : Set := nat.

(** Currently, the only literals are integers and atoms. *)
Inductive Lit : Set :=
| Atom (s: string)
| Integer (x : Z)
(* | Float (q : R) *).

Coercion Atom : string >-> Lit.
Coercion Integer : Z >-> Lit.

(** Patterns of the language are its basic data structures (lists, tuples, maps),
    literals, and pattern variables. PIDs are _not_ patterns. Due to the
    nameless variable representation, pattern variables don't have a name,
    neither an index - their index is their position relative to eachother in
    an inorder traversal of the pattern. *)
Inductive Pat : Set :=
| PVar
(* | PPid (p : PID) *)
| PLit (l : Lit)
| PCons  (hd tl : Pat)
| PTuple (l : list Pat)
| PMap (l : list (Pat * Pat))
| PNil.

Definition FunId : Set := nat * nat.
Definition Var : Set := nat.

(** The following type represents Core Erlang expressions and values. It is
    mutually inductive, since function values include expressions as their body,
    moreover in a small-step semantics it is advantageos to have values as
    subexpressions. *)
Inductive Exp : Set :=
| VVal (e : Val)
| EExp (e : NonVal)

with Val: Set := 
| VNil
| VLit    (l : Lit)
| VPid    (p : PID)
| VCons   (hd tl : Val)
| VTuple  (l : list Val)
| VMap    (l : list (Val * Val))
(** Value sequences are not included here, since they cannot be nested *)
| VVar    (n : Var)
| VFunId  (n : FunId)
(** Function normalforms: closures. These values contain:
     - a list of functions that can be applied recursively by the body expression
     - a function reference number
     - formal parameter count
     - the body *)
| VClos   (ext : list (nat * nat * Exp))
          (id : nat) (* Function reference number *)
          (params : nat) (* Parameter count *)
          (e : Exp)

with NonVal : Set :=
| EFun    (vl : nat) (e : Exp)
| EValues (el : list Exp)
| ECons   (hd tl : Exp)
| ETuple  (l : list Exp)
| EMap    (l : list (Exp * Exp))
| ECall   (m f : Exp) (l : list Exp)
| EPrimOp (f : string)    (l : list Exp)
| EApp    (exp: Exp)     (l : list Exp)
| ECase   (e : Exp) (l : list ((list Pat) * Exp * Exp))
| ELet    (l : nat) (e1 e2 : Exp)
| ESeq    (e1 e2 : Exp)

| ELetRec (l : list (nat * Exp)) (e : Exp) (* One step reduction *)
| ETry    (e1 : Exp) (vl1 : nat) (e2 : Exp) (vl2 : nat) (e3 : Exp)
(** In OTP 23.0, receive expressions were removed from the language primitives,
    thus we don't need any other expression to express concurrency. Message
    receipts are expressed with primitive operations.
 *)
.

Coercion EExp : NonVal >-> Exp.
Notation "˝ v" := (VVal v) (at level 11).
Notation "° n" := (EExp n) (at level 11).

Definition inf :=
  ELetRec
    [(0, °EApp (˝VFunId (0, 0)) [])]
    (EApp (˝VFunId (0, 0)) []).

(** Shorthands: *)
Definition VEmptyMap : Val := VMap [].
Definition VEmptyTuple : Val := VTuple [].
Definition EEmptyMap : Exp := EMap [].
Definition EEmptyTuple : Exp := ETuple [].

Definition ErrorVal : Val := (VLit (Atom "error"%string)).
(* Definition ErrorExp2 : Expression := (ELit (Atom "error"%string)). *)
Definition ErrorExp : Val := (VLit (Atom "error"%string)).
Definition ErrorPat : Pat := PLit(Atom "error"%string).
Notation "'ttrue'"        := (VLit "true"%string).
Notation "'ffalse'"       := (VLit "false"%string).
Notation "'ok'"           := (VLit "ok"%string).
Notation "'link'"         := (VLit "link"%string).
Notation "'spawn'"        := (VLit "spawn"%string).
Notation "'spawn_link'"   := (VLit "spawn_link"%string).
Notation "'unlink'"       := (VLit "unlink"%string).
Notation "'exit'"         := (VLit "exit"%string).
Notation "'send'"         := (VLit "!"%string).
Notation "'normal'"       := (VLit "normal"%string).
Notation "'kill'"         := (VLit "kill"%string).
Notation "'killed'"       := (VLit "killed"%string).
Notation "'EXIT'"         := (VLit "EXIT"%string).
Notation "'self'"         := (VLit "self"%string).
Notation "'ok'"           := (VLit "ok"%string).
Notation "'process_flag'" := (VLit "process_flag"%string).
Notation "'trap_exit'"    := (VLit "trap_exit"%string).
Notation "'erlang'"       := (VLit "erlang"%string).
Notation "'infinity'"     := (VLit "infinity"%string).


(** Exception classes in Erlang *)
Inductive ExcClass : Set :=
| Error | Throw | Exit.

(** Exception class to value conversion *)
Definition exclass_to_value (ex : ExcClass) : Val :=
match ex with
| Error => VLit (Atom "error"%string)
| Throw => VLit (Atom "throw"%string)
| Exit => VLit (Atom "exit"%string)
end.

(** Exceptions are triples:
    - Exception class
    - 1st Value : cause
    - 2nd Value : further details *)
Definition Exception : Set := ExcClass * Val * Val.

(** Commonly used exceptions: *)
Definition badarith (v : Val) : Exception :=
  (Error, VLit (Atom "badarith"%string), v).
Definition badarg (v : Val) : Exception :=
  (Error, VLit (Atom "badarg"%string), v).
Definition undef (v : Val) : Exception :=
  (Error, VLit (Atom "undef"%string), v).
Definition badfun (v : Val) : Exception := 
  (Error,VLit (Atom "badfun"%string), v).
Definition badarity (v : Val) : Exception := 
  (Error,VLit (Atom "badarity"%string), v).
Definition if_clause : Exception := 
  (Error, VLit (Atom "if_clause"%string), ErrorVal).
Definition timeout_value v : Exception :=
  (Error, VLit (Atom "timeout_value"), v).

(** The result of the evaluation is a value sequence (or exception). *)
Definition ValSeq := list Val.

(** Redexes are used in the frame stack semantics (which is a reduction-style
    semantics). `RBox` is used to express parameter list evaluation (i.e., in
    case of tuples, maps, applications, calls, primops) without code
    duplication.
  *)
Inductive Redex : Set :=
| RExp (e : Exp)
| RValSeq (vs : ValSeq)
| RExc (e : Exception)
| RBox.

(** Converting a list of functions into a list of closures. *)
Definition convert_to_closlist (l : list (nat * nat * Exp)) : (list Val) :=
  map (fun '(id,vc,e) => (VClos l id vc e)) l.
