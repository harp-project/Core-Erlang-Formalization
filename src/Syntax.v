From Coq Require ZArith.BinInt.
From Coq Require Strings.String.
From Coq Require Export FunctionalExtensionality PropExtensionality.

(*Require Import Utf8.*)

Export ZArith.BinInt.
Export Strings.String.
Export Lists.List.
Require Export Coq.Structures.OrderedType.
Require Export Coq.micromega.Lia
               Coq.Lists.List
               Coq.Arith.PeanoNat.

From CoreErlang Require Export Basics.

Import ListNotations.


Inductive Lit : Set :=
| Atom (s: string)
| Integer (x : Z)
(* | Float (q : R) *).

Coercion Atom : string >-> Lit.
Coercion Integer : Z >-> Lit.

Inductive Pat : Set :=
| PVar
| PLit (l : Lit)
| PCons  (hd tl : Pat)
| PTuple (l : list Pat)
| PMap (l : list (Pat * Pat))
| PNil.

Definition FunId : Set := nat * nat.
Definition Var : Set := nat.

Inductive Exp : Set :=
| VVal (e : Val)
| EExp (e : NonVal)

with Val: Set := 
| VNil
| VLit    (l : Lit)
| VCons   (hd tl : Val)
| VTuple  (l : list Val)
| VMap    (l : list (Val * Val))
(* | VValues (el : list ValExp) *)
(* VValues will need to be seperate to avoid VValues in VValues. *)
| VVar    (n : Var)
| VFunId  (n : FunId)
(* Function normalforms: closures. These values contain the body, formal parameter count   *)
| VClos   (ext : list (nat * nat * Exp))
          (id : nat) (* Function reference number *)
          (params : nat) (* Parameter count *)
          (e : Exp)
(* Scoping vl + length ext *)

with NonVal : Set :=
| EFun    (vl : nat) (e : Exp) (* One step reduction *)
| EValues (el : list Exp)
| ECons   (hd tl : Exp)
| ETuple  (l : list Exp)
| EMap    (l : list (Exp * Exp))
| ECall   (m f : string) (l : list Exp)
| EPrimOp (f : string)    (l : list Exp)
| EApp    (exp: Exp)     (l : list Exp)
| ECase   (e : Exp) (l : list ((list Pat) * Exp * Exp))
| ELet    (l : nat) (e1 e2 : Exp)
| ESeq    (e1 e2 : Exp)

| ELetRec (l : list (nat * Exp)) (e : Exp) (* One step reduction *)
| ETry    (e1 : Exp) (vl1 : nat) (e2 : Exp) (vl2 : nat) (e3 : Exp)
.

Coercion EExp : NonVal >-> Exp.
Notation "` v" := (VVal v) (at level 11).
Notation "° n" := (EExp n) (at level 11).

(** Shorthands: *)
Definition VEmptyMap : Val := VMap [].
Definition VEmptyTuple : Val := VTuple [].
Definition EEmptyMap : Exp := EMap [].
Definition EEmptyTuple : Exp := ETuple [].

Definition ErrorVal : Val := (VLit (Atom "error"%string)).
(* Definition ErrorExp2 : Expression := (ELit (Atom "error"%string)). *)
Definition ErrorExp : Val := (VLit (Atom "error"%string)).
Definition ErrorPat : Pat := PLit(Atom "error"%string).
Definition ttrue : Val := VLit (Atom "true").
Definition ffalse : Val := VLit (Atom "false").
Definition ok : Val := VLit (Atom "ok").

(** Exception representation *)
Inductive ExcClass : Type :=
| Error | Throw | Exit.

(** Exception class to value converter *)
Definition exclass_to_value (ex : ExcClass) : Val :=
match ex with
| Error => VLit (Atom "error"%string)
| Throw => VLit (Atom "throw"%string)
| Exit => VLit (Atom "exit"%string)
end.

(** Exception class, 1st Value : cause, 2nd Value : further details *)
Definition Exception : Type := ExcClass * Val * Val.

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

Definition ValSeq := list Val.

Inductive Redex : Type :=
| RExp (e : Exp)
| RValSeq (vs : ValSeq)
| RExc (e : Exception)
| RBox.

Definition convert_to_closlist (l : list (nat * nat * Exp)) : (list Val) :=
  map (fun '(id,vc,e) => (VClos l id vc e)) l.
