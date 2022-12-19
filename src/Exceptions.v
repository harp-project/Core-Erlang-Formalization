From CoreErlang Require Export Syntax.

Import ListNotations.

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

(*
Inductive degree_num : Set :=
| Num (n : nat)
| Any.

Definition max_degree (d1 d2 : degree_num) : degree_num :=
match d1, d2 with
| Num n1, Num n2 => Num (max n1 n2)
| Any, Num n => Num n
| Num n, Any => Num n
| Any, Any => Any
end.


Fixpoint degree (e : Expression) : degree_num :=
match e with
| EValues l => (Num (length l))
(* | ESingle e => single_degree e
end
with single_degree (e : SingleExpression) : degree_num :=
match e with *)
 | ENil => Num 1
 | ELit l => Num 1
 | EVar v => Num 1
 | EFunId f => Num 1
 | EFun vl e => Num 1
 | ECons hd tl => Num 1
 | ETuple l => Num 1
 | ECall f l => Num 1
 | EPrimOp f l => Any
 | EApp exp l => Num 1
 | ECase e l => fold_right (fun '(a, b, c) r => max_degree r (degree c)) Any l
 | ELet l e1 e2 => degree e2
 | ESeq e1 e2 => degree e2
 | ELetRec l e => degree e
 | EMap l => Num 1
 | ETry e1 vl1 e2 vl2 e3 => max_degree (degree e2) (degree e3)
end.

Definition match_degree (d1 d2 : degree_num) : bool :=
match d1, d2 with
| Num n1, Num n2 => Nat.eqb n1 n2
| _, _ => true
end.

(* Compute match_degree (Num 4) (Num 5). *)

Definition which_degree (d1 d2 : degree_num) : option degree_num :=
match d1, d2 with
| Num n1, Num n2 => if Nat.eqb n1 n2 then Some (Num n1) else None
| Num n, Any => Some (Num n)
| Any, Num n => Some (Num n)
| Any, Any => Some Any
end.
*)