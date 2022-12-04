Require Export ExpSyntax.


Require Import Hexadecimal Ascii String.

Import ListNotations.

(** Exception representation *)
Inductive ExceptionClass : Type :=
| Error | Throw | Exit.

(** Exception class to value converter *)
Definition exclass_to_value (ex : ExceptionClass) : ValueExpression :=
match ex with
| Error => VLit (Atom "error"%string)
| Throw => VLit (Atom "throw"%string)
| Exit => VLit (Atom "exit"%string)
end.

Definition pp_exception_class (cl : ExceptionClass) : string :=
match cl with
| Error => "error"
| Throw => "throw"
| Exit  => "exit"
end.


(** Helper definitions *)
Definition VEmptyMap : ValueExpression := VMap [].
Definition VEmptyTuple : ValueExpression := VTuple [].

Definition ErrorValue : ValueExpression := (VLit (Atom "error"%string)).
(* Definition ErrorExp2 : Expression := (ELit (Atom "error"%string)). *)
Definition ErrorExp : ValueExpression := (VLit (Atom "error"%string)).
Definition ErrorPat : Pattern := PLit(Atom "error"%string).
Definition ttrue : ValueExpression := VLit (Atom "true").
Definition ffalse : ValueExpression := VLit (Atom "false").
Definition ok : ValueExpression := VLit (Atom "ok").


(*
Definition pretty_print_literal (l : Literal) : string :=
match l with
 | Atom s => "'" ++ s ++ "'"
 | Integer x => NilZero.string_of_int (Z.to_int x)
end.

Fixpoint pretty_print_value (v : ValueExpression) : string :=
match v with
 | VNil => "[]"
 | VLit l => pretty_print_literal l
 | VClos env ext id vl e => "'closure'"
 | VCons vhd vtl => "[" ++ pretty_print_value vhd ++ "|" ++ pretty_print_value vtl ++ "]"
 | VTuple vl => "{" ++ 
    (fix print_list vl : string :=
      match vl with
       | []    => ""%string
       | [x]   => pretty_print_value x
       | x::xs => (pretty_print_value x ++ ","%string ++ print_list xs)%string
      end
    ) vl 
    ++ "}"
 | VMap l => "#{" ++ 
    (fix print_list vl : string :=
    match vl with
     | []         => ""%string
     | [(x, y)]   => (pretty_print_value x ++ "=>" ++ pretty_print_value y)%string
     | (x, y)::xs => (pretty_print_value x ++ "=>" ++ pretty_print_value y ++ "," ++ print_list xs)%string
    end
    ) l
    ++ "}"
end.
*)
(** Exception class, 1st Value : cause, 2nd Value : further details *)
Definition Exception : Type := ExceptionClass * ValueExpression * ValueExpression.

(*
Definition pp_exception (e : Exception) : string :=
match e with
| (class, reason, info) => "{" ++ pp_exception_class class  ++ "," ++
                                  pretty_print_value reason ++ "," ++
                                  pretty_print_value info   ++ "}"
end.
*)

(*
Definition pp_exception (e : Exception) : string :=
match e with
| (class, reason, info) => "{" ++ pp_exception_class class  ++ "," ++
                                  pretty_print_value reason ++ "," ++
                                  pretty_print_value info   ++ "}"
end.
*)

Definition badarith (v : ValueExpression) : Exception :=
  (Error, VLit (Atom "badarith"%string), v).
Definition badarg (v : ValueExpression) : Exception :=
  (Error, VLit (Atom "badarg"%string), v).
Definition undef (v : ValueExpression) : Exception :=
  (Error, VLit (Atom "undef"%string), v).
Definition badfun (v : ValueExpression) : Exception := 
  (Error,VLit (Atom "badfun"%string), v).
Definition badarity (v : ValueExpression) : Exception := 
  (Error,VLit (Atom "badarity"%string), v).
Definition if_clause : Exception := 
  (Error, VLit (Atom "if_clause"%string), ErrorValue).

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

(*
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