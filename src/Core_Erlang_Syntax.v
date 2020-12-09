From Coq Require ZArith.BinInt.
From Coq Require Strings.String.
From Coq Require Structures.OrderedTypeEx.
From Coq Require Numbers.DecimalString.

Module Syntax.

Export ZArith.BinInt.
Export Strings.String.
Export Lists.List.

Import Numbers.DecimalString.
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
| EValues (el : list SingleExpression)
| ESingle (e : SingleExpression)
with SingleExpression : Type :=
| ENil
| ELit    (l : Literal)
| EVar    (v : Var)
| EFunId  (f : FunctionIdentifier)
| EFun    (vl : list Var) (e : Expression)
| ECons   (hd tl : Expression)
| ETuple  (l : list Expression)
(** Initially: for built-in functions : *)
| ECall   (f : string)    (l : list Expression)
| EPrimOp (f : string)    (l : list Expression)
(** For function applications: *)
| EApp    (exp: Expression)     (l : list Expression)
| ECase   (e : Expression) (l : list ((list Pattern) * Expression * Expression))
| ELet    (l : list Var) (e1 e2 : Expression)
(** For sequencing: do expressions (ESeq) *)
| ESeq    (e1 e2 : Expression)
| ELetRec (l : list (FunctionIdentifier * ((list Var) * Expression))) (e : Expression)
| EMap    (l : list (Expression * Expression))
| ETry    (e1 : Expression) (vl1 : list Var) (e2 : Expression) (vl2 : list Var) (e2 : Expression).

Coercion ESingle : SingleExpression >-> Expression.
Notation "^ e" := (ESingle e) (at level 20).

Definition EEmptyMap : SingleExpression := EMap [].
Definition EEmptyTuple : SingleExpression := ETuple [].

(** In the future to simulate modules: *)
Inductive ErlFunction : Type := TopLevelFun (id : FunctionIdentifier) (vl : list Var) (body :  Expression).

Inductive ErlModule : Type := ErlMod (name : string) (fl : list ErlFunction).

Definition FunctionExpression : Type := list Var * Expression.

(** What expressions are in normal form 
    According to CE lang spec. value sequences cannot be nested
*)
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


(** Semantic domain *)
Definition ValueSequence := list Value.

(** Helper definitions *)
Definition VEmptyMap : Value := VMap [].
Definition VEmptyTuple : Value := VTuple [].

Definition ErrorValue : Value := (VLit (Atom "error"%string)).
Definition ErrorExp2 : Expression := ESingle (ELit (Atom "error"%string)).
Definition ErrorExp : SingleExpression := (ELit (Atom "error"%string)).
Definition ErrorPat : Pattern := PLit(Atom "error"%string).
Definition ttrue : Value := VLit (Atom "true").
Definition ffalse : Value := VLit (Atom "false").
Definition ok : Value := VLit (Atom "ok").

Definition pretty_print_literal (l : Literal) : string :=
match l with
 | Atom s => "'" ++ s ++ "'"
 | Integer x => NilZero.string_of_int (Z.to_int x)
end.


Fixpoint pretty_print_value (v : Value) : string :=
match v with
 | VNil => "[]"
 | VLit l => pretty_print_literal l
 | VClos env ext id vl e => ""
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

Local Definition l1 : Value := VCons ttrue VNil.
Local Definition l2 : Value := VCons ttrue ttrue.
Local Definition l3 : Value := VCons (VCons ttrue ttrue) ttrue.
Local Definition l4 : Value := VCons ttrue (VCons ttrue (VCons ttrue VNil)).
Local Definition l5 : Value := VCons ttrue (VCons ttrue ttrue).

Compute (pretty_print_value (VTuple [VLit (Integer 55); VLit (Integer 55); VLit (Integer 55); ttrue; ffalse])).
Compute (pretty_print_value (VMap [(VLit (Integer 55), VLit (Integer 55)); (VLit (Integer 56), ttrue); (ffalse, ffalse)])).
Compute pretty_print_value VNil.
Compute pretty_print_value l1.
Compute pretty_print_value l2.
Compute pretty_print_value l3.
Compute pretty_print_value l4.
Compute pretty_print_value l5.

(** Exception representation *)
Inductive ExceptionClass : Type :=
| Error | Throw | Exit.

(** Exception class to value converter *)
Definition exclass_to_value (ex : ExceptionClass) : Value :=
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
Definition undef (v : Value) : Exception :=
  (Error, VLit (Atom "undef"%string), v).
Definition badfun (v : Value) : Exception := 
  (Error,VLit (Atom "badfun"%string), v).
Definition badarity (v : Value) : Exception := 
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


Fixpoint degree (e : Expression) : degree_num :=
match e with
| EValues l => (Num (length l))
| ESingle e => single_degree e
end
with single_degree (e : SingleExpression) : degree_num :=
match e with
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


(* Compute which_degree (Num 4) (Num 5).
Compute which_degree (Num 4) (Num 4).
Compute which_degree Any (Num 4).
Compute which_degree (Num 4) Any.
Compute which_degree Any Any. *)

Definition valid_single_expression (e : SingleExpression) : bool :=
match e with
 | ENil => true
 | ELit l => true
 | EVar v => true
 | EFunId f => true
 | EFun vl e => match_degree (degree e) (Num 1)
 | ECons hd tl => match_degree (degree hd) (Num 1) && match_degree (degree tl) (Num 1)
 | ETuple l => fold_right (fun 'x r => andb r (match_degree (degree x) (Num 1))) true l
 | ECall f l => fold_right (fun 'x r => andb r (match_degree (degree x) (Num 1))) true l
 | EPrimOp f l => fold_right (fun 'x r => andb r (match_degree (degree x) (Num 1))) true l
 | EApp exp l => match_degree (degree exp) (Num 1) && 
                 fold_right (fun 'x r => andb r (match_degree (degree x) (Num 1))) true l
 | ECase e l => let maxim := fold_right max_degree Any (map degree (map snd l)) in 
                  fold_right (fun '(x, y, z) r => andb r (match_degree (degree z) maxim)) true l
 | ELet l e1 e2 => match_degree (degree e1) (Num (length l))
 | ESeq e1 e2 => match_degree (degree e1) (Num 1)
 | ELetRec l e => true
 | EMap l => true
 | ETry e1 vl1 e2 vl2 e3 => match_degree (degree e2) (degree e3)
end.

Definition valid_expression (e : Expression) : bool :=
match e with
 | EValues el => false
 | ESingle e => valid_single_expression e
end.

End Syntax.


Module Value_Notations.

Import Core_Erlang_Syntax.Syntax.
Import ListNotations.

Notation "' s '" := (VLit (Atom s)) (at level 1).
Notation "` i" := (VLit (Integer i)) (at level 1).
Notation "{ }" := (VTuple []) (at level 1).
Notation "{ x , .. , z }" := (VTuple (cons x .. (cons z nil) .. )) (at level 50).

Notation "@[ @]" := (VNil) (at level 1).
Notation "@[ a | b @]" := (VCons a b) (at level 50).

Notation "x ==> x'" := (@pair Value Value x x') (at level 70).
Notation "#{ }" := (VMap []) (at level 1).
Notation "#{ x , .. , z }" := (VMap (cons x .. (cons z nil) .. )) (at level 50).

(* 
Check VMap [].
Check VMap [(' "asd", ' "asd")].
Check VTuple [].
Check VTuple [' "asd"].
Check VTuple [' "bsc"; ' "asd"].
Check { ' "asd", ' "bsc" }. 
*)

(* Notation "< x , y , .. , z >" := (cons x (cons y .. (cons z nil) .. )) (at level 50). *)
(* 
Check VTuple [].

Check VCons '"asd" VNil.

Check VMap [('"asd", '"asd"); ('"asd", '"asd"); ('"asd", VLit (Integer 7))].
Check VCons '"asd" (VCons '"asd" VNil).

Check VTuple ['"asd"; '"asd"; '"asd"].
 *)
End Value_Notations.