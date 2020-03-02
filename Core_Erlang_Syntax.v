From Coq Require ZArith.BinInt.
From Coq Require Reals.
From Coq Require Init.Nat.
From Coq Require Strings.String.
From Coq Require FSets.FMapList.
Require Import Omega.

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
| ECase  (e: Expression)            (pl : list Pattern) (* The case pattern list *)
                                    (gl : list Expression) (* guard list *)
                                    (bl : list Expression) (* body list *)
| ELet   (s : list Var)             (el : list Expression) (e : Expression)
| ELetrec (fnames : list FunctionSignature) (varlists : list (list Var)) (bodylists : list Expression) (e : Expression)
| EMap   (kl vl : list Expression)   (* maybe map would be better *)
| ETry   (e e1 e2 : Expression) (v1 vex1 vex2 vex3 : Var).


Inductive ErlFunction : Type := TopLevelFun (n : FunctionSignature) (f : ((list Var) * Expression)).

Inductive ErlModule : Type := ErlMod (a : string) (fl : list ErlFunction).

(* Scheme Equality for Expression. *)
Section Prod_Eq_Dec.

Variables A B : Type.

Hypothesis A_eq_dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}.
Hypothesis B_eq_dec : forall b1 b2 : B, {b1 = b2} + {b1 <> b2}.

Proposition prod_eq_dec : forall p1 p2 : A * B, {p1 = p2} + {p1 <> p2}.
Proof.
  set (eq1 := A_eq_dec).
  set (eq2 := B_eq_dec).
  decide equality.
Qed.

End Prod_Eq_Dec.

Section Equalities.

Scheme Equality for Literal.

Fixpoint Pattern_eq_dec (p1 p2 : Pattern) : {p1 = p2} + {p1 <> p2}.
Proof.
  set (Pattern_list_eq_dec := list_eq_dec Pattern_eq_dec).
  set (Pattern_var_eq_dec := string_dec).
  set (Pattern_literal_eq_dec := Literal_eq_dec).
  decide equality.
Qed.

Fixpoint Expression_eq_dec (e1 e2 : Expression) {struct e1} : {e1 = e2} + {e1 <> e2}.
Proof.
  set (var_eq_dec := string_dec).
  set (literal_eq_dec := Literal_eq_dec).
  set (pattern_eq_dec := Pattern_eq_dec).
  set (explist_eq_dec := list_eq_dec Expression_eq_dec).
  set (varlist_eq_dec := list_eq_dec string_dec).
  
  (* for function signatures: *)
  set (funsig_eq_dec := prod_eq_dec string nat string_dec Nat.eq_dec).
  
  set (patlist_eq_dec := list_eq_dec pattern_eq_dec).
  (* for letrec *)
  set (listvarexp_eq_dec := list_eq_dec (prod_eq_dec (list Var) Expression
                                                    (list_eq_dec string_dec) Expression_eq_dec)).
  (* for fnames *)
  set (listfunsig_eq_dec := list_eq_dec funsig_eq_dec).
  set (listlistvar_eq_dec := list_eq_dec (list_eq_dec string_dec)).
  decide equality.
Qed.


End Equalities.

(* What should we call a value *)
Inductive Value : Type :=
| VLiteral (l : Literal)
| VClosure (env : list ((Var + FunctionSignature) * Value) + (FunctionSignature)) (vl : list Var) (e : Expression)
| VList (vhd vtl : Value)
| VTuple (vl : list Value)
| VMap (kl vl : list Value).

Inductive ExceptionClass : Type :=
| Error | Throw | Exit.

Fixpoint make_value_from_ex_class (ex : ExceptionClass) : Value :=
match ex with
| Error => VLiteral (Atom "Error"%string)
| Throw => VLiteral (Atom "Throw"%string)
| Exit => VLiteral (Atom "Exit"%string)
end.


(* Expression : cause, Value : further details*)
Definition Exception : Type := ExceptionClass * Value * Value.

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

Definition badarith : Exception :=  (Error, VLiteral (Atom "badarith"%string), ErrorValue).
Definition badarg : Exception :=  (Error, VLiteral (Atom "badarg"%string), ErrorValue).
Definition novar : Exception :=  (Throw, VLiteral (Atom "Variable error"%string), ErrorValue).
Definition undef : Exception :=  (Error, VLiteral (Atom "undefined function"%string), ErrorValue).
Definition noclosure : Exception := (Error,VLiteral (Atom "not a closure"%string), ErrorValue).
Definition args : Exception := (Error,VLiteral (Atom "Not enough/too many arguments"%string), ErrorValue).

(*   From Equations Require Import Equations.

Section correct_pattern_rect.
  
  Variables (P : Pattern -> Type) (Q : list Pattern -> Type).

  Hypotheses
  (H1 : forall v : Var, P (PVar v))
  (H2 : forall l : Literal, P (PLiteral l))
  (H3 : forall hd tl : Pattern, P hd -> P tl -> P (PList hd tl))
  (H4 : forall l : list Pattern, Q l -> P (PTuple l))
  (H'0 : Q [])
  (H'1 : forall p : Pattern, P p ->
           forall l : list Pattern, Q l -> Q (p::l))
  .
  
  Equations pat_ind (p : Pattern) : P p :=
  { pat_ind (PVar v) := H1 v;
    pat_ind (PLiteral l) := H2 l;
    pat_ind (PList hd tl) := H3 hd tl (pat_ind hd) (pat_ind tl);
    pat_ind (PTuple l) := H4 l (pat_ind_list l) }
  where pat_ind_list (l : list Pattern) : Q l :=
  { pat_ind_list [] := H'0;
    pat_ind_list (t::ts) := H'1 t (pat_ind t) ts (pat_ind_list ts) }.

  Fixpoint Pattern_rect (p : Pattern) : P p :=
  match p with
   | PVar v => H1 v
   | PLiteral l => H2 l
   | PList hd tl => H3 hd tl (Pattern_rect hd) (Pattern_rect tl)
   | PTuple l => H4 l
                    ((fix l_ind (l' : list Pattern) : Q l' :=
                         match l' with
                         | [] => H'0
                         | x::xs => H'1 x (Pattern_rect x) xs (l_ind xs)
                         end) l)
  end.


End correct_pattern_rect.

Section Pattern_ind.

  Variable P : Pattern -> Prop.

  Hypothesis P_PVar : forall v : Var, P (PVar v).
  Hypothesis P_PLit : forall l : Literal, P (PLiteral l).
  Hypothesis P_PList : forall hd tl : Pattern, P hd -> P tl -> P (PList hd tl).
  Hypothesis P_PTuple : forall l : list Pattern, List.Forall P l -> P (PTuple l).

  Definition Pattern_ind (p : Pattern) : P p :=
    Pattern_rect P (List.Forall P) P_PVar P_PLit P_PList P_PTuple 
                (List.Forall_nil _)
                (fun t Pt l Pl => List.Forall_cons _ Pt Pl) p.

End Pattern_ind.

  (* Theorem Pattern_eq_dec_original : forall p1 p2 : Pattern, {p1 = p2} + {p1 <> p2}.
  Proof.
    induction p1 using Pattern_ind.
  Qed. *)

  Theorem Pattern_eq_dec : forall p1 p2 : Pattern, p1 = p2 \/ p1 <> p2.
  Proof.
    induction p1 using Pattern_ind; induction p2 using Pattern_ind.
    all: try solve [try (right; unfold not; intros; try(inversion H); try(inversion H0))].
    * destruct (string_dec v v0); subst.
      - left. reflexivity.
      - right. unfold not in *. intros. apply n. inversion H. reflexivity.
    * destruct (Literal_eq_dec l l0).
      - left. rewrite e. reflexivity.
      - right. unfold not. intros. inversion H. exact (n H1).
    * pose (IHp1_1 p2_1). pose (IHp1_2 p2_2). destruct o.
      - destruct o0.
        + subst. left. reflexivity.
        + right. unfold not. intros. inversion H1. exact (H0 H4).
      - right. unfold not. intros. inversion H0. exact (H H2).
    * pose (list_eq_dec).
  Qed.

End EqualitySchemes. *)


End Core_Erlang_Syntax.