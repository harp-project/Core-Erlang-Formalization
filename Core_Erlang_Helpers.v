Load Core_Erlang_Syntax.
From Coq Require Lists.List.


(* Additional helper functions *)
Module Core_Erlang_Helpers.


Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.

Import Core_Erlang_Syntax.

(* The equality of function signatures *)
Definition equal (v1 v2 : FunctionSignature) : bool :=
match v1, v2 with
| (fname1, num1), (fname2, num2) => eqb fname1 fname2 && Nat.eqb num1 num2
end.

(* Extended equality between functions and vars *)
Fixpoint uequal (v1 v2 : Var + FunctionSignature) : bool :=
match v1, v2 with
| inl s1, inl s2 => eqb s1 s2
| inr f1, inr f2 => equal f1 f2
| _, _ => false
end.

(* Get the vars from a function (Expression) *)
Definition get_vars (exp : Value) : (list Var) :=
match proj1_sig exp with
| EFunction (FunDecl vl e) =>  vl
| _ => []
end.

(* Get the body of a function (Expression) *)
Definition get_fun_exp (exp : Value) : Expression :=
match proj1_sig exp with
| EFunction (FunDecl vl e) => e
| _ => ErrorExp
end.

Section list_proofs.

Variable A : Type.

Lemma list_length_helper_refl : forall l : list A, length l =? length l = true.
Proof.
  induction l.
  * auto.
  * auto.
Qed.

Lemma list_length_helper : forall l l' : list A, length l = length l' -> length l =? length l' = true.
Proof.
  intros. induction l.
  * inversion H. auto.
  * inversion H. simpl. apply list_length_helper_refl.
Qed.

Lemma element_exist : forall n (l : list A), length l = S n -> exists e l', l = e::l'.
Proof.
  intros. destruct l.
  * inversion H.
  * apply ex_intro with a. apply ex_intro with l. reflexivity.
Qed.

(* Lemma list_length : forall n (l : list A), length l = n -> n > 0 -> exists e l', l = e::l'.
Proof.
  intro n. induction n.
  * intros. inversion H0.
  * intros. inversion H.
Qed.*)

End list_proofs.

Section double_lists.

Variable A : Type.
Variable B: Type.

(* Get the second components of a product list *)
Fixpoint first (l : list (A * B)) : list A := fst (split l).

(* Get the first components of a product list *)
Fixpoint second (l : list (A * B)) : list B := snd (split l).

(* Fixpoint make_double_list (f : list A) (s : list B) : list (A * B) := combine f s. *)
(* if Nat.eqb (List.length f) (List.length s) then 
  match f, s with
  | f1::fs, s1::ss => (f1,s1)::(make_double_list fs ss)
  | [], [] => []
  | _, _ => []
  end
else []. *)

(* Lemma double_list_helper : forall (e:A) (e':B) (l: list A) (l': list B), List.length l = List.length l' ->  List.In (e, e') (make_double_list l l') -> List.In e l /\ List.In e' l'.
Proof.
  induction l.
  * intros. destruct l'.
    - inversion H0.
    - simpl in H0. inversion H0.
  * destruct l'.
    - intros. inversion H0.
    - intros. simpl in H0. inversion H. subst. rewrite H2 in H0. rewrite list_length_helper in H0. inversion H0.
      + inversion H1. subst. intuition.
      + pose (IHl l' H2). intuition. 
      + reflexivity.
Qed. *)

(* Lemma double_list_helper_index : forall e e' exps exps', length exps = length exps' -> In (e, e') (make_double_list exps exps') -> exists i, nth_error exps i = Some e /\ nth_error exps' i = Some e'.
Proof.
  induction exps.
  * intros. destruct exps'.
    - inversion H0.
    - simpl in H0. inversion H0.
  * intros. destruct exps'.
    - inversion H0.
    - simpl in H0. inversion H. subst. rewrite H2 in H0. rewrite list_length_helper in H0. inversion H0.
      + inversion H1. apply ex_intro with 0. simpl. intuition.
      + pose (IHexps exps' H2 H1). inversion e0. apply ex_intro with (S x). simpl. assumption.
      + reflexivity.
Qed. *)

End double_lists.

Check proj1_sig.

Fixpoint valuelist_to_exp (l : list Value) : list Expression :=
match l with
| [] => []
| x::xs => (proj1_sig x)::(valuelist_to_exp xs)
end.

(* The matching function of two literals *)
Fixpoint match_literals (l l' : Literal) : bool :=
match l, l' with
| Atom s, Atom s' => eqb s s'
| Integer x, Integer x' => Z.eqb x x'
| EmptyList, EmptyList => true
| EmptyTuple, EmptyTuple => true
| _, _ => false
end.

Compute proj2_sig (exist _ (EList ErrorExp (ELiteral EmptyList)) (VJ_List _ _ _ _)).

(* The matching function to match Expressions *)
(* Fixpoint match_expression_to_pattern (e : Value) (p : Pattern) : bool :=
match p with
| PVar v => true (* every e matches to a pattern variable *)
| PLiteral l => match proj1_sig e with
  | ELiteral l' => match_literals l l'
  | _ => false
  end
| PList hd tl => match (proj2_sig e) with
  | VJ_List hd' tl' p1 p2 => (match_expression_to_pattern (exist _ hd' p1) hd) && (match_expression_to_pattern (exist _ tl' p2) tl)
  | _ => false
  end
| _ => false(*PTuple t => match e with
  | ETuple exps => match_elements exps t
  | _ => false
  end
end
with match_elements (exps : list Expression) (t : Tuple) : bool :=
  match exps, t with
  | [], TNil => true
  | e::es, TCons p ps => (match_expression_to_pattern e p) && (match_elements es ps)
  | _, _ => false
  end*)
end
.

(* Extended matching function, results the variable binding list *)
Fixpoint match_expression_bind_pattern (e : Value) (p : Pattern) : list (Var * Expression) :=
match p with
| PVar v => [(v, e)] (* every e matches to a pattern variable *)
| PLiteral l => match e with
  | ELiteral l' => []
  | _ => []
  end
| PList hd tl => match e with
  | EList hd' tl' => (match_expression_bind_pattern hd' hd) ++ (match_expression_bind_pattern tl' tl)
  | _ => []
  end
| PTuple t => match e with
  | ETuple exps => match_and_bind_elements exps t
  | _ => []
  end
end
with match_and_bind_elements (exps : list Expression) (t : Tuple) : list (Var * Expression) :=
  match exps, t with
  | [], TNil => []
  | e::es, TCons p ps => (match_expression_bind_pattern e p) ++ (match_and_bind_elements es ps) (* Each variable can occur only once in a pattern according to the Core-Erlang ducumentation *)
  | _, _ => []
  end
.

(* Get the matching clause to an Expression *)
Fixpoint match_clauses (e : Value) (cls : list Clause) : option (Expression * Expression * list (Var * Value)) :=
match cls with
| [] => None
| ((CConstructor p g exp)::xs) => if match_expression_to_pattern e p then Some (g, exp, (match_expression_bind_pattern e p)) else match_clauses e xs
end
.


(* Examples *)
Compute match_expression_to_pattern (ELiteral (Atom "alma"%string)) (PVar "X"%string).
Compute match_expression_to_pattern (ELiteral (Atom "alma"%string)) (PLiteral (Atom "alma"%string)).
Compute match_expression_to_pattern (ELiteral (Atom "alma"%string)) (PLiteral EmptyTuple).
Compute match_expression_to_pattern (ETuple [ELiteral (Atom "alma"%string) ; ELiteral (Integer 1)]) (PVar "X"%string).

Compute match_expression_bind_pattern (ELiteral (Atom "alma"%string)) (PVar "X"%string).
Compute match_expression_bind_pattern (ETuple [ELiteral (Atom "alma"%string) ; ELiteral (Integer 1)]) (PTuple [[PVar "X"%string ; PVar "X"%string]]).*)

End Core_Erlang_Helpers.