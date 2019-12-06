Load Core_Erlang_Syntax.
From Coq Require Lists.List.
From Coq Require Lists.ListSet.


(* Additional helper functions *)
Module Core_Erlang_Helpers.


Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.
Import Lists.ListSet.

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
(* Fixpoint match_expression_to_pattern (e : Expression) (p : Pattern) : bool :=
match p with
| PVar v => true (* every e matches to a pattern variable *)
| PLiteral l => match e with
  | ELiteral l' => match_literals l l'
  | _ => false
  end
| PList hd tl => match e with
  | EList hd' tl' => (match_expression_to_pattern hd' hd) && (match_expression_to_pattern tl' tl)
  | _ => false
  end
| PTuple t => match e with
  | ETuple exps => match_elements exps t
  | _ => false
  end
end
with match_elements (exps : list Expression) (t : Tuple) : bool :=
  match exps, t with
  | [], TNil => true
  | e::es, TCons p ps => (match_expression_to_pattern e p) && (match_elements es ps)
  | _, _ => false
  end
.*)

Lemma hd_val (hd tl : Expression) : (EList hd tl) val -> hd val.
Proof.
  intros. inversion H. assumption.
Qed.

Lemma tl_val (hd tl : Expression) : (EList hd tl) val -> tl val.
Proof.
  intros. inversion H. assumption.
Qed.

Lemma tuple_val (exps : list Expression) : (ETuple exps) val -> (forall e : Expression, In e exps -> e val).
Proof.
  intros. inversion H. exact (H2 e H0).
Qed.

Lemma smaller_list e es : (forall e0 : Expression, In e0 (e :: es) -> e0 val) -> forall e0 : Expression, In e0 es -> e0 val.
Proof.
  intros. pose (in_cons e e0 es H0). exact (H e0 i).
Qed.

Fixpoint match_expression_to_pattern (e : Expression) (p : Pattern) (pf : e val) : bool :=
match p with
| PVar v => true (* every e matches to a pattern variable *)
| PLiteral l => match e with
  | ELiteral l' => match_literals l l'
  | _ => false
  end
| PList hd tl => match e in Expression, pf with
  | EList hd' tl', _ => (match_expression_to_pattern hd' hd (hd_val hd' tl' pf)) && (match_expression_to_pattern tl' tl (tl_val hd' tl' pf))
  | _, _ => false
  end
| PTuple t => match e in Expression, pf with
  | ETuple exps, _ => match_elements exps t (tuple_val exps pf)
  | _, _ => false
  end
end
with match_elements (exps : list Expression) (t : Tuple) (pf : forall e: Expression, In e exps -> e val) : bool :=
  match exps in (list _), pf with
  | [], _ => match t with
    | TNil => true
    | _ => false
    end
  | e::es, _ => match t with
    | TCons p ps => (match_expression_to_pattern e p (pf e (in_eq e es))) && (match_elements es ps (smaller_list e es pf))
    | _ => false
    end
  end
.

Compute match_expression_to_pattern (ELiteral (Atom "alma"%string)) (PVar "X"%string) (VJ_Literal _).
Compute match_expression_to_pattern (ELiteral (Atom "alma"%string)) (PLiteral (Atom "alma"%string)) (VJ_Literal _).
Compute match_expression_to_pattern (ELiteral (Atom "alma"%string)) (PLiteral EmptyTuple) (VJ_Literal _).
Compute match_expression_to_pattern (ETuple [ELiteral (Atom "alma"%string) ; ELiteral (Integer 1)]) (PVar "X"%string) (VJ_Tuple _ _).

Fixpoint variable_occurances (p : Pattern) : list Var :=
match p with
 | PVar v => [v]
 | PLiteral l => []
 | PList hd tl => variable_occurances hd ++ variable_occurances tl
 | PTuple t => variable_occurances_list t
end
with variable_occurances_list (t : Tuple) : list Var :=
match t with
| TNil => []
| TCons pat ps => variable_occurances pat ++ variable_occurances_list ps
end.

Fixpoint variable_occurances_set (p : Pattern) : set Var :=
match p with
 | PVar v => [v]
 | PLiteral l => []
 | PList hd tl => set_union string_dec (variable_occurances_set hd) (variable_occurances_set tl)
 | PTuple t => variable_occurances_set_list t
end
with variable_occurances_set_list (t : Tuple) : list Var :=
match t with
| TNil => []
| TCons pat ps => set_union string_dec (variable_occurances_set pat) (variable_occurances_set_list ps)
end.



(* Extended matching function, results the variable binding list *)
Fixpoint match_expression_bind_pattern (e : Expression) (p : Pattern) (pf : e val) : list (Var * Value) :=
match p with
| PVar v => [(v, e p: pf)] (* every e matches to a pattern variable *)
| PLiteral l => match e with
  | ELiteral l' => if match_literals l l' then [] else [] (* Error *)
  | _ => [] (* error *)
  end
| PList hd tl => match e in Expression, pf with
  | EList hd' tl', _ => (match_expression_bind_pattern hd' hd (hd_val hd' tl' pf)) ++ (match_expression_bind_pattern tl' tl (tl_val hd' tl' pf))
  | _, _ => [] (* error *)
  end
| PTuple t => match e in Expression, pf with
  | ETuple exps, _ => match_and_bind_elements exps t (tuple_val exps pf)
  | _, _ => []
  end
end
with match_and_bind_elements (exps : list Expression) (t : Tuple) (pf : forall e: Expression, In e exps -> e val) : list (Var * Value) :=
  match exps in (list _), pf with
  | [], _ => match t with
    | TNil => []
    | _ => [] (* error *)
    end
  | e::es, _ => match t with
    | TCons p ps => (match_expression_bind_pattern e p (pf e (in_eq e es))) ++ (match_and_bind_elements es ps (smaller_list e es pf)) (* Each variable can occur only once in a pattern according to the Core-Erlang ducumentation *)
    |_ => [] (* error *)
    end
  end
.

Fixpoint match_clause (e : Value) (cls : list Clause) (i : nat) : option (Expression * Expression * list (Var * Value)) :=
match cls, i with
| [], _ => None
| ((CCons p g exp)::xs), 0 => if match_expression_to_pattern (proj1_sig e) p (proj2_sig e) then Some (g, exp, (match_expression_bind_pattern (proj1_sig e) p (proj2_sig e))) else None
| ((CCons p g exp)::xs), S n' => match_clause e xs n'
end
.

(* Get the matching clause to an Expression *)
(* Fixpoint match_clauses (e : Value) (cls : list Clause) : option (Expression * Expression * list (Var * Value)) :=
match cls with
| [] => None
| ((CCons p g exp)::xs) => if match_expression_to_pattern (proj1_sig e) p (proj2_sig e) then Some (g, exp, (match_expression_bind_pattern (proj1_sig e) p (proj2_sig e))) else match_clauses e xs
end
.*)

Fixpoint correct_clauses (cl : list Clause) : bool :=
match cl with
| [] => true
| ((CCons p g exp)::xs) => ((length (variable_occurances p)) =? (length (variable_occurances_set p))) && correct_clauses xs
end.

(* Examples *)
Compute variable_occurances (PTuple [[PVar "X"%string ; PVar "X"%string]]).
Compute variable_occurances_set (PTuple [[PVar "X"%string ; PVar "X"%string]]).
Compute match_expression_bind_pattern (ELiteral (Atom "alma"%string)) (PVar "X"%string) (VJ_Literal _).
Compute match_expression_bind_pattern (ETuple [ELiteral (Atom "alma"%string) ; ELiteral (Integer 1)]) (PTuple [[PVar "X"%string ; PVar "X"%string]]) (VJ_Tuple _ _).

End Core_Erlang_Helpers.