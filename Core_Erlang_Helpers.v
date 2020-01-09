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

(* The matching function of two literals *)
Fixpoint match_literals (l l' : Literal) : bool :=
match l, l' with
| Atom s, Atom s' => eqb s s'
| Integer x, Integer x' => Z.eqb x x'
| EmptyList, EmptyList => true
| EmptyTuple, EmptyTuple => true
| _, _ => false
end.

Fixpoint match_value_to_pattern (e : Value) (p : Pattern) : bool :=
match p with
| PVar v => true (* every e matches to a pattern variable *)
| PLiteral l => match e with
  | VLiteral l' => match_literals l l'
  | _ => false
  end
| PList hd tl => match e with
  | VList hd' tl' => (match_value_to_pattern hd' hd) && (match_value_to_pattern tl' tl)
  | _ => false
  end
| PTuple t => match e with
  | VTuple exps => match_elements exps t
  | _ => false
  end
end
with match_elements (exps : list Value) (t : Tuple) : bool :=
  match exps with
  | [] => match t with
    | TNil => true
    | _ => false
    end
  | e::es => match t with
    | TCons p ps => (match_value_to_pattern e p) && (match_elements es ps)
    | _ => false
    end
  end
.

(* Examples *)
Compute match_value_to_pattern (VClosure (inl "X"%string) [] ErrorExp) (PVar "X"%string).
Compute match_value_to_pattern (VLiteral (Atom "alma"%string)) (PVar "X"%string).
Compute match_value_to_pattern (VLiteral (Atom "alma"%string)) (PLiteral (Atom "alma"%string)).
Compute match_value_to_pattern (VLiteral (Atom "alma"%string)) (PLiteral EmptyTuple).
Compute match_value_to_pattern (VTuple [VLiteral (Atom "alma"%string) ; VLiteral (Integer 1)]) (PVar "X"%string).
Compute match_value_to_pattern (VTuple [VLiteral (Atom "alma"%string) ; VLiteral (Integer 1)]) (PTuple [[PVar "X"%string ; PLiteral (Integer 1)]]).

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
Fixpoint match_value_bind_pattern (e : Value) (p : Pattern) : list (Var * Value) :=
match p with
| PVar v => [(v, e)] (* every e matches to a pattern variable *)
| PLiteral l => match e with
  | VLiteral l' => if match_literals l l' then [] else [] (* Error *)
  | _ => [] (* error *)
  end
| PList hd tl => match e with
  | VList hd' tl' => (match_value_bind_pattern hd' hd) ++ (match_value_bind_pattern tl' tl)
  | _ => [] (* error *)
  end
| PTuple t => match e with
  | VTuple exps => match_and_bind_elements exps t
  | _ => []
  end
end
with match_and_bind_elements (exps : list Value) (t : Tuple) : list (Var * Value) :=
  match exps with
  | [] => match t with
    | TNil => []
    | _ => [] (* error *)
    end
  | e::es => match t with
    | TCons p ps => (match_value_bind_pattern e p) ++ (match_and_bind_elements es ps) (* Each variable can occur only once in a pattern according to the Core-Erlang ducumentation *)
    |_ => [] (* error *)
    end
  end
.

Compute match_value_bind_pattern (VClosure (inl "X"%string) [] ErrorExp) (PVar "X"%string).
Compute match_value_bind_pattern (VLiteral (Atom "alma"%string)) (PVar "X"%string).
Compute match_value_bind_pattern (VLiteral (Atom "alma"%string)) (PLiteral (Atom "alma"%string)).
Compute match_value_bind_pattern (VLiteral (Atom "alma"%string)) (PLiteral EmptyTuple).
Compute match_value_bind_pattern (VTuple [VLiteral (Atom "alma"%string) ; VLiteral (Integer 1)]) (PVar "X"%string).
Compute match_value_bind_pattern (VTuple [VLiteral (Atom "alma"%string) ; VLiteral (Integer 1)]) (PTuple [[PVar "X"%string ; PLiteral (Integer 1)]]).


Fixpoint match_clause (e : Value) (cls : list Clause) (i : nat) : option (Expression * Expression * list (Var * Value)) :=
match cls, i with
| [], _ => None
| ((CCons p g exp)::xs), 0 => if match_value_to_pattern e p  then Some (g, exp, (match_value_bind_pattern e p)) else None
| ((CCons p g exp)::xs), S n' => match_clause e xs n'
end
.

Fixpoint correct_clauses (cl : list Clause) : bool :=
match cl with
| [] => true
| ((CCons p g exp)::xs) => ((length (variable_occurances p)) =? (length (variable_occurances_set p))) && correct_clauses xs
end.

(* Examples *)
Compute variable_occurances (PTuple [[PVar "X"%string ; PVar "X"%string]]).
Compute variable_occurances_set (PTuple [[PVar "X"%string ; PVar "X"%string]]).

(* Get the used variables of an expression *)
Fixpoint variables (e : Expression) : list (Var) :=
match e with
| ELiteral l => []
| EVar     v => [v]
| EFunSig  f => []
| EFun  vl e => variables e
| EList hd tl => variables hd ++ variables tl
| ETuple l => flat_map variables l
| ECall  f l => flat_map variables l
| EApply exp l => flat_map variables l ++ variables exp
| ECase  e cls => variables e ++ flat_map clause_variables cls
| ELet s el e => flat_map variables el ++ variables e
| ELetrec fn fs e => variables e
| EMap  kl vl => flat_map variables kl ++ flat_map variables vl
end
with clause_variables (cl : Clause) : list (Var) :=
match cl with
| (CCons p g e) => (variables g) ++ (variables e)
end.

Compute variables (ELet ["X"%string] [EVar "Z"%string] (ELet ["Y"%string] [ErrorExp] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]))).

End Core_Erlang_Helpers.