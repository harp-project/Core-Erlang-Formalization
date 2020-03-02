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
| PTuple l => match e with
  | VTuple exps => (fix match_elements vl pl :=
                   match vl, pl with
                   | [], [] => true
                   | _, [] => false
                   | [], _ => false
                   | (v::vs), (p::ps) => andb (match_value_to_pattern v p) (match_elements vs ps)
                   end) exps l
  | _ => false
  end
end
.

(* Examples *)
Compute match_value_to_pattern (VClosure (inl []) [] ErrorExp) (PVar "X"%string).
Compute match_value_to_pattern (VLiteral (Atom "alma"%string)) (PVar "X"%string).
Compute match_value_to_pattern (VLiteral (Atom "alma"%string)) (PLiteral (Atom "alma"%string)).
Compute match_value_to_pattern (VLiteral (Atom "alma"%string)) (PLiteral EmptyTuple).
Compute match_value_to_pattern (VTuple [VLiteral (Atom "alma"%string) ; VLiteral (Integer 1)]) (PVar "X"%string).
Compute match_value_to_pattern (VTuple [VLiteral (Atom "alma"%string) ; VLiteral (Integer 1)]) (PTuple [PVar "X"%string ; PLiteral (Integer 1)]).

Fixpoint variable_occurances (p : Pattern) : list Var :=
match p with
 | PVar v => [v]
 | PLiteral l => []
 | PList hd tl => variable_occurances hd ++ variable_occurances tl
 | PTuple l => (fix variable_occurances_list l :=
                   match l with
                   | [] => []
                   | pat::ps => variable_occurances pat ++ variable_occurances_list ps
                   end) l
end.

Fixpoint variable_occurances_set (p : Pattern) : set Var :=
match p with
 | PVar v => [v]
 | PLiteral l => []
 | PList hd tl => set_union string_dec (variable_occurances_set hd) (variable_occurances_set tl)
 | PTuple l => (fix variable_occurances_set_list t :=
                    match t with
                    | [] => []
                    | pat::ps => set_union string_dec (variable_occurances_set pat) (variable_occurances_set_list ps)
                    end) l
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
| PTuple pl => match e with
  | VTuple exps => (fix match_and_bind_elements exps t :=
                        match exps with
                        | [] => match t with
                          | [] => []
                          | _ => [] (* error *)
                          end
                        | e::es => match t with
                          | p::ps => (match_value_bind_pattern e p) ++ (match_and_bind_elements es ps) (* Each variable can occur only once in a pattern according to the Core-Erlang ducumentation *)
                          |_ => [] (* error *)
                          end 
                        end) exps pl
  | _ => []
  end
end
.


Compute match_value_bind_pattern (VClosure (inl []) [] ErrorExp) (PVar "X"%string).
Compute match_value_bind_pattern (VLiteral (Atom "alma"%string)) (PVar "X"%string).
Compute match_value_bind_pattern (VLiteral (Atom "alma"%string)) (PLiteral (Atom "alma"%string)).
Compute match_value_bind_pattern (VLiteral (Atom "alma"%string)) (PLiteral EmptyTuple).
Compute match_value_bind_pattern (VTuple [VLiteral (Atom "alma"%string) ; VLiteral (Integer 1)]) (PVar "X"%string).
Compute match_value_to_pattern (VTuple [VLiteral (Atom "alma"%string) ; VLiteral (Integer 1); VLiteral (Integer 2)]) (PTuple [PVar "X"%string ; PVar "Y"%string]).
Compute match_value_bind_pattern (VTuple [VLiteral (Atom "alma"%string) ; VLiteral (Integer 1); VLiteral (Integer 2)]) (PTuple [PVar "X"%string ; PVar "Y"%string]).


Fixpoint match_clause (e : Value) (ps : list Pattern) (gs : list Expression) (bs : list Expression) (i : nat) : option (Expression * Expression * list (Var * Value)) :=
match ps, gs, bs, i with
| [], [], [], _ => None
| p::ps, g::gs, exp::es, 0 => if match_value_to_pattern e p then Some (g, exp, (match_value_bind_pattern e p)) else None
| p::ps, g::gs, e0::es, S n' => match_clause e ps gs es n'
| _, _, _, _ => None
end
.

Fixpoint correct_clauses (ps : list Pattern) (gs : list Expression) (bs : list Expression) : bool :=
match ps, gs, bs with
| [], [], [] => true
| p::ps, g::gs, exp::es => ((length (variable_occurances p)) =? (length (variable_occurances_set p))) && correct_clauses ps gs es
| _, _, _ => false
end.

(* Examples *)
Compute variable_occurances (PTuple [PVar "X"%string ; PVar "X"%string]).
Compute variable_occurances_set (PTuple [PVar "X"%string ; PVar "X"%string]).

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
| ECase  e ps gs bs => variables e ++ flat_map variables gs ++ flat_map variables bs
| ELet s el e => flat_map variables el ++ variables e
| ELetrec fn vs bs e => variables e (* Extesion needed? *)
| EMap  kl vl => flat_map variables kl ++ flat_map variables vl
| ETry e e1 e2 v vex1 vex2 vex3 => [v; vex1; vex2; vex3] ++ variables e ++ variables e1 ++ variables e2
end.

Compute variables (ELet ["X"%string] [EVar "Z"%string] (ELet ["Y"%string] [ErrorExp] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]))).

(* Fixpoint eqb_value (v1 v2 : Value) : bool :=
match v1, v2 with
 | VLiteral l, VLiteral l => true
 | VClosure env vl e, _ => false
 | VList vhd vtl, _ => false
 | VTuple vl, _ => false
 | VMap kl vl, _ => fasle
end
. *)

(* Fixpoint set_add_value (key val : Value) (x y : list Value) : list Value * list Value :=
match x, y with
| [], [] => ([key], [val])
| key'::xs, val'::ys => match {key = key'} + {key <> key'} with
                        | left _ => (key :: xs,val :: ys) (*overwrite*)
                        | right _ => (key' :: (fst (set_add_value key val xs ys)), val' :: (snd (set_add_value key val xs ys)))
                       end
| _, _ => ([], [])
end. *)

Import Lists.ListSet.



(* Fixpoint make_ordered_set (kl vl : list Value) : list Value * list Value :=
match kl, vl with
| [], [] => ([], [])
| key::kls, val::vls => set_add_value key val (fst (make_ordered_set kls vls)) (snd (make_ordered_set kls vls))
| _, _ => ([], [])
end. *)

(* Compute make_ordered_set [] [].
Compute make_ordered_set [ok] [ok].
Compute make_ordered_set [ok;ok] [ok;ErrorValue]. *)

End Core_Erlang_Helpers.