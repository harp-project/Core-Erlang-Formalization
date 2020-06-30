Load Core_Erlang_Equalities.
From Coq Require Lists.ListSet.


(** Additional helper functions *)
Module Core_Erlang_Helpers.


Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.
Import Lists.ListSet.

Import Core_Erlang_Syntax.
Import Core_Erlang_Equalities.

Section list_proofs.

Variable A : Type.

Lemma list_length_helper_refl : forall l : list A, length l =? length l = true.
Proof.
  induction l.
  * auto.
  * auto.
Qed.

Lemma list_length_helper : forall l l' :
  list A, length l = length l' -> length l =? length l' = true.
Proof.
  intros. induction l.
  * inversion H. auto.
  * inversion H. simpl. apply list_length_helper_refl.
Qed.

(** If the list is longer than 0, then it has a first element *)
Lemma element_exist : forall n (l : list A), S n = length l -> exists e l', l = e::l'.
Proof.
  intros. destruct l.
  * inversion H.
  * apply ex_intro with a. apply ex_intro with l. reflexivity.
Qed.

End list_proofs.

(** The matching function of two literals *)
Fixpoint match_literals (l l' : Literal) : bool :=
match l, l' with
| Atom s, Atom s' => eqb s s'
| Integer x, Integer x' => Z.eqb x x'
| _, _ => false
end.

(** Pattern matching success checker *)
Fixpoint match_value_to_pattern (e : Value) (p : Pattern) : bool :=
match p with
| PEmptyList => 
   match e with
   | VEmptyList => true
   | _ => false
   end
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
                     | (v::vs), (p::ps) => andb (match_value_to_pattern v p) 
                                                (match_elements vs ps)
                     end) exps l
  | _ => false
  end
end
.

(** Examples *)
Compute match_value_to_pattern (VClosure [] [] 0 [] ErrorExp) (PVar "X"%string).
Compute match_value_to_pattern (VLiteral (Atom "a"%string)) (PVar "X"%string).
Compute match_value_to_pattern (VLiteral (Atom "a"%string)) (PLiteral (Atom "a"%string)).
Compute match_value_to_pattern (VLiteral (Atom "a"%string)) (PEmptyTuple).
Compute match_value_to_pattern (VTuple [VLiteral (Atom "a"%string) ; VLiteral (Integer 1)]) 
                               (PVar "X"%string).
Compute match_value_to_pattern (VTuple [VLiteral (Atom "a"%string) ; VLiteral (Integer 1)]) 
                               (PTuple [PVar "X"%string ; PLiteral (Integer 1)]).

(** Used variables in a pattern *)
Fixpoint variable_occurances (p : Pattern) : list Var :=
match p with
 | PEmptyList => []
 | PVar v => [v]
 | PLiteral l => []
 | PList hd tl => variable_occurances hd ++ variable_occurances tl
 | PTuple l => (fix variable_occurances_list l :=
                   match l with
                   | [] => []
                   | pat::ps => variable_occurances pat ++ variable_occurances_list ps
                   end) l
end.

(** Used variables in a pattern, but now with sets *)
Fixpoint variable_occurances_set (p : Pattern) : set Var :=
match p with
 | PEmptyList => []
 | PVar v => [v]
 | PLiteral l => []
 | PList hd tl => set_union string_dec (variable_occurances_set hd)
                                       (variable_occurances_set tl)
 | PTuple l => (fix variable_occurances_set_list t :=
                    match t with
                    | [] => []
                    | pat::ps => set_union string_dec (variable_occurances_set pat) 
                                                      (variable_occurances_set_list ps)
                    end) l
end.



(** Extended matching function, results the variable binding list 
    Should be used together with match_value_to_pattern *)
Fixpoint match_value_bind_pattern (e : Value) (p : Pattern) : list (Var * Value) :=
match p with
| PEmptyList => match e with
                | VEmptyList => []
                | _ => [] (** error *)
                end
| PVar v => [(v, e)] (** every e matches to a pattern variable *)
| PLiteral l => match e with
  | VLiteral l' => if match_literals l l' then [] else [] (* Error *)
  | _ => [] (** error *)
  end
| PList hd tl => match e with
  | VList hd' tl' => (match_value_bind_pattern hd' hd) ++ (match_value_bind_pattern tl' tl)
  | _ => [] (** error *)
  end
| PTuple pl => match e with
  | VTuple exps => (fix match_and_bind_elements exps t :=
                        match exps with
                        | [] => match t with
                          | [] => []
                          | _ => [] (** error *)
                          end
                        | e::es => match t with
                          | p::ps => (match_value_bind_pattern e p) ++ 
                                     (match_and_bind_elements es ps) 
(** Each variable can occur only once in a pattern according to the Core-Erlang documentation *)
                          |_ => [] (** error *)
                          end 
                        end) exps pl
  | _ => []
  end
end
.

(** Examples *)
Compute match_value_bind_pattern (VClosure [] [] 0 [] ErrorExp) (PVar "X"%string).
Compute match_value_bind_pattern (VLiteral (Atom "a"%string)) (PVar "X"%string).
Compute match_value_bind_pattern (VLiteral (Atom "a"%string)) (PLiteral (Atom "alma"%string)).
Compute match_value_bind_pattern (VLiteral (Atom "a"%string)) (PEmptyTuple).
Compute match_value_bind_pattern (VTuple [VLiteral (Atom "a"%string) ; VLiteral (Integer 1)]) 
                                 (PVar "X"%string).
Compute match_value_to_pattern (VTuple [VLiteral (Atom "a"%string) ; 
                                        VLiteral (Integer 1); VLiteral (Integer 2)]) 
                               (PTuple [PVar "X"%string ; PVar "Y"%string]).
Compute match_value_bind_pattern (VTuple [VLiteral (Atom "a"%string) ; VLiteral (Integer 1); 
                                          VLiteral (Integer 2)]) 
                                 (PTuple [PVar "X"%string ; PVar "Y"%string]).

(** From the list of patterns, guards and bodies, this function 
  decides if a value matches the ith clause *)
Fixpoint match_clause (e : Value) (ps : list Pattern) (gs : list Expression) 
   (bs : list Expression) (i : nat)
   : option (Expression * Expression * list (Var * Value)) :=
match ps, gs, bs, i with
| [], [], [], _ => None
| p::ps, g::gs, exp::es, 0 => if match_value_to_pattern e p 
                              then Some (g, exp, (match_value_bind_pattern e p)) 
                              else None
| p::ps, g::gs, e0::es, S n' => match_clause e ps gs es n'
| _, _, _, _ => None
end
.

(** Clause checker *)
Fixpoint correct_clauses (ps : list Pattern) (gs : list Expression)
        (bs : list Expression) : bool :=
match ps, gs, bs with
| [], [], [] => true
| p::ps, g::gs, exp::es => 
   ((length (variable_occurances p)) =? (length (variable_occurances_set p))) && 
   correct_clauses ps gs es
| _, _, _ => false
end.

(* Examples *)
Compute variable_occurances (PTuple [PVar "X"%string ; PVar "X"%string]).
Compute variable_occurances_set (PTuple [PVar "X"%string ; PVar "X"%string]).

(** Get the used variables of an expression *)
Fixpoint variables (e : Expression) : list Var :=
match e with
| EEmptyList => []
| ELiteral l => []
| EVar     v => [v]
| EFunId   f => []
| EFun  vl e => variables e
| EList hd tl => variables hd ++ variables tl
| ETuple l => flat_map variables l
| ECall  f l => flat_map variables l
| EApply exp l => flat_map variables l ++ variables exp
| ECase  e ps gs bs => variables e ++ flat_map variables gs ++ flat_map variables bs
| ELet s el e => flat_map variables el ++ variables e
| ELetrec fn vs bs e => variables e (** Extesion needed maybe *)
| EMap  kl vl => flat_map variables kl ++ flat_map variables vl
| ETry e e1 e2 v vex1 vex2 vex3 => [v; vex1; vex2; vex3] ++ 
                                   variables e ++ variables e1 ++ variables e2
end.

Compute variables (ELet ["X"%string] [EVar "Z"%string] (
                     ELet ["Y"%string] [ErrorExp] 
                       (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]))).

(** Building value maps based on the value ordering value_less *)
Fixpoint map_insert (k v : Value) (kl : list Value) (vl : list Value) 
  : (list Value) * (list Value) :=
match kl, vl with
| [], [] => ([k], [v])
| k'::ks, v'::vs => if value_less k k' 
                    then (k::k'::ks, v::v'::vs) 
                    else
                       if bValue_eq_dec k k' 
                       then (k'::ks, v'::vs) 
                       else (k'::(fst (map_insert k v ks vs)), 
                             v'::(snd (map_insert k v ks vs)))
| _, _ => ([], [])
end.

(** Create maps without duplicates based on the ordering *)
Fixpoint make_value_map (kl vl : list Value) : (list Value) * (list Value) :=
match kl, vl with
| [], [] => ([], [])
| k::ks, v::vs => map_insert k v (fst (make_value_map ks vs)) (snd (make_value_map ks vs))
| _, _ => ([], [])
end.

Compute make_value_map [VLiteral (Integer 5); VLiteral (Integer 5); VLiteral (Atom ""%string)] 
                       [VLiteral (Integer 5); VLiteral (Integer 7); VLiteral (Atom ""%string)].

Definition nth_id (ids : list nat) (def i : nat) :=
match i with
| 0 => def
| S i' => nth i' ids 0
end.

Compute nth_id [4; 7; 8] 3 2 = 7.

End Core_Erlang_Helpers.