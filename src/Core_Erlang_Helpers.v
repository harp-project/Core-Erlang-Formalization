Require Core_Erlang_Equalities.
From Coq Require Lists.ListSet.


(** Additional helper functions *)
Module Helpers.

Export Core_Erlang_Equalities.Equalities.

Import ListNotations.
Import Lists.ListSet.

Section list_proofs.

Section list_length_ind.  
  Variable A : Type.
  Variable P : list A -> Prop.

  Hypothesis H : forall xs, (forall l, length l < length xs -> P l) -> P xs.

  Theorem list_length_ind : forall xs, P xs.
  Proof.
    assert (forall xs l : list A, length l <= length xs -> P l) as H_ind.
    { induction xs; intros l Hlen; apply H; intros l0 H0.
      - inversion Hlen. lia.
      - apply IHxs. simpl in Hlen. lia.
    }
    intros xs.
    apply H_ind with (xs := xs).
    lia.
  Qed.
End list_length_ind.

Lemma list_length_helper_refl {A : Type} : forall l : list A, length l =? length l = true.
Proof.
  induction l.
  * auto.
  * auto.
Qed.

Lemma list_length_helper {A : Type} : forall l l' : list A, length l = length l' -> length l =? length l' = true.
Proof.
  intros. induction l.
  * inversion H. auto.
  * inversion H. simpl. apply list_length_helper_refl.
Qed.

(** If the list is longer than 0, then it has a first element *)
Lemma element_exist {A : Type} : forall n (l : list A), S n = length l -> exists e l', l = e::l'.
Proof.
  intros. destruct l.
  * inversion H.
  * apply ex_intro with a. apply ex_intro with l. reflexivity.
Qed.

Proposition list_length {A : Type} {a : A} {l : list A} : length (a :: l) > 0.
Proof.
  simpl. apply Nat.lt_0_succ.
Qed.

Theorem last_element_equal {A : Type} (l : list A) (def def2 : A):
  last l def = last (def :: l) def2.
Proof.
  induction l.
  * auto.
  * simpl. rewrite IHl. simpl. destruct l; auto.
Qed.

Fixpoint list_eqb {A : Type} (eq : A -> A -> bool) (l1 l2 : list A) : bool :=
match l1, l2 with
| [], [] => true
| x::xs, y::ys => eq x y && list_eqb eq xs ys
| _, _ => false
end.

Proposition list_eqb_refl {A : Type} {f : A -> A -> bool} (l : list A) :
  (forall a, f a a = true)
->
  list_eqb f l l = true.
Proof.
  induction l.
  * simpl. reflexivity.
  * simpl. intros. rewrite (H a), (IHl H). auto.
Qed.

End list_proofs.

Section Nat_Proofs.

Proposition modulo_2_plus_2 n :
  n mod 2 = S (S n) mod 2.
Proof.
  assert (S (S n) = n + 2). { lia. }
  rewrite H in *.
  epose (Nat.add_mod_idemp_r n 2 2 _).
  rewrite <- e. rewrite Nat.mod_same. rewrite Nat.add_0_r. auto.
  Unshelve.
  all: lia.
Qed.


Proposition modulo_2 n :
  n mod 2 = 0 \/ n mod 2 = 1.
Proof.
  induction n.
  * left. auto.
  * simpl. destruct (snd (Nat.divmod n 1 0 0)); auto.
Qed.

Proposition n_div_2_mod_0 n :
  n mod 2 = 0
->
  n = n / 2 * 2.
Proof.
  epose (Nat.div_mod n 2 _).
  intros. rewrite H in e. lia.
  Unshelve.
  lia.
Qed.

Proposition n_div_2_mod_1 n :
  n mod 2 = 1
->
  n = n / 2 * 2 + 1.
Proof.
  epose (Nat.div_mod n 2 _).
  intros. rewrite H in e. lia.
  Unshelve.
  lia.
Qed.

Proposition nat_ge_or : forall {n m : nat}, n >= m <-> n = m \/ n > m.
Proof.
  intros. lia.
Qed.

Lemma nat_lt_zero (i j : nat):
  j < i -> exists j', i = S j'.
Proof.
  intros. destruct i.
  * inversion H.
  * exists i. reflexivity.
Qed.

End Nat_Proofs.

(** The matching function of two literals *)
Definition match_literals (l l' : Literal) : bool :=
match l, l' with
| Atom s, Atom s' => eqb s s'
| Integer x, Integer x' => Z.eqb x x'
| _, _ => false
end.

(** Pattern matching success checker *)
Fixpoint match_value_to_pattern (e : Value) (p : Pattern) : bool :=
match p with
| PNil => 
   match e with
   | VNil => true
   | _ => false
   end
| PVar v => true (* every e matches to a pattern variable *)
| PLit l => match e with
  | VLit l' => match_literals l l'
  | _ => false
  end
| PCons hd tl => match e with
  | VCons hd' tl' => (match_value_to_pattern hd' hd) && (match_value_to_pattern tl' tl)
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
| PMap l => match e with
  | VMap l' => (fix match_elements vl pl :=
                     match vl, pl with
                     | [], [] => true
                     | _, [] => false
                     | [], _ => false
                     | ((v1, v2)::vs), ((p1, p2)::ps) => andb (andb (match_value_to_pattern v1 p1) 
                                                                    (match_value_to_pattern v2 p2))
                                                (match_elements vs ps)
                     end) l' l
  | _ => false
  end
end
.

(** Examples *)
Compute match_value_to_pattern (VClos [] [] 0 [] (ESingle ErrorExp)) (PVar "X"%string).
Compute match_value_to_pattern (VLit (Atom "a"%string)) (PVar "X"%string).
Compute match_value_to_pattern (VLit (Atom "a"%string)) (PLit (Atom "a"%string)).
Compute match_value_to_pattern (VLit (Atom "a"%string)) (PEmptyTuple).
Compute match_value_to_pattern (VTuple [VLit (Atom "a"%string) ; VLit (Integer 1)]) 
                               (PVar "X"%string).
Compute match_value_to_pattern (VTuple [VLit (Atom "a"%string) ; VLit (Integer 1)]) 
                               (PTuple [PVar "X"%string ; PLit (Integer 1)]).

Compute match_value_to_pattern (VMap [(ttrue, ttrue); (ttrue, ffalse)]) 
                               (PMap [(PVar "X"%string, PVar "Y"%string); (PLit (Atom "true"), PLit (Atom "false"))]).

(** Used variables in a pattern *)
Fixpoint variable_occurances (p : Pattern) : list Var :=
match p with
 | PNil => []
 | PVar v => [v]
 | PLit l => []
 | PCons hd tl => variable_occurances hd ++ variable_occurances tl
 | PTuple l => (fix variable_occurances_list l :=
                   match l with
                   | [] => []
                   | pat::ps => variable_occurances pat ++ variable_occurances_list ps
                   end) l
 | PMap l => (fix variable_occurances_list l :=
                   match l with
                   | [] => []
                   | (p1, p2)::ps => variable_occurances p1 ++ variable_occurances p2 ++ variable_occurances_list ps
                   end) l
end.

(** Used variables in a pattern, but now with sets *)
Fixpoint variable_occurances_set (p : Pattern) : set Var :=
match p with
 | PNil => []
 | PVar v => [v]
 | PLit l => []
 | PCons hd tl => set_union string_dec (variable_occurances_set hd) (variable_occurances_set tl)
 | PTuple l => (fix variable_occurances_set_list t :=
                    match t with
                    | [] => []
                    | pat::ps => set_union string_dec (variable_occurances_set pat) 
                                                      (variable_occurances_set_list ps)
                    end) l
 | PMap l => (fix variable_occurances_set_list t :=
                    match t with
                    | [] => []
                    | (p1, p2)::ps => set_union string_dec (set_union string_dec (variable_occurances_set p1)
                                                                                 (variable_occurances_set p2))
                                                      (variable_occurances_set_list ps)
                    end) l
end.



(** Extended matching function, results the variable binding list 
    Should be used together with match_value_to_pattern *)
Fixpoint match_value_bind_pattern (e : Value) (p : Pattern) : list (Var * Value) :=
match p with
| PNil => match e with
                | VNil => []
                | _ => [] (** error *)
                end
| PVar v => [(v, e)] (** every e matches to a pattern variable *)
| PLit l => match e with
  | VLit l' => if match_literals l l' then [] else [] (* Error *)
  | _ => [] (** error *)
  end
| PCons hd tl => match e with
  | VCons hd' tl' => (match_value_bind_pattern hd' hd) ++ (match_value_bind_pattern tl' tl)
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
| PMap l => match e with
  | VMap l' => (fix match_and_bind_elements exps t :=
                        match exps with
                        | [] => match t with
                          | [] => []
                          | _ => [] (** error *)
                          end
                        | (e1, e2)::es => match t with
                          | (p1, p2)::ps => (match_value_bind_pattern e1 p1) ++ (match_value_bind_pattern e2 p2) ++
                                     (match_and_bind_elements es ps) 
(** Each variable can occur only once in a pattern according to the Core-Erlang documentation *)
                          |_ => [] (** error *)
                          end 
                        end) l' l
  | _ => []
  end
end
.

(** Examples *)
Compute match_value_bind_pattern (VClos [] [] 0 [] (ESingle ErrorExp)) (PVar "X"%string).
Compute match_value_bind_pattern (VLit (Atom "a"%string)) (PVar "X"%string).
Compute match_value_bind_pattern (VLit (Atom "a"%string)) (PLit (Atom "alma"%string)).
Compute match_value_bind_pattern (VLit (Atom "a"%string)) (PEmptyTuple).
Compute match_value_bind_pattern (VTuple [VLit (Atom "a"%string) ; VLit (Integer 1)]) 
                                 (PVar "X"%string).
Compute match_value_to_pattern (VTuple [VLit (Atom "a"%string) ; 
                                        VLit (Integer 1); VLit (Integer 2)]) 
                               (PTuple [PVar "X"%string ; PVar "Y"%string]).
Compute match_value_bind_pattern (VTuple [VLit (Atom "a"%string) ; VLit (Integer 1); 
                                          VLit (Integer 2)]) 
                                 (PTuple [PVar "X"%string ; PVar "Y"%string]).
Compute match_value_bind_pattern (VMap [(ttrue, ttrue); (ttrue, ffalse)]) 
                               (PMap [(PVar "X"%string, PVar "Y"%string); (PVar "Z"%string, PLit (Atom "false"))]).


Fixpoint match_valuelist_to_patternlist (vl : ValueSequence) (pl : list Pattern) : bool :=
match vl, pl with
| [], [] => true
| (v::vs), (p::ps) => match_value_to_pattern v p && match_valuelist_to_patternlist vs ps
| _, _ => false
end.

Compute match_valuelist_to_patternlist [] [].
Compute match_valuelist_to_patternlist [VLit (Atom "a"%string); VLit (Atom "a"%string)] 
                                       [PVar "X"%string; PVar "Y"%string].
Compute match_valuelist_to_patternlist [VLit (Atom "a"%string); VLit (Atom "a"%string)] 
                                       [PVar "X"%string; PLit (Integer 0)].

Fixpoint match_valuelist_bind_patternlist (vl : ValueSequence) (pl : list Pattern) : 
   list (Var * Value) :=
match vl, pl with
| [], [] => []
| (v::vs), (p::ps) => match_value_bind_pattern v p ++ match_valuelist_bind_patternlist vs ps
| _, _ => []
end.

Compute match_valuelist_bind_patternlist [] [].
Compute match_valuelist_bind_patternlist [VLit (Atom "a"%string); VLit (Atom "a"%string)] 
                                       [PVar "X"%string; PVar "Y"%string].

(** CAUTION : THIS CASE COULDN'T OCCUR IN CORE ERLANG *)
Compute match_valuelist_bind_patternlist [VLit (Atom "a"%string); VLit (Atom "a"%string)] 
                                       [PVar "X"%string; PLit (Integer 0)].

(** From the list of patterns, guards and bodies, this function decides if a value matches the ith clause *)
Fixpoint match_clause (e : ValueSequence) (l : list (list Pattern * Expression * Expression)) (i : nat) : option (Expression * Expression * list (Var * Value)) :=
match l, i with
| [], _ => None
| (p,g,exp)::xs, 0 => if match_valuelist_to_patternlist e p then Some (g, exp, (match_valuelist_bind_patternlist e p)) else None
| (p, g, e0)::xs, S n' => match_clause e xs n'
end
.

(* (** TODO: Clause checker *)
Fixpoint correct_clauses (ps : list (list Pattern)) (gs : list Expression) (bs : list Expression) : bool :=
match ps, gs, bs with
| [], [], [] => true
| p::ps, g::gs, exp::es => 
   ((length (fold_right variable_occurances [] p)) =? (length (variable_occurances_set p))) && 
   correct_clauses ps gs es
| _, _, _ => false
end. *)

(* Examples *)
Compute variable_occurances (PTuple [PVar "X"%string ; PVar "X"%string]).
Compute variable_occurances_set (PTuple [PVar "X"%string ; PVar "X"%string]).

(** Get the used variables of an expression *)
Fixpoint variables (e : Expression) : list Var :=
match e with
| EValues el => flat_map variables_single el
| ESingle e => variables_single e
end
with variables_single (e : SingleExpression) : list Var :=
match e with
  | ENil => []
  | ELit l => []
  | EVar v => [v]
  | EFunId f => []
  | EFun vl e => variables e
  | ECons hd tl => app (variables hd) (variables tl)
  | ETuple l => flat_map variables l
  | ECall f l => flat_map variables l
  | EPrimOp f l => flat_map variables l
  | EApp exp l => app (variables exp) (flat_map variables l)
  | ECase e l => variables e ++ fold_right (fun '(a, b, c) r => app (app (variables b) (variables c)) r) [] l
  | ELet l e1 e2 => l ++ (variables e1) ++ (variables e2)
  | ESeq e1 e2 => app (variables e1) (variables e2)
  | ELetRec l e => variables e 
  | EMap l => fold_right (fun '(a, b) r => app (app (variables a) (variables b)) r) [] l
  | ETry e1 vl1 e2 vl2 e3 => vl1 ++ vl2 ++ variables e1 ++ variables e2 ++ variables e3
end.

Compute variables (ELet ["X"%string] (ESingle (EVar "Z"%string)) (ELet ["Y"%string] ErrorExp (ECall "plus"%string [^ EVar "X"%string ; ^EVar "Y"%string]))).


(** Building value maps based on the value ordering value_less *)
Fixpoint map_insert (k v : Value) (kl : list Value) (vl : list Value) : (list Value) * (list Value) :=
match kl, vl with
| [], [] => ([k], [v])
| k'::ks, v'::vs => if Value_ltb k k' 
                    then (k::k'::ks, v::v'::vs) 
                    else
                       if Value_eqb k k' 
                       then (k'::ks, v'::vs) 
                       else (k'::(fst (map_insert k v ks vs)), v'::(snd (map_insert k v ks vs)))
| _, _ => ([], [])
end.

(** Create maps without duplicates based on the ordering *)
Fixpoint make_value_map (kl vl : list Value) : (list Value) * (list Value) :=
match kl, vl with
| [], [] => ([], [])
| k::ks, v::vs => map_insert k v (fst (make_value_map ks vs)) (snd (make_value_map ks vs))
| _, _ => ([], [])
end.

Compute make_value_map [VLit (Integer 5); VLit (Integer 5); VLit (Atom ""%string)] 
                       [VLit (Integer 5); VLit (Integer 7); VLit (Atom ""%string)].

Fixpoint make_map_exps (l : list (Expression * Expression)) : list Expression :=
match l with
| [] => []
| (x, y)::xs => x::y::(make_map_exps xs)
end.

Lemma length_make_map_exps l :
  length (make_map_exps l) = length l * 2.
Proof.
  induction l.
  * simpl. auto.
  * simpl. destruct a. simpl. lia.
Qed.

Fixpoint make_map_vals (l l' : list Value) : list Value  :=
match l, l' with
| [], [] => []
| k::ks, v::vs => k::v::(make_map_vals ks vs)
| k::ks, _ => [k]
| _, _ => []
end.

Lemma length_make_map_vals l : forall l',
  length l = length l' ->
  length (make_map_vals l l') = length l * 2.
Proof.
  induction l; intros.
  * apply eq_sym, length_zero_iff_nil in H. subst. auto.
  * simpl in *. destruct l'.
    - simpl in H. congruence.
    - inversion H. simpl. rewrite (IHl l' H1). lia.
Qed.

Lemma length_make_map_vals2 l : forall l',
  length l = S (length l') ->
  length (make_map_vals l l') = length l' * 2 + 1.
Proof.
  induction l; intros.
  * inversion H.
  * simpl in *. destruct l'.
    - simpl in H. apply Nat.succ_inj in H. apply length_zero_iff_nil in H.
      subst. simpl. auto.
    - inversion H. simpl. rewrite (IHl l' H1). lia.
Qed.

Lemma make_map_vals_eq kvals : forall kvals0 vvals vvals0,
  length kvals = length vvals ->
  length kvals0 = length vvals0 ->
  length kvals = length kvals0 ->
  make_map_vals kvals vvals = make_map_vals kvals0 vvals0
->
  kvals = kvals0 /\ vvals = vvals0.
Proof.
  induction kvals; intros.
  * apply eq_sym, length_zero_iff_nil in H. apply eq_sym, length_zero_iff_nil in H1. subst.
    apply eq_sym, length_zero_iff_nil in H0. subst.
    auto.
  * pose (element_exist _ _ H).
    pose (element_exist _ _ H1). inversion e. inversion e0.
    destruct H3, H4. subst. clear e. clear e0.
    pose (element_exist _ _ H0). inversion e. destruct H3. clear e.
    subst. simpl in H2. inversion H2. subst.
    inversion H. inversion H0. inversion H1.
    pose (IHkvals _ _ _ H4 H5 H7 H6). destruct a. subst. auto.
Qed.

Lemma make_map_vals_eq_rev kvals kvals0 vvals vvals0 :
  kvals = kvals0 -> vvals = vvals0
->
  make_map_vals kvals vvals = make_map_vals kvals0 vvals0.
Proof.
  intros. subst. auto.
Qed.

Fixpoint make_map_vals_inverse (l : list Value) : option (list Value * list Value) :=
match l with
| [] => Some ([], [])
| x::y::xs => match make_map_vals_inverse xs with
              | Some (vals1, vals2) => Some (x::vals1, y::vals2)
              | None => None
              end
| [x] => None
end.

Theorem make_map_inverse_length :
  forall kvals vvals l,
  make_map_vals_inverse l = Some (kvals, vvals)
->
  length l = 2 * length kvals /\ length l = 2 * length vvals.
Proof.
  induction kvals; intros.
  * destruct l; simpl in H.
    - inversion H. auto.
    - destruct l.
      + inversion H.
      + destruct (make_map_vals_inverse l).
        ** destruct p. inversion H.
        ** inversion H.
  * destruct l; simpl in H.
    - inversion H.
    - destruct l.
      + inversion H.
      + case_eq (make_map_vals_inverse l); intros; rewrite H0 in H.
        ** destruct p. inversion H. subst.
           pose (IHkvals _ _ H0). destruct a0.
           simpl. lia.
        ** congruence.
Qed.

Theorem make_map_inverse_relation :
  forall kvals vvals v,
  make_map_vals_inverse v = Some (kvals, vvals)
->
  v = make_map_vals kvals vvals.
Proof.
  induction kvals; intros.
  * destruct v; simpl in H.
    - inversion H. auto.
    - destruct v0.
      + inversion H.
      + destruct (make_map_vals_inverse v1).
        ** destruct p. inversion H.
        ** inversion H.
  * destruct v; simpl in H.
    - inversion H.
    - destruct v0.
      + inversion H.
      + case_eq (make_map_vals_inverse v1); intros; rewrite H0 in H.
        ** destruct p. inversion H. subst.
           pose (IHkvals _ _ H0).
           simpl. rewrite e. auto.
        ** congruence.
Qed.

Theorem make_map_consistent :
  forall kvals vvals,
  length kvals = length vvals ->
  make_map_vals_inverse (make_map_vals kvals vvals) = Some (kvals, vvals).
Proof.
  induction kvals; intros.
  * apply eq_sym, length_zero_iff_nil in H. subst. simpl. auto.
  * pose (P := element_exist _ _ H). destruct P. destruct H0. subst. inversion H.
    simpl.
    pose (P := IHkvals x0 H1). rewrite P. auto.
Qed.

Theorem map_correcness : forall vals,
  exists kvals vvals, vals = make_map_vals kvals vvals /\ length kvals = length vvals + length vals mod 2.
Proof.
  induction vals using list_length_ind.
  destruct vals.
  * exists []. exists []. auto.
  * destruct vals.
    - exists [v]. exists []. simpl. auto.
    - assert (Datatypes.length vals < Datatypes.length (v :: v0 :: vals)). { simpl. lia. }
      pose (H vals H0). destruct e, H1, H1.
      exists (v::x). exists (v0::x0).
      split.
      + rewrite H1. auto.
      + simpl length. rewrite <- modulo_2_plus_2.
        lia.
Qed.

End Helpers.