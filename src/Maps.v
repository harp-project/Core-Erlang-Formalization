(**
  This file includes a auxiliary definitions to formalise Core Erlang's maps.

  http://erlang.org/pipermail/erlang-questions/2017-October/093981.html
  NOTE:
  Maps are not ordered in Erlang. However, when comparing two maps, first
  keys are compared in ascending order, then the values in key order.

  For simplicity, our representation is ordered, and currently there is no
  standard function (beside comparison) whose formalisation exploits this
  assumption.
*)



From CoreErlang Require Export Equalities.
Import ListNotations.



(** Building Val maps based on the Val ordering Val_ltb
    This function inserts a key-value pair into the map. This operation
    overwrites existing keys.
*)
Fixpoint map_insert (k v : Val) (m : list (Val * Val))
  : (list (Val * Val)) :=
match m with
| [] => [(k,v)]
| (k',v')::ms => if Val_ltb k k' 
                 then ((k, v)::(k',v')::ms) 
                 else
                    if Val_eqb k k' 
                    then m
                    else (k', v')::(map_insert k v ms)
end.

(** This function collapses a list of value pairs into a map *)
Fixpoint make_val_map (l: list (Val * Val)) : list (Val * Val) :=
match l with
| [] => []
| (k,v)::vs => map_insert k v (make_val_map vs)
end.

Goal make_val_map [(VLit 1%Z, VLit 1%Z);(VLit 1%Z, VLit 2%Z)] =
    [(VLit 1%Z, VLit 2%Z)].
Proof. simpl. reflexivity. Qed.

(**
  In this section, we define map flattening and deflattening (the inverse of
  flattening). For example:
                               flatten
  ~{1 => 2, 2 => 3, 3 => 4}~  =========> [1,2,2,3,3,4]
                              <=========
                              deflatten
*)
Section flattening.
  Context {A : Type}.

  (** This function flattens the map into a list by appending the elements in
      `key₁::value₁::key₂::value₂:: ...` order. *)
  Fixpoint flatten_list (l : list (A * A)) : list A :=
  match l with
  | [] => []
  | (x, y)::xs => x::y::(flatten_list xs)
  end.

  (** The flattened list has twice the length of the map *)
  Lemma length_flatten_list (l : list (A * A)) :
    length (flatten_list l) = length l * 2.
  Proof.
    induction l.
    * simpl. auto.
    * simpl. destruct a. simpl. lia.
  Qed.

  (** The inverse of flattening - works correctly only for lists of even length *)
  Fixpoint deflatten_list (l : list A) : list (A * A) :=
  match l with
  | [] => []
  | x::y::xs => (x, y)::deflatten_list xs
  | _ => []
  end.

  (** The length of the map created from a list is half the list's length. *)
  Lemma deflatten_length :
    forall (l : list A),
      length (deflatten_list l) = Nat.div2 (length l).
  Proof.
    induction l using list_length_ind; simpl; auto; destruct l; auto.
    destruct l; auto. simpl in *. rewrite H. 2: lia. lia.
  Qed.

  (** Inverse properties of `flatten` and `deflatten`. *)
  Theorem flatten_deflatten : forall (l : list (A * A)),
    deflatten_list (flatten_list l) = l.
  Proof.
    induction l; simpl; auto.
    * destruct a. simpl. now rewrite IHl.
  Qed.

  Theorem deflatten_flatten : forall n (l : list A),
    length l = 2 * n ->
    flatten_list (deflatten_list l) = l.
  Proof.
    induction n; simpl; intros l H.
    * apply length_zero_iff_nil in H. now subst.
    * replace (S (n + S (n + 0))) with (S (S (2 * n))) in H by nia.
      destruct l. inversion H. destruct l. inversion H.
      simpl length in H. simpl. rewrite IHn; [reflexivity|nia].
  Qed.

  (** List elements will respect the same properties after deflattening *)
  Lemma deflatten_keeps_prop (P : A -> Prop) :
    forall (l : list A),
      Forall P l ->
      Forall (fun x => P (fst x) /\ P (snd x)) (deflatten_list l).
  Proof.
    induction l using list_length_ind.
    intro HF.
    destruct l. 2: destruct l.
    * constructor.
    * cbn. constructor.
    * cbn. inversion HF. inversion H3. subst.
      clear HF H3. constructor; auto.
      apply H; simpl; auto.
  Qed.

  (** The previous property expressed with pattern matching *)
  Corollary deflatten_keeps_prop_match (P : A -> Prop) :
    forall (l : list A),
      Forall P l ->
      Forall (fun '(x, y) => P x /\ P y) (deflatten_list l).
  Proof.
    intros.
    apply deflatten_keeps_prop in H.
    eapply Forall_impl. 2: eassumption.
    intros. now destruct a.
  Qed.

  (** Flattening lists also do not affect propositions that were satsified by
      the list elements *)
  Lemma flatten_keeps_prop (P : A -> Prop) :
    forall (l : list (A * A)),
      Forall (fun '(x, y) => P x /\ P y) l ->
      Forall P (flatten_list l).
  Proof.
    induction l; intros; simpl in *; auto.
    destruct a.
    destruct_foralls. destruct H2. constructor; auto.
  Qed.

  (** Propositions with list pairs are also kept by deflattening *)
  Lemma deflatten_keeps_biprop_match :
    forall P (l1 : list A) (l2 : list A),
      list_biforall P l1 l2 ->
      list_biforall (fun '(x1, y1) '(x2, y2) => P x1 x2 /\ P y1 y2)  (deflatten_list l1) (deflatten_list l2).
  Proof.
    induction l1 using list_length_ind. intros.
    inv H0. constructor.
    inv H2. constructor. simpl.
    constructor.
    * now split.
    * apply H. slia. assumption.
  Qed.
End flattening.

(** Mapping and flattening can be swapped *)
Theorem flatten_map :
  forall T1 T2 (f : T1 -> T2) l,
    map f (flatten_list l) =
    flatten_list (map (fun '(x, y) => (f x, f y)) l).
Proof.
  intros T1 T2 f l.
  induction l as [| [x y] l' IH].
  - simpl.
    reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

(** Append and flattening can be swapped *)
Theorem flatten_app :
  forall T (l l' : list (T * T)),
    flatten_list (l ++ l') =
    (flatten_list l) ++ (flatten_list l').
Proof.
  intros T l l'.
  induction l as [| (x, y) l IH].
  - (* Base case: l is empty *)
    simpl.
    reflexivity.
  - (* Inductive case: l is non-empty *)
    simpl.
    rewrite IH.
    reflexivity.
Qed.

(** Mapping and deflattening can be swapped *)
Theorem deflatten_map :
  forall T1 T2 (f : T1 -> T2) l,
    map (fun '(x, y) => (f x, f y)) (deflatten_list l) =
    deflatten_list (map f l).
Proof.
  induction l using list_length_ind; simpl; auto.
  destruct l; simpl; auto.
  destruct l; simpl; auto.
  rewrite H. reflexivity. slia.
Qed.

(** Inserting a key-value pair into a map, all three respecting some proposition
    results in a map that still respects the proposition. *)
Lemma map_insert_prop :
  forall (P : Val * Val -> Prop) l k v,
    P (k, v) ->
    Forall P l ->
    Forall P (map_insert k v l).
Proof.
  induction l; intros k v HP HF.
  * constructor; auto.
  * simpl. destruct a as [k' v'].
    destruct_foralls.
    break_match_goal. 2: break_match_goal.
    - constructor. 2: constructor. all: auto.
    - constructor; auto.
    - constructor; auto.
Qed.

(**
  Creating a value map from a list of key-value pairs that all respect a
  proposition results in a map that still respects the proposition.
*)
Lemma make_val_map_keeps_prop (P : Val * Val -> Prop) :
  forall l,
    Forall P l ->
    Forall P (make_val_map l).
Proof.
  induction l; intro H.
  * constructor.
  * cbn. destruct a. inversion H. subst. clear H.
    apply IHl in H3. clear IHl.
    now apply map_insert_prop.
Qed.

(**
  Mapping and repeating are interchangeable.
*)
Theorem map_repeat {T Q : Type} :
  forall n (f : T -> Q) (x : T), map f (repeat x n) = repeat (f x) n.
Proof.
  induction n; intros; cbn; auto; now rewrite IHn.
Qed.
