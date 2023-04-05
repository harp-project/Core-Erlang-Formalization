From CoreErlang Require Export Equalities.
Import ListNotations.

(** Building Val maps based on the Val ordering Val_less *)
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

(** Create maps without duplicates based on the ordering *)
Fixpoint make_val_map (l: list (Val * Val)) : list (Val * Val) :=
match l with
| [] => []
| (k,v)::vs => map_insert k v (make_val_map vs)
end.

Goal make_val_map [(VLit 1%Z, VLit 1%Z);(VLit 1%Z, VLit 2%Z)] =
    [(VLit 1%Z, VLit 2%Z)].
Proof. simpl. reflexivity. Qed.

Fixpoint flatten_list {A : Type} (l : list (A * A)) : list A :=
match l with
| [] => []
| (x, y)::xs => x::y::(flatten_list xs)
end.

Lemma length_flatten_list {A : Type} (l : list (A * A)) :
  length (flatten_list l) = length l * 2.
Proof.
  induction l.
  * simpl. auto.
  * simpl. destruct a. simpl. lia.
Qed.

Fixpoint deflatten_list {A : Type} (l : list A) : list (A * A) :=
match l with
| [] => []
| x::y::xs => (x, y)::deflatten_list xs
| _ => []
end.

Theorem flatten_deflatten : forall A (l : list (A * A)),
  deflatten_list (flatten_list l) = l.
Proof.
  induction l; simpl; auto.
  * destruct a. simpl. now rewrite IHl.
Qed.

Import PeanoNat.

Theorem deflatten_flatten : forall A n (l : list A),
  length l = 2 * n ->
  flatten_list (deflatten_list l) = l.
Proof.
  induction n; simpl; intros l H.
  * apply length_zero_iff_nil in H. now subst.
  * replace (S (n + S (n + 0))) with (S (S (2 * n))) in H by nia.
    destruct l. inversion H. destruct l. inversion H.
    simpl length in H. simpl. rewrite IHn; [reflexivity|nia].
Qed.

Lemma deflatten_keeps_prop {A} (P : A -> Prop) :
  forall (l : list A),
    Forall P l ->
    Forall (fun '(x, y) => P x /\ P y) (deflatten_list l).
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

Lemma flatten_keeps_prop {A} (P : A -> Prop) :
  forall (l : list (A * A)),
    Forall (fun '(x, y) => P x /\ P y) l ->
    Forall P (flatten_list l).
Proof.
  induction l; intros; simpl in *; auto.
  destruct a.
  destruct_foralls. destruct H2. constructor; auto.
Qed.
