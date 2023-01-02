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
