From CoreErlang Require Export Equalities.
Import ListNotations.

Section map_builders.

(** Building Val maps based on the Val ordering Val_less *)
Fixpoint map_insert (k v : Val) (kl : list Val) (vl : list Val) : (list Val) * (list Val) :=
match kl, vl with
| [], [] => ([k], [v])
| k'::ks, v'::vs => if Val_ltb k k' 
                    then (k::k'::ks, v::v'::vs) 
                    else
                       if Val_eqb k k' 
                       then (k'::ks, v'::vs) 
                       else (k'::(fst (map_insert k v ks vs)), v'::(snd (map_insert k v ks vs)))
| _, _ => ([], [])
end.

(** Create maps without duplicates based on the ordering *)
Fixpoint make_val_map (kl vl : list Val) : (list Val) * (list Val) :=
match kl, vl with
| [], [] => ([], [])
| k::ks, v::vs => map_insert k v (fst (make_val_map ks vs)) (snd (make_val_map ks vs))
| _, _ => ([], [])
end.

(* Compute make_val_map [VLit (Integer 5); VLit (Integer 5); VLit (Atom ""%string)] 
                       [VLit (Integer 5); VLit (Integer 7); VLit (Atom ""%string)]. *)

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

Fixpoint make_map_vals (l l' : list Val) : list Val  :=
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

Fixpoint make_map_vals_inverse (l : list Val) : option (list Val * list Val) :=
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

End map_builders.
