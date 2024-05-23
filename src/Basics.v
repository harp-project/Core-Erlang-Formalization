(**
  This file includes a general lemmas and theorems about standard
  types and data structures. It also contains simple tactics to
  transform goals and hypotheses
 *)

Require Export Coq.micromega.Lia
               Coq.Lists.List
               Coq.Arith.PeanoNat.
Import ListNotations.

(**
  This tactic trasforms boolean equality between nats to propositional
  inside hypotheses
*)
Ltac eqb_to_eq_prim :=
  match goal with
  | [H : Nat.eqb _ _ = true  |- _] => apply Nat.eqb_eq  in H
  | [H : Nat.eqb _ _ = false |- _] => apply Nat.eqb_neq in H
  end.

Ltac eqb_to_eq := repeat eqb_to_eq_prim.

(** The following two tactics can be used to make case separation in the
    hypotheses or goals by infering the basis of the case separation from the
    context.
 *)
Ltac break_match_hyp :=
match goal with
| [ H : context [ match ?X with _=>_ end ] |- _] =>
     match type of X with
     | sumbool _ _=>destruct X
     | _=>destruct X eqn:? 
     end 
end.

Ltac break_match_goal :=
match goal with
| [ |- context [ match ?X with _=>_ end ] ] => 
    match type of X with
    | sumbool _ _ => destruct X
    | _ => destruct X eqn:?
    end
end.

(** The following tactic puts a function application on an equality hypothesis *)
Tactic Notation "put" constr(f) "on" constr(H) "as" ident(name) :=
match type of H with
| ?p = ?q => assert (name : f p = f q) by (now rewrite H + now setoid_rewrite H)
end.

(**
  A simple theorem about modulo 2 and addition of 2
 *)
Proposition modulo_2_plus_2 n :
  n mod 2 = S (S n) mod 2.
Proof.
  assert (S (S n) = n + 2). { lia. }
  rewrite H in *.
  epose (Nat.Div0.add_mod_idemp_r n 2 2).
  rewrite <- e. rewrite Nat.Div0.mod_same. rewrite Nat.add_0_r. auto.
  Unshelve.
  all: lia.
Qed.

Section lists.
  Context {T : Type}.

  (**
    An alternative phrasing for `Forall_forall` expressed with indexing
   *)
  Theorem indexed_to_forall (l : list T) : forall P def,
    Forall P l
  <->
    (forall i, i < Datatypes.length l -> P (nth i l def)).
  Proof.
    induction l; split; intros.
    * inversion H0.
    * constructor.
    * inversion H. subst. destruct i.
      - simpl. auto.
      - simpl. apply IHl. exact H4. simpl in H0. lia.
    * constructor.
      - apply (H 0). simpl. lia.
      - eapply IHl. intros. apply (H (S i)). simpl. lia.
  Qed.

  (**
    A non-empty list has a first element.
  *)
  Lemma element_exist : forall n (l : list T), S n = Datatypes.length l -> exists e l', l = e::l'.
  Proof.
    intros. destruct l.
    * inversion H.
    * apply ex_intro with t. apply ex_intro with l. reflexivity.
  Qed.

  (**
    Mapping the identity function does not affect the list
   *)
  Theorem map_id : forall (l : list T), List.map id l = l.
  Proof.
    induction l; simpl; try rewrite IHl; auto.
  Qed.

  (**
    A non-empty list has a last element.
  *)
  Theorem last_element_exists :
    forall (l: list T) n, S n = Datatypes.length l -> exists l' x, l = l' ++ [x].
  Proof.
    induction l; intros.
    * inversion H.
    * inversion H. destruct l.
      - exists [], a. reflexivity.
      - simpl in H1. epose (IHl (pred n) _). destruct e, H0. subst. rewrite H0.
        exists (a::x), x0. apply app_comm_cons. Unshelve. simpl. lia.
  Qed.

  (**
    The ith element of a concatenated list either comes from the first or the
    second part of the concatenation.
   *)
  Lemma nth_possibilities:
    forall (l1 l2 : list T) (def : T) i, i < length (l1 ++ l2) ->
      (nth i (l1 ++ l2) def = nth i l1 def) /\ i < length l1 \/
      nth i (l1 ++ l2) def = nth (i - length l1) l2 def /\ (i - length l1) < length l2 /\ i >= length l1.
  Proof.
    intros. destruct (i <? length l1) eqn:P.
    * apply Nat.ltb_lt in P. left. split; [ apply app_nth1 | ]; auto.
    * apply Nat.ltb_nlt in P. right. split; [ apply app_nth2 | rewrite app_length in H ]; lia.
  Qed.

  (**
    A list cannot be equal to itself extended with a new first element.
   *)
  Theorem cons_neq :
    forall (l : list T) e, e :: l = l -> False.
  Proof.
    induction l; intros; inversion H. eapply IHl. eauto.
  Qed.

  (**
    A list cannot be equal to itself extended with two new first element.
   *)
  Lemma cons_cons_neq :
    forall (l : list T) a b, l = a :: b :: l -> False.
  Proof.
    induction l; intros; inversion H.
    eapply IHl. eauto.
  Qed.

  (**
    If a value is not an element of two lists, iff it is not an element
    of the concatenation of these lists.
   *)
  Corollary app_not_in : forall (x:T) (l1 l2 : list T),
    ~In x l1 -> ~In x l2 -> ~In x (l1 ++ l2).
  Proof.
    intros.
    intro. eapply in_app_or in H1. destruct H1; contradiction.
  Qed.

  Theorem not_in_app :
    forall (l1 l2 : list T) x, ~In x (l1 ++ l2) ->
    ~In x l1 /\ ~In x l2.
  Proof.
    induction l1; intros.
    * simpl in *. intuition.
    * simpl in *. apply Decidable.not_or in H as [H1 H2]. apply IHl1 in H2 as [H2 H3].
      intuition.
  Qed.


  (**
    Folding concatenation in the middle of a list.
  *)
  Lemma app_cons_fold : forall (l l' : list T) (a : T),
    l ++ a::l' = l ++ [a] ++ l'.
  Proof.
    firstorder.
  Qed.

  (**
    Two lists cannot be equal, if the first one is a suffix of the
    second (which includes an additional element).
  *)
  Theorem list_app_neq :
    forall (l2 l1 : list T) t, l1 = l2 ++ t :: l1 -> False.
  Proof.
    intros. assert (length l1 = length (l2 ++ t :: l1)). { rewrite H at 1. auto. }
    rewrite app_length in H0. simpl in H0. lia.
  Qed.

  (**
    A predicate is satisfied by all transformed list elements, if it is satisfied
    by the original list elements, and the predicate is kept by the transformation.
   *)
  Lemma Forall_map (l : list T) : forall (P : T -> Prop) (f : T -> T),
    (forall x, P x -> P (f x))
  ->
    Forall P l -> Forall P (map f l).
  Proof.
    induction l; intros; constructor;
    inversion H0; subst. auto.
    apply IHl; auto.
  Qed.

  (**
    The opposite direction of the previous lemma.
  *)
  Lemma map_Forall (l : list T) : forall (P : T -> Prop) (f : T -> T),
    (forall x, P (f x) -> P x)
  ->
    Forall P (map f l) -> Forall P l.
  Proof.
    induction l; intros; constructor;
    inversion H0; subst. auto.
    eapply IHl; eauto.
  Qed.

  (**
    A repeated list's elements satisfy a property when the repeated element satisfies it.
   *)
  Lemma Forall_repeat (P : T -> Prop) (v : T) (n : nat):
    P v ->
    Forall P (repeat v n).
  Proof.
    induction n; simpl; intros; constructor.
    * assumption.
    * now apply IHn.
  Qed.

  (** Folding lemma for the length of non-empty lists. *)
  Lemma length_fold (a2 : T) (n : nat) (l2 : list T):
    n = length l2
    ->
    S n = length (a2 :: l2).
  Proof.
    intros. simpl. rewrite H. auto.
  Qed.

  (**
    Dropping the first `n` elements of a list is the same, as appending the
    `n`th element in front of the list obtained by dropping `(1 + n)` elements.
  *)
  Lemma skipn_S :
    forall n (l : list T) d,
    length l > n ->
    skipn n l = nth n l d :: skipn (S n) l.
  Proof.
    induction n; intros; destruct l; simpl in *; try lia.
    reflexivity.
    erewrite IHn. reflexivity. lia.
  Qed.

  (**
    If two lists are equal, their reverse is equal too
  *)
  Lemma eq_rev :
    forall (l1 l2 : list T), rev l1 = rev l2 -> l1 = l2.
  Proof.
    intros.
    rewrite <- (rev_involutive l1).
    rewrite <- (rev_involutive l2).
    now f_equal.
  Qed.

  (**
    The following lemma is used for the signal ordering guarantee of Erlang.
    If two _fresh_ elements are appended at the end of a list, then is is not
    possible that they appear in the list in an opposite order.
   *)
  Lemma in_list_order :
    forall (l : list T) x1 x2, ~In x1 l -> ~In x2 l -> x1 <> x2 ->
    forall l1 l2 l3, l ++ [x1; x2] <> l1 ++ x2::l2 ++ x1 :: l3.
  Proof.
    induction l; simpl app; intros; intro.
    * destruct l1; simpl.
      - inversion H2. congruence.
      - inversion H2; subst. destruct l1; inversion H5.
        + destruct l2; inversion H4.
        + destruct l1; inversion H6.
    * destruct l1; simpl app in *.
      - inversion H2; subst; clear H2. apply H0. constructor. auto.
      - inversion H2. apply IHl in H5; auto.
        intro. apply H. now constructor 2.
        intro. apply H0. now constructor 2.
  Qed.

  (** Membership in option lists *)
  Definition option_In (x : T) l := option_map (In x) l <> None.

  (**
    Custom induction scheme for lists based on their length, rather than their
    structure.
  *)
  Section list_length_ind.
    Variable P : list T -> Prop.

    Hypothesis H : forall xs, (forall l, length l < length xs -> P l) -> P xs.

    Theorem list_length_ind : forall xs, P xs.
    Proof.
      assert (forall xs l : list T, length l <= length xs -> P l) as H_ind.
      { induction xs; intros l Hlen; apply H; intros l0 H0.
        - inversion Hlen. lia.
        - apply IHxs. simpl in Hlen. lia.
      }
      intros xs.
      apply H_ind with (xs := xs).
      lia.
    Qed.
  End list_length_ind.

End lists.

Section list_biforall.
  Context {T U : Type}.
  (**
    Two lists are pairwise related by a binary relation `P`. Alternatively,
    this definition is equivalent to `Forall (uncurry P)`
   *)
  Inductive list_biforall (P : T -> U -> Prop) : list T -> list U -> Prop :=
  | biforall_nil : list_biforall P [] []
  | biforall_cons hd hd' tl tl' : P hd hd' -> list_biforall P tl tl' -> list_biforall P (hd::tl) (hd'::tl').

  (**
    The `list_biforall` predicate extended to `option (list _)`.
    Either both values are `None`, or both are lists pairwise related
    by `P.`
  *)
  Definition option_list_biforall P (o1 : option (list T))
                                    (o2 : option (list U)) :=
  match o1, o2 with
  | Some l1, Some l2 => list_biforall P l1 l2
  | None, None => True
  | _, _ => False
  end.

  (**
    Alternative definition of pairwise relation with indexing.
  *)
  Theorem indexed_to_biforall : forall (P : T -> U -> Prop) (l1 : list T) (l2 : list U) (d1 : T) (d2 : U),
     list_biforall P l1 l2 <-> (forall i, i < length l1 -> P (nth i l1 d1) (nth i l2 d2)) /\ length l1 = length l2.
  Proof.
    split; intros.
    * induction H.
      - split; intros; auto. inversion H.
      - destruct IHlist_biforall. split. 2: simpl; lia. destruct i; intros.
        + exact H.
        + apply H1. simpl in H3. lia.
    * destruct H. revert H0 H. generalize dependent l2. generalize dependent d1.
      generalize dependent d2. induction l1; intros.
      - simpl in H0. apply eq_sym, length_zero_iff_nil in H0. subst. constructor.
      - simpl in H0. eapply element_exist in H0 as G. destruct G, H1. subst. inversion H0.
        constructor. apply (H 0); simpl; lia. eapply IHl1; auto. intros. apply (H (S i)).
        simpl. lia.
  Qed.

  (**
    If two lists pairwise satisfy a predicate, they have equal length.
  *)
  Theorem biforall_length :
    forall (es : list T) (es' : list U) P, list_biforall P es es' -> length es = length es'.
  Proof.
    intros. induction H; auto. simpl. auto.
  Qed.

  (**
    The predicate - that is pairwise satisfied by two lists - can be
    weakened
   *)
  Lemma biforall_impl : forall (l1 : list T) (l2 : list U) (P Q : T -> U -> Prop),
    (forall x y, P x y -> Q x y) ->
    list_biforall P l1 l2 -> list_biforall Q l1 l2.
  Proof.
    induction l1; intros; inversion H0; constructor; subst.
    now apply H.
    eapply IHl1; eauto.
  Qed.

  (**
    The same weakening property for option lists.
   *)
  Corollary option_biforall_impl : forall l1 l2 (P Q : T -> U -> Prop),
    (forall x y, P x y -> Q x y) ->
    option_list_biforall P l1 l2 -> option_list_biforall Q l1 l2.
  Proof.
    intros. destruct l1, l2; auto; simpl in *.
    eapply biforall_impl; eassumption.
  Qed.

  (**
    The predicate pairwise satisfied by two lists can be weakened. It
    is enough, if the weakening holds for the list elements.
   *)
  Lemma biforall_ext : forall (l1 : list T) (l2 : list U) (P Q : T -> U -> Prop),
    (forall x y, In x l1 -> In y l2 -> P x y -> Q x y) ->
    list_biforall P l1 l2 -> list_biforall Q l1 l2.
  Proof.
    induction l1; intros; inversion H0; constructor; subst.
    apply H; cbn; try apply elem_of_list_here; auto.
    eapply IHl1. 2: eassumption. intros.
    apply H; try constructor 2; try apply elem_of_list_further; auto.
  Qed.

  (**
    The previous weaking lemma expressed for option lists.
   *)
  Corollary option_biforall_ext : forall l1 l2 (P Q : T -> U -> Prop),
    (forall x y, option_In x l1 -> option_In y l2 -> P x y -> Q x y) ->
    option_list_biforall P l1 l2 -> option_list_biforall Q l1 l2.
  Proof.
    intros. destruct l1, l2; auto; simpl in *.
    eapply biforall_ext; try eassumption.
    intros. apply H; now cbn.
  Qed.

  (**
    Connection between a predicate that is satisfied by a pair of lists and
    concatenation.
  *)
  Lemma biforall_app : forall (l1 l1' : list T) (l2 l2' : list U) P,
    list_biforall P l1 l2 -> list_biforall P l1' l2'
  ->
    list_biforall P (l1 ++ l1') (l2 ++ l2').
  Proof.
    induction l1; intros.
    * inversion H. auto.
    * inversion H. subst. do 2 rewrite <- app_comm_cons. constructor; auto. 
  Qed.

  (**
    Two lemmas that convert `list_biforall` into indexing and vice versa.
   *)
  Lemma biforall_forall (P : T -> U -> Prop) (l1 : list T)
    (l2 : list U) (d1 : T) (d2 : U) :
    list_biforall P l1 l2 ->
    (forall i, i < length l1 -> P (nth i l1 d1) (nth i l2 d2)).
  Proof.
    intro. induction H; intros.
    * inversion H.
    * simpl in *. destruct i.
      - assumption.
      - apply IHlist_biforall. nia.
  Qed.

  Lemma forall_biforall (P : T -> U -> Prop) (l1 : list T)
    (l2 : list U) (d1 : T) (d2 : U) :
    length l1 = length l2 ->
    (forall i, i < length l1 -> P (nth i l1 d1) (nth i l2 d2)) ->
    list_biforall P l1 l2.
  Proof.
    revert l2. induction l1; destruct l2; intros.
    * constructor.
    * inversion H.
    * inversion H.
    * simpl in H. constructor.
      - apply (H0 0). simpl. lia.
      - apply IHl1. lia. intros. apply (H0 (S i)). simpl. lia.
  Qed.

End list_biforall.

(**
  Connection between a predicate that is satisfied by a pair of lists and
  list transformation (with `map`).
*)
Lemma biforall_map :
  forall {T1 T2 T1' T2'} l l' f1 f2 (P : T1 -> T2 -> Prop) (Q : T1' -> T2' -> Prop),
  list_biforall P l l' ->
  (forall x y, P x y -> Q (f1 x) (f2 y))
->
  list_biforall Q (map f1 l) (map f2 l').
Proof.
  induction l; intros; inversion H; simpl; constructor; subst.
  * inversion H. subst. apply H0; auto.
  * eapply IHl; eauto.
Qed.

(**
  The previous lemma expressed for option lists.
*)
Corollary option_biforall_map :
  forall {T1 T2 T1' T2'} l l' f1 f2 (P : T1 -> T2 -> Prop) (Q : T1' -> T2' -> Prop),
  option_list_biforall P l l' ->
  (forall x y, P x y -> Q (f1 x) (f2 y))
->
  option_list_biforall Q (option_map (map f1) l) (option_map (map f2) l').
Proof.
  intros. destruct l, l'; simpl in *; auto.
  eapply biforall_map; eassumption.
Qed.

(**
  If all elements of a list are reflexively related, then this can both be expressed
  with `Forall` and `list_biforall` (and `option_biforall`).
*)
Lemma biforall_forall_refl : forall {T} (l: list T) P, list_biforall P l l -> Forall (fun x => P x x) l.
Proof.
  induction l; constructor; inversion H; subst; auto.
Qed.

Lemma forall_biforall_refl : forall {T} (l: list T) P, Forall (fun x => P x x) l -> list_biforall P l l.
Proof.
  induction l; constructor; inversion H; subst; auto.
Qed.


Corollary option_biforall_refl :
  forall {T1} l (P : T1 -> T1 -> Prop),
    (forall x, option_In x l -> P x x) ->
    option_list_biforall P l l.
Proof.
  intros. destruct l; simpl; auto.
  apply forall_biforall_refl.
  apply Forall_forall. intros. now apply H.
Qed.

(**
  If a relation is transitive, list predicates constructed with it are also
  transitive.
 *)
Lemma biforall_trans :
  forall {T1} l l' l'' (P : T1 -> T1 -> Prop),
    (forall x y z, P x y -> P y z -> P x z) ->
    list_biforall P l l' -> list_biforall P l' l'' -> list_biforall P l l''.
Proof.
  intros. generalize dependent l''. induction H0; intros.
  * inversion H1. subst. constructor.
  * inversion H2. subst. apply IHlist_biforall in H7.
    constructor; auto.
    eapply H; eassumption.
Qed.

(**
  The transitivity expressed for option lists.
 *)
Corollary option_biforall_trans :
  forall {T1} l l' l'' (P : T1 -> T1 -> Prop),
    (forall x y z, P x y -> P y z -> P x z) ->
    option_list_biforall P l l' -> option_list_biforall P l' l'' -> option_list_biforall P l l''.
Proof.
  intros. destruct l, l', l''; simpl in *.
  all: try now inversion H0.
  eapply biforall_trans; eassumption.
Qed.

(**
  A general observation about swapping the order of `fold_left` and `map`. For this
  we need a homomorphism.
*)
Theorem fold_left_map :
  forall (T T2 T3 : Type) (l : list T) f (f2 : T -> T2 -> T3 -> T) d t2 t3,
  (forall a b t2 t3, f2 (f a b) t2 t3 = f (f2 a t2 t3) (f2 b t2 t3)) ->
  f2 (fold_left f l d) t2 t3 = fold_left f (map (fun x => f2 x t2 t3) l) (f2 d t2 t3).
Proof.
  induction l; intros; auto.
  intros. cbn.
  rewrite IHl; auto. rewrite H. auto.
Qed.

(**
  Mapping a constant function is the same as repeating the constant.
*)
Theorem map_const :
  forall {T T2} (l : list T) (a : T2), map (fun _ => a) l = repeat a (length l).
Proof.
  induction l; intros.
  auto.
  simpl. rewrite IHl. auto.
Qed.

(**
  Another lemma on the connection between indexing and `Forall`.
 *)
Lemma Forall_pair {A B} (P1 : A -> Prop) (P2 : B -> Prop) l : forall d1 d2,
  (forall i : nat,
  i < Datatypes.length l -> P1 (nth i (map fst l) d1)) ->
  (forall i : nat,
    i < Datatypes.length l -> P2 (nth i (map snd l) d2)) ->
  Forall (fun '(x, y) => P1 x /\ P2 y) l.
Proof.
  induction l; intros; constructor.
  * destruct a. split. apply (H 0). simpl. lia. apply (H0 0). simpl. lia.
  * eapply IHl; intros.
    apply (H (S i)). simpl. lia.
    apply (H0 (S i)). simpl. lia.
Qed.

(**
  Extensionality property for lists expressed with indexing
 *)
Lemma mapeq_if_ntheq :
  forall {A B : Type} (f : A -> B) (g : A -> B) (l : list A) (d : B),
  map f l = map g l <->
  forall i, i < length l -> nth i (map f l) d = nth i (map g l) d.
Proof.
  split.
  * intros. f_equal. assumption.
  * intros. induction l.
    - simpl. reflexivity.
    - simpl. f_equal.
      + specialize (H 0). simpl in H.
        specialize (H (Nat.lt_0_succ (Datatypes.length l))). assumption.
      + apply IHl. intros. specialize (H (S i)).
        remember (nth (S i) (map f (a :: l)) d = nth (S i) (map g (a :: l)) d)
        as F.
        simpl in H. specialize (H ltac:(lia)). subst. auto.
Qed.

(*
(* if there is two identical hypotheses then this tac will clear one *)
Ltac proof_irr :=
match goal with
| [H1 : ?P, H2 : ?P |- _] => assert (H1 = H2) by apply proof_irrelevance; subst
end.
Ltac proof_irr_many := repeat proof_irr. *)

(** The following two tactics deconstruct `Forall` hypotheses *)
Ltac destruct_forall :=
  match goal with
  | [H : Forall _ (_ :: _) |- _] => inversion H; subst; clear H
  | [H : Forall _ [] |- _] => clear H
  end.

Ltac destruct_foralls := repeat destruct_forall.

(** The following tactics are macros for commonly used tactic combinations
    to ease proofs. *)
Ltac inv H := inversion H; subst; clear H.
Ltac slia := simpl; lia.
Ltac snia := simpl; nia.
Ltac destruct_all_hyps := repeat break_match_hyp; try congruence; subst.

(** In Scoping.v there are a number of theorems, which should not appear
    in search lists (because they are too long). *)
Add Search Blacklist "_ind2"
                 "coped_ind"
                 "coped_sind"
                 "FCLOSED_ind"
                 "FCLOSED_sind"
                 "Unnamed_thm".

(** Function application for pairs *)
Definition applyBoth {A B : Type} (f : A -> B) (p : A * A) : B * B :=
  match p with
  | (a1, a2) => (f a1, f a2)
  end.

(** Prop satisfaction for pairs *)
Definition PBoth {A : Type} (P : A -> Prop) (p : A * A) : Prop :=
  P (fst p) /\ P (snd p).

(** First projection for list of pairs in case of `PBoth` *)
Lemma PBoth_left :
  forall {A : Set} (l : list (A * A)) (P : A -> Prop), Forall (PBoth P) l -> Forall P (map fst l).
Proof.
  intros. induction H; simpl; constructor.
  now inv H.
  auto.
Qed.

(** Second projection for list of pairs in case of `PBoth` *)
Lemma PBoth_right :
  forall {A : Set} (l : list (A * A)) (P : A -> Prop), Forall (PBoth P) l -> Forall P (map snd l).
Proof.
  intros. induction H; simpl; constructor.
  now inv H.
  auto.
Qed.

(**
  Another hypothesis deconstruction tactic (for exists and conjunction).
*)
Ltac destruct_hyp :=
  match goal with
  | [H : exists _, _ |- _] => destruct H
  | [H : _ /\ _ |- _] => destruct H
  end.

Ltac destruct_hyps := repeat destruct_hyp.

(**
  Simple inversion tactic for equality of option types or product types
*)
Ltac invSome :=
match goal with
| [H : Some _ = Some _ |- _] => inv H
| [H : Some _ = None |- _] => inv H
| [H : None = Some _ |- _] => inv H
| [H : (_, _) = (_, _) |- _] => inv H
end.


(** stdpp's notation for projections *)
Notation "p .1" := (fst p) (at level 2, left associativity, format "p .1").
Notation "p .2" := (snd p) (at level 2, left associativity, format "p .2").

(**
  This function replaces the `i`th element of a list, if it exists.
*)
Fixpoint replace_nth_error {A : Type} (l : list A) (i : nat) (e : A) : option (list A) :=
match i, l with
| 0, x::xs => Some (e::xs)
| _, [] => None
| S n, x::xs => match (replace_nth_error xs n e) with
               | None => None
               | Some l' => Some (x::l')
               end
end.

(**
  Replacing the `i`th element of a list is swappable with mapping.
*)
Lemma replace_nth_error_map :
  forall A B (f : A -> B) l n e,
    replace_nth_error (map f l) n (f e) = option_map (map f) (replace_nth_error l n e).
Proof.
  induction l; intros; simpl; destruct n; try reflexivity.
  * rewrite IHl. now destruct replace_nth_error.
Qed.

(**
  Two lemma about first and second projections of list zipping.
*)
Lemma fst_combine :
  forall {A B} (l : list A) (l' : list B),
    length l <= length l' ->
    map fst (combine l l') = l.
Proof.
  induction l; destruct l'; simpl; intros.
  1-2: reflexivity.
  1: lia.
  f_equal. apply IHl. lia.
Qed.

Lemma snd_combine :
  forall {A B} (l : list A) (l' : list B),
    length l' <= length l ->
    map snd (combine l l') = l'.
Proof.
  induction l; destruct l'; simpl; intros.
  1,3: reflexivity.
  1: lia.
  f_equal. apply IHl. lia.
Qed.

(**
  Case separation tactics for boolean operations
*)
Ltac destruct_bool :=
  match goal with
  | [H : orb  _ _ = true  |- _] => apply Bool.orb_true_iff in H as [? | ?]
  | [H : orb  _ _ = false |- _] => apply Bool.orb_false_iff in H as [? ?]
  | [H : andb _ _ = true  |- _] => apply Bool.andb_true_iff in H as [? ?]
  | [H : andb _ _ = false |- _] => apply Bool.andb_false_iff in H as [? | ?]
  end.
Ltac destruct_bools := repeat destruct_bool.


(**
  Tactic to deconstruct `~In` hypotheses
*)
Ltac destruct_not_in_base :=
  match goal with
  | [H : ~In _ (_ ++ _) |- _] => apply not_in_app in H as [? ?]
  end.
Ltac destruct_not_in := repeat destruct_not_in_base.

(**
  If an element is not in any list created from the elements of a list, then
  this element is not a member of the `flat_map` of the previous list.
 *)
Lemma foldr_not_in_Forall :
  forall {A B} (f : A -> list B) (l : list A) y b,
    Forall (fun x => ~In y (f x)) l /\ ~In y b <->
    ~In y (fold_right (fun x acc => f x ++ acc) b l).
Proof.
  induction l; intros; split; intros; auto.
  {
    inv H. simpl in *. congruence.
  }
  {
    simpl in *. inv H. inv H0.
    intro. apply in_app_iff in H as [? | ?]. congruence.
    apply (IHl y b) in H; auto.
  }
  {
    simpl in H. destruct_not_in.
    apply (IHl y b) in H0. destruct H0.
    repeat constructor; auto.
  }
Qed.
