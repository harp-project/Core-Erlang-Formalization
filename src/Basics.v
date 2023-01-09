Require Export Coq.micromega.Lia
               Coq.Lists.List
               Coq.Arith.PeanoNat
               Logic.ProofIrrelevance.
Import ListNotations.

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

Theorem indexed_to_forall {A : Type} (l : list A) : forall P def,
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

Lemma element_exist {A : Type} : forall n (l : list A), S n = Datatypes.length l -> exists e l', l = e::l'.
Proof.
  intros. destruct l.
  * inversion H.
  * apply ex_intro with a. apply ex_intro with l. reflexivity.
Qed.

Theorem map_id {T} : forall (l : list T), List.map id l = l.
Proof.
  induction l; simpl; try rewrite IHl; auto.
Qed.

Theorem last_element_exists {T} :
  forall (l: list T) n, S n = Datatypes.length l -> exists l' x, l = l' ++ [x].
Proof.
  induction l; intros.
  * inversion H.
  * inversion H. destruct l.
    - exists [], a. reflexivity.
    - simpl in H1. epose (IHl (pred n) _). destruct e, H0. subst. rewrite H0.
      exists (a::x), x0. apply app_comm_cons. Unshelve. simpl. lia.
Qed.

Inductive list_biforall {T1 T2 : Type} (P : T1 -> T2 -> Prop) : list T1 -> list T2 -> Prop :=
| biforall_nil : list_biforall P [] []
| biforall_cons hd hd' tl tl' : P hd hd' -> list_biforall P tl tl' -> list_biforall P (hd::tl) (hd'::tl').

Theorem indexed_to_biforall {T1 T2 : Type} : forall (P : T1 -> T2 -> Prop) (l1 : list T1) (l2 : list T2) (d1 : T1) (d2 : T2),
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
    - simpl in H0. apply element_exist in H0 as G. destruct G, H1. subst. inversion H0.
      constructor. apply (H 0); simpl; lia. eapply IHl1; auto. intros. apply (H (S i)).
      simpl. lia.
Qed.

Theorem biforall_length :
  forall {T1 T2 : Type} (es : list T1) (es' : list T2) P, list_biforall P es es' -> length es = length es'.
Proof.
  intros. induction H; auto. simpl. auto.
Qed.

Lemma biforall_impl : forall {T1 T2} (l1 : list T1) (l2 : list T2) (P Q : T1 -> T2 -> Prop),
  (forall x y, P x y -> Q x y) ->
  list_biforall P l1 l2 -> list_biforall Q l1 l2.
Proof.
  induction l1; intros; inversion H0; constructor; subst.
  now apply H.
  eapply IHl1; eauto.
Qed.

Lemma biforall_app : forall {T1 T2} (l1 l1' : list T1) (l2 l2' : list T2) P,
  list_biforall P l1 l2 -> list_biforall P l1' l2'
->
  list_biforall P (l1 ++ l1') (l2 ++ l2').
Proof.
  induction l1; intros.
  * inversion H. auto.
  * inversion H. subst. do 2 rewrite <- app_comm_cons. constructor; auto. 
Qed.

Lemma biforall_map :
  forall {T1 T2 T1' T2'} l l' f1 f2 (P : T1 -> T2 -> Prop) (Q : T1' -> T2' -> Prop), list_biforall P l l' ->
  (forall x y, P x y -> Q (f1 x) (f2 y))
->
  list_biforall Q (map f1 l) (map f2 l').
Proof.
  induction l; intros; inversion H; simpl; constructor; subst.
  * inversion H. subst. apply H0; auto.
  * eapply IHl; eauto.
Qed.

Lemma biforall_forall_refl : forall {T} (l: list T) P, list_biforall P l l -> Forall (fun x => P x x) l.
Proof.
  induction l; constructor; inversion H; subst; auto.
Qed.

Lemma forall_biforall_refl : forall {T} (l: list T) P, Forall (fun x => P x x) l -> list_biforall P l l.
Proof.
  induction l; constructor; inversion H; subst; auto.
Qed.

Lemma nth_possibilities {T : Type}:
  forall (l1 l2 : list T) (def : T) i, i < length (l1 ++ l2) ->
    (nth i (l1 ++ l2) def = nth i l1 def) /\ i < length l1 \/
    nth i (l1 ++ l2) def = nth (i - length l1) l2 def /\ (i - length l1) < length l2.
Proof.
  intros. destruct (i <? length l1) eqn:P.
  * apply Nat.ltb_lt in P. left. split; [ apply app_nth1 | ]; auto.
  * apply Nat.ltb_nlt in P. right. split; [ apply app_nth2 | rewrite app_length in H ]; lia.
Qed.

Lemma nth_possibilities_alt {T : Type}:
  forall (l1 l2 : list T) (def : T) i, i < length (l1 ++ l2) ->
    (nth i (l1 ++ l2) def = nth i l1 def) /\ i < length l1 \/
    nth i (l1 ++ l2) def = nth (i - length l1) l2 def /\ (i - length l1) < length l2 /\ i >= length l1.
Proof.
  intros. destruct (i <? length l1) eqn:P.
  * apply Nat.ltb_lt in P. left. split; [ apply app_nth1 | ]; auto.
  * apply Nat.ltb_nlt in P. right. split; [ apply app_nth2 | rewrite app_length in H ]; lia.
Qed.

Definition Injective {A B} (f : A->B) :=
 forall x y, f x = f y -> x = y.

Theorem map_not_in {T T' : Type} : forall (l : list T) (x: T) (f : T -> T'),
  Injective f -> ~In x l -> ~In (f x) (map f l).
Proof.
  induction l; intros; intro.
  * inversion H1.
  * inversion H1.
    - apply H in H2. subst. apply H0. intuition.
    - eapply IHl; eauto. apply not_in_cons in H0. destruct H0. auto.
Qed.

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

Theorem cons_neq :
  forall {T:Type}(l : list T) e, e :: l = l -> False.
Proof.
  induction l; intros; inversion H. eapply IHl. eauto.
Qed.

Lemma cons_cons_neq :
  forall {T : Type} (l : list T) a b, l = a :: b :: l -> False.
Proof.
  induction l; intros; inversion H.
  eapply IHl. eauto.
Qed.

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

Corollary app_not_in {T : Type} : forall (x:T) (l1 l2 : list T),
  ~In x l1 -> ~In x l2 -> ~In x (l1 ++ l2).
Proof.
  intros.
  intro. eapply in_app_or in H1. destruct H1; contradiction.
Qed.

Theorem app_cons_swap {T : Type} : forall (l l' : list T) (a : T),
  l ++ a::l' = l ++ [a] ++ l'.
Proof.
  firstorder.
Qed.

Theorem list_app_neq :
  forall {T : Type} (l2 l1 : list T) t, l1 = l2 ++ t :: l1 -> False.
Proof.
  intros. assert (length l1 = length (l2 ++ t :: l1)). { rewrite H at 1. auto. }
  rewrite app_length in H0. simpl in H0. lia.
Qed.

Theorem fold_left_map :
  forall (T T2 T3 : Type) (l : list T) f (f2 : T -> T2 -> T3 -> T) d t2 t3,
  (forall a b t2 t3, f2 (f a b) t2 t3 = f (f2 a t2 t3) (f2 b t2 t3)) ->
  f2 (fold_left f l d) t2 t3 = fold_left f (map (fun x => f2 x t2 t3) l) (f2 d t2 t3).
Proof.
  induction l; intros; auto.
  intros. cbn.
  rewrite IHl; auto. rewrite H. auto.
Qed.

Theorem map_const :
  forall {T T2} (l : list T) (a : T2), map (fun _ => a) l = repeat a (length l).
Proof.
  induction l; intros.
  auto.
  simpl. rewrite IHl. auto.
Qed.

Lemma Forall_map T (l : list T) : forall (P : T -> Prop) (f : T -> T),
  (forall x, P x -> P (f x))
->
  Forall P l -> Forall P (map f l).
Proof.
  induction l; intros; constructor;
  inversion H0; subst. auto.
  apply IHl; auto.
Qed.

Lemma map_Forall T (l : list T) : forall (P : T -> Prop) (f : T -> T),
  (forall x, P (f x) -> P x)
->
  Forall P (map f l) -> Forall P l.
Proof.
  induction l; intros; constructor;
  inversion H0; subst. auto.
  eapply IHl; eauto.
Qed.

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


(* if there is two identical hypotheses then this tac will clear one *)
Ltac proof_irr :=
match goal with
| [H1 : ?P, H2 : ?P |- _] => assert (H1 = H2) by apply proof_irrelevance; subst
end.
Ltac proof_irr_many := repeat proof_irr.

Ltac destruct_forall :=
  match goal with
  | [H : Forall _ (_ :: _) |- _] => inversion H; subst; clear H
  | [H : Forall _ [] |- _] => clear H
  end.

Ltac destruct_foralls := repeat destruct_forall.

Ltac inv H := inversion H; subst; clear H.
Ltac slia := simpl; lia.
Ltac snia := simpl; nia.
Ltac destruct_all_hyps := repeat break_match_hyp; try congruence; subst.

Add Search Blacklist "_ind2"
                 "coped_ind"
                 "coped_sind"
                 "FCLOSED_ind"
                 "FCLOSED_sind"
                 "Unnamed_thm".