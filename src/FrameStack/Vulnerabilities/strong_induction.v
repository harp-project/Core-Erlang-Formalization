From stdpp Require Import list.

Import ListNotations.

Lemma asd : forall a b c,
  a + (b + c) = (a + b) + c.
Proof.
  Search lt nat "ind".
  induction a using lt_wf_ind.
  destruct a; intros; simpl.
  * reflexivity.
  * rewrite H. reflexivity. lia.
Qed.

Print asd.

Section list_length_ind.
  Variable T : Type.
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

Goal forall {T : Set} (xs ys zs : list T),
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
Proof.
  Check list_length_ind.
  induction xs using list_length_ind.
  destruct xs; simpl; intros.
  * reflexivity.
  * rewrite H. reflexivity.
    simpl. lia.
Qed.

Inductive pal {X : Type} : list X -> Prop :=
  | emptypal : pal []
  | singlpal : forall x, pal [x]
  | inducpal : forall x l, pal l -> pal (x :: l ++ [x]).

Lemma list_two_step_ind {A} (P : list A -> Prop)
  (P_nil : P []) (P_cons : forall x, P [x])
  (P_cons_cons : forall x l x', P l -> P (x :: l ++ [x'])) :
  forall l, P l.
Proof.
  intros. remember (length l) as n. symmetry in Heqn. generalize dependent l.
  Search "pair_induction".
  induction n using Nat.pair_induction.

Theorem palindrome3 : forall {X : Type} (l : list X),
  l = rev l -> pal l.
Proof.
  intros. induction l.
  - apply emptypal.
  - inversion H.
  - inversion H.

