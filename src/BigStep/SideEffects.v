From CoreErlang Require Export Environment Helpers Syntax.

(** The side-effects of Core Erlang *)
Import ListNotations.

Inductive SideEffectId : Set :=
| Input
| Output
.

Definition SideEffectList : Type := list (SideEffectId * list Value).

Definition nth_def {A : Type} (l : list A) (def err : A) (i : nat) :=
match i with
| 0 => def
| S i' => nth i' l err
end.

Goal nth_def [4; 7; 8] 3 0 2 = 7. Proof. reflexivity. Qed.
Goal nth_def [ [(Input, [VLit (Atom "a"%string)] )];
                  [(Input, [VLit (Atom "a"%string)] ); (Input, [VLit (Atom "b"%string)] )]; 
                  [(Input, [VLit (Atom "a"%string)] ); (Input, [VLit (Atom "b"%string)] ); (Input, [VLit (Atom "c"%string)] )]] [] [] 2 = [(Input, [VLit (Atom "a"%string)] ); (Input, [VLit (Atom "b"%string)] )]. Proof. reflexivity. Qed.

Lemma nth_def_eq {A : Type} (l : list A) (i : nat) (e1 def err : A):
  nth_def (e1::l) def err (S i) = nth_def l e1 err i.
Proof.
  simpl. destruct i.
  * simpl. reflexivity.
  * simpl. reflexivity.
Qed.

Theorem last_nth_equal {A : Type} (l : list A) (def err : A) :
  last l def = nth_def l def err (length l).
Proof.
  induction l.
  * auto.
  * simpl. rewrite IHl. destruct l.
    - auto.
    - simpl. auto.
Qed.

Definition effect_id_eqb (id1 id2 : SideEffectId) : bool :=
match id1, id2 with
 | Input, Input => true
 | Output, Output => true
 | _, _ => false
end.


Definition effect_eqb (e1 e2 : SideEffectId * list Value) : bool :=
match e1, e2 with
| (id1, vals1), (id2, vals2) => effect_id_eqb id1 id2 && list_eqb Value_full_eqb vals1 vals2
end.

Theorem effect_eqb_refl :
  forall e,
  effect_eqb e e = true.
Proof.
  intros. unfold effect_eqb. destruct e.
  assert (effect_id_eqb s s = true). { destruct s; auto. }
  rewrite H. simpl.
  apply list_eqb_refl.
  intros. apply Value_full_eqb_refl.
Qed.

Theorem effect_list_eqb_refl :
  forall l,
  list_eqb effect_eqb l l = true.
Proof.
  induction l.
  * auto.
  * simpl. apply andb_true_intro. rewrite effect_eqb_refl. auto.
Qed.

Proposition effect_eqb_eq :
  forall e1 e2,
  e1 = e2
<->
  effect_eqb e1 e2 = true.
Proof.
  intros. split; destruct e1, e2.
  * intros. inversion H. subst. apply effect_eqb_refl.
  * intros. simpl in H. apply eq_sym, Bool.andb_true_eq in H. destruct H.
    apply eq_sym, value_full_list_eqb_eq in H0. subst.
    destruct s, s0; auto.
    inversion H.
    inversion H.
Qed.

Proposition effect_list_eqb_eq (l1 l2 : SideEffectList) :
  l1 = l2
<->
  list_eqb effect_eqb l1 l2 = true.
Proof.
  split.
  * intros. subst. apply effect_list_eqb_refl.
  * generalize dependent l2. induction l1; intros.
    - simpl in H. destruct l2; auto. congruence.
    - simpl in H. destruct l2.
      + congruence.
      + apply eq_sym, Bool.andb_true_eq in H. destruct H.
        pose (IHl1 l2 (eq_sym H0)). rewrite e.
        apply eq_sym, effect_eqb_eq in H. rewrite H. auto.
Qed.
