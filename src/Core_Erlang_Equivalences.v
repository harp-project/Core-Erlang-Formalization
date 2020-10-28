Require Core_Erlang_Proofs.

Export Core_Erlang_Proofs.Proofs.

Import Core_Erlang_Tactics.Tactics.
Import ListNotations.


Definition completely_equivalent e1 e2 :=
forall env eff res eff' id1 id2,
  |env, id1, e1, eff| -e> |id2, res, eff'|
<->
  |env, id1, e2, eff| -e> |id2, res, eff'|.

Definition completely_equivalent_single e1 e2 :=
forall env eff res eff' id1 id2,
  |env, id1, e1, eff| -s> |id2, res, eff'|
<->
  |env, id1, e2, eff| -s> |id2, res, eff'|.

Definition strongly_equivalent e1 e2 id1 id2 id1' id2' :=
forall env eff res eff',
  |env, id1, e1, eff| -e> |id2, res, eff'|
<->
  |env, id1', e2, eff| -e> |id2', res, eff'|.

Definition strongly_equivalent_single e1 e2 id1 id2 id1' id2' :=
forall env eff res eff',
  |env, id1, e1, eff| -s> |id2, res, eff'|
<->
  |env, id1', e2, eff| -s> |id2', res, eff'|.

(* Definition weakly_equivalent e1 e2 id1 id2 id1' id2' eff eff2 eff' eff2' :=
forall env res,
  |env, id1, e1, eff| -e> |id2, res, eff2|
<->
  |env, id1', e2, eff'| -e> |id2', res, eff2'|. *)

(* Theorem completely_to_strong e1 e2 :
  completely_equivalent e1 e2
-> 
  forall id1 id2, strongly_equivalent e1 e2 id1 id2 id1 id2.
Proof.
  unfold completely_equivalent, strongly_equivalent. split; intros.
  apply H. auto.
  apply H. auto.
Qed.

Theorem strong_to_weak e1 e2 id1 id2 id1' id2' :
  strongly_equivalent e1 e2 id1 id2 id1' id2'
-> 
  forall eff1 eff2, weakly_equivalent e1 e2 id1 id2 id1' id2' eff1 eff2 eff1 eff2.
Proof.
  unfold weakly_equivalent, strongly_equivalent. split; intros.
  apply H. auto.
  apply H. auto.
Qed. *)

(* Example exp_to_fun (e : Expression) (x : Var) (id id' : nat):
  strongly_equivalent e (ELet [x] (EFun [] e) (EApp (EVar x) [])) (S id) id' id id'.
Proof.
  unfold strongly_equivalent.
  split; intros.
  * eapply eval_single, eval_let; auto.
    - apply eval_single, eval_fun.
    - reflexivity.
    - eapply eval_single, eval_app with (vals := []) (eff := []) (ids := []); auto.
      + eapply eval_single, eval_var. simpl. rewrite get_value_here. reflexivity.
      + auto.
      + intros. inversion H0.
      + unfold get_env. simpl. auto.
  * inversion H. inversion H3; subst.
    - pose (EE1 := element_exist 0 vals H18). inversion EE1. inversion H0. subst.
      inversion H18. apply eq_sym, length_zero_iff_nil in H2. subst.
      inversion H13. subst. inversion H5. subst.

      inversion H19. inversion H6.
      + subst.
        apply eq_sym, length_zero_iff_nil in H17. subst.
        apply eq_sym, length_zero_iff_nil in H20. subst.
        apply eq_sym, length_zero_iff_nil in H14. subst.
        inversion H15. inversion H7. subst. simpl in H24.
        rewrite get_value_here in H24. inversion H24. subst.

        unfold get_env in H28. simpl in H28. assumption.
      + subst. inversion H22. inversion H7.
      + subst. inversion H14.
      + subst. inversion H17. inversion H7. subst.
        simpl in H27. rewrite get_value_here in H27. inversion H27. subst.
        congruence.
      + subst. inversion H17. inversion H7. subst.
        simpl in H27. rewrite get_value_here in H27. inversion H27. subst.
        contradiction.
    - inversion H17. inversion H4.
Qed. *)

Section equivalence_relation.

Theorem completely_equivalent_refl e :
  completely_equivalent e e.
Proof.
  intros. unfold completely_equivalent. split; intros.
  * auto.
  * auto.
Qed.

(* Theorem strongly_equivalent_refl e :
  forall id id',
  strongly_equivalent e e id id' id id'.
Proof.
  intros. unfold strongly_equivalent. split; intros.
  * auto.
  * auto.
Qed.

Theorem weakly_equivalent_refl e :
  forall id id' eff eff',
  weakly_equivalent e e id id' id id' eff eff' eff eff'.
Proof.
  intros. unfold weakly_equivalent. split; intros.
  * auto.
  * auto.
Qed. *)

Theorem completely_equivalent_sym e1 e2 :
  completely_equivalent e1 e2 -> completely_equivalent e2 e1.
Proof.
  unfold completely_equivalent; intros.
  split; apply H.
Qed.

(* Theorem strongly_equivalent_sym e1 e2 :
  forall id1 id1' id2 id2',
  strongly_equivalent e1 e2 id1 id1' id2 id2' -> strongly_equivalent e2 e1 id2 id2' id1 id1'.
Proof.
  unfold strongly_equivalent; intros.
  split; apply H.
Qed.

Theorem weakly_equivalent_sym e1 e2 :
  forall id1 id1' id2 id2' eff1 eff1' eff2 eff2',
  weakly_equivalent e1 e2 id1 id1' id2 id2' eff1 eff1' eff2 eff2' 
->
  weakly_equivalent e2 e1 id2 id2' id1 id1' eff2 eff2' eff1 eff1'.
Proof.
  unfold weakly_equivalent; intros.
  split; apply H.
Qed. *)

Theorem completely_equivalent_trans e1 e2 e3 :
  completely_equivalent e1 e2 -> completely_equivalent e2 e3
->
  completely_equivalent e1 e3.
Proof.
  unfold completely_equivalent; intros.
  split; intros.
  * apply H in H1. apply H0 in H1. auto.
  * apply H0 in H1. apply H in H1. auto.
Qed.

(* Theorem strongly_equivalent_trans e1 e2 e3 :
  forall id1 id1' id2 id2' id3 id3',
  strongly_equivalent e1 e2 id1 id1' id2 id2' -> strongly_equivalent e2 e3 id2 id2' id3 id3'
->
  strongly_equivalent e1 e3 id1 id1' id3 id3'.
Proof.
  unfold strongly_equivalent; intros.
  split; intros.
  * apply H in H1. apply H0 in H1. auto.
  * apply H0 in H1. apply H in H1. auto.
Qed.

Theorem weakly_equivalent_trans e1 e2 e3 :
    forall id1 id1' id2 id2' id3 id3' eff1 eff1' eff2 eff2' eff3 eff3',
  weakly_equivalent e1 e2 id1 id1' id2 id2' eff1 eff1' eff2 eff2' ->
  weakly_equivalent e2 e3 id2 id2' id3 id3' eff2 eff2' eff3 eff3'
->
  weakly_equivalent e1 e3 id1 id1' id3 id3' eff1 eff1' eff3 eff3'.
Proof.
  unfold weakly_equivalent; intros.
  split; intros.
  * apply H in H1. apply H0 in H1. auto.
  * apply H0 in H1. apply H in H1. auto.
Qed. *)

Theorem completely_equivalent_single_refl e :
  completely_equivalent_single e e.
Proof.
  intros. unfold completely_equivalent_single. split; intros.
  * auto.
  * auto.
Qed.

Theorem completely_equivalent_single_sym e1 e2 :
  completely_equivalent_single e1 e2 -> completely_equivalent_single e2 e1.
Proof.
  unfold completely_equivalent_single; intros.
  split; apply H.
Qed.

Theorem completely_equivalent_single_trans e1 e2 e3 :
  completely_equivalent_single e1 e2 -> completely_equivalent_single e2 e3
->
  completely_equivalent_single e1 e3.
Proof.
  unfold completely_equivalent_single; intros.
  split; intros.
  * apply H in H1. apply H0 in H1. auto.
  * apply H0 in H1. apply H in H1. auto.
Qed.

End equivalence_relation.

Section congruence.

Theorem ECons_congruence hd tl : forall hd' tl',
  completely_equivalent hd hd' -> completely_equivalent tl tl'
->
  completely_equivalent_single (ECons hd tl) (ECons hd' tl').
Proof.
  intros. unfold completely_equivalent, completely_equivalent_single in *.
  split; intros.
  * inversion H1; subst.
    - eapply eval_cons. apply H0 in H6. exact H6. apply H in H11. assumption.
    - eapply eval_cons_tl_ex. apply H0. assumption.
    - eapply eval_cons_hd_ex. apply H0 in H6. exact H6. apply H. assumption.
  * inversion H1; subst.
    - eapply eval_cons. apply H0 in H6. exact H6. apply H in H11. assumption.
    - eapply eval_cons_tl_ex. apply H0. assumption.
    - eapply eval_cons_hd_ex. apply H0 in H6. exact H6. apply H. assumption.
Qed.

Lemma value_exception_eq_dec (res res' : ValueSequence + Exception) : {res = res'} + {res <> res'}.
Proof.
  set Value_eq_dec.
  repeat decide equality.
Defined.

Lemma se_list_eq_dec (l l' : SideEffectList) : {l = l'} + {l <> l'}.
Proof.
  set Value_eq_dec.
  set string_dec.
  repeat decide equality.
Defined.

Theorem ECons_congruence_strongly hd tl : forall hd' tl' id id' id'' id2 id2' id2'',
  strongly_equivalent tl tl' id id' id2 id2' -> 
  strongly_equivalent hd hd' id' id'' id2' id2''
->
  strongly_equivalent_single (ECons hd tl) (ECons hd' tl') id id'' id2 id2''.
Proof.
  intros. unfold strongly_equivalent, strongly_equivalent_single in *.
  split; intros.
  * inversion H1; subst.
    - eapply eval_cons. pose (H env eff (inl [tlv]) eff2). destruct i.
      apply H2. exact H6. apply H in H11. assumption.
    - eapply eval_cons_tl_ex. apply H0. assumption.
    - eapply eval_cons_hd_ex. apply H0 in H6. exact H6. apply H. assumption.
  * inversion H1; subst.
    - eapply eval_cons. apply H0 in H6. exact H6. apply H in H11. assumption.
    - eapply eval_cons_tl_ex. apply H0. assumption.
    - eapply eval_cons_hd_ex. apply H0 in H6. exact H6. apply H. assumption.
Qed.

End congruence.
