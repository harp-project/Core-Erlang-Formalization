Require Core_Erlang_Full_Equivalence.
Require Core_Erlang_Proofs.

Export Core_Erlang_Full_Equivalence.
Export Core_Erlang_Proofs.

Import Core_Erlang_Tactics.Tactics.
Import ListNotations.

Inductive nearly_same : ValueSequence + Exception -> ValueSequence + Exception -> Prop :=
| Same_ex ex : nearly_same (inr ex) (inr ex)
| Same_vals l l': 
  length l = length l' ->
  (forall i, i < length l -> nearly_same_value (nth i l ErrorValue) (nth i l' ErrorValue))
->
  nearly_same (inl l) (inl l')
with nearly_same_value : Value -> Value -> Prop :=
| Same_refl_value v : nearly_same_value v v
| Same_clos env id id' ext vl e e' :
  equivalent_expr' e e'
->
  nearly_same_value (VClos env id ext vl e) (VClos env id' ext vl e')
with equivalent_expr' : Expression -> Expression -> Prop :=
| equiv e1 e2 :
  forall env eff res res' eff' id1,
  (nearly_same res res' ->
  (exists id2 clock, fbs_expr clock env id1 e1 eff = Result id2 res eff')
<->
  (exists id2' clock, fbs_expr clock env id1 e2 eff = Result id2' res' eff'))
->
  equivalent_expr' e1 e2
.

Definition equivalent_expr' e1 e2 :=
forall env eff res res' eff' id1,
  nearly_same res res' ->
  (exists id2 clock, fbs_expr clock env id1 e1 eff = Result id2 res eff')
<->
  (exists id2' clock, fbs_expr clock env id1 e2 eff = Result id2' res' eff').


Fixpoint value_excludes_closure (v : Value) : bool :=
match v with
 | VNil => true
 | VLit l => true
 | VClos env ext id vl e => false
 | VCons vhd vtl => value_excludes_closure vhd && value_excludes_closure vtl
 | VTuple vl => (fix f l :=
                   match l with
                   | [] => true
                   | x::xs => andb (value_excludes_closure x) (f xs)
                   end) vl
 | VMap l => (fix f l :=
                   match l with
                   | [] => true
                   | (x, y)::xs => andb (andb (value_excludes_closure x) (value_excludes_closure y)) (f xs)
                   end) l
end.


Definition result_excludes_closure (res : ValueSequence + Exception) : bool :=
match res with
| inl vals => forallb value_excludes_closure vals
| _ => true
end.

Definition equivalent_expr e1 e2 :=
forall env eff res eff' id1,
  result_excludes_closure res = true ->
  (exists id2 clock, fbs_expr clock env id1 e1 eff = Result id2 res eff')
<->
  (exists id2' clock, fbs_expr clock env id1 e2 eff = Result id2' res eff').

Definition equivalent_single e1 e2 :=
forall env eff res eff' id1 id2,
  result_excludes_closure res = true ->
  (exists clock, fbs_single clock env id1 e1 eff = Result id2 res eff')
<->
  (exists clock, fbs_single clock env id1 e2 eff = Result id2 res eff').

Definition equivalent_exprlist l1 l2 :=
forall env eff res eff' id1 id2,
  result_excludes_closure res = true ->
  (exists clock, fbs_values (fbs_expr clock) env id1 l1 eff = Result id2 res eff')
<->
  (exists clock, fbs_values (fbs_expr clock) env id1 l2 eff = Result id2 res eff').

Definition equivalent_singlelist l1 l2 :=
forall env eff res eff' id1 id2,
  result_excludes_closure res = true ->
  (exists clock, fbs_values (fbs_single clock) env id1 l1 eff = Result id2 res eff')
<->
  (exists clock, fbs_values (fbs_single clock) env id1 l2 eff = Result id2 res eff').

Definition equivalent_case l1 l2 :=
forall env eff res eff' id1 id2 vals,
  result_excludes_closure res = true ->
  (exists clock, fbs_case env id1 l1 eff vals (fbs_expr clock) = Result id2 res eff')
<->
  (exists clock, fbs_case env id1 l2 eff vals (fbs_expr clock) = Result id2 res eff').

Section equivalence_relation.

Theorem equivalent_expr_refl {e} :
  equivalent_expr e e.
Proof.
  unfold equivalent_expr. split; intros; assumption.
Qed.

Theorem equivalent_expr_sym {e1 e2} :
  equivalent_expr e1 e2
->
  equivalent_expr e2 e1.
Proof.
  unfold equivalent_expr. split; intros.
  * eapply H in H1. exact H1. assumption.
  * eapply H in H1. exact H1. assumption.
Qed.

Theorem equivalent_expr_trans {e1 e2 e3} :
  equivalent_expr e1 e2 -> equivalent_expr e2 e3
->
  equivalent_expr e1 e3.
Proof.
  unfold equivalent_expr. split; intros.
  * apply H in H2. apply H0 in H2. all: auto.
  * apply H0 in H2. apply H in H2. all: auto.
Qed.

Theorem equivalent_single_refl {e} :
  equivalent_single e e.
Proof.
  split; intros; assumption.
Qed.

Theorem equivalent_single_sym {e1 e2} :
  equivalent_single e1 e2
->
  equivalent_single e2 e1.
Proof.
   split; intros.
  * eapply H in H1. exact H1. assumption.
  * eapply H in H1. exact H1. assumption.
Qed.

Theorem equivalent_single_trans {e1 e2 e3} :
  equivalent_single e1 e2 -> equivalent_single e2 e3
->
  equivalent_single e1 e3.
Proof.
   split; intros.
  * apply H in H2. apply H0 in H2. all: auto.
  * apply H0 in H2. apply H in H2. all: auto.
Qed.

Theorem equivalent_exprlist_refl {l} :
  equivalent_exprlist l l.
Proof.
   split; intros; auto.
Qed.

Theorem equivalent_exprlist_sym {l1 l2} :
  equivalent_exprlist l1 l2
->
  equivalent_exprlist l2 l1.
Proof.
  split; intros.
  * eapply H in H1. exact H1. assumption.
  * eapply H in H1. exact H1. assumption.
Qed.

Theorem equivalent_exprlist_trans {l1 l2 l3} :
  equivalent_exprlist l1 l2 -> equivalent_exprlist l2 l3
->
  equivalent_exprlist l1 l3.
Proof.
  split; intros.
  * apply H in H2. apply H0 in H2. all: auto.
  * apply H0 in H2. apply H in H2. all: auto.
Qed.

Theorem equivalent_singlelist_refl {l} :
  equivalent_singlelist l l.
Proof.
  split; intros; auto.
Qed.

Theorem equivalent_singlelist_sym {l1 l2} :
  equivalent_singlelist l1 l2
->
  equivalent_singlelist l2 l1.
Proof.
  split; intros.
  * eapply H in H1. exact H1. assumption.
  * eapply H in H1. exact H1. assumption.
Qed.

Theorem equivalent_singlelist_trans {l1 l2 l3} :
  equivalent_singlelist l1 l2 -> equivalent_singlelist l2 l3
->
  equivalent_singlelist l1 l3.
Proof.
  split; intros.
  * apply H in H2. apply H0 in H2. all: auto.
  * apply H0 in H2. apply H in H2. all: auto.
Qed.

Theorem equivalent_case_refl {l} :
  equivalent_case l l.
Proof.
  split; intros; auto.
Qed.

Theorem equivalent_case_sym {l1 l2} :
  equivalent_case l1 l2
->
  equivalent_case l2 l1.
Proof.
  split; intros.
  * eapply H in H1. exact H1. assumption.
  * eapply H in H1. exact H1. assumption.
Qed.

Theorem equivalent_case_trans {l1 l2 l3} :
  equivalent_case l1 l2 -> equivalent_case l2 l3
->
  equivalent_case l1 l3.
Proof.
  split; intros.
  * apply H in H2. apply H0 in H2. all: auto.
  * apply H0 in H2. apply H in H2. all: auto.
Qed.

End equivalence_relation.

Lemma id_extension_singlelist_helper el :
forall {env id1 eff id2 res eff' clock},
(forall (env : Environment) (id1 : nat) (e : SingleExpression)
                          (eff : SideEffectList) (id2 : nat) (res : ValueSequence + Exception)
                          (eff' : SideEffectList),
                        fbs_single clock env id1 e eff = Result id2 res eff' ->
                        exists id', id2 = id1 + id')
  ->
fbs_values (fbs_single clock) env id1 el eff = Result id2 res eff'
->
exists id', id2 = id1 + id'.
Proof.
  induction el; intros.
  * simpl in H0. inversion H0. subst. exists 0. auto.
  * simpl in H0.
    destruct (fbs_single clock env id1 a eff) eqn:D.
    destruct res0. destruct v. congruence. destruct v0. 2: congruence.
    3-4: congruence.
    - apply H in D.
      destruct D. subst.
      destruct (fbs_values (fbs_single clock) env (id1 + x) el eff0) eqn:D2.
      destruct res0. 3-4: congruence.
      + inversion H0. apply IHel in D2. destruct D2. subst.
        exists (x + x0). lia.
        exact H.
      + inversion H0. subst. apply IHel in D2. destruct D2.
        exists (x + x0). lia.
        exact H.
    - inversion H0. subst. apply H in D. exact D.
Qed.

Lemma id_extension_exprlist_helper el :
forall {env id1 eff id2 res eff' clock},
(forall (env : Environment) (id1 : nat) (e : Expression)
                          (eff : SideEffectList) (id2 : nat) (res : ValueSequence + Exception)
                          (eff' : SideEffectList),
                        fbs_expr clock env id1 e eff = Result id2 res eff' ->
                        exists id', id2 = id1 + id')
  ->
fbs_values (fbs_expr clock) env id1 el eff = Result id2 res eff'
->
exists id', id2 = id1 + id'.
Proof.
  induction el; intros.
  * simpl in H0. inversion H0. subst. exists 0. auto.
  * simpl in H0.
    destruct (fbs_expr clock env id1 a eff) eqn:D.
    destruct res0. destruct v. congruence. destruct v0. 2: congruence.
    3-4: congruence.
    - apply H in D.
      destruct D. subst.
      destruct (fbs_values (fbs_expr clock) env (id1 + x) el eff0) eqn:D2.
      destruct res0. 3-4: congruence.
      + inversion H0. apply IHel in D2. destruct D2. subst.
        exists (x + x0). lia.
        exact H.
      + inversion H0. subst. apply IHel in D2. destruct D2.
        exists (x + x0). lia.
        exact H.
    - inversion H0. subst. apply H in D. exact D.
Qed.

Lemma id_extension_case_helper el :
forall {env id1 eff id2 res eff' vals clock},
(forall (env : Environment) (id1 : nat) (e : Expression)
                          (eff : SideEffectList) (id2 : nat) (res : ValueSequence + Exception)
                          (eff' : SideEffectList),
                        fbs_expr clock env id1 e eff = Result id2 res eff' ->
                        exists id', id2 = id1 + id')
  ->
fbs_case el env id1 eff vals (fbs_expr clock) = Result id2 res eff'
->
exists id', id2 = id1 + id'.
Proof.
  induction el; intros.
  * simpl in H0. inversion H0. subst. exists 0. auto.
  * simpl in H0. destruct a, p. destruct (match_valuelist_to_patternlist vals l) eqn:D1.
    - destruct (fbs_expr clock (add_bindings (match_valuelist_bind_patternlist vals l) env) id1 e0 eff) eqn:D2.
      destruct res0. destruct v. congruence. destruct v0. 2,4-5:congruence.
      destruct (((id =? id1) && list_eqb effect_eqb eff eff0)%bool) eqn:D3.
      2: congruence.
      + destruct v; try congruence. destruct l0; try congruence.
        destruct ((s =? "true")%string).
        ** apply H in H0. destruct H0. eexists. exact H0.
        ** destruct (s =? "false")%string. 2: congruence.
           eapply IHel. exact H. exact H0.
      + congruence.
    - eapply IHel. exact H. exact H0.
Qed.

Theorem id_extension_expr :
forall {clock env id1 e eff id2 res eff'},
  fbs_expr clock env id1 e eff = Result id2 res eff'
->
  exists id', id2 = id1 + id'
with id_extension_single :
forall {clock env id1 e eff id2 res eff'},
  fbs_single clock env id1 e eff = Result id2 res eff'
->
  exists id', id2 = id1 + id'.
Proof.
{
  induction clock; intros. inversion H. destruct e.
  * simpl in H. eapply id_extension_singlelist_helper. 2: exact H.
    intros. apply id_extension_single in H0. exact H0.
  * simpl in H. apply id_extension_single in H. exact H.
}
{
  induction clock; intros. inversion H. destruct e; simpl in H.
  * inversion H; subst; exists 0; auto.
  * inversion H; subst; exists 0; auto.
  * inversion H; subst; exists 0; auto. destruct (get_value env (inl v)). inversion H. auto. congruence.
  * inversion H; subst; exists 0; auto. destruct (get_value env (inr f)). inversion H. auto. congruence.
  * exists 1. inversion H. lia.
  * destruct (fbs_expr clock env id1 tl eff) eqn:D1.
    destruct res0. destruct v. congruence. destruct v0. 2, 4-5: congruence.
    - apply id_extension_expr in D1. destruct D1.
      destruct (fbs_expr clock env id hd eff0) eqn:D2.
      destruct res0. destruct v0. congruence. destruct v1. 2, 4-5: congruence.
      + apply id_extension_expr in D2. destruct D2. subst. inversion H. subst.
        exists (x + x0). lia.
      + apply id_extension_expr in D2. destruct D2. subst. inversion H. subst.
        exists (x + x0). lia.
    - apply id_extension_expr in D1. destruct D1. inversion H. subst. 
      exists x. auto.
  * destruct (fbs_values (fbs_expr clock) env id1 l eff) eqn:D1.
    destruct res0. 3-4: congruence.
    - inversion H. subst. eapply id_extension_exprlist_helper in D1. destruct D1.
      exists x. subst. auto. intros. eapply id_extension_expr. exact H0.
    - inversion H. subst. eapply id_extension_exprlist_helper in D1. destruct D1.
      exists x. subst. auto. intros. eapply id_extension_expr. exact H0.
  * destruct (fbs_values (fbs_expr clock) env id1 l eff) eqn:D1.
    destruct res0. 3-4: congruence.
    - inversion H. subst. eapply id_extension_exprlist_helper in D1 as D1'.
      destruct D1'. 2: intros; eapply id_extension_expr; exact H0.
      subst. exists x. auto.
    - inversion H. subst. eapply id_extension_exprlist_helper in D1. destruct D1.
      exists x. subst. auto. intros. eapply id_extension_expr. exact H0.
  * destruct (fbs_values (fbs_expr clock) env id1 l eff) eqn:D1.
    destruct res0. 3-4: congruence.
    - inversion H. subst. eapply id_extension_exprlist_helper in D1 as D1'.
      destruct D1'. 2: intros; eapply id_extension_expr; exact H0.
      subst. exists x. auto.
    - inversion H. subst. eapply id_extension_exprlist_helper in D1. destruct D1.
      exists x. subst. auto. intros. eapply id_extension_expr. exact H0.
  * destruct (fbs_expr clock env id1 exp eff) eqn:D1.
    destruct res0. destruct v. congruence. destruct v0. 2,4-5: congruence.
    - apply id_extension_expr in D1. destruct D1. subst.
      destruct (fbs_values (fbs_expr clock) env (id1 + x) l eff0) eqn:D2.
      destruct res0. 3-4: congruence.
      + destruct v.
        3: destruct (length vl =? length v0).
        1-2, 4-7:
           apply id_extension_exprlist_helper in D2; [ destruct D2; subst;
           inversion H; exists (x + x0); lia | 
           intros; eapply id_extension_expr; exact H0 ].
        apply id_extension_exprlist_helper in D2. destruct D2; subst.
        apply id_extension_expr in H. destruct H. subst.
        exists (x + x0 + x1). lia.
        intros; eapply id_extension_expr; exact H0.
      + apply id_extension_exprlist_helper in D2; [ destruct D2; subst;
           inversion H; exists (x + x0); lia | 
           intros; eapply id_extension_expr; exact H0 ].
    - apply id_extension_expr in D1. destruct D1. subst.
      inversion H. exists x. auto.
  * destruct (fbs_expr clock env id1 e eff) eqn:D1.
    destruct res0. 3-4: congruence.
    - apply id_extension_expr in D1. destruct D1. subst.
      apply id_extension_case_helper in H. destruct H. subst.
      exists (x + x0). lia.
      intros; eapply id_extension_expr; exact H0.
    - inversion H. apply id_extension_expr in D1. destruct D1. subst.
      exists x. auto.
  * destruct (fbs_expr clock env id1 e1 eff) eqn:D1.
    destruct res0. destruct (Datatypes.length v =? Datatypes.length l).
    2, 4-5: congruence.
    - apply id_extension_expr in D1. destruct D1.
      apply id_extension_expr in H. destruct H. subst.
      exists (x + x0). lia.
    - apply id_extension_expr in D1. destruct D1. inversion H. subst. 
      exists x. auto.
  * destruct (fbs_expr clock env id1 e1 eff) eqn:D1.
    destruct res0. destruct v. congruence. destruct v0. 2, 4-5: congruence.
    - apply id_extension_expr in D1. destruct D1.
      apply id_extension_expr in H. destruct H. subst.
      exists (x + x0). lia.
    - apply id_extension_expr in D1. destruct D1. inversion H. subst. 
      exists x. auto.
  * apply id_extension_expr in H. destruct H. exists (length l + x). lia.
  * destruct (fbs_values (fbs_expr clock) env id1 (make_map_exps l) eff) eqn:D1.
    destruct res0. 3-4: congruence.
    - inversion H. subst. eapply id_extension_exprlist_helper in D1. destruct D1.
      destruct (make_map_vals_inverse v). 2: congruence. destruct p. inversion H.
      exists x. subst. auto. intros. eapply id_extension_expr. exact H0.
    - inversion H. subst. eapply id_extension_exprlist_helper in D1. destruct D1.
      exists x. subst. auto. intros. eapply id_extension_expr. exact H0.
  * destruct (fbs_expr clock env id1 e1 eff) eqn:D1.
    destruct res0. destruct (Datatypes.length v =? Datatypes.length vl1).
    2, 4-5: congruence.
    - apply id_extension_expr in D1. destruct D1.
      apply id_extension_expr in H. destruct H. subst.
      exists (x + x0). lia.
    - apply id_extension_expr in D1. destruct D1.
      apply id_extension_expr in H. destruct H. subst.
      exists (x + x0). lia.
}
Qed.

Theorem id_extension_exprlist el :
forall {env id1 eff id2 res eff' clock},
fbs_values (fbs_expr clock) env id1 el eff = Result id2 res eff'
->
exists id', id2 = id1 + id'.
Proof.
  intros. eapply id_extension_exprlist_helper in H. assumption.
  intros. eapply id_extension_expr. exact H0.
Qed.

Theorem id_extension_singlelist el :
forall {env id1 eff id2 res eff' clock},
fbs_values (fbs_single clock) env id1 el eff = Result id2 res eff'
->
exists id', id2 = id1 + id'.
Proof.
  intros. eapply id_extension_singlelist_helper in H. assumption.
  intros. eapply id_extension_single. exact H0.
Qed.

Theorem id_extension_case l :
forall env id1 eff v id2 res eff' clock,
fbs_case l env id1 eff v (fbs_expr clock) = Result id2 res eff'
->
exists id', id2 = id1 + id'.
Proof.
  intros.
  eapply id_extension_case_helper. 2: exact H.
  intros. eapply id_extension_expr. exact H0.
Qed.

Lemma id_irrelevant_singlelist_helper :
forall el env id1 eff id2 res eff' clock,
  (forall (env : Environment) (id1 : nat)
                         (e : SingleExpression) (eff : SideEffectList) 
                         (id2 : nat) (res : ValueSequence + Exception) 
                         (eff' : SideEffectList),
                       result_excludes_closure res = true ->
                       fbs_single clock env id1 e eff = Result (id1 + id2) res eff' ->
                       forall id1' : nat,
                       fbs_single clock env id1' e eff = Result (id1' + id2) res eff')
  ->
  result_excludes_closure res = true
  ->
  fbs_values (fbs_single clock) env id1 el eff = Result (id1 + id2) res eff'
->
  forall id1', fbs_values (fbs_single clock) env id1' el eff = Result (id1' + id2) res eff'.
Proof.
  induction el; intros.
  * simpl. simpl in H1. inversion H1. subst. assert (id2 = 0). { lia. } subst.
    rewrite Nat.add_0_r. auto.
  * simpl in H1. break_match_singleton; subst.
    - apply id_extension_single in Heqr as D. destruct D. subst.
      eapply H with (id1' := id1') in Heqr.
      break_match_list; subst.
      + admit.
      + admit.
      + simpl.
    - simpl. apply id_extension_single in Heqr as D. destruct D. subst.
      eapply H with (id1' := id1') in Heqr. rewrite Heqr. inversion H1. subst.
      assert (x = id2). { lia. } subst. auto.
      simpl. auto.
Qed.


Theorem id_irrelevant_expr :
(forall {clock env id1 e eff id2 res eff'},
  result_excludes_closure res = true ->
  fbs_expr clock env id1 e eff = Result (id1 + id2) res eff'
->
forall id1',
  fbs_expr clock env id1' e eff = Result (id1' + id2) res eff')
with id_irrelevant_single :
(forall {clock env id1 e eff id2 res eff'},
  result_excludes_closure res = true ->
  fbs_single clock env id1 e eff = Result (id1 + id2) res eff'
->
forall id1',
  fbs_single clock env id1' e eff = Result (id1' + id2) res eff').
Proof.
{
  induction clock; intros.
  * simpl in H0. inversion H0.
  * simpl in H0. destruct e.
    - 
    - simpl. eapply id_irrelevant_single in H0. exact H0. auto.
}
{
  induction clock; intros.
  * simpl in H0. inversion H0.
  * simpl in H0. destruct e.
    all: admit.
}
Admitted.

Goal forall e x,
  equivalent_expr e (ELet [x] (EFun [] e) (EApp (EVar x) [])).
Proof.
  split; intros.
  * destruct H0, H0. apply fbs_expr_correctness in H0.
    exists (S x0). apply fbs_soundness.
    eapply eval_single, eval_let; auto.
    - apply eval_single, eval_fun.
    - reflexivity.
    - eapply eval_single, eval_app with (vals := []) (eff := []) (ids := []); auto.
      + eapply eval_single, eval_var. simpl. rewrite Proofs.get_value_here. reflexivity.
      + auto.
      + intros. inversion H1.
      + unfold get_env. simpl. auto. apply fbs_soundness in H0. destruct H0.
        apply fbs_expr_correctness with (clock := x2).
        eapply id_extension_expr in H0 as D. destruct D. subst.
        eapply id_irrelevant_expr in H0. 2: auto. exact H0.
  * destruct H0, H0. apply fbs_expr_correctness in H0.
    inversion H0. inversion H4; subst.
    - pose (EE1 := element_exist 0 vals H19). inversion EE1. inversion H1. subst.
      inversion H19. apply eq_sym, length_zero_iff_nil in H3. subst.
      inversion H14. subst. inversion H6. subst.

      inversion H20. inversion H7.
      + subst.
        apply eq_sym, length_zero_iff_nil in H18. subst.
        apply eq_sym, length_zero_iff_nil in H21. subst.
        apply eq_sym, length_zero_iff_nil in H15. subst.
        inversion H16. inversion H8. subst. simpl in H25.
        rewrite Proofs.get_value_here in H25. inversion H25. subst.

        unfold get_env in H29. simpl in H29.

        apply fbs_soundness in H29. destruct H29.
        eapply id_extension_expr in H2 as D. destruct D. subst.
        eapply id_irrelevant_expr in H2. 2: auto.

        exists (n + x3), x2. exact H2.
      + subst. inversion H23. inversion H8.
      + subst. inversion H15.
      + subst. inversion H18. inversion H8. subst.
        simpl in H28. rewrite Proofs.get_value_here in H28. inversion H28. subst.
        congruence.
      + subst. inversion H18. inversion H8. subst.
        simpl in H28. rewrite Proofs.get_value_here in H28. inversion H28. subst.
        contradiction.
    - inversion H18. inversion H5.
Qed.

