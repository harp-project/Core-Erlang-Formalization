Require Core_Erlang_Full_Equivalence.

Require Import Coq.Sorting.Permutation.
Import Core_Erlang_Full_Equivalence.
Import ListNotations.

Definition weakly_equivalent e1 e2 :=
(forall env eff res eff' id1 id2,
  |env, id1, e1, eff| -e> |id2, res, eff'|
->
  exists eff'', |env, id1, e2, eff| -e> |id2, res, eff''| /\ Permutation eff' eff'')
/\
(forall env eff res eff' id1 id2,
  |env, id1, e2, eff| -e> |id2, res, eff'|
->
  exists eff'', |env, id1, e1, eff| -e> |id2, res, eff''| /\ Permutation eff' eff'').

Definition weakly_equivalent_single e1 e2 :=
(forall env eff res eff' id1 id2,
  |env, id1, e1, eff| -s> |id2, res, eff'|
->
  exists eff'', |env, id1, e2, eff| -s> |id2, res, eff''| /\ Permutation eff' eff'')
/\
(forall env eff res eff' id1 id2,
  |env, id1, e2, eff| -s> |id2, res, eff'|
->
  exists eff'', |env, id1, e1, eff| -s> |id2, res, eff''| /\ Permutation eff' eff'').


Section helpers.

Theorem last_remove_first {A : Type} :
forall (l : list A) e1 e2 def,
  last (e1 :: e2 :: l) def = last (e2 :: l) def.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem effect_extension_list :
  forall eff eff1,
  (forall i : nat,
    i < Datatypes.length eff ->
    exists l0 : list (SideEffectId * list Value),
      nth_def eff eff1 [] (S i) = nth_def eff eff1 [] i ++ l0)
->
  exists l, last eff eff1 = eff1 ++ l.
Proof.
  induction eff; intros.
  * simpl. exists []. rewrite app_nil_r. auto.
  * destruct eff.
    - pose (H 0 (Nat.lt_0_1)). destruct e. simpl in H0. exists x. simpl. auto.
    - epose (IHeff eff1 _).
      destruct e. rewrite <- last_element_equal in H0.
      exists x. rewrite last_remove_first. rewrite <- last_element_equal. auto.
Unshelve.
  intros. simpl in H0. epose (H (S i) _). destruct e.
  remember (l::eff) as l'. simpl in H1. simpl.
  destruct i.
  + simpl. epose (H 0 _). destruct e. simpl in H2.
    rewrite H1, H2. rewrite <- app_assoc. exists (x0 ++ x). auto.
    Unshelve. simpl. lia. simpl. lia. 
  + exists x. simpl. exact H1.
Qed.

Theorem effect_extension :
(forall env id e eff id' res eff',
  | env, id, e, eff | -e> | id', res, eff' |
->
  exists l, eff' = eff ++ l)
/\
(forall env id e eff id' res eff',
  | env, id, e, eff | -s> | id', res, eff' |
->
  exists l, eff' = eff ++ l).
Proof.
  apply eval_ind; intros; try assumption.
  * subst. rewrite e0 in H.
    apply effect_extension_list. exact H.
  * rewrite <- e0 in H. apply effect_extension_list in H.
    destruct H. rewrite H in H0.
    destruct H0. exists (x ++ x0). rewrite <- app_assoc in H0. auto.
  * exists []; rewrite app_nil_r; auto.
  * exists []; rewrite app_nil_r; auto.
  * exists []; rewrite app_nil_r; auto.
  * exists []; rewrite app_nil_r; auto.
  * exists []; rewrite app_nil_r; auto.
  * rewrite e3. eapply effect_extension_list. rewrite e0 in H. auto.
  * destruct H. destruct H0. exists (x ++ x0).
    subst. rewrite app_assoc. auto.
  * destruct H, H1, H2. rewrite H in H2. rewrite <- app_assoc in H2.
    eexists. exact H2.
  * rewrite e0 in H. apply effect_extension_list in H. destruct H.
    rewrite H in e3 at 1. subst. apply eval_effect_extension in e3.
    destruct e3. rewrite <- app_assoc in H0. eexists. exact H0.
  * rewrite e0 in H. apply effect_extension_list in H. destruct H.
    rewrite H in e3 at 1. subst. apply eval_effect_extension in e3.
    destruct e3. rewrite <- app_assoc in H0. eexists. exact H0.
  * rewrite e2 in H0. destruct H. apply effect_extension_list in H0.
    destruct H0, H1. rewrite H in *. rewrite H0 in H1 at 1.
    rewrite <- app_assoc, <- app_assoc in H1. eexists. exact H1.
  * destruct H, H0. rewrite H in H0. rewrite <- app_assoc in H0.
    eexists. exact H0.
  * destruct H, H0. rewrite H in H0. rewrite <- app_assoc in H0.
    eexists. exact H0.
  * unfold exps in H. rewrite length_make_map_exps in H. rewrite e1 in H.
    rewrite e6. apply effect_extension_list. exact H.
  * destruct H, H0. rewrite H in H0. rewrite <- app_assoc in H0.
    eexists. exact H0.
  * rewrite <- e0 in H. apply effect_extension_list in H.
    destruct H, H0. rewrite H in H0 at 1.
    exists (x ++ x0). rewrite <- app_assoc in H0. auto.
  * destruct H, H0. rewrite H in H0. rewrite <- app_assoc in H0.
    eexists. exact H0.
  * destruct H, H0. rewrite H in H0. rewrite <- app_assoc in H0.
    eexists. exact H0.
  * rewrite <- e0 in H. apply effect_extension_list in H.
    destruct H, H0. rewrite H in H0 at 1.
    exists (x ++ x0). rewrite <- app_assoc in H0. auto.
  * rewrite <- e0 in H. apply effect_extension_list in H.
    destruct H, H0. rewrite H in H0 at 1.
    exists (x ++ x0). rewrite <- app_assoc in H0. auto.
  * destruct H.
    rewrite <- e0 in H0. apply effect_extension_list in H0.
    destruct H0, H1. rewrite H in *. rewrite H0 in H1 at 1.
    eexists. rewrite <- app_assoc, <- app_assoc in H1. exact H1.
  * destruct H.
    rewrite e0 in H0. apply effect_extension_list in H0.
    destruct H0. rewrite H in *.
    eexists. rewrite <- app_assoc in H0. rewrite e4. exact H0.
  * destruct H.
    rewrite e0 in H0. apply effect_extension_list in H0.
    destruct H0. rewrite H in *.
    eexists. rewrite <- app_assoc in H0. rewrite e4. exact H0.
  * rewrite <- e1 in H. apply effect_extension_list in H. destruct H, H0.
    eexists. rewrite H in H0 at 1. rewrite <- app_assoc in H0. exact H0.
Qed.

Theorem effect_extension_expr :
(forall {env id e eff id' res eff'},
  | env, id, e, eff | -e> | id', res, eff' |
->
  exists l, eff' = eff ++ l)
.
Proof.
  apply effect_extension.
Qed.

Theorem effect_extension_single :
(forall {env id e eff id' res eff'},
  | env, id, e, eff | -s> | id', res, eff' |
->
  exists l, eff' = eff ++ l).
Proof.
  apply effect_extension.
Qed.

Lemma effect_extension_values_single el :
forall env id0 eff id' res eff' clock,
fbs_values (fbs_single clock) env id0 el eff = Result id' res eff'
->
exists l, eff' = eff ++ l.
Proof.
  induction el; intros.
  * simpl in H. inversion H. subst. exists []. rewrite app_nil_r. auto.
  * simpl in H.
    destruct (fbs_single clock env id0 a eff) eqn:D.
    destruct res0. destruct v. congruence. destruct v0. 2: congruence.
    3-4: congruence.
    - apply fbs_single_correctness in D. apply effect_extension_single in D.
      destruct D. subst.
      destruct (fbs_values (fbs_single clock) env id el (eff ++ x)) eqn:D2.
      destruct res0. 3-4: congruence.
      + inversion H. apply IHel in D2. destruct D2. subst.
        exists (x ++ x0). rewrite <- app_assoc. auto.
      + inversion H. subst. apply IHel in D2. destruct D2. rewrite <- app_assoc in H0.
        exists (x ++ x0). assumption.
    - inversion H. subst. apply fbs_single_correctness in D.
      apply effect_extension_single in D. exact D.
Qed.

Lemma effect_extension_values_expr el :
forall env id0 eff id' res eff' clock,
fbs_values (fbs_expr clock) env id0 el eff = Result id' res eff'
->
exists l, eff' = eff ++ l.
Proof.
  induction el; intros.
  * simpl in H. inversion H. subst. exists []. rewrite app_nil_r. auto.
  * simpl in H.
    destruct (fbs_expr clock env id0 a eff) eqn:D.
    destruct res0. destruct v. congruence. destruct v0. 2: congruence.
    3-4: congruence.
    - apply fbs_expr_correctness in D. apply effect_extension_expr in D.
      destruct D. subst.
      destruct (fbs_values (fbs_expr clock) env id el (eff ++ x)) eqn:D2.
      destruct res0. 3-4: congruence.
      + inversion H. apply IHel in D2. destruct D2. subst.
        exists (x ++ x0). rewrite <- app_assoc. auto.
      + inversion H. subst. apply IHel in D2. destruct D2. rewrite <- app_assoc in H0.
        exists (x ++ x0). assumption.
    - inversion H. subst. apply fbs_expr_correctness in D.
      apply effect_extension_expr in D. exact D.
Qed.

Lemma single_list_effectlist_irrelevant el :
  forall env id eff id' res eff' clock,
  (forall (env : Environment) (id : nat) (e : SingleExpression) 
            (eff : SideEffectList) (id' : nat) (res : ValueSequence + Exception)
            (eff' : list (SideEffectId * list Value)),
          fbs_single clock env id e eff = Result id' res (eff ++ eff') ->
          forall eff0 : SideEffectList,
          fbs_single clock env id e eff0 = Result id' res (eff0 ++ eff'))
  ->
  fbs_values (fbs_single clock) env id el eff = Result id' res (eff ++ eff')
->
  forall eff0, fbs_values (fbs_single clock) env id el eff0 = Result id' res (eff0 ++ eff').
Proof.
  induction el; intros.
  * simpl in *. inversion H0. rewrite <- app_nil_r in H4 at 1. apply app_inv_head in H4.
    subst. rewrite app_nil_r. reflexivity.
  * simpl in H0. simpl. destruct (fbs_single clock env id a eff) eqn:D1.
    destruct res0. destruct v. congruence. destruct v0. 2: congruence.
    3-4: congruence.
    - remember D1 as D1'. clear HeqD1'. apply fbs_single_correctness in D1.
      pose (effect_extension_single D1). destruct e. subst.
      apply H with (eff0 := eff0) in D1'. rewrite D1'.
      destruct (fbs_values (fbs_single clock) env id0 el (eff ++ x)) eqn:D2.
      destruct res0. 3-4: congruence.
      + inversion H0. subst.
        pose (P := effect_extension_values_single _ _ _ _ _ _ _ _ D2). destruct P.
        rewrite <- app_assoc in H1. apply app_inv_head in H1. subst.
        rewrite app_assoc in D2.
        epose (IHel env id0 (eff ++ x) id' _ _ clock H D2 (eff0 ++ x)).
        rewrite e. rewrite app_assoc. reflexivity.
      + inversion H0.
        pose (P := effect_extension_values_single _ _ _ _ _ _ _ _ D2). destruct P.
        rewrite <- app_assoc in H1. subst. apply app_inv_head in H1. subst.
        rewrite app_assoc in D2.
        epose (IHel env id0 (eff ++ x) id' _ _ clock H D2 (eff0 ++ x)).
        rewrite e0. rewrite app_assoc. reflexivity.
    - inversion H0. subst. eapply H in D1. rewrite D1. reflexivity.
Qed.

Lemma expr_list_effectlist_irrelevant el :
  forall env id eff id' res eff' clock,
  (forall (env : Environment) (id : nat) (e : Expression) 
            (eff : SideEffectList) (id' : nat) (res : ValueSequence + Exception)
            (eff' : list (SideEffectId * list Value)),
          fbs_expr clock env id e eff = Result id' res (eff ++ eff') ->
          forall eff0 : SideEffectList,
          fbs_expr clock env id e eff0 = Result id' res (eff0 ++ eff'))
  ->
  fbs_values (fbs_expr clock) env id el eff = Result id' res (eff ++ eff')
->
  forall eff0, fbs_values (fbs_expr clock) env id el eff0 = Result id' res (eff0 ++ eff').
Proof.
  induction el; intros.
  * simpl in *. inversion H0. rewrite <- app_nil_r in H4 at 1. apply app_inv_head in H4.
    subst. rewrite app_nil_r. reflexivity.
  * simpl in H0. simpl. destruct (fbs_expr clock env id a eff) eqn:D1.
    destruct res0. destruct v. congruence. destruct v0. 2: congruence.
    3-4: congruence.
    - remember D1 as D1'. clear HeqD1'. apply fbs_expr_correctness in D1.
      pose (effect_extension_expr D1). destruct e. subst.
      apply H with (eff0 := eff0) in D1'. rewrite D1'.
      destruct (fbs_values (fbs_expr clock) env id0 el (eff ++ x)) eqn:D2.
      destruct res0. 3-4: congruence.
      + inversion H0. subst.
        pose (P := effect_extension_values_expr _ _ _ _ _ _ _ _ D2). destruct P.
        rewrite <- app_assoc in H1. apply app_inv_head in H1. subst.
        rewrite app_assoc in D2.
        epose (IHel env id0 (eff ++ x) id' _ _ clock H D2 (eff0 ++ x)).
        rewrite e. rewrite app_assoc. reflexivity.
      + inversion H0.
        pose (P := effect_extension_values_expr _ _ _ _ _ _ _ _ D2). destruct P.
        rewrite <- app_assoc in H1. subst. apply app_inv_head in H1. subst.
        rewrite app_assoc in D2.
        epose (IHel env id0 (eff ++ x) id' _ _ clock H D2 (eff0 ++ x)).
        rewrite e0. rewrite app_assoc. reflexivity.
    - inversion H0. subst. eapply H in D1. rewrite D1. reflexivity.
Qed.

Lemma effectlist_irrelevant_case l :
forall env id0 eff v id' res eff' clock,
fbs_case l env id0 eff v (fbs_expr clock) = Result id' res (eff ++ eff')
->
(forall (env : Environment) (id : nat) (e : Expression) 
            (eff : SideEffectList) (id' : nat) (res : ValueSequence + Exception)
            (eff' : list (SideEffectId * list Value)),
          fbs_expr clock env id e eff = Result id' res (eff ++ eff') ->
          forall eff0 : SideEffectList,
          fbs_expr clock env id e eff0 = Result id' res (eff0 ++ eff'))
->
forall eff0, fbs_case l env id0 eff0 v (fbs_expr clock) = Result id' res (eff0 ++ eff').
Proof.
  induction l; intros.
  * simpl in *. inversion H. rewrite <- app_nil_r in H4 at 1. apply app_inv_head in H4.
    subst. rewrite app_nil_r. reflexivity.
  * simpl in *. destruct a, p.
    destruct (match_valuelist_to_patternlist v l0).
    - destruct (fbs_expr clock (add_bindings (match_valuelist_bind_patternlist v l0) env) id0 e0 eff) eqn:D1.
      destruct res0. destruct v0. congruence. destruct v1. 2: congruence.
      2-4: congruence. remember D1 as D1'. clear HeqD1'.
      apply fbs_expr_correctness, effect_extension_expr in D1. destruct D1. subst.
      eapply H0 in D1'. rewrite D1'.
      destruct (((id =? id0) && list_eqb effect_eqb eff (eff ++ x))%bool) eqn:D2.
      + apply andb_prop in D2. destruct D2.
        apply Nat.eqb_eq in H1. apply side_effect_list_eqb_eq in H2.
        rewrite <- app_nil_r in H2 at 1. apply app_inv_head in H2. subst.
        rewrite app_nil_r. rewrite Nat.eqb_refl, list_effect_eqb_refl. simpl.
        destruct v0; try congruence. destruct l1; try congruence.
        destruct (s =? "true")%string.
        ** eapply H0 in H. exact H.
        ** destruct (s =? "false")%string. 2: congruence.
           eapply IHl. exact H.
           intros. eapply H0. exact H1.
      + congruence.
    - eapply IHl. exact H. intros. eapply H0. exact H1.
Qed.

Theorem effect_extension_case l :
forall env id0 eff v id' res eff' clock,
fbs_case l env id0 eff v (fbs_expr clock) = Result id' res eff'
->
exists l', eff' = eff ++ l'.
Proof.
  induction l; intros.
  * simpl in H. inversion H. exists []. rewrite app_nil_r. auto.
  * simpl in H. destruct a, p.
    destruct (match_valuelist_to_patternlist v l0).
    - destruct (fbs_expr clock (add_bindings (match_valuelist_bind_patternlist v l0) env) id0 e0 eff) eqn:D1.
      destruct res0. destruct v0. congruence. destruct v1. 2: congruence.
      2-4: congruence.
      destruct (((id =? id0) && list_eqb effect_eqb eff eff0)%bool) eqn:D2.
      2: congruence.
      destruct v0; try congruence. destruct l1; try congruence.
      destruct ((s =? "true")%string).
      + apply andb_prop in D2. destruct D2. apply Nat.eqb_eq in H0.
        apply side_effect_list_eqb_eq in H1. subst.
        apply fbs_expr_correctness, effect_extension_expr in D1. destruct D1.
        rewrite <- app_nil_r in H0 at 1. apply app_inv_head in H0. subst.
        apply fbs_expr_correctness, effect_extension_expr in H. assumption.
      + destruct (s =? "false")%string. 2: congruence.
        eapply IHl. exact H.
    - eapply IHl. exact H.
Qed.

Theorem effectlist_irrelevant_fbs_expr :
(forall clock env id e eff id' res eff',
  fbs_expr clock env id e eff = Result id' res (eff ++ eff')
->
forall eff0,
  fbs_expr clock env id e eff0 = Result id' res (eff0 ++ eff'))
with effectlist_irrelevant_fbs_single :
(forall clock env id e eff id' res eff',
  fbs_single clock env id e eff = Result id' res (eff ++ eff')
->
forall eff0,
  fbs_single clock env id e eff0 = Result id' res (eff0 ++ eff')).
Proof.
{
  induction clock; intros.
  * simpl in H. inversion H.
  * destruct e; subst.
    - simpl. simpl in H. eapply single_list_effectlist_irrelevant.
      2: exact H. intros. eapply effectlist_irrelevant_fbs_single. exact H0.
    - simpl in *. eapply effectlist_irrelevant_fbs_single. exact H.
}
{
  induction clock; intros.
  * simpl in H. inversion H.
  * destruct e; subst.
    - simpl in H; inversion H. simpl. rewrite <- app_nil_r in H3 at 1.
      apply app_inv_head in H3. subst. rewrite app_nil_r. reflexivity.
    - simpl in H; inversion H. simpl. rewrite <- app_nil_r in H3 at 1.
      apply app_inv_head in H3. subst. rewrite app_nil_r. reflexivity.
    - simpl in H. simpl. destruct (get_value env (inl v)). 2: congruence.
      inversion H. rewrite <- app_nil_r in H3 at 1.
      apply app_inv_head in H3. subst. rewrite app_nil_r. reflexivity.
    - simpl in H. simpl. destruct (get_value env (inr f)). 2: congruence.
      inversion H. rewrite <- app_nil_r in H3 at 1.
      apply app_inv_head in H3. subst. rewrite app_nil_r. reflexivity.
    - simpl in H; inversion H. simpl. rewrite <- app_nil_r in H3 at 1.
      apply app_inv_head in H3. subst. rewrite app_nil_r. reflexivity.
    - simpl in H. simpl.
      destruct (fbs_expr clock env id tl eff) eqn:D1.
      destruct res0. destruct v. congruence. destruct v0. 2: congruence.
      3-4: congruence.
      + remember D1 as D1'. clear HeqD1'. apply fbs_expr_correctness in D1.
        epose (effect_extension_expr D1). destruct e. subst.
        apply effectlist_irrelevant_fbs_expr with (eff0 := eff0) in D1'.
        destruct (fbs_expr clock env id0 hd (eff ++ x)) eqn:D2.
        destruct res0. destruct v0. congruence. destruct v1. 2: congruence.
        3-4: congruence.
        ** remember D2 as D2'. clear HeqD2'. apply fbs_expr_correctness in D2.
           epose (effect_extension_expr D2). destruct e. subst.
           apply effectlist_irrelevant_fbs_expr with (eff0 := eff0 ++ x) in D2'.
           rewrite D1', D2'. inversion H. rewrite <- app_assoc in H3.
           apply app_inv_head in H3. subst. rewrite <- app_assoc. reflexivity.
        ** remember D2 as D2'. clear HeqD2'. apply fbs_expr_correctness in D2.
           epose (effect_extension_expr D2). destruct e0. subst.
           apply effectlist_irrelevant_fbs_expr with (eff0 := eff0 ++ x) in D2'.
           rewrite D1', D2'. inversion H. rewrite <- app_assoc in H3.
           apply app_inv_head in H3. subst. rewrite <- app_assoc. reflexivity.
      + remember D1 as D1'. clear HeqD1'. apply fbs_expr_correctness in D1.
        epose (effect_extension_expr D1). destruct e0. subst.
        apply effectlist_irrelevant_fbs_expr with (eff0 := eff0) in D1'.
        rewrite D1'. inversion H. apply app_inv_head in H3. subst. reflexivity.
    - simpl. simpl in H. destruct (fbs_values (fbs_expr clock) env id l eff) eqn:D1.
      destruct res0. 3-4: congruence.
      + inversion H. subst. eapply expr_list_effectlist_irrelevant in D1.
        rewrite D1. reflexivity. intros. eapply effectlist_irrelevant_fbs_expr in H0. exact H0.
      + inversion H. subst. eapply expr_list_effectlist_irrelevant in D1.
        rewrite D1. reflexivity. intros. eapply effectlist_irrelevant_fbs_expr in H0. exact H0.
    - simpl. simpl in H. destruct (fbs_values (fbs_expr clock) env id l eff) eqn:D1.
      destruct res0. 3-4: congruence.
      + inversion H. subst. remember D1 as D1'. clear HeqD1'.
        eapply effect_extension_values_expr in D1. destruct D1. subst.
        eapply expr_list_effectlist_irrelevant in D1'. rewrite D1'.
        remember H3 as H3'. clear HeqH3'.
        eapply eval_effect_extension_snd in H3. destruct H3.
        rewrite <- app_assoc in H0. apply app_inv_head in H0. subst.
        rewrite app_assoc in H3'.
        epose (P := @eval_effect_irrelevant_snd _ _ (eff ++ x) x0 H3' (eff0 ++ x)).
        rewrite P. rewrite <- app_assoc. erewrite eval_effect_irrelevant_fst. reflexivity.
        intros. eapply effectlist_irrelevant_fbs_expr. exact H0.
      + inversion H. subst.
        eapply expr_list_effectlist_irrelevant in D1. rewrite D1. reflexivity.
        intros. eapply effectlist_irrelevant_fbs_expr. exact H0.
    - simpl. simpl in H. destruct (fbs_values (fbs_expr clock) env id l eff) eqn:D1.
      destruct res0. 3-4: congruence.
      + inversion H. subst. remember D1 as D1'. clear HeqD1'.
        eapply effect_extension_values_expr in D1. destruct D1. subst.
        eapply expr_list_effectlist_irrelevant in D1'. rewrite D1'.
        remember H3 as H3'. clear HeqH3'.
        eapply eval_effect_extension_snd in H3. destruct H3.
        rewrite <- app_assoc in H0. apply app_inv_head in H0. subst.
        rewrite app_assoc in H3'.
        epose (P := @eval_effect_irrelevant_snd _ _ (eff ++ x) x0 H3' (eff0 ++ x)).
        rewrite P. rewrite <- app_assoc. erewrite eval_effect_irrelevant_fst. reflexivity.
        intros. eapply effectlist_irrelevant_fbs_expr. exact H0.
      + inversion H. subst.
        eapply expr_list_effectlist_irrelevant in D1. rewrite D1. reflexivity.
        intros. eapply effectlist_irrelevant_fbs_expr. exact H0.
    - simpl. simpl in H. destruct (fbs_expr clock env id exp eff) eqn:D1.
      destruct res0. destruct v. congruence. destruct v0. 2: congruence. 3-4: congruence.
      + remember D1 as D1'. clear HeqD1'.
        eapply fbs_expr_correctness, effect_extension_expr in D1. destruct D1. subst.
        eapply effectlist_irrelevant_fbs_expr in D1'. rewrite D1'.
        destruct (fbs_values (fbs_expr clock) env id0 l (eff ++ x)) eqn:D2.
        destruct res0. 3-4: congruence.
        ** remember D2 as D2'. clear HeqD2'.
           eapply effect_extension_values_expr in D2. destruct D2. subst.
           eapply expr_list_effectlist_irrelevant in D2'. rewrite D2'.
           destruct v.
           1-2, 4-6: inversion H; subst; rewrite <- app_assoc in H3;
                     apply app_inv_head in H3; subst; rewrite app_assoc; reflexivity.
           -- destruct (length vl =? length v0) eqn:D3.
              ++ rewrite <- app_assoc in H. remember H as H'. clear HeqH'.
                 eapply fbs_expr_correctness, effect_extension_expr in H. destruct H.
                 rewrite <- app_assoc, <- app_assoc in H. apply app_inv_head in H. subst.
                 replace (eff ++ x ++ x0 ++ x1) with ((eff ++ x ++ x0) ++ x1) in H'.
                 apply effectlist_irrelevant_fbs_expr with (eff0 := eff0 ++ x ++ x0) in H'.
                 repeat rewrite <- app_assoc in *. exact H'.
                 repeat rewrite <- app_assoc in *. auto.
              ++ inversion H; subst; rewrite <- app_assoc in H3;
                 apply app_inv_head in H3; subst; rewrite app_assoc; reflexivity.
           -- intros. eapply effectlist_irrelevant_fbs_expr. exact H0.
        ** inversion H. subst. remember D2 as D2'. clear HeqD2'.
           eapply effect_extension_values_expr in D2. destruct D2.
           rewrite <- app_assoc in H0. apply app_inv_head in H0. subst.
           rewrite app_assoc in D2'.
           eapply expr_list_effectlist_irrelevant in D2'. rewrite D2'.
           rewrite <- app_assoc. reflexivity.
           intros. eapply effectlist_irrelevant_fbs_expr. exact H0.
      + inversion H. subst. eapply effectlist_irrelevant_fbs_expr in D1. rewrite D1.
        reflexivity.
    - simpl in H. simpl. destruct (fbs_expr clock env id e eff) eqn:D1.
      destruct res0. 3-4: congruence.
      + remember D1 as D1'. clear HeqD1'.
        eapply fbs_expr_correctness, effect_extension_expr in D1. destruct D1. subst.
        eapply effectlist_irrelevant_fbs_expr in D1'. rewrite D1'.
        remember H as H'. clear HeqH'. eapply effect_extension_case in H. destruct H.
        rewrite <- app_assoc in H. apply app_inv_head in H. subst.
        rewrite app_assoc in H'. eapply effectlist_irrelevant_case in H'.
        rewrite app_assoc. exact H'.
        intros. eapply effectlist_irrelevant_fbs_expr. exact H.
      + inversion H. subst. eapply effectlist_irrelevant_fbs_expr in D1.
        rewrite D1. reflexivity.
    - simpl in H. simpl. destruct (fbs_expr clock env id e1 eff) eqn:D1.
      destruct res0. 3-4: congruence.
      + remember D1 as D1'. clear HeqD1'.
        eapply fbs_expr_correctness, effect_extension_expr in D1. destruct D1. subst.
        eapply effectlist_irrelevant_fbs_expr in D1'. rewrite D1'.
        destruct (length v =? length l). 2: congruence.
        remember H as H'. clear HeqH'.
        eapply fbs_expr_correctness, effect_extension_expr in H. destruct H.
        rewrite <- app_assoc in H. apply app_inv_head in H. subst.
        rewrite app_assoc in H'.
        eapply effectlist_irrelevant_fbs_expr in H'. rewrite H'. rewrite app_assoc.
        reflexivity.
      + inversion H. subst. remember D1 as D1'. clear HeqD1'.
        eapply fbs_expr_correctness, effect_extension_expr in D1. destruct D1. subst.
        eapply effectlist_irrelevant_fbs_expr in D1'. rewrite D1'. reflexivity.
    - simpl in H. simpl. destruct (fbs_expr clock env id e1 eff) eqn:D1.
      destruct res0. destruct v. congruence. destruct v0. 2: congruence. 3-4: congruence.
      + remember D1 as D1'. clear HeqD1'.
        eapply fbs_expr_correctness, effect_extension_expr in D1. destruct D1. subst.
        eapply effectlist_irrelevant_fbs_expr in D1'. rewrite D1'.
        remember H as H'. clear HeqH'.
        eapply fbs_expr_correctness, effect_extension_expr in H. destruct H.
        rewrite <- app_assoc in H. apply app_inv_head in H. subst.
        rewrite app_assoc in H'.
        eapply effectlist_irrelevant_fbs_expr in H'. rewrite H'. rewrite app_assoc.
        reflexivity.
      + inversion H. subst. remember D1 as D1'. clear HeqD1'.
        eapply fbs_expr_correctness, effect_extension_expr in D1. destruct D1. subst.
        eapply effectlist_irrelevant_fbs_expr in D1'. rewrite D1'. reflexivity.
    - eapply effectlist_irrelevant_fbs_expr. exact H.
    - simpl. simpl in H.
      destruct (fbs_values (fbs_expr clock) env id (make_map_exps l) eff) eqn:D1.
      destruct res0. 3-4: congruence.
      + destruct (make_map_vals_inverse v) eqn:D2. 2: congruence. destruct p.
        remember D1 as D1'. clear HeqD1'.
        eapply effect_extension_values_expr in D1. destruct D1. subst.
        eapply expr_list_effectlist_irrelevant in D1'. rewrite D1'. rewrite D2.
        inversion H. subst. apply app_inv_head in H3. subst. reflexivity.
        intros. eapply effectlist_irrelevant_fbs_expr. exact H0.
      + inversion H. subst.
        eapply expr_list_effectlist_irrelevant in D1. rewrite D1. reflexivity.
        intros. eapply effectlist_irrelevant_fbs_expr. exact H0.
    - simpl in H. simpl. destruct (fbs_expr clock env id e1 eff) eqn:D1.
      destruct res0. 3-4: congruence.
      + remember D1 as D1'. clear HeqD1'.
        eapply fbs_expr_correctness, effect_extension_expr in D1. destruct D1. subst.
        eapply effectlist_irrelevant_fbs_expr in D1'. rewrite D1'.
        remember H as H'. clear HeqH'. destruct (length v =? length vl1). 2: congruence.
        eapply fbs_expr_correctness, effect_extension_expr in H. destruct H.
        rewrite <- app_assoc in H. apply app_inv_head in H. subst.
        rewrite app_assoc in H'.
        eapply effectlist_irrelevant_fbs_expr in H'. rewrite H'. rewrite app_assoc.
        reflexivity.
      + remember D1 as D1'. clear HeqD1'.
        eapply fbs_expr_correctness, effect_extension_expr in D1. destruct D1. subst.
        eapply effectlist_irrelevant_fbs_expr in D1'. rewrite D1'.
        remember H as H'. clear HeqH'.
        eapply fbs_expr_correctness, effect_extension_expr in H. destruct H.
        rewrite <- app_assoc in H. apply app_inv_head in H. subst.
        rewrite app_assoc in H'.
        eapply effectlist_irrelevant_fbs_expr in H'. rewrite H'. rewrite app_assoc.
        reflexivity.
}
Qed.

Theorem effectlist_irrelevant_expr :
forall env id e eff id' res eff',
  |env, id, e, eff| -e> | id', res, eff ++ eff'|
->
forall eff0,
  | env, id, e, eff0 | -e> |id', res, eff0 ++ eff'|.
Proof.
  intros. apply fbs_soundness in H. destruct H.
  eapply effectlist_irrelevant_fbs_expr in H.
  apply fbs_expr_correctness in H. exact H.
Qed.

Theorem effectlist_irrelevant_single :
forall env id e eff id' res eff',
  |env, id, e, eff| -s> | id', res, eff ++ eff'|
->
forall eff0,
  | env, id, e, eff0 | -s> |id', res, eff0 ++ eff'|.
Proof.
  intros. apply fbs_soundness in H. destruct H.
  eapply effectlist_irrelevant_fbs_single in H.
  apply fbs_single_correctness in H. exact H.
Qed.

End helpers.

Section equivalence_relation.

Theorem weak_refl {e} :
  weakly_equivalent e e.
Proof.
  unfold weakly_equivalent. split; intros.
  eexists. split. apply H. apply Permutation_refl.
  eexists. split. apply H. apply Permutation_refl.
Qed.

Theorem weak_sym {e1 e2} :
  weakly_equivalent e1 e2
->
  weakly_equivalent e2 e1.
Proof.
  unfold weakly_equivalent. split; intros.
  destruct H. apply H1 in H0. exact H0.
  destruct H. apply H in H0. exact H0.
Qed.

Theorem weak_trans {e1 e2 e3} :
  weakly_equivalent e1 e2 -> weakly_equivalent e2 e3
->
  weakly_equivalent e1 e3.
Proof.
  unfold weakly_equivalent. split; intros;
  destruct H, H0.
  * apply H in H1. destruct H1, H1. apply H0 in H1. destruct H1, H1. eexists.
    split. exact H1. eapply Permutation_trans. exact H4. exact H5.
  * apply H3 in H1. destruct H1, H1. apply H2 in H1. destruct H1, H1. eexists.
    split. exact H1. eapply Permutation_trans. exact H4. exact H5.
Qed.

Theorem weak_single_refl {e} :
  weakly_equivalent_single e e.
Proof.
  unfold weakly_equivalent_single. split; intros.
  eexists. split. apply H. apply Permutation_refl.
  eexists. split. apply H. apply Permutation_refl.
Qed.

Theorem weak_single_sym {e1 e2} :
  weakly_equivalent_single e1 e2
->
  weakly_equivalent_single e2 e1.
Proof.
  unfold weakly_equivalent_single. split; intros.
  destruct H. apply H1 in H0. exact H0.
  destruct H. apply H in H0. exact H0.
Qed.

Theorem weak_single_trans {e1 e2 e3} :
  weakly_equivalent_single e1 e2 -> weakly_equivalent_single e2 e3
->
  weakly_equivalent_single e1 e3.
Proof.
  unfold weakly_equivalent_single. split; intros;
  destruct H, H0.
  * apply H in H1. destruct H1, H1. apply H0 in H1. destruct H1, H1. eexists.
    split. exact H1. eapply Permutation_trans. exact H4. exact H5.
  * apply H3 in H1. destruct H1, H1. apply H2 in H1. destruct H1, H1. eexists.
    split. exact H1. eapply Permutation_trans. exact H4. exact H5.
Qed.

End equivalence_relation.

Section congruence.

Lemma nth_last_eq {A : Type} (l : list A) : forall e,
  forall d1 d2, nth (length l) (e::l) d1 = last (e::l) d2.
Proof.
  induction l using list_length_ind; intros.
  destruct l.
  * simpl. auto.
  * simpl. destruct (length l) eqn:HH.
    - apply length_zero_iff_nil in HH. subst. auto.
    - pose (element_exist _ _ (eq_sym HH)). destruct e0. destruct H0. subst.
      inversion HH. apply H. simpl. lia.
Qed.

Definition transform_with {A : Type} (l : list (list A)) (addition : list A) : list (list A) :=
  map (fun x => addition ++ x) l.


Lemma effect_extension_exprlist_fbs exps :
forall c env id0 eff0 id' res eff',
  fbs_values (fbs_expr c) env id0 exps eff0 = Result id' res eff'
->
  exists l, eff' = eff0 ++ l.
Proof.
  induction exps; intros.
  * exists []. simpl in H. inversion H. subst. rewrite app_nil_r. auto.
  * simpl in H. destruct (fbs_expr c env id0 a eff0) eqn:D1. destruct res0.
    destruct v. congruence. destruct v0. 2: congruence. 3-4: congruence.
    - apply fbs_expr_correctness in D1 as D1'.
      apply effect_extension_expr in D1'. destruct D1'. subst.
      destruct (fbs_values (fbs_expr c) env id exps (eff0 ++ x)) eqn:D2.
      destruct res0. 3-4: congruence.
      + inversion H. subst. apply IHexps in D2. destruct D2. subst.
        exists (x ++ x0). rewrite <- app_assoc. auto.
      + inversion H. subst. apply IHexps in D2. destruct D2. subst.
        exists (x ++ x0). rewrite <- app_assoc. auto.
    - inversion H. subst.
      apply fbs_expr_correctness in D1 as D1'.
      apply effect_extension_expr in D1'. destruct D1'. subst.
      exists x. auto.
Qed.

Lemma effectlist_irrelevant_exprlist_fbs exps :
forall c env id0 id' res eff0 ad,
  fbs_values (fbs_expr c) env id0 exps eff0 = Result id' res (eff0 ++ ad)
->
  forall eff1, 
  fbs_values (fbs_expr c) env id0 exps eff1 = Result id' res (eff1 ++ ad).
Proof.
  intros. apply expr_list_effectlist_irrelevant with eff0. 2: auto.
  intros. eapply effectlist_irrelevant_fbs_expr. exact H0.
Qed.

Lemma exprlist_cong_fbs (l : list Expression) :
forall (l' : list Expression) clock env id eff id' res eff',
   length l = length l' ->
   (forall i, i < length l -> weakly_equivalent (nth i l ErrorExp) (nth i l' ErrorExp)) ->
  fbs_values (fbs_expr clock) env id l eff = Result id' res eff'
->
  exists cl eff'', fbs_values (fbs_expr cl) env id l' eff = Result id' res eff'' /\ Permutation eff' eff''.
Proof.
  induction l; intros.
  * inversion H1. subst. exists clock, eff'.
    apply eq_sym, length_zero_iff_nil in H. subst. simpl. split; auto.
  * pose (element_exist _ _ H). destruct e. destruct H2. subst.
    pose (EQ0 := H0 0 (Nat.lt_0_succ _)). simpl in EQ0.
    simpl in H1. destruct (fbs_expr clock env id a eff) eqn:D1.
    destruct res0. destruct v. congruence. destruct v0. 2: congruence.
    3-4: congruence.
    - destruct (fbs_values (fbs_expr clock) env id0 l eff0) eqn:D2.
      destruct res0. 3-4: congruence.
      + apply fbs_expr_correctness in D1.
        apply effect_extension_expr in D1 as HH. destruct HH. subst.
        apply EQ0 in D1. destruct D1, H2.
        apply effect_extension_expr in H2 as HH.
        apply fbs_soundness in H2.
        destruct H2, HH. subst.

        apply effect_extension_exprlist_fbs in D2 as D2'. destruct D2'. subst.
        apply IHl with (l' := x0) in D2. destruct D2, H4, H4.
        2: simpl in H; lia.
        2: { intros. epose (H0 (S i) _). exact w. Unshelve. simpl. lia. }
        apply effect_extension_exprlist_fbs in H4 as HH. destruct HH. subst.
        inversion H1. subst.

        exists (x3 + x5), (eff ++ x4 ++ x7). simpl.
        apply bigger_clock_expr with (clock' := x3 + x5) in H2. 2: lia.
        rewrite H2.
        apply bigger_clock_list with (clock' := x3 + x5) in H4. 2: lia.
        apply effectlist_irrelevant_exprlist_fbs with (eff1 := eff ++ x4) in H4.
        2: { intros. apply clock_increase_expr. exact H6. }
        rewrite H4. split; rewrite <- app_assoc.
        ** auto.
        ** apply Permutation_app_head. apply Permutation_app_inv_l in H3.
           apply Permutation_app_inv_l in H5. apply Permutation_app; auto.
      + apply fbs_expr_correctness in D1.
        apply effect_extension_expr in D1 as HH. destruct HH. subst.
        apply EQ0 in D1. destruct D1, H2.
        apply effect_extension_expr in H2 as HH.
        apply fbs_soundness in H2.
        destruct H2, HH. subst.

        apply effect_extension_exprlist_fbs in D2 as D2'. destruct D2'. subst.
        apply IHl with (l' := x0) in D2. destruct D2, H4, H4.
        2: simpl in H; lia.
        2: { intros. epose (H0 (S i) _). exact w. Unshelve. simpl. lia. }
        apply effect_extension_exprlist_fbs in H4 as HH. destruct HH. subst.
        inversion H1. subst.

        exists (x3 + x5), (eff ++ x4 ++ x7). simpl.
        apply bigger_clock_expr with (clock' := x3 + x5) in H2. 2: lia.
        rewrite H2.
        apply bigger_clock_list with (clock' := x3 + x5) in H4. 2: lia.
        apply effectlist_irrelevant_exprlist_fbs with (eff1 := eff ++ x4) in H4.
        2: { intros. apply clock_increase_expr. exact H6. }
        rewrite H4. split; rewrite <- app_assoc.
        ** auto.
        ** apply Permutation_app_head. apply Permutation_app_inv_l in H3.
           apply Permutation_app_inv_l in H5. apply Permutation_app; auto.
    - inversion H1. subst. apply fbs_expr_correctness in D1.
      apply EQ0 in D1. destruct D1. destruct H2.
      apply fbs_soundness in H2. destruct H2. exists x2, x1.
      simpl. rewrite H2; auto.
Qed.

(* Lemma exprlist_congruence (l : list Expression) :
forall (l' : list Expression) vals eff0 ids env id eff,
  (forall i, i < length l -> weakly_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
  ->
  (forall i : nat,
       i < length l ->
       | env, nth_def ids id 0 i, nth i l ErrorExp, eff ++ nth_def eff0 [] [] i | -e>
       | nth_def ids id 0 (S i), inl [nth i vals ErrorValue], eff ++ nth_def eff0 [] [] (S i) |)
  ->
  length l = length l' ->
  length l = length vals ->
  length l = length eff0 ->
  length l = length ids
->
  (exists effs, length l = length effs /\ 
    (forall i : nat, i < length l' ->
    | env, nth_def ids id 0 i, nth i l' ErrorExp, eff ++ nth_def effs [] [] i | -e>
    | nth_def ids id 0 (S i), inl [nth i vals ErrorValue], eff ++ nth_def effs [] [] (S i)| /\
    Permutation (nth i eff0 []) (nth i effs []))
  ).
Proof.
  induction l; intros.
  * simpl length in *. repeat unfold_list_once. exists []. split. 2: split.
    all: auto;
    inversion H1.
  * pose (element_exist _ _ H1). pose (element_exist _ _ H2).
    pose (element_exist _ _ H3). pose (element_exist _ _ H4).
    destruct e as [e']. destruct e0 as [v']. destruct e1 as [eff1].
    destruct e2 as [id1]. destruct H5, H6, H7, H8. subst.
    pose (E := H0 0 (Nat.lt_0_succ (length l))). simpl in E.
    apply effect_extension_expr in E as E'. destruct E'. subst.
    inversion H1. inversion H2. inversion H3. inversion H4.
    pose (W := H 0 (Nat.lt_0_succ _)). simpl in W. apply W in E. clear W. destruct E, H6.
    apply effect_extension_expr in H6 as HH'. destruct HH'. subst.
    epose (IHl x x0 (transform_with x1 x3) x2 env id1 (eff ++ x5) _ _ H7 H8 _ H10). destruct e, H12.
    eexists (x5 :: x4). split. 2: split.
    - simpl. (* unfold transform_with. rewrite map_length. *) lia.
    - intros. destruct i.
      + simpl. rewrite app_nil_r. rewrite app_nil_r in H6. exact H6.
      + simpl in H14. apply Lt.lt_S_n in H14. epose (P := H13 i H14).
        simpl in P. unfold transform_with. simpl.
        destruct i.
        ** simpl in P. admit.
        
        (* epose (P1 := @nth_error_nth' _ x4 0 [] _).
           apply map_nth_error with (f := fun x => x5 ++ x) in P1.
           pose (P2 := @nth_error_nth _ _ _ _ [] P1).
           rewrite P2. simpl in P. rewrite app_nil_r in P.
           rewrite <- app_assoc in P. apply P. *)
        ** epose (P1 := @nth_error_nth' _ x4 (S i) [] _).
           apply map_nth_error with (f := fun x => x5 ++ x) in P1.
           pose (P2 := @nth_error_nth _ _ _ _ [] P1).
           rewrite P2. simpl in P.
           epose (P1' := @nth_error_nth' _ x4 i [] _).
           apply map_nth_error with (f := fun x => x5 ++ x) in P1'.
           pose (P2' := @nth_error_nth _ _ _ _ [] P1').
           rewrite P2'.
           rewrite <- app_assoc, <- app_assoc in P. apply P.
    - destruct i.
      + simpl. rewrite app_nil_r in H11. apply Permutation_app_inv_l in H11.
        auto.
      + simpl in H14. apply Lt.lt_S_n in H14. pose (P := H13 i H14).
        destruct P. simpl.
        epose (P1' := @nth_error_nth' _ x4 i [] _).
        apply map_nth_error with (f := fun x => x5 ++ x) in P1'.
        pose (P2' := @nth_error_nth _ _ _ _ [] P1').
        unfold transform_with. rewrite P2'. rewrite app_assoc. auto.
Unshelve.
 ** intros. epose (H (S i) _). exact w. Unshelve. simpl. lia.
 ** intros. epose (H0 (S i) (Lt.lt_n_S _ _ H11)). simpl in e.
    destruct i.
    -- simpl.
 ** simpl. simpl in e.
Admitted. *)

Theorem ECons_weak_congr hd tl : forall hd' tl',
  weakly_equivalent hd hd' -> weakly_equivalent tl tl'
->
  weakly_equivalent_single (ECons hd tl) (ECons hd' tl').
Proof.
  assert (A : forall hd hd' tl tl' env id eff id' res eff',
    weakly_equivalent hd hd' -> weakly_equivalent tl tl' ->
    | env, id, ECons hd tl, eff | -s> |id', res, eff'|
  ->
    (exists eff'', | env, id, ECons hd' tl', eff | -s> |id', res, eff''| /\ Permutation eff' eff'')
  ). {
    intros. unfold weakly_equivalent in H, H0. destruct H, H0. inversion H1; subst.
    * apply effect_extension_expr in H8 as H8'. destruct H8'. subst.
      apply effect_extension_expr in H13 as H13'. destruct H13'. subst.
      pose (P := H0 _ _ _ _ _ _ H8). destruct P, H4.
      apply effect_extension_expr in H4 as H4'. destruct H4'. subst.
      apply effectlist_irrelevant_expr with (eff0 := eff ++ x2) in H13.
      pose (P := H _ _ _ _ _ _ H13). destruct P, H6.
      apply effect_extension_expr in H6 as H6'. destruct H6'. subst.
      exists ((eff ++ x2) ++ x3). split. eapply eval_cons.
      - exact H4.
      - exact H6.
      - rewrite <- app_assoc, <- app_assoc.
        apply Permutation_app_head. apply Permutation_app_inv_l in H5.
        apply Permutation_app. exact H5.
        apply Permutation_app_inv_l in H7. exact H7.
    * apply effect_extension_expr in H12 as H12'. destruct H12'. subst.
      pose (P := H0 _ _ _ _ _ _ H12). destruct P, H4.
      apply effect_extension_expr in H4 as H4'. destruct H4'. subst.
      exists (eff ++ x1). split.
      - eapply eval_cons_tl_ex. exact H4.
      - apply Permutation_app_head. apply Permutation_app_inv_l in H5. exact H5.
    * apply effect_extension_expr in H8 as H8'. destruct H8'. subst.
      apply effect_extension_expr in H13 as H13'. destruct H13'. subst.
      pose (P := H0 _ _ _ _ _ _ H8). destruct P, H4.
      apply effect_extension_expr in H4 as H4'. destruct H4'. subst.
      apply effectlist_irrelevant_expr with (eff0 := eff ++ x2) in H13.
      pose (P := H _ _ _ _ _ _ H13). destruct P, H6.
      apply effect_extension_expr in H6 as H6'. destruct H6'. subst.
      exists ((eff ++ x2) ++ x3). split. eapply eval_cons_hd_ex.
      - exact H4.
      - exact H6.
      - rewrite <- app_assoc, <- app_assoc.
        apply Permutation_app_head. apply Permutation_app_inv_l in H5.
        apply Permutation_app. exact H5.
        apply Permutation_app_inv_l in H7. exact H7.
  }
  split; intros.
  * eapply A. exact H. exact H0. exact H1.
  * eapply A. exact (weak_sym H). exact (weak_sym H0). exact H1.
Qed.


Theorem ETuple_weak_congr (l : list Expression) : forall (l' : list Expression),
  length l = length l' ->
  (forall i, i < length l -> weakly_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
->
  weakly_equivalent_single (ETuple l) (ETuple l').
Proof.
  assert (A : forall (l l' : list Expression) env id eff id' res eff',
    length l = length l' ->
    (forall i, i < length l -> weakly_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
    ->
    (exists clock, fbs_single clock env id (ETuple l) eff = Result id' res eff')
    ->
    exists clock eff'', fbs_single clock env id (ETuple l') eff = Result id' res eff'' /\ Permutation eff' eff''). {
  intros. destruct H1, x.
  inversion H1.
  simpl in H1. destruct (fbs_values (fbs_expr x) env id l0 eff) eqn: D1.
  destruct res0. 3-4: congruence.
  * inversion H1.
    apply exprlist_cong_fbs with (l' := l') in D1. destruct D1, H2, H2.
    subst.
    exists (S x0), x1. split; auto.
    2-3: auto.
    simpl. rewrite H2. reflexivity.
  * inversion H1.
    apply exprlist_cong_fbs with (l' := l') in D1. destruct D1, H2, H2.
    subst.
    exists (S x0), x1. split; auto.
    2-3: auto.
    simpl. rewrite H2. reflexivity.
  }
  split; intros.
  * apply fbs_soundness in H1. eapply A in H; auto. 2: exact H1. 
    destruct H, H, H.
    exists x0. apply fbs_single_correctness in H. split. exact H. auto.
  * apply fbs_soundness in H1. eapply A with (l' := l) in H1; auto.
    2: { intros. apply weak_sym. apply H0. lia. }
    destruct H1, H1, H1.
    exists x0. apply fbs_single_correctness in H1. split. exact H1. auto.
Qed.

Theorem ECall_weak_congr (f : string) (l : list Expression) : forall (l' : list Expression),
  length l = length l' ->
  (forall i, i < length l -> weakly_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
->
  weakly_equivalent_single (ECall f l) (ECall f l').
Proof.
  assert (A : forall f (l l' : list Expression) env id eff id' res eff',
  length l = length l' ->
  (forall i, i < length l -> weakly_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
  ->
  |env, id, ECall f l, eff| -s> |id', res, eff'|
  ->
  |env, id, ECall f l', eff| -s> |id', res, eff'|). {
  intros. unfold weakly_equivalent, weakly_equivalent_single in *.
  * inversion H1; subst; rewrite H in *.
    - eapply eval_call.
      + exact H4.
      + exact H5.
      + exact H6.
      + intros. pose (H7 i H2). apply H0 in e. 2: auto. auto.
      + auto.
      + auto.
    - eapply eval_call_ex.
      + exact H4.
      + reflexivity.
      + exact H6.
      + exact H7.
      + intros. pose (H10 j H2). apply H0 in e. 2: lia. auto.
      + apply H0 in H15. auto. lia.
  }
  split; intros.
  * eapply A. exact H. auto. auto.
  * eapply A. symmetry. exact H. intros. rewrite <- H in *.
    apply weak_sym. auto. auto.
Qed.

Theorem EPrimOp_weak_congr (f : string) (l : list Expression) : forall (l' : list Expression),
  length l = length l' ->
  (forall i, i < length l -> weakly_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
->
  weakly_equivalent_single (EPrimOp f l) (EPrimOp f l').
Proof.
  assert (A : forall f (l l' : list Expression) env id eff id' res eff',
  length l = length l' ->
  (forall i, i < length l -> weakly_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
  ->
  |env, id, EPrimOp f l, eff| -s> |id', res, eff'|
  ->
  |env, id, EPrimOp f l', eff| -s> |id', res, eff'|). {
  intros. unfold weakly_equivalent, weakly_equivalent_single in *.
  * inversion H1; subst; rewrite H in *.
    - eapply eval_primop.
      + exact H4.
      + exact H5.
      + exact H6.
      + intros. pose (H7 i H2). apply H0 in e. 2: auto. auto.
      + auto.
      + auto.
    - eapply eval_primop_ex.
      + exact H4.
      + reflexivity.
      + exact H6.
      + exact H7.
      + intros. pose (H10 j H2). apply H0 in e. 2: lia. auto.
      + apply H0 in H15. auto. lia.
  }
  split; intros.
  * eapply A. exact H. auto. auto.
  * eapply A. symmetry. exact H. intros. rewrite <- H in *.
    apply weak_sym. auto. auto.
Qed.

Theorem EApp_weak_congr (exp : Expression) (l : list Expression) : forall (exp' : Expression) (l' : list Expression),
  length l = length l' ->
  weakly_equivalent exp exp' ->
  (forall i, i < length l -> weakly_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
->
  weakly_equivalent_single (EApp exp l) (EApp exp' l').
Proof.
  assert (A : forall exp exp' (l l' : list Expression) env id eff id' res eff',
    length l = length l' ->
    weakly_equivalent exp exp' ->
    (forall i, i < length l -> weakly_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
    ->
    |env, id, EApp exp l, eff| -s> |id', res, eff'|
    ->
    |env, id, EApp exp' l', eff| -s> |id', res, eff'|).
  {
    unfold weakly_equivalent.
    intros. remember (EApp exp0 l0) as appl.
    induction H2; inversion Heqappl; subst.
    * eapply eval_app; rewrite H in *.
      - exact H2.
      - apply H0. exact H3.
      - auto.
      - exact H5.
      - exact H6.
      - intros. pose (H7 i H9). apply H1. auto. auto.
      - auto.
    * eapply eval_app_closure_ex. apply H0. exact H2.
    * eapply eval_app_param_ex; rewrite H in *.
      - exact H2.
      - reflexivity.
      - exact H4.
      - exact H5.
      - apply H0. auto. exact H6.
      - intros. pose (H7 j H3). apply H1. lia. auto.
      - apply H1. lia. auto.
    * eapply eval_app_badfun_ex; rewrite H in *.
      - exact H2.
      - exact H3.
      - exact H4.
      - apply H0. auto. exact H5.
      - intros. pose (H6 j H8). apply H1. lia. auto.
      - congruence.
      - auto.
      - auto.
    * eapply eval_app_badarity_ex; rewrite H in *.
      - exact H2.
      - exact H3.
      - exact H4.
      - apply H0. auto. exact H5.
      - intros. pose (H6 j H8). apply H1. lia. auto.
      - congruence.
      - auto.
      - auto.
  }
  intros. split.
  * apply A; auto.
  * apply A; try lia.
    apply weak_sym. auto.
    intros. apply weak_sym. apply H1. lia.
Qed.

Theorem case_weak_congr_helper (l l' : list (list Pattern * Expression * Expression)) vals j gg ee bb:
length l = length l' ->
((forall i, i < length l -> weakly_equivalent (nth i (map snd l) ErrorExp)
                                                   (nth i (map snd l') ErrorExp) /\
                             weakly_equivalent (nth i (map snd (map fst l)) ErrorExp)
                                                   (nth i (map snd (map fst l')) ErrorExp)
                   /\ nth i (map fst (map fst l)) [] = nth i (map fst (map fst l')) [])) ->
 match_clause vals l j = Some (gg, ee, bb)
->
 match_clause vals l' j = Some (nth j (map snd (map fst l')) ErrorExp, nth j (map snd l') ErrorExp, bb).
Proof.
  generalize dependent l'. generalize dependent j.
  induction l; intros.
  * inversion H1.
  * pose (element_exist _ _ H). destruct e. destruct H2. subst.
    inversion H.
    destruct j.
    - simpl. simpl in H1. destruct a, p, x, p.
      pose (H0 0 (Nat.lt_0_succ _)). destruct a. destruct H4.
      simpl in H2, H4, H5. subst.
      destruct (match_valuelist_to_patternlist vals l1).
      + simpl. inversion H1. auto.
      + congruence.
    - simpl. simpl in H1. destruct a, p, x, p.
      apply IHl. auto.
      intros. epose (H0 (S i) _). simpl in a. exact a. Unshelve. 2: simpl; lia.
      auto.
Qed.

Theorem ECase_weak_congr (exp : Expression) (l : list (list Pattern * Expression * Expression)) : forall (exp' : Expression) (l' : list (list Pattern * Expression * Expression)),
  length l = length l' ->
  weakly_equivalent exp exp' ->
  (forall i, i < length l -> weakly_equivalent (nth i (map snd l) ErrorExp)
                                                   (nth i (map snd l') ErrorExp) /\
                             weakly_equivalent (nth i (map snd (map fst l)) ErrorExp)
                                                   (nth i (map snd (map fst l')) ErrorExp)
                   /\ nth i (map fst (map fst l)) [] = nth i (map fst (map fst l')) [])
->
  weakly_equivalent_single (ECase exp l) (ECase exp' l').
Proof.
  intros. unfold weakly_equivalent, weakly_equivalent_single in *.
  split; intros; inversion H2; subst.
  * eapply eval_case; rewrite H in *.
    - apply H0. exact H5.
    - exact H6.
    - apply case_congr_helper with (l' := l') in H7.
      3: unfold weakly_equivalent; rewrite H; exact H1.
      exact H7.
      auto.
    - intros. assert (match_clause vals l' j = Some (gg, ee, bb)). { auto. }
      apply match_clause_ith in H9. destruct H9. destruct H10. subst.
      apply case_congr_helper with (l' := l) in H4. 2: auto.
      pose (H8 j H3 _ _ _ H4). epose (H1 j _). Unshelve. 3: lia. destruct a.
      apply H10. exact e.
      intros. split. 2: split.
      + apply weak_sym. epose (H1 i0 _). Unshelve. 2: lia. destruct a.
        unfold weakly_equivalent.
        intros. apply H10.
      + apply weak_sym. epose (H1 i0 _). Unshelve. 2: lia. destruct a.
        unfold weakly_equivalent.
        intros. apply H12.
      + epose (H1 i0 _). Unshelve. 2: lia. destruct a.
        destruct H12. auto.
    - apply match_clause_ith in H7. destruct H7, H4. subst.
      apply H1. auto. auto.
    - apply match_clause_ith in H7. destruct H7, H4. subst.
      apply H1. auto. auto.
  * eapply eval_case_pat_ex. apply H0. auto.
  * eapply eval_case_clause_ex.
    - apply H0. exact H7.
    - intros. assert (match_clause vals l' j = Some (gg, ee, bb)). { auto. }
      apply match_clause_ith in H5. destruct H5. destruct H6. subst.
      apply case_congr_helper with (l' := l) in H4.
      rewrite H in *. 2: auto.
      pose (H12 j H3 _ _ _ H4). epose (H1 j _). Unshelve. 3: lia. destruct a.
      apply H6. exact e.
      intros. split. 2: split.
      + apply weak_sym. epose (H1 i _). Unshelve. 2: lia. destruct a.
        unfold weakly_equivalent.
        intros. apply H6.
      + apply weak_sym. epose (H1 i _). Unshelve. 2: lia. destruct a.
        unfold weakly_equivalent.
        intros. apply H8.
      + epose (H1 i _). Unshelve. 2: lia. destruct a.
        destruct H8. auto.
  * eapply eval_case; rewrite <- H in *.
    - apply H0. exact H5.
    - exact H6.
    - apply case_congr_helper with (l' := l) in H7. 2: lia.
      exact H7.
      rewrite <- H. intros.
      split. 2: split.
      + apply weak_sym. pose (H1 i0 H3). unfold weakly_equivalent.
        apply a.
      + apply weak_sym. pose (H1 i0 H3). unfold weakly_equivalent.
        apply a.
      + pose (H1 i0 H3). unfold weakly_equivalent. destruct a. destruct H9.
        symmetry. apply H10.
    - intros. assert (match_clause vals l j = Some (gg, ee, bb)). { auto. }
      apply match_clause_ith in H9. destruct H9. destruct H10. subst.
      apply case_congr_helper with (l' := l') in H4. 2: auto.
      pose (H8 j H3 _ _ _ H4). epose (H1 j _). Unshelve. 3: lia. destruct a.
      apply H10. exact e.
      intros. split. 2: split.
      + apply weak_sym. epose (H1 i0 _). Unshelve. 2: lia. destruct a.
        unfold weakly_equivalent. symmetry.
        intros. apply H10.
      + apply weak_sym. epose (H1 i0 _). Unshelve. 2: lia. destruct a.
        unfold weakly_equivalent.
        intros. symmetry. apply H12.
      + epose (H1 i0 _). Unshelve. 2: lia. destruct a.
        destruct H12. auto.
    - apply match_clause_ith in H7. destruct H7, H4. subst.
      apply H1. auto. auto.
    - apply match_clause_ith in H7. destruct H7, H4. subst.
      apply H1. auto. auto.
  * eapply eval_case_pat_ex. apply H0. auto.
  * eapply eval_case_clause_ex.
    - apply H0. exact H7.
    - intros. assert (match_clause vals l j = Some (gg, ee, bb)). { auto. }
      apply match_clause_ith in H5. destruct H5. destruct H6. subst.
      apply case_congr_helper with (l' := l') in H4. 2: auto.
      rewrite H in *.
      pose (H12 j H3 _ _ _ H4). epose (H1 j _). Unshelve. 3: lia. destruct a.
      apply H6. exact e.
      intros. split. 2: split.
      + apply weak_sym. epose (H1 i _). Unshelve. 2: lia. destruct a.
        unfold weakly_equivalent.
        intros. symmetry. apply H6.
      + apply weak_sym. epose (H1 i _). Unshelve. 2: lia. destruct a.
        unfold weakly_equivalent.
        intros. symmetry. apply H8.
      + epose (H1 i _). Unshelve. 2: lia. destruct a.
        destruct H8. auto.
Qed.

Theorem ELet_weak_congr (e1 e2 : Expression) vl : forall (e1' e2' : Expression),
  weakly_equivalent e1 e1' ->
  weakly_equivalent e2 e2'
->
  weakly_equivalent_single (ELet vl e1 e2) (ELet vl e1' e2').
Proof.
  assert (A : forall env id e1 e1' e2 e2' vl eff id' res eff',
    weakly_equivalent e1 e1' -> weakly_equivalent e2 e2' ->
    | env, id, ELet vl e1 e2, eff | -s> | id', res, eff' |
  ->
    exists eff'', | env, id, ELet vl e1' e2', eff | -s> |id', res, eff'' | /\ Permutation eff' eff''
  ).
  {
    intros. unfold weakly_equivalent in *. destruct H, H0.
    inversion H1; subst.
    * apply effect_extension_expr in H9 as H9'. destruct H9'. subst.
      apply effect_extension_expr in H15 as H15'. destruct H15'. subst.
      apply H in H9. destruct H9, H4.
      apply effect_extension_expr in H4 as H4'. destruct H4'. subst.
      apply effectlist_irrelevant_expr with (eff0 := eff ++ x2) in H15.
      apply H0 in H15. destruct H15, H6.
      apply effect_extension_expr in H6 as H6'. destruct H6'. subst.
      exists ((eff ++ x2) ++ x3). split. eapply eval_let.
      - exact H4.
      - assumption.
      - exact H6.
      - apply Permutation_app.
        + apply Permutation_app_head. apply Permutation_app_inv_l in H5. assumption.
        + apply Permutation_app_inv_l in H7. assumption.
    * apply effect_extension_expr in H13 as H13'. destruct H13'. subst.
      apply H in H13. destruct H13, H4.
      apply effect_extension_expr in H4 as H4'. destruct H4'. subst.
      exists (eff ++ x1). split; [ eapply eval_let_ex; auto | auto ].
  }
  split; intros.
  * eapply A. exact H. exact H0. exact H1.
  * eapply A. exact (weak_sym H). exact (weak_sym H0). exact H1.
Qed.

Theorem ESeq_weak_congr e1 e2 e1' e2' :
  weakly_equivalent e1 e1' -> weakly_equivalent e2 e2'
->
  weakly_equivalent_single (ESeq e1 e2) (ESeq e1' e2').
Proof.
  unfold weakly_equivalent, weakly_equivalent_single.
  split; intros.
  * inversion H1. subst.
    - destruct H, H0. apply H in H6. destruct H6, H4.
      apply H0 in H11. destruct H11. destruct H6.
      pose (effect_extension_expr H6). destruct e. subst.
      apply effectlist_irrelevant_expr with (eff0 := x) in H6.
      exists (x ++ x1). split.
      + eapply eval_seq. exact H4. exact H6.
      + eapply perm_trans.
        ** exact H7.
        ** apply Permutation_app_tail. auto.
    - subst. apply H in H10. destruct H10.
      eexists. split. eapply eval_seq_ex. apply H2. apply H2.
  * inversion H1. subst.
    - destruct H, H0. apply H2 in H6. destruct H6, H4.
      apply H3 in H11. destruct H11. destruct H6.
      pose (effect_extension_expr H6). destruct e. subst.
      apply effectlist_irrelevant_expr with (eff0 := x) in H6.
      exists (x ++ x1). split.
      + eapply eval_seq. exact H4. exact H6.
      + eapply perm_trans.
        ** exact H7.
        ** apply Permutation_app_tail. auto.
    - subst. apply H in H10. destruct H10.
      eexists. split. eapply eval_seq_ex. apply H2. apply H2.
Qed.

Theorem ELetRec_weak_congr (exp : Expression) l : forall (exp' : Expression),
  weakly_equivalent exp exp'
->
  weakly_equivalent_single (ELetRec l exp) (ELetRec l exp').
Proof.
  intros. unfold weakly_equivalent, weakly_equivalent_single in *.
  split; intros.
  * inversion H0. subst. destruct H. apply H in H9. destruct H9, H2.
    exists x. split; auto. eapply eval_letrec; auto.
  * inversion H0. subst. destruct H. apply H1 in H9. destruct H9, H2.
    exists x. split; auto. eapply eval_letrec; auto.
Qed.

Theorem EMap_weak_congr (l : list (Expression * Expression)) : 
  forall (l' : list (Expression * Expression)),
  length l = length l' ->
  (let exps := make_map_exps l in
   let exps' := make_map_exps l' in
  forall i, i < length exps -> weakly_equivalent (nth i exps ErrorExp) (nth i exps' ErrorExp))
->
  weakly_equivalent_single (EMap l) (EMap l').
Proof.
  assert (A :
    forall (l l' : list (Expression * Expression)) env id eff eff' id' res,
    length l = length l' ->
    (let exps := make_map_exps l in
      let exps' := make_map_exps l' in
       forall i, i < length exps -> weakly_equivalent (nth i exps ErrorExp) (nth i exps' ErrorExp)) ->
    |env, id, EMap l, eff | -s> |id', res, eff'|
    ->
    |env, id, EMap l', eff | -s> |id', res, eff' |
  ). {
  intros. unfold weakly_equivalent, weakly_equivalent_single in *.
  * inversion H1; subst; rewrite H in *.
    - unfold exps, vals in *.
      eapply eval_map.
      + exact H3.
      + exact H4.
      + exact H5.
      + exact H6.
      + intros. rewrite length_make_map_exps in H2, H7. rewrite H in H7.
        pose (H7 i H2). apply H0 in e. exact e.
        rewrite length_make_map_exps. lia.
      + exact H8.
      + auto.
      + auto.
      + auto.
    - unfold exps, vals in *.
      eapply eval_map_ex.
      + exact H3.
      + exact H4.
      + exact H5.
      + reflexivity.
      + exact H7.
      + intros.
        pose (H8 j H2). apply H0 in e. exact e.
        rewrite length_make_map_exps. lia.
      + apply H0 in H11. auto. rewrite length_make_map_exps. lia.
  }
  split; intros.
  * eapply A. exact H. auto. auto.
  * eapply A. symmetry. exact H.
    simpl. simpl in H0. rewrite length_make_map_exps. rewrite length_make_map_exps in H0.
    intros. apply weak_sym. apply H0. lia. auto.
Qed.

Theorem ETry_weak_congr (e1 e2 e3 : Expression) vl1 vl2 : forall (e1' e2' e3' : Expression),
  weakly_equivalent e1 e1' ->
  weakly_equivalent e2 e2' ->
  weakly_equivalent e3 e3'
->
  weakly_equivalent_single (ETry e1 vl1 e2 vl2 e3) (ETry e1' vl1 e2' vl2 e3').
Proof.
  assert (A : forall e1 e1' e2 e2' e3 e3' env id eff id' res eff',
    weakly_equivalent e1 e1' ->
    weakly_equivalent e2 e2' ->
    weakly_equivalent e3 e3' ->
    |env, id, ETry e1 vl1 e2 vl2 e3, eff | -s> |id', res, eff'|
    ->
    (exists eff'', |env, id, ETry e1' vl1 e2' vl2 e3', eff| -s> |id', res, eff''| /\ Permutation eff' eff'')
  ).
  {
    intros. unfold weakly_equivalent in *. destruct H, H0, H1. inversion H2; subst.
    * apply effect_extension_expr in H17 as H17'. destruct H17'. subst.
      apply effect_extension_expr in H19 as H19'. destruct H19'. subst.
      apply H in H17. destruct H17, H6.
      apply effect_extension_expr in H6 as H6'. destruct H6'. subst.
      apply H0 in H19. destruct H19, H8.
      apply effect_extension_expr in H8 as H8'. destruct H8'. subst.
      apply effectlist_irrelevant_expr with (eff0 := eff ++ x2) in H8.
      exists (eff ++ x2 ++ x3). split. eapply eval_try.
      - exact H6.
      - auto.
      - rewrite app_assoc. exact H8.
      - rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app.
        + apply Permutation_app_inv_l in H7. auto.
        + apply Permutation_app_inv_l in H9. auto.
    * apply effect_extension_expr in H17 as H17'. destruct H17'. subst.
      apply effect_extension_expr in H18 as H18'. destruct H18'. subst.
      apply H in H17. destruct H17, H6.
      apply effect_extension_expr in H6 as H6'. destruct H6'. subst.
      apply H1 in H18. destruct H18, H8.
      apply effect_extension_expr in H8 as H8'. destruct H8'. subst.
      apply effectlist_irrelevant_expr with (eff0 := eff ++ x2) in H8.
      exists (eff ++ x2 ++ x3). split. eapply eval_catch.
      - exact H6.
      - rewrite app_assoc. exact H8.
      - rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app.
        + apply Permutation_app_inv_l in H7. auto.
        + apply Permutation_app_inv_l in H9. auto.
  }
  split; intros.
  * eapply A. exact H. exact H0. exact H1. auto.
  * eapply A.
    1-3: apply weak_sym.
    exact H. exact H0. exact H1. auto.
Qed.

Theorem EValues_weak_congr (l : list SingleExpression) : forall (l' : list SingleExpression),
  length l = length l' ->
  (forall i, i < length l -> weakly_equivalent_single (nth i l ErrorExp) (nth i l' ErrorExp))
->
  weakly_equivalent (EValues l) (EValues l').
Proof.
  assert (A : forall (l l' : list SingleExpression) env id eff id' res eff',
    length l = length l' ->
    (forall i, i < length l -> weakly_equivalent_single (nth i l ErrorExp) (nth i l' ErrorExp))
    ->
    |env, id, EValues l, eff| -e> |id', res, eff'|
    ->
    |env, id, EValues l', eff| -e> |id', res, eff'|). {
  intros. unfold weakly_equivalent, weakly_equivalent_single in *.
  * inversion H1; subst; rewrite H in *.
    - eapply eval_values.
      + exact H3.
      + exact H4.
      + exact H5.
      + intros. pose (H6 i H2). apply H0 in e. 2: auto. auto.
      + auto.
      + auto.
    - eapply eval_values_ex.
      + exact H3.
      + reflexivity.
      + exact H5.
      + exact H6.
      + intros. pose (H7 j H2). apply H0 in e. 2: lia. auto.
      + apply H0 in H10. auto. lia.
  }
  split; intros.
  * eapply A. exact H. auto. auto.
  * eapply A. symmetry. exact H. intros. rewrite <- H in *.
    apply weakly_equivalent_single_sym. auto. auto.
Qed.

Theorem ESingle_weak_congr (e : SingleExpression)  : forall (e': SingleExpression),
  weakly_equivalent_single e e'
->
  weakly_equivalent (ESingle e) (ESingle e').
Proof.
  unfold weakly_equivalent_single.
  split; intros.
  * inversion H0. subst. destruct H. apply H in H4. destruct H4, H2.
    exists x. split; auto. eapply eval_single; auto.
  * inversion H0. subst. destruct H. apply H1 in H4. destruct H4, H2.
    exists x. split; auto. eapply eval_single; auto.
Qed.

End congruence.

Section examples.

Definition write (s : string) : Expression :=
  ESingle (ECall "fwrite" [^ELit (Atom s)]).

Example weak1 e :
  weakly_equivalent (ESeq (ESeq (write "a") (write "b")) e)
                    (ESeq (ESeq (write "b") (write "a")) e).
Proof.
  unfold weakly_equivalent.
  split; intros.
  * inversion H; subst. inversion H3; subst.
    - inversion H5. subst. inversion H4. subst.
      inversion H7. inversion H6. inversion H13. inversion H31. subst.
      unfold_list.
      pose (H19 0 (Nat.lt_0_succ _)). inversion e0. inversion H8. subst.
      pose (H41 0 (Nat.lt_0_succ _)). inversion e1. inversion H9. subst.
      simpl in H21, H20, H25, H24, H22, H44. inversion H22. inversion H44. subst.
      remember H10 as HH. clear HeqHH. apply effect_extension in H10. destruct H10 as [eff3].
      subst.
      exists ((((x3 ++ [(Output, [VLit (Atom "b")])]) ++ [(Output, [VLit (Atom "a")])]) ++ eff3)).
      constructor. econstructor. econstructor.
      + econstructor. econstructor.
        ** econstructor. apply eval_call with (vals := [VLit (Atom "b")]) (eff := [x3]) (ids := [x]); auto.
           -- intros. inversion H0. 2: inversion H2. simpl. repeat constructor.
           -- simpl. reflexivity.
        ** econstructor. eapply eval_call with (vals := [VLit (Atom "a")]) (eff := [x3 ++ [(Output, [VLit (Atom "b")])]]) (ids := [x]); auto.
           -- intros. inversion H0. 2: inversion H2.
              simpl. constructor. constructor.
           -- reflexivity.
      + simpl. simpl in HH.
        eapply effectlist_irrelevant_expr in HH.
        exact HH.
      + apply Permutation_app_tail. rewrite <- app_assoc, <- app_assoc.
        apply Permutation_app_head. simpl. apply perm_swap.
    - inversion H9. inversion H4. subst.
      + inversion H19. inversion H5. subst.
        ** unfold_list. pose (H17 0 (Nat.lt_0_succ _)). inversion e0. subst.
           inversion H21.
        ** subst. inversion H15. unfold_list.
           -- inversion H26. inversion H6.
           -- inversion H1.
      + subst. inversion H18. inversion H5; subst.
        ** unfold_list. inversion H20.
        ** inversion H14.
           -- unfold_list. inversion H25. inversion H6.
           -- inversion H1.
  * inversion H; subst. inversion H3; subst.
    - inversion H5. subst. inversion H4. subst.
      inversion H7. inversion H6. inversion H13. inversion H31. subst.
      unfold_list.
      pose (H19 0 (Nat.lt_0_succ _)). inversion e0. inversion H8. subst.
      pose (H41 0 (Nat.lt_0_succ _)). inversion e1. inversion H9. subst.
      simpl in H21, H20, H25, H24, H22, H44. inversion H22. inversion H44. subst.
      remember H10 as HH. clear HeqHH. apply effect_extension in H10. destruct H10 as [eff3].
      subst.
      exists ((((x3 ++ [(Output, [VLit (Atom "a")])]) ++ [(Output, [VLit (Atom "b")])]) ++ eff3)).
      constructor. econstructor. econstructor.
      + econstructor. econstructor.
        ** econstructor. apply eval_call with (vals := [VLit (Atom "a")]) (eff := [x3]) (ids := [x]); auto.
           -- intros. inversion H0. 2: inversion H2. simpl. repeat constructor.
           -- simpl. reflexivity.
        ** econstructor. eapply eval_call with (vals := [VLit (Atom "b")]) (eff := [x3 ++ [(Output, [VLit (Atom "a")])]]) (ids := [x]); auto.
           -- intros. inversion H0. 2: inversion H2.
              simpl. constructor. constructor.
           -- reflexivity.
      + simpl. simpl in HH.
        eapply effectlist_irrelevant_expr in HH.
        exact HH.
      + apply Permutation_app_tail. rewrite <- app_assoc, <- app_assoc.
        apply Permutation_app_head. simpl. apply perm_swap.
    - inversion H9. inversion H4. subst.
      + inversion H19. inversion H5. subst.
        ** unfold_list. pose (H17 0 (Nat.lt_0_succ _)). inversion e0. subst.
           inversion H21.
        ** subst. inversion H15. unfold_list.
           -- inversion H26. inversion H6.
           -- inversion H1.
      + subst. inversion H18. inversion H5; subst.
        ** unfold_list. inversion H20.
        ** inversion H14.
           -- unfold_list. inversion H25. inversion H6.
           -- inversion H1.
Qed.

End examples.

Theorem fully_implies_weakly e1 e2 :
  fully_equivalent e1 e2
->
  weakly_equivalent e1 e2.
Proof.
  intros. unfold fully_equivalent, weakly_equivalent in *.
  split; intros; apply H in H0; exists eff'; split; auto.
Qed.

Theorem fully_implies_weakly_single e1 e2 :
  fully_equivalent_single e1 e2
->
  weakly_equivalent_single e1 e2.
Proof.
  intros. unfold fully_equivalent_single, weakly_equivalent_single in *.
  split; intros; apply H in H0; exists eff'; split; auto.
Qed.
