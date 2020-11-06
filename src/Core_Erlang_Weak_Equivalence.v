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

Theorem weak_refl e :
  weakly_equivalent e e.
Proof.
  unfold weakly_equivalent. split; intros.
  eexists. split. apply H. apply Permutation_refl.
  eexists. split. apply H. apply Permutation_refl.
Qed.

Theorem weak_sym e1 e2 :
  weakly_equivalent e1 e2
->
  weakly_equivalent e2 e1.
Proof.
  unfold weakly_equivalent. split; intros.
  destruct H. apply H1 in H0. exact H0.
  destruct H. apply H in H0. exact H0.
Qed.

Theorem weak_trans e1 e2 e3 :
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

Theorem weak_single_refl e :
  weakly_equivalent_single e e.
Proof.
  unfold weakly_equivalent_single. split; intros.
  eexists. split. apply H. apply Permutation_refl.
  eexists. split. apply H. apply Permutation_refl.
Qed.

Theorem weak_single_sym e1 e2 :
  weakly_equivalent_single e1 e2
->
  weakly_equivalent_single e2 e1.
Proof.
  unfold weakly_equivalent_single. split; intros.
  destruct H. apply H1 in H0. exact H0.
  destruct H. apply H in H0. exact H0.
Qed.

Theorem weak_single_trans e1 e2 e3 :
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

Theorem ESeq_congr_weak e1 e2 e1' e2' :
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
