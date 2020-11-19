Require Core_Erlang_Full_Equivalence.

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
      destruct (((id =? id0) && list_eqb effect_struct_eqb eff (eff ++ x))%bool) eqn:D2.
      + apply andb_prop in D2. destruct D2.
        apply Nat.eqb_eq in H1. apply effect_list_struct_eqb_eq in H2.
        rewrite <- app_nil_r in H2 at 1. apply app_inv_head in H2. subst.
        rewrite app_nil_r. rewrite Nat.eqb_refl, list_effect_struct_eqb_refl. simpl.
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
      destruct (((id =? id0) && list_eqb effect_struct_eqb eff eff0)%bool) eqn:D2.
      2: congruence.
      destruct v0; try congruence. destruct l1; try congruence.
      destruct ((s =? "true")%string).
      + apply andb_prop in D2. destruct D2. apply Nat.eqb_eq in H0.
        apply effect_list_struct_eqb_eq in H1. subst.
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

Lemma effect_extension_singlelist_fbs exps :
forall c env id0 eff0 id' res eff',
  fbs_values (fbs_single c) env id0 exps eff0 = Result id' res eff'
->
  exists l, eff' = eff0 ++ l.
Proof.
  induction exps; intros.
  * exists []. simpl in H. inversion H. subst. rewrite app_nil_r. auto.
  * simpl in H. destruct (fbs_single c env id0 a eff0) eqn:D1. destruct res0.
    destruct v. congruence. destruct v0. 2: congruence. 3-4: congruence.
    - apply fbs_single_correctness in D1 as D1'.
      apply effect_extension_single in D1'. destruct D1'. subst.
      destruct (fbs_values (fbs_single c) env id exps (eff0 ++ x)) eqn:D2.
      destruct res0. 3-4: congruence.
      + inversion H. subst. apply IHexps in D2. destruct D2. subst.
        exists (x ++ x0). rewrite <- app_assoc. auto.
      + inversion H. subst. apply IHexps in D2. destruct D2. subst.
        exists (x ++ x0). rewrite <- app_assoc. auto.
    - inversion H. subst.
      apply fbs_single_correctness in D1 as D1'.
      apply effect_extension_single in D1'. destruct D1'. subst.
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

Lemma effectlist_irrelevant_singlelist_fbs exps :
forall c env id0 id' res eff0 ad,
  fbs_values (fbs_single c) env id0 exps eff0 = Result id' res (eff0 ++ ad)
->
  forall eff1, 
  fbs_values (fbs_single c) env id0 exps eff1 = Result id' res (eff1 ++ ad).
Proof.
  intros. apply single_list_effectlist_irrelevant with eff0. 2: auto.
  intros. eapply effectlist_irrelevant_fbs_single. exact H0.
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

Lemma singlelist_cong_fbs (l : list SingleExpression) :
forall (l' : list SingleExpression) clock env id eff id' res eff',
   length l = length l' ->
   (forall i, i < length l -> weakly_equivalent_single (nth i l ErrorExp) (nth i l' ErrorExp)) ->
  fbs_values (fbs_single clock) env id l eff = Result id' res eff'
->
  exists cl eff'', fbs_values (fbs_single cl) env id l' eff = Result id' res eff'' /\ Permutation eff' eff''.
Proof.
  induction l; intros.
  * inversion H1. subst. exists clock, eff'.
    apply eq_sym, length_zero_iff_nil in H. subst. simpl. split; auto.
  * pose (element_exist _ _ H). destruct e. destruct H2. subst.
    pose (EQ0 := H0 0 (Nat.lt_0_succ _)). simpl in EQ0.
    simpl in H1. destruct (fbs_single clock env id a eff) eqn:D1.
    destruct res0. destruct v. congruence. destruct v0. 2: congruence.
    3-4: congruence.
    - destruct (fbs_values (fbs_single clock) env id0 l eff0) eqn:D2.
      destruct res0. 3-4: congruence.
      + apply fbs_single_correctness in D1.
        apply effect_extension_single in D1 as HH. destruct HH. subst.
        apply EQ0 in D1. destruct D1, H2.
        apply effect_extension_single in H2 as HH.
        apply fbs_soundness in H2.
        destruct H2, HH. subst.

        apply effect_extension_singlelist_fbs in D2 as D2'. destruct D2'. subst.
        apply IHl with (l' := x0) in D2. destruct D2, H4, H4.
        2: simpl in H; lia.
        2: { intros. epose (H0 (S i) _). exact w. Unshelve. simpl. lia. }
        apply effect_extension_singlelist_fbs in H4 as HH. destruct HH. subst.
        inversion H1. subst.

        exists (x3 + x5), (eff ++ x4 ++ x7). simpl.
        apply bigger_clock_single with (clock' := x3 + x5) in H2. 2: lia.
        rewrite H2.
        apply bigger_clock_list with (clock' := x3 + x5) in H4. 2: lia.
        apply effectlist_irrelevant_singlelist_fbs with (eff1 := eff ++ x4) in H4.
        2: { intros. apply clock_increase_single. exact H6. }
        rewrite H4. split; rewrite <- app_assoc.
        ** auto.
        ** apply Permutation_app_head. apply Permutation_app_inv_l in H3.
           apply Permutation_app_inv_l in H5. apply Permutation_app; auto.
      + apply fbs_single_correctness in D1.
        apply effect_extension_single in D1 as HH. destruct HH. subst.
        apply EQ0 in D1. destruct D1, H2.
        apply effect_extension_single in H2 as HH.
        apply fbs_soundness in H2.
        destruct H2, HH. subst.

        apply effect_extension_singlelist_fbs in D2 as D2'. destruct D2'. subst.
        apply IHl with (l' := x0) in D2. destruct D2, H4, H4.
        2: simpl in H; lia.
        2: { intros. epose (H0 (S i) _). exact w. Unshelve. simpl. lia. }
        apply effect_extension_singlelist_fbs in H4 as HH. destruct HH. subst.
        inversion H1. subst.

        exists (x3 + x5), (eff ++ x4 ++ x7). simpl.
        apply bigger_clock_single with (clock' := x3 + x5) in H2. 2: lia.
        rewrite H2.
        apply bigger_clock_list with (clock' := x3 + x5) in H4. 2: lia.
        apply effectlist_irrelevant_singlelist_fbs with (eff1 := eff ++ x4) in H4.
        2: { intros. apply clock_increase_single. exact H6. }
        rewrite H4. split; rewrite <- app_assoc.
        ** auto.
        ** apply Permutation_app_head. apply Permutation_app_inv_l in H3.
           apply Permutation_app_inv_l in H5. apply Permutation_app; auto.
    - inversion H1. subst. apply fbs_single_correctness in D1.
      apply EQ0 in D1. destruct D1. destruct H2.
      apply fbs_soundness in H2. destruct H2. exists x2, x1.
      simpl. rewrite H2; auto.
Qed.

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
  assert (A : forall (l l' : list Expression) f env id eff id' res eff',
    length l = length l' ->
    (forall i, i < length l -> weakly_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
    ->
    (exists clock, fbs_single clock env id (ECall f l) eff = Result id' res eff')
    ->
    exists clock eff'', fbs_single clock env id (ECall f l') eff = Result id' res eff'' /\ Permutation eff' eff''). {
    intros. destruct H1, x.
    inversion H1.
    simpl in H1. destruct (fbs_values (fbs_expr x) env id l0 eff) eqn: D1.
    destruct res0. 3-4: congruence.
    * inversion H1.
      apply effect_extension_exprlist_fbs in D1 as D. destruct D. subst.
      apply exprlist_cong_fbs with (l' := l') in D1. destruct D1, H2, H2.
      subst.
      apply effect_extension_exprlist_fbs in H2 as D. destruct D. subst.
      exists (S x1), (snd (eval f0 v (eff ++ x3))). split; auto.
      - simpl. rewrite H2. erewrite eval_effect_irrelevant_fst at 1. reflexivity.
      - apply eval_effect_permutation. auto.
      - auto.
      - intros. apply H0. auto.
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

Theorem EPrimOp_weak_congr (f : string) (l : list Expression) : forall (l' : list Expression),
  length l = length l' ->
  (forall i, i < length l -> weakly_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
->
  weakly_equivalent_single (EPrimOp f l) (EPrimOp f l').
Proof.
  assert (A : forall (l l' : list Expression) f env id eff id' res eff',
    length l = length l' ->
    (forall i, i < length l -> weakly_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
    ->
    (exists clock, fbs_single clock env id (EPrimOp f l) eff = Result id' res eff')
    ->
    exists clock eff'', fbs_single clock env id (EPrimOp f l') eff = Result id' res eff'' /\ Permutation eff' eff''). {
    intros. destruct H1, x.
    inversion H1.
    simpl in H1. destruct (fbs_values (fbs_expr x) env id l0 eff) eqn: D1.
    destruct res0. 3-4: congruence.
    * inversion H1.
      apply effect_extension_exprlist_fbs in D1 as D. destruct D. subst.
      apply exprlist_cong_fbs with (l' := l') in D1. destruct D1, H2, H2.
      subst.
      apply effect_extension_exprlist_fbs in H2 as D. destruct D. subst.
      exists (S x1), (snd (eval f0 v (eff ++ x3))). split; auto.
      - simpl. rewrite H2. erewrite eval_effect_irrelevant_fst at 1. reflexivity.
      - apply eval_effect_permutation. auto.
      - auto.
      - intros. apply H0. auto.
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
    | env, id, EApp exp l, eff | -s>  | id', res, eff'| (* needed for better induction *)
    ->
    exists clock eff'', fbs_single clock env id (EApp exp' l') eff = Result id' res eff'' /\ Permutation eff' eff'').
  {
    unfold weakly_equivalent.
    intros. remember (EApp exp0 l0) as appl.
    induction H2; inversion Heqappl; subst.
    * apply effect_extension_expr in H3 as A1. destruct A1. subst.
      apply H0 in H3. destruct H3, H3.
      apply effect_extension_expr in H3 as A1. destruct A1. subst.
      assert (A2 :
      forall j : nat,
        j < Datatypes.length l0 ->
        exists clock : nat,
          fbs_expr clock env (nth_def ids id' 0 j) (nth j l0 ErrorExp)
            (nth_def eff (eff1 ++ x) [] j) =
          Result (nth_def ids id' 0 (S j)) (inl [nth j vals ErrorValue])
            (nth_def eff (eff1 ++ x) [] (S j))
      ). { intros. pose (H7 j H10). apply fbs_soundness. exact e. }
      epose (fbs_expr_list_soundness A2 _ _ _). Unshelve. all: try lia; auto.
      destruct e. 
      apply effect_extension_exprlist_fbs in H10 as P. destruct P. subst.
      apply exprlist_cong_fbs with (l' := l') in H10. destruct H10, H10, H10.
      apply effect_extension_exprlist_fbs in H10 as P. destruct P. subst.
      subst. apply fbs_soundness in H3. destruct H3.
      apply effect_extension_expr in H8 as A1. destruct A1.
      rewrite H11 in *. rewrite H13 in *.
      apply Permutation_app_inv_l in H12. apply Permutation_app_inv_l in H9.
      apply fbs_soundness in H8. destruct H8.
      exists (S (x4 + x3 + x7)), (((eff1 ++ x1) ++ x5) ++ x6). split.
      2 : { rewrite H11 at 1. apply Permutation_app. apply Permutation_app.
            apply Permutation_app_head. auto. auto. auto. }
      all: try lia; auto.
      simpl.
      eapply bigger_clock_expr in H3.
      eapply bigger_clock_list in H10. rewrite H3.
      eapply effectlist_irrelevant_exprlist_fbs in H10. rewrite H10.
      apply Nat.eqb_eq in H4. rewrite H4.
      eapply bigger_clock_expr in H8. rewrite H11 in H8 at 1.
      rewrite H11 in H8 at 1.
      eapply effectlist_irrelevant_fbs_expr in H8. exact H8.
      all: try lia.
      intros. apply clock_increase_expr. auto.
    * apply H0 in H2. destruct H2, H2. apply fbs_soundness in H2. destruct H2.
      exists (S x0), x. split; auto. simpl. rewrite H2. auto.
    * apply effect_extension_expr in H6 as A1. destruct A1. subst.
      apply H0 in H6. destruct H6, H3.
      apply effect_extension_expr in H3 as A1. destruct A1. subst.
      assert (A2 :
      forall j : nat,
        j < Datatypes.length vals ->
        exists clock : nat,
          fbs_expr clock env (nth_def ids id' 0 j) (nth j l0 ErrorExp)
            (nth_def eff (eff1 ++ x) [] j) =
          Result (nth_def ids id' 0 (S j)) (inl [nth j vals ErrorValue])
            (nth_def eff (eff1 ++ x) [] (S j))
      ). { intros. pose (H7 j H9). apply fbs_soundness. exact e. }
      apply fbs_soundness in H8.
      epose (fbs_expr_list_soundness_exception A2 H8 _ _ _ _). Unshelve. all: try lia.
      destruct e.
      apply effect_extension_exprlist_fbs in H9 as P. destruct P. subst.
      apply exprlist_cong_fbs with (l' := l') in H9. destruct H9, H9, H9.
      apply effect_extension_exprlist_fbs in H9 as P. destruct P. subst.
      subst.
      apply fbs_soundness in H3. destruct H3.
      exists (S (x4 + x3)), ((eff1 ++ x1) ++ x5). split; auto.
      2-5: auto.
      - simpl.
        eapply bigger_clock_expr in H3.
        eapply bigger_clock_list in H9. rewrite H3.
        eapply effectlist_irrelevant_exprlist_fbs in H9. rewrite H9. reflexivity.
        + lia.
        + intros. apply clock_increase_expr. auto.
        + lia.
      - apply Permutation_app. apply Permutation_app_head.
        apply Permutation_app_inv_l in H6. auto.
        apply Permutation_app_inv_l in H10. auto.
    * apply effect_extension_expr in H5 as A1. destruct A1. subst.
      apply H0 in H5. destruct H5, H5.
      apply effect_extension_expr in H5 as A1. destruct A1. subst.
      assert (A2 :
      forall j : nat,
        j < Datatypes.length l0 ->
        exists clock : nat,
          fbs_expr clock env (nth_def ids id' 0 j) (nth j l0 ErrorExp)
            (nth_def eff (eff1 ++ x) [] j) =
          Result (nth_def ids id' 0 (S j)) (inl [nth j vals ErrorValue])
            (nth_def eff (eff1 ++ x) [] (S j))
      ). { intros. pose (H6 j H9). apply fbs_soundness. exact e. }
      epose (fbs_expr_list_soundness A2 _ _ _). Unshelve. all: try lia; auto.
      destruct e. 
      apply effect_extension_exprlist_fbs in H9 as P. destruct P. subst.
      apply exprlist_cong_fbs with (l' := l') in H9. destruct H9, H9, H9.
      apply effect_extension_exprlist_fbs in H9 as P. destruct P. subst.
      subst. apply fbs_soundness in H5. destruct H5.
      rewrite H10 in H11. apply Permutation_app_inv_l in H11.
      exists (S (x4 + x3)), ((eff1 ++ x1) ++ x5). split.
      2 : { rewrite H10 at 1. apply Permutation_app. apply Permutation_app_head.
            apply Permutation_app_inv_l in H8. auto. auto. }
      all: try lia; auto.
      simpl.
      eapply bigger_clock_expr in H5.
      eapply bigger_clock_list in H9. rewrite H5.
      eapply effectlist_irrelevant_exprlist_fbs in H9. rewrite H9.
      destruct v.
      all: try lia; try reflexivity.
      congruence.
      intros. apply clock_increase_expr. auto.
    * apply effect_extension_expr in H5 as A1. destruct A1. subst.
      apply H0 in H5. destruct H5, H5.
      apply effect_extension_expr in H5 as A1. destruct A1. subst.
      assert (A2 :
      forall j : nat,
        j < Datatypes.length l0 ->
        exists clock : nat,
          fbs_expr clock env (nth_def ids id' 0 j) (nth j l0 ErrorExp)
            (nth_def eff (eff1 ++ x) [] j) =
          Result (nth_def ids id' 0 (S j)) (inl [nth j vals ErrorValue])
            (nth_def eff (eff1 ++ x) [] (S j))
      ). { intros. pose (H6 j H9). apply fbs_soundness. exact e. }
      epose (fbs_expr_list_soundness A2 _ _ _). Unshelve. all: try lia; auto.
      destruct e. 
      apply effect_extension_exprlist_fbs in H9 as P. destruct P. subst.
      apply exprlist_cong_fbs with (l' := l') in H9. destruct H9, H9, H9.
      apply effect_extension_exprlist_fbs in H9 as P. destruct P. subst.
      subst. apply fbs_soundness in H5. destruct H5.
      rewrite H10 in H11. apply Permutation_app_inv_l in H11.
      exists (S (x4 + x3)), ((eff1 ++ x1) ++ x5). split.
      2 : { rewrite H10 at 1. apply Permutation_app. apply Permutation_app_head.
            apply Permutation_app_inv_l in H8. auto. auto. }
      all: try lia; auto.
      simpl.
      eapply bigger_clock_expr in H5.
      eapply bigger_clock_list in H9. rewrite H5.
      eapply effectlist_irrelevant_exprlist_fbs in H9. rewrite H9.
      destruct (Datatypes.length var_list =? Datatypes.length vals) eqn:D2.
      all: try lia; try reflexivity.
      apply Nat.eqb_eq in D2. congruence.
      intros. apply clock_increase_expr. auto.
  }
  split; intros.
  * apply A with (l' := l') (exp' := exp') in H2; auto.
    destruct H2, H2, H2.
    exists x0. apply fbs_single_correctness in H2. split. exact H2. auto.
  * eapply A with (l' := l) (exp' := exp) in H2; auto.
    2: apply weak_sym; assumption.
    destruct H2, H2, H2.
    exists x0. apply fbs_single_correctness in H2. split. exact H2. auto.
    intros. apply weak_sym. apply H1. lia.
Qed.

Theorem case_weak_congr_helper (l l' : list (list Pattern * Expression * Expression)) :
forall env id0 eff0 v x id' res eff',
length l = length l' ->
((forall i, i < length l -> weakly_equivalent (nth i (map snd l) ErrorExp)
                                                   (nth i (map snd l') ErrorExp) /\
                             weakly_equivalent (nth i (map snd (map fst l)) ErrorExp)
                                                   (nth i (map snd (map fst l')) ErrorExp)
                   /\ nth i (map fst (map fst l)) [] = nth i (map fst (map fst l')) [])) ->
 fbs_case l env id0 eff0 v (fbs_expr x) = Result id' res eff'
->
 exists x eff'', fbs_case l' env id0 eff0 v (fbs_expr x) = Result id' res eff'' /\
 Permutation eff' eff''.
Proof.
  generalize dependent l'.
  induction l; intros.
  * apply eq_sym, length_zero_iff_nil in H. subst. simpl in H1. inversion H1. subst.
    exists 0, eff'. simpl. split; auto.
  * simpl in H1. destruct a, p.
    destruct (match_valuelist_to_patternlist v l0) eqn:D1.
    - destruct (fbs_expr x (add_bindings (match_valuelist_bind_patternlist v l0) env) id0 e0 eff0) eqn:D2.
      destruct res0. 2-4: congruence. destruct v0. congruence. destruct v1. 2: congruence.
      + destruct (((id =? id0) && list_eqb effect_struct_eqb eff0 eff)%bool) eqn:D3.
        2: congruence. destruct v0; try congruence. destruct l1; try congruence.
        apply andb_prop in D3. destruct D3. apply Nat.eqb_eq in H2.
        apply effect_list_struct_eqb_eq in H3. subst.
        destruct ((s =? "true")%string) eqn:D4.
        ** pose (H0 0 (Nat.lt_0_succ _)). destruct a. destruct H3.
           simpl in H2, H3, H4.
           apply fbs_expr_correctness in D2.
           apply effect_extension in D2 as D2'. destruct D2'. subst.
           apply H3 in D2. destruct D2, H4.
           apply effect_extension in H4 as D2'. destruct D2'. subst.
           rewrite H5 in H6 at 1. apply Permutation_app_inv_l in H6.
           rewrite <- app_nil_r in H5 at 1. apply app_inv_head in H5. subst.
           apply Permutation_nil in H6. subst. rewrite app_nil_r in *.
           apply fbs_expr_correctness in H1.
           apply effect_extension in H1 as D2'. destruct D2'. subst.
           apply H2 in H1. destruct H1, H1.
           apply effect_extension in H1 as D2'. destruct D2'. subst.
           apply fbs_soundness in H4. apply fbs_soundness in H1. destruct H4, H1.
           exists (x1 + x3), (eff ++ x2).
           pose (element_exist _ _ H). destruct e1, H6. subst.
           simpl. destruct x4, p. apply eqb_eq in D4. subst.
           simpl in D1. rewrite D1.
           eapply bigger_clock_expr in H4. rewrite H4.
           rewrite Nat.eqb_refl, list_effect_struct_eqb_refl. simpl.
           eapply bigger_clock_expr in H1.
           rewrite H1. auto. lia. lia.
        ** destruct ((s =? "false")%string) eqn:D5. 2: congruence.
           pose (H0 0 (Nat.lt_0_succ _)). destruct a. destruct H3.
           simpl in H2, H3, H4.
           apply fbs_expr_correctness in D2.
           apply effect_extension in D2 as D2'. destruct D2'. subst.
           apply H3 in D2. destruct D2, H4.
           apply effect_extension in H4 as D2'. destruct D2'. subst.
           rewrite H5 in H6 at 1. apply Permutation_app_inv_l in H6.
           rewrite <- app_nil_r in H5 at 1. apply app_inv_head in H5. subst.
           apply Permutation_nil in H6. subst. rewrite app_nil_r in *.
           pose (element_exist _ _ H). destruct e1, H5. subst.
           inversion H.
           epose (IH := IHl _ _ _ _ _ _ _ _ _ H6 _ H1). destruct IH, H5.
           apply eqb_eq in D5. subst. apply fbs_soundness in H4. destruct H4.
           exists (x4 + x2), x3. simpl.
           destruct x0, p. simpl in D1. rewrite D1.
           eapply bigger_clock_expr in H4. rewrite H4.
           rewrite Nat.eqb_refl, list_effect_struct_eqb_refl. simpl.
           destruct H5.
           eapply bigger_clock_case in H5. rewrite H5. auto. lia. lia.
           Unshelve.
           intros. epose (H0 (S i) _). apply a.
           Unshelve. simpl. lia.
    - pose (element_exist _ _ H). destruct e1, H2. subst. inversion H.
      epose (IH := IHl _ _ _ _ _ _ _ _ _ H3 _ H1). destruct IH, H2, H2.
      pose (H0 0 (Nat.lt_0_succ _)). destruct a. destruct H6.
      exists x2, x3. simpl. destruct x0, p. simpl in H7. rewrite H7 in D1. rewrite D1.
      rewrite H2. auto.
      Unshelve.
      intros. epose (H0 (S i) _). apply a.
      Unshelve. simpl. lia.
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
  assert (A : forall exp exp' (l l' : list (list Pattern * Expression * Expression)) env id eff id' res eff',
  length l = length l' ->
  weakly_equivalent exp exp' ->
  (forall i, i < length l -> weakly_equivalent (nth i (map snd l) ErrorExp)
                                                   (nth i (map snd l') ErrorExp) /\
                             weakly_equivalent (nth i (map snd (map fst l)) ErrorExp)
                                                   (nth i (map snd (map fst l')) ErrorExp)
                   /\ nth i (map fst (map fst l)) [] = nth i (map fst (map fst l')) [])
  ->
    (exists clock, fbs_single clock env id (ECase exp l) eff = Result id' res eff')
  ->
    (exists clock eff'',
                   fbs_single clock env id (ECase exp' l') eff = Result id' res eff'' /\
                   Permutation eff' eff'') 
  ).
  {
    intros. destruct H2. destruct x. inversion H2.
    simpl in H2.
    destruct (fbs_expr x env id exp0 eff) eqn:D1.
    destruct res0. 3-4: congruence.
    * apply fbs_expr_correctness, effect_extension_expr in D1 as D1'. destruct D1'. subst.
      apply H0 in D1. destruct D1, H3.
      apply effect_extension_expr in H3 as D1'. destruct D1'. subst.
      apply fbs_soundness in H3. destruct H3.
      apply effect_extension_case in H2 as A. destruct A. subst.
      apply case_weak_congr_helper with (l' := l') in H2; auto. destruct H2, H2, H2.
      apply effect_extension_case in H2 as A. destruct A. subst.
      exists (S (x1 + x4)), ((eff ++ x2) ++ x6). split; auto. simpl.
      eapply bigger_clock_expr in H3. rewrite H3.
      eapply effectlist_irrelevant_case in H2.
      eapply bigger_clock_case in H2. exact H2. all: try (simpl; lia).
      intros. eapply effectlist_irrelevant_fbs_expr in H6. exact H6.
      apply Permutation_app. apply Permutation_app. apply Permutation_refl.
      apply Permutation_app_inv_l in H4. auto.
      apply Permutation_app_inv_l in H5. auto.
    * inversion H2. subst. apply fbs_expr_correctness in D1. apply H0 in D1.
      destruct D1, H3. apply fbs_soundness in H3. destruct H3.
      exists (S x1), x0. simpl. rewrite H3. split; auto. 
  }
  split; intros.
  * apply fbs_soundness in H2.
    apply A with (l' := l') (exp' := exp') in H2; auto.
    destruct H2, H2, H2.
    exists x0. apply fbs_single_correctness in H2. split. exact H2. auto.
  * apply fbs_soundness in H2.
    eapply A with (l' := l) (exp' := exp) in H2; auto.
    2: apply weak_sym; assumption.
    destruct H2, H2, H2.
    exists x0. apply fbs_single_correctness in H2. split. exact H2. auto.
    intros. split. 2: split.
    - apply weak_sym. apply H1. lia.
    - apply weak_sym. apply H1. lia.
    - symmetry. apply H1. lia.
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
    (exists clock, fbs_single clock env id (EMap l) eff = Result id' res eff')
    ->
    (exists clock eff'', fbs_single clock env id (EMap l') eff = Result id' res eff'' /\
     Permutation eff' eff'')
  ). {
    intros. destruct H1, x.
    inversion H1.
    simpl in H1. destruct (fbs_values (fbs_expr x) env id (make_map_exps l0) eff) eqn: D1.
    destruct res0. 3-4: congruence.
    * destruct (make_map_vals_inverse v) eqn:HH. 2: congruence. destruct p. inversion H1.
      subst.
      apply exprlist_cong_fbs with (l' := make_map_exps l') in D1. destruct D1, H2, H2.
      subst.
      exists (S x0), x1. split; auto.
      3: auto.
      - simpl. rewrite H2, HH. reflexivity.
      - rewrite length_make_map_exps, length_make_map_exps. lia.
    * inversion H1.
      apply exprlist_cong_fbs with (l' := make_map_exps l') in D1. destruct D1, H2, H2.
      subst.
      exists (S x0), x1. split; auto.
      3: auto.
      - simpl. rewrite H2. reflexivity.
      - rewrite length_make_map_exps, length_make_map_exps. lia.
  }
  split; intros.
  * apply fbs_soundness in H1. eapply A in H; auto. 2: exact H1. 
    destruct H, H, H.
    exists x0. apply fbs_single_correctness in H. split. exact H. auto.
  * apply fbs_soundness in H1. eapply A with (l' := l) in H1; auto.
    2: { intros. apply weak_sym. apply H0. unfold exps in H2.
         rewrite length_make_map_exps. rewrite length_make_map_exps in H2. lia. }
    destruct H1, H1, H1.
    exists x0. apply fbs_single_correctness in H1. split. exact H1. auto.
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
    (exists clock, fbs_expr clock env id (EValues l) eff = Result id' res eff')
    ->
    exists clock eff'', fbs_expr clock env id (EValues l') eff = Result id' res eff'' /\
      Permutation eff' eff''). {
  intros. destruct H1, x.
    inversion H1.
    simpl in H1. destruct (fbs_values (fbs_single x) env id l0 eff) eqn: D1.
    destruct res0. 3-4: congruence.
    * inversion H1.
      apply singlelist_cong_fbs with (l' := l') in D1. destruct D1, H2, H2.
      subst.
      exists (S x0), x1. split; auto.
      all: auto.
    * inversion H1.
      apply singlelist_cong_fbs with (l' := l') in D1. destruct D1, H2, H2.
      subst.
      exists (S x0), x1. split; auto.
      all: auto.
  }
  split; intros.
  * apply fbs_soundness in H1. eapply A in H; auto. 2: exact H1. 
    destruct H, H, H.
    exists x0. apply fbs_expr_correctness in H. split. exact H. auto.
  * apply fbs_soundness in H1. eapply A with (l' := l) in H1; auto.
    2: { intros. apply weak_single_sym. apply H0. lia. }
    destruct H1, H1, H1.
    exists x0. apply fbs_expr_correctness in H1. split. exact H1. auto.
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
