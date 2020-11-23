Require Core_Erlang_Semantics_Equivalence.

Export Core_Erlang_Semantics_Equivalence.

Import Core_Erlang_Tactics.Tactics.
Import ListNotations.


Definition fully_equivalent_expr e1 e2 :=
forall env eff res eff' id1 id2,
  (exists clock, fbs_expr clock env id1 e1 eff = Result id2 res eff')
<->
  (exists clock, fbs_expr clock env id1 e2 eff = Result id2 res eff').

Definition fully_equivalent_single e1 e2 :=
forall env eff res eff' id1 id2,
  (exists clock, fbs_single clock env id1 e1 eff = Result id2 res eff')
<->
  (exists clock, fbs_single clock env id1 e2 eff = Result id2 res eff').

Section equivalence_relation.

Theorem fully_equivalent_expr_refl {e} :
  fully_equivalent_expr e e.
Proof.
  intros. unfold fully_equivalent_expr. split; intros.
  * auto.
  * auto.
Qed.

Theorem fully_equivalent_expr_sym {e1 e2} :
  fully_equivalent_expr e1 e2 -> fully_equivalent_expr e2 e1.
Proof.
  unfold fully_equivalent_expr; intros.
  split; apply H.
Qed.

Theorem fully_equivalent_expr_trans {e1 e2 e3} :
  fully_equivalent_expr e1 e2 -> fully_equivalent_expr e2 e3
->
  fully_equivalent_expr e1 e3.
Proof.
  unfold fully_equivalent_expr; intros.
  split; intros.
  * apply H in H1. apply H0 in H1. auto.
  * apply H0 in H1. apply H in H1. auto.
Qed.

Theorem fully_equivalent_single_refl {e} :
  fully_equivalent_single e e.
Proof.
  intros. unfold fully_equivalent_single. split; intros.
  * auto.
  * auto.
Qed.

Theorem fully_equivalent_single_sym {e1 e2} :
  fully_equivalent_single e1 e2 -> fully_equivalent_single e2 e1.
Proof.
  unfold fully_equivalent_single; intros.
  split; apply H.
Qed.

Theorem fully_equivalent_single_trans {e1 e2 e3} :
  fully_equivalent_single e1 e2 -> fully_equivalent_single e2 e3
->
  fully_equivalent_single e1 e3.
Proof.
  unfold fully_equivalent_single; intros.
  split; intros.
  * apply H in H1. apply H0 in H1. auto.
  * apply H0 in H1. apply H in H1. auto.
Qed.

Definition fully_equivalent_exprlist l1 l2 :=
forall env eff res eff' id1 id2,
  (exists clock, fbs_values (fbs_expr clock) env id1 l1 eff = Result id2 res eff')
<->
  (exists clock, fbs_values (fbs_expr clock) env id1 l2 eff = Result id2 res eff').

Theorem fully_equivalent_exprlist_refl {l} :
  fully_equivalent_exprlist l l.
Proof.
  intros. unfold fully_equivalent_exprlist. split; intros.
  * auto.
  * auto.
Qed.

Theorem fully_equivalent_exprlist_sym {l1 l2} :
  fully_equivalent_exprlist l1 l2 -> fully_equivalent_exprlist l2 l1.
Proof.
  unfold fully_equivalent_exprlist; intros.
  split; apply H.
Qed.

Theorem fully_equivalent_exprlist_trans {l1 l2 l3} :
  fully_equivalent_exprlist l1 l2 -> fully_equivalent_exprlist l2 l3
->
  fully_equivalent_exprlist l1 l3.
Proof.
  unfold fully_equivalent_exprlist; intros.
  split; intros.
  * apply H in H1. apply H0 in H1. auto.
  * apply H0 in H1. apply H in H1. auto.
Qed.

Definition fully_equivalent_singlelist l1 l2 :=
forall env eff res eff' id1 id2,
  (exists clock, fbs_values (fbs_single clock) env id1 l1 eff = Result id2 res eff')
<->
  (exists clock, fbs_values (fbs_single clock) env id1 l2 eff = Result id2 res eff').

Theorem fully_equivalent_singlelist_refl {l} :
  fully_equivalent_singlelist l l.
Proof.
  intros. unfold fully_equivalent_singlelist. split; intros.
  * auto.
  * auto.
Qed.

Theorem fully_equivalent_singlelist_sym {l1 l2} :
  fully_equivalent_singlelist l1 l2 -> fully_equivalent_singlelist l2 l1.
Proof.
  unfold fully_equivalent_singlelist; intros.
  split; apply H.
Qed.

Theorem fully_equivalent_singlelist_trans {l1 l2 l3} :
  fully_equivalent_singlelist l1 l2 -> fully_equivalent_singlelist l2 l3
->
  fully_equivalent_singlelist l1 l3.
Proof.
  unfold fully_equivalent_singlelist; intros.
  split; intros.
  * apply H in H1. apply H0 in H1. auto.
  * apply H0 in H1. apply H in H1. auto.
Qed.

(** If all elements are equivalent in a list, then the lists are equivalent too
  * ATTENTION: does not work in the opposite direction 
  * *)
Theorem fully_equivalent_elements_exprlist (l l' : list Expression) :
  length l = length l' ->
  (forall i : nat, i < length l -> fully_equivalent_expr (nth i l ErrorExp) (nth i l' ErrorExp))
->
  fully_equivalent_exprlist l l'
.
Proof.
  generalize dependent l'. induction l; intros.
  * apply eq_sym, length_zero_iff_nil in H. subst. split; intros; exact H.
  * pose (EE := element_exist _ _ H). destruct EE, H1. subst. inversion H.
    pose (F := H0 0 (Nat.lt_0_succ _)). simpl in F.
    epose (IH := IHl _ H2 _).
    split; intros; destruct H1; simpl in H1.
    - destruct (fbs_expr x1 env id1 a eff) eqn:D1. destruct res0. destruct v. congruence.
      destruct v0. 2: congruence. 3-4: congruence.
      + edestruct F. pose (P := H3 (ex_intro _ x1 D1)). destruct P.
        destruct (fbs_values (fbs_expr x1) env id l eff0) eqn:D2.
        destruct res0. 3-4: congruence.
        ** edestruct IH. pose (P := H6 (ex_intro _ x1 D2)). destruct P.
           exists (x2 + x3). simpl. eapply bigger_clock_list in H8.
           erewrite (bigger_clock_expr _ _ H5), H8. assumption.
           lia. intros. apply clock_increase_expr. assumption.
        ** edestruct IH. pose (P := H6 (ex_intro _ x1 D2)). destruct P.
           exists (x2 + x3). simpl. eapply bigger_clock_list in H8.
           erewrite (bigger_clock_expr _ _ H5), H8. assumption.
           lia. intros. apply clock_increase_expr. assumption.
      + edestruct F. pose (P := H3 (ex_intro _ x1 D1)). destruct P.
        exists x2. simpl. rewrite H5. assumption.
    - destruct (fbs_expr x1 env id1 x eff) eqn:D1. destruct res0. destruct v. congruence.
      destruct v0. 2: congruence. 3-4: congruence.
      + edestruct F. pose (P := H4 (ex_intro _ x1 D1)). destruct P.
        destruct (fbs_values (fbs_expr x1) env id x0 eff0) eqn:D2.
        destruct res0. 3-4: congruence.
        ** edestruct IH. pose (P := H7 (ex_intro _ x1 D2)). destruct P.
           exists (x2 + x3). simpl. eapply bigger_clock_list in H8.
           erewrite (bigger_clock_expr _ _ H5), H8. assumption.
           lia. intros. apply clock_increase_expr. assumption.
        ** edestruct IH. pose (P := H7 (ex_intro _ x1 D2)). destruct P.
           exists (x2 + x3). simpl. eapply bigger_clock_list in H8.
           erewrite (bigger_clock_expr _ _ H5), H8. assumption.
           lia. intros. apply clock_increase_expr. assumption.
      + edestruct F. pose (P := H4 (ex_intro _ x1 D1)). destruct P.
        exists x2. simpl. rewrite H5. assumption.
Unshelve.
all: try lia.
intros. apply (H0 (S i)). simpl. lia.
Qed.

Theorem fully_equivalent_elements_singlelist (l l' : list SingleExpression) :
  length l = length l' ->
  (forall i : nat, i < length l -> fully_equivalent_single (nth i l ErrorExp) (nth i l' ErrorExp))
->
  fully_equivalent_singlelist l l'
.
Proof.
  generalize dependent l'. induction l; intros.
  * apply eq_sym, length_zero_iff_nil in H. subst. split; intros; exact H.
  * pose (EE := element_exist _ _ H). destruct EE, H1. subst. inversion H.
    pose (F := H0 0 (Nat.lt_0_succ _)). simpl in F.
    epose (IH := IHl _ H2 _).
    split; intros; destruct H1; simpl in H1.
    - destruct (fbs_single x1 env id1 a eff) eqn:D1. destruct res0. destruct v. congruence.
      destruct v0. 2: congruence. 3-4: congruence.
      + edestruct F. pose (P := H3 (ex_intro _ x1 D1)). destruct P.
        destruct (fbs_values (fbs_single x1) env id l eff0) eqn:D2.
        destruct res0. 3-4: congruence.
        ** edestruct IH. pose (P := H6 (ex_intro _ x1 D2)). destruct P.
           exists (x2 + x3). simpl. eapply bigger_clock_list in H8.
           erewrite (bigger_clock_single _ _ H5), H8. assumption.
           lia. intros. apply clock_increase_single. assumption.
        ** edestruct IH. pose (P := H6 (ex_intro _ x1 D2)). destruct P.
           exists (x2 + x3). simpl. eapply bigger_clock_list in H8.
           erewrite (bigger_clock_single _ _ H5), H8. assumption.
           lia. intros. apply clock_increase_single. assumption.
      + edestruct F. pose (P := H3 (ex_intro _ x1 D1)). destruct P.
        exists x2. simpl. rewrite H5. assumption.
    - destruct (fbs_single x1 env id1 x eff) eqn:D1. destruct res0. destruct v. congruence.
      destruct v0. 2: congruence. 3-4: congruence.
      + edestruct F. pose (P := H4 (ex_intro _ x1 D1)). destruct P.
        destruct (fbs_values (fbs_single x1) env id x0 eff0) eqn:D2.
        destruct res0. 3-4: congruence.
        ** edestruct IH. pose (P := H7 (ex_intro _ x1 D2)). destruct P.
           exists (x2 + x3). simpl. eapply bigger_clock_list in H8.
           erewrite (bigger_clock_single _ _ H5), H8. assumption.
           lia. intros. apply clock_increase_single. assumption.
        ** edestruct IH. pose (P := H7 (ex_intro _ x1 D2)). destruct P.
           exists (x2 + x3). simpl. eapply bigger_clock_list in H8.
           erewrite (bigger_clock_single _ _ H5), H8. assumption.
           lia. intros. apply clock_increase_single. assumption.
      + edestruct F. pose (P := H4 (ex_intro _ x1 D1)). destruct P.
        exists x2. simpl. rewrite H5. assumption.
Unshelve.
all: try lia.
intros. apply (H0 (S i)). simpl. lia.
Qed.

End equivalence_relation.

Section congruence.

Theorem ECons_congr hd tl : forall hd' tl',
  fully_equivalent_expr hd hd' -> fully_equivalent_expr tl tl'
->
  fully_equivalent_single (ECons hd tl) (ECons hd' tl').
Proof.
  assert (A : forall env id hd tl hd' tl' eff id' res eff',
    fully_equivalent_expr hd hd' -> fully_equivalent_expr tl tl'
   ->
    (exists clock, fbs_single clock env id (ECons hd tl) eff = Result id' res eff')
   ->
    (exists clock, fbs_single clock env id (ECons hd' tl') eff = Result id' res eff')
  ).
  {
  intros.
  * destruct H1. destruct x. inversion H1. simpl in H1.
    destruct (fbs_expr x env id tl0 eff) eqn:D1.
    destruct res0. destruct v. congruence. destruct v0. 2: congruence. 3-4: congruence.
    - destruct (fbs_expr x env id0 hd0 eff0) eqn:D2.
      destruct res0. destruct v0. congruence. destruct v1. 2: congruence. 3-4: congruence.
      + inversion H1. subst. epose (D1' := H0 _ _ _ _ _ _). destruct D1'. epose (H2 (ex_intro (fun x => fbs_expr x env id tl0 eff = Result id0 (inl [v]) eff0) x D1)).
        epose (D2' := H _ _ _ _ _ _). destruct D2'. epose (H4 (ex_intro (fun x => fbs_expr x env id0 hd0 eff0 = Result id' (inl [v0]) eff') x D2)). destruct e, e0.
        exists (S (x0 + x1)). simpl. erewrite (bigger_clock_expr _ _ H6), (bigger_clock_expr _ _ H7). reflexivity.
      + inversion H1. subst. epose (D1' := H0 _ _ _ _ _ _). destruct D1'. epose (H2 (ex_intro (fun x => fbs_expr x env id tl0 eff = Result id0 (inl [v]) eff0) x D1)).
        epose (D2' := H _ _ _ _ _ _). destruct D2'. epose (H4 (ex_intro (fun x => fbs_expr x env id0 hd0 eff0 = Result id' (inr e) eff') x D2)). destruct e0, e1.
        exists (S (x0 + x1)). simpl. erewrite (bigger_clock_expr _ _ H6), (bigger_clock_expr _ _ H7). reflexivity.
    - inversion H1. subst. epose (D1' := H0 _ _ _ _ _ _). destruct D1'. epose (H2 (ex_intro (fun x => fbs_expr x env id tl0 eff = Result id' (inr e) eff') x D1)).
      destruct e0. exists (S x0). simpl. rewrite H4. auto.
  }
  split; intros.
  * eapply A. exact H. exact H0. exact H1.
  * eapply A. exact (fully_equivalent_expr_sym H). exact (fully_equivalent_expr_sym H0).
    exact H1.
Unshelve.
all: lia.
Qed.

Theorem ETuple_congr (l : list Expression) : forall (l' : list Expression),
  fully_equivalent_exprlist l l'
->
  fully_equivalent_single (ETuple l) (ETuple l').
Proof.
  assert (A : forall (l l' : list Expression) env id eff id' res eff',
    fully_equivalent_exprlist l l'
    ->
    (exists clock, fbs_single clock env id (ETuple l) eff = Result id' res eff')
    ->
    (exists clock, fbs_single clock env id (ETuple l') eff = Result id' res eff')).
  {
    intros. unfold fully_equivalent_exprlist, fully_equivalent_single in *.
    destruct H0. destruct x. inversion H0. simpl in H0.
    destruct (fbs_values (fbs_expr x) env id l0 eff) eqn:D.
    destruct res0. 3-4: congruence.
    * inversion H0. subst. epose (E := H _ _ _ _ _ _). destruct E.
      pose (E := H1 (ex_intro (fun x => fbs_values (fbs_expr x) env id l0 eff = Result id' (inl v) eff') x D)). destruct E. exists (S x0). simpl. rewrite H3. auto.
    * inversion H0. subst. epose (E := H _ _ _ _ _ _). destruct E.
      pose (E := H1 (ex_intro (fun x => fbs_values (fbs_expr x) env id l0 eff = Result id' (inr e) eff') x D)). destruct E. exists (S x0). simpl. rewrite H3. auto.
  }
  split; intros.
  * eapply A. exact H. auto.
  * eapply A. exact (fully_equivalent_exprlist_sym H). exact H0.
Qed.

Theorem ECall_congr (f : string) (l : list Expression) : forall (l' : list Expression),
  length l = length l' ->
  (forall i, i < length l -> fully_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
->
  fully_equivalent_single (ECall f l) (ECall f l').
Proof.
  assert (A : forall f (l l' : list Expression) env id eff id' res eff',
  length l = length l' ->
  (forall i, i < length l -> fully_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
  ->
  |env, id, ECall f l, eff| -s> |id', res, eff'|
  ->
  |env, id, ECall f l', eff| -s> |id', res, eff'|). {
  intros. unfold fully_equivalent, fully_equivalent_single in *.
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
    apply fully_equivalent_sym. auto. auto.
Qed.

Theorem EPrimOp_congr (f : string) (l : list Expression) : forall (l' : list Expression),
  length l = length l' ->
  (forall i, i < length l -> fully_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
->
  fully_equivalent_single (EPrimOp f l) (EPrimOp f l').
Proof.
  assert (A : forall f (l l' : list Expression) env id eff id' res eff',
  length l = length l' ->
  (forall i, i < length l -> fully_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
  ->
  |env, id, EPrimOp f l, eff| -s> |id', res, eff'|
  ->
  |env, id, EPrimOp f l', eff| -s> |id', res, eff'|). {
  intros. unfold fully_equivalent, fully_equivalent_single in *.
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
    apply fully_equivalent_sym. auto. auto.
Qed.

Theorem EApp_congr (exp : Expression) (l : list Expression) : forall (exp' : Expression) (l' : list Expression),
  length l = length l' ->
  fully_equivalent exp exp' ->
  (forall i, i < length l -> fully_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
->
  fully_equivalent_single (EApp exp l) (EApp exp' l').
Proof.
  assert (A : forall exp exp' (l l' : list Expression) env id eff id' res eff',
    length l = length l' ->
    fully_equivalent exp exp' ->
    (forall i, i < length l -> fully_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
    ->
    |env, id, EApp exp l, eff| -s> |id', res, eff'|
    ->
    |env, id, EApp exp' l', eff| -s> |id', res, eff'|).
  {
    unfold fully_equivalent.
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
    apply fully_equivalent_sym. auto.
    intros. apply fully_equivalent_sym. apply H1. lia.
Qed.

Lemma match_clause_ith l : forall vals i gg ee bb,
  match_clause vals l i = Some (gg,ee,bb)
->
  gg = nth i (map snd (map fst l)) ErrorExp /\
  ee = nth i (map snd l) ErrorExp /\
  bb = match_valuelist_bind_patternlist vals (nth i (map fst (map fst l)) []).
Proof.
  induction l; intros.
  * inversion H.
  * destruct i.
    - destruct a. destruct p. simpl. simpl in H.
      destruct (match_valuelist_to_patternlist vals l0); inversion H. auto.
    - simpl in H. destruct a, p.
      simpl. pose (IHl _ _ _ _ _ H). exact a.
Qed.

Theorem case_congr_helper (l l' : list (list Pattern * Expression * Expression)) vals j gg ee bb:
length l = length l' ->
((forall i, i < length l -> fully_equivalent (nth i (map snd l) ErrorExp)
                                                   (nth i (map snd l') ErrorExp) /\
                             fully_equivalent (nth i (map snd (map fst l)) ErrorExp)
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

Theorem ECase_congr (exp : Expression) (l : list (list Pattern * Expression * Expression)) : forall (exp' : Expression) (l' : list (list Pattern * Expression * Expression)),
  length l = length l' ->
  fully_equivalent exp exp' ->
  (forall i, i < length l -> fully_equivalent (nth i (map snd l) ErrorExp)
                                                   (nth i (map snd l') ErrorExp) /\
                             fully_equivalent (nth i (map snd (map fst l)) ErrorExp)
                                                   (nth i (map snd (map fst l')) ErrorExp)
                   /\ nth i (map fst (map fst l)) [] = nth i (map fst (map fst l')) [])
->
  fully_equivalent_single (ECase exp l) (ECase exp' l').
Proof.
  intros. unfold fully_equivalent, fully_equivalent_single in *.
  split; intros; inversion H2; subst.
  * eapply eval_case; rewrite H in *.
    - apply H0. exact H5.
    - exact H6.
    - apply case_congr_helper with (l' := l') in H7.
      3: unfold fully_equivalent; rewrite H; exact H1.
      exact H7.
      auto.
    - intros. assert (match_clause vals l' j = Some (gg, ee, bb)). { auto. }
      apply match_clause_ith in H9. destruct H9. destruct H10. subst.
      apply case_congr_helper with (l' := l) in H4. 2: auto.
      pose (H8 j H3 _ _ _ H4). epose (H1 j _). Unshelve. 3: lia. destruct a.
      apply H10. exact e.
      intros. split. 2: split.
      + apply fully_equivalent_sym. epose (H1 i0 _). Unshelve. 2: lia. destruct a.
        unfold fully_equivalent.
        intros. apply H10.
      + apply fully_equivalent_sym. epose (H1 i0 _). Unshelve. 2: lia. destruct a.
        unfold fully_equivalent.
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
      + apply fully_equivalent_sym. epose (H1 i _). Unshelve. 2: lia. destruct a.
        unfold fully_equivalent.
        intros. apply H6.
      + apply fully_equivalent_sym. epose (H1 i _). Unshelve. 2: lia. destruct a.
        unfold fully_equivalent.
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
      + apply fully_equivalent_sym. pose (H1 i0 H3). unfold fully_equivalent.
        apply a.
      + apply fully_equivalent_sym. pose (H1 i0 H3). unfold fully_equivalent.
        apply a.
      + pose (H1 i0 H3). unfold fully_equivalent. destruct a. destruct H9.
        symmetry. apply H10.
    - intros. assert (match_clause vals l j = Some (gg, ee, bb)). { auto. }
      apply match_clause_ith in H9. destruct H9. destruct H10. subst.
      apply case_congr_helper with (l' := l') in H4. 2: auto.
      pose (H8 j H3 _ _ _ H4). epose (H1 j _). Unshelve. 3: lia. destruct a.
      apply H10. exact e.
      intros. split. 2: split.
      + apply fully_equivalent_sym. epose (H1 i0 _). Unshelve. 2: lia. destruct a.
        unfold fully_equivalent. symmetry.
        intros. apply H10.
      + apply fully_equivalent_sym. epose (H1 i0 _). Unshelve. 2: lia. destruct a.
        unfold fully_equivalent.
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
      + apply fully_equivalent_sym. epose (H1 i _). Unshelve. 2: lia. destruct a.
        unfold fully_equivalent.
        intros. symmetry. apply H6.
      + apply fully_equivalent_sym. epose (H1 i _). Unshelve. 2: lia. destruct a.
        unfold fully_equivalent.
        intros. symmetry. apply H8.
      + epose (H1 i _). Unshelve. 2: lia. destruct a.
        destruct H8. auto.
Qed.

Theorem ELet_congr (e1 e2 : Expression) vl : forall (e1' e2' : Expression),
  fully_equivalent e1 e1' ->
  fully_equivalent e2 e2'
->
  fully_equivalent_single (ELet vl e1 e2) (ELet vl e1' e2').
Proof.
  intros. unfold fully_equivalent, fully_equivalent_single in *.
  split; intros.
  * inversion H1; subst.
    - eapply eval_let. apply H. exact H7. auto. apply H0. exact H13.
    - eapply eval_let_ex. apply H. auto.
  * inversion H1; subst.
    - eapply eval_let. apply H. exact H7. auto. apply H0. exact H13.
    - eapply eval_let_ex. apply H. auto.
Qed.

Theorem ESeq_congr (e1 e2 : Expression) (l : list Expression) : forall (e1' e2' : Expression),
  fully_equivalent e1 e1' ->
  fully_equivalent e2 e2'
->
  fully_equivalent_single (ESeq e1 e2) (ESeq e1' e2').
Proof.
  intros. unfold fully_equivalent, fully_equivalent_single in *.
  split; intros.
  * inversion H1; subst.
    - eapply eval_seq. apply H. exact H6. auto. apply H0. exact H11.
    - eapply eval_seq_ex. apply H. auto.
  * inversion H1; subst.
    - eapply eval_seq. apply H. exact H6. auto. apply H0. exact H11.
    - eapply eval_seq_ex. apply H. auto.
Qed.

Theorem ELetRec_congr (exp : Expression) l : forall (exp' : Expression),
  fully_equivalent exp exp'
->
  fully_equivalent_single (ELetRec l exp) (ELetRec l exp').
Proof.
  intros. unfold fully_equivalent, fully_equivalent_single in *.
  split; intros.
  * inversion H0. subst. eapply eval_letrec. apply H. exact H9.
  * inversion H0. subst. eapply eval_letrec. apply H. exact H9.
Qed.

Theorem EMap_congr (l : list (Expression * Expression)) : 
  forall (l' : list (Expression * Expression)),
  length l = length l' ->
  (let exps := make_map_exps l in
   let exps' := make_map_exps l' in
  forall i, i < length exps -> fully_equivalent (nth i exps ErrorExp) (nth i exps' ErrorExp))
->
  fully_equivalent_single (EMap l) (EMap l').
Proof.
  assert (A :
    forall (l l' : list (Expression * Expression)) env id eff eff' id' res,
    length l = length l' ->
    (let exps := make_map_exps l in
      let exps' := make_map_exps l' in
       forall i, i < length exps -> fully_equivalent (nth i exps ErrorExp) (nth i exps' ErrorExp)) ->
    |env, id, EMap l, eff | -s> |id', res, eff'|
    ->
    |env, id, EMap l', eff | -s> |id', res, eff' |
  ). {
  intros. unfold fully_equivalent, fully_equivalent_single in *.
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
    intros. apply fully_equivalent_sym. apply H0. lia. auto.
Qed.

Theorem ETry_congr (e1 e2 e3 : Expression) vl1 vl2 : forall (e1' e2' e3' : Expression),
  fully_equivalent e1 e1' ->
  fully_equivalent e2 e2' ->
  fully_equivalent e3 e3'
->
  fully_equivalent_single (ETry e1 vl1 e2 vl2 e3) (ETry e1' vl1 e2' vl2 e3').
Proof.
  assert (A : forall e1 e1' e2 e2' e3 e3' env id eff id' res eff',
    fully_equivalent e1 e1' ->
    fully_equivalent e2 e2' ->
    fully_equivalent e3 e3' ->
    |env, id, ETry e1 vl1 e2 vl2 e3, eff | -s> |id', res, eff'|
    ->
    |env, id, ETry e1' vl1 e2' vl2 e3', eff| -s> |id', res, eff'|
  ).
  {
    intros. inversion H2; subst.
    * eapply eval_try. apply H. exact H14. auto. apply H0. exact H16.
    * eapply eval_catch. apply H. exact H14. apply H1. exact H15.
  }
  split; intros.
  * eapply A. exact H. exact H0. exact H1. auto.
  * eapply A.
    1-3: apply fully_equivalent_sym.
    exact H. exact H0. exact H1. auto.
Qed.

Theorem EValues_congr (l : list SingleExpression) : forall (l' : list SingleExpression),
  length l = length l' ->
  (forall i, i < length l -> fully_equivalent_single (nth i l ErrorExp) (nth i l' ErrorExp))
->
  fully_equivalent (EValues l) (EValues l').
Proof.
  assert (A : forall (l l' : list SingleExpression) env id eff id' res eff',
    length l = length l' ->
    (forall i, i < length l -> fully_equivalent_single (nth i l ErrorExp) (nth i l' ErrorExp))
    ->
    |env, id, EValues l, eff| -e> |id', res, eff'|
    ->
    |env, id, EValues l', eff| -e> |id', res, eff'|). {
  intros. unfold fully_equivalent, fully_equivalent_single in *.
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
    apply fully_equivalent_single_sym. auto. auto.
Qed.

Theorem ESingle_congr (e : SingleExpression)  : forall (e': SingleExpression),
  fully_equivalent_single e e'
->
  fully_equivalent (ESingle e) (ESingle e').
Proof.
  unfold fully_equivalent_single.
  split; intros.
  * inversion H0. eapply eval_single. subst. apply H. auto.
  * inversion H0. eapply eval_single. subst. apply H. auto.
Qed.

End congruence.

Ltac cleanup_unfold_list :=
match goal with
| [H : exists _, _ |- _] => destruct H; cleanup_unfold_list
| _ => idtac
end; idtac.

Ltac unfold_list_once :=
match goal with
| [H : 0 = length ?l |- _ ] => apply eq_sym, length_zero_iff_nil in H; subst
| [H : length ?l = 0 |- _ ] => apply length_zero_iff_nil in H; subst
| [H : S ?n = length ?l |- _ ] => inversion H; apply element_exist in H; cleanup_unfold_list; subst
| [H : length ?l = S ?n |- _] => inversion H; apply eq_sym in H; apply element_exist in H; cleanup_unfold_list; subst
| _ => idtac "nomatch"
end.

Ltac unfold_list :=
match goal with
| [H : S _ = S (length _) |- _] => apply Nat.succ_inj in H; unfold_list
| [H : S (length _) = S _ |- _] => apply Nat.succ_inj in H; unfold_list
| [H : _ = length _ |- _] => simpl in H; unfold_list_once; unfold_list
| [H : length _ = _ |- _] => simpl in H; unfold_list_once; unfold_list
| _ => idtac "nomatch list"
end.

Section examples.

Example complete1 e :
  fully_equivalent (e) (ESeq (ECall "+" [^ELit (Integer 2); ^ELit (Integer 2)]) e).
Proof.
  split; intros.
  * constructor. econstructor.
    - solve.
    - exact H.
  * inversion H. inversion H3. subst.
    - inversion H12. inversion H4. subst.
      simpl in H11, H13, H14.
      unfold_list_once. inversion H1. clear H1.
      unfold_list_once. inversion H1. clear H1.
      unfold_list_once. unfold_list_once.
      unfold_list_once. unfold_list_once. unfold_list_once.
      unfold_list_once. unfold_list_once. unfold_list_once.
      unfold_list_once. unfold_list_once. unfold_list_once.
      inversion H2. subst. inversion H1. subst. inversion H5. subst.
      epose (H15 0 (Nat.lt_0_2)). simpl in e0. inversion e0. subst. inversion H9. subst.
      epose (H15 1 (Nat.lt_1_2)). simpl in e1. inversion e1. inversion H10. subst.
      simpl in H17. inversion H19. subst. assumption.
    - inversion H16. inversion H20; subst.
      + simpl in H27, H28, H29.
        unfold_list_once. inversion H1. clear H1.
        unfold_list_once. inversion H1. clear H1.
        unfold_list_once. unfold_list_once.
        unfold_list_once. unfold_list_once. unfold_list_once.
        unfold_list_once. unfold_list_once. unfold_list_once.
        unfold_list_once. unfold_list_once. unfold_list_once.
        inversion H4. inversion H2. inversion H1. subst.
        epose (H30 0 (Nat.lt_0_2)). simpl in e0. inversion e0. subst. inversion H8. subst.
        epose (H30 1 (Nat.lt_1_2)). simpl in e1. inversion e1. inversion H9. subst.
        inversion H33.
      + inversion H28. rewrite H1 in *.
        ** unfold_list_once. unfold_list_once. unfold_list_once.
           unfold_list_once. unfold_list_once. unfold_list_once. unfold_list_once.
           unfold_list_once. unfold_list_once. inversion H2. inversion H0. inversion H1.
           subst. inversion H38. inversion H7.
        ** inversion H1. 2: inversion H4.
           rewrite H4 in *. unfold_list_once. unfold_list_once. unfold_list_once.
           inversion H38. inversion H5.
Qed.

End examples.