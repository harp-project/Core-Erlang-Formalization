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

Definition strongly_equivalent e1 e2 P1 P2 :=
(forall env eff res eff' id1 id2,
  P1 id1 ->
  |env, id1, e1, eff| -e> |id2, res, eff'|
->
  exists id1' id2', |env, id1', e2, eff| -e> |id2', res, eff'|)
/\
(forall env eff res eff' id1' id2',
  P2 id1' ->
  |env, id1', e2, eff| -e> |id2', res, eff'|
->
  exists id1 id2, |env, id1, e1, eff| -e> |id2, res, eff'|).

Definition strongly_equivalent_single e1 e2 P1 P2 :=
(forall env eff res eff' id1 id2,
  P1 id1 ->
  |env, id1, e1, eff| -s> |id2, res, eff'|
->
  exists id1' id2', |env, id1', e2, eff| -s> |id2', res, eff'|)
/\
(forall env eff res eff' id1' id2',
  P2 id1' ->
  |env, id1', e2, eff| -s> |id2', res, eff'|
->
  exists id1 id2, |env, id1, e1, eff| -s> |id2, res, eff'|).

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
  strongly_equivalent e (ELet [x] (EFun [] e) (EApp (EVar x) [])) (fun x => x > 0) (fun x => True).
Proof.
  unfold strongly_equivalent.
  split; intros.
  * exists (pred id1), id2. eapply eval_single, eval_let; auto.
    - apply eval_single, eval_fun.
    - reflexivity.
    - eapply eval_single, eval_app with (vals := []) (eff := []) (ids := []); auto.
      + eapply eval_single, eval_var. simpl. rewrite get_value_here. reflexivity.
      + auto.
      + intros. inversion H1.
      + unfold get_env. simpl. auto.
        destruct id1. inversion H. simpl. auto.
  * exists (S id1'), id2'. clear H. rename H0 into H. inversion H. inversion H3; subst.
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

(* Theorem strongly_equivalent_refl e P :
  strongly_equivalent e e P P.
Proof.
  intros. unfold strongly_equivalent. split; intros.
  * eexists. eexists. exact H.
  * eexists. eexists. exact H.
Qed. *)

(*
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

(* Theorem strongly_equivalent_sym e1 e2 P1 P2 :
  strongly_equivalent e1 e2 P1 P2 -> strongly_equivalent e2 e1 P2 P1.
Proof.
  unfold strongly_equivalent; intros.
  split; apply H.
Qed. *)

(* Theorem weakly_equivalent_sym e1 e2 :
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

(* Theorem strongly_equivalent_trans e1 e2 e3 P1 P2 P3 :
  strongly_equivalent e1 e2 P1 P2 -> strongly_equivalent e2 e3 P2 P3
->
  strongly_equivalent e1 e3 P1 P3.
Proof.
  unfold strongly_equivalent; intros; destruct H, H0.
  split; intros.
  * apply H in H3. destruct H3, H3. apply H0 in H3. auto. 2: auto.
  * apply H0 in H1. apply H in H1. auto.
Qed. *)

(*
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

Theorem ECons_congr hd tl : forall hd' tl',
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

Theorem ETuple_congr (l : list Expression) : forall (l' : list Expression),
  length l = length l' ->
  (forall i, i < length l -> completely_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
->
  completely_equivalent_single (ETuple l) (ETuple l').
Proof.
  assert (A : forall (l l' : list Expression) env id eff id' res eff',
    length l = length l' ->
    (forall i, i < length l -> completely_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
    ->
    |env, id, ETuple l, eff| -s> |id', res, eff'|
    ->
    |env, id, ETuple l', eff| -s> |id', res, eff'|). {
  intros. unfold completely_equivalent, completely_equivalent_single in *.
  * inversion H1; subst; rewrite H in *.
    - eapply eval_tuple.
      + exact H3.
      + exact H4.
      + exact H5.
      + intros. pose (H6 i H2). apply H0 in e. 2: auto. auto.
      + auto.
      + auto.
    - eapply eval_tuple_ex.
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
    apply completely_equivalent_sym. auto. auto.
Qed.

Theorem ECall_congr (f : string) (l : list Expression) : forall (l' : list Expression),
  length l = length l' ->
  (forall i, i < length l -> completely_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
->
  completely_equivalent_single (ECall f l) (ECall f l').
Proof.
  assert (A : forall f (l l' : list Expression) env id eff id' res eff',
  length l = length l' ->
  (forall i, i < length l -> completely_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
  ->
  |env, id, ECall f l, eff| -s> |id', res, eff'|
  ->
  |env, id, ECall f l', eff| -s> |id', res, eff'|). {
  intros. unfold completely_equivalent, completely_equivalent_single in *.
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
    apply completely_equivalent_sym. auto. auto.
Qed.

Theorem EPrimOp_congr (f : string) (l : list Expression) : forall (l' : list Expression),
  length l = length l' ->
  (forall i, i < length l -> completely_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
->
  completely_equivalent_single (EPrimOp f l) (EPrimOp f l').
Proof.
  assert (A : forall f (l l' : list Expression) env id eff id' res eff',
  length l = length l' ->
  (forall i, i < length l -> completely_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
  ->
  |env, id, EPrimOp f l, eff| -s> |id', res, eff'|
  ->
  |env, id, EPrimOp f l', eff| -s> |id', res, eff'|). {
  intros. unfold completely_equivalent, completely_equivalent_single in *.
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
    apply completely_equivalent_sym. auto. auto.
Qed.

Theorem EApp_congr (exp : Expression) (l : list Expression) : forall (exp' : Expression) (l' : list Expression),
  length l = length l' ->
  completely_equivalent exp exp' ->
  (forall i, i < length l -> completely_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
->
  completely_equivalent_single (EApp exp l) (EApp exp' l').
Proof.
  assert (A : forall exp exp' (l l' : list Expression) env id eff id' res eff',
    length l = length l' ->
    completely_equivalent exp exp' ->
    (forall i, i < length l -> completely_equivalent (nth i l ErrorExp) (nth i l' ErrorExp))
    ->
    |env, id, EApp exp l, eff| -s> |id', res, eff'|
    ->
    |env, id, EApp exp' l', eff| -s> |id', res, eff'|).
  {
    unfold completely_equivalent.
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
    apply completely_equivalent_sym. auto.
    intros. apply completely_equivalent_sym. apply H1. lia.
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
((forall i, i < length l -> completely_equivalent (nth i (map snd l) ErrorExp)
                                                   (nth i (map snd l') ErrorExp) /\
                             completely_equivalent (nth i (map snd (map fst l)) ErrorExp)
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
  completely_equivalent exp exp' ->
  (forall i, i < length l -> completely_equivalent (nth i (map snd l) ErrorExp)
                                                   (nth i (map snd l') ErrorExp) /\
                             completely_equivalent (nth i (map snd (map fst l)) ErrorExp)
                                                   (nth i (map snd (map fst l')) ErrorExp)
                   /\ nth i (map fst (map fst l)) [] = nth i (map fst (map fst l')) [])
->
  completely_equivalent_single (ECase exp l) (ECase exp' l').
Proof.
  intros. unfold completely_equivalent, completely_equivalent_single in *.
  split; intros; inversion H2; subst.
  * eapply eval_case; rewrite H in *.
    - apply H0. exact H5.
    - exact H6.
    - apply case_congr_helper with (l' := l') in H7.
      3: unfold completely_equivalent; rewrite H; exact H1.
      exact H7.
      auto.
    - intros. assert (match_clause vals l' j = Some (gg, ee, bb)). { auto. }
      apply match_clause_ith in H9. destruct H9. destruct H10. subst.
      apply case_congr_helper with (l' := l) in H4. 2: auto.
      pose (H8 j H3 _ _ _ H4). epose (H1 j _). Unshelve. 3: lia. destruct a.
      apply H10. exact e.
      intros. split. 2: split.
      + apply completely_equivalent_sym. epose (H1 i0 _). Unshelve. 2: lia. destruct a.
        unfold completely_equivalent.
        intros. apply H10.
      + apply completely_equivalent_sym. epose (H1 i0 _). Unshelve. 2: lia. destruct a.
        unfold completely_equivalent.
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
      + apply completely_equivalent_sym. epose (H1 i _). Unshelve. 2: lia. destruct a.
        unfold completely_equivalent.
        intros. apply H6.
      + apply completely_equivalent_sym. epose (H1 i _). Unshelve. 2: lia. destruct a.
        unfold completely_equivalent.
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
      + apply completely_equivalent_sym. pose (H1 i0 H3). unfold completely_equivalent.
        apply a.
      + apply completely_equivalent_sym. pose (H1 i0 H3). unfold completely_equivalent.
        apply a.
      + pose (H1 i0 H3). unfold completely_equivalent. destruct a. destruct H9.
        symmetry. apply H10.
    - intros. assert (match_clause vals l j = Some (gg, ee, bb)). { auto. }
      apply match_clause_ith in H9. destruct H9. destruct H10. subst.
      apply case_congr_helper with (l' := l') in H4. 2: auto.
      pose (H8 j H3 _ _ _ H4). epose (H1 j _). Unshelve. 3: lia. destruct a.
      apply H10. exact e.
      intros. split. 2: split.
      + apply completely_equivalent_sym. epose (H1 i0 _). Unshelve. 2: lia. destruct a.
        unfold completely_equivalent. symmetry.
        intros. apply H10.
      + apply completely_equivalent_sym. epose (H1 i0 _). Unshelve. 2: lia. destruct a.
        unfold completely_equivalent.
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
      + apply completely_equivalent_sym. epose (H1 i _). Unshelve. 2: lia. destruct a.
        unfold completely_equivalent.
        intros. symmetry. apply H6.
      + apply completely_equivalent_sym. epose (H1 i _). Unshelve. 2: lia. destruct a.
        unfold completely_equivalent.
        intros. symmetry. apply H8.
      + epose (H1 i _). Unshelve. 2: lia. destruct a.
        destruct H8. auto.
Qed.

Theorem ELet_congr (e1 e2 : Expression) vl : forall (e1' e2' : Expression),
  completely_equivalent e1 e1' ->
  completely_equivalent e2 e2'
->
  completely_equivalent_single (ELet vl e1 e2) (ELet vl e1' e2').
Proof.
  intros. unfold completely_equivalent, completely_equivalent_single in *.
  split; intros.
  * inversion H1; subst.
    - eapply eval_let. apply H. exact H7. auto. apply H0. exact H13.
    - eapply eval_let_ex. apply H. auto.
  * inversion H1; subst.
    - eapply eval_let. apply H. exact H7. auto. apply H0. exact H13.
    - eapply eval_let_ex. apply H. auto.
Qed.

Theorem ESeq_congr (e1 e2 : Expression) (l : list Expression) : forall (e1' e2' : Expression),
  completely_equivalent e1 e1' ->
  completely_equivalent e2 e2'
->
  completely_equivalent_single (ESeq e1 e2) (ESeq e1' e2').
Proof.
  intros. unfold completely_equivalent, completely_equivalent_single in *.
  split; intros.
  * inversion H1; subst.
    - eapply eval_seq. apply H. exact H6. auto. apply H0. exact H11.
    - eapply eval_seq_ex. apply H. auto.
  * inversion H1; subst.
    - eapply eval_seq. apply H. exact H6. auto. apply H0. exact H11.
    - eapply eval_seq_ex. apply H. auto.
Qed.

Theorem ELetRec_congr (exp : Expression) l : forall (exp' : Expression),
  completely_equivalent exp exp'
->
  completely_equivalent_single (ELetRec l exp) (ELetRec l exp').
Proof.
  intros. unfold completely_equivalent, completely_equivalent_single in *.
  split; intros.
  * inversion H0. subst. eapply eval_letrec. apply H. exact H9.
  * inversion H0. subst. eapply eval_letrec. apply H. exact H9.
Qed.

Theorem EMap_congr (l : list (Expression * Expression)) : 
  forall (l' : list (Expression * Expression)),
  length l = length l' ->
  (let exps := make_map_exps l in
   let exps' := make_map_exps l' in
  forall i, i < length exps -> completely_equivalent (nth i exps ErrorExp) (nth i exps' ErrorExp))
->
  completely_equivalent_single (EMap l) (EMap l').
Proof.
  assert (A :
    forall (l l' : list (Expression * Expression)) env id eff eff' id' res,
    length l = length l' ->
    (let exps := make_map_exps l in
      let exps' := make_map_exps l' in
       forall i, i < length exps -> completely_equivalent (nth i exps ErrorExp) (nth i exps' ErrorExp)) ->
    |env, id, EMap l, eff | -s> |id', res, eff'|
    ->
    |env, id, EMap l', eff | -s> |id', res, eff' |
  ). {
  intros. unfold completely_equivalent, completely_equivalent_single in *.
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
    intros. apply completely_equivalent_sym. apply H0. lia. auto.
Qed.

Theorem ETry_congr (e1 e2 e3 : Expression) vl1 vl2 : forall (e1' e2' e3' : Expression),
  completely_equivalent e1 e1' ->
  completely_equivalent e2 e2' ->
  completely_equivalent e3 e3'
->
  completely_equivalent_single (ETry e1 vl1 e2 vl2 e3) (ETry e1' vl1 e2' vl2 e3').
Proof.
  assert (A : forall e1 e1' e2 e2' e3 e3' env id eff id' res eff',
    completely_equivalent e1 e1' ->
    completely_equivalent e2 e2' ->
    completely_equivalent e3 e3' ->
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
    1-3: apply completely_equivalent_sym.
    exact H. exact H0. exact H1. auto.
Qed.

Theorem EValues_congr (l : list SingleExpression) : forall (l' : list SingleExpression),
  length l = length l' ->
  (forall i, i < length l -> completely_equivalent_single (nth i l ErrorExp) (nth i l' ErrorExp))
->
  completely_equivalent (EValues l) (EValues l').
Proof.
  assert (A : forall (l l' : list SingleExpression) env id eff id' res eff',
    length l = length l' ->
    (forall i, i < length l -> completely_equivalent_single (nth i l ErrorExp) (nth i l' ErrorExp))
    ->
    |env, id, EValues l, eff| -e> |id', res, eff'|
    ->
    |env, id, EValues l', eff| -e> |id', res, eff'|). {
  intros. unfold completely_equivalent, completely_equivalent_single in *.
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
    apply completely_equivalent_single_sym. auto. auto.
Qed.

Theorem ESingle_congr (e : SingleExpression)  : forall (e': SingleExpression),
  completely_equivalent_single e e'
->
  completely_equivalent (ESingle e) (ESingle e').
Proof.
  unfold completely_equivalent_single.
  split; intros.
  * inversion H0. eapply eval_single. subst. apply H. auto.
  * inversion H0. eapply eval_single. subst. apply H. auto.
Qed.

(* Lemma value_exception_eq_dec (res res' : ValueSequence + Exception) : {res = res'} + {res <> res'}.
Proof.
  set Value_eq_dec.
  repeat decide equality.
Defined.

Lemma se_list_eq_dec (l l' : SideEffectList) : {l = l'} + {l <> l'}.
Proof.
  set Value_eq_dec.
  set string_dec.
  repeat decide equality.
Defined. *)

(* Definition strongly_equivalent2 (e1 e2 : Expression) :=
(forall env id1 id1' id2 id2' eff eff' eff2' res res',
  |env, id1, e1, eff| -e> |id1', res, eff'|
->
  |env, id2, e2, eff| -e> |id2', res', eff2'|
-> res = res' /\ eff' = eff2').

Definition strongly_equivalent_single2 (e1 e2 : SingleExpression) :=
(forall env id1 id1' id2 id2' eff eff' eff2' res res',
  |env, id1, e1, eff| -s> |id1', res, eff'|
->
  |env, id2, e2, eff| -s> |id2', res', eff2'|
-> res = res' /\ eff' = eff2').
(*
Definition strongly_equivalent_single2 e1 e2 id1 id1' id2 id2' :=
(forall env eff res eff',
  |env, id1, e1, eff| -s> |id1', res, eff'|
<->
  |env, id2, e2, eff| -s> |id2', res, eff'|). *)

Theorem reflll e:
  strongly_equivalent2 e e.
Proof.
  unfold strongly_equivalent2. intros.
  pose (eval_expr_determinism H _ _ _ H0).

Theorem ECons_congruence_strongly hd tl : forall hd' tl',
  strongly_equivalent2 tl tl' -> 
  strongly_equivalent2 hd hd'
->
  strongly_equivalent_single2 (ECons hd tl) (ECons hd' tl').
Proof.
  intros. unfold strongly_equivalent2, strongly_equivalent_single2 in *.
  intros. inversion H1; inversion H2; subst.
  * pose (H _ _ _ _ _ _ _ _ _ _ H7 H17). inversion a. subst.
    pose (H0 _ _ _ _ _ _ _ _ _ _ H12 H22). inversion a0. inversion H3. inversion H4.
    subst. auto.
  * pose (H _ _ _ _ _ _ _ _ _ _ H7 H21). destruct a. congruence.
  * pose (H0 _ _ _ _ _ _ _ _ _ _ H12 H22). destruct a. congruence.
  * pose (H _ _ _ _ _ _ _ _ _ _ _ H11 H16). congruence.
  * pose (H _ _ _ _ _ _ _ _ _ _ _ H11 H20). auto.
  * pose (H _ _ _ _ _ _ _ _ _ _ _ H11 H16). congruence.
  * pose (H0 _ _ _ _ _ _ _ _ _ _ _ H12 H22). congruence.
  * pose (H _ _ _ _ _ _ _ _ _ _ _ H7 H21). congruence.
  * pose (H _ _ _ _ _ _ _ _ _ _ _ H7 H17).
    pose (H0 _ _ _ _ _ _ _ _ _ _ _ H12 H22). auto.
Qed. *)

End congruence.

Require Import Coq.Sorting.Permutation.

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

Definition write (s : string) : Expression :=
  ESingle (ECall "fwrite" [^ELit (Atom s)]).

Ltac cleanup_unfold_list :=
match goal with
| [H : exists _, _ |- _] => destruct H; cleanup_unfold_list
| _ => idtac
end; idtac.

Ltac unfold_list_once :=
match goal with
| [H : S ?n = length ?l |- _ ] => inversion H; apply element_exist in H; cleanup_unfold_list; subst
| [H : length ?l = S ?n |- _] => inversion H; apply eq_sym in H; apply element_exist in H; cleanup_unfold_list; subst
| [H : 0 = length ?l |- _ ] => apply eq_sym, length_zero_iff_nil in H; subst
| [H : length ?l = 0 |- _ ] => apply length_zero_iff_nil in H; subst
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

Theorem effectlist_irrelevant e :
forall env id id' eff res eff',
| env, id, e, eff | -e> |id', res, eff ++ eff'|
->
forall eff0,
| env, id, e, eff0| -e> |id', res, eff0 ++ eff'|.
Proof.






Admitted.

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
(forall env id e eff id' res eff',
  | env, id, e, eff | -e> | id', res, eff' |
->
  exists l, eff' = eff ++ l)
.
Proof.
  apply effect_extension.
Qed.

Theorem effect_extension_single :
(forall env id e eff id' res eff',
  | env, id, e, eff | -s> | id', res, eff' |
->
  exists l, eff' = eff ++ l).
Proof.
  apply effect_extension.
Qed.

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
      pose (effect_extension_expr _ _ _ _ _ _ _ H6). destruct e. subst.
      apply effectlist_irrelevant with (eff0 := x) in H6.
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
      pose (effect_extension_expr _ _ _ _ _ _ _ H6). destruct e. subst.
      apply effectlist_irrelevant with (eff0 := x) in H6.
      exists (x ++ x1). split.
      + eapply eval_seq. exact H4. exact H6.
      + eapply perm_trans.
        ** exact H7.
        ** apply Permutation_app_tail. auto.
    - subst. apply H in H10. destruct H10.
      eexists. split. eapply eval_seq_ex. apply H2. apply H2.
Qed.
 

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
           -- intros. inversion H0. 2: inversion H2. solve.
           -- reflexivity.
      + simpl. simpl in HH.
        eapply effectlist_irrelevant in HH.
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
           -- intros. inversion H0. 2: inversion H2. solve.
           -- reflexivity.
      + simpl. simpl in HH.
        eapply effectlist_irrelevant in HH.
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