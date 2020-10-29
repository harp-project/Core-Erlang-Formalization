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

Theorem ECase_congr (exp : Expression) (l : list (list Pattern * Expression * Expression)) : forall (exp' : Expression) (l' : list (list Pattern * Expression * Expression)),
  length l = length l' ->
  completely_equivalent exp exp' ->
  (forall i, i < length l -> completely_equivalent (nth i (map snd l) ErrorExp)
                                                   (nth i (map snd (map fst l')) ErrorExp))
->
  completely_equivalent_single (ECase exp l) (ECase exp' l').
Proof.
  intros. unfold completely_equivalent, completely_equivalent_single in *.
  split; intros. inversion H2; subst.
  * eapply eval_case; rewrite H in *.
    - apply H0. exact H5.
    - exact H6.
    - pose (match_clause_ith _ _ _ _ _ _ H7). destruct a. destruct H4.
Admitted.

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

(* Theorem ECons_congruence_strongly hd tl : forall hd' tl' id id' id'' id2 id2' id2'',
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
Qed. *)

End congruence.
