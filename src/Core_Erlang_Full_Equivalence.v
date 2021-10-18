Require Core_Erlang_Semantics_Equivalence.

Export Core_Erlang_Semantics_Equivalence.

Import Core_Erlang_Tactics.Tactics.
Import ListNotations.


Definition fully_equivalent_expr e1 e2 :=
forall env eff res eff' id1 id2,
  (exists clock, fbs_expr clock env id1 e1 eff = Result id2 res eff')
<->
  (exists clock, fbs_expr clock env id1 e2 eff = Result id2 res eff').

Definition fully_equivalent_exprlist l1 l2 :=
forall env eff res eff' id1 id2,
  (exists clock, fbs_values (fbs_expr clock) env id1 l1 eff = Result id2 res eff')
<->
  (exists clock, fbs_values (fbs_expr clock) env id1 l2 eff = Result id2 res eff').

Definition fully_equivalent_case l1 l2 :=
forall env eff res eff' id1 id2 vals,
  (exists clock, fbs_case l1 env id1 eff vals (fbs_expr clock) = Result id2 res eff')
<->
  (exists clock, fbs_case l2 env id1 eff vals (fbs_expr clock) = Result id2 res eff').

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

Theorem fully_equivalent_case_refl {l} :
  fully_equivalent_case l l.
Proof.
  intros. unfold fully_equivalent_case. split; intros.
  * auto.
  * auto.
Qed.

Theorem fully_equivalent_case_sym {l1 l2} :
  fully_equivalent_case l1 l2 -> fully_equivalent_case l2 l1.
Proof.
  unfold fully_equivalent_case; intros.
  split; apply H.
Qed.

Theorem fully_equivalent_case_trans {l1 l2 l3} :
  fully_equivalent_case l1 l2 -> fully_equivalent_case l2 l3
->
  fully_equivalent_case l1 l3.
Proof.
  unfold fully_equivalent_case; intros.
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

Theorem fully_equivalent_elements_case (l l' : list (list Pattern * Expression * Expression )) :
  length l = length l' ->
  ((forall i, i < length l -> fully_equivalent_expr (nth i (map snd l) ErrorExp)
                                                   (nth i (map snd l') ErrorExp) /\
                             fully_equivalent_expr (nth i (map snd (map fst l)) ErrorExp)
                                                   (nth i (map snd (map fst l')) ErrorExp)
                   /\ nth i (map fst (map fst l)) [] = nth i (map fst (map fst l')) []))
->
  fully_equivalent_case l l'
.
Proof.
  generalize dependent l'. induction l; intros.
  * apply eq_sym, length_zero_iff_nil in H. subst. split; intros; assumption.
  * pose (EE := element_exist _ _ H). destruct EE, H1. subst. inversion H.
    pose (F := H0 0 (Nat.lt_0_succ _)). simpl in F.
    epose (IH := IHl _ H2 _). Unshelve. 2: { intros. apply (H0 (S i)). simpl. lia. }
    split; intros; destruct H1; simpl in H1.
    - destruct a, p. destruct (match_valuelist_to_patternlist vals l0) eqn:D1.
      + destruct (fbs_expr x1 (add_bindings (match_valuelist_bind_patternlist vals l0) env) id1 e0
         eff) eqn:D2.
         destruct res0. destruct v. congruence. destruct v0. 2: congruence. 3-4: congruence.
         ** destruct (((id =? id1) && list_eqb effect_eqb eff eff0)%bool) eqn:D3. 2: congruence.
            apply andb_prop in D3. destruct D3. apply Nat.eqb_eq in H3.
            apply effect_list_eqb_eq in H4. subst.
            destruct v; try congruence. destruct l1; try congruence.
            destruct (s =? "true")%string eqn:D4.
            -- apply eqb_eq in D4. subst.
               destruct F, H4. destruct x, p. simpl in H3, H4, H5.
               epose (P := H4 _ _ _ _ _ _). destruct P. pose (P1 := H6 (ex_intro _ _ D2)).
               epose (P := H3 _ _ _ _ _ _). destruct P. pose (P2 := H8 (ex_intro _ _ H1)).
               destruct P1, P2. exists (x + x2). simpl. subst. rewrite D1.
               erewrite (bigger_clock_expr _ _ H10). rewrite Nat.eqb_refl, effect_list_eqb_refl.
               simpl. eapply (bigger_clock_expr _ _ H11). Unshelve. all: lia.
            -- destruct (s =? "false")%string eqn:D5. 2: congruence.
               apply eqb_eq in D5. subst.
               destruct F, H4. destruct x, p. simpl in H3, H4, H5.
               epose (P := H4 _ _ _ _ _ _). destruct P. pose (P1 := H6 (ex_intro _ _ D2)).
               epose (P := IH _ _ _ _ _ _ _). destruct P. pose (P2 := H8 (ex_intro _ _ H1)).
               clear IH. destruct P1, P2. exists (x + x2). simpl. subst. rewrite D1.
               erewrite (bigger_clock_expr _ _ H10). rewrite Nat.eqb_refl, effect_list_eqb_refl.
               simpl. eapply (bigger_clock_case _ H11 _). Unshelve. all: lia.
         ** congruence.
       + epose (P := IH _ _ _ _ _ _ _). destruct P. pose (P2 := H3 (ex_intro _ _ H1)).
         clear IH. destruct P2. exists x2. simpl. destruct F, H7. destruct x, p.
         simpl in H6, H7, H8. subst. rewrite D1. assumption.
    - destruct x, p. destruct (match_valuelist_to_patternlist vals l0) eqn:D1.
      + destruct (fbs_expr x1 (add_bindings (match_valuelist_bind_patternlist vals l0) env) id1 e0
         eff) eqn:D2.
         destruct res0. destruct v. congruence. destruct v0. 2: congruence. 3-4: congruence.
         ** destruct (((id =? id1) && list_eqb effect_eqb eff eff0)%bool) eqn:D3. 2: congruence.
            apply andb_prop in D3. destruct D3. apply Nat.eqb_eq in H3.
            apply effect_list_eqb_eq in H4. subst.
            destruct v; try congruence. destruct l1; try congruence.
            destruct (s =? "true")%string eqn:D4.
            -- apply eqb_eq in D4. subst.
               destruct F, H4. destruct a, p. simpl in H3, H4, H5.
               epose (P := H4 _ _ _ _ _ _). destruct P. pose (P1 := H7 (ex_intro _ _ D2)).
               epose (P := H3 _ _ _ _ _ _). destruct P. pose (P2 := H9 (ex_intro _ _ H1)).
               destruct P1, P2. exists (x + x2). simpl. subst. rewrite D1.
               erewrite (bigger_clock_expr _ _ H10). rewrite Nat.eqb_refl, effect_list_eqb_refl.
               simpl. eapply (bigger_clock_expr _ _ H11). Unshelve. all: lia.
            -- destruct (s =? "false")%string eqn:D5. 2: congruence.
               apply eqb_eq in D5. subst.
               destruct F, H4. destruct a, p. simpl in H3, H4, H5.
               epose (P := H4 _ _ _ _ _ _). destruct P. pose (P1 := H7 (ex_intro _ _ D2)).
               epose (P := IH _ _ _ _ _ _ _). destruct P. pose (P2 := H9 (ex_intro _ _ H1)).
               clear IH. destruct P1, P2. exists (x + x2). simpl. subst. rewrite D1.
               erewrite (bigger_clock_expr _ _ H10). rewrite Nat.eqb_refl, effect_list_eqb_refl.
               simpl. eapply (bigger_clock_case _ H11 _). Unshelve. all: lia.
         ** congruence.
       + epose (P := IH _ _ _ _ _ _ _). destruct P. pose (P2 := H4 (ex_intro _ _ H1)).
         clear IH. destruct P2. exists x. simpl. destruct F, H7. destruct a, p.
         simpl in H6, H7, H8. subst. rewrite D1. assumption.
Qed.

End equivalence_relation.

Section congruence.

Theorem ECons_full_cong hd tl : forall hd' tl',
  fully_equivalent_expr hd hd' -> fully_equivalent_expr tl tl'
->
  fully_equivalent_expr (ECons hd tl) (ECons hd' tl').
Proof.
  assert (A : forall env id hd tl hd' tl' eff id' res eff',
    fully_equivalent_expr hd hd' -> fully_equivalent_expr tl tl'
   ->
    (exists clock, fbs_expr clock env id (ECons hd tl) eff = Result id' res eff')
   ->
    (exists clock, fbs_expr clock env id (ECons hd' tl') eff = Result id' res eff')
  ).
  {
  intros.
  * destruct H1. destruct x. inversion H1. simpl in H1.
    destruct (fbs_expr x env id tl0 eff) eqn:D1.
    destruct res0. destruct v. congruence. destruct v0. 2: congruence. 3-4: congruence.
    - destruct (fbs_expr x env id0 hd0 eff0) eqn:D2.
      destruct res0. destruct v0. congruence. destruct v1. 2: congruence. 3-4: congruence.
      + inversion H1. subst. epose (D1' := H0 _ _ _ _ _ _). destruct D1'. epose (H2 (ex_intro _ x D1)).
        epose (D2' := H _ _ _ _ _ _). destruct D2'. epose (H4 (ex_intro _ x D2)). destruct e, e0.
        exists (S (x0 + x1)). simpl. erewrite (bigger_clock_expr _ _ H6), (bigger_clock_expr _ _ H7). reflexivity.
      + inversion H1. subst. epose (D1' := H0 _ _ _ _ _ _). destruct D1'. epose (H2 (ex_intro _ x D1)).
        epose (D2' := H _ _ _ _ _ _). destruct D2'. epose (H4 (ex_intro _ x D2)). destruct e0, e1.
        exists (S (x0 + x1)). simpl. erewrite (bigger_clock_expr _ _ H6), (bigger_clock_expr _ _ H7). reflexivity.
    - inversion H1. subst. epose (D1' := H0 _ _ _ _ _ _). destruct D1'. epose (H2 (ex_intro _ x D1)).
      destruct e0. exists (S x0). simpl. rewrite H4. auto.
  }
  split; intros.
  * eapply A. exact H. exact H0. exact H1.
  * eapply A. exact (fully_equivalent_expr_sym H). exact (fully_equivalent_expr_sym H0).
    exact H1.
Unshelve.
all: lia.
Qed.

Theorem ETuple_full_cong (l : list Expression) : forall (l' : list Expression),
  fully_equivalent_exprlist l l'
->
  fully_equivalent_expr (ETuple l) (ETuple l').
Proof.
  assert (A : forall (l l' : list Expression) env id eff id' res eff',
    fully_equivalent_exprlist l l'
    ->
    (exists clock, fbs_expr clock env id (ETuple l) eff = Result id' res eff')
    ->
    (exists clock, fbs_expr clock env id (ETuple l') eff = Result id' res eff')).
  {
    intros. unfold fully_equivalent_exprlist, fully_equivalent_expr in *.
    destruct H0. destruct x. inversion H0. simpl in H0.
    destruct (fbs_values (fbs_expr x) env id l0 eff) eqn:D.
    destruct res0. 3-4: congruence.
    * inversion H0. subst. epose (E := H _ _ _ _ _ _). destruct E.
      pose (E := H1 (ex_intro _ x D)). destruct E. exists (S x0). simpl. rewrite H3. auto.
    * inversion H0. subst. epose (E := H _ _ _ _ _ _). destruct E.
      pose (E := H1 (ex_intro _ x D)). destruct E. exists (S x0). simpl. rewrite H3. auto.
  }
  split; intros.
  * eapply A. exact H. auto.
  * eapply A. exact (fully_equivalent_exprlist_sym H). exact H0.
Qed.

Theorem ECall_full_cong (m : string) (f : string) (l : list Expression) : forall (l' : list Expression),
  fully_equivalent_exprlist l l'
->
  fully_equivalent_expr (ECall m f l) (ECall m f l').
Proof.
  assert (A : forall f (l l' : list Expression) env id eff id' res eff',
  fully_equivalent_exprlist l l'
  ->
  (exists clock, fbs_expr clock env id (ECall m f l) eff = Result id' res eff')
  ->
  (exists clock, fbs_expr clock env id (ECall m f l') eff = Result id' res eff')). 
  {
    intros. destruct H0, x. inversion H0. simpl in H0.
    destruct (fbs_values (fbs_expr x) env id l0 eff) eqn:D.
    destruct res0. 3-4: congruence.
    all: epose (P := H _ _ _ _ _ _); destruct P; pose (P := H1 (ex_intro _ x D));
      destruct P; exists (S x0); simpl; rewrite H3; assumption.
  }
  split; intros.
  * eapply A. exact H. auto.
  * eapply A. exact (fully_equivalent_exprlist_sym H). exact H0.
Qed.

Theorem EPrimOp_full_cong (f : string) (l : list Expression) : forall (l' : list Expression),
  fully_equivalent_exprlist l l'
->
  fully_equivalent_expr (EPrimOp f l) (EPrimOp f l').
Proof.
  assert (A : forall f (l l' : list Expression) env id eff id' res eff',
  fully_equivalent_exprlist l l'
  ->
  (exists clock, fbs_expr clock env id (EPrimOp f l) eff = Result id' res eff')
  ->
  (exists clock, fbs_expr clock env id (EPrimOp f l') eff = Result id' res eff')). 
  {
    intros. destruct H0, x. inversion H0. simpl in H0.
    destruct (fbs_values (fbs_expr x) env id l0 eff) eqn:D.
    destruct res0. 3-4: congruence.
    all: epose (P := H _ _ _ _ _ _); destruct P; pose (P := H1 (ex_intro _ x D));
      destruct P; exists (S x0); simpl; rewrite H3; assumption.
  }
  split; intros.
  * eapply A. exact H. auto.
  * eapply A. exact (fully_equivalent_exprlist_sym H). exact H0.
Qed.

Theorem EApp_full_cong (exp : Expression) (l : list Expression) : forall (exp' : Expression) (l' : list Expression),
  fully_equivalent_expr exp exp' ->
  fully_equivalent_exprlist l l'
->
  fully_equivalent_expr (EApp exp l) (EApp exp' l').
Proof.
  assert (A : forall exp exp' (l l' : list Expression) env id eff id' res eff',
    fully_equivalent_expr exp exp' ->
    fully_equivalent_exprlist l l'
    ->
    (exists clock, fbs_expr clock env id (EApp exp l) eff = Result id' res eff')
    ->
    (exists clock, fbs_expr clock env id (EApp exp' l') eff = Result id' res eff')).
  {
    intros. destruct H1, x. inversion H1. simpl in H1.
    destruct (fbs_expr x env id exp0 eff) eqn:D1.
    destruct res0. destruct v. congruence. destruct v0. 2: congruence. 3-4: congruence.
    * destruct (fbs_values (fbs_expr x) env id0 l0 eff0) eqn:D2.
      destruct res0. 3-4: congruence.
      - epose (P := H _ _ _ _ _ _); destruct P; pose (P := H2 (ex_intro _ x D1)); destruct P;
        epose (P := H0 _ _ _ _ _ _); destruct P; pose (P := H5 (ex_intro _ x D2)); destruct P.
        destruct v.
        + exists (S (x0 + x1)); simpl; eapply bigger_clock_list in H7;
          try (erewrite (bigger_clock_expr _ _ H4), H7; assumption).
          lia.
          intros; apply clock_increase_expr; auto.
        + exists (S (x0 + x1)); simpl; eapply bigger_clock_list in H7;
          try (erewrite (bigger_clock_expr _ _ H4), H7; assumption).
          lia.
          intros; apply clock_increase_expr; auto.
        + destruct (length vl =? length v0) eqn:D3.
          ** exists (S (x0 + x1 + x)). simpl; eapply bigger_clock_list in H7.
             erewrite (bigger_clock_expr _ _ H4), H7, D3, (bigger_clock_expr _ _ H1). auto.
             lia.
             intros; apply clock_increase_expr; auto.
          ** exists (S (x0 + x1)); simpl; eapply bigger_clock_list in H7.
             erewrite (bigger_clock_expr _ _ H4), H7, D3. assumption.
             lia.
             intros; apply clock_increase_expr; auto.
        + exists (S (x0 + x1)); simpl; eapply bigger_clock_list in H7;
          try (erewrite (bigger_clock_expr _ _ H4), H7; assumption).
          lia.
          intros; apply clock_increase_expr; auto.
        + exists (S (x0 + x1)); simpl; eapply bigger_clock_list in H7;
          try (erewrite (bigger_clock_expr _ _ H4), H7; assumption).
          lia.
          intros; apply clock_increase_expr; auto.
        + exists (S (x0 + x1)); simpl; eapply bigger_clock_list in H7;
          try (erewrite (bigger_clock_expr _ _ H4), H7; assumption).
          lia.
          intros; apply clock_increase_expr; auto.
      - epose (P := H _ _ _ _ _ _). destruct P. pose (P := H2 (ex_intro _ x D1)). destruct P.
        epose (P := H0 _ _ _ _ _ _). destruct P. pose (P := H5 (ex_intro _ x D2)). destruct P.
        exists (S (x0 + x1)). simpl. eapply bigger_clock_list in H7.
        erewrite (bigger_clock_expr _ _ H4), H7. assumption.
        lia. intros. apply clock_increase_expr. auto.
    * epose (P := H _ _ _ _ _ _). destruct P. pose (P := H2 (ex_intro _ x D1)).
      destruct P. exists (S x0). simpl. rewrite H4. assumption.
  }
  split; intros.
  * eapply A. exact H. exact H0. auto.
  * eapply A. exact (fully_equivalent_expr_sym H). exact (fully_equivalent_exprlist_sym H0). exact H1.
Unshelve.
all: lia.
Qed.

Theorem ECase_full_cong (exp : Expression) (l : list (list Pattern * Expression * Expression)) : forall (exp' : Expression) (l' : list (list Pattern * Expression * Expression)),
  fully_equivalent_expr exp exp' ->
  fully_equivalent_case l l'
->
  fully_equivalent_expr (ECase exp l) (ECase exp' l').
Proof.
  assert (A : forall exp exp' l l' env id eff id' res eff',
    fully_equivalent_expr exp exp' ->
    fully_equivalent_case l l' ->
    (exists clock, fbs_expr clock env id (ECase exp l) eff = Result id' res eff')
   ->
    (exists clock, fbs_expr clock env id (ECase exp' l') eff = Result id' res eff')
  ).
  {
    intros. destruct H1, x. inversion H1. simpl in H1.
    destruct (fbs_expr x env id exp0 eff) eqn:D.
    destruct res0. 3-4: congruence.
    * epose (P := H _ _ _ _ _ _). destruct P. pose (P := H2 (ex_intro _ x D)). destruct P.
      epose (P := H0 _ _ _ _ _ _ _). destruct P. pose (P := H5 (ex_intro _ x H1)). destruct P.
      exists (S (x0 + x1)). simpl. eapply bigger_clock_case in H7.
      erewrite (bigger_clock_expr _ _ H4). exact H7. lia.
      Unshelve. lia.
    * epose (P := H _ _ _ _ _ _). destruct P. pose (P := H2 (ex_intro _ x D)). destruct P.
      exists (S x0). simpl. rewrite H4. auto.
  }
  split; intros.
  * eapply A. exact H. exact H0. auto.
  * eapply A. exact (fully_equivalent_expr_sym H). exact (fully_equivalent_case_sym H0). auto.
Qed.

Theorem ELet_full_cong (e1 e2 : Expression) vl : forall (e1' e2' : Expression),
  fully_equivalent_expr e1 e1' ->
  fully_equivalent_expr e2 e2'
->
  fully_equivalent_expr (ELet vl e1 e2) (ELet vl e1' e2').
Proof.
  assert (A : forall env id id' res eff eff' e1 e1' e2 e2',
    fully_equivalent_expr e1 e1' ->
    fully_equivalent_expr e2 e2' ->
    (exists clock, fbs_expr clock env id (ELet vl e1 e2) eff = Result id' res eff')
   ->
    (exists clock, fbs_expr clock env id (ELet vl e1' e2') eff = Result id' res eff')
  ).
  {
    intros.
    destruct H1. destruct x. inversion H1. simpl in H1.
    destruct (fbs_expr x env id e0 eff) eqn:D1.
    destruct res0.
    destruct (Datatypes.length v =? Datatypes.length vl) eqn:D2. 2, 4-5: congruence.
    * epose (P := H _ _ _ _ _ _). destruct P. pose (P1 := H2 (ex_intro _ _ D1)).
      epose (P := H0 _ _ _ _ _ _). destruct P. pose (P2 := H4 (ex_intro _ _ H1)).
      destruct P1, P2. exists (S (x0 + x1)). simpl.
      erewrite (bigger_clock_expr _ _ H6), (bigger_clock_expr _ _ H7), D2. auto.
      Unshelve. all: lia.
    * epose (P := H _ _ _ _ _ _). destruct P. pose (P1 := H2 (ex_intro _ _ D1)). destruct P1.
      exists (S x0). simpl. erewrite (bigger_clock_expr _ _ H4). auto. Unshelve. lia.
  }
  split; intros.
  * eapply A. exact H. exact H0. auto.
  * eapply A. exact (fully_equivalent_expr_sym H). exact (fully_equivalent_expr_sym H0). auto.
Qed.

Theorem ESeq_full_cong (e1 e2 : Expression) (l : list Expression) : forall (e1' e2' : Expression),
  fully_equivalent_expr e1 e1' ->
  fully_equivalent_expr e2 e2'
->
  fully_equivalent_expr (ESeq e1 e2) (ESeq e1' e2').
Proof.
  assert (A : forall env id id' res eff eff' e1 e1' e2 e2',
    fully_equivalent_expr e1 e1' ->
    fully_equivalent_expr e2 e2' ->
    (exists clock, fbs_expr clock env id (ESeq e1 e2) eff = Result id' res eff')
   ->
    (exists clock, fbs_expr clock env id (ESeq e1' e2') eff = Result id' res eff')
  ).
  {
    intros.
    destruct H1. destruct x. inversion H1. simpl in H1.
    destruct (fbs_expr x env id e0 eff) eqn:D1.
    destruct res0. destruct v. congruence. destruct v0. 2, 4-5: congruence.
    * epose (P := H _ _ _ _ _ _). destruct P. pose (P1 := H2 (ex_intro _ _ D1)).
      epose (P := H0 _ _ _ _ _ _). destruct P. pose (P2 := H4 (ex_intro _ _ H1)).
      destruct P1, P2. exists (S (x0 + x1)). simpl.
      erewrite (bigger_clock_expr _ _ H6), (bigger_clock_expr _ _ H7). auto.
      Unshelve. all: lia.
    * epose (P := H _ _ _ _ _ _). destruct P. pose (P1 := H2 (ex_intro _ _ D1)). destruct P1.
      exists (S x0). simpl. erewrite (bigger_clock_expr _ _ H4). auto. Unshelve. lia.
  }
  split; intros.
  * eapply A. exact H. exact H0. auto.
  * eapply A. exact (fully_equivalent_expr_sym H). exact (fully_equivalent_expr_sym H0). auto.
Qed.

Theorem ELetRec_full_cong (exp : Expression) l : forall (exp' : Expression),
  fully_equivalent_expr exp exp'
->
  fully_equivalent_expr (ELetRec l exp) (ELetRec l exp').
Proof.
  intros.
  split; intros.
  * destruct H0, x. inversion H0. simpl in H0.
    epose (P := H _ _ _ _ _ _). destruct P. pose (P := H1 (ex_intro _ _ H0)). destruct P.
    exists (S x0). simpl. auto.
  * destruct H0, x. inversion H0. simpl in H0.
    epose (P := H _ _ _ _ _ _). destruct P. pose (P := H2 (ex_intro _ _ H0)). destruct P.
    exists (S x0). simpl. auto.
Qed.

Theorem EMap_full_cong (l : list (Expression * Expression)) : 
  forall (l' : list (Expression * Expression)),
  fully_equivalent_exprlist (make_map_exps l) (make_map_exps l')
->
  fully_equivalent_expr (EMap l) (EMap l').
Proof.
  assert (A :
    forall (l l' : list (Expression * Expression)) env id eff eff' id' res,
    fully_equivalent_exprlist (make_map_exps l) (make_map_exps l') ->
    (exists clock, fbs_expr clock env id (EMap l) eff = Result id' res eff')
    ->
    (exists clock, fbs_expr clock env id (EMap l') eff = Result id' res eff')
  ).
  {
    intros. unfold fully_equivalent_exprlist, fully_equivalent_expr in *.
    destruct H0. destruct x. inversion H0. simpl in H0.
    destruct (fbs_values (fbs_expr x) env id (make_map_exps l0) eff) eqn:D.
    destruct res0. 3-4: congruence.
    * inversion H0. subst. epose (E := H _ _ _ _ _ _). destruct E.
      pose (E := H1 (ex_intro _ x D)). destruct E. exists (S x0). simpl. rewrite H4. auto.
    * inversion H0. subst. epose (E := H _ _ _ _ _ _). destruct E.
      pose (E := H1 (ex_intro _ x D)). destruct E. exists (S x0). simpl. rewrite H3. auto.
  }
  split; intros.
  * eapply A. exact H. auto.
  * eapply A. exact (fully_equivalent_exprlist_sym H). auto.
Qed.

Theorem ETry_full_cong (e1 e2 e3 : Expression) vl1 vl2 : forall (e1' e2' e3' : Expression),
  fully_equivalent_expr e1 e1' ->
  fully_equivalent_expr e2 e2' ->
  fully_equivalent_expr e3 e3'
->
  fully_equivalent_expr (ETry e1 vl1 e2 vl2 e3) (ETry e1' vl1 e2' vl2 e3').
Proof.
  assert (A : forall env id id' res eff eff' e1 e1' e2 e2' e3 e3',
    fully_equivalent_expr e1 e1' ->
    fully_equivalent_expr e2 e2' ->
    fully_equivalent_expr e3 e3' ->
    (exists clock, fbs_expr clock env id (ETry e1 vl1 e2 vl2 e3) eff = Result id' res eff')
   ->
    (exists clock, fbs_expr clock env id (ETry e1' vl1 e2' vl2 e3') eff = Result id' res eff')
  ).
  {
    intros.
    destruct H2. destruct x. inversion H2. simpl in H2.
    destruct (fbs_expr x env id e0 eff) eqn:D1.
    destruct res0. destruct (Datatypes.length v =? Datatypes.length vl1) eqn:D2.
    2, 4-5: congruence.
    * epose (P := H _ _ _ _ _ _). destruct P. pose (P1 := H3 (ex_intro _ _ D1)).
      epose (P := H0 _ _ _ _ _ _). destruct P. pose (P2 := H5 (ex_intro _ _ H2)).
      destruct P1, P2. exists (S (x0 + x1)). simpl.
      erewrite (bigger_clock_expr _ _ H7), (bigger_clock_expr _ _ H8), D2. auto.
      Unshelve. all: lia.
    * epose (P := H _ _ _ _ _ _). destruct P. pose (P1 := H3 (ex_intro _ _ D1)).
      epose (P := H1 _ _ _ _ _ _). destruct P. pose (P2 := H5 (ex_intro _ _ H2)).
      destruct P1, P2. exists (S (x0 + x1)). simpl.
      erewrite (bigger_clock_expr _ _ H7), (bigger_clock_expr _ _ H8). auto.
      Unshelve. all: lia.
  }
  split; intros.
  * eapply A. exact H. exact H0. exact H1. auto.
  * eapply A. exact (fully_equivalent_expr_sym H). exact (fully_equivalent_expr_sym H0).
    exact (fully_equivalent_expr_sym H1). auto.
Qed.

Theorem EValues_full_cong (l : list Expression) : forall (l' : list Expression),
  fully_equivalent_exprlist l l'
->
  fully_equivalent_expr (EValues l) (EValues l').
Proof.
  assert (A : forall (l l' : list Expression) env id eff id' res eff',
    fully_equivalent_exprlist l l'
    ->
    (exists clock, fbs_expr clock env id (EValues l) eff = Result id' res eff')
    ->
    (exists clock, fbs_expr clock env id (EValues l') eff = Result id' res eff')).
  {
   intros. unfold fully_equivalent_exprlist, fully_equivalent_expr in *.
    destruct H0. destruct x. inversion H0. simpl in H0.
    destruct (fbs_values (fbs_expr x) env id l0 eff) eqn:D.
    destruct res0. 3-4: congruence.
    * inversion H0. subst. epose (E := H _ _ _ _ _ _). destruct E.
      pose (E := H1 (ex_intro _ x D)). destruct E. exists (S x0). simpl. rewrite H3. auto.
    * inversion H0. subst. epose (E := H _ _ _ _ _ _). destruct E.
      pose (E := H1 (ex_intro _ x D)). destruct E. exists (S x0). simpl. rewrite H3. auto.
  }
  split; intros.
  * eapply A. exact H. auto.
  * eapply A. exact (fully_equivalent_exprlist_sym H). exact H0.
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

(** 
  * Examples why list congruence and list element congruence works only in one direction
  * *)
Goal
  fully_equivalent_expr (ETuple [EApp ErrorExp []]) (ETuple [ErrorExp;EApp ErrorExp []]).
Proof.
  split; intros; destruct H; destruct x; inversion H.
  * clear H1. exists (S x).
    simpl in H; destruct x; inversion H.
    simpl in H; destruct x; inversion H.
    simpl in H. inversion H. clear H1.
    simpl. auto.
  * clear H1. exists (S x).
    simpl in H; destruct x; inversion H.
    simpl in H; destruct x; inversion H.
    simpl in H. inversion H. clear H1.
    simpl. auto.
Qed.

(** 
  * The pair of the prevoius example
  *)

Goal
  fully_equivalent_expr (ETuple [ErrorExp; EApp ErrorExp []]) (ETuple [ErrorExp;EApp ErrorExp []]).
Proof.
  apply ETuple_full_cong. apply fully_equivalent_elements_exprlist; auto.
  intros. inversion H. 2: inversion H1. 3: inversion H3.
  all: apply fully_equivalent_expr_refl.
Qed.


(**
  * Quite inconvenient to use this
  *)
Example complete1 e :
  fully_equivalent_expr (e) (ESeq (ECall "erlang" "+" [ELit (Integer 2); ELit (Integer 2)]) e).
Proof.
  split; intros.
  * destruct H. exists (S (S (S x))).
    remember (S (S x)) as x'. simpl. rewrite Heqx' at 1.
    simpl. eapply bigger_clock_expr in H. exact H. lia.
  * destruct H.
    destruct x. inversion H. simpl in H.
    destruct x. inversion H. simpl fbs_expr in H at 1.
    destruct x. inversion H. simpl fbs_expr in H at 1. simpl fbs_expr in H at 1.
    remember (S (S x)) as x'. simpl in H. exists x'. auto.
Qed.



End examples.