Require Core_Erlang_Full_Equivalence.

Export Core_Erlang_Full_Equivalence.
Import ListNotations.

Definition weakly_equivalent_expr (P : list ErlModule -> Prop ) e1 e2 :=
  (*TODO: get_module io/erlang*)
(forall env modules own_module eff res eff' id1 id2, P modules ->
  (exists clock, fbs_expr clock env modules own_module id1 e1 eff = Result id2 res eff')
->
  (exists eff'', (exists clock, fbs_expr clock env modules own_module id1 e2 eff = Result id2 res eff'') /\ Permutation eff' eff'')
)
/\
(forall env modules own_module eff res eff' id1 id2, P modules -> 
  (exists clock, fbs_expr clock env modules own_module id1 e2 eff = Result id2 res eff')
->
  (exists eff'', (exists clock, fbs_expr clock env modules own_module id1 e1 eff = Result id2 res eff'') /\ Permutation eff' eff'')).



Definition weakly_equivalent_exprlist (P : list ErlModule -> Prop ) l1 l2 :=
(forall env modules own_module  eff res eff' id1 id2, P modules ->
  (exists clock, fbs_values (fbs_expr clock) env modules own_module id1 l1 eff = Result id2 res eff')
->
  (exists eff'', (exists clock, fbs_values (fbs_expr clock) env modules own_module id1 l2 eff = Result id2 res eff'') /\ Permutation eff' eff'')
)
/\
(forall env modules own_module eff res eff' id1 id2, P modules ->
  (exists clock, fbs_values (fbs_expr clock) env modules own_module id1 l2 eff = Result id2 res eff')
->
  (exists eff'', (exists clock, fbs_values (fbs_expr clock) env modules own_module id1 l1 eff = Result id2 res eff'') /\ Permutation eff' eff'')).

Definition weakly_equivalent_case (P : list ErlModule -> Prop ) l1 l2 :=
(forall env modules own_module eff res eff' id1 id2 vals, P modules ->
  (exists clock, fbs_case l1 env modules own_module id1 eff vals (fbs_expr clock) = Result id2 res eff')
->
  (exists eff'', (exists clock, fbs_case l2 env modules own_module id1 eff vals (fbs_expr clock)= Result id2 res eff'') /\ Permutation eff' eff'')
)
/\
(forall env modules own_module eff res eff' id1 id2 vals, P modules ->
  (exists clock, fbs_case l2 env modules own_module id1 eff vals (fbs_expr clock) = Result id2 res eff')
->
  (exists eff'', (exists clock, fbs_case l1 env modules own_module id1 eff vals (fbs_expr clock) = Result id2 res eff'') /\ Permutation eff' eff'')).

Ltac perm_hypos :=
match goal with
| [ H : Permutation (?h ++ _) (?h ++ _) |- _ ] => apply Permutation_app_inv_l in H
| _                                          => idtac "not permutation hypo"
end.

Ltac perm_solver :=
match goal with
| |- Permutation (_ ++ _) (_ ++ _) => apply Permutation_app; perm_solver
| |- Permutation ?h ?h             => apply Permutation_refl
| [H : ?P |- ?P]                   => assumption
| |- Permutation _  _              => idtac "perming"; repeat perm_hypos; perm_solver
| _                                => idtac "not permutation"
end.

Section helpers.

Theorem last_remove_first {A : Type} :
forall (l : list A) e1 e2 def,
  last (e1 :: e2 :: l) def = last (e2 :: l) def.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma effect_extension_exprlist_helper el :
forall {env modules own_module id0 eff id' res eff' clock},
(forall (env : Environment) (id : nat) (e : Expression)
                          (eff : SideEffectList) (id' : nat) (res : ValueSequence + Exception)
                          (eff' : SideEffectList),
                        fbs_expr clock env modules own_module id e eff = Result id' res eff' ->
                        exists l : list (SideEffectId * list Value), eff' = eff ++ l)
  ->
fbs_values (fbs_expr clock) env modules own_module id0 el eff = Result id' res eff'
->
exists l, eff' = eff ++ l.
Proof.
  induction el; intros.
  * simpl in H0. inversion H0. subst. exists []. rewrite app_nil_r. auto.
  * simpl in H0.
    destruct (fbs_expr clock env modules own_module id0 a eff) eqn:D.
    destruct res0. destruct v. congruence. destruct v0. 2: congruence.
    3-4: congruence.
    - apply H in D.
      destruct D. subst.
      destruct (fbs_values (fbs_expr clock) env modules own_module id el (eff ++ x)) eqn:D2.
      destruct res0. 3-4: congruence.
      + inversion H0. apply IHel in D2. destruct D2. subst.
        exists (x ++ x0). rewrite <- app_assoc. auto.
        exact H.
      + inversion H0. subst. apply IHel in D2. destruct D2. rewrite <- app_assoc in H1.
        exists (x ++ x0). assumption.
        exact H.
    - inversion H0. subst. apply H in D. exact D.
Qed.

Lemma effect_extension_case_helper el :
forall {env modules own_module id0 eff id' res eff' vals clock},
(forall (env : Environment) (id : nat) (e : Expression)
                          (eff : SideEffectList) (id' : nat) (res : ValueSequence + Exception)
                          (eff' : SideEffectList),
                        fbs_expr clock env modules own_module id e eff = Result id' res eff' ->
                        exists l : list (SideEffectId * list Value), eff' = eff ++ l)
  ->
fbs_case el env modules own_module id0 eff vals (fbs_expr clock) = Result id' res eff'
->
exists l, eff' = eff ++ l.
Proof.
  induction el; intros.
  * simpl in H0. inversion H0. subst. exists []. rewrite app_nil_r. auto.
  * simpl in H0. destruct a, p. destruct (match_valuelist_to_patternlist vals l) eqn:D1.
    - destruct (fbs_expr clock (add_bindings (match_valuelist_bind_patternlist vals l) env) modules own_module id0 e0 eff) eqn:D2.
      destruct res0. destruct v. congruence. destruct v0. 2,4-5:congruence.
      destruct (((id =? id0) && list_eqb effect_eqb eff eff0)%bool) eqn:D3.
      2: congruence.
      + destruct v; try congruence. destruct l0; try congruence. 
        destruct ((s =? "true")%string).
        ** apply H in H0. destruct H0. eexists. exact H0.
        ** destruct (s =? "false")%string. 2: congruence.
           eapply IHel. exact H. exact H0.
      + congruence.
    - eapply IHel. exact H. exact H0.
Qed.

Theorem effect_extension_expr :
forall {clock env modules own_module id e eff id' res eff'},
  fbs_expr clock env modules own_module id e eff = Result id' res eff'
->
  exists l, eff' = eff ++ l.
Proof.
  induction clock; intros; inversion H. destruct e.
  2-6: inversion H; subst; exists []; rewrite app_nil_r; auto.
  * simpl in H. eapply effect_extension_exprlist_helper. 2: exact H.
    intros. apply IHclock in H0. exact H0.
  * destruct (get_value env (inl v)). inversion H1. auto. congruence.
  * destruct (get_value env (inr f)). inversion H1. auto. 
    destruct get_own_modfunc. inversion H1. auto. congruence.
  * destruct (fbs_expr clock env modules own_module id e2 eff) eqn:D1.
    destruct res0. destruct v. congruence. destruct v0. 2, 4-5: congruence.
    - apply IHclock in D1. destruct D1.
      destruct (fbs_expr clock env modules own_module id0 e1 eff0) eqn:D2.
      destruct res0. destruct v0. congruence. destruct v1. 2, 4-5: congruence.
      + apply IHclock in D2. destruct D2. subst. inversion H1. subst.
        exists (x ++ x0). rewrite app_assoc. auto.
      + apply IHclock in D2. destruct D2. subst. inversion H1. subst.
        exists (x ++ x0). rewrite app_assoc. auto.
    - apply IHclock in D1. destruct D1. inversion H1. subst. 
      exists x. auto.
  * destruct (fbs_values (fbs_expr clock) env modules own_module id l eff) eqn:D1.
    destruct res0. 3-4: congruence.
    - inversion H1. subst. eapply effect_extension_exprlist_helper in D1. destruct D1.
      exists x. subst. auto. intros. eapply IHclock. exact H0.
    - inversion H1. subst. eapply effect_extension_exprlist_helper in D1. destruct D1.
      exists x. subst. auto. intros. eapply IHclock. exact H0.
  * destruct (fbs_expr clock env modules own_module id e1 eff) eqn: D1; try congruence.
    destruct res0. destruct v; try congruence. destruct v0; try congruence.
    - destruct (fbs_expr clock env modules own_module id0 e2 eff0) eqn:D2; try congruence.
      destruct res0. destruct v0; try congruence. destruct v1; try congruence.
        -- destruct (fbs_values (fbs_expr clock) env modules own_module id1 l eff1) eqn:D; try congruence.
          destruct res0. destruct v; try congruence.
          + apply IHclock in D1. destruct D1. subst.
            apply IHclock in D2. destruct D2. subst.
            inversion H1. subst. eapply effect_extension_exprlist_helper in D. destruct D.
            exists  (x ++ x0 ++ x1 ). rewrite app_assoc. rewrite app_assoc.
            auto. intros; eapply IHclock; exact H0.
          + destruct l0. destruct v0.
            ++  apply IHclock in D1. destruct D1. subst.
                apply IHclock in D2. destruct D2. subst.
                inversion H1. subst. eapply effect_extension_exprlist_helper in D. destruct D.
                exists  (x ++ x0 ++ x1 ). rewrite app_assoc. rewrite app_assoc.
                auto. intros; eapply IHclock; exact H0.
            ++ destruct l0.
              +++ destruct get_modfunc. 
                +++++ apply IHclock in D1. destruct D1. subst.
                      apply IHclock in D2. destruct D2. subst.
                      apply IHclock in H1. destruct H1. subst.
                      eapply effect_extension_exprlist_helper in D. destruct D.
                      2: intros; eapply IHclock; exact H0.
                      exists  (x ++ x0  ++ x2 ++ x1).
                      rewrite app_assoc. rewrite app_assoc. rewrite app_assoc.
                      rewrite H0. reflexivity. 
                +++++ apply IHclock in D1. destruct D1. subst.
                      apply IHclock in D2. destruct D2. subst.
                      eapply effect_extension_exprlist_helper in D as D'.
                      destruct D'. 2: intros; eapply IHclock; exact H0.
                      subst. remember (snd (eval s s0 v1 (((eff ++ x) ++ x0) ++ x1))) as HELPER.
                      symmetry in HeqHELPER. apply eval_effect_extension_snd in HeqHELPER.
                      destruct HeqHELPER. subst.
                      inversion H1. subst. 
                      exists (x ++ x0 ++ x1 ++ x2 ).
                      rewrite app_assoc. rewrite app_assoc. rewrite app_assoc. auto.
              +++ apply IHclock in D1. destruct D1. subst.
                  apply IHclock in D2. destruct D2. subst.
                  inversion H1. subst. eapply effect_extension_exprlist_helper in D. destruct D.
                  exists  ( x0 ++ x1 ++ x2 ). rewrite app_assoc. rewrite app_assoc.
                  auto. intros; eapply IHclock; exact H0.

            ++ apply IHclock in D1. destruct D1. subst.
               apply IHclock in D2. destruct D2. subst.
               inversion H1. subst. eapply effect_extension_exprlist_helper in D. destruct D.
               exists  (x ++ x0 ++ x1 ). rewrite app_assoc. rewrite app_assoc.
               auto. intros; eapply IHclock; exact H0.
            ++ apply IHclock in D1. destruct D1. subst.
               apply IHclock in D2. destruct D2. subst.
               inversion H1. subst. eapply effect_extension_exprlist_helper in D. destruct D.
               exists  (x ++ x0 ++ x1 ). rewrite app_assoc. rewrite app_assoc.
               auto. intros; eapply IHclock; exact H0.
            ++ apply IHclock in D1. destruct D1. subst.
               apply IHclock in D2. destruct D2. subst.
               inversion H1. subst. eapply effect_extension_exprlist_helper in D. destruct D.
               exists  (x ++ x0 ++ x1 ). rewrite app_assoc. rewrite app_assoc.
               auto. intros; eapply IHclock; exact H0.
            ++ apply IHclock in D1. destruct D1. subst.
               apply IHclock in D2. destruct D2. subst.
               inversion H1. subst. eapply effect_extension_exprlist_helper in D. destruct D.
               exists  (x ++ x0 ++ x1 ). rewrite app_assoc. rewrite app_assoc.
               auto. intros; eapply IHclock; exact H0.
            ++ apply IHclock in D1. destruct D1. subst.
               apply IHclock in D2. destruct D2. subst.
               inversion H1. subst. eapply effect_extension_exprlist_helper in D. destruct D.
               exists  ( x0 ++ x1 ++ x2 ). rewrite app_assoc. rewrite app_assoc.
               auto. intros; eapply IHclock; exact H0.
       
          + apply IHclock in D1. destruct D1. subst.
            apply IHclock in D2. destruct D2. subst.
            inversion H1. subst. eapply effect_extension_exprlist_helper in D. destruct D.
            exists  (x ++ x0 ++ x1 ). rewrite app_assoc. rewrite app_assoc.
            auto. intros; eapply IHclock; exact H0.
          + apply IHclock in D1. destruct D1. subst.
            apply IHclock in D2. destruct D2. subst.
            inversion H1. subst. eapply effect_extension_exprlist_helper in D. destruct D.
            exists  (x ++ x0 ++ x1 ). rewrite app_assoc. rewrite app_assoc.
            auto. intros; eapply IHclock; exact H0.
          + apply IHclock in D1. destruct D1. subst.
            apply IHclock in D2. destruct D2. subst.
            inversion H1. subst. eapply effect_extension_exprlist_helper in D. destruct D.
            exists  (x ++ x0 ++ x1 ). rewrite app_assoc. rewrite app_assoc.
            auto. intros; eapply IHclock; exact H0.
          + apply IHclock in D1. destruct D1. subst.
            apply IHclock in D2. destruct D2. subst.
            inversion H1. subst. eapply effect_extension_exprlist_helper in D. destruct D.
            exists  (x ++ x0 ++ x1 ). rewrite app_assoc. rewrite app_assoc.
            auto. intros; eapply IHclock; exact H0.
          + apply IHclock in D1. destruct D1. subst.
            apply IHclock in D2. destruct D2. subst.
            inversion H1. subst. eapply effect_extension_exprlist_helper in D. destruct D.
            exists  (x ++ x0 ++ x1 ). rewrite app_assoc. rewrite app_assoc.
            auto. intros; eapply IHclock; exact H0.
        --  apply IHclock in D1. destruct D1. subst.
            apply IHclock in D2. destruct D2. subst.
            inversion H1. subst. 
            exists  (x ++ x0). rewrite app_assoc.  auto.
      -  apply IHclock in D1. destruct D1. subst.
         inversion H1. subst. 
         exists  (x).  auto.


  (* * destruct (fbs_values (fbs_expr clock) env modules id l eff) eqn:D1.
    destruct res0. 3-4: congruence.
    - (*inversion H1. subst.*) eapply effect_extension_exprlist_helper in D1 as D1'.
      destruct D1'. 2: intros; eapply IHclock; exact H0.
      subst. remember (snd (eval m f v (eff ++ x))) as HELPER.
      symmetry in HeqHELPER. apply eval_effect_extension_snd in HeqHELPER.
      destruct HeqHELPER. subst.
      destruct get_modfunc. destruct t. (*, f0, p.
*)        -- eapply IHclock in H1. inversion H1.  exists (x ++ x1). rewrite app_assoc. auto.
        -- inversion H1. subst. eapply effect_extension_exprlist_helper in D1. destruct D1.
        exists  (x ++ x0). rewrite app_assoc. auto. intros. eapply IHclock. exact H0.
 
    - inversion H1. subst. eapply effect_extension_exprlist_helper in D1. destruct D1.
      exists x. subst. auto. intros. eapply IHclock. exact H0. *)
  * destruct (fbs_values (fbs_expr clock) env modules own_module id l eff) eqn:D1.
    destruct res0. 3-4: congruence.
    - inversion H1. subst. eapply effect_extension_exprlist_helper in D1 as D1'.
      destruct D1'. 2: intros; eapply IHclock; exact H0.
      subst. remember (snd (primop_eval f v (eff ++ x))) as HELPER.
      symmetry in HeqHELPER. apply primop_eval_effect_extension_snd in HeqHELPER.
      destruct HeqHELPER. subst. exists (x ++ x0). rewrite app_assoc. auto.
    - inversion H1. subst. eapply effect_extension_exprlist_helper in D1. destruct D1.
      exists x. subst. auto. intros. eapply IHclock. exact H0.
  * destruct (fbs_expr clock env modules own_module id e eff) eqn:D1.
    destruct res0. destruct v. congruence. destruct v0. 2,4-5: congruence.
    - apply IHclock in D1. destruct D1. subst.
      destruct (fbs_values (fbs_expr clock) env modules own_module id0 l (eff ++ x)) eqn:D2.
      destruct res0. 3-4: congruence.
      + destruct v.
        3: destruct (length vl =? length v0).
        1-2, 4-7:
           apply effect_extension_exprlist_helper in D2; [ destruct D2; subst;
           inversion H1; exists (x ++ x0); rewrite app_assoc; auto | 
           intros; eapply IHclock; exact H0 ].
        apply effect_extension_exprlist_helper in D2. destruct D2; subst.
        apply IHclock in H1. destruct H1. subst.
        exists (x ++ x0 ++ x1). repeat rewrite app_assoc. auto.
        intros; eapply IHclock; exact H0.
      + apply effect_extension_exprlist_helper in D2; [ destruct D2; subst;
           inversion H1; exists (x ++ x0); rewrite app_assoc; auto | 
           intros; eapply IHclock; exact H0 ].
    - apply IHclock in D1. destruct D1. subst.
      inversion H1. exists x. auto.
  * destruct (fbs_expr clock env modules own_module id e eff) eqn:D1.
    destruct res0. 3-4: congruence.
    - apply IHclock in D1. destruct D1. subst.
      apply effect_extension_case_helper in H1. destruct H1. subst.
      exists (x ++ x0). rewrite app_assoc. auto.
      intros; eapply IHclock; exact H0.
    - inversion H1. apply IHclock in D1. destruct D1. subst.
      exists x. auto.
  * destruct (fbs_expr clock env modules own_module id e1 eff) eqn:D1.
    destruct res0. destruct (Datatypes.length v =? Datatypes.length l).
    2, 4-5: congruence.
    - apply IHclock in D1. destruct D1.
      apply IHclock in H1. destruct H1. subst.
      exists (x ++ x0). rewrite app_assoc. auto.
    - apply IHclock in D1. destruct D1. inversion H1. subst. 
      exists x. auto.
  * destruct (fbs_expr clock env modules own_module id e1 eff) eqn:D1.
    destruct res0. destruct v. congruence. destruct v0. 2, 4-5: congruence.
    - apply IHclock in D1. destruct D1.
      apply IHclock in H1. destruct H1. subst.
      exists (x ++ x0). rewrite app_assoc. auto.
    - apply IHclock in D1. destruct D1. inversion H1. subst. 
      exists x. auto.
  * apply IHclock in H1. exact H1.
  * destruct (fbs_values (fbs_expr clock) env modules own_module id (make_map_exps l) eff) eqn:D1.
    destruct res0. 3-4: congruence.
    - inversion H. subst. eapply effect_extension_exprlist_helper in D1. destruct D1.
      destruct (make_map_vals_inverse v). 2: congruence. destruct p. inversion H1.
      exists x. subst. auto. intros. eapply IHclock. exact H0.
    - inversion H1. subst. eapply effect_extension_exprlist_helper in D1. destruct D1.
      exists x. subst. auto. intros. eapply IHclock. exact H0.
  * destruct (fbs_expr clock env modules own_module id e1 eff) eqn:D1.
    destruct res0. destruct (Datatypes.length v =? Datatypes.length vl1).
    2, 4-5: congruence.
    - apply IHclock in D1. destruct D1.
      apply IHclock in H1. destruct H1. subst.
      exists (x ++ x0). rewrite app_assoc. auto.
    - apply IHclock in D1. destruct D1.
      apply IHclock in H1. destruct H1. subst.
      exists (x ++ x0). rewrite app_assoc. auto.
Qed.

Theorem effect_extension_exprlist el :
forall {env modules own_module id0 eff id' res eff' clock},
fbs_values (fbs_expr clock) env modules own_module id0 el eff = Result id' res eff'
->
exists l, eff' = eff ++ l.
Proof.
  intros. eapply effect_extension_exprlist_helper in H. assumption.
  intros. eapply effect_extension_expr. exact H0.
Qed.

Theorem effect_extension_case l :
forall env modules own_module id0 eff v id' res eff' clock,
fbs_case l env modules own_module id0 eff v (fbs_expr clock) = Result id' res eff'
->
exists l', eff' = eff ++ l'.
Proof.
  intros.
  eapply effect_extension_case_helper. 2: exact H.
  intros. eapply effect_extension_expr. exact H0.
Qed.

Lemma effect_irrelevant_exprlist_helper el :
  forall env modules own_module id eff id' res eff' clock,
  (forall (env : Environment) (id : nat) (e : Expression) 
            (eff : SideEffectList) (id' : nat) (res : ValueSequence + Exception)
            (eff' : list (SideEffectId * list Value)),
          fbs_expr clock env modules own_module id e eff = Result id' res (eff ++ eff') ->
          forall eff0 : SideEffectList,
          fbs_expr clock env modules own_module id e eff0 = Result id' res (eff0 ++ eff'))
  ->
  fbs_values (fbs_expr clock) env modules own_module id el eff = Result id' res (eff ++ eff')
->
  forall eff0, fbs_values (fbs_expr clock) env modules own_module id el eff0 = Result id' res (eff0 ++ eff').
Proof.
  induction el; intros.
  * simpl in *. inversion H0. rewrite <- app_nil_r in H4 at 1. apply app_inv_head in H4.
    subst. rewrite app_nil_r. reflexivity.
  * simpl in H0. simpl. destruct (fbs_expr clock env modules own_module id a eff) eqn:D1.
    destruct res0. destruct v. congruence. destruct v0. 2: congruence.
    3-4: congruence.
    - remember D1 as D1'. clear HeqD1'. pose (effect_extension_expr D1).
      destruct e. subst.
      apply H with (eff0 := eff0) in D1'. rewrite D1'.
      destruct (fbs_values (fbs_expr clock) env modules own_module id0 el (eff ++ x)) eqn:D2.
      destruct res0. 3-4: congruence.
      + inversion H0. subst.
        pose (P := effect_extension_exprlist _ D2). destruct P.
        rewrite <- app_assoc in H1. apply app_inv_head in H1. subst.
        rewrite app_assoc in D2.
        epose (IHel env modules own_module id0 (eff ++ x) id' _ _ clock H D2 (eff0 ++ x)).
        rewrite e. rewrite app_assoc. reflexivity.
      + inversion H0.
        pose (P := effect_extension_exprlist _ D2). destruct P.
        rewrite <- app_assoc in H1. subst. apply app_inv_head in H1. subst.
        rewrite app_assoc in D2.
        epose (IHel env modules own_module id0 (eff ++ x) id' _ _ clock H D2 (eff0 ++ x)).
        rewrite e0. rewrite app_assoc. reflexivity.
    - inversion H0. subst. eapply H in D1. rewrite D1. reflexivity.
Qed.

Lemma effect_irrelevant_case_helper l :
forall env modules own_module id0 eff v id' res eff' clock,
fbs_case l env modules own_module id0 eff v (fbs_expr clock) = Result id' res (eff ++ eff')
->
(forall (env : Environment) (id : nat) (e : Expression) 
            (eff : SideEffectList) (id' : nat) (res : ValueSequence + Exception)
            (eff' : list (SideEffectId * list Value)),
          fbs_expr clock env modules own_module id e eff = Result id' res (eff ++ eff') ->
          forall eff0 : SideEffectList,
          fbs_expr clock env modules own_module id e eff0 = Result id' res (eff0 ++ eff'))
->
forall eff0, fbs_case l env modules own_module id0 eff0 v (fbs_expr clock) = Result id' res (eff0 ++ eff').
Proof.
  induction l; intros.
  * simpl in *. inversion H. rewrite <- app_nil_r in H4 at 1. apply app_inv_head in H4.
    subst. rewrite app_nil_r. reflexivity.
  * simpl in *. destruct a, p.
    destruct (match_valuelist_to_patternlist v l0).
    - destruct (fbs_expr clock (add_bindings (match_valuelist_bind_patternlist v l0) env) modules own_module id0 e0 eff) eqn:D1.
      destruct res0. destruct v0. congruence. destruct v1. 2: congruence.
      2-4: congruence. remember D1 as D1'. clear HeqD1'.
      apply effect_extension_expr in D1. destruct D1. subst.
      eapply H0 in D1'. rewrite D1'.
      destruct (((id =? id0) && list_eqb effect_eqb eff (eff ++ x))%bool) eqn:D2.
      + apply andb_prop in D2. destruct D2.
        apply Nat.eqb_eq in H1. apply effect_list_eqb_eq in H2.
        rewrite <- app_nil_r in H2 at 1. apply app_inv_head in H2. subst.
        rewrite app_nil_r. rewrite Nat.eqb_refl, effect_list_eqb_refl. simpl.
        destruct v0; try congruence. destruct l1; try congruence.
        destruct (s =? "true")%string.
        ** eapply H0 in H. exact H.
        ** destruct (s =? "false")%string. 2: congruence.
           eapply IHl. exact H.
           intros. eapply H0. exact H1.
      + congruence.
    - eapply IHl. exact H. intros. eapply H0. exact H1.
Qed.

Theorem effect_irrelevant_expr :
(forall {clock env modules own_module id e eff id' res eff'},
  fbs_expr clock env modules own_module id e eff = Result id' res (eff ++ eff')
->
forall eff0,
  fbs_expr clock env modules own_module id e eff0 = Result id' res (eff0 ++ eff')).
Proof.
  induction clock; intros.
  * simpl in H. inversion H.
  * destruct e; subst.
    - simpl. simpl in H. eapply effect_irrelevant_exprlist_helper.
      2: exact H. intros. eapply IHclock. exact H0.
    - simpl in H; inversion H. simpl. rewrite <- app_nil_r in H3 at 1.
      apply app_inv_head in H3. subst. rewrite app_nil_r. reflexivity.
    - simpl in H; inversion H. simpl. rewrite <- app_nil_r in H3 at 1.
      apply app_inv_head in H3. subst. rewrite app_nil_r. reflexivity.
    - simpl in H. simpl. destruct (get_value env (inl v)). 2: congruence.
      inversion H. rewrite <- app_nil_r in H3 at 1.
      apply app_inv_head in H3. subst. rewrite app_nil_r. reflexivity.
    - simpl in H. simpl. destruct (get_value env (inr f)). 
      inversion H. rewrite <- app_nil_r in H3 at 1.
      apply app_inv_head in H3. subst. rewrite app_nil_r. reflexivity.
      destruct get_own_modfunc. inversion H. rewrite <- app_nil_r in H3 at 1.
      apply app_inv_head in H3. subst. rewrite app_nil_r. reflexivity. congruence.
    - simpl in H; inversion H. simpl. rewrite <- app_nil_r in H3 at 1.
      apply app_inv_head in H3. subst. rewrite app_nil_r. reflexivity.
    - simpl in H. simpl.
      destruct (fbs_expr clock env modules own_module id e2 eff) eqn:D1.
      destruct res0. destruct v. congruence. destruct v0. 2: congruence.
      3-4: congruence.
      + remember D1 as D1'. clear HeqD1'.
        epose (effect_extension_expr D1). destruct e. subst.
        apply IHclock with (eff0 := eff0) in D1'.
        destruct (fbs_expr clock env modules own_module id0 e1 (eff ++ x)) eqn:D2.
        destruct res0. destruct v0. congruence. destruct v1. 2: congruence.
        3-4: congruence.
        ** remember D2 as D2'. clear HeqD2'.
           epose (effect_extension_expr D2). destruct e. subst.
           apply IHclock with (eff0 := eff0 ++ x) in D2'.
           rewrite D1', D2'. inversion H. rewrite <- app_assoc in H3.
           apply app_inv_head in H3. subst. rewrite <- app_assoc. reflexivity.
        ** remember D2 as D2'. clear HeqD2'.
           epose (effect_extension_expr D2). destruct e0. subst.
           apply IHclock with (eff0 := eff0 ++ x) in D2'.
           rewrite D1', D2'. inversion H. rewrite <- app_assoc in H3.
           apply app_inv_head in H3. subst. rewrite <- app_assoc. reflexivity.
      + remember D1 as D1'. clear HeqD1'.
        epose (effect_extension_expr D1). destruct e0. subst.
        apply IHclock with (eff0 := eff0) in D1'.
        rewrite D1'. inversion H. apply app_inv_head in H3. subst. reflexivity.
    - simpl. simpl in H. destruct (fbs_values (fbs_expr clock) env modules own_module id l eff) eqn:D1.
      destruct res0. 3-4: congruence.
      + inversion H. subst. eapply effect_irrelevant_exprlist_helper in D1.
        rewrite D1. reflexivity. intros. eapply IHclock in H0. exact H0.
      + inversion H. subst. eapply effect_irrelevant_exprlist_helper in D1.
        rewrite D1. reflexivity. intros. eapply IHclock in H0. exact H0.
    - simpl. simpl in H.
      destruct (fbs_expr clock env modules own_module id e1 eff ) eqn:D1; try congruence.
      destruct res0. destruct v; try congruence. destruct v0; try congruence.
      + remember D1 as D1'. clear HeqD1'.
        eapply effect_extension_expr in D1. destruct D1. subst.
        eapply IHclock in D1'. rewrite D1'.
        destruct (fbs_expr clock env modules own_module id0 e2 (eff ++ x)) eqn:D2; try congruence.
        destruct res0. destruct v0; try congruence. destruct v1; try congruence.
        ++ remember D2 as D2'. clear HeqD2'.
           eapply effect_extension_expr in D2. destruct D2. subst.
           eapply IHclock in D2'. rewrite D2'.
           destruct (fbs_values (fbs_expr clock) env modules own_module id1 l ((eff ++ x) ++ x0)) eqn:D; try congruence.
           destruct res0. destruct v.
           
           ** remember D as D'. clear HeqD'.
              eapply effect_extension_exprlist  in D. destruct D. subst.
              eapply effect_irrelevant_exprlist_helper in D'.
              rewrite D'.
              inversion H; subst; rewrite <- app_assoc in H3; rewrite <- app_assoc in H3;
              apply app_inv_head in H3; subst; rewrite app_assoc; rewrite app_assoc; reflexivity.
              intros; eapply IHclock; exact H0.
          ** remember D as D'. clear HeqD'.
             eapply effect_extension_exprlist  in D. destruct D. subst.
             eapply effect_irrelevant_exprlist_helper in D'.
             rewrite D'.
             2: intros; eapply IHclock; exact H0.
             destruct l0. destruct v0.
              1,3,4,5,6,7: inversion H; subst; rewrite <- app_assoc in H3; rewrite <- app_assoc in H3;
                  apply app_inv_head in H3; subst; rewrite app_assoc; rewrite app_assoc; reflexivity.
              *** destruct l0.
                  destruct get_modfunc.
                    -- remember H as H'. clear HeqH'.
                      eapply effect_extension_expr in H. destruct H.
                      rewrite <- app_assoc in H. rewrite <- app_assoc in H. rewrite <- app_assoc in H.
                      apply app_inv_head in H. subst.
                      replace (eff ++ x ++ x0 ++ x1 ++ x2) with ((((eff ++ x) ++ x0) ++ x1) ++ x2) in H'.
                       apply IHclock with (eff0 := ((((eff0 ++ x) ++ x0) ++ x1))) in H'. 
                      repeat rewrite <- app_assoc in *. exact H'.
                      repeat rewrite <- app_assoc in *. auto.
                    -- remember H as H'. clear HeqH'.
                       inversion H. subst.
                       eapply eval_effect_extension_snd in H3 as [l' P].
                       rewrite <- app_assoc in P. rewrite <- app_assoc in P. rewrite <- app_assoc in P.
                       apply app_inv_head in P. subst.
                       inversion H. 
                       rewrite app_assoc in H1. rewrite app_assoc in H1. rewrite app_assoc in H1.
                       epose proof (P := @eval_effect_irrelevant_snd _ _ _ (((eff ++ x) ++ x0) ++ x1) l' H1 (((eff0 ++ x) ++ x0) ++ x1)).
                       rewrite P. rewrite <- app_assoc. rewrite <- app_assoc. rewrite <- app_assoc. rewrite <- app_assoc. rewrite <- app_assoc.
                      erewrite eval_effect_irrelevant_fst. reflexivity.
                    -- inversion H; subst; rewrite <- app_assoc in H3; rewrite <- app_assoc in H3;
                       apply app_inv_head in H3; subst; rewrite app_assoc; rewrite app_assoc; reflexivity.
          ** remember D as D'. clear HeqD'.
              eapply effect_extension_exprlist  in D. destruct D. subst.
              eapply effect_irrelevant_exprlist_helper in D'.
              rewrite D'.
              inversion H; subst; rewrite <- app_assoc in H3; rewrite <- app_assoc in H3;
              apply app_inv_head in H3; subst; rewrite app_assoc; rewrite app_assoc; reflexivity.
              intros; eapply IHclock; exact H0.
          ** remember D as D'. clear HeqD'.
              eapply effect_extension_exprlist  in D. destruct D. subst.
              eapply effect_irrelevant_exprlist_helper in D'.
              rewrite D'.
              inversion H; subst; rewrite <- app_assoc in H3; rewrite <- app_assoc in H3;
              apply app_inv_head in H3; subst; rewrite app_assoc; rewrite app_assoc; reflexivity.
              intros; eapply IHclock; exact H0.
          ** remember D as D'. clear HeqD'.
              eapply effect_extension_exprlist  in D. destruct D. subst.
              eapply effect_irrelevant_exprlist_helper in D'.
              rewrite D'.
              inversion H; subst; rewrite <- app_assoc in H3; rewrite <- app_assoc in H3;
              apply app_inv_head in H3; subst; rewrite app_assoc; rewrite app_assoc; reflexivity.
              intros; eapply IHclock; exact H0.
          ** remember D as D'. clear HeqD'.
              eapply effect_extension_exprlist  in D. destruct D. subst.
              eapply effect_irrelevant_exprlist_helper in D'.
              rewrite D'.
              inversion H; subst; rewrite <- app_assoc in H3; rewrite <- app_assoc in H3;
              apply app_inv_head in H3; subst; rewrite app_assoc; rewrite app_assoc; reflexivity.
              intros; eapply IHclock; exact H0.
          ** remember D as D'. clear HeqD'.
              eapply effect_extension_exprlist  in D. destruct D. subst.
              eapply effect_irrelevant_exprlist_helper in D'.
              rewrite D'.
              inversion H; subst; rewrite <- app_assoc in H3; rewrite <- app_assoc in H3;
              apply app_inv_head in H3; subst; rewrite app_assoc; rewrite app_assoc; reflexivity.
              intros; eapply IHclock; exact H0.
        ++  remember D2 as D2'. clear HeqD2'.
            eapply effect_extension_expr in D2. destruct D2. subst.
            eapply IHclock in D2'. rewrite D2'.
            inversion H; subst; rewrite <- app_assoc in H3;
            apply app_inv_head in H3; subst; rewrite app_assoc; reflexivity.
      + remember D1 as D1'; clear HeqD1';
        epose (effect_extension_expr D1); destruct e0; subst;
        apply IHclock with (eff0 := eff0) in D1';
        rewrite D1'; inversion H; subst;
        apply app_inv_head in H3; subst; reflexivity.

    - simpl. simpl in H. destruct (fbs_values (fbs_expr clock) env modules own_module id l eff) eqn:D1.
      destruct res0. 3-4: congruence.
      + inversion H. subst. remember D1 as D1'. clear HeqD1'.
        eapply effect_extension_exprlist in D1. destruct D1. subst.
        eapply effect_irrelevant_exprlist_helper in D1'. rewrite D1'.
        remember H3 as H3'. clear HeqH3'.
        eapply primop_eval_effect_extension_snd in H3. destruct H3.
        rewrite <- app_assoc in H0. apply app_inv_head in H0. subst.
        rewrite app_assoc in H3'.
        epose (P := @primop_eval_effect_irrelevant_snd _ _ (eff ++ x) x0 H3' (eff0 ++ x)).
        rewrite P. rewrite <- app_assoc. erewrite primop_eval_effect_irrelevant_fst. reflexivity.
        intros. eapply IHclock. exact H0.
      + inversion H. subst.
        eapply effect_irrelevant_exprlist_helper in D1. rewrite D1. reflexivity.
        intros. eapply IHclock. exact H0.
    - simpl. simpl in H. destruct (fbs_expr clock env modules own_module id e eff) eqn:D1.
      destruct res0. destruct v. congruence. destruct v0. 2: congruence. 3-4: congruence.
      + remember D1 as D1'. clear HeqD1'.
        eapply effect_extension_expr in D1. destruct D1. subst.
        eapply IHclock in D1'. rewrite D1'.
        (* destruct res0. 3-4: congruence. *)
        destruct (fbs_values (fbs_expr clock) env modules own_module id0 l (eff ++ x)) eqn:D2; try congruence.
        ** remember D2 as D2'. clear HeqD2'.
           eapply effect_extension_exprlist in D2. destruct D2. subst.
           eapply effect_irrelevant_exprlist_helper in D2'. rewrite D2'.
           destruct res0.
           destruct v.
           1-2, 4-6: inversion H; subst; rewrite <- app_assoc in H3;
                     apply app_inv_head in H3; subst; rewrite app_assoc; reflexivity.
           -- destruct (length vl =? length v0) eqn:D3.
              ++ rewrite <- app_assoc in H. remember H as H'. clear HeqH'.
                 eapply effect_extension_expr in H. destruct H.
                 rewrite <- app_assoc, <- app_assoc in H. apply app_inv_head in H. subst.
                 replace (eff ++ x ++ x0 ++ x1) with ((eff ++ x ++ x0) ++ x1) in H'.
                 apply IHclock with (eff0 := eff0 ++ x ++ x0) in H'.
                 repeat rewrite <- app_assoc in *. exact H'.
                 repeat rewrite <- app_assoc in *. auto.
              ++ inversion H; subst; rewrite <- app_assoc in H3;
                 apply app_inv_head in H3; subst; rewrite app_assoc; reflexivity.
           --  inversion H. subst. rewrite <- app_assoc in H3.
               apply app_inv_head in H3. subst. rewrite app_assoc. reflexivity.
           --  intros. eapply IHclock. exact H0.
        (* ** inversion H. subst. remember D2 as D2'. clear HeqD2'.
           eapply effect_extension_exprlist in D2. destruct D2.
           rewrite <- app_assoc in H0. apply app_inv_head in H0. subst.
           rewrite app_assoc in D2'.
           eapply effect_irrelevant_exprlist_helper in D2'. rewrite D2'.
           rewrite <- app_assoc. reflexivity.
           intros. eapply IHclock. exact H0. *)
      + inversion H. subst. eapply IHclock in D1. rewrite D1.
        reflexivity.
    - simpl in H. simpl. destruct (fbs_expr clock env modules own_module id e eff) eqn:D1.
      destruct res0. 3-4: congruence.
      + remember D1 as D1'. clear HeqD1'.
        eapply effect_extension_expr in D1. destruct D1. subst.
        eapply IHclock in D1'. rewrite D1'.
        remember H as H'. clear HeqH'. eapply effect_extension_case in H. destruct H.
        rewrite <- app_assoc in H. apply app_inv_head in H. subst.
        rewrite app_assoc in H'. eapply effect_irrelevant_case_helper in H'.
        rewrite app_assoc. exact H'.
        intros. eapply IHclock. exact H.
      + inversion H. subst. eapply IHclock in D1.
        rewrite D1. reflexivity.
    - simpl in H. simpl. destruct (fbs_expr clock env modules own_module id e1 eff) eqn:D1.
      destruct res0. 3-4: congruence.
      + remember D1 as D1'. clear HeqD1'.
        eapply effect_extension_expr in D1. destruct D1. subst.
        eapply IHclock in D1'. rewrite D1'.
        destruct (length v =? length l). 2: congruence.
        remember H as H'. clear HeqH'.
        eapply effect_extension_expr in H. destruct H.
        rewrite <- app_assoc in H. apply app_inv_head in H. subst.
        rewrite app_assoc in H'.
        eapply IHclock in H'. rewrite H'. rewrite app_assoc.
        reflexivity.
      + inversion H. subst. remember D1 as D1'. clear HeqD1'.
        eapply effect_extension_expr in D1. destruct D1. subst.
        eapply IHclock in D1'. rewrite D1'. reflexivity.
    - simpl in H. simpl. destruct (fbs_expr clock env modules own_module id e1 eff) eqn:D1.
      destruct res0. destruct v. congruence. destruct v0. 2: congruence. 3-4: congruence.
      + remember D1 as D1'. clear HeqD1'.
        eapply effect_extension_expr in D1. destruct D1. subst.
        eapply IHclock in D1'. rewrite D1'.
        remember H as H'. clear HeqH'.
        eapply effect_extension_expr in H. destruct H.
        rewrite <- app_assoc in H. apply app_inv_head in H. subst.
        rewrite app_assoc in H'.
        eapply IHclock in H'. rewrite H'. rewrite app_assoc.
        reflexivity.
      + inversion H. subst. remember D1 as D1'. clear HeqD1'.
        eapply effect_extension_expr in D1. destruct D1. subst.
        eapply IHclock in D1'. rewrite D1'. reflexivity.
    - eapply IHclock. exact H.
    - simpl. simpl in H.
      destruct (fbs_values (fbs_expr clock) env modules own_module id (make_map_exps l) eff) eqn:D1.
      destruct res0. 3-4: congruence.
      + destruct (make_map_vals_inverse v) eqn:D2. 2: congruence. destruct p.
        remember D1 as D1'. clear HeqD1'.
        eapply effect_extension_exprlist in D1. destruct D1. subst.
        eapply effect_irrelevant_exprlist_helper in D1'. rewrite D1'. rewrite D2.
        inversion H. subst. apply app_inv_head in H3. subst. reflexivity.
        intros. eapply IHclock. exact H0.
      + inversion H. subst.
        eapply effect_irrelevant_exprlist_helper in D1. rewrite D1. reflexivity.
        intros. eapply IHclock. exact H0.
    - simpl in H. simpl. destruct (fbs_expr clock env modules own_module id e1 eff) eqn:D1.
      destruct res0. 3-4: congruence.
      + remember D1 as D1'. clear HeqD1'.
        eapply effect_extension_expr in D1. destruct D1. subst.
        eapply IHclock in D1'. rewrite D1'.
        remember H as H'. clear HeqH'. destruct (length v =? length vl1). 2: congruence.
        eapply effect_extension_expr in H. destruct H.
        rewrite <- app_assoc in H. apply app_inv_head in H. subst.
        rewrite app_assoc in H'.
        eapply IHclock in H'. rewrite H'. rewrite app_assoc.
        reflexivity.
      + remember D1 as D1'. clear HeqD1'.
        eapply effect_extension_expr in D1. destruct D1. subst.
        eapply IHclock in D1'. rewrite D1'.
        remember H as H'. clear HeqH'.
        eapply effect_extension_expr in H. destruct H.
        rewrite <- app_assoc in H. apply app_inv_head in H. subst.
        rewrite app_assoc in H'.
        eapply IHclock in H'. rewrite H'. rewrite app_assoc.
        reflexivity.
Qed.

Theorem effect_irrelevant_exprlist {el} :
  forall {env modules own_module id eff id' res clock eff'},
  fbs_values (fbs_expr clock) env modules own_module id el eff = Result id' res (eff ++ eff')
->
  forall eff0, fbs_values (fbs_expr clock) env modules own_module id el eff0 = Result id' res (eff0 ++ eff').
Proof.
  intros. eapply effect_irrelevant_exprlist_helper. 2: exact H.
  intros. eapply effect_irrelevant_expr. exact H0.
Qed.

Theorem effect_irrelevant_case {l} :
forall {env modules own_module id0 eff v id' res eff' clock},
  fbs_case l env modules own_module id0 eff v (fbs_expr clock) = Result id' res (eff ++ eff')
->
  forall eff0, fbs_case l env modules own_module id0 eff0 v (fbs_expr clock) = Result id' res (eff0 ++ eff').
Proof.
  intros. eapply effect_irrelevant_case_helper. exact H.
  intros. eapply effect_irrelevant_expr. exact H0.
Qed.

End helpers.

Section equivalence_relation.

Theorem weakly_equivalent_expr_refl (P : list ErlModule -> Prop) {e} :
  weakly_equivalent_expr P e e.
Proof.
  unfold weakly_equivalent_expr. split; intros.
  * exists eff'. split. exact H0. apply Permutation_refl.
  * exists eff'. split. exact H0. apply Permutation_refl.
Qed.

Theorem weakly_equivalent_expr_sym (P : list ErlModule -> Prop ) {e1 e2} :
  weakly_equivalent_expr P e1 e2
->
  weakly_equivalent_expr P e2 e1.
Proof.
  unfold weakly_equivalent_expr. split; intros.
  * destruct H. apply H2 in H1. exact H1. auto.
  * destruct H. apply H in H1. exact H1. auto.
Qed.

Theorem weakly_equivalent_expr_trans (P : list ErlModule -> Prop ) {e1 e2 e3} :
  weakly_equivalent_expr P e1 e2 -> weakly_equivalent_expr P e2 e3
->
  weakly_equivalent_expr P e1 e3.
Proof.
  unfold weakly_equivalent_expr. split; intros env modules own_module eff res eff' id1 id2 F H1;
  destruct H, H0.
  * apply H in H1. destruct H1, H1. apply H0 in H1. destruct H1, H1. eexists.
    split. exact H1. eapply Permutation_trans. exact H4. exact H5. all : auto.
  * apply H3 in H1. destruct H1, H1. apply H2 in H1. destruct H1, H1. eexists.
    split. exact H1. eapply Permutation_trans. exact H4. exact H5. all : auto.
Qed.

Theorem weakly_equivalent_exprlist_refl (P : list ErlModule -> Prop ) {l} :
  weakly_equivalent_exprlist P l l.
Proof.
  unfold weakly_equivalent_exprlist. split; intros env modules own_module eff res eff' id1 id2 F H.
  * exists eff'. split. exact H. apply Permutation_refl.
  * exists eff'. split. exact H. apply Permutation_refl.
Qed.

Theorem weakly_equivalent_exprlist_sym (P : list ErlModule -> Prop ) {l1 l2} :
  weakly_equivalent_exprlist P l1 l2
->
  weakly_equivalent_exprlist P l2 l1.
Proof.
  unfold weakly_equivalent_exprlist. split; intros env own_module modules eff res eff' id1 id2 F H0.
  * destruct H. apply H1 in H0. exact H0. auto.
  * destruct H. apply H in H0. exact H0. auto.
Qed.

Theorem weakly_equivalent_exprlist_trans (P : list ErlModule -> Prop ) {l1 l2 l3} :
  weakly_equivalent_exprlist P l1 l2 -> weakly_equivalent_exprlist P l2 l3
->
  weakly_equivalent_exprlist P l1 l3.
Proof.
  unfold weakly_equivalent_exprlist. split; intros env modules own_module eff res eff' id1 id2 F H1;
  destruct H, H0.
  * apply H in H1. destruct H1, H1. apply H0 in H1. destruct H1, H1. eexists.
    split. exact H1. eapply Permutation_trans. exact H4. exact H5. all : auto.
  * apply H3 in H1. destruct H1, H1. apply H2 in H1. destruct H1, H1. eexists.
    split. exact H1. eapply Permutation_trans. exact H4. exact H5. all : auto.
Qed.

Theorem weakly_equivalent_case_refl (P : list ErlModule -> Prop ) {l} :
  weakly_equivalent_case P l l.
Proof.
  unfold weakly_equivalent_case. split; intros env modules own_module eff res eff' id1 id2 vals F H.
  * exists eff'. split. exact H. apply Permutation_refl.
  * exists eff'. split. exact H. apply Permutation_refl.
Qed.

Theorem weakly_equivalent_case_sym (P : list ErlModule -> Prop ) {l1 l2} :
  weakly_equivalent_case P l1 l2
->
  weakly_equivalent_case P l2 l1.
Proof.
  unfold weakly_equivalent_case. split; intros env modules own_module eff res eff' id1 id2 vals F H0.
  * destruct H. apply H1 in H0. exact H0. auto.
  * destruct H. apply H in H0. exact H0. auto.
Qed.

Theorem weakly_equivalent_case_trans (P : list ErlModule -> Prop ) {l1 l2 l3} :
  weakly_equivalent_case P l1 l2 -> weakly_equivalent_case P l2 l3
->
  weakly_equivalent_case P l1 l3.
Proof.
  unfold weakly_equivalent_case. split; intros env modules own_module eff res eff' id1 id2 vals F H1;
  destruct H, H0.
  * apply H in H1. destruct H1, H1. apply H0 in H1. destruct H1, H1. eexists.
    split. exact H1. eapply Permutation_trans. exact H4. exact H5. all : auto.
  * apply H3 in H1. destruct H1, H1. apply H2 in H1. destruct H1, H1. eexists.
    split. exact H1. eapply Permutation_trans. exact H4. exact H5. all : auto.
Qed.

End equivalence_relation.

Section congruence.

Theorem ECons_weak_congr (P : list ErlModule -> Prop ) hd tl : forall hd' tl',
  weakly_equivalent_expr P hd hd' -> weakly_equivalent_expr P tl tl'
->
  weakly_equivalent_expr P (ECons hd tl) (ECons hd' tl').
Proof.
  assert (A : forall hd hd' tl tl' env modules own_module id eff id' res eff', P modules ->
    weakly_equivalent_expr P hd hd' -> weakly_equivalent_expr P tl tl' ->
    (exists clock, fbs_expr clock env modules own_module id (ECons hd tl) eff = Result id' res eff')
  ->
    (exists eff'', (exists clock, fbs_expr clock env modules own_module id (ECons hd' tl') eff = Result id' res eff'') /\ Permutation eff' eff'')
  ). {
    intros hd0 hd' tl0 tl' env modules own_module id eff id' res eff' F H H0 H1.
    unfold weakly_equivalent_expr in H, H0. destruct H, H0. destruct H1; subst.
    destruct x; inversion H1. destruct (fbs_expr x env modules own_module id tl0 eff) eqn:D1.
    destruct res0. destruct v. congruence. destruct v0. 2,4-5: congruence.
    * apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
      apply ex_intro with (x := x), H0 in D1. destruct D1, H4, H4.
      apply effect_extension_expr in H4 as A'. destruct A'. subst.
      destruct (fbs_expr x env modules own_module id0 hd0 (eff ++ x0)) eqn:D2.
      destruct res0. destruct v0. congruence. destruct v1. 2,4-5: congruence.
      - inversion H5. subst.
        apply effect_extension_expr in D2 as D2'. destruct D2'. subst.
        apply ex_intro with (x := x), H in D2. destruct D2, H7, H7.
        apply effect_extension_expr in H7 as A'. destruct A'. subst.
        apply effect_irrelevant_expr with (eff0 := eff ++ x3) in H7.
        exists ((eff ++ x3) ++ x6). split.
        + exists (S (x2 + x5)). simpl.
          erewrite (bigger_clock_expr _ _ H4), (bigger_clock_expr _ _ H7). auto.
        + perm_solver.
        + auto.
      - apply effect_extension_expr in D2 as D2'. destruct D2'. subst.
        apply ex_intro with (x := x), H in D2. destruct D2, H7, H7.
        apply effect_extension_expr in H7 as A'. destruct A'. subst.
        apply effect_irrelevant_expr with (eff0 := eff ++ x3) in H7.
        inversion H5. subst.
        exists ((eff ++ x3) ++ x6). split.
        + exists (S (x2 + x5)). simpl.
          erewrite (bigger_clock_expr _ _ H4), (bigger_clock_expr _ _ H7). auto.
        + perm_solver.
        + auto.
      - auto.
    * apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
      apply ex_intro with (x := x), H0 in D1. destruct D1, H4, H4.
      apply effect_extension_expr in H4 as A'. destruct A'. subst.
      inversion H5. subst.
      exists (eff ++ x3). split.
      - exists (S x2). simpl. rewrite H4. auto.
      - perm_solver.
      - auto.
  }
  split; intros env modules own_module eff res eff' id1 id2 F H1.
  * eapply A. auto. exact H. exact H0. exact H1.
  * eapply A. auto. exact (weakly_equivalent_expr_sym P H). exact (weakly_equivalent_expr_sym P H0). exact H1.
Unshelve. all:lia.
Qed.


Theorem ETuple_weak_congr (P : list ErlModule -> Prop ) (l : list Expression) : forall (l' : list Expression),
  weakly_equivalent_exprlist P l l'
->
  weakly_equivalent_expr P (ETuple l) (ETuple l').
Proof.
  assert (A : forall (l l' : list Expression) env own_module modules id eff id' res eff', P modules ->
      weakly_equivalent_exprlist P l l' ->
      (exists clock, fbs_expr clock env modules own_module id (ETuple l) eff = Result id' res eff')
    ->
      exists eff'', (exists clock, fbs_expr clock env modules own_module id (ETuple l') eff = Result id' res eff'') /\ Permutation eff' eff''). 
  {
    intros l0 l' env modules own_module id eff id' res eff' F H H0.
    destruct H0, x.
    inversion H0.
    simpl in H0. destruct (fbs_values (fbs_expr x) env own_module modules id l0 eff) eqn:D1.
    destruct res0. 3-4: congruence.
    * inversion H0. subst.
      apply ex_intro with (x := x), H in D1. destruct D1, H1, H1.
      exists x0. split. exists (S x1). simpl. rewrite H1. all : auto.
    * inversion H0. subst.
      apply ex_intro with (x := x), H in D1. destruct D1, H1, H1.
      exists x0. split. exists (S x1). simpl. rewrite H1. all :auto.
      
  }
  split; intros env modules own_module eff res eff' id1 id2 F H0.
  * eapply A. auto. exact H. exact H0.
  * eapply A. auto. exact (weakly_equivalent_exprlist_sym P H). exact H0.
Qed.

Theorem ECall_weak_congr (P : list ErlModule -> Prop) (m : Expression) (f : Expression) (l : list Expression) : forall (l' : list Expression),
  weakly_equivalent_exprlist P l l'
->
  weakly_equivalent_expr P (ECall m f l) (ECall m f l').
Proof.
  assert (A : forall (l l' : list Expression) f env modules own_module id eff id' res eff', P modules ->
      weakly_equivalent_exprlist P l l' ->
      (exists clock, fbs_expr clock env modules own_module id (ECall m f l) eff = Result id' res eff')
    ->
      exists eff'', (exists clock, fbs_expr clock env modules own_module id (ECall m f l') eff = Result id' res eff'') /\ Permutation eff' eff''). 
  {
    intros l0 l' f0 env modules own_module id eff id' res eff' F H H0.
    destruct H0, x.
    inversion H0.
    simpl in H0.
    destruct ( fbs_expr x env modules own_module id m eff) eqn:D1; try congruence.
    destruct res0. destruct v; try congruence. destruct v0; try congruence.
    destruct (fbs_expr x env modules own_module id0 f0 eff0) eqn: D2; try congruence.
    destruct res0. destruct v0; try congruence. destruct v1; try congruence.
    * destruct (fbs_values (fbs_expr x) env modules own_module id1 l0 eff1) eqn:D; try congruence.
      destruct res0. destruct v; try congruence.
    
      ** inversion H0; subst.
         apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
         apply effect_extension_expr in D2 as D2'. destruct D2'. subst.
         apply effect_extension_exprlist in D as D'. destruct D'. subst. 
         apply ex_intro with (x := x), H in D. destruct D, H1, H1. 
         eapply bigger_clock_list with (clock' := x + x4) in H1.
         eapply bigger_clock_expr with (clock' := x + x4)  in D1.
         eapply bigger_clock_expr with (clock' := x + x4)  in D2.
         exists x3. split. exists (S (x + x4)). simpl. rewrite D1 , D2, H1.
         1-2,7: auto. 1-3: lia. intros; apply clock_increase_expr; auto. 
      ** destruct l1. destruct v0.
        + inversion H0; subst.
          apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
          apply effect_extension_expr in D2 as D2'. destruct D2'. subst.
          apply effect_extension_exprlist in D as D'. destruct D'. subst. 
          apply ex_intro with (x := x), H in D. destruct D, H1, H1. 
          eapply bigger_clock_list with (clock' := x + x4) in H1.
          eapply bigger_clock_expr with (clock' := x + x4)  in D1.
          eapply bigger_clock_expr with (clock' := x + x4)  in D2.
          exists x3. split. exists (S (x + x4)). simpl. rewrite D1 , D2, H1.
          1-2,7: auto. 1-3: lia. intros; apply clock_increase_expr; auto.
        + destruct l1. destruct get_modfunc eqn:MOD.
          ++ apply ex_intro with (x := x), H in D. destruct D, H1, H1.   
             apply effect_extension_expr in H0 as H0'. destruct H0'. subst.  
             apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
             apply effect_extension_expr in D2 as D2'. destruct D2'. subst.
             apply effect_extension_exprlist in H1 as H1'. destruct H1'. subst. 
             eapply bigger_clock_list with (clock' := x + x1) in H1.
             eapply bigger_clock_expr with (clock' := x + x1)  in D1.
             eapply bigger_clock_expr with (clock' := x + x1)  in D2.
             eapply bigger_clock_expr with (clock' := x + x1)  in H0.
             eapply effect_irrelevant_expr with (eff0 := (((eff ++ x3) ++ x4) ++ x5))  in H0.  
             exists ((((eff ++ x3) ++ x4) ++ x5) ++ x2). split. exists (S (x + x1)). simpl. rewrite D1 , D2 , H1 , MOD.
            1-2,8: auto. perm_solver. 1-4: lia. intros; apply clock_increase_expr; auto.
          ++  inversion H0. subst.
              apply ex_intro with (x := x), H in D. destruct D, H1, H1.
              remember (snd (eval s s0 v1 eff2)) as f1. symmetry in Heqf1.
              apply eval_effect_extension_snd in Heqf1 as F1.
              destruct F1. rewrite H3 in Heqf1.
              eapply bigger_clock_list with (clock' := x + x1) in H1.
              eapply bigger_clock_expr with (clock' := x + x1)  in D1.
              eapply bigger_clock_expr with (clock' := x + x1)  in D2.
              eapply eval_effect_irrelevant_snd with (eff3 := x0) in Heqf1. 
              exists (x0 ++ x2). split. exists (S x + x1). simpl.  rewrite D1, D2, H1, MOD.
              rewrite Heqf1; erewrite eval_effect_irrelevant_fst; reflexivity.  
              subst. perm_solver. 1-3:lia. intros; apply clock_increase_expr. all: auto.
          ++  inversion H0. subst.
              apply ex_intro with (x := x), H in D. destruct D, H1, H1.
              eapply bigger_clock_list with (clock' := x + x2) in H1.
              eapply bigger_clock_expr with (clock' := x + x2)  in D1.
              eapply bigger_clock_expr with (clock' := x + x2)  in D2.
              exists (x1). split. exists (S x + x2). simpl.  rewrite D1, D2, H1.
              auto. perm_solver. 1-3:lia. intros; apply clock_increase_expr. all: auto.
          
        + inversion H0; subst.
          apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
          apply effect_extension_expr in D2 as D2'. destruct D2'. subst.
          apply effect_extension_exprlist in D as D'. destruct D'. subst. 
          apply ex_intro with (x := x), H in D. destruct D, H1, H1. 
          eapply bigger_clock_list with (clock' := x + x4) in H1.
          eapply bigger_clock_expr with (clock' := x + x4)  in D1.
          eapply bigger_clock_expr with (clock' := x + x4)  in D2.
          exists x3. split. exists (S (x + x4)). simpl. rewrite D1 , D2, H1.
          1-2,7: auto. 1-3: lia. intros; apply clock_increase_expr; auto.
        + inversion H0; subst.
          apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
          apply effect_extension_expr in D2 as D2'. destruct D2'. subst.
          apply effect_extension_exprlist in D as D'. destruct D'. subst. 
          apply ex_intro with (x := x), H in D. destruct D, H1, H1. 
          eapply bigger_clock_list with (clock' := x + x4) in H1.
          eapply bigger_clock_expr with (clock' := x + x4)  in D1.
          eapply bigger_clock_expr with (clock' := x + x4)  in D2.
          exists x3. split. exists (S (x + x4)). simpl. rewrite D1 , D2, H1.
          1-2,7: auto. 1-3: lia. intros; apply clock_increase_expr; auto.
        + inversion H0; subst.
          apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
          apply effect_extension_expr in D2 as D2'. destruct D2'. subst.
          apply effect_extension_exprlist in D as D'. destruct D'. subst. 
          apply ex_intro with (x := x), H in D. destruct D, H1, H1. 
          eapply bigger_clock_list with (clock' := x + x4) in H1.
          eapply bigger_clock_expr with (clock' := x + x4)  in D1.
          eapply bigger_clock_expr with (clock' := x + x4)  in D2.
          exists x3. split. exists (S (x + x4)). simpl. rewrite D1 , D2, H1.
          1-2,7: auto. 1-3: lia. intros; apply clock_increase_expr; auto.
        + inversion H0; subst.
          apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
          apply effect_extension_expr in D2 as D2'. destruct D2'. subst.
          apply effect_extension_exprlist in D as D'. destruct D'. subst. 
          apply ex_intro with (x := x), H in D. destruct D, H1, H1. 
          eapply bigger_clock_list with (clock' := x + x4) in H1.
          eapply bigger_clock_expr with (clock' := x + x4)  in D1.
          eapply bigger_clock_expr with (clock' := x + x4)  in D2.
          exists x3. split. exists (S (x + x4)). simpl. rewrite D1 , D2, H1.
          1-2,7: auto. 1-3: lia. intros; apply clock_increase_expr; auto.
        + inversion H0; subst.
          apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
          apply effect_extension_expr in D2 as D2'. destruct D2'. subst.
          apply effect_extension_exprlist in D as D'. destruct D'. subst. 
          apply ex_intro with (x := x), H in D. destruct D, H1, H1. 
          eapply bigger_clock_list with (clock' := x + x5) in H1.
          eapply bigger_clock_expr with (clock' := x + x5)  in D1.
          eapply bigger_clock_expr with (clock' := x + x5)  in D2.
          exists x4. split. exists (S (x + x5)). simpl. rewrite D1 , D2, H1.
          1-2,7: auto. 1-3: lia. intros; apply clock_increase_expr; auto.

      ** inversion H0; subst.
         apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
         apply effect_extension_expr in D2 as D2'. destruct D2'. subst.
         apply effect_extension_exprlist in D as D'. destruct D'. subst. 
         apply ex_intro with (x := x), H in D. destruct D, H1, H1. 
         eapply bigger_clock_list with (clock' := x + x4) in H1.
         eapply bigger_clock_expr with (clock' := x + x4)  in D1.
         eapply bigger_clock_expr with (clock' := x + x4)  in D2.
         exists x3. split. exists (S (x + x4)). simpl. rewrite D1 , D2, H1.
         1-2,7: auto. 1-3: lia. intros; apply clock_increase_expr; auto. 
      ** inversion H0; subst.
         apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
         apply effect_extension_expr in D2 as D2'. destruct D2'. subst.
         apply effect_extension_exprlist in D as D'. destruct D'. subst. 
         apply ex_intro with (x := x), H in D. destruct D, H1, H1. 
         eapply bigger_clock_list with (clock' := x + x4) in H1.
         eapply bigger_clock_expr with (clock' := x + x4)  in D1.
         eapply bigger_clock_expr with (clock' := x + x4)  in D2.
         exists x3. split. exists (S (x + x4)). simpl. rewrite D1 , D2, H1.
         1-2,7: auto. 1-3: lia. intros; apply clock_increase_expr; auto. 
      ** inversion H0; subst.
         apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
         apply effect_extension_expr in D2 as D2'. destruct D2'. subst.
         apply effect_extension_exprlist in D as D'. destruct D'. subst. 
         apply ex_intro with (x := x), H in D. destruct D, H1, H1. 
         eapply bigger_clock_list with (clock' := x + x4) in H1.
         eapply bigger_clock_expr with (clock' := x + x4)  in D1.
         eapply bigger_clock_expr with (clock' := x + x4)  in D2.
         exists x3. split. exists (S (x + x4)). simpl. rewrite D1 , D2, H1.
         1-2,7: auto. 1-3: lia. intros; apply clock_increase_expr; auto. 
      ** inversion H0; subst.
         apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
         apply effect_extension_expr in D2 as D2'. destruct D2'. subst.
         apply effect_extension_exprlist in D as D'. destruct D'. subst. 
         apply ex_intro with (x := x), H in D. destruct D, H1, H1. 
         eapply bigger_clock_list with (clock' := x + x4) in H1.
         eapply bigger_clock_expr with (clock' := x + x4)  in D1.
         eapply bigger_clock_expr with (clock' := x + x4)  in D2.
         exists x3. split. exists (S (x + x4)). simpl. rewrite D1 , D2, H1.
         1-2,7: auto. 1-3: lia. intros; apply clock_increase_expr; auto.
      ** inversion H0; subst.
         apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
         apply effect_extension_expr in D2 as D2'. destruct D2'. subst.
         apply effect_extension_exprlist in D as D'. destruct D'. subst. 
         apply ex_intro with (x := x), H in D. destruct D, H1, H1. 
         eapply bigger_clock_list with (clock' := x + x4) in H1.
         eapply bigger_clock_expr with (clock' := x + x4)  in D1.
         eapply bigger_clock_expr with (clock' := x + x4)  in D2.
         exists x3. split. exists (S (x + x4)). simpl. rewrite D1 , D2, H1.
         1-2,7: auto. 1-3: lia. intros; apply clock_increase_expr; auto.
    * inversion H0; subst.
      apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
      apply effect_extension_expr in D2 as D2'. destruct D2'. subst.
      exists ((eff ++ x0) ++ x1). split. exists (S x). simpl. rewrite D1 , D2. all:auto.
    * inversion H0; subst.
    apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
    exists ((eff ++ x0)). split. exists (S x). simpl. rewrite D1. all:auto.

  }
  split; intros env modules own_module eff res eff' id1 id2 F H0.
  * eapply A. auto. exact H. exact H0.
  * eapply A. auto. exact (weakly_equivalent_exprlist_sym P H). exact H0.
Qed.

Theorem EPrimOp_weak_congr (P : list ErlModule -> Prop) (f : string) (l : list Expression) : forall (l' : list Expression),
  weakly_equivalent_exprlist P l l'
->
  weakly_equivalent_expr P (EPrimOp f l) (EPrimOp f l').
Proof.
  assert (A : forall (l l' : list Expression) f env modules own_module id eff id' res eff', P modules ->
      weakly_equivalent_exprlist P l l' ->
      (exists clock, fbs_expr clock env modules own_module id (EPrimOp f l) eff = Result id' res eff')
    ->
      exists eff'', (exists clock, fbs_expr clock env modules own_module id (EPrimOp f l') eff = Result id' res eff'') /\ Permutation eff' eff''). 
  {
    intros l0 l' f0 env modules own_module id eff id' res eff' F H H0.
    destruct H0, x.
    inversion H0.
    simpl in H0. destruct (fbs_values (fbs_expr x) env modules own_module id l0 eff) eqn:D1.
    destruct res0. 3-4: congruence.
    * inversion H0. subst.
      apply ex_intro with (x := x), H in D1. destruct D1, H1, H1.
      remember (snd (primop_eval f0 v eff0)) as f1. symmetry in Heqf1.
      apply primop_eval_effect_extension_snd in Heqf1 as F1.
      destruct F1. rewrite H3 in Heqf1.
      eapply primop_eval_effect_irrelevant_snd with (eff1 := x0) in Heqf1.
      exists (x0 ++ x2). split. exists (S x1). simpl. rewrite H1. rewrite Heqf1.
      erewrite primop_eval_effect_irrelevant_fst. reflexivity. subst. perm_solver. auto.
    * inversion H0. subst.
      apply ex_intro with (x := x), H in D1. destruct D1, H1, H1.
      exists x0. split. exists (S x1). simpl. rewrite H1. all :auto.
      
  }
  split; intros env modules own_module eff res eff' id1 id2 F H0.
  * eapply A. auto. exact H. exact H0.
  * eapply A. auto. exact (weakly_equivalent_exprlist_sym P H). exact H0.
Qed.

Theorem EApp_weak_congr (P : list ErlModule -> Prop) (exp : Expression) (l : list Expression) : forall (exp' : Expression) (l' : list Expression),
  weakly_equivalent_expr P exp exp' ->
  weakly_equivalent_exprlist P l l'
->
  weakly_equivalent_expr P (EApp exp l) (EApp exp' l').
Proof.
  assert (A : forall exp exp' (l l' : list Expression) env modules own_module id eff id' res eff', P modules ->
    weakly_equivalent_expr P exp exp' ->
    weakly_equivalent_exprlist P l l'
    ->
    (exists clock, fbs_expr clock env modules own_module id (EApp exp l) eff = Result id' res eff')
    ->
    exists eff'', (exists clock, fbs_expr clock env modules own_module id (EApp exp' l') eff = Result id' res eff'') /\ Permutation eff' eff'').
  {
    intros exp0 exp' l0 l' env modules own_module id eff id' res eff' F H H0 H1. 
    destruct H1. destruct x. inversion H1. simpl in H1.
    destruct (fbs_expr x env modules own_module id exp0 eff) eqn:D1.
    destruct res0. destruct v. congruence. destruct v0. 2,4-5: congruence.
    * destruct (fbs_values (fbs_expr x) env modules own_module id0 l0 eff0) eqn:D2.
      destruct res0. 3-4: congruence.
      - apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
        apply ex_intro with (x := x), H in D1. destruct D1, H2, H2.
        apply effect_extension_expr in H2 as D1'. destruct D1'. subst.
        apply effect_extension_exprlist in D2 as D1'. destruct D1'. subst.
        apply ex_intro with (x := x), H0 in D2. destruct D2, H4, H4.
        apply effect_extension_exprlist in H4 as D1'. destruct D1'. subst.
        eapply effect_irrelevant_exprlist with (eff0 := eff ++ x3) in H4.
        destruct v.
          1-2, 4-6: inversion H1; subst; exists ((eff ++ x3) ++ x6); split;
            [ exists (S (x2 + x5)); eapply bigger_clock_list in H4;
                [ simpl; erewrite (bigger_clock_expr _ _ H2), H4; auto
                | auto
                | intros; eapply clock_increase_expr; auto 
                ]
              | perm_solver
            ]; lia.
        destruct (length vl =? length v0) eqn:D3.
        + apply effect_extension_expr in H1 as D1'. destruct D1'. subst.
          eapply effect_irrelevant_expr with (eff0 := (eff ++ x3) ++ x6) in H1.
          exists (((eff ++ x3) ++ x6) ++ x4). split.
          ** exists (S (x2 + x5 + x)). eapply bigger_clock_list with (clock' := x2 + x5 + x) in H4.
             2: lia.
             2: intros; eapply clock_increase_expr; auto.
             simpl. erewrite (bigger_clock_expr _ _ H2), H4, (bigger_clock_expr _ _ H1), D3. auto.
          ** perm_solver.
        + inversion H1; subst; exists ((eff ++ x3) ++ x6); split;
            [ exists (S (x2 + x5)); eapply bigger_clock_list in H4;
                [ simpl; erewrite (bigger_clock_expr _ _ H2), H4, D3; auto
                | auto
                | intros; eapply clock_increase_expr; auto 
                ]
              | perm_solver
            ]; lia.
        + auto.
        + auto.
      - inversion H1. subst.
        apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
        apply ex_intro with (x := x), H in D1. destruct D1, H2, H2.
        apply effect_extension_expr in H2 as D1'. destruct D1'. subst.
        apply effect_extension_exprlist in D2 as D1'. destruct D1'. subst.
        apply ex_intro with (x := x), H0 in D2. destruct D2, H4, H4.
        apply effect_extension_exprlist in H4 as D1'. destruct D1'. subst.
        eapply effect_irrelevant_exprlist in H4.
        exists ((eff ++ x3) ++ x6). split. exists (S (x2 + x5)). simpl.
        eapply bigger_clock_list in H4. 3: { intros. eapply clock_increase_expr. auto. }
        erewrite (bigger_clock_expr _ _ H2), H4. auto. lia. perm_solver. all : auto.
      
    * inversion H1. subst.
      apply ex_intro with (x := x), H in D1. destruct D1, H2, H2.
      exists (x0). split. exists (S x1). simpl. rewrite H2. all :auto.
  }
  split; intros env modules own_module eff res eff' id1 id2 F H1.
  * eapply A. auto. exact H. exact H0. exact H1.
  * eapply A. auto. exact (weakly_equivalent_expr_sym P H). exact (weakly_equivalent_exprlist_sym P H0). exact H1.
Unshelve. all: lia.
Qed.

Theorem ECase_weak_congr (P : list ErlModule -> Prop) (exp : Expression) (l : list (list Pattern * Expression * Expression)) : forall (exp' : Expression) (l' : list (list Pattern * Expression * Expression)),
  weakly_equivalent_expr P exp exp' ->
  weakly_equivalent_case P l l'
->
  weakly_equivalent_expr P (ECase exp l) (ECase exp' l').
Proof.
  assert (A : forall exp exp' (l l' : list (list Pattern * Expression * Expression)) env modules own_module id eff id' res eff', P modules ->
  weakly_equivalent_expr P exp exp' ->
    weakly_equivalent_case P l l'
  ->
    (exists clock, fbs_expr clock env modules own_module id (ECase exp l) eff = Result id' res eff')
  ->
    (exists eff'', (exists clock,
                   fbs_expr clock env modules own_module id (ECase exp' l') eff = Result id' res eff'') /\
                   Permutation eff' eff'') 
  ).
  {
    intros exp0 exp' l0 l' env modules own_module id eff id' res eff' F H H0 H1. 
    destruct H1. destruct x. inversion H1. simpl in H1.
    destruct (fbs_expr x env modules own_module id exp0 eff) eqn:D1.
    destruct res0. 3-4: congruence.
    * apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
      apply ex_intro with (x := x), H in D1. destruct D1, H2, H2.
      apply effect_extension_expr in H2 as D1'. destruct D1'. subst.
      apply effect_extension_case in H1 as A. destruct A. subst.
      apply ex_intro with (x := x), H0 in H1. destruct H1, H1, H1.
      apply effect_extension_case in H1 as A. destruct A. subst.
      apply effect_irrelevant_case with (eff0 := eff ++ x3) in H1.
      exists ((eff ++ x3) ++ x6). split. 2: perm_solver.
      exists (S (x2 + x5)). simpl.
      erewrite (bigger_clock_expr _ _ H2), (bigger_clock_case _ H1 _). all :auto.
    * inversion H1. subst.
      apply ex_intro with (x := x), H in D1. destruct D1, H2, H2.
      exists x0. split. 2: auto. exists (S x1). simpl. rewrite H2. all : auto. 
  }
  split; intros env modules own_module eff res eff' id1 id2 F H1.
  * eapply A. auto. exact H. exact H0. exact H1.
  * eapply A. auto. exact (weakly_equivalent_expr_sym P H). exact (weakly_equivalent_case_sym P H0). exact H1.
Unshelve. all: lia.
Qed.

Theorem ELet_weak_congr (P : list ErlModule -> Prop) (e1 e2 : Expression) vl : forall (e1' e2' : Expression),
  weakly_equivalent_expr P e1 e1' ->
  weakly_equivalent_expr P e2 e2'
->
  weakly_equivalent_expr P (ELet vl e1 e2) (ELet vl e1' e2').
Proof.
  assert (A : forall env modules own_module id e1 e1' e2 e2' vl eff id' res eff', P modules ->
    weakly_equivalent_expr P e1 e1' -> weakly_equivalent_expr P e2 e2' ->
    (exists clock, fbs_expr clock env modules own_module id (ELet vl e1 e2) eff = Result id' res eff')
  ->
    (exists eff'', (exists clock, fbs_expr clock env modules own_module id (ELet vl e1' e2') eff = Result id' res eff'') /\ Permutation eff' eff'')
  ).
  {
    intros env modules own_module id e0 e1' e3 e2' vl0 eff id' res eff' F H H0 H1.
    destruct H1, x. inversion H1. simpl in H1.
    destruct (fbs_expr x env modules own_module id e0 eff) eqn:D1.
    destruct res0. destruct (length v =? length vl0) eqn:D2. 2,4-5: congruence.
    * apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
      apply ex_intro with (x := x), H in D1. destruct D1, H2, H2.
      apply effect_extension_expr in H2 as D1'. destruct D1'. subst.
      apply effect_extension_expr in H1 as D1'. destruct D1'. subst.
      apply ex_intro with (x := x), H0 in H1. destruct H1, H1, H1.
      apply effect_extension_expr in H1 as D1'. destruct D1'. subst.
      apply effect_irrelevant_expr with (eff0 := eff ++ x3) in H1.
      exists ((eff ++ x3) ++ x6). split. 2: perm_solver.
      exists (S (x2 + x5)). simpl.
      erewrite (bigger_clock_expr _ _ H2), (bigger_clock_expr _ _ H1), D2. all : auto.
    * inversion H1. subst.
      apply ex_intro with (x := x), H in D1. destruct D1, H2, H2.
      exists x0. split. 2: auto. exists (S x1). simpl. rewrite H2. all : auto.
  }
  split; intros env modules own_module eff res eff' id1 id2 F H1.
  * eapply A. auto. exact H. exact H0. exact H1.
  * eapply A. auto. exact (weakly_equivalent_expr_sym P H). exact (weakly_equivalent_expr_sym P H0). exact H1.
  Unshelve. all: lia.
Qed.

Theorem ESeq_weak_congr  (P : list ErlModule -> Prop ) e1 e2 e1' e2' :
  weakly_equivalent_expr P e1 e1' -> weakly_equivalent_expr P e2 e2'
->
  weakly_equivalent_expr P (ESeq e1 e2) (ESeq e1' e2').
Proof.
  assert (A : forall env modules own_module id e1 e1' e2 e2' eff id' res eff', P modules ->
    weakly_equivalent_expr P e1 e1' -> weakly_equivalent_expr P e2 e2' ->
    (exists clock, fbs_expr clock env modules own_module id (ESeq e1 e2) eff = Result id' res eff')
  ->
    (exists eff'', (exists clock, fbs_expr clock env modules own_module id (ESeq e1' e2') eff = Result id' res eff'') /\ Permutation eff' eff'')
  ).
  {
    intros env modules own_module id e0 e1'0 e3 e2'0 eff id' res eff' F H H0 H1.
    destruct H1, x. inversion H1. simpl in H1.
    destruct (fbs_expr x env modules own_module id e0 eff) eqn:D1.
    destruct res0. destruct v. congruence. destruct v0. 2,4-5: congruence.
    * apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
      apply ex_intro with (x := x), H in D1. destruct D1, H2, H2.
      apply effect_extension_expr in H2 as D1'. destruct D1'. subst.
      apply effect_extension_expr in H1 as D1'. destruct D1'. subst.
      apply ex_intro with (x := x), H0 in H1. destruct H1, H1, H1.
      apply effect_extension_expr in H1 as D1'. destruct D1'. subst.
      apply effect_irrelevant_expr with (eff0 := eff ++ x3) in H1.
      exists ((eff ++ x3) ++ x6). split. 2: perm_solver.
      exists (S (x2 + x5)). simpl.
      erewrite (bigger_clock_expr _ _ H2), (bigger_clock_expr _ _ H1). all : auto.
    * inversion H1. subst.
      apply ex_intro with (x := x), H in D1. destruct D1, H2, H2.
      exists x0. split. 2: auto. exists (S x1). simpl. rewrite H2. all : auto.
  }
  split; intros env modules own_module eff res eff' id1 id2 F H1.
  * eapply A. auto. eexact H. exact H0. exact H1.
  * eapply A. auto.  eexact (weakly_equivalent_expr_sym P H). exact (weakly_equivalent_expr_sym P H0). exact H1.
  Unshelve. all: lia.
Qed.

Theorem ELetRec_weak_congr (P : list ErlModule -> Prop) (exp : Expression) l : forall (exp' : Expression),
  weakly_equivalent_expr P exp exp'
->
  weakly_equivalent_expr P (ELetRec l exp) (ELetRec l exp').
Proof.
  intros.
  split; intros env modules own_module eff res eff' id1 id2 F H0.
  * destruct H0. destruct x. inversion H0. simpl in H0.
    apply ex_intro with (x := x), H in H0. destruct H0, H0, H0.
    exists x0. split. 2: auto. exists (S x1). simpl. rewrite H0. all : auto.
  * destruct H0. destruct x. inversion H0. simpl in H0.
    apply ex_intro with (x := x), H in H0. destruct H0, H0, H0.
    exists x0. split. 2: auto. exists (S x1). simpl. rewrite H0. all : auto.
Qed.

Theorem EMap_weak_congr (P : list ErlModule -> Prop) (l : list (Expression * Expression)) : 
  forall (l' : list (Expression * Expression)),
  weakly_equivalent_exprlist P (make_map_exps l) (make_map_exps l')
->
  weakly_equivalent_expr P (EMap l) (EMap l').
Proof.
  assert (A :
    forall (l l' : list (Expression * Expression)) env modules own_module id eff eff' id' res, P modules ->
    weakly_equivalent_exprlist P (make_map_exps l) (make_map_exps l') ->
    (exists clock, fbs_expr clock env modules own_module id (EMap l) eff = Result id' res eff')
    ->
    (exists eff'', (exists clock, fbs_expr clock env modules own_module id (EMap l') eff = Result id' res eff'') /\ Permutation eff' eff'')
  ). {
    intros l0 l' env modules own_module id eff eff' id' res F H H0.
    destruct H0, x. inversion H0. simpl in H0.
    destruct (fbs_values (fbs_expr x) env modules own_module id (make_map_exps l0) eff) eqn: D1.
    destruct res0. 3-4: congruence.
    * destruct (make_map_vals_inverse v) eqn:HH. 2: congruence. destruct p. inversion H0.
      subst. apply ex_intro with (x := x), H in D1. destruct D1, H1, H1.
      exists x0. split. 2: auto. exists (S x1). simpl. rewrite H1, HH. all : auto.
    * inversion H0. subst.
      apply ex_intro with (x := x), H in D1. destruct D1, H1, H1.
      exists x0. split. 2: auto. exists (S x1). simpl. rewrite H1. all : auto.
  }
  split; intros env modules own_module eff res eff' id1 id2 F H0.
  * eapply A. auto. exact H. exact H0.
  * eapply A. auto. exact (weakly_equivalent_exprlist_sym P H). exact H0.
Qed.

Theorem ETry_weak_congr (P : list ErlModule -> Prop) (e1 e2 e3 : Expression) vl1 vl2 : forall (e1' e2' e3' : Expression),
  weakly_equivalent_expr P e1 e1' ->
  weakly_equivalent_expr P e2 e2' ->
  weakly_equivalent_expr P e3 e3'
->
  weakly_equivalent_expr P (ETry e1 vl1 e2 vl2 e3) (ETry e1' vl1 e2' vl2 e3').
Proof.
  assert (A : forall env modules own_module id e1 e1' e2 e2' e3 e3' eff id' res eff', P modules ->
    weakly_equivalent_expr P e1 e1' ->
    weakly_equivalent_expr P e2 e2' ->
    weakly_equivalent_expr P e3 e3' ->
    (exists clock, fbs_expr clock env modules own_module id (ETry e1 vl1 e2 vl2 e3) eff = Result id' res eff')
  ->
    (exists eff'', (exists clock, fbs_expr clock env modules own_module id (ETry e1' vl1 e2' vl2 e3') eff = Result id' res eff'') /\ Permutation eff' eff'')
  ).
  {
    intros env modules own_module id e0 e1' e4 e2' e5 e3' eff id' res eff' F H H0 H1 H2.
    destruct H2, x. inversion H2. simpl in H2.
    destruct (fbs_expr x env modules own_module id e0 eff) eqn:D1.
    destruct res0. destruct (length v =? length vl1) eqn:D2. 2,4-5: congruence.
    * apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
      apply ex_intro with (x := x), H in D1. destruct D1, H3, H3.
      apply effect_extension_expr in H3 as D1'. destruct D1'. subst.
      apply effect_extension_expr in H2 as D1'. destruct D1'. subst.
      apply ex_intro with (x := x), H0 in H2. destruct H2, H2, H2.
      apply effect_extension_expr in H2 as D1'. destruct D1'. subst.
      apply effect_irrelevant_expr with (eff0 := eff ++ x3) in H2.
      exists ((eff ++ x3) ++ x6). split. 2: perm_solver.
      exists (S (x2 + x5)). simpl.
      erewrite (bigger_clock_expr _ _ H3), (bigger_clock_expr _ _ H2), D2. all : auto.
    * apply effect_extension_expr in D1 as D1'. destruct D1'. subst.
      apply ex_intro with (x := x), H in D1. destruct D1, H3, H3.
      apply effect_extension_expr in H3 as D1'. destruct D1'. subst.
      apply effect_extension_expr in H2 as D1'. destruct D1'. subst.
      apply ex_intro with (x := x), H1 in H2. destruct H2, H2, H2.
      apply effect_extension_expr in H2 as D1'. destruct D1'. subst.
      apply effect_irrelevant_expr with (eff0 := eff ++ x3) in H2.
      exists ((eff ++ x3) ++ x6). split. 2: perm_solver.
      exists (S (x2 + x5)). simpl.
      erewrite (bigger_clock_expr _ _ H3), (bigger_clock_expr _ _ H2). all : auto.
  }
  split; intros env modules own_module eff res eff' id1 id2 F H2.
  * eapply A. auto. exact H. exact H0. exact H1. exact H2.
  * eapply A. auto. exact (weakly_equivalent_expr_sym P H). exact (weakly_equivalent_expr_sym P H0). exact (weakly_equivalent_expr_sym P H1). exact H2.
  Unshelve. all: lia.
Qed.

Theorem EValues_weak_congr (P : list ErlModule -> Prop) (l : list Expression) : forall (l' : list Expression),
  weakly_equivalent_exprlist P l l'
->
  weakly_equivalent_expr P (EValues l) (EValues l').
Proof.
  assert (A : forall (l l' : list Expression) env modules own_module id eff id' res eff', P modules ->
      weakly_equivalent_exprlist P l l' ->
      (exists clock, fbs_expr clock env modules own_module id (EValues l) eff = Result id' res eff')
    ->
      exists eff'', (exists clock, fbs_expr clock env modules own_module id (EValues l') eff = Result id' res eff'') /\ Permutation eff' eff'').
  {
    intros l0 l' env modules own_module id eff id' res eff' F H H0.
    destruct H0, x.
    inversion H0.
    simpl in H0. destruct (fbs_values (fbs_expr x) env modules own_module id l0 eff) eqn:D1.
    destruct res0. 3-4: congruence.
    * inversion H0. subst.
      apply ex_intro with (x := x), H in D1. destruct D1, H1, H1.
      exists x0. split. exists (S x1). simpl. rewrite H1. all : auto.
      
    * inversion H0. subst.
      apply ex_intro with (x := x), H in D1. destruct D1, H1, H1.
      exists x0. split. exists (S x1). simpl. rewrite H1. all : auto.
      
  }
  split; intros env modules own_module eff res eff' id1 id2 F H0.
  * eapply A. auto. exact H. exact H0.
  * eapply A. auto. exact (weakly_equivalent_exprlist_sym P H). exact H0.
Qed.

End congruence.

Theorem fully_implies_weakly (P : list ErlModule -> Prop) e1 e2 :
  fully_equivalent_expr P e1 e2
->
  weakly_equivalent_expr P e1 e2.
Proof.
  intros. split.
  * intros. apply H in H1. exists eff'. split. exact H1. all : auto.
  * intros. apply H in H1. exists eff'. split. exact H1. all : auto.
Qed.

Theorem fully_implies_weakly_exprlist (P : list ErlModule -> Prop) l1 l2 :
  fully_equivalent_exprlist P l1 l2
->
  weakly_equivalent_exprlist P l1 l2.
Proof.
  intros. split.
  * intros. apply H in H1. exists eff'. split. exact H1. all : auto.
  * intros. apply H in H1. exists eff'. split. exact H1. all : auto.
Qed.

Theorem fully_implies_weakly_case (P : list ErlModule -> Prop) l1 l2 :
  fully_equivalent_case P l1 l2
->
  weakly_equivalent_case P l1 l2.
Proof.
  intros. split.
  * intros. apply H in H1. exists eff'. split. exact H1. all : auto.
  * intros. apply H in H1. exists eff'. split. exact H1. all : auto.
Qed.

