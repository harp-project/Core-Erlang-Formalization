Require Core_Erlang_Determinism_Helpers.

From Coq Require Import Arith.PeanoNat.

(** Proofs about the semantics *)
Module Proofs.

Export Core_Erlang_Determinism_Helpers.Determinism_Helpers.

Import ListNotations.
(* Import Coq.Init.Logic. *)

Proposition length_split_eq {A B : Type} (l : list (A * B)) :
  length (fst (split l)) = length (snd (split l)).
Proof.
  rewrite split_length_l, split_length_r. auto.
Qed.

Proposition split_eq {A B : Type} {l l0 : list (A * B)} : 
  split l = split l0 <-> l = l0.
Proof.
  split; generalize dependent l0.
  * induction l; intros.
    - inversion H. destruct l0.
      + reflexivity.
      + inversion H1. destruct p. destruct (split l0). inversion H2.
    - destruct l0.
      + inversion H. destruct a. destruct (split l). inversion H1.
      + inversion H. subst. assert (split l = split l0). {
        destruct a, p. destruct (split l), (split l0). inversion H1. subst. auto.
        }
        pose (IH := IHl l0 H0).
        destruct a, p. destruct (split l), (split l0) in H1. inversion H1. rewrite IH. auto.
  * intros. rewrite H. reflexivity.
Qed.

Proposition plus_comm_basic {e1 e2 t : Value} {eff : SideEffectList} : 
eval "+"%string [e1 ; e2] eff = (inl [t], eff)
->
eval "+"%string [e2; e1] eff = (inl [t], eff).
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(reflexivity || inversion H1).
  all: try(destruct l); try(destruct l0); try(reflexivity || inversion H1).
  * unfold eval. simpl. rewrite <- Z.add_comm. reflexivity.
Qed.

Proposition plus_comm_basic_value {e1 e2 v : Value} (eff eff2 : SideEffectList) : 
  eval "+"%string [e1 ; e2] eff = (inl [v], eff)
->
  eval "+"%string [e2; e1] eff2 = (inl [v], eff2).
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(reflexivity || inversion H1).
  all: try(destruct l); try(destruct l0); try(reflexivity || inversion H1).
  * unfold eval. simpl. rewrite <- Z.add_comm. reflexivity.
Qed.

Proposition plus_comm_extended {e1 e2 : Value} (v : ValueSequence + Exception) (eff eff2 : SideEffectList) : 
  eval "+"%string [e1 ; e2] eff = (v, eff)
->
  exists v', eval "+"%string [e2; e1] eff2 = (v', eff2).
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  1-7, 9-36: eexists; try(inversion H1; reflexivity).
  * eexists. reflexivity.
Qed.

Proposition plus_effect_unmodified {e1 e2 : Value} (v' : ValueSequence + Exception) (eff eff2 : SideEffectList) :
  eval "+"%string [e1 ; e2] eff = (v', eff2)
->
  eff = eff2.
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(inversion H1; reflexivity).
  all: try(destruct l); try(inversion H1; reflexivity).
  all: destruct l0.
Qed.

Proposition plus_effect_changeable {v1 v2 : Value} (v' : ValueSequence + Exception) (eff eff2 : SideEffectList) :
  eval "+"%string [v1; v2] eff = (v', eff)
->
  eval "+"%string [v1; v2] eff2 = (v', eff2).
Proof.
  intros. simpl in *. case_eq v1; case_eq v2; intros; subst.
  all: try(inversion H; reflexivity).
  all: try(destruct l); try(inversion H; reflexivity).
  all: destruct l0; inversion H; auto.
Qed.

Theorem determinism_mutual :
(
  forall env id e eff id' v1 eff',
  |env, id, e, eff| -e> | id', v1, eff'|
->
  (forall v2 eff'' id'', |env, id, e, eff| -e> |id'', v2, eff''| -> v1 = v2 /\ eff' = eff''
      /\ id' = id'')
) /\
(
  forall env id e eff id' v1 eff',
  |env, id, e, eff| -s> | id', v1, eff'|
->
  (forall v2 eff'' id'', |env, id, e, eff| -s> |id'', v2, eff''| -> v1 = v2 /\ eff' = eff''
      /\ id' = id'')
)
.
Proof.
  apply eval_ind; intros.

  (* VALUE LIST *)
  * inversion H0; subst.
    - pose (P := singleexplist_equality _ _ _ _ _ _ _ H H5 H2 H3 e e0 e1 H4).
      destruct P. destruct H6. subst. auto.
    - pose (P := singleexplist_prefix_eq _ _ _ _ _ _ _ _ _ _ _ e e0 H4 H2 e1 H5 H H6 H9).
      inversion P.

  (* VALUE LIST EXCEPTION *)
  * inversion H1; subst.
    - pose (P := singleexplist_prefix_eq_rev _ _ _ _ _ _ _ _ _ _ _ H H6 H0 l e0 H3 H4 H5 e1).
      inversion P.
    - epose (P := exception_equality_single _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H10 H0 H7
        _ _ _ _ _ _ _ _).
      destruct P, H4, H8. subst. auto.
      Unshelve.
      all: auto.

  (* SINGLE EXPRESSION *)
  * apply H. inversion H0. auto.

  (* NIL *)
  * inversion H. auto.

  (* LIT *)
  * inversion H. auto.

  (* VAR *)
  * inversion H. subst. rewrite e in H3. inversion H3. auto.

  (* FUNID *)
  * inversion H. subst. rewrite e in H3. inversion H3. auto.

  (* FUN *)
  * inversion H. auto.

  (* TUPLE *)
  * inversion H0; subst.
    - pose (P := explist_equality _ _ _ _ _ _ _ H H5 H2 H3 e e0 e1 H4).
      destruct P. destruct H6. subst. auto.
    - pose (P := explist_prefix_eq _ _ _ _ _ _ _ _ _ _ _ e e0 H4 H2 e1 H5 H H6 H9).
      inversion P.

  (* CONS *)
  * inversion H1; subst.
    - apply H in H6. destruct H6, H3. inversion H2. subst.
      apply H0 in H11. destruct H11, H4. inversion H3. subst. auto.
    - apply H in H10. destruct H10. congruence.
    - apply H in H6. destruct H6, H3. inversion H2. subst.
      apply H0 in H11. destruct H11, H4. congruence.

  (* CASE *)
  * inversion H3; subst.
    - apply H in H6. destruct H6, H5. inversion H4. subst.
      pose (P := index_case_equality _ _ _ _ _ _ _ _ _ _ H0 H9 e1 H8 H12 e3 H1).
      assert (i = i0). { auto. }
      clear P. subst. rewrite e1 in H8. inversion H8. subst.
      apply H1 in H12. apply H2 in H17. auto.
    - apply H in H12. destruct H12. congruence.
    - apply H in H8. destruct H8, H5. inversion H4. subst.
      pose (P := H13 i l0 _ _ _ e1).
      apply H1 in P. destruct P. inversion H5.

  (* CALL *)
  * inversion H0; subst.
    - pose (P := explist_equality _ _ _ _ _ _ _ H H6 H3 H4 e e0 e1 H5).
      destruct P. destruct H2. subst. rewrite H9 in e3. inversion e3. auto.
    - pose (P := explist_prefix_eq _ _ _ _ _ _ _ _ _ _ _ e e0 H5 H3 e1 H6 H H9 H14).
      inversion P.

  (* PRIMOP *)
  * inversion H0; subst.
    - pose (P := explist_equality _ _ _ _ _ _ _ H H6 H3 H4 e e0 e1 H5).
      destruct P. destruct H2. subst. rewrite H9 in e3. inversion e3. auto.
    - pose (P := explist_prefix_eq _ _ _ _ _ _ _ _ _ _ _ e e0 H5 H3 e1 H6 H H9 H14).
      inversion P.

  (* APP *)
  * inversion H2; subst.
    - apply H in H6. destruct H6, H4. inversion H3. subst.
      pose (P := explist_equality _ _ _ _ _ _ _ H0 H12 H5 H8 e e2 e3 H9).
      destruct P. destruct H6. subst. apply H1. auto.
    - apply H in H11. destruct H11. congruence.
    - apply H in H9. destruct H9, H4. inversion H3. subst.
      pose (P := explist_prefix_eq _ _ _ _ _ _ _ _ _ _ _ e e2 H7 H5 e3 H8 H0 H12 H17).
      inversion P.
    - apply H in H8. destruct H8, H4. inversion H3. subst.
      congruence.
    - apply H in H8. destruct H8, H4. inversion H3. subst.
      lia.

  (* LET *)
  * inversion H1; subst.
    - apply H in H7. destruct H7, H3. inversion H2. subst.
      apply H0 in H13. auto.
    - apply H in H11. destruct H11. congruence.

  (* SEQ *)
  * inversion H1; subst.
    - apply H in H6. destruct H6, H3. inversion H2. subst.
      apply H0 in H11. auto.
    - apply H in H10. destruct H10. inversion H2.

  (* LETREC *)
  * inversion H0. subst. apply H in H9. auto.

  (* MAP *)
  * inversion H0; subst.
    - assert (exps = exps0). { auto. } rewrite <- H1 in *.
      assert (length vals0 = length l * 2). { unfold vals0. rewrite H3. eapply length_make_map_vals. lia. }
      assert (length vals = length l * 2). { unfold vals. rewrite e0. eapply length_make_map_vals. lia. }
      assert (length exps = length l * 2). { unfold exps. apply length_make_map_exps. }
      rewrite <- H10 in *.
      pose (P := explist_equality _ _ _ _ _ _ _ H H6 (eq_sym H8) H4 (eq_sym H9) e1 e2 H5).
      destruct P. destruct H12. subst.
      unfold vals, vals0 in H12. apply make_map_vals_eq in H12.
      2-4: lia.
      destruct H12. subst. rewrite H7 in e4. inversion e4. subst. auto.
    - assert (length exps = length vals). { unfold vals. unfold exps. rewrite length_make_map_vals. rewrite length_make_map_exps. lia. rewrite <- e, <- e0. auto. }
      assert (length eff4 = length vals0).
      {
        unfold vals0. case_eq (modulo_2 (length eff4)); intros.
        * rewrite e5 in *. rewrite length_make_map_vals. rewrite Nat.add_0_r in H4.
          2: lia. rewrite H4. simpl. apply n_div_2_mod_0. lia.
        * rewrite e5 in *. rewrite length_make_map_vals2. 2: lia.
          rewrite H3. apply n_div_2_mod_1. lia.
      }
      rewrite H5 in H7, H10.
      epose (P := explist_prefix_eq _ _ _ _ _ _ _ _ _ _ _ H1 _ _ _ _ _ H H7 H10).
      inversion P.
      Unshelve.
      + unfold exps. rewrite length_make_map_exps. lia.
      + auto.
      + unfold vals0, exps.
        rewrite length_make_map_exps.
        unfold vals0. case_eq (modulo_2 (length eff4)); intros.
        ** rewrite e5 in *. rewrite length_make_map_vals. rewrite Nat.add_0_r in H4.
          2: lia. rewrite H4. rewrite <- n_div_2_mod_0. lia. lia.
        ** rewrite e5 in *. rewrite length_make_map_vals2. 2: lia.
          rewrite H3. rewrite <- n_div_2_mod_1. lia. lia.
      + unfold exps. rewrite length_make_map_exps. lia.
      + lia.

  (* CONS TL EXCEPTION *)
  * inversion H0; subst.
    - apply H in H5. destruct H5. congruence.
    - apply H in H9. auto.
    - apply H in H5. destruct H5. congruence.

  (* CONS HEAD EXCEPTION *)
  * inversion H1; subst.
    - apply H in H6. destruct H6, H3. inversion H2. subst.
      apply H0 in H11. destruct H11. congruence.
    - apply H in H10. destruct H10. congruence.
    - apply H in H6. destruct H6, H3. inversion H2. subst.
      apply H0 in H11. destruct H11, H4. inversion H2. auto.

  (* TUPLE EXCEPTION *)
  * inversion H1; subst.
    - pose (P := explist_prefix_eq_rev _ _ _ _ _ _ _ _ _ _ _ H H6 H0 l e0 H3 H4 H5 e1).
      inversion P.
    - epose (P := exception_equality _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H10 H0 H7
        _ _ _ _ _ _ _ _).
      destruct P, H4, H8. subst. auto.
      Unshelve.
      all: auto.

  (* TRY *)
  * inversion H1; subst.
    - apply H in H13. destruct H13, H3. inversion H2. subst.
      apply H0 in H15. destruct H15, H4. auto.
    - apply H in H13. destruct H13. congruence.

  (* CATCH *)
  * inversion H1; subst.
    - apply H in H13. destruct H13. congruence.
    - apply H in H13. destruct H13, H3. inversion H2. subst.
      apply H0 in H14. destruct H14, H4. auto.

  (* CASE EXCEPTION *)
  * inversion H0; subst.
    - apply H in H3. destruct H3. congruence.
    - apply H in H9. auto.
    - apply H in H5. destruct H5. congruence.

  (* CASE IFCLAUSE EXCEPTION *)
  * inversion H1; subst.
    - apply H in H4. destruct H4, H3. inversion H2. subst.
      pose (P := H0 i H5 _ _ _ H6 _ _ _ H10). destruct P. inversion H3.
    - apply H in H10. destruct H10. congruence.
    - apply H in H6. destruct H6, H3. inversion H2. subst.
      auto.

  (* CALL *)
  * inversion H1; subst.
    - pose (P := explist_prefix_eq_rev _ _ _ _ _ _ _ _ _ _ _ H H7 H0 l e0 H4 H5 H6 e1).
      inversion P.
    - epose (P := exception_equality _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H15 H0 H10
        _ _ _ _ _ _ _ _).
      destruct P, H3, H5. subst. auto.
      Unshelve.
      all: auto.

  (* PRIMOP *)
  * inversion H1; subst.
    - pose (P := explist_prefix_eq_rev _ _ _ _ _ _ _ _ _ _ _ H H7 H0 l e0 H4 H5 H6 e1).
      inversion P.
    - epose (P := exception_equality _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H15 H0 H10
        _ _ _ _ _ _ _ _).
      destruct P, H3, H5. subst. auto.
      Unshelve.
      all: auto.

  (* APP FUNEXP EXCEPTION *)
  * inversion H0; subst.
    - apply H in H4. destruct H4. congruence.
    - apply H in H9. auto.
    - apply H in H7. destruct H7. congruence.
    - apply H in H6. destruct H6. congruence.
    - apply H in H6. destruct H6. congruence.

  (* APP PARAM EXCEPTION *)
  * inversion H2; subst.
    - apply H in H6. destruct H6, H4. inversion H3. subst.
      epose (P := explist_prefix_eq_rev _ _ _ _ _ _ _ _ _ _ _ H0 H12 H1 _ _ _ _ _ _).
      inversion P.
      Unshelve.
      all: auto.
    - apply H in H11. destruct H11. congruence.
    - apply H in H9. destruct H9, H4. inversion H3. subst.
      epose (P := exception_equality _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H17 H1 H12
        _ _ _ _ _ _ _ _).
      destruct P, H6, H9. subst. auto.
      Unshelve.
      all: auto.
    - apply H in H8. destruct H8, H4. inversion H3. subst.
      epose (P := explist_prefix_eq_rev _ _ _ _ _ _ _ _ _ _ _ H0 H9 H1 _ _ _ _ _ _).
      inversion P.
      Unshelve.
      all: auto.
    - apply H in H8. destruct H8, H4. inversion H3. subst.
      epose (P := explist_prefix_eq_rev _ _ _ _ _ _ _ _ _ _ _ H0 H9 H1 _ _ _ _ _ _).
      inversion P.
      Unshelve.
      all: auto.

  (* APP BADFUN EXCEPTION *)
  * inversion H1; subst.
    - apply H in H5. destruct H5, H3. inversion H2. subst.
      congruence.
    - apply H in H10. destruct H10. congruence.
    - apply H in H8. destruct H8, H3. inversion H2. subst.
      pose (P := explist_prefix_eq _ _ _ _ _ _ _ _ _ _ _ e e0 H6 H4 e1 H7 H0 H11 H16).
      inversion P.
    - apply H in H7. destruct H7, H3. inversion H2. subst.
      pose (P := explist_equality _ _ _ _ _ _ _ H0 H8 H4 H5 e e0 e1 H6).
      destruct P. destruct H7. subst. auto.
    - apply H in H7. destruct H7, H3. inversion H2. subst.
      congruence.

  (* APP BADARITY EXCEPTION *)
  * inversion H1; subst.
    - apply H in H5. destruct H5, H3. inversion H2. subst.
      congruence.
    - apply H in H10. destruct H10. congruence.
    - apply H in H8. destruct H8, H3. inversion H2. subst.
      pose (P := explist_prefix_eq _ _ _ _ _ _ _ _ _ _ _ e e0 H6 H4 e1 H7 H0 H11 H16).
      inversion P.
    - apply H in H7. destruct H7, H3. inversion H2. subst.
      congruence.
    - apply H in H7. destruct H7, H3. inversion H2. subst.
      pose (P := explist_equality _ _ _ _ _ _ _ H0 H8 H4 H5 e e0 e1 H6).
      destruct P. destruct H7. subst. auto.

  (* LET EXCEPTION *)
  * inversion H0; subst.
    - apply H in H6. destruct H6. congruence.
    - apply H in H10. auto.

  (* SEQ EXCEPTION *)
  * inversion H0; subst.
    - apply H in H5. destruct H5. congruence.
    - apply H in H9. auto.


  (* MAP EXCEPTION *)
  * inversion H1; subst.
    - assert (length eff = length vals). 
      { 
        unfold vals.
        case_eq (modulo_2 (length eff)); intros.
        * rewrite e1 in *. rewrite length_make_map_vals. rewrite Nat.add_0_r in e0.
          2: lia. rewrite e0. simpl. apply n_div_2_mod_0. lia.
        * rewrite e1 in *. rewrite length_make_map_vals2. 2: lia.
          rewrite e. apply n_div_2_mod_1. lia.
      }
      rewrite H2 in H, H0.
      epose (P := explist_prefix_eq_rev _ _ _ _ _ _ _ _ _ _ _ H H7 H0 _ _ _ _ _ _).
      inversion P.
      Unshelve.
      + unfold vals, exps. rewrite length_make_map_exps.
        case_eq (modulo_2 (length eff)); intros.
        ** rewrite e1 in *. rewrite length_make_map_vals. rewrite Nat.add_0_r in e0.
           2: lia. rewrite e0. rewrite <- n_div_2_mod_0. lia. lia.
        ** rewrite e1 in *. rewrite length_make_map_vals2. 2: lia.
           rewrite e. rewrite <- n_div_2_mod_1. lia. lia.
      + lia.
      + unfold vals0. rewrite length_make_map_vals. 2: lia.
        unfold exps. rewrite length_make_map_exps. lia.
      + unfold exps. rewrite length_make_map_exps. lia.
      + unfold exps. rewrite length_make_map_exps. lia.
      + lia.
    - epose (P := exception_equality _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H11 H0 H8
        _ _ _ _ _ _ _ _).
      destruct P, H6, H9. subst. apply H0 in H11. auto.
      Unshelve.
      all: try lia.
      + unfold vals. case_eq (modulo_2 (length eff)); intros.
        ** rewrite e1 in *. rewrite length_make_map_vals. rewrite Nat.add_0_r in e0.
          2: lia. rewrite e0. rewrite <- n_div_2_mod_0. lia. lia.
        ** rewrite e1 in *. rewrite length_make_map_vals2. 2: lia.
          rewrite e. rewrite <- n_div_2_mod_1. lia. lia.
      + unfold exps. rewrite length_make_map_exps. lia.
      + unfold vals0. case_eq (modulo_2 (length eff4)); intros.
        ** rewrite e1 in *. rewrite length_make_map_vals. rewrite Nat.add_0_r in H5.
           2: lia. rewrite H5. rewrite <- n_div_2_mod_0. lia. lia.
        ** rewrite e1 in *. rewrite length_make_map_vals2. 2: lia.
           rewrite H4. rewrite <- n_div_2_mod_1. lia. lia.
      + unfold exps. rewrite length_make_map_exps. lia.
Qed.

Theorem eval_expr_determinism {env : Environment} {id id' : nat} {e : Expression} {eff eff' : SideEffectList} {v1 : ValueSequence + Exception} :
(
  |env, id, e, eff| -e> | id', v1, eff'|
->
  (forall v2 eff'' id'', |env, id, e, eff| -e> |id'', v2, eff''| -> v1 = v2 /\ eff' = eff''
      /\ id' = id'')
)
.
Proof.
  apply determinism_mutual.
Qed.

Theorem eval_singleexpr_determinism {env : Environment} {id id' : nat} {e : SingleExpression} {eff eff' : SideEffectList} {v1 : ValueSequence + Exception} :
(
  |env, id, e, eff| -s> | id', v1, eff'|
->
  (forall v2 eff'' id'', |env, id, e, eff| -s> |id'', v2, eff''| -> v1 = v2 /\ eff' = eff''
      /\ id' = id'')
)
.
Proof.
  apply determinism_mutual.
Qed.


(** Helper about variables contained in a list of expression *)
Proposition list_variables_not_in (x : Var) (exps : list Expression) :
~ In x ((flat_map variables exps)) ->
(forall exp : Expression, In exp exps -> ~ In x (variables exp)).
Proof.
  intros. induction exps.
  * inversion H0.
  * simpl in H. assert (~ In x (variables a) /\ ~ In x (flat_map variables exps)).
    {
      unfold not in *. split; intros.
      * apply H. apply in_or_app. left. assumption.
      * apply H. apply in_or_app. right. assumption.
    }
    inversion H1. inversion H0.
    - subst. assumption.
    - apply IHexps.
      + assumption.
      + assumption.
Qed.

(** Helpers regarding variables and their containment *)
Proposition var_not_in_neq (var s : Var):
  ~(In var (variables (EVar s))) ->
  s <> var.
Proof.
  intros. unfold not in *. intro. apply H. rewrite H0. simpl. left. reflexivity.
Qed.

Proposition var_neq_not_in (var s : Var) :
  s <> var -> 
  ~(In var (variables (EVar s))).
Proof.
  intros. unfold not in *. intro. destruct (string_dec s var).
  * exact (H e).
  * apply H. inversion H0.
    - assumption.
    - inversion H1.
Qed.

(** New variable binding doesn't affect previous ones *)
Proposition irrelevant_append (env : Environment) (s var : Var) (val : Value) (t : option ValueSequence):
  s <> var ->
  get_value env (inl s) = t <->
  get_value (append_vars_to_env [var] [val] env) (inl s) = t.
Proof.
  intros; split; intro.
  * simpl. induction env.
    - simpl in *. subst. apply eqb_neq in H. rewrite H. reflexivity.
    - destruct a. assert (get_value ((s0, v) :: env) (inl s) = t). { auto. }
      unfold get_value in H0. case_eq (var_funid_eqb (inl s) s0).
      + intro. rewrite H2 in H0. subst. inversion H2. destruct s0.
        ** apply eqb_eq in H3. subst. simpl. apply eqb_neq in H. rewrite H. simpl.
           rewrite eqb_refl. reflexivity.
        ** inversion H3.
      + intros. simpl in H1. destruct s0.
        ** inversion H2. rewrite H4 in H1. simpl. destruct ((v0 =? var)%string).
          ++ simpl. apply eqb_neq in H. rewrite H. assumption.
          ++ simpl. rewrite H4. apply eqb_neq in H. simpl. exact (IHenv H1).
        ** simpl. exact (IHenv H1).
  * simpl in H0. induction env.
    - simpl in H0. apply eqb_neq in H. rewrite H in H0. subst. simpl. reflexivity.
    - destruct a. simpl in *. case_eq (var_funid_eqb s0 (inl var)).
      + intro. destruct s0.
        ** inversion H1. apply eqb_eq in H3. rewrite H3. apply eqb_neq in H. rewrite H.
           rewrite H1 in H0. simpl in H0. rewrite H in H0. assumption.
        **  rewrite H1 in H0. simpl in H0. apply eqb_neq in H. rewrite H in H0. assumption.
      + intro. destruct s0.
        ** inversion H1. case_eq ((s =? v0)%string); intro.
          -- rewrite H1 in H0. simpl in H0. rewrite H2 in H0. assumption.
          -- rewrite H1 in H0. simpl in H0. rewrite H2 in H0. exact (IHenv H0).
        ** rewrite H1 in H0. simpl in H0. exact (IHenv H0).
Qed.

(** New variable binding doesn't affect previous ones *)
Proposition irrelevant_append_eq (env : Environment) (s var : Var) (val : Value):
  s <> var ->
  get_value env (inl s) = get_value (append_vars_to_env [var] [val] env) (inl s).
Proof.
  intros. pose (IRA := irrelevant_append env s var val (get_value env (inl s)) H).
  assert (get_value env (inl s) = get_value env (inl s)). reflexivity. inversion IRA.
  pose (P1 := H1 H0). apply eq_sym. assumption.
Qed.

(* Theorem variable_irrelevancy (env: Environment) (cl : Closures) (e : Expression) (t val : Value) (var : Var) :
  ~(In var (variables e)) -> (forall env' a b, t <> VClosure env' a b) ->
  |env, cl, e| -e> t <->
  |append_vars_to_env [var] [val] env, cl, e| -e> t.
Proof.
  intro. split; intro. 
  * induction H1 using eval_expr_ind_extended.
    - apply eval_lit.
    - assert (get_value env (inl s) = get_value (append_vars_to_env [var] [val] env) (inl s)). { apply (var_not_in_neq) in H. pose (irrelevant_append_eq env s var val H). assumption. } rewrite H1. apply eval_var.
    - admit.
    - pose (H0 (inl env) (snd (split l)) e).  unfold not in n. assert (VClosure (inl env) (snd (split l)) e = VClosure (inl env) (snd (split l)) e). reflexivity. pose (n H1). inversion f.
    - apply eval_tuple.
      + assumption.
      + intros. apply H3; try(assumption).
        ** simpl in H. apply (list_variables_not_in) with (exps := exps). assumption. apply in_combine_l in H4. assumption.
        ** intros.
Qed.*)

(** Last append result *)
Proposition get_value_here (env : Environment) (var : Var + FunctionIdentifier) (val : Value):
get_value (insert_value env var val) var = Some [val].
Proof.
  induction env.
  * simpl. rewrite var_funid_eqb_refl. reflexivity.
  * simpl. destruct a. case_eq (var_funid_eqb s var); intro.
    - simpl. rewrite var_funid_eqb_refl. reflexivity.
    - simpl. rewrite var_funid_eqb_sym, H. assumption.
Qed.

(** Previous append result *)
Proposition get_value_there (env : Environment) (var var' : Var + FunctionIdentifier) 
     (val : Value):
var <> var' ->
get_value (insert_value env var val) var' = get_value env var'.
Proof.
  intro. induction env.
  * simpl. apply var_funid_eqb_neq in H. rewrite var_funid_eqb_sym in H. rewrite H. reflexivity.
  * simpl. destruct a. case_eq (var_funid_eqb s var); intro.
    - apply var_funid_eqb_eq in H0. assert (var <> var'). auto. rewrite <- H0 in H.
      apply var_funid_eqb_neq in H. rewrite var_funid_eqb_sym in H. rewrite H. simpl. apply var_funid_eqb_neq in H1.
      rewrite var_funid_eqb_sym in H1. rewrite H1. reflexivity.
    - simpl. case_eq (var_funid_eqb var' s); intros.
      + reflexivity.
      + apply IHenv.
Qed.

End Proofs.