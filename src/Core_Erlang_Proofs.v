(* Require Core_Erlang_Determinism_Helpers. *)
Require Core_Erlang_Tactics.

From Coq Require Import Arith.PeanoNat.

(** Proofs about the semantics *)
Module Proofs.

(* Export Core_Erlang_Determinism_Helpers.Determinism_Helpers. *)
Export Core_Erlang_Semantics.Semantics.
Import Core_Erlang_Tactics.Tactics.

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
  * admit.

  (* VALUE LIST EXCEPTION *)
  * admit.

  (* SINGLE EXPRESSION *)
  * apply H. inversion H0. auto.

  (* NIL *)
  * inversion H. auto.

  (* LIT *)
  * inversion H. auto.

  (* VAR *)
  * inversion H. subst. auto.

  (* FUNID *)
  * inversion H. subst. auto.

  (* FUN *)
  * inversion H. auto.

  (* TUPLE *)
  * admit.

  (* CONS *)
  * inversion H1; subst.
    - apply H in H6. destruct H6, H3. inversion H2. subst.
      apply H0 in H11. destruct H11, H4. inversion H3. subst. auto.
    - apply H in H10. destruct H10. congruence.
    - apply H in H6. destruct H6, H3. inversion H2. subst.
      apply H0 in H11. destruct H11, H4. congruence.

  (* CASE *)
  * admit.

  (* CALL *)
  * admit.

  (* PRIMOP *)
  * admit.

  (* APP *)
  * admit.

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
  * admit.

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
  * admit.

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
  * admit.

  (* CALL *)
  * admit.

  (* PRIMOP *)
  * admit.

  (* APP FUNEXP EXCEPTION *)
  * admit.

  (* APP PARAM EXCEPTION *)
  * admit.

  (* APP BADFUN EXCEPTION *)
  * admit.

  (* APP BADARITY EXCEPTION *)
  * admit.

  (* LET EXCEPTION *)
  * inversion H0; subst.
    - apply H in H6. destruct H6. congruence.
    - apply H in H10. auto.

  (* SEQ EXCEPTION *)
  * inversion H0; subst.
    - apply H in H5. destruct H5. congruence.
    - apply H in H9. auto.


  (* MAP EXCEPTION *)
  * admit.

Admitted.

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








(* 

  intro. intro. intro. intro. intro. intro. intro. intro IND. induction IND.
  (* LITERAL, VARIABLE, FUNCTION SIGNATURE, FUNCTION DEFINITION *)
  1-4: intros; inversion H; try(inversion H0); subst; auto.
  * intros. inversion H. auto.

  (* TUPLE *)
  * intros. inversion H6; subst.
    - pose (LEQ := list_equality vals vals0 eff eff4 _ _ _ H2 H3 H11 H8 H9 H H0 H1 H10).
      inversion LEQ. inversion H5. subst. auto.
    - pose (P1 := H3 (Datatypes.length vals0) H8 (inr ex)
          (eff'')).
      pose (EU := @eff_until_i env eff eff4 exps vals vals0 eff1 _ _ id _ _ _
               H H0 H10 H8 H1 H11 H3 H12 H15). inversion EU.

  (* LIST *)
  * intros. inversion H.
    - subst. pose (IH1 := IHIND1 (inl tlv0) eff4 _ H4). 
      inversion IH1. destruct H1. inversion H0. subst.
      pose (IH2 := IHIND2 (inl hdv0) (eff'') _ H9). inversion IH2. destruct H2.
      inversion H1. inversion H. subst. auto.
    - subst. pose (IH1 := IHIND1 (inr ex) (eff'') _ H8). inversion IH1. inversion H0.
    - subst.
      pose (IH1 := IHIND1 (inl vtl) (eff4) _ H4).
      inversion IH1. destruct H1. subst.
      pose (IH2 := IHIND2 (inr ex) eff'' _ H9). inversion IH2. inversion H1.

  (* CASE *)
  * intros. inversion H8. 
    - subst.
      pose (LEQ := list_equality vals vals0 _ _ _ _ _ H2 H3 H14 H11 H12 H H0 H1 H13).
      destruct LEQ. destruct H10. subst.
      assert (match_clause vals0 l i = Some (guard, exp, bindings)). { auto. }
      pose (IEQ := index_case_equality i i0 guard guard0 exp exp0 bindings bindings0 
                   _ _ H7 H17 H5 H16 H20 IND1 IHIND1).
      rewrite IEQ, H16 in H9. inversion H9. rewrite H18, H19, H21 in *.
      apply IHIND2 in H25. destruct H25. destruct H22. auto.
    - subst.
      pose (P1 := H3 (Datatypes.length vals0) H11 (inr ex)
          (eff'')).
      pose (EU := @eff_until_i env eff _ exps vals vals0 eff1 _ _ id _ _ _
               H H0 H13 H11 H1 H14 H3 H17 H22). inversion EU.
    - subst. 
      pose (LEQ := list_equality vals vals0 _ _ _ _ _ H2 H3 H14 H11 H12 H H0 H1 H13).
      destruct LEQ. destruct H10. subst.
      pose (EE := H23 i H4 guard exp bindings H5).
      pose (IHE := IHIND1 _ _ _ EE). inversion IHE. inversion H9.

  (* CALL *)
  * intros. inversion H6.
    - subst.
      pose (LEQ := list_equality vals vals0 eff eff4 _ _ _ H2 H3 H12 H9 H10 H H0 H1 H11).
      destruct LEQ. destruct H7. subst. rewrite H4 in H15. inversion H15.
      subst. auto.
    - subst. pose (P1 := H3 (Datatypes.length vals0) H9 (inr ex)
                            eff'').
      pose (EU := @eff_until_i env eff eff4 params vals vals0 eff1 _ _ id _ _ _ 
                H H0 H11 H9 H1 H12 H3 H15 H20). inversion EU.

  (* APPLY *)
  * intros. inversion H5.
    - subst. apply IHIND1 in H9. inversion H9. destruct H7.
      inversion H6. subst.
      pose (EQ := list_equality vals vals0 eff eff6 _ _ _ H3 H4 H15 H8 H11 H H1 H2 H12).
      inversion EQ. destruct H13. subst.
      apply IHIND2 in H20. destruct H20. destruct H13. auto.
    - subst. apply IHIND1 in H14. inversion H14. congruence.
    - subst. apply IHIND1 in H12. destruct H12. destruct H7.
      inversion H6. subst.
      pose (P1 := @eff_until_i env eff eff6 params vals vals0 _ _ _ _ _ _ _
                H H1 H10 H8 H2 H11 H4 H15 H20).
      inversion P1.
    - subst. apply IHIND1 in H11. inversion H11. inversion H6. subst.
      pose (P := H13 ref ext var_list body). congruence.
    - subst. apply IHIND1 in H11. inversion H11. inversion H6. subst. congruence.

  (* LET *)
  * intros. inversion H4. subst.
   - rewrite <- split_length_r in *.
     pose (LEQ := list_equality vals vals0 eff eff0 _ _ _ H2 H3 H12 H7 H8 H H0 H1 H9).
     destruct LEQ. destruct H6. subst.
     pose (IH1 := IHIND v2 eff'' _ H17). assumption.
   - subst. rewrite <- split_length_r in *.
     pose (EU := @eff_until_i env eff eff4 (snd (split l)) vals vals0 _ _ _ _ _ _ _
                 H H0 H9 H7 H1 H10 H3 H13 H18). inversion EU.

  (* DO (SEQUENCING) *)
  * intros. inversion H; subst.
    - apply IHIND1 in H4. destruct H4. destruct H1. subst.
      apply IHIND2 in H9. destruct H9. destruct H2. subst. auto.
    - apply IHIND1 in H8. destruct H8. congruence.

  (* LETREC *)
  * intros. inversion H. 
    - subst. pose (IH2 := IHIND v2 (eff'') _ H8). destruct IH2. destruct H1.
      subst. auto.

  (* MAP *)
  * intros. inversion H12.
    - subst.
      rewrite <- split_length_l in H, H0, H1, H2, H3, H14, H15, H16, H17.
      rewrite <- split_length_r in H6, H4, H18, H19.
      pose (MEQ := map_lists_equality kvals vvals kvals0 vvals0 eff1
                   eff eff4 ids ids0 id H4 H6 (length_split_eq l) H H0 H1 H2 H18 H19 H14 H15 H16 H17).
      destruct MEQ. destruct H10. destruct H11. subst. rewrite H7 in H20. inversion H20. subst. auto.
    -
      assert (| env, last ids0 id, nth i (fst (split l)) ErrorExp, last eff4 eff1 | 
              -e> | id'', inr ex, eff'' |
              \/
              | env, last ids0 id, nth i (fst (split l)) ErrorExp, last eff4 eff1 | 
              -e> | id'', inl ErrorValue, eff'' |
              /\
              | env, id'', nth i (snd (split l)) ErrorExp, eff'' | -e> 
              | id'', inr ex, eff'' |). { left. exact H23. }
      assert (Datatypes.length vvals0 < Datatypes.length (snd (split l))). { rewrite split_length_r in *. omega. }
      rewrite <- split_length_l in H, H0, H1, H2, H3, H14.
      rewrite <- split_length_r in H4, H6.
      pose (MEQ := map_lists_equal_until_i kvals vvals kvals0 vvals0 
                   i eff1 eff eff4 ex eff'' eff'' ErrorValue _ _ _ _ _ H4 H6 (length_split_eq l) H H0 H1 H2
                   H19 H20 H15 H16 (Nat.lt_le_incl _ _ H14) H17 H18 H28).
      destruct MEQ. destruct H31. destruct H32. destruct H33. subst.
      rewrite (last_nth_equal ids0 id 0), (last_nth_equal eff4 eff1 []), H17, H18, Nat.mul_comm in H23.
      pose (IH1 := H4 (length vvals0) H29 (inr ex)
                   _ _ H23).
      destruct IH1. congruence.
    -
      assert (| env, last ids0 id, nth i (fst (split l)) ErrorExp, last eff5 eff1 |
              -e> | id'0, inr ex, eff3 |
              \/
              | env, last ids0 id, nth i (fst (split l)) ErrorExp, last eff5 eff1 |
              -e> | id'0, inl val, eff3 |
              /\
              | env, id'0, nth i (snd (split l)) ErrorExp, eff3 |
              -e> | id'', inr ex,  eff'' |). { auto. }
      rewrite <- split_length_l in H, H0, H1, H2, H3, H14.
      rewrite <- split_length_r in H4, H6.
      pose (MEQ := map_lists_equal_until_i kvals vvals kvals0 vvals0 i eff1 eff eff5 ex
                   eff3 eff'' val ids ids0 _ _ _ H4 H6 (length_split_eq l) H H0 H1 H2 H19 H20 H15 H16
                   (Nat.lt_le_incl _ _ H14) H17 H18 H29).
      destruct MEQ. destruct H31. destruct H32. destruct H33. subst.
      assert (Datatypes.length vvals0 < Datatypes.length (snd (split l))). { omega. }
      rewrite (last_nth_equal ids0 id 0), (last_nth_equal eff5 eff1 []), H17, H18, Nat.mul_comm in H21.
      pose (IH1 := H4 (length vvals0) H8 _ _ _ H21). destruct IH1. destruct H11.
      inversion H10. subst.
      pose (IH2 := H6 (length vvals0) H8 (inr ex) _ _ H24). destruct IH2. congruence.


  (* LIST HEAD EXCEPTION *)
  * intros. inversion H; subst.
    - pose (IH := IHIND (inl tlv) eff3 _ H4). inversion IH. congruence.
    - apply IHIND. assumption.
    - pose (IH := IHIND (inl vtl) eff3 _ H4). inversion IH. congruence.

  (* LIST TAIL EXCEPTION *)
  * intros. inversion H; subst.
    - pose (IH1 := IHIND1 (inl tlv) eff4 _ H4). inversion IH1.
      destruct H1. inversion H0. subst.
      pose (IH2 := IHIND2 (inl hdv) eff'' _ H9). inversion IH2. congruence.
    - pose (IH1 := IHIND1 (inr ex0) eff'' _ H8). inversion IH1. congruence.
    - pose (IH1 := IHIND1 (inl vtl0) eff4 _ H4). destruct IH1. destruct H1.
      inversion H1. subst.
      apply IHIND2. assumption.

  (* TUPLE EXCEPTION *)
  * intros. inversion H5.
    - subst.
      pose (EU := @eff_until_i_rev env eff _ exps vals vals0 eff1 ids ids0 id _ _ _
               H4 H10 IHIND H H1 H7 H8 H9 H2). inversion EU.
    -
      pose (EE := exception_equality vals vals0 ex eff1 eff _ i
             i0 _ ex0 _ _ _ _ _ _ H4 H14 IHIND H11 H0 H H1 H8 H7 H9 H2 H10).
      destruct EE. destruct H20. inversion H21. subst.
      apply (IHIND (inr ex0) _ _ H14).

  (* CORECT TRY *)
  * intros. inversion H4.
    - subst.
      rewrite <- split_length_l in *.
      pose (LEQ := @list_equality env (fst (split l)) eff1 vals vals0 eff eff0 _ _ _ H2 H3 H20 H17 H18 H H0 H1 H19). destruct LEQ. destruct H6. subst. 
      pose (IH := IHIND _ _ _ H21). destruct IH. destruct H6.
      subst. auto.
    - subst.
      rewrite <- split_length_l in *.
      pose (EU := @eff_until_i env eff _ (fst (split l)) vals vals0 eff1 ids ids0 id id'' ex _ H H0 H19 H11 H1 H20 H3 H21 H22).
      inversion EU.

  (* CORRECT CATCH *)
  * intros. inversion H5.
    - subst. 
      rewrite <- split_length_l in *.
      pose (EU := @eff_until_i_rev env eff eff0 (fst (split l)) vals vals0 eff1 ids ids0 id _ _ _ H4 H21 IHIND1 H H1 H18 H19 H20 H2).
      inversion EU.
    - rewrite <- split_length_l in *.
      pose (EE := @exception_equality env (fst (split l)) vals vals0 ex eff1 eff _ i i0 _ ex0 _ _ _ _ _ _ H4 H23 IHIND1 H22 H0 H H1 H15 H12 H20 H2 H21). destruct EE. destruct H26. destruct H27. subst.
      pose (IH1 := IHIND1 _ _ _ H23). destruct IH1. destruct H6. inversion H0. subst.
      pose (IH2 := IHIND2 _ _ _ H24). destruct IH2. destruct H7. subst. auto.


  (* CASE EXCEPTIONS *)
  (** binding expression exception *)
  * intros. inversion H5.
    - subst.
      pose (EU := @eff_until_i_rev env eff _ exps vals vals0 eff1 ids ids0 id _ _ _
               H4 H11 IHIND H H1 H8 H9 H10 H2). inversion EU.
    - subst.
      pose (EE := exception_equality vals vals0 ex eff1 eff _ _
             _ _ ex0 _ _ _ _ _ _ H4 H19 IHIND H14 eq_refl H H1 eq_refl H8 H10 H2 H11).
      destruct EE. destruct H6. inversion H7. subst.
      apply (IHIND (inr ex0) _ _ H19).
    - subst.
      pose (EU := @eff_until_i_rev env eff _ exps vals vals0 eff1 ids ids0 id _ _ _
               H4 H11 IHIND H H1 H8 H9 H10 H2). inversion EU.

  (** no matching clause *)
  * intros. inversion H8.
    - subst.
      pose (LEQ := list_equality vals vals0 _ _ _ _ _ H2 H3 H14 H11 H12 H H0 H1 H13).
      destruct LEQ. destruct H5. subst.
      pose (WRONG := H7 i H15 _ _ _ H16 _ _ _ H20).
      inversion WRONG. inversion H4.
    - subst.
      pose (P1 := H3 (Datatypes.length vals0) H11 (inr ex)
          (eff'')).
      pose (EU := @eff_until_i env eff _ exps vals vals0 eff1 _ _ id _ _ _
               H H0 H13 H11 H1 H14 H3 H17 H22). inversion EU.
    - subst. 
      pose (LEQ := list_equality vals vals0 _ _ _ _ _ H2 H3 H14 H11 H12 H H0 H1 H13).
      destruct LEQ. destruct H5. subst.
      auto.

  (* CALL EXCEPTION *)
  * intros. inversion H5.
    - subst.
      pose (EU := @eff_until_i_rev env eff _ params vals vals0 eff1 ids ids0 id _ _ _
              H4 H11 IHIND H H1 H8 H9 H10 H2). inversion EU.
    - apply IHIND.
      pose (EEQ := exception_equality vals vals0 ex eff1 eff _ i
             i0 _ ex0 _ _ _ _ _ _ H4 H19 IHIND H14 H0 H H1 H9 H8 H10 H2 H11).
      destruct EEQ. destruct H21. destruct H22. subst. assumption.

  (* APPLY EXCEPTION *)
  (* name evaluates to an exception *)
  * intros. inversion H.
    - subst. pose (IH := IHIND _ _ _ H3). inversion IH. congruence.
    - subst. apply IHIND. assumption.
    - subst. pose (IH := IHIND _ _ _ H6). inversion IH. congruence.
    - subst. pose (IH := IHIND _ _ _ H5). inversion IH. congruence.
    - subst. pose (IH := IHIND _ _ _ H5). inversion IH. congruence.

  (* parameter exception *)
  * intros. inversion H5.
    - subst. apply IHIND1 in H9. destruct H9. destruct H6. inversion H0.
      subst.
      pose (P1 := @eff_until_i_rev env eff _ params vals vals0 _ ids ids0 id'0 _ _ _
                   H4 H15 IHIND2 H H1 H8 H11 H12 H2). inversion P1.
    - subst. apply IHIND1 in H14. inversion H14. congruence.
    - apply IHIND1 in H12. destruct H12. destruct H21. inversion H12.
      rewrite H21, H22, H24 in *.
      assert (| env, last ids0 id'0, nth i0 params ErrorExp, last eff6 eff4 | -e> | id''0, inr ex0, eff'' |). { assumption. }
      pose (EE := exception_equality vals vals0 ex _ eff _ i i0 _ ex0
                 _ _ _ _ _ _ H4 H20 IHIND2 H15 (eq_sym H0) H H1 (eq_sym H9) H8 H10 H2 H11).
      destruct EE. destruct H26. destruct H27. subst.
      apply IHIND2 in H23.
      assumption.
    - subst. apply IHIND1 in H11. destruct H11. inversion H0. destruct H6.
      subst.
      pose (P1 := @eff_until_i_rev env eff _ params vals vals0 _ ids ids0 id'0 _ _ _
                 H4 H12 IHIND2 H H1 H8 H9 H10 H2). inversion P1.
    - subst. apply IHIND1 in H11. destruct H11. inversion H0. destruct H6.
      subst.
      pose (P1 := @eff_until_i_rev env eff _ params vals vals0 _ ids ids0 id'0 _ _ _
                 H4 H12 IHIND2 H H1 H8 H9 H10 H2). inversion P1.

  (* name evaluate to a non-closure value *)
  * intros. inversion H7.
    - apply IHIND in H11. destruct H11. destruct H23. inversion H11.
      pose (P := H4 ref ext var_list body _ H26). inversion P.
    - subst. apply IHIND in H16. inversion H16. congruence.
    - subst. apply IHIND in H14. destruct H14. inversion H5. destruct H6.
      subst.
      pose (P1 := @eff_until_i env eff _ params vals vals0 _ ids ids0 id'0 id''0 ex _
                         H H0 H12 H10 H1 H13 H3 H17 H22). inversion P1.
    - subst. apply IHIND in H13. destruct H13. inversion H5. destruct H6. subst.
      pose (LEQ := @list_equality env params _ vals vals0 eff _ _ _ _
                     H2 H3 H14 H10 H11 H H0 H1 H12).
      destruct LEQ. destruct H8. subst. auto.
    - subst. apply IHIND in H13. destruct H13. inversion H5. destruct H6. subst.
      pose (P := H4 ref ext var_list body). congruence.

  (* paramlist is too short/long *)
  * intros. inversion H7.
    - subst. 
      pose (P1 := IHIND _ _ _ H11). destruct P1. destruct H6. inversion H5. subst.
      pose (EL:= list_equality vals vals0 eff _ _ _ _ H2 H3 H17 H10 H13 H H0 H1 H14).
      destruct EL. destruct H8. subst. intuition. 
    - subst. pose (IH := IHIND _ _ _ H16). inversion IH. congruence.
    - subst.
      pose (P1 := IHIND _ _ _ H14). destruct P1. destruct H6. inversion H5. subst.
      pose (P2 := @eff_until_i env eff _ params vals vals0 _ ids ids0 id'0 id''0 ex _
                     H H0 H12 H10 H1 H13 H3 H17 H22). inversion P2.
    - subst.
      pose (P1 := IHIND _ _ _ H13). destruct P1. destruct H6. inversion H5. subst.
      pose (P2 := H15 ref ext var_list body).
      congruence.
    - subst.
      pose (P1 := IHIND _ _ _ H13). destruct P1. destruct H6. inversion H5. subst.
      pose (EL:= list_equality vals vals0 eff _ _ _ _ H2 H3 H14 H10 H11 H H0 H1 H12).
      destruct EL. destruct H8. subst. auto.

  
  (* LET EXCEPTION *)
  * intros. inversion H5.
    - subst.
      rewrite <- split_length_r in *.
      pose (EU := @eff_until_i_rev env eff _ (snd (split l)) vals vals0 eff1 ids ids0 _ _ _ _
                      H4 H13 IHIND H H1 H8 H9 H10 H2). inversion EU.
    - apply IHIND.
      rewrite <- split_length_r in *.
      pose (EEQ := exception_equality vals vals0 ex eff1 eff _
            i i0 _ ex0 _ _ _ _ _ _ H4 H19 IHIND H14 H0 H H1 H9 H8 H10 H2 H11).
      destruct EEQ. destruct H21. destruct H22. subst. assumption.

  (* DO EXCEPTION *)
  * intros. inversion H; subst.
    - apply IHIND in H4. destruct H4. congruence.
    - apply IHIND in H8. destruct H8. destruct H1. auto.

  (* MAP KEY EXCEPTION *)
  * intros. inversion H8.
    - 
      assert ((forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
               | env, last ids id, nth i (fst (split l)) ErrorExp, last eff eff1 | -e> |id'', v2, eff'' |
               ->
                inr ex = v2 /\ eff2 = eff'' /\ id' = id'')
               \/
            (forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
             | env, last ids id, nth i (fst (split l)) ErrorExp, last eff eff1 | -e> | id'', v2, eff'' | ->
             inl ErrorValue = v2 /\ eff2 = eff'' /\ id' = id'')
             /\
            (forall (v2 : Value + Exception) (eff'' : SideEffectList) (id''' : nat),
             | env, id', nth i (snd (split l)) ErrorExp, eff2 | -e> | id''', v2, eff'' | ->
             inr ex = v2 /\ [] = eff'' /\ id'' = id''')). { auto. }
     rewrite <- split_length_l in H, H12, H13, H10, H11.
     rewrite <- split_length_r in H14, H15.
     pose (MEQ := map_lists_equal_until_i_key_or_val kvals vvals kvals0 vvals0 i eff1 eff _ _
                        [] ErrorValue ex _ _ _ _ _ H5 H7 H27 (length_split_eq l) H0 H1 (Nat.lt_le_incl _ _ H) H2
                        H3 H14 H15 H10 H11 (eq_sym H12) (eq_sym H13)).
     destruct MEQ. destruct H29. destruct H30. destruct H31. subst.
     assert (Datatypes.length vvals0 < Datatypes.length (snd (split l))). { omega. }
     pose (ERR := H14 (length vvals0) H0).
     rewrite (last_nth_equal ids0 id 0), (last_nth_equal eff4 eff1 []) in IHIND.
     rewrite <- H12, <- H13, mult_comm, H10 in IHIND.
     pose (DIS := IHIND _ _ _ ERR). inversion DIS. congruence.
    - assert (| env, last ids0 id, nth i0 (fst (split l)) ErrorExp, last eff4 eff1 | 
              -e> | id'', inr ex0, eff'' | \/
              | env, last ids0 id, nth i0 (fst (split l)) ErrorExp, last eff4 eff1 | -e> 
              | id'', inl ErrorValue,
               eff'' | /\
               | env, id'', nth i0 (snd (split l)) ErrorExp, eff'' | -e> 
               | id'', inr ex0, eff'' |). { left. exact H19. }
      rewrite <- split_length_l in H, H10.
      pose (MEQ := map_lists_equal_until_i_key kvals vvals kvals0 vvals0 i i0 eff1 eff _ ex0 _
                   _ _ ErrorValue ex _ _ _ _ _ _ H5 H7 IHIND (length_split_eq l) H0 H1 (Nat.lt_le_incl _ _ H) H2
                   H3 H15 H16 H11 H12 (Nat.lt_le_incl _ _ H10) H13 H14 H24).
      destruct MEQ. destruct H26. destruct H27. destruct H28. subst.
      pose (IH1 := IHIND _ _ _ H19). inversion IH1. inversion H0.
      destruct H9. subst. auto.
    - assert (| env, last ids0 id, nth i0 (fst (split l)) ErrorExp, last eff5 eff1 |
              -e> | id'0, inr ex0, eff3 | \/
               | env, last ids0 id, nth i0 (fst (split l)) ErrorExp, last eff5 eff1 | -e> 
               | id'0, inl val,
               eff3 | /\
               | env, id'0, nth i0 (snd (split l)) ErrorExp, eff3 | -e> 
               | id'', inr ex0, eff'' |). { auto. }
      rewrite <- split_length_l in H, H10.
      pose (MEQ := map_lists_equal_until_i_key kvals vvals kvals0 vvals0 i i0 eff1 eff _ ex0 _
                   _ _ val ex _ _ _ _ _ _ H5 H7 IHIND (length_split_eq l) H0 H1 (Nat.lt_le_incl _ _ H) H2
                   H3 H15 H16 H11 H12 (Nat.lt_le_incl _ _ H10) H13 H14 H25).
      destruct MEQ. destruct H27. destruct H28. destruct H29. subst.
      pose (IH1 := IHIND _ _ _ H17). inversion IH1. congruence.

  (* MAP VALUE EXCEPTION *)
  * intros. inversion H8.
    - assert ((forall (v2 : Value + Exception) (eff'' : SideEffectList) (id''' : nat),
              | env, last ids id, nth i (fst (split l)) ErrorExp, last eff eff1 | -e> | id''', v2, eff'' | ->
              inr ex = v2 /\ eff2 = eff'' /\ id' = id''') \/
             (forall (v2 : Value + Exception) (eff'' : SideEffectList) (id''' : nat),
              | env, last ids id, nth i (fst (split l)) ErrorExp, last eff eff1 | -e> | id''', v2, eff'' | ->
              inl val = v2 /\ eff2 = eff'' /\ id' = id''') /\
             (forall (v2 : Value + Exception) (eff'' : SideEffectList) (id''' : nat),
              | env, id', nth i (snd (split l)) ErrorExp, eff2 | -e> | id''', v2, eff'' | ->
              inr ex = v2 /\ eff3 = eff'' /\ id'' = id''')). { right. split. exact IHIND1. exact IHIND2. }
      rewrite <- split_length_l in H, H10, H11, H12, H13.
      rewrite <- split_length_r in H14, H15.
      pose (MEQ := map_lists_equal_until_i_key_or_val kvals vvals kvals0 vvals0 i eff1 eff _ _
                  _ val ex _ _ _ _ _ H5 H7 H27 (length_split_eq l) H0 H1 (Nat.lt_le_incl _ _ H) H2
                  H3 H14 H15 H10 H11 (eq_sym H12) (eq_sym H13)).
      destruct MEQ. destruct H29. destruct H30. destruct H31. subst.
      assert (Datatypes.length vvals0 < Datatypes.length (snd (split l))). { omega. }
      pose (GOOD := H14 (length vvals0) H0).
      rewrite (last_nth_equal ids0 id 0), (last_nth_equal eff5 eff1 []) in IHIND1.
      rewrite <- H12, <- H13, mult_comm, H10 in IHIND1.
      pose (GOOD' := IHIND1 _ _ _ GOOD). inversion GOOD'. inversion H9. destruct H17. subst.
      pose (BAD := H15 (length vvals0) H0).
      pose (BAD' := IHIND2 _ _ _ BAD). inversion BAD'. congruence.
    - assert (| env, last ids0 id, nth i0 (fst (split l)) ErrorExp, last eff5 eff1 | -e> 
      | id''0, inr ex0, eff'' | \/
              | env, last ids0 id, nth i0 (fst (split l)) ErrorExp, last eff5 eff1 | -e> 
              | id''0, inl ErrorValue, eff'' | /\
              | env, id''0, nth i0 (snd (split l)) ErrorExp, eff'' | -e> | 
              id''0, inr ex0, eff'' |). { auto. }
      rewrite <- split_length_l in H, H10.
      pose (MEQ := map_lists_equal_until_i_val kvals vvals kvals0 vvals0 i i0 eff1 eff _ ex0 _ _
                   _ _ val ErrorValue ex _ _ _ _ _ _ _ H5 H7 IHIND1 IHIND2 (length_split_eq l) H0 H1 (Nat.lt_le_incl _ _ H) H2
                   H3 H15 H16 H11 H12 (Nat.lt_le_incl _ _ H10) H13 H14 H24).
      destruct MEQ. destruct H26. destruct H27. destruct H28. subst.
      pose (IH1 := IHIND1 _ _ _ H19). inversion IH1. congruence.
    - assert (| env, last ids0 id, nth i0 (fst (split l)) ErrorExp, last eff6 eff1 | -e> | id'0, inr ex0, eff4 | \/
              | env, last ids0 id, nth i0 (fst (split l)) ErrorExp, last eff6 eff1 | -e> | id'0, inl val0, eff4 | /\
              | env, id'0, nth i0 (snd (split l)) ErrorExp, eff4 | -e> | id''0,
              inr ex0, eff'' |). { auto. }
      rewrite <- split_length_l in H, H10.
      pose (MEQ := map_lists_equal_until_i_val kvals vvals kvals0 vvals0 i i0 eff1 eff _ ex0 _ _
                   _ _ val val0 ex _ _ _ _ _ _ _ H5 H7 IHIND1 IHIND2 (length_split_eq l) H0 H1 (Nat.lt_le_incl _ _ H) H2
                   H3 H15 H16 H11 H12 (Nat.lt_le_incl _ _ H10) H13 H14 H25).
      destruct MEQ. inversion H27. destruct H29. destruct H30. subst.
      pose (IH1 := IHIND1 _ _ _ H17). destruct IH1. inversion H0. destruct H9. subst.
      pose (IH2 := IHIND2 _ _ _ H20). assumption.
Qed. *)

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
Proposition irrelevant_append (env : Environment) (s var : Var) (val : Value) (t : Value + Exception):
  s <> var ->
  get_value env (inl s) = t <->
  get_value (append_vars_to_env [var] [val] env) (inl s) = t.
Proof.
  intros; split; intro.
  * simpl. induction env.
    - simpl in *. subst. apply eqb_neq in H. rewrite H. reflexivity.
    - destruct a. assert (get_value ((s0, v) :: env) (inl s) = t). { auto. }
      unfold get_value in H0. case_eq (uequal (inl s) s0).
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
    - destruct a. simpl in *. case_eq (uequal s0 (inl var)).
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
get_value (insert_value env var val) var = inl val.
Proof.
  induction env.
  * simpl. rewrite uequal_refl. reflexivity.
  * simpl. destruct a. case_eq (uequal s var); intro.
    - simpl. rewrite uequal_refl. reflexivity.
    - simpl. rewrite uequal_sym, H. assumption.
Qed.

(** Previous append result *)
Proposition get_value_there (env : Environment) (var var' : Var + FunctionIdentifier) 
     (val : Value):
var <> var' ->
get_value (insert_value env var val) var' = get_value env var'.
Proof.
  intro. induction env.
  * simpl. apply uequal_neq in H. rewrite uequal_sym in H. rewrite H. reflexivity.
  * simpl. destruct a. case_eq (uequal s var); intro.
    - apply uequal_eq in H0. assert (var <> var'). auto. rewrite <- H0 in H.
      apply uequal_neq in H. rewrite uequal_sym in H. rewrite H. simpl. apply uequal_neq in H1.
      rewrite uequal_sym in H1. rewrite H1. reflexivity.
    - simpl. case_eq (uequal var' s); intros.
      + reflexivity.
      + apply IHenv.
Qed.

End Proofs.