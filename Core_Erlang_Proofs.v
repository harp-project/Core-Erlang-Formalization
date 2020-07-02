Load Core_Erlang_Determinism_Helpers.

From Coq Require Import Arith.PeanoNat.

(** Proofs about the semantics *)
Module Core_Erlang_Proofs.

Import Core_Erlang_Syntax.
Import Core_Erlang_Semantics.
Import Core_Erlang_Environment.
Import Core_Erlang_Helpers.
Import Core_Erlang_Equalities.
Import Core_Erlang_Side_Effects.
Import Core_Erlang_Determinism_Helpers.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.
Import Coq.Init.Logic.
Import Omega.

Proposition plus_comm_basic {e1 e2 t : Value} {eff : SideEffectList} : 
eval "plus"%string [e1 ; e2] eff = (inl t, eff)
->
eval "plus"%string [e2; e1] eff = (inl t, eff).
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(reflexivity || inversion H1).
  all: try(destruct l); try(destruct l0); try(reflexivity || inversion H1).
  * unfold eval. simpl. rewrite <- Z.add_comm. reflexivity.
Qed.

Proposition plus_comm_basic_value {e1 e2 v : Value} (eff eff2 : SideEffectList) : 
  eval "plus"%string [e1 ; e2] eff = (inl v, eff)
->
  eval "plus"%string [e2; e1] eff2 = (inl v, eff2).
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(reflexivity || inversion H1).
  all: try(destruct l); try(destruct l0); try(reflexivity || inversion H1).
  * unfold eval. simpl. rewrite <- Z.add_comm. reflexivity.
Qed.

Proposition plus_comm_extended {e1 e2 : Value} (v : Value + Exception) (eff eff2 : SideEffectList) : 
  eval "plus"%string [e1 ; e2] eff = (v, eff)
->
  exists v', eval "plus"%string [e2; e1] eff2 = (v', eff2).
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  1-7, 9-36: eexists; try(inversion H1; reflexivity).
  1-5: try(destruct l); try(inversion H1; reflexivity).
  destruct l, l0.
  1-3: eexists. try(inversion H1; reflexivity).
  reflexivity.
  reflexivity.
  * eexists. reflexivity.
Qed.

Proposition plus_effect_unmodified {e1 e2 : Value} (v' : Value + Exception) (eff eff2 : SideEffectList) :
  eval "plus"%string [e1 ; e2] eff = (v', eff2)
->
  eff = eff2.
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(inversion H1; reflexivity).
  all: try(destruct l); try(inversion H1; reflexivity).
  all: destruct l0.
  1-3: inversion H1; auto.
  inversion H1. auto.
Qed.

Proposition plus_effect_changeable {v1 v2 : Value} (v' : Value + Exception) (eff eff2 : SideEffectList) :
  eval "plus"%string [v1; v2] eff = (v', eff)
->
  eval "plus"%string [v1; v2] eff2 = (v', eff2).
Proof.
  intros. simpl in *. case_eq v1; case_eq v2; intros; subst.
  all: try(inversion H; reflexivity).
  all: try(destruct l); try(inversion H; reflexivity).
  all: destruct l0; inversion H; auto.
Qed.

Import Arith.PeanoNat.

Theorem determinism : forall {env : Environment} {e : Expression} {v1 : Value + Exception} 
    {id id' : nat} {eff eff' : SideEffectList}, 
  |env, id, e, eff| -e> | id', v1, eff'|
->
  (forall v2 eff'' id'', |env, id, e, eff| -e> |id'', v2, eff''| -> v1 = v2 /\ eff' = eff'' /\ id' = id'').
Proof.
  intro. intro. intro. intro. intro. intro. intro. intro IND. induction IND.
  (* LITERAL, VARIABLE, FUNCTION SIGNATURE, FUNCTION DEFINITION *)
  1-4: intros; inversion H; subst; auto.
  * intros. inversion H. auto.

  (* TUPLE *)
  * intros. inversion H6; subst.
    - pose (LEQ := list_equality vals vals0 eff eff4 _ _ _ H2 H3 H11 H8 H9 H H0 H1 H10).
      inversion LEQ. inversion H5. subst. auto.
    - pose (P1 := H3 (Datatypes.length vals0) H9 (inr ex)
          (concatn eff1 eff5 (Datatypes.length vals0) ++ eff3)).
      pose (EU := @eff_until_i env eff eff5 exps vals vals0 eff1 _ _ id _ _ _ H H0 H10 H9 H1 H11 H3 H12 H16). inversion EU.

  (* LIST *)
  * intros. inversion H0. 
    - subst. pose (IH1 := IHIND1 (inl tlv0) (eff1 ++ eff5) _ H6). 
      inversion IH1. destruct H1. apply app_inv_head in H1. subst.
      pose (IH2 := IHIND2 (inl hdv0) (eff1 ++ eff5 ++ eff6) _ H11). inversion IH2. destruct H2.
      apply app_inv_head, app_inv_head in H2. inversion H1. inversion H. subst. auto.
    - subst. pose (IH1 := IHIND1 (inr ex) (eff1 ++ eff5) _ H10). inversion IH1. inversion H.
    - subst.
      pose (IH1 := IHIND1 (inl vtl) (eff1 ++ eff5) _ H6).
      inversion IH1. destruct H1. apply app_inv_head in H1. subst.
      pose (IH2 := IHIND2 (inr ex) (eff1 ++ eff5 ++ eff6) _ H11). inversion IH2. inversion H1.

  (* CASE *)
  * intros. inversion H6. 
    - subst. apply IHIND1 in H13. inversion H13. inversion H5. destruct H7. apply app_inv_head in H7. subst.
      assert (match_clause v0 patts guards bodies i = Some (guard, exp, bindings)). { auto. }
      pose (IEQ := index_case_equality i i0 guard guard0 exp exp0 bindings bindings0 
                   (eff1 ++ eff5) _ H4 H18 H2 H15 H24 IND2 IHIND2). rewrite IEQ in H7.
      rewrite H15 in H7. inversion H7. rewrite H9, H10, H16 in *.
      apply IHIND3 in H25. destruct H25. destruct H17.
      apply app_inv_head, app_inv_head in H17. rewrite H8, H17. auto.
    - subst. apply IHIND1 in H20. inversion H20. inversion H5. 
    - subst. apply IHIND1 in H20. inversion H20. destruct H7. apply app_inv_head in H7. inversion H5.
      subst. pose (EE := H21 i H1 guard exp bindings H2).
      pose (IHE := IHIND2 _ _ _ EE). inversion IHE. inversion H7.

  (* CALL *)
  * intros. inversion H6.
    - subst.
      pose (LEQ := list_equality vals vals0 eff eff4 _ _ _ H2 H3 H12 H9 H10 H H0 H1 H11).
      destruct LEQ. destruct H7. subst. rewrite H4 in H15. inversion H15.
      subst. auto.
    - subst. pose (P1 := H3 (Datatypes.length vals0) H10 (inr ex)
                            (concatn eff1 eff5 (Datatypes.length vals0) ++ eff3)).
      pose (EU := @eff_until_i env eff eff5 params vals vals0 eff1 _ _ id _ _ _ H H0 H11 H10 H1 H12 H3 H13 H21). inversion EU.

  (* APPLY *)
  * intros. inversion H6.
    - subst. apply IHIND1 in H10. inversion H10. destruct H7.
      apply app_inv_head in H7. inversion H5. subst.
      pose (EQ := list_equality vals vals0 eff eff8 _ _ _ H3 H4 H14 H9 H12 H H1 H2 H13).
      inversion EQ. destruct H8. subst.
      apply IHIND2 in H22. destruct H22. destruct H8. auto.
    - subst. apply IHIND1 in H16. inversion H16. congruence.
    - subst. apply IHIND1 in H13. destruct H13. destruct H7.
      inversion H5. apply app_inv_head in H7. subst.
      pose (P1 := @eff_until_i env eff eff8 params vals vals0 _ _ _ _ _ _ _ H H1 H11 H10 H2 H12 H4 H14 H22).
      inversion P1.
    - subst. apply IHIND1 in H12. inversion H12. inversion H5. subst.
      pose (P := H14 ref ext var_list body). congruence.
    - subst. apply IHIND1 in H12. inversion H12. inversion H5. subst. congruence.

  (* LET *)
  * intros. inversion H5. subst.
   - pose (LEQ := list_equality vals vals0 eff eff0 _ _ _ H2 H3 H14 H9 H10 H H0 H1 H11). destruct LEQ. destruct H6. subst.
     pose (IH1 := IHIND v2 (concatn eff1 eff0 (Datatypes.length exps) ++ eff5) _ H20). assumption.
   - subst. pose (EU := @eff_until_i env eff eff6 exps vals vals0 _ _ _ _ _ _ _ H H0 H11 H10  H1 H12 H3 H15 H21). inversion EU.

  (* LETREC *)
  * intros. inversion H2. 
    - subst. pose (IH2 := IHIND v2 (eff1 ++ eff4) _ H15). destruct IH2. destruct H3.
      apply app_inv_head in H3. subst. auto.

  (* MAP *)
  * intros. inversion H11.
    - subst. pose (MEQ := map_lists_equality kvals vvals kvals0 vvals0 eff1
                   eff eff4 ids ids0 id H6 H8 H H0 H1 H2 H3 H20 H21 H15 H16 H17 H18).
      destruct MEQ. destruct H10. destruct H12. subst. rewrite H4 in H19. inversion H19. auto.
    - rewrite H24 in H29.
      assert (| env, last ids0 id, nth i kl ErrorExp, concatn eff1 eff5 (2 * i) | 
              -e> | id'', inr ex, concatn eff1 eff5 (2 * i) ++ eff3 |
              \/
              | env, last ids0 id, nth i kl ErrorExp, concatn eff1 eff5 (2 * i) | 
              -e> | id'', inl ErrorValue, concatn eff1 eff5 (2 * i) ++ eff3 |
              /\
              | env, id'', nth i vl ErrorExp, concatn eff1 eff5 (2 * i) ++ eff3 | -e> 
              | id'', inr ex, concatn eff1 eff5 (2 * i) ++ eff3 ++ [] |). { left. exact H29. }
      assert (Datatypes.length vvals0 < Datatypes.length vl). { omega. }
      pose (MEQ := map_lists_equal_until_i kvals vvals kvals0 vvals0 
                   i eff1 eff eff5 ex eff3 [] ErrorValue _ _ _ _ _ H6 H8 H14 H0 H1 H2 H3
                   H20 H21 H15 H16 (Nat.lt_le_incl _ _ H17) H18 H19 H30).
      destruct MEQ. destruct H33. destruct H34. destruct H35. subst.
      rewrite last_nth_equal, H19, Nat.mul_comm in H29.
      pose (IH1 := H6 (length vvals0) H31 (inr ex)
                   (concatn eff1 eff5 (2 * Datatypes.length vvals0) ++ eff3) _ H29).
      destruct IH1. congruence.
    - rewrite H25 in H30.
      assert (| env, last ids0 id, nth i kl ErrorExp, concatn eff1 eff6 (2 * i) |
              -e> | id'0, inr ex, concatn eff1 eff6 (2 * i) ++ eff3 |
              \/
              | env, last ids0 id, nth i kl ErrorExp, concatn eff1 eff6 (2 * i) |
              -e> | id'0, inl val, concatn eff1 eff6 (2 * i) ++ eff3 |
              /\
              | env, id'0, nth i vl ErrorExp, concatn eff1 eff6 (2 * i) ++ eff3 |
              -e> | id'', inr ex, concatn eff1 eff6 (2 * i) ++ eff3 ++ eff4 |). { auto. }
      pose (MEQ := map_lists_equal_until_i kvals vvals kvals0 vvals0 i eff1 eff eff6 ex
                   eff3 eff4 val _ _ _ _ _ H6 H8 H14 H0 H1 H2 H3 H20 H21 H15 H16
                   (Nat.lt_le_incl _ _ H17) H18 H19 H31).
      destruct MEQ. destruct H33. destruct H34. destruct H35. subst.
      assert (Datatypes.length vvals0 < Datatypes.length vl). { omega. }
      rewrite last_nth_equal, H19, Nat.mul_comm in H22.
      pose (IH1 := H6 (length vvals0) H9 _ _ _ H22). destruct IH1. destruct H12.
      inversion H10. subst. rewrite <- H12 in H30.
      pose (IH2 := H8 (length vvals0) H9 (inr ex) _ _ H30). destruct IH2. congruence.

  (* LIST HEAD EXCEPTION *)
  * intros. inversion H0; subst.
    - pose (IH := IHIND (inl tlv) (eff1 ++ eff4) _ H6). inversion IH. congruence.
    - apply IHIND. assumption.
    - pose (IH := IHIND (inl vtl) (eff1 ++ eff4) _ H6). inversion IH. congruence.

  (* LIST TAIL EXCEPTION *)
  * intros. inversion H0; subst.
    - pose (IH1 := IHIND1 (inl tlv) (eff1 ++ eff5) _ H6). inversion IH1.
      destruct H1. apply app_inv_head in H1. inversion H. subst.
      pose (IH2 := IHIND2 (inl hdv) (eff1 ++ eff5 ++ eff6) _ H11). inversion IH2. congruence.
    - pose (IH1 := IHIND1 (inr ex0) (eff1 ++ eff5) _ H10). inversion IH1. congruence.
    - pose (IH1 := IHIND1 (inl vtl0) (eff1 ++ eff5) _ H6). destruct IH1. destruct H1.
      apply app_inv_head in H1. inversion H. subst.
      apply IHIND2. assumption.

  (* TUPLE EXCEPTION *)
  * intros. inversion H6.
    - subst.
      pose (EU := @eff_until_i_rev env eff eff5 exps vals vals0 eff1 ids ids0 id _ _ _ H4 H11 IHIND H0 H1 H8 H9 H10 H2). inversion EU.
    - rewrite H13 in H16.
      pose (EE := exception_equality vals vals0 ex eff1 eff eff6 i
             i0 eff3 ex0 eff4 _ _ _ _ _ H4 H16 IHIND H12 H H0 H1 H8 H9 H10 H2 H11).
      destruct EE. destruct H22. inversion H23. subst.
      apply (IHIND (inr ex0) (concatn eff1 eff6 (Datatypes.length vals0) ++ eff4) _ H16).
  
  (* CORECT TRY *)
  * intros. inversion H0.
    - subst. apply IHIND2. pose (IH1 := IHIND1 (inl val'0) (eff1 ++ eff5) _ H14).
      destruct IH1. inversion H. destruct H1. apply app_inv_head in H1. subst. assumption.
    - subst. pose (IH1 := IHIND1 (inr ex) _ _ H14). inversion IH1. congruence.
  
  (* CORRECT CATCH *)
  * intros. inversion H0.
    - subst. pose (IH1 := IHIND1 (inl val') _ _ H14). destruct IH1. congruence.
    - subst. apply IHIND2. pose (IH1 := IHIND1 (inr ex0) _ _ H14). destruct IH1.
      inversion H. destruct H1. apply app_inv_head in H1. subst. assumption.

  (* CASE EXCEPTIONS *)
  (** binding expression exception *)
  * intros. inversion H2.
    - subst. apply IHIND in H9. inversion H9. congruence.
    - subst. apply IHIND in H16. assumption.
    - subst. apply IHIND in H16. inversion H16. congruence.

  (** no matching clause *)
  * intros. inversion H4.
    - subst. apply IHIND in H11. destruct H11. destruct H5. apply app_inv_head in H5. inversion H1.
      subst. pose (EE := H3 i H12 guard exp bindings H13).
      pose (IHE := EE _ _ _ H22). inversion IHE. inversion H5.
    - subst. apply IHIND in H18. inversion H18. congruence.
    - subst. apply IHIND in H18. inversion H18. destruct H5. apply app_inv_head in H5. inversion H1. subst. auto.

  (* CALL EXCEPTION *)
  * intros. inversion H6.
    - subst.
      pose (EU := @eff_until_i_rev env eff eff5 params vals vals0 eff1 ids ids0 id _ _ _ H4 H12 IHIND H0 H1 H9 H10 H11 H2). inversion EU.
    - rewrite H16 in H21. apply IHIND.
      pose (EEQ := exception_equality vals vals0 ex eff1 eff eff6 i
             i0 eff3 ex0 eff4 _ _ _ _ _ H4 H21 IHIND H13 H H0 H1 H9 H10 H11 H2 H12).
      destruct EEQ. destruct H23. destruct H24. subst. assumption.

  (* APPLY EXCEPTION *)
  (* name evaluates to an exception *)
  * intros. inversion H0.
    - subst. pose (IH := IHIND _ _ _ H4). inversion IH. congruence.
    - subst. apply IHIND. assumption.
    - subst. pose (IH := IHIND _ _ _ H7). inversion IH. congruence.
    - subst. pose (IH := IHIND _ _ _ H6). inversion IH. congruence.
    - subst. pose (IH := IHIND _ _ _ H6). inversion IH. congruence.

  (* parameter exception *)
  * intros. inversion H6.
    - subst. apply IHIND1 in H10. destruct H10. destruct H5. inversion H.
      apply app_inv_head in H5. subst.
      pose (P1 := @eff_until_i_rev env eff _ params vals vals0 (eff1 ++ eff5) ids ids0 id'0 _ _ _ H4 H14 IHIND2 H0 H1 H9 H12 H13 H2). inversion P1.
    - subst. apply IHIND1 in H16. inversion H16. congruence.
    - apply IHIND1 in H13. destruct H13. destruct H23. apply app_inv_head in H23. inversion H13.
      rewrite H26, H23, H24 in *.
      rewrite H17 in *.
      assert (| env, last ids0 id'0, nth i0 params ErrorExp, concatn (eff1 ++ eff5) eff8 i0 | -e> | id''0,
      inr ex0, concatn (eff1 ++ eff5) eff8 i0 ++ eff6 |). { assumption. }
      pose (EE := exception_equality vals vals0 ex (eff1 ++ eff5) eff eff8 i i0 eff4 ex0
                 eff6 _ _ _ _ _ H4 H22 IHIND2 H14 (eq_sym H) H0 H1 (eq_sym H9) H10 H11 H2 H12).
      destruct EE. destruct H28. destruct H29. subst.
      apply IHIND2 in H25.
      assumption.
    - subst. apply IHIND1 in H12. destruct H12. inversion H. destruct H5.
      apply app_inv_head in H5. subst.
      pose (P1 := @eff_until_i_rev env eff _ params vals vals0 (eff1 ++ eff5) ids ids0 id'0 _ _ _ H4 H13 IHIND2 H0 H1 H9 H10 H11 H2). inversion P1.
    - subst. apply IHIND1 in H12. destruct H12. inversion H. destruct H5.
      apply app_inv_head in H5. subst.
      pose (P1 := @eff_until_i_rev env eff _ params vals vals0 (eff1 ++ eff5) ids ids0 id'0 _ _ _ H4 H13 IHIND2 H0 H1 H9 H10 H11 H2). inversion P1.

  (* name evaluate to a non-closure value *)
  * intros. inversion H7.
    - apply IHIND in H11. destruct H11. destruct H24. inversion H11.
      pose (P := H4 ref ext var_list body _ H27). inversion P.
    - subst. apply IHIND in H17. inversion H17. congruence.
    - subst. apply IHIND in H14. destruct H14. inversion H5. destruct H6. apply app_inv_head in H6. subst.
      pose (P1 := @eff_until_i env eff eff7 params vals vals0 (eff1 ++ eff4) ids ids0 id'0 id''0 ex eff5 H H0 H12 H11 H1 H13 H3 H15 H23). inversion P1.
    - subst. apply IHIND in H13. destruct H13. inversion H5. destruct H6. apply app_inv_head in H6. subst.
      pose (LEQ := @list_equality env params (eff1 ++ eff4) vals vals0 eff eff6 _ _ _ H2 H3 H14 H10 H11 H H0 H1 H12).
      destruct LEQ. destruct H8. subst. auto.
    - subst. apply IHIND in H13. destruct H13. inversion H5. destruct H6. apply app_inv_head in H6. subst.
      pose (P := H4 ref ext var_list body). congruence.

  (* paramlist is too short/long *)
  * intros. inversion H7.
    - subst. 
      pose (P1 := IHIND _ _ _ H11). destruct P1. destruct H6. apply app_inv_head in H6. inversion H5. subst.
      pose (EL:= list_equality vals vals0 eff eff7 _ _ _ H2 H3 H15 H10 H13 H H0 H1 H14). destruct EL. destruct H8. subst. intuition. 
    - subst. pose (IH := IHIND _ _ _ H17). inversion IH. congruence.
    - subst.
      pose (P1 := IHIND _ _ _ H14). destruct P1. destruct H6. apply app_inv_head in H6. inversion H5. subst.
      pose (P2 := @eff_until_i env eff eff7 params vals vals0 (eff1 ++ eff4) ids ids0 id'0 id''0 ex eff5 H H0 H12 H11 H1 H13 H3 H15 H23). inversion P2.
    - subst.
      pose (P1 := IHIND _ _ _ H13). destruct P1. destruct H6. inversion H5. subst.
      pose (P2 := H15 ref ext var_list body).
      congruence.
    - subst.
      pose (P1 := IHIND _ _ _ H13). destruct P1. destruct H6. apply app_inv_head in H6. inversion H5. subst.
      pose (EL:= @list_equality env params (eff1 ++ eff4) vals vals0 eff eff6 _ _ _ H2 H3 H14 H10 H11 H H0 H1 H12).
      destruct EL. destruct H8. subst. auto.

  
  (* LET EXCEPTION *)
  * intros. inversion H6.
    - subst.
      pose (EU := @eff_until_i_rev env eff _ exps vals vals0 eff1 ids ids0 _ _ _ _ H4 H15 IHIND H0 H1 H10 H11 H12 H2). inversion EU.
    - rewrite H21 in H22. apply IHIND. 
      pose (EEQ := exception_equality vals vals0 ex eff1 eff eff6
            i i0 eff3 ex0 eff4 _ _ _ _ _ H4 H22 IHIND H16 H H0 H1 H10 H11 H12 H2 H13).
      destruct EEQ. destruct H24. destruct H25. subst. assumption.

  (* MAP KEY EXCEPTION *)
  * intros. inversion H10.
    - rewrite H9 in IHIND.
      assert ((forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
               | env, last ids id, nth i kl ErrorExp, concatn eff1 eff (2 * i) | -e> |id'', v2, eff'' |
               ->
                inr ex = v2 /\ concatn eff1 eff (2 * i) ++ eff2 = eff'' /\ id' = id'')
               \/
            (forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
             | env, last ids id, nth i kl ErrorExp, concatn eff1 eff (2 * i) | -e> | id'', v2, eff'' | ->
             inl ErrorValue = v2 /\ concatn eff1 eff (2 * i) ++ eff2 = eff'' /\ id' = id'')
             /\
            (forall (v2 : Value + Exception) (eff'' : SideEffectList) (id''' : nat),
             | env, id', nth i vl ErrorExp, concatn eff1 eff (2 * i) ++ eff2 | -e> | id''', v2, eff'' | ->
             inr ex = v2 /\ [] = eff'' /\ id'' = id''')). { auto. }
     pose (MEQ := map_lists_equal_until_i_key_or_val kvals vvals kvals0 vvals0 i eff1 eff eff5 eff2
                        [] ErrorValue ex _ _ _ _ _ H6 H8 H29 H H0 H1 (Nat.lt_le_incl _ _ H2) H3 H4 H19 H20 H14 H15 (eq_sym H16) (eq_sym H17)).
     destruct MEQ. destruct H31. inversion H32. destruct H34. subst.
     assert (Datatypes.length vvals0 < Datatypes.length vl). { omega. }
     pose (ERR := H19 (length vvals0) H0).
     rewrite last_nth_equal, H4, mult_comm in IHIND.
     pose (DIS := IHIND _ _ _ ERR). inversion DIS. congruence.
    - rewrite H9 in IHIND. rewrite H23 in H28.
      assert (| env, last ids0 id, nth i0 kl ErrorExp, concatn eff1 eff6 (2 * i0) | 
              -e> | id'', inr ex0, concatn eff1 eff6 (2 * i0) ++ eff4 | \/
              | env, last ids0 id, nth i0 kl ErrorExp, concatn eff1 eff6 (2 * i0) | -e> | id'', inl ErrorValue,
               concatn eff1 eff6 (2 * i0) ++ eff4 | /\
               | env, id'', nth i0 vl ErrorExp, concatn eff1 eff6 (2 * i0) ++ eff4 | -e> | id'', inr ex0,
               concatn eff1 eff6 (2 * i0) ++ eff4 ++ [] |). { left. exact H28. }
      pose (MEQ := map_lists_equal_until_i_key kvals vvals kvals0 vvals0 i i0 eff1 eff eff6 ex0 eff4
                   eff2 [] ErrorValue ex _ _ _ _ _ _ H6 H8 IHIND H H0 H1 (Nat.lt_le_incl _ _ H2) H3 H4 H19 H20 H14 H15 (Nat.lt_le_incl _ _ H16) H17 H18 H29).
      destruct MEQ. destruct H31. destruct H32. destruct H33. subst.
      pose (IH1 := IHIND _ _ _ H28). inversion IH1. inversion H0.
      destruct H9. apply app_inv_head in H9. subst. auto.
    - rewrite H9 in IHIND. rewrite H24 in H29.
      assert (| env, last ids0 id, nth i0 kl ErrorExp, concatn eff1 eff7 (2 * i0) |
              -e> | id'0, inr ex0, concatn eff1 eff7 (2 * i0) ++ eff4 | \/
               | env, last ids0 id, nth i0 kl ErrorExp, concatn eff1 eff7 (2 * i0) | -e> | id'0, inl val,
               concatn eff1 eff7 (2 * i0) ++ eff4 | /\
               | env, id'0, nth i0 vl ErrorExp, concatn eff1 eff7 (2 * i0) ++ eff4 | -e> | id'', inr ex0,
               concatn eff1 eff7 (2 * i0) ++ eff4 ++ eff5 |). { auto. }
      pose (MEQ := map_lists_equal_until_i_key kvals vvals kvals0 vvals0 i i0 eff1 eff eff7 ex0 eff4
                   eff2 eff5 val ex _ _ _ _ _ _ H6 H8 IHIND H H0 H1 (Nat.lt_le_incl _ _ H2) H3 H4 H19 H20 H14 H15 (Nat.lt_le_incl _ _ H16) H17 H18 H30).
      destruct MEQ. destruct H32. destruct H33. destruct H34. subst.
      pose (IH1 := IHIND _ _ _ H21). inversion IH1. congruence.

  (* MAP VALUE EXCEPTION *)
  * intros. inversion H10.
    - assert ((forall (v2 : Value + Exception) (eff'' : SideEffectList) (id''' : nat),
              | env, last ids id, nth i kl ErrorExp, concatn eff1 eff (2 * i) | -e> | id''', v2, eff'' | ->
              inr ex = v2 /\ concatn eff1 eff (2 * i) ++ eff2 = eff'' /\ id' = id''') \/
             (forall (v2 : Value + Exception) (eff'' : SideEffectList) (id''' : nat),
              | env, last ids id, nth i kl ErrorExp, concatn eff1 eff (2 * i) | -e> | id''', v2, eff'' | ->
              inl val = v2 /\ concatn eff1 eff (2 * i) ++ eff2 = eff'' /\ id' = id''') /\
             (forall (v2 : Value + Exception) (eff'' : SideEffectList) (id''' : nat),
              | env, id', nth i vl ErrorExp, concatn eff1 eff (2 * i) ++ eff2 | -e> | id''', v2, eff'' | ->
              inr ex = v2 /\ eff4 = eff'' /\ id'' = id''')). { right. split. exact IHIND1. exact IHIND2. }
      pose (MEQ := map_lists_equal_until_i_key_or_val kvals vvals kvals0 vvals0 i eff1 eff eff6 eff2
                  eff4 val ex _ _ _ _ _ H6 H8 H29 H H0 H1 (Nat.lt_le_incl _ _ H2)
                  H3 H4 H19 H20 H14 H15 (eq_sym H16) (eq_sym H17)).
      destruct MEQ. destruct H31. destruct H32. destruct H33. subst.
      assert (Datatypes.length vvals0 < Datatypes.length vl). { omega. }
      pose (GOOD := H19 (length vvals0) H0).
      rewrite last_nth_equal, H4, mult_comm in IHIND1.
      pose (GOOD' := IHIND1 _ _ _ GOOD). inversion GOOD'. inversion H9. destruct H11.
      pose (BAD := H20 (length vvals0) H0). rewrite <- H11, <- H12 in BAD.
      pose (BAD' := IHIND2 _ _ _ BAD). inversion BAD'. congruence.
    - rewrite H23 in H28.
      assert (| env, last ids0 id, nth i0 kl ErrorExp, concatn eff1 eff7 (2 * i0) | -e> | id''0, inr ex0,
              concatn eff1 eff7 (2 * i0) ++ eff5 | \/
              | env, last ids0 id, nth i0 kl ErrorExp, concatn eff1 eff7 (2 * i0) | -e> | id''0, inl ErrorValue,
              concatn eff1 eff7 (2 * i0) ++ eff5 | /\
              | env, id''0, nth i0 vl ErrorExp, concatn eff1 eff7 (2 * i0) ++ eff5 | -e> | 
              id''0, inr ex0, concatn eff1 eff7 (2 * i0) ++ eff5 ++ [] |). { auto. }
      pose (MEQ := map_lists_equal_until_i_val kvals vvals kvals0 vvals0 i i0 eff1 eff eff7 ex0 eff5 eff2
                   eff4 [] val ErrorValue ex _ _ _ _ _ _ _ H6 H8 IHIND1 IHIND2 H H0 H1 (Nat.lt_le_incl _ _ H2)
                   H3 H4 H19 H20 H14 H15 (Nat.lt_le_incl _ _ H16) H17 H18 H29).
      destruct MEQ. destruct H31. destruct H32. destruct H33. subst.
      pose (IH1 := IHIND1 _ _ _ H28). inversion IH1. congruence.
    - rewrite H24 in H29.
      assert (| env, last ids0 id, nth i0 kl ErrorExp, concatn eff1 eff8 (2 * i0) | -e> | id'0, inr ex0,
              concatn eff1 eff8 (2 * i0) ++ eff5 | \/
              | env, last ids0 id, nth i0 kl ErrorExp, concatn eff1 eff8 (2 * i0) | -e> | id'0, inl val0,
              concatn eff1 eff8 (2 * i0) ++ eff5 | /\
              | env, id'0, nth i0 vl ErrorExp, concatn eff1 eff8 (2 * i0) ++ eff5 | -e> | id''0,
              inr ex0, concatn eff1 eff8 (2 * i0) ++ eff5 ++ eff6 |). { auto. }
      pose (MEQ := map_lists_equal_until_i_val kvals vvals kvals0 vvals0 i i0 eff1 eff eff8 ex0 eff5 eff2
                   eff4 eff6 val val0 ex _ _ _ _ _ _ _ H6 H8 IHIND1 IHIND2 H H0 H1 (Nat.lt_le_incl _ _ H2) H3  H4 H19 H20 H14 H15 (Nat.lt_le_incl _ _ H16) H17 H18 H30).
      destruct MEQ. inversion H32. destruct H34. destruct H35. subst.
      pose (IH1 := IHIND1 _ _ _ H21). destruct IH1. inversion H0. destruct H9. apply app_inv_head in H9. subst.
      pose (IH2 := IHIND2 _ _ _ H29). assumption.
Qed.

(* Theorem env_app_get (env : Environment) (var : Var + FunctionIdentifier) (val : Value):
get_value (insert_value env var val) var = inl val.
Proof.
  induction env.
  * simpl. rewrite uequal_refl. reflexivity.
  * simpl. destruct a. case_eq (uequal s var).
    - intros. simpl. rewrite uequal_refl. reflexivity.
    - intros. simpl. rewrite uequal_sym in H. rewrite H. exact IHenv.
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
    - pose (H0 (inl env) vl e).  unfold not in n. assert (VClosure (inl env) vl e = VClosure (inl env) vl e). reflexivity. pose (n H1). inversion f.
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

End Core_Erlang_Proofs.