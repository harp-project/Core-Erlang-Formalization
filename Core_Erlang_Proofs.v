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

  (* (* APPLY *)
  * intros. inversion H5.
    - subst. apply IHIND1 in H9. inversion H9. apply app_inv_head in H6. inversion H4. subst.
      pose (EQ := list_equality vals vals0 eff eff8 H2 H3 H12 H8 H11 H H1). inversion EQ. subst.
      apply IHIND2 in H18. inversion H18. auto.
    - subst. apply IHIND1 in H13. inversion H13. congruence.
    - subst. apply IHIND1 in H11. inversion H11. inversion H4. apply app_inv_head in H6. subst.
      pose (P1 := eff_until_i vals vals0 (eff1 ++ eff5) eff eff8 H H1 H10 H9 H3 H12).
      pose (P2 := H3 (Datatypes.length vals0) H9 (inr ex) (concatn (eff1 ++ eff5) 
                  eff8 (Datatypes.length vals0) ++ eff6)).
      rewrite <- P1 in P2. pose (P3 := P2 H18). inversion P3. inversion H6.
    - subst. apply IHIND1 in H10. inversion H10. inversion H4. subst.
      pose (P := H13 ref ext var_list body). congruence.
    - subst. apply IHIND1 in H10. inversion H10. inversion H4. subst. congruence.

  (* LET *)
  * intros. inversion H4. subst.
   - pose (LEQ := list_equality vals vals0 eff eff0 H1 H2 H11 H8 H9 H H0). destruct LEQ. subst.
     pose (IH1 := IHIND v2 (concatn eff1 eff0 (Datatypes.length exps) ++ eff5) H16). assumption.
   - subst. pose (P1 := H2 (Datatypes.length vals0) H9 (inr ex)
                           (concatn eff1 eff6 (Datatypes.length vals0) ++ eff4)).
     pose (EU := eff_until_i vals vals0 eff1 eff eff6 H H0 H10 H9 H2 H12).
     rewrite EU in H17. rewrite EU in P1. pose (P2 := P1 H17). inversion P2. inversion H3.

  (* LETREC *)
  * intros. inversion H2. 
    - subst. pose (IH2 := IHIND v2 (eff1 ++ eff4) H13). destruct IH2.
      apply app_inv_head in H3. subst. split; reflexivity.

  (* MAP *)
  * intros. inversion H9.
    - pose (MEQ := map_lists_equality kvals vvals kvals0 vvals0 eff1
                   eff eff4 H5 H7 H12 H0 H1 H2 H17 H19 H13 H14 H15).
     inversion MEQ. inversion H25. subst. rewrite H3 in H16. inversion H16. auto.
    - rewrite H20 in H24.
      assert (| env, nth i kl ErrorExp, concatn eff1 eff5 (2 * i) | 
              -e> | inr ex, concatn eff1 eff5 (2 * i) ++ eff3 |
              \/
              | env, nth i kl ErrorExp, concatn eff1 eff5 (2 * i) | 
              -e> | inl ErrorValue, concatn eff1 eff5 (2 * i) ++ eff3 |
              /\
              | env, nth i vl ErrorExp, concatn eff1 eff5 (2 * i) ++ eff3 | -e> 
              | inr ex, concatn eff1 eff5 (2 * i) ++ eff3 ++ [] |). { left. exact H24. }
      assert (Datatypes.length vvals0 < Datatypes.length vl). { omega. }
      pose (MEQ := map_lists_equal_until_i kvals vvals kvals0 vvals0 
                   i eff1 eff eff5 ex eff3 [] ErrorValue H5 H7 H12 H0 H1 (eq_sym H2) 
                   H17 H18 H13 H14 (Nat.lt_le_incl _ _ H15) H16 H25).
      inversion MEQ. inversion H28. inversion H30. subst.
      pose (IH1 := H5 (length vvals0) H26 (inr ex)
                   (concatn eff1 eff5 (2 * Datatypes.length vvals0) ++ eff3) H24).
      inversion IH1. inversion H8.
    - rewrite H21 in H25.
      assert (| env, nth i kl ErrorExp, concatn eff1 eff6 (2 * i) |
              -e> | inr ex, concatn eff1 eff6 (2 * i) ++ eff3 |
              \/
              | env, nth i kl ErrorExp, concatn eff1 eff6 (2 * i) |
              -e> | inl val, concatn eff1 eff6 (2 * i) ++ eff3 |
              /\
              | env, nth i vl ErrorExp, concatn eff1 eff6 (2 * i) ++ eff3 |
              -e> | inr ex, concatn eff1 eff6 (2 * i) ++ eff3 ++ eff4 |). { auto. }
      pose (MEQ := map_lists_equal_until_i kvals vvals kvals0 vvals0 i eff1 eff eff6 ex
                   eff3 eff4 val H5 H7 H12 H0 H1 (eq_sym H2) H17 H18 H13 H14
                   (Nat.lt_le_incl _ _ H15) H16 H26).
      inversion MEQ. inversion H28. inversion H30. subst.
      assert (Datatypes.length vvals0 < Datatypes.length vl). { omega. }
      pose (IH1 := H5 (length vvals0) H8 _ _ H19). inversion IH1. inversion H10.
      rewrite <- H11 in H25.
      pose (IH2 := H7 (length vvals0) H8 (inr ex) _ H25). inversion IH2. inversion H13.

  (* LIST HEAD EXCEPTION *)
  * intros. inversion H0; subst.
    - pose (IH := IHIND (inl tlv) (eff1 ++ eff4) H5). inversion IH. inversion H.
    - apply IHIND. assumption.
    - pose (IH := IHIND (inl vtl) (eff1 ++ eff4) H5). inversion IH. inversion H.

  (* LIST TAIL EXCEPTION *)
  * intros. inversion H0; subst.
    - pose (IH1 := IHIND1 (inl tlv) (eff1 ++ eff5) H5). inversion IH1.
      apply app_inv_head in H1. inversion H. subst.
      pose (IH2 := IHIND2 (inl hdv) (eff1 ++ eff5 ++ eff6) H9). inversion IH2. inversion H1.
    - pose (IH1 := IHIND1 (inr ex0) (eff1 ++ eff5) H8). inversion IH1. inversion H.
    - pose (IH1 := IHIND1 (inl vtl0) (eff1 ++ eff5) H5). inversion IH1.
      apply app_inv_head in H1. inversion H. subst.
      apply IHIND2. assumption.

  (* TUPLE EXCEPTION *)
  * intros. inversion H5.
    - subst.
      pose (P1 := H9 (length vals) H0).
      pose (EU := eff_until_i_rev exps vals vals0 eff5 H3 H9 H0 H1 H7 H8).
      rewrite EU in P1.
      pose (IH2 := IHIND (inl (nth (Datatypes.length vals) vals0 ErrorValue))
                  (concatn eff1 eff5 (S (Datatypes.length vals))) P1).
      destruct IH2. inversion H.
    - rewrite H11 in H13. 
      pose (EE := exception_equality vals vals0 ex eff1 eff eff6 i
             i0 eff3 ex0 eff4 H3 H13 IHIND H10 H H0 H1 H7 H8 H9).
      inversion EE. inversion H18. subst.
      pose (IHIND (inr ex0) (concatn eff1 eff6 (Datatypes.length vals0) ++ eff4) H13). assumption.
  
  (* CORECT TRY *)
  * intros. inversion H0.
    - subst. apply IHIND2. pose (IH1 := IHIND1 (inl val'0) (eff1 ++ eff5) H12).
      inversion IH1. inversion H. apply app_inv_head in H1. subst. assumption.
    - subst. pose (IH1 := IHIND1 (inr ex) _ H12). inversion IH1. inversion H.
  
  (* CORRECT CATCH *)
  * intros. inversion H0.
    - subst. pose (IH1 := IHIND1 (inl val') _ H12). inversion IH1. inversion H.
    - subst. apply IHIND2. pose (IH1 := IHIND1 (inr ex0) _ H12). inversion IH1.
      inversion H. apply app_inv_head in H1. subst. assumption.

  (* CASE EXCEPTIONS *)
  (** binding expression exception *)
  * intros. inversion H2.
    - subst. apply IHIND in H9. inversion H9. inversion H1.
    - subst. apply IHIND in H14. assumption.
    - subst. apply IHIND in H14. inversion H14. inversion H1.

  (** no matching clause *)
  * intros. inversion H4.
    - subst. apply IHIND in H11. inversion H11. apply app_inv_head in H5. inversion H1.
      subst. pose (EE := H3 i H12 guard exp bindings H13).
      pose (IHE := EE _ _ H20). inversion IHE. inversion H5.
    - subst. apply IHIND in H16. inversion H16. inversion H1.
    - subst. apply IHIND in H16. inversion H16. apply app_inv_head in H5. inversion H1.
      subst. auto.
  (* CALL EXCEPTION *)
  * intros. inversion H5.
    - subst.
      pose (P1 := H11 (length vals) H0).
      pose (EU := eff_until_i_rev params vals vals0 eff5 H3 H11 H0 H1 H8 H9).
      rewrite EU in P1.
      pose (IH2 := IHIND (inl (nth (Datatypes.length vals) vals0 ErrorValue))
                     (concatn eff1 eff5 (S (Datatypes.length vals))) P1).
      destruct IH2. inversion H.
    - rewrite H13 in H17. apply IHIND.
      pose (EEQ := exception_equality vals vals0 ex
          eff1 eff eff6 i i0 eff3 ex0 eff4 H3 H17 IHIND H11 H H0 H1 H8 H9 H10).
      inversion EEQ. inversion H19. subst. assumption.

  (* APPLY EXCEPTION *)
  (* name evaluates to an exception *)
  * intros. inversion H0.
    - subst. pose (IH := IHIND _ _ H4). inversion IH. inversion H.
    - subst. apply IHIND. assumption.
    - subst. pose (IH := IHIND _ _ H6). inversion IH. inversion H.
    - subst. pose (IH := IHIND _ _ H5). inversion IH. inversion H.
    - subst. pose (IH := IHIND _ _ H5). inversion IH. inversion H.

  (* parameter exception *)
  * intros. inversion H5.
    - subst. apply IHIND1 in H9. inversion H9. inversion H. apply app_inv_head in H4. subst.
      pose (P1 := eff_until_i_rev params vals vals0 eff8 H3 H12 H0 H1 H8 H11).
      pose (P2 := H12 (length vals) H0 ).
      pose (P3 := IHIND2 (inl (nth (Datatypes.length vals) vals0 ErrorValue))
                     (concatn (eff1 ++ eff5) eff8 (S (Datatypes.length vals)))).
      rewrite <- P1 in P3.
      pose (P4 := P3 P2).
      inversion P4. inversion H4.
    - subst. apply IHIND1 in H13. inversion H13. inversion H.
    - apply IHIND1 in H11. inversion H11. inversion H19. apply app_inv_head in H20.
      rewrite H20, H22 in *.
      rewrite H14 in *.
      assert (| env, nth i0 params ErrorExp, concatn (eff1 ++ eff5) eff8 i0 |
      -e> | inr ex0, concatn (eff1 ++ eff5) eff8 i0 ++ eff6 |). { assumption. }
      pose (EE := exception_equality vals vals0 ex (eff1 ++ eff5) eff eff8 i i0 eff4 ex0
                 eff6 H3 H18 IHIND2 H12 (eq_sym H) H0 H1 (eq_sym H8) H9 H10).
      inversion EE. inversion H24. subst.
      apply IHIND2 in H21.
      assumption.
    - subst. apply IHIND1 in H10. inversion H10. inversion H. apply app_inv_head in H4. subst.
      pose (P1 := eff_until_i_rev params vals vals0 eff7 H3 H11 H0 H1 H8 H9).
      pose (P2 := H11 (length vals) H0 ).
      pose (P3 := IHIND2 (inl (nth (Datatypes.length vals) vals0 ErrorValue))
                     (concatn (eff1 ++ eff5) eff7 (S (Datatypes.length vals)))).
      rewrite <- P1 in P3.
      pose (P4 := P3 P2).
      inversion P4. inversion H4.
    - subst. apply IHIND1 in H10. inversion H10. inversion H. apply app_inv_head in H4. subst.
      pose (P1 := eff_until_i_rev params vals vals0 eff7 H3 H11 H0 H1 H8 H9).
      pose (P2 := H11 (length vals) H0 ).
      pose (P3 := IHIND2 (inl (nth (Datatypes.length vals) vals0 ErrorValue))
                     (concatn (eff1 ++ eff5) eff7 (S (Datatypes.length vals)))).
      rewrite <- P1 in P3.
      pose (P4 := P3 P2).
      inversion P4. inversion H4.

  (* name evaluate to a non-closure value *)
  * intros. inversion H5.
    - apply IHIND in H9. inversion H9. inversion H19.
      pose (P := H3 ref ext var_list body _ H22). inversion P.
    - subst. apply IHIND in H13. inversion H13. inversion H4.
    - subst. apply IHIND in H11. inversion H11. inversion H4. apply app_inv_head in H6. subst.
      pose (P1 := eff_until_i vals vals0 (eff1 ++ eff4) eff eff7 H H0 H10 H9 H2 H12).
      pose (P2 := H2 (length vals0) H9 (inr ex) (concatn (eff1 ++ eff4) eff7 
                     (Datatypes.length vals0) ++ eff5)).
      rewrite <- P1 in P2.
      pose (P3 := P2 H18). inversion P3. inversion H6.
    - subst. apply IHIND in H10. inversion H10. inversion H4. apply app_inv_head in H6. subst.
      pose (LEQ := @list_equality env params (eff1 ++ eff4) vals vals0 eff eff6 H1 H2 H11 H8 H9 H H0).
      inversion LEQ. subst. auto.
    - subst. apply IHIND in H10. inversion H10. inversion H4. apply app_inv_head in H6. subst.
      pose (P := H3 ref ext var_list body). congruence.

  (* paramlist is too short/long *)
  * intros. inversion H5.
    - subst. 
      pose (P1 := IHIND _ _ H9). inversion P1. apply app_inv_head in H6. inversion H4. subst.
      pose (EL:= list_equality vals vals0 eff eff7 H1 H2 H12 H8 H11 H H0). inversion EL. subst. intuition. 
    - subst. pose (IH := IHIND _ _ H13). inversion IH. inversion H4.
    - subst.
      pose (P1 := IHIND _ _ H11). inversion P1. apply app_inv_head in H6. inversion H4. subst.
      pose (P2 := eff_until_i vals vals0 (eff1 ++ eff4) eff eff7 H H0 H10 H9 H2 H12).
      rewrite P2 in H18.
      pose (P3 := H2 (length vals0) H9 _ _ H18). inversion P3. inversion H6.
    - subst.
      pose (P1 := IHIND _ _ H10). inversion P1. inversion H4. subst.
      pose (P2 := H13 ref ext var_list body).
      congruence.
    - subst.
      pose (P1 := IHIND _ _ H10). inversion P1. apply app_inv_head in H6. inversion H4. subst.
      pose (EL:= @list_equality env params (eff1 ++ eff4) vals vals0 eff eff6 H1 H2 H11 H8 H9 H H0).
      inversion EL. subst. split; reflexivity.

  
  (* LET EXCEPTION *)
  * intros. inversion H5.
    - subst.
      pose (P1 := H12 (length vals) H0).
      pose (EU := eff_until_i_rev exps vals vals0 eff0 H3 H12 H0 H1 H9 H10).
      rewrite EU in P1.
      pose (IH2 := IHIND (inl (nth (Datatypes.length vals) vals0 ErrorValue))
             (concatn eff1 eff0 (S (Datatypes.length vals))) P1). destruct IH2. inversion H.
    - rewrite H17 in H18. apply IHIND. 
      pose (EEQ := exception_equality vals vals0 ex eff1 eff eff6
            i i0 eff3 ex0 eff4 H3 H18 IHIND H13 H H0 H1 H9 H10 H11).
      inversion EEQ. inversion H20. subst. assumption.

  (* MAP KEY EXCEPTION *)
  * intros. inversion H9.
    - rewrite H8 in IHIND.
      assert ((forall (v2 : Value + Exception) (eff'' : SideEffectList),
               | env, nth i kl ErrorExp, concatn eff1 eff (2 * i) | -e> | v2, eff'' |
               ->
                inr ex = v2 /\ concatn eff1 eff (2 * i) ++ eff2 = eff'')
               \/
            (forall (v2 : Value + Exception) (eff'' : SideEffectList),
             | env, nth i kl ErrorExp, concatn eff1 eff (2 * i) | -e> | v2, eff'' | ->
             inl ErrorValue = v2 /\ concatn eff1 eff (2 * i) ++ eff2 = eff'')
             /\
            (forall (v2 : Value + Exception) (eff'' : SideEffectList),
             | env, nth i vl ErrorExp, concatn eff1 eff (2 * i) ++ eff2 | -e> | v2, eff'' | ->
             inr ex = v2 /\ [] = eff'')). { auto. }
     pose (MEQ := map_lists_equal_until_i_key_or_val kvals vvals kvals0 vvals0 i eff1 eff eff5 eff2
                        [] ErrorValue ex H5 H7 H24 H12 H0 H1 (Nat.lt_le_incl _ _ H2) H3 H17 H19 H13
                        H14 (eq_sym H15)).
     inversion MEQ. inversion H26. inversion H28. subst.
     assert (Datatypes.length vvals0 < Datatypes.length vl). { omega. }
     pose (ERR := H17 (length vvals0) H0).
     pose (DIS := IHIND _ _ ERR). inversion DIS. inversion H8.
    - rewrite H8 in IHIND. rewrite H20 in H24.
      assert (| env, nth i0 kl ErrorExp, concatn eff1 eff6 (2 * i0) | 
              -e> | inr ex0, concatn eff1 eff6 (2 * i0) ++ eff4 | \/
              | env, nth i0 kl ErrorExp, concatn eff1 eff6 (2 * i0) | -e> | inl ErrorValue,
               concatn eff1 eff6 (2 * i0) ++ eff4 | /\
               | env, nth i0 vl ErrorExp, concatn eff1 eff6 (2 * i0) ++ eff4 | -e> | inr ex0,
               concatn eff1 eff6 (2 * i0) ++ eff4 ++ [] |). { left. auto. }
      pose (MEQ := map_lists_equal_until_i_key kvals vvals kvals0 vvals0 i i0 eff1 eff eff6 ex0 eff4
                   eff2 [] ErrorValue ex H5 H7 IHIND H12 H0 H1 (Nat.lt_le_incl _ _ H2) H3 H17 H18 H13 H14
                   (Nat.lt_le_incl _ _ H15) H16 H25).
      inversion MEQ. inversion H27. inversion H29. subst.
      pose (IH1 := IHIND _ _ H24). inversion IH1. inversion H0.
      apply app_inv_head in H8. subst. auto.
    - rewrite H8 in IHIND. rewrite H21 in H25.
      assert (| env, nth i0 kl ErrorExp, concatn eff1 eff7 (2 * i0) |
              -e> | inr ex0, concatn eff1 eff7 (2 * i0) ++ eff4 | \/
               | env, nth i0 kl ErrorExp, concatn eff1 eff7 (2 * i0) | -e> | inl val,
               concatn eff1 eff7 (2 * i0) ++ eff4 | /\
               | env, nth i0 vl ErrorExp, concatn eff1 eff7 (2 * i0) ++ eff4 | -e> | inr ex0,
               concatn eff1 eff7 (2 * i0) ++ eff4 ++ eff5 |). { auto. }
      pose (MEQ := map_lists_equal_until_i_key kvals vvals kvals0 vvals0 i i0 eff1 eff eff7 ex0 eff4
                   eff2 eff5 val ex H5 H7 IHIND H12 H0 H1 (Nat.lt_le_incl _ _ H2)
                   H3 H17 H18 H13 H14 (Nat.lt_le_incl _ _ H15) H16 H26).
      inversion MEQ. inversion H28. inversion H30. subst.
      pose (IH1 := IHIND _ _ H19). inversion IH1. inversion H0.

  (* MAP VALUE EXCEPTION *)
  * intros. inversion H9.
    - assert ((forall (v2 : Value + Exception) (eff'' : SideEffectList),
              | env, nth i kl ErrorExp, concatn eff1 eff (2 * i) | -e> | v2, eff'' | ->
              inr ex = v2 /\ concatn eff1 eff (2 * i) ++ eff2 = eff'') \/
             (forall (v2 : Value + Exception) (eff'' : SideEffectList),
              | env, nth i kl ErrorExp, concatn eff1 eff (2 * i) | -e> | v2, eff'' | ->
              inl val = v2 /\ concatn eff1 eff (2 * i) ++ eff2 = eff'') /\
             (forall (v2 : Value + Exception) (eff'' : SideEffectList),
              | env, nth i vl ErrorExp, concatn eff1 eff (2 * i) ++ eff2 | -e> | v2, eff'' | ->
              inr ex = v2 /\ eff4 = eff'')). { right. split. exact IHIND1. exact IHIND2. }
      pose (MEQ := map_lists_equal_until_i_key_or_val kvals vvals kvals0 vvals0 i eff1 eff eff6 eff2
                  eff4 val ex H5 H7 H24 H12 H0 H1 (Nat.lt_le_incl _ _ H2)
                  H3 H17 H19 H13 H14 (eq_sym H15)).
      inversion MEQ. inversion H26. inversion H28. subst.
      assert (Datatypes.length vvals0 < Datatypes.length vl). { omega. }
      pose (GOOD := H17 (length vvals0) H0).
      pose (GOOD' := IHIND1 _ _ GOOD). inversion GOOD'. inversion H8.
      pose (BAD := H19 (length vvals0) H0). rewrite <- H10 in BAD.
      pose (BAD' := IHIND2 _ _ BAD). inversion BAD'. inversion H11.
    - rewrite H20 in H24.
      assert (| env, nth i0 kl ErrorExp, concatn eff1 eff7 (2 * i0) | -e> | inr ex0,
              concatn eff1 eff7 (2 * i0) ++ eff5 | \/
              | env, nth i0 kl ErrorExp, concatn eff1 eff7 (2 * i0) | -e> | inl ErrorValue,
              concatn eff1 eff7 (2 * i0) ++ eff5 | /\
              | env, nth i0 vl ErrorExp, concatn eff1 eff7 (2 * i0) ++ eff5 | -e> | 
              inr ex0, concatn eff1 eff7 (2 * i0) ++ eff5 ++ [] |). { auto. }
      pose (MEQ := map_lists_equal_until_i_val kvals vvals kvals0 vvals0 i i0 eff1 eff eff7 ex0 eff5 eff2
                   eff4 [] val ErrorValue ex H5 H7 IHIND1 IHIND2 H H0 H1 (Nat.lt_le_incl _ _ H2)
                   H3 H17 H18 H13 H14 (Nat.lt_le_incl _ _ H15) H16 H25).
      inversion MEQ. inversion H27. inversion H29. subst.
      pose (IH1 := IHIND1 _ _ H24). inversion IH1. inversion H0.
    - rewrite H21 in H25.
      assert (| env, nth i0 kl ErrorExp, concatn eff1 eff8 (2 * i0) | -e> | inr ex0,
              concatn eff1 eff8 (2 * i0) ++ eff5 | \/
              | env, nth i0 kl ErrorExp, concatn eff1 eff8 (2 * i0) | -e> | inl val0,
              concatn eff1 eff8 (2 * i0) ++ eff5 | /\
              | env, nth i0 vl ErrorExp, concatn eff1 eff8 (2 * i0) ++ eff5 | -e> | 
              inr ex0, concatn eff1 eff8 (2 * i0) ++ eff5 ++ eff6 |). { auto. }
      pose (MEQ := map_lists_equal_until_i_val kvals vvals kvals0 vvals0 i i0 eff1 eff eff8 ex0 eff5 eff2
                   eff4 eff6 val val0 ex H5 H7 IHIND1 IHIND2 H H0 H1 (Nat.lt_le_incl _ _ H2) H3 H17 H18
                   H13 H14 (Nat.lt_le_incl _ _ H15) H16 H26). inversion MEQ. inversion H28. inversion H30. subst.
      pose (IH1 := IHIND1 _ _ H19). inversion IH1. inversion H0. apply app_inv_head in H8. subst.
      pose (IH2 := IHIND2 _ _ H25). assumption. *)
Admitted.

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