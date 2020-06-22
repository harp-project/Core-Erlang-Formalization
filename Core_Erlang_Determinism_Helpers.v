Load Core_Erlang_Semantics.

From Coq Require Import Arith.PeanoNat.

(** Helper lemmas for determinism *)
Module Core_Erlang_Determinism_Helpers.

Import Core_Erlang_Syntax.
Import Core_Erlang_Semantics.
Import Core_Erlang_Environment.
Import Core_Erlang_Helpers.
Import Core_Erlang_Equalities.
Import Core_Erlang_Side_Effects.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.
Import Coq.Init.Logic.
Import Omega.

(** Macro tactics *)
Ltac simpl_app :=
  repeat (rewrite app_assoc);
  repeat (rewrite app_nil_r).

Ltac simpl_app_H Hyp0 :=
  repeat (rewrite app_assoc in Hyp0);
  repeat (rewrite app_nil_r in Hyp0).

Ltac simpl_concatn :=
  unfold concatn; simpl; simpl_app.

Ltac simpl_concatn_H Hyp0 :=
    unfold concatn in Hyp0; simpl in Hyp0; simpl_app_H Hyp0.

(* List unfolding tactics *)
Ltac unfold_list :=
match goal with
| [ H : Datatypes.length ?l = 0 |- _] => apply length_zero_iff_nil in H; subst
| [ H : 0 = Datatypes.length ?l |- _] => apply eq_sym, length_zero_iff_nil in H; subst
| [ H : Datatypes.length ?l = S ?n |- _] => symmetry in H; unfold_list
| [ H : S ?n = Datatypes.length ?l |- _] => 
   pose (element_exist _ _ _ H);
   match goal with
   | [H' : exists x l', _ = x::l' |- _] => 
     inversion H';
     match goal with
     | [H'' : exists l', _ = ?x::l' |- _] => inversion H''; subst; simpl in H; inversion H; unfold_list
     end
   end
end
.

Ltac single_unfold_list :=
match goal with
| [ Hyp : Datatypes.length ?l = 0 |- _] => apply length_zero_iff_nil in Hyp; subst
| [ Hyp : 0 = Datatypes.length ?l |- _] => apply eq_sym, length_zero_iff_nil in Hyp; subst
| [ Hyp : Datatypes.length ?l = S ?n |- _] => symmetry in Hyp; unfold_list
| [ Hyp : S ?n = Datatypes.length ?l |- _] => 
   pose (element_exist _ _ _ Hyp);
   match goal with
   | [H' : exists x l', _ = x::l' |- _] => 
     inversion H';
     match goal with
     | [H'' : exists l', _ = ?x::l' |- _] => inversion H''; subst; simpl in Hyp; inversion Hyp
     end
   end
end
.

Section List_Length_Theorems.

Proposition list_length {A : Type} {a : A} {l : list A} : length (a :: l) > 0.
Proof.
  simpl. apply Nat.lt_0_succ.
Qed.

Proposition split_length_r_l {A B : Type} {l : list (A * B)} : 
  length (fst (split l)) = length (snd (split l)).
Proof.
  rewrite split_length_l, split_length_r. reflexivity.
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

End List_Length_Theorems.

Lemma concatn_app {eff1 x1 : SideEffectList} {x6 : list SideEffectList} {i : nat} : 
  concatn eff1 (x1 :: x6) (S i) = concatn (eff1 ++ x1) x6 i.
Proof.
  induction i.
  * simpl_concatn. reflexivity.
  * simpl_concatn. simpl_concatn_H IHi. reflexivity.
Qed.

(** Attibute restriction to a smaller list *)
Lemma restrict_helper {env : Environment} {eff1 : SideEffectList} {exps : list Expression} 
    (a : Expression) (x1 : SideEffectList) (x6 : list SideEffectList) (x0 : Value) 
    (x3 : list Value):
(forall i : nat,
    i < Datatypes.length (a :: exps) ->
    | env, nth i (a :: exps) ErrorExp, concatn eff1 (x1 :: x6) i | -e>
    | inl (nth i (x0 :: x3) ErrorValue), concatn eff1 (x1 :: x6) (S i) |)
->
forall i : nat,
    i < Datatypes.length exps ->
    | env, nth i exps ErrorExp, concatn (eff1 ++ x1) x6 i | -e>
    | inl (nth i x3 ErrorValue), concatn (eff1 ++ x1) x6 (S i) |
.
Proof.
  intros.
  assert (S i < Datatypes.length (a :: exps)) as A1.
  { simpl. apply lt_n_S. assumption. } pose (E := H (S i) A1). 
  pose (P1 := @concatn_app eff1 x1 x6 i).
  pose (P2 := @concatn_app eff1 x1 x6 (S i)).
  simpl in E. rewrite P1, P2 in E. assumption.
Qed.

(** Value lists are equal ased on the determinism hypotheses *)
Lemma list_equality {env : Environment} {exps : list Expression} {eff1 : SideEffectList} : 
forall vals vals0 : list Value, forall eff eff4 : list SideEffectList,
  (forall i : nat,
     i < Datatypes.length exps ->
     | env, nth i exps ErrorExp, concatn eff1 eff i | -e> | inl (nth i vals ErrorValue),
     concatn eff1 eff (S i) |)
->
(forall i : nat,
     i < Datatypes.length exps ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList),
     | env, nth i exps ErrorExp, concatn eff1 eff i | -e> | v2, eff'' | ->
     inl (nth i vals ErrorValue) = v2 /\ concatn eff1 eff (S i) = eff'')
->
(forall i : nat,
     i < Datatypes.length exps ->
     | env, nth i exps ErrorExp, concatn eff1 eff4 i | -e> | inl (nth i vals0 ErrorValue),
     concatn eff1 eff4 (S i) |)
->
Datatypes.length exps = Datatypes.length vals0
->
Datatypes.length exps = Datatypes.length eff4
->
Datatypes.length exps = Datatypes.length vals
->
Datatypes.length exps = Datatypes.length eff
->
eff = eff4 /\ vals = vals0.
Proof.
  generalize dependent eff1. induction exps.
  * intros. inversion H3. inversion H2. inversion H4. inversion H5.
    repeat (unfold_list).
    subst. split; reflexivity.
  * intros. inversion H3. inversion H2. inversion H4. inversion H5.
  
  (* first elements are the same *)
    single_unfold_list. single_unfold_list.
    single_unfold_list. single_unfold_list.
    pose (P1 := H1 0 list_length). simpl_concatn_H P1.
    pose (P2 := H0 0 list_length (inl x3) (concatn eff1 (x5 :: x6) 1)). simpl_concatn_H P2.
    pose (P3 := P2 P1). inversion P3. inversion H17. apply app_inv_head in H19. subst.
  (* remaining lists are the same *)

  (* These three asserts ensure, that if something states for every element in 
    a (b::l) list, then it states for every element in l too*)
    assert (
      (forall i : nat,
    i < Datatypes.length exps ->
    | env, nth i exps ErrorExp, concatn (eff1 ++ x5) x0 i | -e> | inl (nth i x2 ErrorValue),
    concatn (eff1 ++ x5) x0 (S i) |)
    ).
    {
      intros. pose (P4 := restrict_helper a _ _ _ _ H i H19). assumption.
    }
    assert (
      (forall i : nat,
      i < Datatypes.length exps ->
      forall (v2 : Value + Exception) (eff'' : SideEffectList),
      | env, nth i exps ErrorExp, concatn (eff1 ++ x5) x0 i | -e> | v2, eff'' | ->
      inl (nth i x2 ErrorValue) = v2 /\ concatn (eff1 ++ x5) x0 (S i) = eff'')
    ).
    {
      intros. assert (S i < Datatypes.length (a::exps)). { simpl. omega. } 
      pose (P4 := H0 (S i) H22 v2 eff''). simpl nth in P4. rewrite concatn_app in P4. 
      rewrite concatn_app in P4. exact (P4 H21).
    }
    assert (
     (forall i : nat,
    i < Datatypes.length exps ->
    | env, nth i exps ErrorExp, concatn (eff1 ++ x5) x6 i | -e> | inl (nth i x4 ErrorValue),
    concatn (eff1 ++ x5) x6 (S i) |)
    ).
    {
      intros. assert (S i < Datatypes.length (a :: exps)). { simpl. omega. } 
      pose (P4 := H1 (S i) H22). simpl nth in P4. rewrite concatn_app in P4. 
      rewrite concatn_app in P4. assumption.
    }
    (* simpl list lengths *)
    inversion H4. inversion H5. inversion H8. inversion H7.
    pose (IH := IHexps (eff1 ++ x5) x2 x4 x0 x6 H19 H20 H21 H25 H26 H23 H24). 
    inversion IH. subst. split; reflexivity.
Qed.

Proposition nat_ge_or : forall {n m : nat}, n >= m <-> n = m \/ n > m.
Proof.
intros. omega.
Qed.

(** Based on determinism hypotheses, the same clause was chosen in case evaluation *)
Lemma index_case_equality {env : Environment} {l : list (Pattern * Expression * Expression)} {v0 : Value} (i i0 : nat) 
    (guard guard0 exp exp0 : Expression) (bindings bindings0 : list (Var * Value)) 
    (eff1 : SideEffectList) : 
  (forall j : nat,
     j < i ->
     forall (gg ee : Expression) (bb : list (Var * Value)),
     match_clause v0 l j = Some (gg, ee, bb) ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList),
     | add_bindings bb env, gg, eff1 | -e> | v2, eff'' | ->
     inl ffalse = v2 /\ eff1 = eff'')
  ->
  (forall j : nat,
      j < i0 ->
      forall (gg ee : Expression) (bb : list (Var * Value)),
      match_clause v0 l j = Some (gg, ee, bb) ->
      | add_bindings bb env, gg, eff1 | -e> | inl ffalse, eff1 |)
  ->
  match_clause v0 l i = Some (guard, exp, bindings)
  ->
  match_clause v0 l i0 = Some (guard0, exp0, bindings0)
  ->
  | add_bindings bindings0 env, guard0, eff1 | -e> | inl ttrue, eff1 |
  ->
  | add_bindings bindings env, guard, eff1 | -e> | inl ttrue, eff1 |
  ->
  (forall (v2 : Value + Exception) (eff'' : SideEffectList),
         | add_bindings bindings env, guard, eff1 | -e> | v2, eff'' | ->
         inl ttrue = v2 /\ eff1 = eff'')
->
  i = i0.
Proof.
  intros. pose (D := Nat.lt_decidable i i0). destruct D.
  * pose (P1 := H0 i H6 guard exp bindings H1). pose (P2 := H5 (inl ffalse) _ P1). 
    inversion P2. inversion H7.
  * apply not_lt in H6. apply (nat_ge_or) in H6. inversion H6.
    - assumption.
    - pose (P3 := H i0 H7 guard0 exp0 bindings0 H2 (inl ttrue) _ H3). inversion P3. inversion H8.
Qed.

(** Based on determinism, until the i-th element, the side effects are equal *)
Lemma firstn_eq {env : Environment} {eff : list SideEffectList} : 
forall (eff5 : list SideEffectList) (exps : list Expression) (vals vals0 : list Value) 
   (eff1 : SideEffectList),
length exps = length vals ->
Datatypes.length exps = Datatypes.length eff
->
Datatypes.length eff5 = Datatypes.length vals0
->
Datatypes.length vals0 < Datatypes.length exps 
->
(forall i : nat,
     i < Datatypes.length exps ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList),
     | env, nth i exps ErrorExp, concatn eff1 eff i | -e> | v2, eff'' | ->
     inl (nth i vals ErrorValue) = v2 /\ concatn eff1 eff (S i) = eff'')
->
(forall j : nat,
     j < Datatypes.length vals0 ->
     | env, nth j exps ErrorExp, concatn eff1 eff5 j | -e> | inl (nth j vals0 ErrorValue),
     concatn eff1 eff5 (S j) |)
->
firstn (Datatypes.length vals0) eff5 = firstn (Datatypes.length vals0) eff.
Proof.
  induction eff.
  * intros. inversion H0. rewrite H6 in H2. inversion H2.
  * intros. destruct eff5.
    - inversion H1. simpl. reflexivity.
    - inversion H1. simpl.
    (* first elements *)
      inversion H0. assert (0 < length exps). { omega. } assert (0 < length vals0). { omega. }
      simpl in H0, H1.
      (* single_unfold_list H1. *)
      pose (EE1 := element_exist Expression (length eff) exps (eq_sym H7)).
      pose (EE2 := element_exist Value (length eff5) vals0 H1).
      rewrite H in H0.
      pose (EE3 := element_exist Value (length eff) vals (eq_sym H0)). 
      inversion EE1 as [e]. inversion EE2 as [v]. inversion EE3 as [v']. 
      inversion H10. inversion H9. inversion H11. subst.
      pose (P0 := H4 0 H8). simpl_concatn_H P0.
      pose (P1 := H3 0 H5 (inl v) (eff1 ++ s ++ [])). simpl_concatn_H P1.
      pose (P2 := P1 P0). destruct P2. apply app_inv_head in H13. subst.
    (* other elements *)
      inversion H1. rewrite H14.
      assert (firstn (Datatypes.length x) eff5 = firstn (Datatypes.length x) eff).
      {
        apply IHeff with (exps := x0) (vals := x1) (eff1 := eff1 ++ s); auto.
        - intuition.
        - intros. assert (S i < Datatypes.length (e :: x0)). { simpl. omega. } 
          pose (A := H3 (S i) H16 v2 eff''). rewrite concatn_app, concatn_app in A. simpl in A. 
          pose (B := A H15). assumption.
        - intros. assert (S j < Datatypes.length (v :: x)). { omega. } 
          pose (A := H4 (S j) H15). 
          rewrite concatn_app, concatn_app in A. simpl in A. exact A.
      }
      rewrite H13. reflexivity.
Qed.

(** Side effect equality until the ith element using concatn *)
Lemma eff_until_i {env : Environment} {exps : list Expression} (vals vals0 : list Value) 
     (eff1 : SideEffectList) (eff eff5 : list SideEffectList) :
length exps = length vals ->
Datatypes.length exps = Datatypes.length eff
->
Datatypes.length eff5 = Datatypes.length vals0
->
Datatypes.length vals0 < Datatypes.length exps
->
(forall i : nat,
     i < Datatypes.length exps ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList),
     | env, nth i exps ErrorExp, concatn eff1 eff i | -e> | v2, eff'' | ->
     inl (nth i vals ErrorValue) = v2 /\ concatn eff1 eff (S i) = eff'')
->
(forall j : nat,
     j < Datatypes.length vals0 ->
     | env, nth j exps ErrorExp, concatn eff1 eff5 j | -e> | inl (nth j vals0 ErrorValue),
     concatn eff1 eff5 (S j) |) 
->
  concatn eff1 eff5 (Datatypes.length vals0) = concatn eff1 eff (Datatypes.length vals0).
Proof.
  intros. simpl_concatn. rewrite (firstn_eq eff5 exps vals vals0 eff1 H H0 H1 H2 H3 H4). reflexivity.
Qed.

(** First i elements are equal, but with changed hypotheses *)
Lemma firstn_eq_rev {env : Environment} {eff : list SideEffectList} : 
   forall (eff5 : list SideEffectList) (exps : list Expression) (vals vals0 : list Value) 
          (eff1 : SideEffectList),
(forall j : nat,
     j < Datatypes.length vals ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList),
     | env, nth j exps ErrorExp, concatn eff1 eff j | -e> | v2, eff'' | ->
     inl (nth j vals ErrorValue) = v2 /\ concatn eff1 eff (S j) = eff'')
->
(forall i : nat,
     i < Datatypes.length exps ->
     | env, nth i exps ErrorExp, concatn eff1 eff5 i | -e> | inl (nth i vals0 ErrorValue),
     concatn eff1 eff5 (S i) |)
->
Datatypes.length vals < Datatypes.length exps ->
Datatypes.length eff = Datatypes.length vals ->
Datatypes.length exps = Datatypes.length vals0 ->
Datatypes.length exps = Datatypes.length eff5
->
firstn (Datatypes.length vals) eff5 = firstn (Datatypes.length vals) eff.
Proof.
  induction eff.
  * intros. inversion H2. simpl. reflexivity.
  * intros. destruct eff5.
    - inversion H4. rewrite H4 in H1. inversion H1.
    - inversion H2. inversion H4. simpl.
    (* first elements *)
      assert (0 < length exps). { omega. } assert (0 < length vals). { omega. } simpl in H0, H1.
      assert (S (Datatypes.length eff5) = Datatypes.length exps).
      { auto. }
      assert (Datatypes.length exps = Datatypes.length vals0) as LENGTH. { auto. }
      (* single_unfold_list H9. *)
      pose (EE1 := element_exist Expression (length eff5) exps (eq_sym H7)).
      pose (EE2 := element_exist Value (length eff) vals H6).
      rewrite <- H9 in H3.
      pose (EE3 := element_exist Value (length eff5) vals0 H3).
      inversion EE1 as [e]. inversion EE2 as [v]. inversion EE3 as [v']. 
      inversion H10. inversion H12. inversion H11. subst.
      pose (P0 := H0 0 H5). simpl_concatn_H P0.
      pose (P1 := H 0 H8 (inl v') (eff1 ++ s ++ [])). simpl_concatn_H P1.
      pose (P2 := P1 P0). destruct P2. apply app_inv_head in H14. subst.
    (* other elements *)
      inversion H2. rewrite H15.
      assert (firstn (Datatypes.length x1) eff5 = firstn (Datatypes.length x1) eff).
      {
        apply IHeff with (exps := x) (vals := x1) (eff1 := eff1 ++ s) (vals0 := x0); auto.
        - intros. assert (S j < Datatypes.length (v :: x1)). { simpl. omega. } 
          pose (A := H (S j) H17 v2 eff''). rewrite concatn_app, concatn_app in A. simpl in A. 
          pose (B := A H16). assumption.
        - intros. assert (S i < Datatypes.length (e :: x)). { simpl. omega. } 
          pose (A := H0 (S i) H16). rewrite concatn_app, concatn_app in A. simpl in A. exact A.
        - intuition.
      }
      rewrite H14. reflexivity.
Qed.

(** First i (length vals) element are equal with concatn *)
Lemma eff_until_i_rev {env : Environment} {eff1 : SideEffectList} {eff : list SideEffectList} : 
   forall (exps : list Expression) (vals vals0 : list Value) (eff5 : list SideEffectList),
(forall j : nat,
     j < Datatypes.length vals ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList),
     | env, nth j exps ErrorExp, concatn eff1 eff j | -e> | v2, eff'' | ->
     inl (nth j vals ErrorValue) = v2 /\ concatn eff1 eff (S j) = eff'')
->
(forall i : nat,
     i < Datatypes.length exps ->
     | env, nth i exps ErrorExp, concatn eff1 eff5 i | -e> | inl (nth i vals0 ErrorValue),
     concatn eff1 eff5 (S i) |)
->
Datatypes.length vals < Datatypes.length exps ->
Datatypes.length eff = Datatypes.length vals ->
Datatypes.length exps = Datatypes.length vals0 ->
Datatypes.length exps = Datatypes.length eff5
->
concatn eff1 eff5 (Datatypes.length vals) = concatn eff1 eff (Datatypes.length vals).
Proof.
  intros. simpl_concatn. rewrite (firstn_eq_rev eff5 exps vals vals0 eff1 H H0 H1 H2 H3 H4). 
  reflexivity.
Qed.

Lemma nat_exist {n m : nat} : n < m -> exists x, m = S x.
Proof.
  intros. inversion H.
  * apply ex_intro with n. reflexivity.
  * apply ex_intro with m0. reflexivity.
Qed.

(** First i element are equal with concatn *)
Lemma con_n_equality {env : Environment} {eff : list SideEffectList} : 
  forall (exps : list Expression) (vals vals0 : list Value) eff1 eff6 i i0,
(forall j : nat,
    j < i ->
    forall (v2 : Value + Exception) (eff'' : SideEffectList),
    | env, nth j exps ErrorExp, concatn eff1 eff j | -e> | v2, eff'' | ->
    inl (nth j vals ErrorValue) = v2 /\ concatn eff1 eff (S j) = eff'')
->
(forall j : nat,
     j < i0 ->
     | env, nth j exps ErrorExp, concatn eff1 eff6 j | -e> | inl (nth j vals0 ErrorValue),
     concatn eff1 eff6 (S j) |)
->
Datatypes.length eff = i ->
i < Datatypes.length exps ->
Datatypes.length vals = i ->
Datatypes.length vals0 = i0 ->
i0 < Datatypes.length exps ->
Datatypes.length eff6 = i0 ->
i < i0
->
concatn eff1 eff6 i = concatn eff1 eff i.
Proof.
  induction eff.
  * intros. simpl in H1. subst. simpl_concatn. reflexivity.
  * intros. inversion H1. simpl in H1. rewrite <- H1 in H3.
    pose (EE1 := element_exist Value (length eff) vals (eq_sym H3)). 
    inversion EE1 as [v]. inversion H9 as [vs]. destruct eff6.
    - simpl in H6. subst. rewrite <- H6 in H7. inversion H7.
    - subst. simpl. simpl_concatn_H IHeff. rewrite concatn_app, concatn_app. simpl_concatn.
      simpl in H6. (* single_unfold_list H6. *) 
      pose (EE2 := element_exist Value (length eff6) vals0 H6). inversion EE2. 
      inversion H1.
      pose (nat_exist H2). inversion e.
      pose (EE3 := element_exist Expression x1 exps (eq_sym H10)). inversion EE3. inversion H11.
      assert (s = a). {
        subst.
        assert (0 < Datatypes.length (x :: x0)). {  simpl. omega. }
        pose (H0 0 H4).
        assert (0 < S (Datatypes.length eff)). {  simpl. omega. }
        pose (H 0 H12 (inl (nth 0 (x :: x0) ErrorValue)) (concatn eff1 (s :: eff6) 1) e0). 
        inversion a0.
        simpl_concatn_H H14. apply app_inv_head in H14. symmetry. assumption.
      }
      rewrite <- H13. subst.
      apply IHeff with (exps := x3) (vals := vs) (vals0 := x0) (eff1 := eff1 ++ a) (i0 := length x0); auto.
      + intros. assert (S j < S (Datatypes.length eff)). { simpl. omega. } pose (H (S j) H13 v2 eff''). 
      rewrite concatn_app, concatn_app in a0. simpl in a0. pose (a0 H12). assumption.
      + intros. assert (S j < Datatypes.length (x :: x0)). { simpl. omega. }
        pose (H0 (S j) H12). rewrite concatn_app, concatn_app in e0. simpl in e0. assumption.
      + intuition.
      + intuition.
      + intuition.
Qed.

(** Value lists are equal until ith value *)
Lemma list_equal_until_i {env : Environment} {eff : list SideEffectList} :
  forall (exps : list Expression) (vals vals0 : list Value) (eff6 : list SideEffectList) (eff1 : SideEffectList),
(forall j : nat,
    j < Datatypes.length vals ->
    forall (v2 : Value + Exception) (eff'' : SideEffectList),
    | env, nth j exps ErrorExp, concatn eff1 eff j | -e> | v2, eff'' | ->
    inl (nth j vals ErrorValue) = v2 /\ concatn eff1 eff (S j) = eff'')
->
(forall j : nat,
     j < Datatypes.length vals0 ->
     | env, nth j exps ErrorExp, concatn eff1 eff6 j | -e> | inl (nth j vals0 ErrorValue),
     concatn eff1 eff6 (S j) |)
->
Datatypes.length vals = Datatypes.length vals0
->
Datatypes.length eff = Datatypes.length vals
->
Datatypes.length eff6 = Datatypes.length vals0
->
Datatypes.length vals0 < Datatypes.length exps
->
eff = eff6 /\ vals = vals0.
Proof.
  induction eff.
  * intros. inversion H2. apply eq_sym, length_zero_iff_nil in H6. subst. simpl in H1. 
    apply eq_sym, length_zero_iff_nil in H1. subst. simpl in H3. apply length_zero_iff_nil in H3. 
    subst. auto.
  * intros. simpl in H2. rewrite <- H2 in H1. rewrite <- H1 in H3. pose (nat_exist H4). inversion e.
    (* single_unfold_list H2. *)
    pose (EE1 := element_exist Value (length eff) vals H2).
    pose (EE2 := element_exist Value (length eff) vals0 H1).
    pose (EE3 := element_exist SideEffectList (length eff) eff6 (eq_sym H3)).
    pose (EE4 := element_exist Expression x exps (eq_sym H5)).
    inversion EE1 as [v]. inversion EE2 as [v']. inversion EE3 as [fe]. inversion EE4 as [e'].
    inversion H6. inversion H7. inversion H8. inversion H9. subst.
    assert (0 < Datatypes.length (v' :: x1)). { simpl. omega. }
    pose (H0 0 H10).
    assert (0 < Datatypes.length (v :: x0)). { simpl. omega. }
    pose (H 0 H11 (inl (nth 0 (v' :: x1) ErrorValue)) (concatn eff1 (fe :: x2) 1) e0). inversion a0.
    simpl_concatn_H H13. apply app_inv_head in H13. inversion H12. subst.
    
    assert (eff = x2 /\ x0 = x1).
    {
      apply IHeff with (exps := x3) (vals := x0) (vals0 := x1) (eff1 := eff1 ++ fe); auto.
      + intros. assert (S j < S (Datatypes.length x0)). { simpl. omega. } pose (H (S j) H15 v2 eff''). 
        rewrite concatn_app, concatn_app in a. simpl in a. pose (a H14). assumption.
      + intros. assert (S j < Datatypes.length (v' :: x1)). { simpl. omega. }
        pose (H0 (S j) H14). rewrite concatn_app, concatn_app in e4. simpl in e4. assumption.
      + inversion H2. inversion H3. inversion H1. auto.
      + inversion H2. inversion H3. inversion H1. auto.
      + intuition.
    }
    inversion H13. subst. auto.
Qed.

(** Slightly different hypotheses for i first element concatn equality *)
Lemma con_n_equality_rev {env : Environment} {eff : list SideEffectList} : 
forall (exps : list Expression) (vals vals0 : list Value) (eff1 : SideEffectList) 
   (eff6 : list SideEffectList) (i i0 : nat),
(forall j : nat,
    j < i ->
    forall (v2 : Value + Exception) (eff'' : SideEffectList),
    | env, nth j exps ErrorExp, concatn eff1 eff j | -e> | v2, eff'' | ->
    inl (nth j vals ErrorValue) = v2 /\ concatn eff1 eff (S j) = eff'')
->
(forall j : nat,
     j < i0 ->
     | env, nth j exps ErrorExp, concatn eff1 eff6 j | -e> | inl (nth j vals0 ErrorValue),
     concatn eff1 eff6 (S j) |)
->
Datatypes.length eff = i ->
i < Datatypes.length exps ->
Datatypes.length vals = i ->
Datatypes.length vals0 = i0 ->
i0 < Datatypes.length exps ->
Datatypes.length eff6 = i0 ->
i > i0
->
concatn eff1 eff6 i0 = concatn eff1 eff i0.
Proof.
induction eff.
  * intros. simpl in H1. subst. simpl_concatn. inversion H7.
  * intros. simpl in H1. rewrite <- H1 in H3.
    pose (EE1 := element_exist Value (length eff) vals (eq_sym H3)).
    inversion EE1 as [v]. inversion H8 as [vs]. destruct eff6.
    - simpl in H6. subst. rewrite <- H6 in H7. rewrite <- H6. simpl_concatn. simpl. reflexivity.
    - subst. simpl. simpl_concatn_H IHeff. simpl in H6. rewrite <- H6. simpl_concatn.
      simpl in H6. pose (EE2 := element_exist Value (length eff6) vals0 H6). inversion EE2. inversion H1.
      pose (nat_exist H2). inversion e.
      pose (EE3 := element_exist Expression x1 exps (eq_sym H9)). inversion EE3. inversion H10.
      assert (s = a). {
        subst.
        assert (0 < Datatypes.length (x :: x0)). {  simpl. omega. }
        pose (H0 0 H4).
        assert (0 < S (Datatypes.length eff)). {  simpl. omega. }
        pose (H 0 H11 (inl (nth 0 (x :: x0) ErrorValue)) (concatn eff1 (s :: eff6) 1) e0). inversion a0.
        simpl_concatn_H H13. apply app_inv_head in H13. simpl in H13. symmetry. assumption.
      }
      rewrite <- H12. subst.
      apply IHeff with (exps := x3) (vals := vs) (vals0 := x0) (eff1 := eff1 ++ a) 
                       (i0 := length eff6) (i := length eff); auto.
      + intros. assert (S j < S (Datatypes.length eff)). { simpl. omega. }
        pose (H (S j) H12 v2 eff''). rewrite concatn_app, concatn_app in a0. simpl in a0.
        pose (a0 H11). assumption.
      + intros. inversion H6. assert (S j < Datatypes.length (x :: x0)). { simpl. omega. }
        pose (H0 (S j) H11). rewrite concatn_app, concatn_app in e0. simpl in e0. assumption.
      + intuition.
      + inversion H6. auto.
      + rewrite <- H6 in H5. simpl in H5. omega.
      + omega.
Qed.

(** Based on determinsim, using lists with exceptions, these are equal *)
Lemma exception_equality {env : Environment} {exps : list Expression} (vals vals0 : list Value) 
   (ex : Exception) (eff1 : SideEffectList) (eff eff6 : list SideEffectList) (i i0 : nat) 
   (eff3 : SideEffectList) (ex0 : Exception) (eff4 : SideEffectList) :
(forall j : nat,
     j < i ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList),
     | env, nth j exps ErrorExp, concatn eff1 eff j | -e> | v2, eff'' | ->
     inl (nth j vals ErrorValue) = v2 /\ concatn eff1 eff (S j) = eff'')
->
| env, nth i0 exps ErrorExp, concatn eff1 eff6 i0 | -e> | inr ex0, concatn eff1 eff6 i0 ++ eff4 |
->
(forall (v2 : Value + Exception) (eff'' : SideEffectList),
        | env, nth i exps ErrorExp, concatn eff1 eff i | -e> | v2, eff'' | -> inr ex = v2 /\ eff3 = eff'')
->
(forall j : nat,
      j < i0 ->
      | env, nth j exps ErrorExp, concatn eff1 eff6 j | -e> | inl (nth j vals0 ErrorValue),
      concatn eff1 eff6 (S j) |)
->
Datatypes.length vals = i ->
 i < Datatypes.length exps ->
 Datatypes.length eff = i ->
 Datatypes.length vals0 = i0 ->
 i0 < Datatypes.length exps ->
 Datatypes.length eff6 = i0
->
i = i0 /\ eff = eff6 /\ vals = vals0.
Proof.
  intros. destruct (le_gt_dec i i0).
  * case_eq (le_lt_or_eq i i0 l).
    - intros. pose (P1 := H2 i l0).
      assert (concatn eff1 eff6 i = concatn eff1 eff i).
      {
        apply (con_n_equality exps vals vals0 eff1 eff6 i i0 H H2 H5 H4 H3 H6 H7 H8 l0).
      }
      rewrite H10 in P1.
      pose (P2 := H1 (inl (nth i vals0 ErrorValue)) (concatn eff1 eff6 (S i)) P1). inversion P2. inversion H11.
    - intros. subst. pose (list_equal_until_i exps vals vals0 eff6 eff1 H H2 e H5 H8 H7). auto.
  * 
    assert (concatn eff1 eff6 i0 = concatn eff1 eff i0).
    {
      apply (con_n_equality_rev exps vals vals0 eff1 eff6 i i0 H H2 H5 H4 H3 H6 H7 H8 g).
    }
    rewrite H9 in H0 at 1.
    pose (H i0 g (inr ex0) (concatn eff1 eff6 i0 ++ eff4) H0). inversion a. inversion H10.
Qed.

(** Map lists are equal *)
Lemma map_lists_equality {env : Environment} {kl : list Expression} : 
forall {vl : list Expression} (kvals vvals kvals0 vvals0 : list Value) (eff1 : SideEffectList) 
     (eff eff7 : list SideEffectList),
(forall j : nat,
     j < length vl ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList),
     | env, nth j kl ErrorExp, concatn eff1 eff (2 * j) | -e> | v2, eff'' | ->
     inl (nth j kvals ErrorValue) = v2 /\ concatn eff1 eff (S (2 * j)) = eff'')
->
(forall j : nat,
     j < length vl ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList),
     | env, nth j vl ErrorExp, concatn eff1 eff (S (2 * j)) | -e> | v2, eff'' | ->
     inl (nth j vvals ErrorValue) = v2 /\ concatn eff1 eff (S (S (2 * j))) = eff'')
->
Datatypes.length kl = Datatypes.length vl ->
length kl = Datatypes.length vvals ->
length kl = Datatypes.length kvals ->
((length kl) * 2)%nat = Datatypes.length eff ->
(forall j : nat,
      j < length vl ->
      | env, nth j kl ErrorExp, concatn eff1 eff7 (2 * j) | -e> | inl (nth j kvals0 ErrorValue),
      concatn eff1 eff7 (S (2 * j)) |)
->
(forall j : nat,
      j < length vl ->
      | env, nth j vl ErrorExp, concatn eff1 eff7 (S (2 * j)) | -e>
      | inl (nth j vvals0 ErrorValue), concatn eff1 eff7 (S (S (2 * j))) |)
->
length kl = Datatypes.length vvals0 ->
length kl = Datatypes.length kvals0 ->
((length kl) * 2)%nat = Datatypes.length eff7
->
kvals = kvals0 /\ vvals = vvals0 /\ eff = eff7.
Proof.
  induction kl.
  * intros. inversion H1. inversion H2. inversion H3. inversion H4.
    repeat unfold_list.
    inversion H7. inversion H8. inversion H9.
    repeat unfold_list.
    auto.
  * intros. inversion H1. inversion H2. inversion H3. inversion H4. simpl in H9, H14, H7, H8.
    single_unfold_list. single_unfold_list. single_unfold_list. 
    single_unfold_list. single_unfold_list. single_unfold_list.
    single_unfold_list. single_unfold_list. single_unfold_list.
    (** FIRST ELEMENTS ARE EQUAL *)
    pose (F1 := H5 0 (Nat.lt_0_succ (length x7))).
    pose (F2 := H 0 (Nat.lt_0_succ _) _ _ F1). inversion F2. inversion H31.
    rewrite concatn_app, concatn_app in H33. simpl_concatn_H H33. apply app_inv_head in H33. subst.
    pose (F3 := H6 0 (Nat.lt_0_succ (length x7))).
    pose (F4 := H0 0 (Nat.lt_0_succ _) _ _ F3). inversion F4. inversion H33.
    rewrite concatn_app, concatn_app in H34. simpl_concatn_H H34. apply app_inv_head in H34. subst. simpl.
    (** OTHER ELEMETS *)
    assert (x3 = x12 /\ x5 = x14 /\ x2 = x11).
    {
      eapply IHkl with (vl := x7); auto.
      * intros. assert (S j < length (x6 :: x7)). { simpl. omega. }
        pose (P3 := H (S j) H36 v2 eff''). simpl in P3.
        rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r, <- plus_n_Sm, concatn_app,
               <- app_assoc in P3. simpl in H35. rewrite Nat.add_0_r in H35.
        pose (P4 := P3 H35). simpl. rewrite Nat.add_0_r. assumption.
      * intros. assert (S j < length (x6 :: x7)). { simpl. omega. }
        pose (P3 := H0 (S j) H36 v2 eff''). simpl in P3.
        rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r, <- plus_n_Sm, concatn_app,
               <- app_assoc in P3. simpl in H35. rewrite Nat.add_0_r in H35.
        pose (P4 := P3 H35). simpl. rewrite Nat.add_0_r. assumption.
      * intros. assert (S j < length (x6 :: x7)). { simpl. omega. }
        pose (P3 := H5 (S j) H35). simpl in P3. 
        rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r, <- plus_n_Sm, concatn_app,
               <- app_assoc in P3. simpl. rewrite Nat.add_0_r. assumption.
      * intros. assert (S j < length (x6 :: x7)). { simpl. omega. }
        pose (P3 := H6 (S j) H35). simpl in P3.
        rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r, <- plus_n_Sm, concatn_app,
               <- app_assoc in P3. simpl. rewrite Nat.add_0_r. assumption.
    }
    inversion H34. inversion H36. subst. auto.
Qed.

(** Map lists are equal until ith element *)
Lemma map_lists_equal_until_i {env : Environment} {kl : list Expression} : forall {vl : list Expression}
   (kvals vvals kvals0 vvals0 : list Value) (i0 : nat) (eff1 : SideEffectList)
   (eff eff7 : list SideEffectList) (ex0 : Exception) (eff5 eff6 : SideEffectList) (val0 : Value),
(forall j : nat,
     j < length vl ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList),
     | env, nth j kl ErrorExp, concatn eff1 eff (2 * j) | -e> | v2, eff'' | ->
     inl (nth j kvals ErrorValue) = v2 /\ concatn eff1 eff (S (2 * j)) = eff'')
->
(forall j : nat,
     j < length vl ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList),
     | env, nth j vl ErrorExp, concatn eff1 eff (S (2 * j)) | -e> | v2, eff'' | ->
     inl (nth j vvals ErrorValue) = v2 /\ concatn eff1 eff (S (S (2 * j))) = eff'')
->
Datatypes.length kl = Datatypes.length vl ->
length kl = Datatypes.length vvals ->
length kl = Datatypes.length kvals ->
Datatypes.length eff = ((length kl) * 2)%nat ->
(forall j : nat,
      j < i0 ->
      | env, nth j kl ErrorExp, concatn eff1 eff7 (2 * j) | -e> | inl (nth j kvals0 ErrorValue),
      concatn eff1 eff7 (S (2 * j)) |)
->
(forall j : nat,
      j < i0 ->
      | env, nth j vl ErrorExp, concatn eff1 eff7 (S (2 * j)) | -e>
      | inl (nth j vvals0 ErrorValue), concatn eff1 eff7 (S (S (2 * j))) |)
->
Datatypes.length vvals0 = i0 ->
Datatypes.length kvals0 = i0 ->
i0 <= Datatypes.length kl ->
Datatypes.length eff7 = (i0 * 2)%nat ->
(| env, nth i0 kl ErrorExp, concatn eff1 eff7 (2 * i0) | -e> | inr ex0, concatn eff1 eff7 (2 * i0) ++ eff5 |
\/
(| env, nth i0 kl ErrorExp, concatn eff1 eff7 (2 * i0) | -e> | inl val0,
      concatn eff1 eff7 (2 * i0) ++ eff5 | /\
| env, nth i0 vl ErrorExp, concatn eff1 eff7 (2 * i0) ++ eff5 | -e> | 
      inr ex0, concatn eff1 eff7 (2 * i0) ++ eff5 ++ eff6 |)
)
->
length vl = i0 /\ kvals = kvals0 /\ vvals = vvals0 /\ eff = eff7.
Proof.
  induction kl.
  * intros. inversion H2. apply eq_sym, length_zero_iff_nil in H13. subst. inversion H1.
    apply eq_sym, length_zero_iff_nil in H12. subst. inversion H9. apply length_zero_iff_nil in H12.
    subst. inversion H3. apply eq_sym,  length_zero_iff_nil in H12. subst. inversion H8.
    apply length_zero_iff_nil in H12. subst. inversion H10. apply length_zero_iff_nil in H12.
    subst. inversion H4. apply length_zero_iff_nil in H12. subst. auto.
  * intros. inversion H1.
    pose (EE1 := element_exist Expression (length kl) vl H13). inversion EE1 as [ve]. inversion H12 as [ves].
    subst.
    case_eq (length vvals0).
    - intros. apply length_zero_iff_nil in H7. subst.
      apply length_zero_iff_nil in H8. apply length_zero_iff_nil in H10. subst.
      simpl_concatn_H H11.
      inversion H11.
      + pose (P1 := H 0 (Nat.lt_0_succ _) (inr ex0) (eff1 ++ eff5)).
        simpl_concatn_H P1. pose (P2 := P1 H7). inversion P2. inversion H8.
      + inversion H7. pose (P1 := H 0 (Nat.lt_0_succ _) (inl val0) (eff1 ++ eff5)).
        simpl_concatn_H P1. pose (P2 := P1 H8). inversion P2. inversion H14. subst.
        pose (P3 := H0 0 (Nat.lt_0_succ _) (inr ex0) (eff1 ++ eff5 ++ eff6)).
        simpl_concatn_H P3.
        rewrite <- H15 in H10 at 1.
        pose (P4 := P3 H10). inversion P4. inversion H16.

    - intros. rewrite H7 in *. simpl in H2, H3. simpl in H4, H10.
      pose (EE2 := element_exist Value _ kvals0 (eq_sym H8)).
      pose (EE3 := element_exist Value _ vvals0 (eq_sym H7)).
      pose (EE4 := element_exist Value _ kvals H3).
      pose (EE5 := element_exist Value _ vvals H2).
      pose (EE6 := element_exist SideEffectList _ eff (eq_sym H4)).
      pose (EE7 := element_exist SideEffectList _ eff7 (eq_sym H10)).
      inversion EE2 as [kv']. inversion EE3 as [vv']. inversion EE4 as [kv]. inversion EE5 as [vv].
      inversion EE6 as [e1]. inversion EE7 as [e1'].
      inversion H14. inversion H15. inversion H16. inversion H17. inversion H18. inversion H19. subst.
      inversion H4. inversion H10.
      pose (EE8 := element_exist SideEffectList _ x3 (eq_sym H21)).
      pose (EE9 := element_exist SideEffectList _ x4 (eq_sym H22)).
      inversion EE8 as [e2]. inversion EE9 as [e2']. inversion H20. inversion H23. subst.
      (** FIRST ELEMENTS ARE EQUAL *)
      pose (F1 := H5 0 (Nat.lt_0_succ n)).
      pose (F2 := H 0 (Nat.lt_0_succ _) _ _ F1). inversion F2. inversion H24.
      rewrite concatn_app, concatn_app in H25. simpl_concatn_H H25. apply app_inv_head in H25. subst.
      pose (F3 := H6 0 (Nat.lt_0_succ n)).
      pose (F4 := H0 0 (Nat.lt_0_succ _) _ _ F3). inversion F4. inversion H25.
      rewrite concatn_app, concatn_app in H26. simpl_concatn_H H26. apply app_inv_head in H26. subst. simpl.
      (** OTHER ELEMETS *)
      assert (length ves = n /\ x1 = x /\ x2 = x0 /\ x5 = x6).
      {
        apply IHkl with (eff1 := eff1 ++ e1' ++ e2') (ex0 := ex0) (eff5 := eff5) (vl := ves) (eff6 := eff6) (val0 := val0); auto.
        * intros. assert (S j < length (ve :: ves)). { simpl. omega. }
          pose (P3 := H (S j) H28 v2 eff''). simpl in P3.
          rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r,
                <- plus_n_Sm, concatn_app, <- app_assoc in P3. simpl in H27. rewrite Nat.add_0_r in H27.
          pose (P4 := P3 H27). simpl. rewrite Nat.add_0_r. assumption.
        * intros. assert (S j < length (ve :: ves)). { simpl. omega. }
          pose (P3 := H0 (S j) H28 v2 eff''). simpl in P3.
          rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r,
                <- plus_n_Sm, concatn_app, <- app_assoc in P3. simpl in H27. rewrite Nat.add_0_r in H27.
          pose (P4 := P3 H27). simpl. rewrite Nat.add_0_r. assumption.
        * intros. assert (S j < S n). { omega. }
          pose (P3 := H5 (S j) H27). simpl in P3.
          rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r,
                <- plus_n_Sm, concatn_app, <- app_assoc in P3. simpl. rewrite Nat.add_0_r. assumption.
        * intros. assert (S j < S n). { omega. }
          pose (P3 := H6 (S j) H27). simpl in P3.
          rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r,
               <- plus_n_Sm, concatn_app, <- app_assoc in P3. simpl. rewrite Nat.add_0_r. assumption.
        * simpl in H9. omega.
        * simpl in H11. 
          rewrite concatn_app, Nat.add_0_r, <- plus_n_Sm, concatn_app,
              <- app_assoc in H11. simpl. rewrite Nat.add_0_r. assumption.
      }
      inversion H26. inversion H28. inversion H30. subst. auto.
Qed.

(** Map lists are equal until ith key *)
Lemma map_lists_equal_until_i_key {env : Environment} {kl : list Expression} :
  forall {vl : list Expression} (kvals vvals kvals0 vvals0 : list Value) (i i0 : nat) 
     (eff1 : SideEffectList) (eff eff7 : list SideEffectList) (ex0 : Exception) 
     (eff5 eff2 eff6 : SideEffectList) (val0 : Value) (ex : Exception),
(forall j : nat,
     j < i ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList),
     | env, nth j kl ErrorExp, concatn eff1 eff (2 * j) | -e> | v2, eff'' | ->
     inl (nth j kvals ErrorValue) = v2 /\ concatn eff1 eff (S (2 * j)) = eff'')
->
(forall j : nat,
     j < i ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList),
     | env, nth j vl ErrorExp, concatn eff1 eff (S (2 * j)) | -e> | v2, eff'' | ->
     inl (nth j vvals ErrorValue) = v2 /\ concatn eff1 eff (S (S (2 * j))) = eff'')
->
(forall (v2 : Value + Exception) (eff'' : SideEffectList),
         | env, nth i kl ErrorExp, concatn eff1 eff (2 * i) | -e> | v2, eff'' | ->
         inr ex = v2 /\ concatn eff1 eff (2 * i) ++ eff2 = eff'')
->
Datatypes.length kl = Datatypes.length vl ->
Datatypes.length vvals = i ->
Datatypes.length kvals = i ->
i <= Datatypes.length kl ->
Datatypes.length eff = (i * 2)%nat ->
(forall j : nat,
      j < i0 ->
      | env, nth j kl ErrorExp, concatn eff1 eff7 (2 * j) | -e> | inl (nth j kvals0 ErrorValue),
      concatn eff1 eff7 (S (2 * j)) |)
->
(forall j : nat,
      j < i0 ->
      | env, nth j vl ErrorExp, concatn eff1 eff7 (S (2 * j)) | -e>
      | inl (nth j vvals0 ErrorValue), concatn eff1 eff7 (S (S (2 * j))) |)
->
Datatypes.length vvals0 = i0 ->
Datatypes.length kvals0 = i0 ->
i0 <= Datatypes.length kl ->
Datatypes.length eff7 = (i0 * 2)%nat ->
(| env, nth i0 kl ErrorExp, concatn eff1 eff7 (2 * i0) | -e> | inr ex0, concatn eff1 eff7 (2 * i0) ++ eff5 |
\/
(| env, nth i0 kl ErrorExp, concatn eff1 eff7 (2 * i0) | -e> | inl val0,
      concatn eff1 eff7 (2 * i0) ++ eff5 | /\
| env, nth i0 vl ErrorExp, concatn eff1 eff7 (2 * i0) ++ eff5 | -e> | 
      inr ex0, concatn eff1 eff7 (2 * i0) ++ eff5 ++ eff6 |)
)
->
i = i0 /\ kvals = kvals0 /\ vvals = vvals0 /\ eff = eff7.
Proof.
  induction kl.
  * intros. inversion H2. apply eq_sym, length_zero_iff_nil in H15. subst. inversion H11.
    apply length_zero_iff_nil in H9. subst. inversion H5. apply length_zero_iff_nil in H9.
    subst. inversion H4. apply length_zero_iff_nil in H9. subst. inversion H6.
    apply length_zero_iff_nil in H9. subst. inversion H10. apply length_zero_iff_nil in H9. subst.
    inversion H12. apply length_zero_iff_nil in H9. subst. auto.
  * intros. inversion H2. simpl in H2. 
    pose (EE1 := element_exist Expression (length kl) vl H15). inversion EE1 as [ve]. inversion H14 as [ves].
    subst.
    case_eq (length vvals); case_eq (length vvals0).
    - intros. apply length_zero_iff_nil in H3. apply length_zero_iff_nil in H9. subst.
      apply length_zero_iff_nil in H4. apply length_zero_iff_nil in H10.
      apply length_zero_iff_nil in H12. apply length_zero_iff_nil in H6. subst. auto.
    - intros. rewrite H3, H9 in *.
      apply length_zero_iff_nil in H6.
      pose (EE2 := element_exist SideEffectList _ eff7 (eq_sym H12)). inversion EE2. inversion H16.
      subst. inversion H12. 
      pose (EE3 := element_exist SideEffectList _ x0 (eq_sym H17)).
      inversion EE3. inversion H6. subst.
      pose (P1 := H7 0 (Nat.lt_0_succ n)). pose (P2 := H8 0 (Nat.lt_0_succ n)). simpl in P1, P2.
      pose (P3 := H1 _ _ P1). inversion P3.
      inversion H18.
    - intros. rewrite H3, H9 in *. simpl_concatn_H H13.
      inversion H13. 2: inversion H16.
      (** KEY EXCEPTION *)
        + pose (P2 := H 0 (Nat.lt_0_succ n) (inr ex0) (eff1 ++ eff5)).
          simpl_concatn_H P2. pose (P3 := P2 H16). inversion P3. inversion H17.
      (** VALUE EXCEPTION *)
        + pose (P2 := H 0 (Nat.lt_0_succ n) (inl val0) (eff1 ++ eff5)).
          simpl_concatn_H P2. inversion H16. pose (P3 := P2 H17).
          inversion P3.
          pose (P4 := H0 0 (Nat.lt_0_succ n) (inr ex0) (eff1 ++ eff5 ++ eff6)). simpl in P4.
          assert (concatn eff1 eff 1 = eff1 ++ eff5). { simpl_concatn. exact H22. }
          rewrite H23 in P4 at 1. rewrite <- app_assoc in H20. pose (P5 := P4 H20).
          inversion P5. inversion H24.

    - intros. rewrite H3, H9 in *. simpl in H6, H12.
      pose (EE2 := element_exist Value _ kvals0 (eq_sym H10)).
      pose (EE3 := element_exist Value _ vvals0 (eq_sym H3)).
      pose (EE4 := element_exist Value _ kvals (eq_sym H4)).
      pose (EE5 := element_exist Value _ vvals (eq_sym H9)).
      pose (EE6 := element_exist SideEffectList _ eff (eq_sym H6)).
      pose (EE7 := element_exist SideEffectList _ eff7 (eq_sym H12)).
      inversion EE2 as [kv']. inversion EE3 as [vv']. inversion EE4 as [kv]. inversion EE5 as [vv].
      inversion EE6 as [e1]. inversion EE7 as [e1']. inversion H17. inversion H18. 
      inversion H19. inversion H20. inversion H21. inversion H16. subst.
      inversion H6. inversion H12.
      pose (EE8 := element_exist SideEffectList _ x2 (eq_sym H23)).
      pose (EE9 := element_exist SideEffectList _ x3 (eq_sym H24)).
      inversion EE8 as [e2]. inversion EE9 as [e2']. inversion H22. inversion H25. subst.
      (** FIRST ELEMENTS ARE EQUAL *)
      pose (F1 := H7 0 (Nat.lt_0_succ n)).
      pose (F2 := H 0 (Nat.lt_0_succ n0) _ _ F1). inversion F2. inversion H26.
      rewrite concatn_app, concatn_app in H27. simpl_concatn_H H27. apply app_inv_head in H27. subst.
      pose (F3 := H8 0 (Nat.lt_0_succ n)).
      pose (F4 := H0 0 (Nat.lt_0_succ n0) _ _ F3). inversion F4. inversion H27.
      rewrite concatn_app, concatn_app in H28. simpl_concatn_H H28. apply app_inv_head in H28. subst.
      (** OTHER ELEMETS *)
      assert (n0 = n /\ x0 = x4 /\ x1 = x /\ x5 = x6).
      {
        apply IHkl with (eff1 := eff1 ++ e1' ++ e2') (ex0 := ex0) (eff5 := eff5) (eff2 := eff2) 
                        (ex := ex) (vl := ves) (eff6 := eff6) (val0 := val0); auto.
        * intros. assert (S j < S n0). { omega. } pose (P3 := H (S j) H30 v2 eff'').
          simpl in P3.
          rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r,
               <- plus_n_Sm, concatn_app, <- app_assoc in P3. simpl in H29. rewrite Nat.add_0_r in H29.
          pose (P4 := P3 H29). simpl. rewrite Nat.add_0_r. assumption.
        * intros. assert (S j < S n0). { omega. } 
          pose (P3 := H0 (S j) H30 v2 eff''). simpl in P3.
          rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r,
               <- plus_n_Sm, concatn_app, <- app_assoc in P3. simpl in H29. rewrite Nat.add_0_r in H29.
          pose (P4 := P3 H29). simpl. rewrite Nat.add_0_r. assumption.
        * intros. pose (P3 := H1 v2 eff''). simpl in P3. simpl in P3.
           rewrite concatn_app, Nat.add_0_r, <- plus_n_Sm, concatn_app, <- app_assoc in P3.
           simpl. rewrite Nat.add_0_r. simpl in H28. rewrite Nat.add_0_r in H28. apply (P3 H28).
        * simpl in H5. omega.
        * intros. assert (S j < S n). { omega. }
          pose (P3 := H7 (S j) H29). simpl in P3.
          rewrite Nat.add_0_r, concatn_app, concatn_app, concatn_app,
               <- plus_n_Sm, concatn_app, <- app_assoc in P3. simpl. rewrite Nat.add_0_r. assumption.
        * intros. assert (S j < S n). { omega. }
        pose (P3 := H8 (S j) H29).
          simpl in P3. 
          rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r,
               <- plus_n_Sm, concatn_app, <- app_assoc in P3. simpl. rewrite Nat.add_0_r. assumption.
        * simpl in H11. omega.
        * simpl in H13. 
          rewrite concatn_app, Nat.add_0_r, <- plus_n_Sm, concatn_app,
               <- app_assoc in H13. simpl. rewrite Nat.add_0_r. assumption.
      }
      inversion H28. inversion H30. inversion H32. subst. auto.
Qed.

Ltac simpl_concatn_app Hyp :=
repeat (rewrite Nat.add_0_r in Hyp);
repeat (rewrite plus_n_Sm in Hyp);
repeat (rewrite concatn_app in Hyp);
repeat (rewrite app_assoc in Hyp)
.

(** Map lists are equal until ith value *)
Lemma map_lists_equal_until_i_val {env : Environment} {kl : list Expression} : 
   forall {vl : list Expression} (kvals vvals kvals0 vvals0 : list Value) (i i0 : nat) 
   (eff1 : SideEffectList) (eff eff7 : list SideEffectList) (ex0 : Exception) 
   (eff5 eff2 eff4 eff6 : SideEffectList) (val val0 : Value) (ex : Exception),
(forall j : nat,
     j < i ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList),
     | env, nth j kl ErrorExp, concatn eff1 eff (2 * j) | -e> | v2, eff'' | ->
     inl (nth j kvals ErrorValue) = v2 /\ concatn eff1 eff (S (2 * j)) = eff'')
->
(forall j : nat,
     j < i ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList),
     | env, nth j vl ErrorExp, concatn eff1 eff (S (2 * j)) | -e> | v2, eff'' | ->
     inl (nth j vvals ErrorValue) = v2 /\ concatn eff1 eff (S (S (2 * j))) = eff'')
->
(forall (v2 : Value + Exception) (eff'' : SideEffectList),
         | env, nth i kl ErrorExp, concatn eff1 eff (2 * i) | -e> | v2, eff'' | ->
         inl val = v2 /\ concatn eff1 eff (2 * i) ++ eff2 = eff'')
->
(forall (v2 : Value + Exception) (eff'' : SideEffectList),
         | env, nth i vl ErrorExp, concatn eff1 eff (2 * i) ++ eff2 | -e> | v2, eff'' | ->
         inr ex = v2 /\ eff4 = eff'')
->
Datatypes.length kl = Datatypes.length vl ->
Datatypes.length vvals = i ->
Datatypes.length kvals = i ->
i <= Datatypes.length kl ->
Datatypes.length eff = (i * 2)%nat ->
(forall j : nat,
      j < i0 ->
      | env, nth j kl ErrorExp, concatn eff1 eff7 (2 * j) | -e> | inl (nth j kvals0 ErrorValue),
      concatn eff1 eff7 (S (2 * j)) |)
->
(forall j : nat,
      j < i0 ->
      | env, nth j vl ErrorExp, concatn eff1 eff7 (S (2 * j)) | -e>
      | inl (nth j vvals0 ErrorValue), concatn eff1 eff7 (S (S (2 * j))) |)
->
Datatypes.length vvals0 = i0 ->
Datatypes.length kvals0 = i0->
i0 <= Datatypes.length kl ->
Datatypes.length eff7 = (i0 * 2)%nat ->
(| env, nth i0 kl ErrorExp, concatn eff1 eff7 (2 * i0) | -e> | inr ex0, concatn eff1 eff7 (2 * i0) ++ eff5 |
\/
(| env, nth i0 kl ErrorExp, concatn eff1 eff7 (2 * i0) | -e> | inl val0,
      concatn eff1 eff7 (2 * i0) ++ eff5 | /\
| env, nth i0 vl ErrorExp, concatn eff1 eff7 (2 * i0) ++ eff5 | -e> | 
      inr ex0, concatn eff1 eff7 (2 * i0) ++ eff5 ++ eff6 |)
)
->
i = i0 /\ kvals = kvals0 /\ vvals = vvals0 /\ eff = eff7.
Proof.
  induction kl.
  * intros. inversion H3. apply eq_sym, length_zero_iff_nil in H16. subst. inversion H12.
    apply length_zero_iff_nil in H10. subst. inversion H6. apply length_zero_iff_nil in H10.
    subst. inversion H5. apply length_zero_iff_nil in H10. subst. inversion H7.
    apply length_zero_iff_nil in H10. subst. inversion H11. apply length_zero_iff_nil in H10. subst.
    inversion H13. apply length_zero_iff_nil in H10. subst. auto.
  * intros. inversion H3. simpl in H3. 
    pose (EE1 := element_exist Expression (length kl) vl H16). inversion EE1 as [ve]. inversion H15 as [ves]. subst.
    case_eq (length vvals); case_eq (length vvals0).
    - intros. apply length_zero_iff_nil in H4. apply length_zero_iff_nil in H10. subst.
      apply length_zero_iff_nil in H5. apply length_zero_iff_nil in H11.
      apply length_zero_iff_nil in H13. apply length_zero_iff_nil in H7. subst. auto.
    - intros. rewrite H4, H10 in *.
      apply length_zero_iff_nil in H7.
      pose (EE2 := element_exist SideEffectList _ eff7 (eq_sym H13)). inversion EE2. inversion H17. subst.
      inversion H13. pose (EE3 := element_exist SideEffectList _ x0 (eq_sym H18)). inversion EE3. inversion H7.
      subst.
      pose (P1 := H8 0 (Nat.lt_0_succ n)). pose (P2 := H9 0 (Nat.lt_0_succ n)). simpl in P1, P2.
      pose (P3 := H1 _ _ P1). inversion P3.
      inversion H19. rewrite concatn_app in H20. simpl_concatn_H H20. apply app_inv_head in H20. subst.
      simpl_concatn_H H2. simpl_concatn_H P2.
      pose (P4 := H2 _ _ P2). inversion P4. inversion H20.
    - intros. rewrite H4, H10 in *. simpl_concatn_H H14.
      inversion H14. 2: inversion H17.
      (** KEY EXCEPTION *)
        + pose (P2 := H 0 (Nat.lt_0_succ n) (inr ex0) (eff1 ++ eff5)).
          simpl_concatn_H P2. pose (P3 := P2 H17). inversion P3. inversion H18.
      (** VALUE EXCEPTION *)
        + pose (P2 := H 0 (Nat.lt_0_succ n) (inl val0) (eff1 ++ eff5)). simpl_concatn_H P2.
          inversion H17. pose (P3 := P2 H18).
          inversion P3.
          pose (P4 := H0 0 (Nat.lt_0_succ n) (inr ex0) (eff1 ++ eff5 ++ eff6)). simpl in P4.
          inversion P3.
          assert (concatn eff1 eff 1 = eff1 ++ eff5). { simpl_concatn. exact H23. }
          rewrite H26 in P4. rewrite <- app_assoc in H19. pose (P5 := P4 H19). inversion P5. inversion H27.

    - intros. rewrite H4, H10 in *. simpl in H7, H13.
      pose (EE2 := element_exist Value _ kvals0 (eq_sym H11)).
      pose (EE3 := element_exist Value _ vvals0 (eq_sym H4)).
      pose (EE4 := element_exist Value _ kvals (eq_sym H5)).
      pose (EE5 := element_exist Value _ vvals (eq_sym H10)).
      pose (EE6 := element_exist SideEffectList _ eff (eq_sym H7)).
      pose (EE7 := element_exist SideEffectList _ eff7 (eq_sym H13)).
      inversion EE2 as [kv']. inversion EE3 as [vv']. inversion EE4 as [kv]. inversion EE5 as [vv].
      inversion EE6 as [e1]. inversion EE7 as [e1'].
      inversion H17. inversion H18. inversion H19. inversion H20. inversion H21. inversion H22. subst.
      inversion H7. inversion H13.
      pose (EE8 := element_exist SideEffectList _ x3 (eq_sym H24)).
      pose (EE9 := element_exist SideEffectList _ x4 (eq_sym H25)).
      inversion EE8 as [e2]. inversion EE9 as [e2']. inversion H23. inversion H26. subst.
      (** FIRST ELEMENTS ARE EQUAL *)
      pose (F1 := H8 0 (Nat.lt_0_succ n)).
      pose (F2 := H 0 (Nat.lt_0_succ n0) _ _ F1). inversion F2. inversion H27.
      simpl_concatn_app H28. simpl_concatn_H H28. apply app_inv_head in H28. subst.
      pose (F3 := H9 0 (Nat.lt_0_succ n)).
      pose (F4 := H0 0 (Nat.lt_0_succ n0) _ _ F3). inversion F4. 
      inversion H28. simpl_concatn_app H29. simpl_concatn_H H29. 
      apply app_inv_head in H29. subst.
      (** OTHER ELEMETS *)
      assert (n0 = n /\ x1 = x /\ x2 = x0 /\ x5 = x6).
      {
        apply IHkl with (eff1 := eff1 ++ e1' ++ e2') (ex0 := ex0) (eff5 := eff5)
             (eff4 := eff4) (eff2 := eff2) (val := val) (ex := ex) (vl := ves) (eff6 := eff6) (val0 := val0); auto.
        * intros. assert (S j < S n0). { omega. } pose (P3 := H (S j) H31 v2 eff''). simpl in P3.
          rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r, <- plus_n_Sm, concatn_app,
               <- app_assoc in P3. simpl in H30. rewrite Nat.add_0_r in H30.
          pose (P4 := P3 H30). simpl. rewrite Nat.add_0_r. assumption.
        * intros. assert (S j < S n0). { omega. } pose (P3 := H0 (S j) H31 v2 eff''). simpl in P3.
          rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r, <- plus_n_Sm, concatn_app,
               <- app_assoc in P3. simpl in H30. rewrite Nat.add_0_r in H30.
          pose (P4 := P3 H30). simpl. rewrite Nat.add_0_r. assumption.
        * intros. pose (P3 := H1 v2 eff''). simpl in P3. simpl in P3.
          rewrite concatn_app, Nat.add_0_r, <- plus_n_Sm, concatn_app, <- app_assoc in P3.
          simpl. rewrite Nat.add_0_r. simpl in H29. rewrite Nat.add_0_r in H29. apply (P3 H29).
        * intros. pose (P3 := H2 v2 eff''). simpl in P3. simpl in P3.
          rewrite concatn_app, Nat.add_0_r, <- plus_n_Sm, concatn_app, <- app_assoc in P3.
          simpl in H29. rewrite Nat.add_0_r in H29. apply (P3 H29).
        * simpl in H6. omega.
        * intros. assert (S j < S n). { omega. } pose (P3 := H8 (S j) H30). simpl in P3.
          rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r, <- plus_n_Sm, concatn_app,
             <- app_assoc in P3. simpl. rewrite Nat.add_0_r. assumption.
        * intros. assert (S j < S n). { omega. } pose (P3 := H9 (S j) H30). simpl in P3.
          rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r, <- plus_n_Sm, concatn_app,
             <- app_assoc in P3. simpl. rewrite Nat.add_0_r. assumption.
        * simpl in H12. omega.
        * simpl in H14. rewrite concatn_app, Nat.add_0_r, <- plus_n_Sm, concatn_app,
                            <- app_assoc in H14. simpl. rewrite Nat.add_0_r. assumption.
      }
      inversion H29. inversion H31. inversion H33. subst. auto.
Qed.

(** Map attribute restriction to shorter lists *)
Lemma restrict_map {env : Environment} {kl : list Expression} (ves : list Expression) (eff1 : SideEffectList) 
    (a ve : Expression) (e1' e2' : SideEffectList) (x5 : list SideEffectList) (n : nat) 
    (eff2 : SideEffectList) (val : Value) (eff4 : SideEffectList) (ex : Exception) :
((forall (v2 : Value + Exception) (eff'' : SideEffectList),
        | env, nth (S n) (a :: kl) ErrorExp, concatn eff1 (e1' :: e2' :: x5) (2 * S n) | -e> | v2, eff'' | ->
        inr ex = v2 /\ concatn eff1 (e1' :: e2' :: x5) (2 * S n) ++ eff2 = eff'') \/
       (forall (v2 : Value + Exception) (eff'' : SideEffectList),
        | env, nth (S n) (a :: kl) ErrorExp, concatn eff1 (e1' :: e2' :: x5) (2 * S n) | -e> | v2, eff'' | ->
        inl val = v2 /\ concatn eff1 (e1' :: e2' :: x5) (2 * S n) ++ eff2 = eff'') /\
       (forall (v2 : Value + Exception) (eff'' : SideEffectList),
        | env, nth (S n) (ve :: ves) ErrorExp, concatn eff1 (e1' :: e2' :: x5) (2 * S n) ++ eff2 | -e> | v2,
        eff'' | -> inr ex = v2 /\ eff4 = eff''))
->
(forall (v2 : Value + Exception) (eff'' : SideEffectList),
 | env, nth n kl ErrorExp, concatn (eff1 ++ e1' ++ e2') x5 (2 * n) | -e> | v2, eff'' | ->
 inr ex = v2 /\ concatn (eff1 ++ e1' ++ e2') x5 (2 * n) ++ eff2 = eff'') \/
(forall (v2 : Value + Exception) (eff'' : SideEffectList),
 | env, nth n kl ErrorExp, concatn (eff1 ++ e1' ++ e2') x5 (2 * n) | -e> | v2, eff'' | ->
 inl val = v2 /\ concatn (eff1 ++ e1' ++ e2') x5 (2 * n) ++ eff2 = eff'') /\
(forall (v2 : Value + Exception) (eff'' : SideEffectList),
 | env, nth n ves ErrorExp, concatn (eff1 ++ e1' ++ e2') x5 (2 * n) ++ eff2 | -e> | v2, eff'' | ->
 inr ex = v2 /\ eff4 = eff'').
Proof.
  intros. inversion H.
  * left. simpl in H0.
    rewrite concatn_app, Nat.add_0_r, Nat.add_succ_r, concatn_app, <- app_assoc in H0. simpl.
    rewrite Nat.add_0_r. exact H0.
  * right. simpl in H0.
    rewrite concatn_app, Nat.add_0_r, Nat.add_succ_r, concatn_app, <- app_assoc in H0.
    simpl. rewrite Nat.add_0_r. exact H0.
Qed.

(** Map generalised until i-th element equality *)
Lemma map_lists_equal_until_i_key_or_val {env : Environment} {kl : list Expression} : 
forall {vl : list Expression} (kvals vvals kvals0 vvals0 : list Value) (i : nat) (eff1 : SideEffectList) 
      (eff eff7 : list SideEffectList) (eff2 eff4 : SideEffectList) (val : Value) (ex : Exception),
(forall j : nat,
     j < i ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList),
     | env, nth j kl ErrorExp, concatn eff1 eff (2 * j) | -e> | v2, eff'' | ->
     inl (nth j kvals ErrorValue) = v2 /\ concatn eff1 eff (S (2 * j)) = eff'')
->
(forall j : nat,
     j < i ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList),
     | env, nth j vl ErrorExp, concatn eff1 eff (S (2 * j)) | -e> | v2, eff'' | ->
     inl (nth j vvals ErrorValue) = v2 /\ concatn eff1 eff (S (S (2 * j))) = eff'')
->
(
(forall (v2 : Value + Exception) (eff'' : SideEffectList),
         | env, nth i kl ErrorExp, concatn eff1 eff (2 * i) | -e> | v2, eff'' | ->
         inr ex = v2 /\ concatn eff1 eff (2 * i) ++ eff2 = eff'')
\/
(forall (v2 : Value + Exception) (eff'' : SideEffectList),
         | env, nth i kl ErrorExp, concatn eff1 eff (2 * i) | -e> | v2, eff'' | ->
         inl val = v2 /\ concatn eff1 eff (2 * i) ++ eff2 = eff'')
/\
(forall (v2 : Value + Exception) (eff'' : SideEffectList),
         | env, nth i vl ErrorExp, concatn eff1 eff (2 * i) ++ eff2 | -e> | v2, eff'' | ->
         inr ex = v2 /\ eff4 = eff''))
->
Datatypes.length kl = Datatypes.length vl ->
Datatypes.length vvals = i ->
Datatypes.length kvals = i ->
i <= Datatypes.length kl ->
Datatypes.length eff = (i * 2)%nat ->
(forall j : nat,
      j < length vl ->
      | env, nth j kl ErrorExp, concatn eff1 eff7 (2 * j) | -e> | inl (nth j kvals0 ErrorValue),
      concatn eff1 eff7 (S (2 * j)) |)
->
(forall j : nat,
      j < length vl ->
      | env, nth j vl ErrorExp, concatn eff1 eff7 (S (2 * j)) | -e>
      | inl (nth j vvals0 ErrorValue), concatn eff1 eff7 (S (S (2 * j))) |)
->
length kl = Datatypes.length vvals0 ->
length kl = Datatypes.length kvals0 ->
Datatypes.length eff7 = (length kl * 2)%nat
->
i = length vl /\ kvals = kvals0 /\ vvals = vvals0 /\ eff = eff7.
Proof.
  induction kl.
  * intros. simpl in H11. rewrite <- H11 in *. inversion H5. subst.
    apply eq_sym, length_zero_iff_nil in H9.
    apply eq_sym, length_zero_iff_nil in H10.
    apply eq_sym, length_zero_iff_nil in H2.
    apply length_zero_iff_nil in H12.
    apply length_zero_iff_nil in H11.
    subst.
    simpl in H4, H6.
    apply length_zero_iff_nil in H4.
    apply length_zero_iff_nil in H6.
    subst. auto.
  * intros. inversion H2.
    pose (EE1 := element_exist Expression (length kl) vl H13). inversion EE1 as [ve]. inversion H12 as [ves]. subst.
    case_eq (length vvals).
    - intros. apply length_zero_iff_nil in H3. subst. simpl length in *.
      apply length_zero_iff_nil in H4. subst.
      pose (E1 := H7 0 (Nat.lt_0_succ (length ves))).
      pose (E2 := H8 0 (Nat.lt_0_succ (length ves))).
    (** CASE SEPARATION, KEY EXCEPTION OR VALUE EXCEPTION HAPPENED *)
      inversion H1.
      + pose (P1 := H3 _ _ E1). inversion P1. inversion H4.
      + inversion H3. pose (P1 := H4 _ _ E1). inversion P1. inversion H15.
        rewrite <- H16 in E2.
        pose (P2 := H14 _ _ E2). inversion P2. inversion H17.

    - intros. rewrite H3 in *. simpl mult in H11, H6. simpl length in *.
      pose (EE2 := element_exist Value _ kvals0 H10).
      pose (EE3 := element_exist Value _ vvals0 H9).
      pose (EE4 := element_exist Value _ kvals (eq_sym H4)).
      pose (EE5 := element_exist Value _ vvals (eq_sym H3)).
      pose (EE6 := element_exist SideEffectList _ eff (eq_sym H6)).
      pose (EE7 := element_exist SideEffectList _ eff7 (eq_sym H11)).
      inversion EE2 as [kv']. inversion EE3 as [vv']. inversion EE4 as [kv]. inversion EE5 as [vv].
      inversion EE6 as [e1]. inversion EE7 as [e1']. inversion H14. inversion H15. inversion H16. inversion H17. 
      inversion H18. inversion H19. subst.
      inversion H6. inversion H11.
      pose (EE8 := element_exist SideEffectList _ x3 (eq_sym H21)).
      pose (EE9 := element_exist SideEffectList _ x4 (eq_sym H22)).
      inversion EE8 as [e2]. inversion EE9 as [e2']. inversion H20. inversion H23. subst.
      (** FIRST ELEMENTS ARE EQUAL *)
      pose (F1 := H7 0 (Nat.lt_0_succ (length ves))).
      pose (F2 := H 0 (Nat.lt_0_succ n) _ _ F1). inversion F2. inversion H24.
      rewrite concatn_app, concatn_app in H25. simpl_concatn_H H25. apply app_inv_head in H25. subst.
      pose (F3 := H8 0 (Nat.lt_0_succ (length ves))).
      pose (F4 := H0 0 (Nat.lt_0_succ n) _ _ F3). inversion F4. inversion H25.
      rewrite concatn_app, concatn_app in H26. simpl_concatn_H H26. apply app_inv_head in H26. subst.
      (** OTHER ELEMETS *)
      assert (n = length ves /\ x1 = x /\ x2 = x0 /\ x5 = x6).
      {
        apply IHkl with (eff1 := eff1 ++ e1' ++ e2') (eff4 := eff4) (eff2 := eff2)
                (val := val) (ex := ex) (vl := ves); auto.
        * intros. assert (S j < S n). { omega. }
          pose (P3 := H (S j) H28 v2 eff''). simpl in P3.
          rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r, <- plus_n_Sm, concatn_app,
              <- app_assoc in P3. simpl in H27. rewrite Nat.add_0_r in H27.
          pose (P4 := P3 H27). simpl. rewrite Nat.add_0_r. assumption.
        * intros. assert (S j < S n). { omega. }
          pose (P3 := H0 (S j) H28 v2 eff''). simpl in P3.
          rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r, <- plus_n_Sm, concatn_app,
              <- app_assoc in P3. simpl in H27. rewrite Nat.add_0_r in H27.
          pose (P4 := P3 H27). simpl. rewrite Nat.add_0_r. assumption.
        * intros. apply restrict_map in H1. assumption.
        * simpl in H5. omega.
        * intros. assert (S j < S (length ves)). { omega. } pose (P3 := H7 (S j) H27).
          simpl in P3.
          rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r, <- plus_n_Sm,
             concatn_app, <- app_assoc in P3. simpl. rewrite Nat.add_0_r. assumption.
        * intros. assert (S j < S (length ves)). { omega. }
          pose (P3 := H8 (S j) H27). simpl in P3. 
          rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r, <- plus_n_Sm,
               concatn_app, <- app_assoc in P3. simpl. rewrite Nat.add_0_r. assumption.
      }
      inversion H26. inversion H28. inversion H30. subst. auto.
Qed.

End Core_Erlang_Determinism_Helpers.