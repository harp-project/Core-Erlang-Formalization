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

Theorem last_element_equal {A : Type} (l : list A) (def def2 : A):
  last l def = last (def :: l) def2.
Proof.
  induction l.
  * auto.
  * simpl. rewrite IHl. simpl. destruct l; auto.
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
    (x3 : list Value) (id' : nat) (ids : list nat) (id : nat):
(forall i : nat,
    i < Datatypes.length (a :: exps) ->
    | env, nth_id (id'::ids) id i, nth i (a :: exps) ErrorExp, concatn eff1 (x1 :: x6) i | -e>
    | nth_id (id'::ids) id (S i), inl (nth i (x0 :: x3) ErrorValue), concatn eff1 (x1 :: x6) (S i) |)
->
forall i : nat,
    i < Datatypes.length exps ->
    | env, nth_id ids id' i, nth i exps ErrorExp, concatn (eff1 ++ x1) x6 i | -e>
    | nth_id ids id' (S i), inl (nth i x3 ErrorValue), concatn (eff1 ++ x1) x6 (S i) |
.
Proof.
  intros.
  assert (S i < Datatypes.length (a :: exps)) as A1.
  { simpl. apply lt_n_S. assumption. } pose (E := H (S i) A1). 
  pose (P1 := @concatn_app eff1 x1 x6 i).
  pose (P2 := @concatn_app eff1 x1 x6 (S i)).
  rewrite P1, P2 in E. simpl in E. simpl. unfold nth_id. exact E.
Qed.

(** Value lists are equal ased on the determinism hypotheses *)
Lemma list_equality {env : Environment} {exps : list Expression} {eff1 : SideEffectList} : 
forall vals vals0 : list Value, forall eff eff4 : list SideEffectList,
forall id ids ids0,
  (forall i : nat,
     i < Datatypes.length exps ->
     | env, nth_id ids id i, nth i exps ErrorExp, concatn eff1 eff i | 
     -e> 
     | nth_id ids id (S i), inl (nth i vals ErrorValue), concatn eff1 eff (S i) |)
->
(forall i : nat,
     i < Datatypes.length exps ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, nth_id ids id i, nth i exps ErrorExp, concatn eff1 eff i |
     -e>
     | id'', v2, eff'' | ->
     inl (nth i vals ErrorValue) = v2 /\ concatn eff1 eff (S i) = eff'' /\ nth_id ids id (S i) = id'')
->
(forall i : nat,
     i < Datatypes.length exps ->
     | env, nth_id ids0 id i, nth i exps ErrorExp, concatn eff1 eff4 i |
     -e> 
     | nth_id ids0 id (S i), inl (nth i vals0 ErrorValue), concatn eff1 eff4 (S i) |)
->
Datatypes.length exps = Datatypes.length vals0
->
Datatypes.length exps = Datatypes.length eff4
->
Datatypes.length exps = Datatypes.length vals
->
Datatypes.length exps = Datatypes.length eff
->
length exps = length ids
->
length exps = length ids0
->
eff = eff4 /\ vals = vals0 /\ ids = ids0.
Proof.
  generalize dependent eff1. induction exps.
  * intros. inversion H3. inversion H2. inversion H4. inversion H5. inversion H6. inversion H7.
    repeat (unfold_list).
    auto.
  * intros. inversion H3. inversion H2. inversion H4. inversion H5. inversion H6. inversion H7.
  
  (* first elements are the same *)
    single_unfold_list. single_unfold_list.
    single_unfold_list. single_unfold_list.
    single_unfold_list. single_unfold_list.
    pose (P1 := H1 0 list_length). simpl_concatn_H P1.
    pose (P2 := H0 0 list_length (inl x7) (concatn eff1 (x9 :: x10) 1) x). simpl_concatn_H P2.
    pose (P3 := P2 P1). inversion P3. inversion H25. inversion H27. apply app_inv_head in H28. subst.
  (* remaining lists are the same *)

  (* These three asserts ensure, that if something states for every element in 
    a (b::l) list, then it states for every element in l too*)
    assert (
      (forall i : nat,
    i < Datatypes.length exps ->
    | env, nth_id x2 x i, nth i exps ErrorExp, concatn (eff1 ++ x9) x4 i | -e> | nth_id x2 x (S i), inl (nth i x6 ErrorValue),
    concatn (eff1 ++ x9) x4 (S i) |)
    ).
    {
      intros. pose (P4 := restrict_helper a _ _ _ _ _ _ _ H i H28). assumption.
    }
    assert (
      (forall i : nat,
      i < Datatypes.length exps ->
      forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
      | env, nth_id x2 x i, nth i exps ErrorExp, concatn (eff1 ++ x9) x4 i | -e> | id'', v2, eff'' | ->
      inl (nth i x6 ErrorValue) = v2 /\ concatn (eff1 ++ x9) x4 (S i) = eff'' /\ nth_id x2 x (S i) = id'')
    ).
    {
      intros. assert (S i < Datatypes.length (a::exps)). { simpl. omega. } 
      pose (P4 := H0 (S i) H31 v2 eff'' id''). simpl nth in P4. rewrite concatn_app in P4. 
      rewrite concatn_app in P4. exact (P4 H30).
    }
    assert (
     (forall i : nat,
    i < Datatypes.length exps ->
    | env, nth_id x0 x i, nth i exps ErrorExp, concatn (eff1 ++ x9) x10 i | -e> | nth_id x0 x (S i), inl (nth i x8 ErrorValue),
    concatn (eff1 ++ x9) x10 (S i) |)
    ).
    {
      intros. assert (S i < Datatypes.length (a :: exps)). { simpl. omega. } 
      pose (P4 := H1 (S i) H31). simpl nth in P4. rewrite concatn_app in P4. 
      rewrite concatn_app in P4. simpl in P4. assumption.
    }
    (* simpl list lengths *)
    inversion H10. inversion H11. inversion H12. inversion H13. inversion H14.
    pose (IH := IHexps (eff1 ++ x9) x6 x8 x4 x10 x x2 x0 H28 H29 H30 H32 H26 H33 H34 H35 H36). 
    inversion IH. inversion H37. subst. auto.
Qed.

Proposition nat_ge_or : forall {n m : nat}, n >= m <-> n = m \/ n > m.
Proof.
  intros. omega.
Qed.

(** Based on determinism hypotheses, the same clause was chosen in case evaluation *)
Lemma index_case_equality {env : Environment} {patterns : list Pattern} 
    {guards bodies : list Expression} {v0 : Value} (i i0 : nat) 
    (guard guard0 exp exp0 : Expression) (bindings bindings0 : list (Var * Value)) 
    (eff1 : SideEffectList) (id' : nat) : 
  (forall j : nat,
     j < i ->
     forall (gg ee : Expression) (bb : list (Var * Value)),
     match_clause v0 patterns guards bodies j = Some (gg, ee, bb) ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
     | add_bindings bb env, id', gg, eff1 | -e> | id'', v2, eff'' | ->
     inl ffalse = v2 /\ eff1 = eff'' /\ id' = id'')
  ->
  (forall j : nat,
      j < i0 ->
      forall (gg ee : Expression) (bb : list (Var * Value)),
      match_clause v0 patterns guards bodies j = Some (gg, ee, bb) ->
      | add_bindings bb env, id', gg, eff1 | -e> | id', inl ffalse, eff1 |)
  ->
  match_clause v0 patterns guards bodies i = Some (guard, exp, bindings)
  ->
  match_clause v0 patterns guards bodies i0 = Some (guard0, exp0, bindings0)
  ->
  | add_bindings bindings0 env, id', guard0, eff1 | -e> | id', inl ttrue, eff1 |
  ->
  | add_bindings bindings env, id', guard, eff1 | -e> | id', inl ttrue, eff1 |
  ->
  (forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
         | add_bindings bindings env, id', guard, eff1 | -e> | id'', v2, eff'' | ->
         inl ttrue = v2 /\ eff1 = eff'' /\ id' = id'')
->
  i = i0.
Proof.
  intros. pose (D := Nat.lt_decidable i i0). destruct D.
  * pose (P1 := H0 i H6 guard exp bindings H1). pose (P2 := H5 (inl ffalse) _ _ P1). 
    inversion P2. inversion H7.
  * apply not_lt in H6. apply (nat_ge_or) in H6. inversion H6.
    - assumption.
    - pose (P3 := H i0 H7 guard0 exp0 bindings0 H2 (inl ttrue) _ _ H3). inversion P3. inversion H8.
Qed.

(** Based on determinism, until the i-th element, the side effects are equal *)
Lemma firstn_eq {env : Environment} {eff : list SideEffectList} : 
forall (eff5 : list SideEffectList) (exps : list Expression) (vals vals0 : list Value) 
   (eff1 : SideEffectList) (ids ids0 : list nat) (id id'' : nat) ex eff3,
length exps = length vals ->
Datatypes.length exps = Datatypes.length eff
->
Datatypes.length eff5 = Datatypes.length vals0
->
Datatypes.length vals0 < Datatypes.length exps 
->
length exps = length ids
->
length ids0 = length vals0
->
(forall i : nat,
     i < Datatypes.length exps ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, nth_id ids id i, nth i exps ErrorExp, concatn eff1 eff i | -e> | id'', v2, eff'' | ->
     inl (nth i vals ErrorValue) = v2 /\ concatn eff1 eff (S i) = eff'' /\ nth_id ids id (S i) = id'')
->
(forall j : nat,
     j < Datatypes.length vals0 ->
     | env, nth_id ids0 id j, nth j exps ErrorExp, concatn eff1 eff5 j | -e> | nth_id ids0 id (S j), inl (nth j vals0 ErrorValue),
     concatn eff1 eff5 (S j) |)
->
| env, last ids0 id, nth (Datatypes.length vals0) exps ErrorExp,
      concatn eff1 eff5 (Datatypes.length vals0) | -e> | id'', inr ex,
      concatn eff1 eff5 (Datatypes.length vals0) ++ eff3 |
->
False.
Proof.
  induction eff.
  * intros. inversion H0. rewrite H9 in H2. inversion H2.
  * intros. destruct eff5.
    - inversion H1. simpl in H1. apply eq_sym, length_zero_iff_nil in H1. subst.
      simpl in H4.
      apply length_zero_iff_nil in H4. subst. simpl in H0. rewrite H0 in H5.
      pose (P := H5 0 (Nat.lt_0_succ _) _ _ _ H7). destruct P. inversion H1.
    - inversion H1. simpl.
    (* first elements *)
      inversion H0.
      assert (0 < length exps). { omega. }
      assert (0 < length vals0). { omega. }
      assert (0 < length ids0). { omega. }
      simpl in H0, H1.
      (* single_unfold_list H1. *)
      assert (Datatypes.length exps = S (Datatypes.length eff)) as Helper. { auto. }
      assert (Datatypes.length ids0 = Datatypes.length vals0) as Helper2. { auto. }
      assert (Datatypes.length exps = Datatypes.length ids) as Helper3. { auto. }
      pose (EE1 := element_exist _ _ _ (eq_sym H10)).
      pose (EE2 := element_exist _ _ _ H1).
      rewrite H in H0.
      pose (EE3 := element_exist _ _ _ (eq_sym H0)).
      rewrite <- H1 in H4. rewrite H10 in H3.
      pose (EE4 := element_exist _ _ _ H3).
      pose (EE5 := element_exist _ _ _ (eq_sym H4)).
      inversion EE1 as [e]. inversion EE2 as [v]. inversion EE3 as [v'].
      inversion EE4 as [id0']. inversion EE5 as [id0'']. 
      inversion H13. inversion H14. inversion H15. inversion H16. inversion H17. subst.
      pose (P0 := H6 0 H11). simpl_concatn_H P0.
      pose (P1 := H5 0 H8 (inl v) (eff1 ++ s ++ [])). simpl_concatn_H P1.
      pose (P2 := P1 _ P0). destruct P2. destruct H18, H19. apply app_inv_head in H18. subst.
    (* other elements *)
      inversion H1.
      eapply IHeff with (exps := x) (vals := x1) (vals0 := x0) (eff1 := eff1 ++ s) (ids := x2) (ids0 := x3) (id := id0'') (eff5 := eff5); auto.
        + intuition.
        + intros. assert (S i < Datatypes.length (e :: x)). { simpl. omega. }
          pose (A := H5 (S i) H21 v2 eff''). rewrite concatn_app, concatn_app in A.
          simpl in A, H20.
          pose (B := A _ H20). assumption.
        + intros. assert (S j < Datatypes.length (v :: x0)). { omega. } 
          pose (A := H6 (S j) H20). 
          rewrite concatn_app, concatn_app in A. simpl in A. exact A.
        + rewrite <- last_element_equal in H7. simpl in H7. rewrite concatn_app in H7. exact H7.
Qed.

(** Side effect equality until the ith element using concatn *)
Lemma eff_until_i {env : Environment} {eff : list SideEffectList} : 
forall (eff5 : list SideEffectList) {exps : list Expression} (vals vals0 : list Value) 
   (eff1 : SideEffectList) (ids ids0 : list nat) (id id'' : nat) ex  eff3,
length exps = length vals ->
Datatypes.length exps = Datatypes.length eff
->
Datatypes.length eff5 = Datatypes.length vals0
->
Datatypes.length vals0 < Datatypes.length exps 
->
length exps = length ids
->
length ids0 = length vals0
->
(forall i : nat,
     i < Datatypes.length exps ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, nth_id ids id i, nth i exps ErrorExp, concatn eff1 eff i | -e> | id'', v2, eff'' | ->
     inl (nth i vals ErrorValue) = v2 /\ concatn eff1 eff (S i) = eff'' /\ nth_id ids id (S i) = id'')
->
(forall j : nat,
     j < Datatypes.length vals0 ->
     | env, nth_id ids0 id j, nth j exps ErrorExp, concatn eff1 eff5 j | -e> | nth_id ids0 id (S j), inl (nth j vals0 ErrorValue),
     concatn eff1 eff5 (S j) |)
->
| env, last ids0 id, nth (Datatypes.length vals0) exps ErrorExp,
      concatn eff1 eff5 (Datatypes.length vals0) | -e> | id'', inr ex,
      concatn eff1 eff5 (Datatypes.length vals0) ++ eff3 |
->
  False.
Proof.
  intros. simpl_concatn. pose (P := firstn_eq eff5 exps vals vals0 _ _ _ _ _ _ _ H H0 H1 H2 H3 H4 H5 H6 H7). inversion P.
Qed.

(** First i elements are equal, but with changed hypotheses *)
Lemma firstn_eq_rev {env : Environment} {eff : list SideEffectList} : 
   forall (eff5 : list SideEffectList) (exps : list Expression) (vals vals0 : list Value) 
          (eff1 : SideEffectList) (ids ids0 : list nat) (id : nat),
(forall j : nat,
     j < Datatypes.length vals ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, nth_id ids id j, nth j exps ErrorExp, concatn eff1 eff j | -e> | id'', v2, eff'' | ->
     inl (nth j vals ErrorValue) = v2 /\ concatn eff1 eff (S j) = eff'' /\ nth_id ids id (S j) = id'')
->
(forall i : nat,
     i < Datatypes.length exps ->
     | env, nth_id ids0 id i, nth i exps ErrorExp, concatn eff1 eff5 i | -e> | nth_id ids0 id (S i), inl (nth i vals0 ErrorValue),
     concatn eff1 eff5 (S i) |)
->
Datatypes.length vals < Datatypes.length exps ->
Datatypes.length eff = Datatypes.length vals ->
Datatypes.length exps = Datatypes.length vals0 ->
Datatypes.length exps = Datatypes.length eff5 ->
length exps = length ids0 ->
length ids = length vals
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
      assert (S (Datatypes.length eff) = Datatypes.length vals) as Helper1. { auto. }
      assert (Datatypes.length exps = Datatypes.length ids0) as Helper2. { auto. }
      (* single_unfold_list H9. *)
      pose (EE1 := element_exist Expression (length eff5) exps (eq_sym H4)).
      pose (EE2 := element_exist Value (length eff) vals H8).
      rewrite H4 in H3, H5. rewrite <- H8 in H6.
      pose (EE3 := element_exist Value (length eff5) vals0 H3).
      pose (EE4 := element_exist _ _ _ (eq_sym H6)).
      pose (EE5 := element_exist _ _ _ H5).

      inversion EE1 as [e]. inversion EE2 as [v]. inversion EE3 as [v'].
      inversion EE4 as [id']. inversion EE5 as [id'']. 
      inversion H12. inversion H13. inversion H14. inversion H15. inversion H16. subst.
      pose (P0 := H0 0 H7). simpl_concatn_H P0.
      pose (P1 := H 0 H10 (inl v') (eff1 ++ s ++ [])). simpl_concatn_H P1.
      pose (P2 := P1 _ P0). destruct P2. destruct H18. apply app_inv_head in H18. inversion H17. subst.
    (* other elements *)
      inversion H2.
      assert (firstn (Datatypes.length x0) eff5 = firstn (Datatypes.length x0) eff).
      {
        apply IHeff with (exps := x) (vals := x0) (eff1 := eff1 ++ s) (vals0 := x1) (ids := x2) (ids0 := x3) (id := id''); auto.
        - intros. assert (S j < Datatypes.length (v' :: x0)). { simpl. omega. } 
          pose (A := H (S j) H21 v2 eff''). rewrite concatn_app, concatn_app in A. simpl in A. 
          pose (B := A _ H20). assumption.
        - intros. assert (S i < Datatypes.length (e :: x)). { simpl. omega. } 
          pose (A := H0 (S i) H20). rewrite concatn_app, concatn_app in A. simpl in A. exact A.
        - intuition.
        - inversion H6. omega.
      }
      rewrite <- H19 in H18. rewrite H18. reflexivity.
Qed.

(** First i (length vals) element are equal with concatn *)
Lemma eff_until_i_rev {env : Environment} {eff : list SideEffectList} : 
   forall (eff5 : list SideEffectList) (exps : list Expression) (vals vals0 : list Value) 
          (eff1 : SideEffectList) (ids ids0 : list nat) (id : nat),
(forall j : nat,
     j < Datatypes.length vals ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, nth_id ids id j, nth j exps ErrorExp, concatn eff1 eff j | -e> | id'', v2, eff'' | ->
     inl (nth j vals ErrorValue) = v2 /\ concatn eff1 eff (S j) = eff'' /\ nth_id ids id (S j) = id'')
->
(forall i : nat,
     i < Datatypes.length exps ->
     | env, nth_id ids0 id i, nth i exps ErrorExp, concatn eff1 eff5 i | -e> | nth_id ids0 id (S i), inl (nth i vals0 ErrorValue),
     concatn eff1 eff5 (S i) |)
->
Datatypes.length vals < Datatypes.length exps ->
Datatypes.length eff = Datatypes.length vals ->
Datatypes.length exps = Datatypes.length vals0 ->
Datatypes.length exps = Datatypes.length eff5 ->
length exps = length ids0 ->
length ids = length vals
->
concatn eff1 eff5 (Datatypes.length vals) = concatn eff1 eff (Datatypes.length vals).
Proof.
  intros. simpl_concatn. rewrite (firstn_eq_rev eff5 exps vals vals0 eff1 _ _ _ H H0 H1 H2 H3 H4 H5 H6). 
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
  forall (exps : list Expression) (vals vals0 : list Value) eff1 eff6 i i0 ids ids0 id eff3 id' ex,
(forall j : nat,
    j < i ->
    forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
    | env, nth_id ids id j, nth j exps ErrorExp, concatn eff1 eff j | -e> | id'', v2, eff'' | ->
    inl (nth j vals ErrorValue) = v2 /\ concatn eff1 eff (S j) = eff'' /\ nth_id ids id (S j) = id'')
->
(forall j : nat,
     j < i0 ->
     | env, nth_id ids0 id j, nth j exps ErrorExp, concatn eff1 eff6 j | -e> | nth_id ids0 id (S j), inl (nth j vals0 ErrorValue),
     concatn eff1 eff6 (S j) |)
->
(forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, last ids id, nth i exps ErrorExp, concatn eff1 eff i | -e> | id'', v2, eff'' | ->
     inr ex = v2 /\ eff3 = eff'' /\ id' = id'')
->
Datatypes.length eff = i ->
i < Datatypes.length exps ->
Datatypes.length vals = i ->
Datatypes.length vals0 = i0 ->
i0 < Datatypes.length exps ->
Datatypes.length eff6 = i0 ->
length ids = i ->
length ids0 = i0 ->
i < i0
->
False.
Proof.
  induction eff.
  * intros. simpl in H1. subst. simpl in H10. pose (P := H0 0 H10).
    simpl in H8, P. apply length_zero_iff_nil in H8. subst.
    pose (P2 := H1 _ _ _ P). inversion P2. congruence.
  * intros. inversion H2. simpl in H2. rewrite <- H2 in H4.
    pose (EE1 := element_exist Value (length eff) vals (eq_sym H4)). 
    inversion EE1 as [v]. inversion H12 as [vs]. destruct eff6.
    - simpl in H7. subst. rewrite <- H7 in H10. inversion H10.
    - subst. simpl. (* simpl_concatn_H IHeff. rewrite concatn_app, concatn_app. simpl_concatn. *)
      simpl in H7. (* single_unfold_list H6. *) 
      pose (EE2 := element_exist Value (length eff6) vals0 H7). inversion EE2. 
      inversion H2.
      pose (NE := nat_exist H3). inversion NE.
      pose (EE3 := element_exist Expression x1 exps (eq_sym H13)). inversion EE3. inversion H14.
      subst. 
      pose (EE4 := element_exist _ _ _ (eq_sym H8)).
      pose (EE5 := element_exist _ _ _ (eq_sym H9)).
      inversion EE4 as [id0']. inversion EE5 as [id0''].
      inversion H5. inversion H15. subst.
      assert (s = a /\ id0' = id0''). {
        subst.
        assert (0 < Datatypes.length (x :: x0)). {  simpl. omega. }
        pose (P := H0 0 H16).
        assert (0 < S (Datatypes.length eff)). {  simpl. omega. }
        pose (P2 := H 0 H17 (inl (nth 0 (x :: x0) ErrorValue)) (concatn eff1 (s :: eff6) 1) _ P). 
        inversion P2.
        simpl_concatn_H H19. destruct H19. apply app_inv_head in H19. auto.
      }
      destruct H16. subst.
      
      eapply IHeff with (exps := x3) (vals := vs) (vals0 := x0) (eff1 := eff1 ++ a) (i0 := length x0) (ids := x4) (ids0 := x5); auto.
      + intros. assert (S j < S (Datatypes.length eff)). { simpl. omega. } pose (P := H (S j) H18 v2 eff'' id''). 
        rewrite concatn_app, concatn_app in P. pose (P H17). assumption.
      + intros. assert (S j < Datatypes.length (x :: x0)). { simpl. omega. }
        pose (P := H0 (S j) H17). rewrite concatn_app, concatn_app in P. simpl in P. exact P.
      + intros. apply H1. rewrite concatn_app.
        rewrite (last_element_equal _ _ id) in H16.
        exact H16.
      + intuition.
      + intuition.
      + intuition.
      + intuition.
Qed.

(** Value lists are equal until ith value *)
Lemma list_equal_until_i {env : Environment} {eff : list SideEffectList} :
  forall (exps : list Expression) (vals vals0 : list Value) (eff6 : list SideEffectList) (eff1 : SideEffectList) (ids ids0 : list nat) (id : nat),
(forall j : nat,
    j < Datatypes.length vals ->
    forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
    | env, nth_id ids id j, nth j exps ErrorExp, concatn eff1 eff j | -e> | id'', v2, eff'' | ->
    inl (nth j vals ErrorValue) = v2 /\ concatn eff1 eff (S j) = eff'' /\ nth_id ids id (S j) = id'')
->
(forall j : nat,
     j < Datatypes.length vals0 ->
     | env, nth_id ids0 id j, nth j exps ErrorExp, concatn eff1 eff6 j | -e> | nth_id ids0 id (S j), inl (nth j vals0 ErrorValue),
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
length ids = length vals
->
length ids0 = length vals0
->
eff = eff6 /\ vals = vals0 /\ ids = ids0.
Proof.
  induction eff.
  * intros. inversion H2. apply eq_sym, length_zero_iff_nil in H8. subst. simpl in H1. 
    apply eq_sym, length_zero_iff_nil in H1. subst. simpl in H3. apply length_zero_iff_nil in H3. 
    apply length_zero_iff_nil in H5. apply length_zero_iff_nil in H6. subst. auto.
  * intros. simpl in H2. rewrite <- H2 in H1. rewrite <- H1 in H3. pose (NE := nat_exist H4). inversion NE.
    (* single_unfold_list H2. *)
    pose (EE1 := element_exist Value (length eff) vals H2).
    pose (EE2 := element_exist Value (length eff) vals0 H1).
    pose (EE3 := element_exist SideEffectList (length eff) eff6 (eq_sym H3)).
    pose (EE4 := element_exist Expression x exps (eq_sym H7)).
    inversion EE1 as [v]. inversion EE2 as [v']. inversion EE3 as [fe]. inversion EE4 as [e'].
    inversion H8. inversion H9. inversion H10. inversion H11. subst.
    pose (EE5 := element_exist _ _ _ (eq_sym H5)).
    pose (EE6 := element_exist _ _ _ (eq_sym H6)).
    inversion EE5 as [id']. inversion EE6 as [id''].
    inversion H12. inversion H13. subst.
    assert (0 < Datatypes.length (v' :: x1)). { simpl. omega. }
    pose (P := H0 0 H14).
    assert (0 < Datatypes.length (v :: x0)). { simpl. omega. }
    pose (P1 := H 0 H15 (inl (nth 0 (v' :: x1) ErrorValue)) (concatn eff1 (fe :: x2) 1) _ P). inversion P1. destruct H17.
    simpl_concatn_H H17. simpl in H18. apply app_inv_head in H17. inversion H16. subst.
    
    assert (eff = x2 /\ x0 = x1 /\ x4 = x5).
    {
      apply IHeff with (exps := x3) (vals := x0) (vals0 := x1) (eff1 := eff1 ++ fe) (id := id''); auto.
      + intros. assert (S j < S (Datatypes.length x0)). { simpl. omega. } pose (P2 := H (S j) H19 v2 eff''). 
        rewrite concatn_app, concatn_app in P2. simpl in P2. pose (P2 _ H18). assumption.
      + intros. assert (S j < Datatypes.length (v' :: x1)). { simpl. omega. }
        pose (P3 := H0 (S j) H18). rewrite concatn_app, concatn_app in P3. simpl in P3. assumption.
      + inversion H2. inversion H3. inversion H1. auto.
      + inversion H2. inversion H3. inversion H1. auto.
      + intuition.
    }
    inversion H17. inversion H19. subst. auto.
Qed.

(** Slightly different hypotheses for i first element concatn equality *)
Lemma con_n_equality_rev {env : Environment} {eff : list SideEffectList} : 
forall (exps : list Expression) (vals vals0 : list Value) (eff1 : SideEffectList) 
   (eff6 : list SideEffectList) (i i0 : nat) (id : nat) (ids ids0 : list nat) id' ex0 eff4,
(forall j : nat,
    j < i ->
    forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
    | env, nth_id ids id j, nth j exps ErrorExp, concatn eff1 eff j | -e> | id'', v2, eff'' | ->
    inl (nth j vals ErrorValue) = v2 /\ concatn eff1 eff (S j) = eff'' /\ nth_id ids id (S j) = id'')
->
(forall j : nat,
     j < i0 ->
     | env, nth_id ids0 id j, nth j exps ErrorExp, concatn eff1 eff6 j | -e> | nth_id ids0 id (S j), inl (nth j vals0 ErrorValue),
     concatn eff1 eff6 (S j) |)
->
Datatypes.length eff = i ->
i < Datatypes.length exps ->
Datatypes.length vals = i ->
Datatypes.length vals0 = i0 ->
i0 < Datatypes.length exps ->
Datatypes.length eff6 = i0 ->
length ids = i ->
length ids0 = i0 ->
i > i0 ->
(| env, last ids0 id, nth i0 exps ErrorExp, concatn eff1 eff6 i0 | -e> | id', 
     inr ex0, concatn eff1 eff6 i0 ++ eff4 |)
->
False.
Proof.
induction eff.
  * intros. simpl in H1. subst. inversion H9.
  * intros. simpl in H1. rewrite <- H1 in H3.
    pose (EE1 := element_exist Value (length eff) vals (eq_sym H3)).
    inversion EE1 as [v]. inversion H11 as [vs]. destruct eff6.
    - subst. apply eq_sym, length_zero_iff_nil in H6. subst. apply length_zero_iff_nil in H8. subst.
      simpl in H10. pose (P := H 0 (Nat.lt_0_succ _) _ _ _ H10). inversion P. congruence.
    - subst.
      assert (Datatypes.length ids0 = Datatypes.length vals0) as Helper. { auto. }
      pose (EE2 := element_exist Value (length eff6) vals0 H6). inversion EE2. inversion H1.
      pose (NE := nat_exist H2). inversion NE.
      pose (EE3 := element_exist Expression x1 exps (eq_sym H12)). inversion EE3. inversion H13. subst.
      pose (EE4 := element_exist _ _ _ (eq_sym H7)).
      pose (EE5 := element_exist _ _ _ (eq_sym H8)).
      inversion EE4 as [id0']. inversion EE5 as [id0'']. inversion H4. inversion H14. subst.
      assert (s = a /\ id0' = id0''). {
        subst.
        assert (0 < Datatypes.length (x :: x0)). {  simpl. omega. }
        pose (P := H0 0 H15).
        assert (0 < S (Datatypes.length eff)). {  simpl. omega. }
        pose (P1 := H 0 H16 (inl (nth 0 (x :: x0) ErrorValue)) (concatn eff1 (s :: eff6) 1) _ P). destruct P1. destruct H18.
        simpl_concatn_H H18. apply app_inv_head in H18. simpl in H19. auto.
      }
      destruct H15. subst.
      eapply IHeff with (exps := x3) (vals := vs) (vals0 := x0) (eff1 := eff1 ++ a) 
                       (i0 := length eff6) (i := length eff) (ids := x4) (ids0 := x5); auto.
      + intros. assert (S j < S (Datatypes.length eff)). { simpl. omega. }
        pose (P := H (S j) H17 v2 eff''). rewrite concatn_app, concatn_app in P. simpl in P.
        pose (P1 := P _ H16). assumption.
      + intros. inversion H6. assert (S j < Datatypes.length (x :: x0)). { simpl. omega. }
        pose (P := H0 (S j) H16). rewrite concatn_app, concatn_app in P. simpl in P. assumption.
      + intuition.
      + inversion H6. auto.
      + rewrite <- H6 in H5. simpl in H5. omega.
      + rewrite <- H6 in Helper. auto.
      + simpl in *. rewrite <- H6 in H9. omega.
      + rewrite <- last_element_equal in H10. simpl in H10. rewrite concatn_app in H10. 
        inversion H6. rewrite H16. exact H10.
Qed.

(** Based on determinsim, using lists with exceptions, these are equal *)
Lemma exception_equality {env : Environment} {exps : list Expression} (vals vals0 : list Value) 
   (ex : Exception) (eff1 : SideEffectList) (eff eff6 : list SideEffectList) (i i0 : nat) 
   (eff3 : SideEffectList) (ex0 : Exception) (eff4 : SideEffectList) (ids ids0 : list nat) (id id' : nat) :
(forall j : nat,
     j < i ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, nth_id ids id j, nth j exps ErrorExp, concatn eff1 eff j | -e> | id'', v2, eff'' | ->
     inl (nth j vals ErrorValue) = v2 /\ concatn eff1 eff (S j) = eff'' /\ nth_id ids id (S j) = id'')
->
| env, last ids0 id, nth i0 exps ErrorExp, concatn eff1 eff6 i0 | -e> | id', inr ex0, concatn eff1 eff6 i0 ++ eff4 |
->
(forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
        | env, last ids id, nth i exps ErrorExp, concatn eff1 eff i | -e> | id'', v2, eff'' | -> inr ex = v2 /\ eff3 = eff'' /\ id' = id'')
->
(forall j : nat,
      j < i0 ->
      | env, nth_id ids0 id j, nth j exps ErrorExp, concatn eff1 eff6 j | -e> | nth_id ids0 id (S j), inl (nth j vals0 ErrorValue),
      concatn eff1 eff6 (S j) |)
->
Datatypes.length vals = i ->
 i < Datatypes.length exps ->
 Datatypes.length eff = i ->
 Datatypes.length vals0 = i0 ->
 i0 < Datatypes.length exps ->
 Datatypes.length eff6 = i0 ->
 length ids = i ->
 length ids0 = i0
->
i = i0 /\ eff = eff6 /\ vals = vals0 /\ ids = ids0.
Proof.
  intros. destruct (le_gt_dec i i0).
  * case_eq (le_lt_or_eq i i0 l).
    - intros.
      pose (P1 := con_n_equality exps vals vals0 eff1 eff6 i i0 ids ids0 id _ _ _ H H2 H1 H5 H4 H3 H6 H7 H8 H9 H10 l0). inversion P1.
    - intros. subst. pose (list_equal_until_i exps vals vals0 eff6 eff1 _ _ _ H H2 e H5 H8 H7 H9 H10). auto.
  * pose (P := con_n_equality_rev exps vals vals0 eff1 eff6 i i0 id ids ids0 _ _ _ H H2 H5 H4 H3 H6 H7 H8 H9 H10 g H0). inversion P.
Qed.

(** Map lists are equal *)
Lemma map_lists_equality {env : Environment} {kl : list Expression} : 
forall {vl : list Expression} (kvals vvals kvals0 vvals0 : list Value) (eff1 : SideEffectList) 
     (eff eff7 : list SideEffectList) (ids ids0 : list nat) (id : nat),
(forall j : nat,
     j < length vl ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, nth_id ids id (2*j), nth j kl ErrorExp, concatn eff1 eff (2 * j) | -e> | id'', v2, eff'' | ->
     inl (nth j kvals ErrorValue) = v2 /\ concatn eff1 eff (S (2 * j)) = eff'' /\ nth_id ids id (S (2*j)) = id'')
->
(forall j : nat,
     j < length vl ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, nth_id ids id (S (2*j)), nth j vl ErrorExp, concatn eff1 eff (S (2 * j)) | -e> | id'', v2, eff'' | ->
     inl (nth j vvals ErrorValue) = v2 /\ concatn eff1 eff (S (S (2 * j))) = eff'' /\ nth_id ids id (S (S (2*j))) = id'')
->
Datatypes.length kl = Datatypes.length vl ->
length kl = Datatypes.length vvals ->
length kl = Datatypes.length kvals ->
((length kl) * 2)%nat = Datatypes.length eff ->
((length kl) * 2)%nat = length ids ->
(forall j : nat,
      j < length vl ->
      | env, nth_id ids0 id (2*j), nth j kl ErrorExp, concatn eff1 eff7 (2 * j) | -e> | nth_id ids0 id (S (2*j)), inl (nth j kvals0 ErrorValue),
      concatn eff1 eff7 (S (2 * j)) |)
->
(forall j : nat,
      j < length vl ->
      | env, nth_id ids0 id (S (2*j)), nth j vl ErrorExp, concatn eff1 eff7 (S (2 * j)) | -e>
      | nth_id ids0 id (S(S(2*j))), inl (nth j vvals0 ErrorValue), concatn eff1 eff7 (S (S (2 * j))) |)
->
length kl = Datatypes.length vvals0 ->
length kl = Datatypes.length kvals0 ->
((length kl) * 2)%nat = Datatypes.length eff7 ->
((length kl) * 2)%nat = length ids0
->
kvals = kvals0 /\ vvals = vvals0 /\ eff = eff7 /\ ids = ids0.
Proof.
  induction kl.
  * intros. inversion H1. inversion H2. inversion H3. inversion H4.
    repeat unfold_list.
    inversion H10. inversion H8. inversion H9. inversion H11. inversion H5.
    repeat unfold_list.
    auto.
  * intros. inversion H1. inversion H2. inversion H3. inversion H4. simpl in H9, H14, H7, H8, H10, H5, H11.
    single_unfold_list. single_unfold_list. single_unfold_list. 
    single_unfold_list. single_unfold_list. single_unfold_list.
    single_unfold_list. single_unfold_list. single_unfold_list.
    single_unfold_list. single_unfold_list. single_unfold_list. single_unfold_list.
    (** FIRST ELEMENTS ARE EQUAL *)
    pose (F1 := H6 0 (Nat.lt_0_succ (length x7))). simpl in F1.
    pose (F2 := H 0 (Nat.lt_0_succ _) _ _ _ F1). inversion F2. inversion H41.
    rewrite concatn_app, concatn_app in H43. simpl_concatn_H H43. destruct H43. apply app_inv_head in H43. subst.
    pose (F3 := H7 0 (Nat.lt_0_succ (length x7))).
    pose (F4 := H0 0 (Nat.lt_0_succ _) _ _ _ F3). inversion F4. inversion H43.
    rewrite concatn_app, concatn_app in H44. simpl_concatn_H H44. destruct H44. apply app_inv_head in H44. subst. simpl.
    (** OTHER ELEMETS *)
    assert (x3 = x15 /\ x5 = x17 /\ x2 = x14 /\ x21 = x11).
    {
      eapply IHkl with (vl := x7); auto.
      * intros. assert (S j < length (x6 :: x7)). { simpl. omega. }
        pose (P3 := H (S j) H46 v2 eff''). simpl in P3.
        rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r, <- plus_n_Sm, concatn_app,
               <- app_assoc in P3. simpl in H45. rewrite Nat.add_0_r in H45.
        pose (P4 := P3 _ H45). simpl. rewrite Nat.add_0_r. assumption.
      * intros. assert (S j < length (x6 :: x7)). { simpl. omega. }
        pose (P3 := H0 (S j) H46 v2 eff''). simpl in P3.
        rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r, <- plus_n_Sm, concatn_app,
               <- app_assoc in P3. simpl in H45. rewrite Nat.add_0_r in H45.
        pose (P4 := P3 _ H45). simpl. rewrite Nat.add_0_r. assumption.
      * intros. assert (S j < length (x6 :: x7)). { simpl. omega. }
        pose (P3 := H6 (S j) H45). simpl in P3. 
        rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r, <- plus_n_Sm, concatn_app,
               <- app_assoc in P3. simpl. rewrite Nat.add_0_r. assumption.
      * intros. assert (S j < length (x6 :: x7)). { simpl. omega. }
        pose (P3 := H7 (S j) H45). simpl in P3.
        rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r, <- plus_n_Sm, concatn_app,
               <- app_assoc in P3. simpl. rewrite Nat.add_0_r. assumption.
    }
    destruct H44. destruct H45. destruct H46. subst. auto.
Qed.

(** Map lists are equal until ith element *)
Lemma map_lists_equal_until_i {env : Environment} {kl : list Expression} : forall {vl : list Expression}
   (kvals vvals kvals0 vvals0 : list Value) (i0 : nat) (eff1 : SideEffectList)
   (eff eff7 : list SideEffectList) (ex0 : Exception) (eff5 eff6 : SideEffectList) (val0 : Value)
   (ids ids0 : list nat) (id id' id'' : nat),
(forall j : nat,
     j < length vl ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, nth_id ids id (2*j), nth j kl ErrorExp, concatn eff1 eff (2 * j) | -e> | id'', v2, eff'' | ->
     inl (nth j kvals ErrorValue) = v2 /\ concatn eff1 eff (S (2 * j)) = eff'' /\ nth_id ids id (S (2*j)) = id'')
->
(forall j : nat,
     j < length vl ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, nth_id ids id (S (2*j)), nth j vl ErrorExp, concatn eff1 eff (S (2 * j)) | -e> | id'', v2, eff'' | ->
     inl (nth j vvals ErrorValue) = v2 /\ concatn eff1 eff (S (S (2 * j))) = eff'' /\ nth_id ids id (S (S (2*j))) = id'')
->
Datatypes.length kl = Datatypes.length vl ->
length kl = Datatypes.length vvals ->
length kl = Datatypes.length kvals ->
((length kl) * 2)%nat = Datatypes.length eff ->
((length kl) * 2)%nat = Datatypes.length ids ->
(forall j : nat,
      j < i0 ->
      | env, nth_id ids0 id (2*j), nth j kl ErrorExp, concatn eff1 eff7 (2 * j) | -e> | nth_id ids0 id (S (2*j)), inl (nth j kvals0 ErrorValue),
      concatn eff1 eff7 (S (2 * j)) |)
->
(forall j : nat,
      j < i0 ->
      | env, nth_id ids0 id (S (2*j)), nth j vl ErrorExp, concatn eff1 eff7 (S (2 * j)) | -e>
      | nth_id ids0 id (S (S (2*j))), inl (nth j vvals0 ErrorValue), concatn eff1 eff7 (S (S (2 * j))) |)
->
Datatypes.length vvals0 = i0 ->
Datatypes.length kvals0 = i0 ->
i0 <= Datatypes.length kl ->
Datatypes.length eff7 = (i0 * 2)%nat ->
length ids0 = (i0 * 2)%nat ->
(| env, last ids0 id, nth i0 kl ErrorExp, concatn eff1 eff7 (2 * i0) | -e> | id', inr ex0, concatn eff1 eff7 (2 * i0) ++ eff5 |
\/
(| env, last ids0 id, nth i0 kl ErrorExp, concatn eff1 eff7 (2 * i0) | -e> | id', inl val0,
      concatn eff1 eff7 (2 * i0) ++ eff5 | /\
| env, id', nth i0 vl ErrorExp, concatn eff1 eff7 (2 * i0) ++ eff5 | -e> | 
      id'', inr ex0, concatn eff1 eff7 (2 * i0) ++ eff5 ++ eff6 |)
)
->
length vl = i0 /\ kvals = kvals0 /\ vvals = vvals0 /\ eff = eff7 /\ ids = ids0.
Proof.
  induction kl.
  * intros. inversion H2. apply eq_sym, length_zero_iff_nil in H15. subst. inversion H1.
    apply eq_sym, length_zero_iff_nil in H14. subst. inversion H10. apply length_zero_iff_nil in H14.
    subst. inversion H3. apply eq_sym,  length_zero_iff_nil in H14. subst. inversion H11.
    apply length_zero_iff_nil in H14. subst. inversion H12. apply length_zero_iff_nil in H14. subst.
    inversion H4. apply eq_sym, length_zero_iff_nil in H14. subst. apply length_zero_iff_nil in H9.
    subst. apply eq_sym, length_zero_iff_nil in H5. auto.
  * intros. inversion H1.
    pose (EE1 := element_exist Expression (length kl) vl H15). 
    inversion EE1 as [ve]. inversion H14 as [ves].
    subst.
    case_eq (length vvals0).
    - intros. apply length_zero_iff_nil in H8. subst.
      apply length_zero_iff_nil in H9. apply length_zero_iff_nil in H12. apply length_zero_iff_nil in H11. subst.
      rewrite <- H1 in H, H0.
      simpl_concatn_H H13.
      inversion H13.
      + pose (P1 := H 0 (Nat.lt_0_succ _) (inr ex0) (eff1 ++ eff5) id').
        simpl_concatn_H P1. pose (P2 := P1 H8). inversion P2. inversion H9.
      + destruct H8. pose (P1 := H 0 (Nat.lt_0_succ _) (inl val0) (eff1 ++ eff5) id').
        simpl_concatn_H P1. pose (P2 := P1 H8). destruct P2. inversion H11. subst.
        pose (P3 := H0 0 (Nat.lt_0_succ _) (inr ex0) (eff1 ++ eff5 ++ eff6) id'').
        simpl_concatn_H P3.
        destruct H12.
        rewrite <- H12 in H9 at 1. rewrite H16 in P3.
        pose (P4 := P3 H9). inversion P4. inversion H17.

    - intros. rewrite H8 in *. simpl in H2, H3. simpl in H4, H10.
      pose (EE2 := element_exist Value _ kvals0 (eq_sym H9)).
      pose (EE3 := element_exist Value _ vvals0 (eq_sym H8)).
      pose (EE4 := element_exist Value _ kvals H3).
      pose (EE5 := element_exist Value _ vvals H2).
      pose (EE6 := element_exist SideEffectList _ eff H4).
      pose (EE7 := element_exist SideEffectList _ eff7 (eq_sym H11)).
      pose (EE8 := element_exist _ _ _ H5).
      pose (EE9 := element_exist _ _ _ (eq_sym H12)).
      inversion EE2 as [kv']. inversion EE3 as [vv']. inversion EE4 as [kv]. inversion EE5 as [vv].
      inversion EE6 as [e1]. inversion EE7 as [e1']. inversion EE8 as [id1]. inversion EE9 as [id1'].
      inversion H16. inversion H17. inversion H18. inversion H19.
      inversion H20. inversion H21. inversion H22. inversion H23. subst.
      
      inversion H4. inversion H11. inversion H5. inversion H12.
      pose (EE10 := element_exist SideEffectList _ x3 (H25)).
      pose (EE11 := element_exist SideEffectList _ x4 (eq_sym H26)).
      pose (EE12 := element_exist _ _ x5 (H27)).
      pose (EE13 := element_exist _ _ x6 (eq_sym H28)).
      inversion EE10 as [e2]. inversion EE11 as [e2']. inversion EE12 as [id2]. inversion EE13 as [id2']. 
      inversion H24. inversion H29. inversion H30. inversion H31. subst.
      (** FIRST ELEMENTS ARE EQUAL *)
      pose (F1 := H6 0 (Nat.lt_0_succ n)).
      pose (F2 := H 0 (Nat.lt_0_succ _) _ _ _ F1). inversion F2. inversion H32. destruct H33.
      rewrite concatn_app, concatn_app in H33. simpl_concatn_H H33. apply app_inv_head in H33. 
      simpl in H34. subst.
      pose (F3 := H7 0 (Nat.lt_0_succ n)).
      pose (F4 := H0 0 (Nat.lt_0_succ _) _ _ _ F3). inversion F4. inversion H33. destruct H34.
      rewrite concatn_app, concatn_app in H34. simpl_concatn_H H34. apply app_inv_head in H34. 
      simpl in H35. subst. simpl.
      (** OTHER ELEMETS *)
      assert (length ves = n /\ x1 = x /\ x2 = x0 /\ x7 = x8 /\ x9 = x10).
      {
        eapply IHkl with (eff1 := eff1 ++ e1' ++ e2') (ex0 := ex0) (eff5 := eff5) (vl := ves) (eff6 := eff6) (val0 := val0); auto.
        * intros. assert (S j < length (ve :: ves)). { simpl. omega. }
          pose (P3 := H (S j) H36 v2 eff''). simpl in P3.
          rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r,
                <- plus_n_Sm, concatn_app, <- app_assoc in P3. simpl in H35. rewrite Nat.add_0_r in H35.
          pose (P4 := P3 _ H35). simpl. rewrite Nat.add_0_r. assumption.
        * intros. assert (S j < length (ve :: ves)). { simpl. omega. }
          pose (P3 := H0 (S j) H36 v2 eff''). simpl in P3.
          rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r,
                <- plus_n_Sm, concatn_app, <- app_assoc in P3. simpl in H35. rewrite Nat.add_0_r in H35.
          pose (P4 := P3 _ H35). simpl. rewrite Nat.add_0_r. assumption.
        * intros. assert (S j < S n). { omega. }
          pose (P3 := H6 (S j) H35). simpl in P3.
          rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r,
                <- plus_n_Sm, concatn_app, <- app_assoc in P3. simpl. rewrite Nat.add_0_r. assumption.
        * intros. assert (S j < S n). { omega. }
          pose (P3 := H7 (S j) H35). simpl in P3.
          rewrite concatn_app, concatn_app, concatn_app, Nat.add_0_r,
               <- plus_n_Sm, concatn_app, <- app_assoc in P3. simpl. rewrite Nat.add_0_r. assumption.
        * simpl in H9. omega.
        * rewrite <- last_element_equal, <- last_element_equal in H13. simpl in H13.
          rewrite concatn_app, Nat.add_0_r, <- plus_n_Sm, concatn_app,
              <- app_assoc in H13. simpl. rewrite Nat.add_0_r. exact H13.
      }
      destruct H34. destruct H35. destruct H36. destruct H37. subst. auto.
Qed.
(*
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
*)
End Core_Erlang_Determinism_Helpers.