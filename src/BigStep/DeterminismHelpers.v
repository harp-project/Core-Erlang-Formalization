From CoreErlang Require Import Tactics.
From CoreErlang Require Export BigStep.

From Coq Require Arith.PeanoNat.

(** Helper lemmas for determinism *)


Import ListNotations.

Ltac empty_list_in_hypo :=
match goal with
| [H : 0 = length _ |- _ ] => apply eq_sym, length_zero_iff_nil in H
| [H : length _ = 0 |- _ ] => apply length_zero_iff_nil in H
| _ => idtac
end.

Ltac single_unfold_list :=
match goal with
| [ Hyp : Datatypes.length ?l = 0 |- _] => apply length_zero_iff_nil in Hyp; subst
| [ Hyp : 0 = Datatypes.length ?l |- _] => apply eq_sym, length_zero_iff_nil in Hyp; subst
| [ Hyp : Datatypes.length ?l = S ?n |- _] => symmetry in Hyp; single_unfold_list
| [ Hyp : S ?n = Datatypes.length ?l |- _] => 
   pose (element_exist _ _ Hyp);
   match goal with
   | [H' : exists x l', _ = x::l' |- _] => 
     inversion H';
     match goal with
     | [H'' : exists l', _ = ?x::l' |- _] => inversion H''; subst; simpl in Hyp; inversion Hyp
     end
   end
end
.

(** Value lists are equal ased on the determinism hypotheses *)
Lemma explist_equality {env : Environment} {modules : list ErlModule} {own_module : string} {exps : list Expression} {eff1 : SideEffectList} : 
forall vals vals0 : list Value, forall eff eff4 : list SideEffectList,
forall id ids ids0,
(forall i : nat,
     i < Datatypes.length exps ->
     forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, modules, own_module, nth_def ids id 0 i, nth i exps ErrorExp, nth_def eff eff1 [] i |
     -e>
     | id'', v2, eff'' | ->
     inl [nth i vals ErrorValue] = v2 /\ nth_def eff eff1 [] (S i) = eff'' /\ nth_def ids id 0 (S i) = id'')
->
(forall i : nat,
     i < Datatypes.length exps ->
     | env, modules, own_module, nth_def ids0 id 0 i, nth i exps ErrorExp, nth_def eff4 eff1 [] i |
     -e> 
     | nth_def ids0 id 0 (S i), inl [nth i vals0 ErrorValue], nth_def eff4 eff1 [] (S i) |)
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
  * intros. simpl in H3, H2, H4, H5, H6, H1.
    repeat empty_list_in_hypo.
    subst. auto.
  * intros. inversion H3. inversion H2. inversion H4. inversion H5. inversion H6. inversion H1.
  
  (* first elements are the same *)
    single_unfold_list. single_unfold_list.
    single_unfold_list. single_unfold_list.
    single_unfold_list. single_unfold_list.
    pose (P1 := H0 0 list_length).
    pose (P2 := H 0 list_length _ _ _ P1).
    inversion P2. inversion H24. destruct H26.
    simpl in H26, H27.
    subst.
  (* remaining lists are the same *)
    assert (
      (forall i : nat,
      i < Datatypes.length exps ->
      forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
      | env, modules, own_module, nth_def x4 x1 0 i, nth i exps ErrorExp, nth_def x6 x7 [] i | -e> | id'', v2, eff'' | ->
      inl [nth i x10 ErrorValue] = v2 /\ nth_def x6 x7 [] (S i) = eff'' /\ nth_def x4 x1 0 (S i) = id'')
    ).
    {
      intros. assert (S i < Datatypes.length (a::exps)). { simpl. lia. } 
      pose (P4 := H (S i) H28 v2 eff'' id''). simpl nth in P4. exact (P4 H27).
    }
    assert (
     (forall i : nat,
    i < Datatypes.length exps ->
    | env, modules, own_module, nth_def x2 x1 0 i, nth i exps ErrorExp, nth_def x8 x7 [] i | -e>
    | nth_def x2 x1 0 (S i), inl [nth i x0 ErrorValue],
    nth_def x8 x7 [] (S i) |)
    ).
    {
      intros. assert (S i < Datatypes.length (a :: exps)). { simpl. lia. } 
      pose (P4 := H0 (S i) H28). simpl nth in P4. assumption.
    }
    (* simpl list lengths *)
    inversion H10. inversion H11. inversion H12. inversion H13. inversion H9.
    inversion H8.
    pose (IH := IHexps _ _ _ _ _ _ _ _ H26 H27 H32 H33 H34 H29 H30 H31). 
    destruct IH. destruct H35. subst. auto.
Qed.
(* 
Lemma singleexplist_equality {env : Environment} {exps : list SingleExpression} {eff1 : SideEffectList} : 
forall vals vals0 : list Value, forall eff eff4 : list SideEffectList,
forall id ids ids0,
(forall i : nat,
     i < Datatypes.length exps ->
     forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, nth_def ids id 0 i, nth i exps ErrorExp, nth_def eff eff1 [] i |
     -s>
     | id'', v2, eff'' | ->
     inl [nth i vals ErrorValue] = v2 /\ nth_def eff eff1 [] (S i) = eff'' /\ nth_def ids id 0 (S i) = id'')
->
(forall i : nat,
     i < Datatypes.length exps ->
     | env, nth_def ids0 id 0 i, nth i exps ErrorExp, nth_def eff4 eff1 [] i |
     -s> 
     | nth_def ids0 id 0 (S i), inl [nth i vals0 ErrorValue], nth_def eff4 eff1 [] (S i) |)
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
  * intros. simpl in H3, H2, H4, H5, H6, H1.
    repeat empty_list_in_hypo.
    subst. auto.
  * intros. inversion H3. inversion H2. inversion H4. inversion H5. inversion H6. inversion H1.
  
  (* first elements are the same *)
    single_unfold_list. single_unfold_list.
    single_unfold_list. single_unfold_list.
    single_unfold_list. single_unfold_list.
    pose (P1 := H0 0 list_length).
    pose (P2 := H 0 list_length _ _ _ P1).
    inversion P2. inversion H24. destruct H26.
    simpl in H26, H27.
    subst.
  (* remaining lists are the same *)
    assert (
      (forall i : nat,
      i < Datatypes.length exps ->
      forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
      | env, nth_def x4 x1 0 i, nth i exps ErrorExp, nth_def x6 x7 [] i | -s> | id'', v2, eff'' | ->
      inl [nth i x10 ErrorValue] = v2 /\ nth_def x6 x7 [] (S i) = eff'' /\ nth_def x4 x1 0 (S i) = id'')
    ).
    {
      intros. assert (S i < Datatypes.length (a::exps)). { simpl. lia. } 
      pose (P4 := H (S i) H28 v2 eff'' id''). simpl nth in P4. exact (P4 H27).
    }
    assert (
     (forall i : nat,
    i < Datatypes.length exps ->
    | env, nth_def x2 x1 0 i, nth i exps ErrorExp, nth_def x8 x7 [] i | -s>
    | nth_def x2 x1 0 (S i), inl [nth i x0 ErrorValue],
    nth_def x8 x7 [] (S i) |)
    ).
    {
      intros. assert (S i < Datatypes.length (a :: exps)). { simpl. lia. } 
      pose (P4 := H0 (S i) H28). simpl nth in P4. assumption.
    }
    (* simpl list lengths *)
    inversion H10. inversion H11. inversion H12. inversion H13. inversion H9.
    inversion H8.
    pose (IH := IHexps _ _ _ _ _ _ _ _ H26 H27 H32 H33 H34 H29 H30 H31). 
    destruct IH. destruct H35. subst. auto.
Qed. *)


(** Based on determinism hypotheses, the same clause was chosen in case evaluation *)
Lemma index_case_equality {env : Environment} {modules : list ErlModule} {own_module : string} {clauses : list (list Pattern * Expression * Expression)} {vals : list Value} (i i0 : nat) 
    (guard guard0 exp exp0 : Expression) (bindings bindings0 : list (Var * Value)) 
    (eff1 : SideEffectList) (id' : nat) : 
  (forall j : nat,
     j < i ->
     forall (gg ee : Expression) (bb : list (Var * Value)),
     match_clause vals clauses j = Some (gg, ee, bb) ->
     forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
     | add_bindings bb env, modules, own_module, id', gg, eff1 | -e> | id'', v2, eff'' | ->
     inl [ffalse] = v2 /\ eff1 = eff'' /\ id' = id'')
  ->
  (forall j : nat,
      j < i0 ->
      forall (gg ee : Expression) (bb : list (Var * Value)),
      match_clause vals clauses j = Some (gg, ee, bb) ->
      | add_bindings bb env, modules, own_module, id', gg, eff1 | -e> | id', inl [ffalse], eff1 |)
  ->
  match_clause vals clauses i = Some (guard, exp, bindings)
  ->
  match_clause vals clauses i0 = Some (guard0, exp0, bindings0)
  ->
  | add_bindings bindings0 env, modules, own_module, id', guard0, eff1 | -e> | id', inl [ttrue], eff1 |
  ->
  | add_bindings bindings env, modules, own_module, id', guard, eff1 | -e> | id', inl [ttrue], eff1 |
  ->
  (forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
         | add_bindings bindings env, modules, own_module, id', guard, eff1 | -e> | id'', v2, eff'' | ->
         inl [ttrue] = v2 /\ eff1 = eff'' /\ id' = id'')
->
  i = i0.
Proof.
  intros. pose (D := Nat.lt_decidable i i0). destruct D.
  * pose (P1 := H0 i H6 guard exp bindings H1). pose (P2 := H5 (inl [ffalse]) _ _ P1). 
    inversion P2. inversion H7.
  * apply Compare_dec.not_lt in H6. apply (nat_ge_or) in H6. inversion H6.
    - assumption.
    - pose (P3 := H i0 H7 guard0 exp0 bindings0 H2 (inl [ttrue]) _ _ H3). inversion P3. inversion H8.
Qed.

(** Based on determinism, until the i-th element, the side effects are equal *)
Lemma explist_prefix_eq {env : Environment} {modules : list ErlModule} {own_module : string} {eff : list SideEffectList} : 
forall (eff' : list SideEffectList) (exps : list Expression) (vals vals' : list Value) 
   (eff1 : SideEffectList) (ids ids' : list nat) (id id'' : nat) ex eff3,
length exps = length vals ->
Datatypes.length exps = Datatypes.length eff
->
Datatypes.length eff' = Datatypes.length vals'
->
Datatypes.length vals' < Datatypes.length exps 
->
length exps = length ids
->
length ids' = length vals'
->
(forall i : nat,
     i < Datatypes.length exps ->
     forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, modules, own_module, nth_def ids id 0 i, nth i exps ErrorExp, nth_def eff eff1 [] i | -e> | id'', v2, eff'' | ->
     inl [nth i vals ErrorValue] = v2 /\ nth_def eff eff1 [] (S i) = eff'' /\ nth_def ids id 0 (S i) = id'')
->
(forall j : nat,
     j < Datatypes.length vals' ->
     | env, modules, own_module, nth_def ids' id 0 j, nth j exps ErrorExp, nth_def eff' eff1 [] j | -e>
     | nth_def ids' id 0 (S j), inl [nth j vals' ErrorValue],
     nth_def eff' eff1 [] (S j) |)
->
| env, modules, own_module, last ids' id, nth (Datatypes.length vals') exps ErrorExp,
      last eff' eff1 | -e> | id'', inr ex,
      eff3 |
->
False.
Proof.
  induction eff.
  * intros. inversion H0. rewrite H9 in H2. inversion H2.
  * intros. destruct eff'.
    - inversion H1. simpl in H1. apply eq_sym, length_zero_iff_nil in H1. subst.
      simpl in H4.
      apply length_zero_iff_nil in H4. subst. simpl in H0. rewrite H0 in H5.
      pose (P := H5 0 (Nat.lt_0_succ _) _ _ _ H7). destruct P. inversion H1.
    - inversion H1. simpl.
    (* first elements *)
      inversion H0.
      assert (0 < length exps). { lia. }
      assert (0 < length vals'). { lia. }
      assert (0 < length ids'). { lia. }
      simpl in H0, H1.
      (* single_unfold_list H1. *)
      assert (Datatypes.length exps = S (Datatypes.length eff)) as Helper. { auto. }
      assert (Datatypes.length ids' = Datatypes.length vals') as Helper2. { auto. }
      assert (Datatypes.length exps = Datatypes.length ids) as Helper3. { auto. }
      pose (EE1 := element_exist _ _ (eq_sym H10)).
      pose (EE2 := element_exist _ _ H1).
      rewrite H in H0.
      pose (EE3 := element_exist _ _ (eq_sym H0)).
      rewrite <- H1 in H4. rewrite H10 in H3.
      pose (EE4 := element_exist _ _ H3).
      pose (EE5 := element_exist _ _ (eq_sym H4)).
      inversion EE1 as [e]. inversion EE2 as [v]. inversion EE3 as [v'].
      inversion EE4 as [id0']. inversion EE5 as [id0'']. 
      inversion H13. inversion H14. inversion H15. inversion H16. inversion H17. subst.
      pose (P0 := H6 0 H11).
      pose (P1 := H5 0 H8 (inl [v]) (s)).
      pose (P2 := P1 _ P0). destruct P2. destruct H18, H19. simpl in H18, H19. subst.
    (* other elements *)
      inversion H1.
      eapply IHeff with (exps := x) (vals := x1) (vals' := x0) (eff1 := s)
                      (ids := x2) (ids' := x3) (id := id0'') (eff' := eff'); auto.
        + intuition.
        + intros. assert (S i < Datatypes.length (e :: x)). { simpl. lia. }
          pose (A := H5 (S i) H21 v2 eff''). simpl in A, H20.
          pose (B := A _ H20). assumption.
        + intros. assert (S j < Datatypes.length (v :: x0)). { lia. } 
          pose (A := H6 (S j) H20). exact A.
        + rewrite <- last_element_equal, <- last_element_equal in H7. exact H7.
Qed.

(* 
Lemma singleexplist_prefix_eq {env : Environment} {eff : list SideEffectList} : 
forall (eff' : list SideEffectList) (exps : list SingleExpression) (vals vals' : list Value) 
   (eff1 : SideEffectList) (ids ids' : list nat) (id id'' : nat) ex eff3,
length exps = length vals ->
Datatypes.length exps = Datatypes.length eff
->
Datatypes.length eff' = Datatypes.length vals'
->
Datatypes.length vals' < Datatypes.length exps 
->
length exps = length ids
->
length ids' = length vals'
->
(forall i : nat,
     i < Datatypes.length exps ->
     forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, nth_def ids id 0 i, nth i exps ErrorExp, nth_def eff eff1 [] i | -s> | id'', v2, eff'' | ->
     inl [nth i vals ErrorValue] = v2 /\ nth_def eff eff1 [] (S i) = eff'' /\ nth_def ids id 0 (S i) = id'')
->
(forall j : nat,
     j < Datatypes.length vals' ->
     | env, nth_def ids' id 0 j, nth j exps ErrorExp, nth_def eff' eff1 [] j | -s>
     | nth_def ids' id 0 (S j), inl [nth j vals' ErrorValue],
     nth_def eff' eff1 [] (S j) |)
->
| env, last ids' id, nth (Datatypes.length vals') exps ErrorExp,
      last eff' eff1 | -s> | id'', inr ex,
      eff3 |
->
False.
Proof.
  induction eff.
  * intros. inversion H0. rewrite H9 in H2. inversion H2.
  * intros. destruct eff'.
    - inversion H1. simpl in H1. apply eq_sym, length_zero_iff_nil in H1. subst.
      simpl in H4.
      apply length_zero_iff_nil in H4. subst. simpl in H0. rewrite H0 in H5.
      pose (P := H5 0 (Nat.lt_0_succ _) _ _ _ H7). destruct P. inversion H1.
    - inversion H1. simpl.
    (* first elements *)
      inversion H0.
      assert (0 < length exps). { lia. }
      assert (0 < length vals'). { lia. }
      assert (0 < length ids'). { lia. }
      simpl in H0, H1.
      (* single_unfold_list H1. *)
      assert (Datatypes.length exps = S (Datatypes.length eff)) as Helper. { auto. }
      assert (Datatypes.length ids' = Datatypes.length vals') as Helper2. { auto. }
      assert (Datatypes.length exps = Datatypes.length ids) as Helper3. { auto. }
      pose (EE1 := element_exist _ _ (eq_sym H10)).
      pose (EE2 := element_exist _ _ H1).
      rewrite H in H0.
      pose (EE3 := element_exist _ _ (eq_sym H0)).
      rewrite <- H1 in H4. rewrite H10 in H3.
      pose (EE4 := element_exist _ _ H3).
      pose (EE5 := element_exist _ _ (eq_sym H4)).
      inversion EE1 as [e]. inversion EE2 as [v]. inversion EE3 as [v'].
      inversion EE4 as [id0']. inversion EE5 as [id0'']. 
      inversion H13. inversion H14. inversion H15. inversion H16. inversion H17. subst.
      pose (P0 := H6 0 H11).
      pose (P1 := H5 0 H8 (inl [v]) (s)).
      pose (P2 := P1 _ P0). destruct P2. destruct H18, H19. simpl in H18, H19. subst.
    (* other elements *)
      inversion H1.
      eapply IHeff with (exps := x) (vals := x1) (vals' := x0) (eff1 := s)
                      (ids := x2) (ids' := x3) (id := id0'') (eff' := eff'); auto.
        + intuition.
        + intros. assert (S i < Datatypes.length (e :: x)). { simpl. lia. }
          pose (A := H5 (S i) H21 v2 eff''). simpl in A, H20.
          pose (B := A _ H20). assumption.
        + intros. assert (S j < Datatypes.length (v :: x0)). { lia. } 
          pose (A := H6 (S j) H20). exact A.
        + rewrite <- last_element_equal, <- last_element_equal in H7. exact H7.
Qed.
 *)
(** First i elements are equal, but with changed hypotheses *)
Lemma explist_prefix_eq_rev {env : Environment} {modules : list ErlModule} {own_module : string} {eff : list SideEffectList} : 
   forall (eff' : list SideEffectList) (exps : list Expression) (vals vals' : list Value) 
          (eff1 : SideEffectList) (ids ids' : list nat) (id : nat) (eff2 : SideEffectList) 
          (id' : nat) (ex : Exception),
(forall j : nat,
     j < Datatypes.length vals ->
     forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, modules, own_module, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j | -e> | id'', v2, eff'' | ->
     inl [nth j vals ErrorValue] = v2 /\ nth_def eff eff1 [] (S j) = eff'' /\ nth_def ids id 0 (S j) = id'')
->
(forall i : nat,
     i < Datatypes.length exps ->
     | env, modules, own_module, nth_def ids' id 0 i, nth i exps ErrorExp, nth_def eff' eff1 [] i | -e>
     | nth_def ids' id 0 (S i), inl [nth i vals' ErrorValue],
     nth_def eff' eff1 [] (S i) |) ->
(forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
        | env, modules, own_module, last ids id, nth (Datatypes.length vals) exps ErrorExp,
        last eff eff1 | -e> | id'', v2, eff'' | ->
        inr ex = v2 /\ eff2 = eff'' /\ id' = id'')
->
Datatypes.length vals < Datatypes.length exps ->
Datatypes.length eff = Datatypes.length vals ->
Datatypes.length exps = Datatypes.length vals' ->
Datatypes.length exps = Datatypes.length eff' ->
length exps = length ids' ->
length ids = length vals
->
False.
Proof.
  induction eff.
  * intros. apply eq_sym, length_zero_iff_nil in H3. subst.
    apply length_zero_iff_nil in H7. subst.
    pose (P := H0 0 H2).
    pose (P2 := H1 _ _ _ P). inversion P2. congruence.
  * intros. destruct eff'.
    - inversion H5. rewrite H5 in H2. inversion H2.
    - inversion H3. inversion H5.
    (* first elements *)
      assert (0 < length exps). { lia. } assert (0 < length vals). { lia. }
      assert (S (Datatypes.length eff') = Datatypes.length exps). { auto. }
      assert (Datatypes.length exps = Datatypes.length vals') as LENGTH. { auto. }
      assert (S (Datatypes.length eff) = Datatypes.length vals) as Helper1. { auto. }
      assert (Datatypes.length exps = Datatypes.length ids') as Helper2. { auto. }
      (* single_unfold_list H9. *)
      pose (EE1 := element_exist (length eff') exps (eq_sym H5)).
      pose (EE2 := element_exist (length eff) vals H9).
      rewrite H5 in H4, H6. rewrite <- H9 in H7.
      pose (EE3 := element_exist (length eff') vals' H4).
      pose (EE4 := element_exist _ _ (eq_sym H7)).
      pose (EE5 := element_exist _ _ H6).
      
      inversion EE1 as [e]. inversion EE2 as [v]. inversion EE3 as [v'].
      inversion EE4 as [id0']. inversion EE5 as [id0'']. 
      inversion H13. inversion H14. inversion H15. inversion H16. inversion H17. subst.
      pose (P0 := H0 0 H8).
      pose (P1 := H 0 H11 (inl [v']) s).
      pose (P2 := P1 _ P0). destruct P2. destruct H19. inversion H18. simpl in H19, H20. subst.
    (* other elements *)
      inversion H3.
      apply IHeff with (exps := x) (vals := x0) (eff1 := s) (vals' := x1)
                  (ids := x2) (ids' := x3) (id := id0'') (ex := ex) (eff' := eff')
                  (eff2 := eff2) (id' := id'); auto.
        + intros. assert (S j < Datatypes.length (v' :: x0)). { simpl. lia. } 
          pose (A := H (S j) H22 v2 eff'').
          pose (B := A _ H21). assumption.
        + intros. assert (S i < Datatypes.length (e :: x)). { simpl. lia. } 
          pose (A := H0 (S i) H21). exact A.
        + intros. rewrite <- last_element_equal, <- last_element_equal in H1. apply H1. assumption.
        + intuition.
        + inversion H7. lia.
Qed.
(* 

Lemma singleexplist_prefix_eq_rev {env : Environment} {eff : list SideEffectList} : 
   forall (eff' : list SideEffectList) (exps : list SingleExpression) (vals vals' : list Value) 
          (eff1 : SideEffectList) (ids ids' : list nat) (id : nat) (eff2 : SideEffectList) 
          (id' : nat) (ex : Exception),
(forall j : nat,
     j < Datatypes.length vals ->
     forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j | -s> | id'', v2, eff'' | ->
     inl [nth j vals ErrorValue] = v2 /\ nth_def eff eff1 [] (S j) = eff'' /\ nth_def ids id 0 (S j) = id'')
->
(forall i : nat,
     i < Datatypes.length exps ->
     | env, nth_def ids' id 0 i, nth i exps ErrorExp, nth_def eff' eff1 [] i | -s>
     | nth_def ids' id 0 (S i), inl [nth i vals' ErrorValue],
     nth_def eff' eff1 [] (S i) |) ->
(forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
        | env, last ids id, nth (Datatypes.length vals) exps ErrorExp,
        last eff eff1 | -s> | id'', v2, eff'' | ->
        inr ex = v2 /\ eff2 = eff'' /\ id' = id'')
->
Datatypes.length vals < Datatypes.length exps ->
Datatypes.length eff = Datatypes.length vals ->
Datatypes.length exps = Datatypes.length vals' ->
Datatypes.length exps = Datatypes.length eff' ->
length exps = length ids' ->
length ids = length vals
->
False.
Proof.
  induction eff.
  * intros. apply eq_sym, length_zero_iff_nil in H3. subst.
    apply length_zero_iff_nil in H7. subst.
    pose (P := H0 0 H2).
    pose (P2 := H1 _ _ _ P). inversion P2. congruence.
  * intros. destruct eff'.
    - inversion H5. rewrite H5 in H2. inversion H2.
    - inversion H3. inversion H5.
    (* first elements *)
      assert (0 < length exps). { lia. } assert (0 < length vals). { lia. }
      assert (S (Datatypes.length eff') = Datatypes.length exps). { auto. }
      assert (Datatypes.length exps = Datatypes.length vals') as LENGTH. { auto. }
      assert (S (Datatypes.length eff) = Datatypes.length vals) as Helper1. { auto. }
      assert (Datatypes.length exps = Datatypes.length ids') as Helper2. { auto. }
      (* single_unfold_list H9. *)
      pose (EE1 := element_exist (length eff') exps (eq_sym H5)).
      pose (EE2 := element_exist (length eff) vals H9).
      rewrite H5 in H4, H6. rewrite <- H9 in H7.
      pose (EE3 := element_exist (length eff') vals' H4).
      pose (EE4 := element_exist _ _ (eq_sym H7)).
      pose (EE5 := element_exist _ _ H6).
      
      inversion EE1 as [e]. inversion EE2 as [v]. inversion EE3 as [v'].
      inversion EE4 as [id0']. inversion EE5 as [id0'']. 
      inversion H13. inversion H14. inversion H15. inversion H16. inversion H17. subst.
      pose (P0 := H0 0 H8).
      pose (P1 := H 0 H11 (inl [v']) s).
      pose (P2 := P1 _ P0). destruct P2. destruct H19. inversion H18. simpl in H19, H20. subst.
    (* other elements *)
      inversion H3.
      apply IHeff with (exps := x) (vals := x0) (eff1 := s) (vals' := x1)
                  (ids := x2) (ids' := x3) (id := id0'') (ex := ex) (eff' := eff')
                  (eff2 := eff2) (id' := id'); auto.
        + intros. assert (S j < Datatypes.length (v' :: x0)). { simpl. lia. } 
          pose (A := H (S j) H22 v2 eff'').
          pose (B := A _ H21). assumption.
        + intros. assert (S i < Datatypes.length (e :: x)). { simpl. lia. } 
          pose (A := H0 (S i) H21). exact A.
        + intros. rewrite <- last_element_equal, <- last_element_equal in H1. apply H1. assumption.
        + intuition.
        + inversion H7. lia.
Qed. *)

(** First i element are equal with concatn *)
Lemma con_n_equality {env : Environment} {modules : list ErlModule} {own_module : string} {eff : list SideEffectList} : 
  forall (exps : list Expression) (vals vals0 : list Value) eff1 eff6 i i0 ids ids0 id eff3 id' ex,
(forall j : nat,
    j < i ->
    forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
    | env, modules, own_module, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j | -e> | id'', v2, eff'' | ->
    inl [nth j vals ErrorValue] = v2 /\ nth_def eff eff1 [] (S j) = eff'' /\ nth_def ids id 0 (S j) = id'')
->
(forall j : nat,
     j < i0 ->
     | env, modules, own_module, nth_def ids0 id 0 j, nth j exps ErrorExp, nth_def eff6 eff1 [] j | -e>
     | nth_def ids0 id 0 (S j), inl [nth j vals0 ErrorValue],
     nth_def eff6 eff1 [] (S j) |)
->
(forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, modules, own_module, last ids id, nth i exps ErrorExp, last eff eff1 | -e> | id'', v2, eff'' | ->
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
    pose (EE1 := element_exist (length eff) vals (eq_sym H4)). 
    inversion EE1 as [v]. inversion H12 as [vs]. destruct eff6.
    - simpl in H7. subst. rewrite <- H7 in H10. inversion H10.
    - subst. simpl. (* simpl_concatn_H IHeff. rewrite concatn_app, concatn_app. simpl_concatn. *)
      simpl in H7. (* single_unfold_list H6. *) 
      pose (EE2 := element_exist (length eff6) vals0 H7). inversion EE2. 
      inversion H2.
      pose (NE := nat_lt_zero _ _  H3). inversion NE.
      pose (EE3 := element_exist x1 exps (eq_sym H13)). inversion EE3. inversion H14.
      subst. 
      pose (EE4 := element_exist _ _ (eq_sym H8)).
      pose (EE5 := element_exist _ _ (eq_sym H9)).
      inversion EE4 as [id0']. inversion EE5 as [id0''].
      inversion H5. inversion H15. subst.
      assert (s = a /\ id0' = id0''). {
        subst.
        assert (0 < Datatypes.length (x :: x0)). {  simpl. lia. }
        pose (P := H0 0 H16).
        assert (0 < S (Datatypes.length eff)). {  simpl. lia. }
        pose (P2 := H 0 H17 (inl [nth 0 (x :: x0) ErrorValue]) (nth_def (s :: eff6) eff1 [] 1) _ P). 
        inversion P2.
        destruct H19. auto.
      }
      destruct H16. subst.
      
      eapply IHeff with (exps := x3) (vals := vs) (vals0 := x0) (eff1 := a)
                        (i0 := length x0) (ids := x4) (ids0 := x5); auto.
      + intros. assert (S j < S (Datatypes.length eff)). { simpl. lia. }
        pose (P := H (S j) H18 v2 eff'' id''). pose (P H17). assumption.
      + intros. assert (S j < Datatypes.length (x :: x0)). { simpl. lia. }
        pose (P := H0 (S j) H17). exact P.
      + intros. apply H1.
        rewrite (last_element_equal _ _ id), (last_element_equal _ _ eff1) in H16.
        exact H16.
      + intuition.
      + intuition.
      + intuition.
      + intuition.
Qed.

(** Value lists are equal until ith value *)
Lemma list_equal_until_i {env : Environment} {modules : list ErlModule} {own_module : string} {eff : list SideEffectList} :
  forall (exps : list Expression) (vals vals0 : list Value) (eff6 : list SideEffectList)
      (eff1 : SideEffectList) (ids ids0 : list nat) (id : nat),
(forall j : nat,
    j < Datatypes.length vals ->
    forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
    | env, modules, own_module, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j | -e> | id'', v2, eff'' | ->
    inl [nth j vals ErrorValue] = v2 /\ nth_def eff eff1 [] (S j) = eff'' /\ nth_def ids id 0 (S j) = id'')
->
(forall j : nat,
     j < Datatypes.length vals0 ->
     | env, modules, own_module, nth_def ids0 id 0 j, nth j exps ErrorExp, nth_def eff6 eff1 [] j | -e> 
     | nth_def ids0 id 0 (S j), inl [nth j vals0 ErrorValue],
     nth_def eff6 eff1 [] (S j) |)
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
  * intros. simpl in H2. rewrite <- H2 in H1. rewrite <- H1 in H3. pose (NE := nat_lt_zero _ _ H4). inversion NE.
    (* single_unfold_list H2. *)
    pose (EE1 := element_exist (length eff) vals H2).
    pose (EE2 := element_exist (length eff) vals0 H1).
    pose (EE3 := element_exist (length eff) eff6 (eq_sym H3)).
    pose (EE4 := element_exist x exps (eq_sym H7)).
    inversion EE1 as [v]. inversion EE2 as [v']. inversion EE3 as [fe]. inversion EE4 as [e'].
    inversion H8. inversion H9. inversion H10. inversion H11. subst.
    pose (EE5 := element_exist _ _ (eq_sym H5)).
    pose (EE6 := element_exist _ _ (eq_sym H6)).
    inversion EE5 as [id']. inversion EE6 as [id''].
    inversion H12. inversion H13. subst.
    assert (0 < Datatypes.length (v' :: x1)). { simpl. lia. }
    pose (P := H0 0 H14).
    assert (0 < Datatypes.length (v :: x0)). { simpl. lia. }
    pose (P1 := H 0 H15 (inl [nth 0 (v' :: x1) ErrorValue]) (nth_def (fe :: x2) eff1 [] 1) _ P).
    inversion P1. destruct H17. simpl in H18. inversion H16. simpl in H17. subst.
    
    assert (eff = x2 /\ x0 = x1 /\ x4 = x5).
    {
      apply IHeff with (exps := x3) (vals := x0) (vals0 := x1) (eff1 := fe) (id := id''); auto.
      + intros. assert (S j < S (Datatypes.length x0)). { simpl. lia. } pose (P2 := H (S j) H19 v2 eff''). 
        simpl in P2. pose (P2 _ H18). assumption.
      + intros. assert (S j < Datatypes.length (v' :: x1)). { simpl. lia. }
        pose (P3 := H0 (S j) H18). simpl in P3. assumption.
      + inversion H2. inversion H3. inversion H1. auto.
      + inversion H2. inversion H3. inversion H1. auto.
      + intuition.
    }
    inversion H17. inversion H19. subst. auto.
Qed.

(** Slightly different hypotheses for i first element concatn equality *)
Lemma con_n_equality_rev {env : Environment} {modules : list ErlModule} {own_module : string} {eff : list SideEffectList} : 
forall (exps : list Expression) (vals vals0 : list Value) (eff1 : SideEffectList) 
   (eff6 : list SideEffectList) (i i0 : nat) (id : nat) (ids ids0 : list nat) id' ex0 eff4,
(forall j : nat,
    j < i ->
    forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
    | env, modules, own_module, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j | -e> | id'', v2, eff'' | ->
    inl [nth j vals ErrorValue] = v2 /\ nth_def eff eff1 [] (S j) = eff'' /\ nth_def ids id 0 (S j) = id'')
->
(forall j : nat,
     j < i0 ->
     | env, modules, own_module, nth_def ids0 id 0 j, nth j exps ErrorExp, nth_def eff6 eff1 [] j | -e> 
     | nth_def ids0 id 0 (S j), inl [nth j vals0 ErrorValue],
     nth_def eff6 eff1 [] (S j) |)
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
(| env, modules, own_module, last ids0 id, nth i0 exps ErrorExp, last eff6 eff1 | -e> | id', 
     inr ex0,eff4 |)
->
False.
Proof.
induction eff.
  * intros. simpl in H1. subst. inversion H9.
  * intros. simpl in H1. rewrite <- H1 in H3.
    pose (EE1 := element_exist (length eff) vals (eq_sym H3)).
    inversion EE1 as [v]. inversion H11 as [vs]. destruct eff6.
    - subst. apply eq_sym, length_zero_iff_nil in H6. subst. apply length_zero_iff_nil in H8.
      subst.
      simpl in H10. pose (P := H 0 (Nat.lt_0_succ _) _ _ _ H10). inversion P. congruence.
    - subst.
      assert (Datatypes.length ids0 = Datatypes.length vals0) as Helper. { auto. }
      pose (EE2 := element_exist (length eff6) vals0 H6). inversion EE2. inversion H1.
      pose (NE := nat_lt_zero _ _ H2). inversion NE.
      pose (EE3 := element_exist x1 exps (eq_sym H12)). inversion EE3.
      inversion H13. subst.
      pose (EE4 := element_exist _ _ (eq_sym H7)).
      pose (EE5 := element_exist _ _ (eq_sym H8)).
      inversion EE4 as [id0']. inversion EE5 as [id0'']. inversion H4. inversion H14. subst.
      assert (s = a /\ id0' = id0''). {
        subst.
        assert (0 < Datatypes.length (x :: x0)). {  simpl. lia. }
        pose (P := H0 0 H15).
        assert (0 < S (Datatypes.length eff)). {  simpl. lia. }
        pose (P1 := H 0 H16 (inl [nth 0 (x :: x0) ErrorValue]) (nth_def (s :: eff6) eff1 [] 1) _ P).
        destruct P1. destruct H18. simpl in H19, H18. auto.
      }
      destruct H15. subst.
      eapply IHeff with (exps := x3) (vals := vs) (vals0 := x0) (eff1 := a) 
                       (i0 := length eff6) (i := length eff) (ids := x4) (ids0 := x5); auto.
      + intros. assert (S j < S (Datatypes.length eff)). { simpl. lia. }
        pose (P := H (S j) H17 v2 eff''). simpl in P.
        pose (P1 := P _ H16). assumption.
      + intros. inversion H6. assert (S j < Datatypes.length (x :: x0)). { simpl. lia. }
        pose (P := H0 (S j) H16). assumption.
      + intuition.
      + inversion H6. auto.
      + rewrite <- H6 in H5. simpl in H5. lia.
      + rewrite <- H6 in Helper. auto.
      + simpl in *. rewrite <- H6 in H9. lia.
      + rewrite <- last_element_equal, <- last_element_equal in H10. simpl in H10. 
        inversion H6. rewrite H16. exact H10.
Qed.

(** Based on determinsim, using lists with exceptions, these are equal *)
Lemma exception_equality {env : Environment} {modules : list ErlModule} {own_module : string} {exps : list Expression} (vals vals0 : list Value) 
   (ex : Exception) (eff1 : SideEffectList) (eff eff6 : list SideEffectList) (i i0 : nat) 
   (eff3 : SideEffectList) (ex0 : Exception) (eff4 : SideEffectList) (ids ids0 : list nat)
   (id id' id'' : nat) :
(forall j : nat,
     j < i ->
     forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, modules, own_module, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j | -e> | id'', v2, eff'' | ->
     inl [nth j vals ErrorValue] = v2 /\ nth_def eff eff1 [] (S j) = eff'' /\ nth_def ids id 0 (S j) = id'')
->
| env, modules, own_module, last ids0 id, nth i0 exps ErrorExp, last eff6 eff1 | -e>
| id'', inr ex0, eff4 |
->
(forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
        | env, modules, own_module, last ids id, nth i exps ErrorExp, last eff eff1 | -e>
        | id'', v2, eff'' | -> inr ex = v2 /\ eff3 = eff'' /\ id' = id'')
->
(forall j : nat,
      j < i0 ->
      | env, modules, own_module, nth_def ids0 id 0 j, nth j exps ErrorExp, nth_def eff6 eff1 [] j | -e>
      | nth_def ids0 id 0 (S j), inl [nth j vals0 ErrorValue],
      nth_def eff6 eff1 [] (S j) |)
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
  intros. destruct (Compare_dec.le_gt_dec i i0).
  * case_eq (Lt.le_lt_or_eq i i0 l).
    - intros.
      pose (P1 := con_n_equality exps vals vals0 eff1 eff6 i i0 ids ids0 id _ _ _
                 H H2 H1 H5 H4 H3 H6 H7 H8 H9 H10 l0). inversion P1.
    - intros. subst. pose (list_equal_until_i exps vals vals0 eff6 eff1 _ _ _
                            H H2 e H5 H8 H7 H9 H10). auto.
  * pose (P := con_n_equality_rev exps vals vals0 eff1 eff6 i i0 id ids ids0 _ _ _
               H H2 H5 H4 H3 H6 H7 H8 H9 H10 g H0). inversion P.
Qed.
(* 
Lemma con_n_equality_single {env : Environment} {eff : list SideEffectList} : 
  forall (exps : list SingleExpression) (vals vals0 : list Value) eff1 eff6 i i0 ids ids0 id eff3 id' ex,
(forall j : nat,
    j < i ->
    forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
    | env, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j | -s> | id'', v2, eff'' | ->
    inl [nth j vals ErrorValue] = v2 /\ nth_def eff eff1 [] (S j) = eff'' /\ nth_def ids id 0 (S j) = id'')
->
(forall j : nat,
     j < i0 ->
     | env, nth_def ids0 id 0 j, nth j exps ErrorExp, nth_def eff6 eff1 [] j | -s>
     | nth_def ids0 id 0 (S j), inl [nth j vals0 ErrorValue],
     nth_def eff6 eff1 [] (S j) |)
->
(forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, last ids id, nth i exps ErrorExp, last eff eff1 | -s> | id'', v2, eff'' | ->
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
    pose (EE1 := element_exist (length eff) vals (eq_sym H4)). 
    inversion EE1 as [v]. inversion H12 as [vs]. destruct eff6.
    - simpl in H7. subst. rewrite <- H7 in H10. inversion H10.
    - subst. simpl. (* simpl_concatn_H IHeff. rewrite concatn_app, concatn_app. simpl_concatn. *)
      simpl in H7. (* single_unfold_list H6. *) 
      pose (EE2 := element_exist (length eff6) vals0 H7). inversion EE2. 
      inversion H2.
      pose (NE := nat_lt_zero _ _  H3). inversion NE.
      pose (EE3 := element_exist x1 exps (eq_sym H13)). inversion EE3. inversion H14.
      subst. 
      pose (EE4 := element_exist _ _ (eq_sym H8)).
      pose (EE5 := element_exist _ _ (eq_sym H9)).
      inversion EE4 as [id0']. inversion EE5 as [id0''].
      inversion H5. inversion H15. subst.
      assert (s = a /\ id0' = id0''). {
        subst.
        assert (0 < Datatypes.length (x :: x0)). {  simpl. lia. }
        pose (P := H0 0 H16).
        assert (0 < S (Datatypes.length eff)). {  simpl. lia. }
        pose (P2 := H 0 H17 (inl [nth 0 (x :: x0) ErrorValue]) (nth_def (s :: eff6) eff1 [] 1) _ P). 
        inversion P2.
        destruct H19. auto.
      }
      destruct H16. subst.
      
      eapply IHeff with (exps := x3) (vals := vs) (vals0 := x0) (eff1 := a)
                        (i0 := length x0) (ids := x4) (ids0 := x5); auto.
      + intros. assert (S j < S (Datatypes.length eff)). { simpl. lia. }
        pose (P := H (S j) H18 v2 eff'' id''). pose (P H17). assumption.
      + intros. assert (S j < Datatypes.length (x :: x0)). { simpl. lia. }
        pose (P := H0 (S j) H17). exact P.
      + intros. apply H1.
        rewrite (last_element_equal _ _ id), (last_element_equal _ _ eff1) in H16.
        exact H16.
      + intuition.
      + intuition.
      + intuition.
      + intuition.
Qed.

(** Value lists are equal until ith value *)
Lemma list_equal_until_i_single {env : Environment} {eff : list SideEffectList} :
  forall (exps : list SingleExpression) (vals vals0 : list Value) (eff6 : list SideEffectList)
      (eff1 : SideEffectList) (ids ids0 : list nat) (id : nat),
(forall j : nat,
    j < Datatypes.length vals ->
    forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
    | env, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j | -s> | id'', v2, eff'' | ->
    inl [nth j vals ErrorValue] = v2 /\ nth_def eff eff1 [] (S j) = eff'' /\ nth_def ids id 0 (S j) = id'')
->
(forall j : nat,
     j < Datatypes.length vals0 ->
     | env, nth_def ids0 id 0 j, nth j exps ErrorExp, nth_def eff6 eff1 [] j | -s> 
     | nth_def ids0 id 0 (S j), inl [nth j vals0 ErrorValue],
     nth_def eff6 eff1 [] (S j) |)
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
  * intros. simpl in H2. rewrite <- H2 in H1. rewrite <- H1 in H3. pose (NE := nat_lt_zero _ _ H4). inversion NE.
    (* single_unfold_list H2. *)
    pose (EE1 := element_exist (length eff) vals H2).
    pose (EE2 := element_exist (length eff) vals0 H1).
    pose (EE3 := element_exist (length eff) eff6 (eq_sym H3)).
    pose (EE4 := element_exist x exps (eq_sym H7)).
    inversion EE1 as [v]. inversion EE2 as [v']. inversion EE3 as [fe]. inversion EE4 as [e'].
    inversion H8. inversion H9. inversion H10. inversion H11. subst.
    pose (EE5 := element_exist _ _ (eq_sym H5)).
    pose (EE6 := element_exist _ _ (eq_sym H6)).
    inversion EE5 as [id']. inversion EE6 as [id''].
    inversion H12. inversion H13. subst.
    assert (0 < Datatypes.length (v' :: x1)). { simpl. lia. }
    pose (P := H0 0 H14).
    assert (0 < Datatypes.length (v :: x0)). { simpl. lia. }
    pose (P1 := H 0 H15 (inl [nth 0 (v' :: x1) ErrorValue]) (nth_def (fe :: x2) eff1 [] 1) _ P).
    inversion P1. destruct H17. simpl in H18. inversion H16. simpl in H17. subst.
    
    assert (eff = x2 /\ x0 = x1 /\ x4 = x5).
    {
      apply IHeff with (exps := x3) (vals := x0) (vals0 := x1) (eff1 := fe) (id := id''); auto.
      + intros. assert (S j < S (Datatypes.length x0)). { simpl. lia. } pose (P2 := H (S j) H19 v2 eff''). 
        simpl in P2. pose (P2 _ H18). assumption.
      + intros. assert (S j < Datatypes.length (v' :: x1)). { simpl. lia. }
        pose (P3 := H0 (S j) H18). simpl in P3. assumption.
      + inversion H2. inversion H3. inversion H1. auto.
      + inversion H2. inversion H3. inversion H1. auto.
      + intuition.
    }
    inversion H17. inversion H19. subst. auto.
Qed.

(** Slightly different hypotheses for i first element concatn equality *)
Lemma con_n_equality_rev_single {env : Environment} {eff : list SideEffectList} : 
forall (exps : list SingleExpression) (vals vals0 : list Value) (eff1 : SideEffectList) 
   (eff6 : list SideEffectList) (i i0 : nat) (id : nat) (ids ids0 : list nat) id' ex0 eff4,
(forall j : nat,
    j < i ->
    forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
    | env, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j | -s> | id'', v2, eff'' | ->
    inl [nth j vals ErrorValue] = v2 /\ nth_def eff eff1 [] (S j) = eff'' /\ nth_def ids id 0 (S j) = id'')
->
(forall j : nat,
     j < i0 ->
     | env, nth_def ids0 id 0 j, nth j exps ErrorExp, nth_def eff6 eff1 [] j | -s> 
     | nth_def ids0 id 0 (S j), inl [nth j vals0 ErrorValue],
     nth_def eff6 eff1 [] (S j) |)
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
(| env, last ids0 id, nth i0 exps ErrorExp, last eff6 eff1 | -s> | id', 
     inr ex0,eff4 |)
->
False.
Proof.
induction eff.
  * intros. simpl in H1. subst. inversion H9.
  * intros. simpl in H1. rewrite <- H1 in H3.
    pose (EE1 := element_exist (length eff) vals (eq_sym H3)).
    inversion EE1 as [v]. inversion H11 as [vs]. destruct eff6.
    - subst. apply eq_sym, length_zero_iff_nil in H6. subst. apply length_zero_iff_nil in H8.
      subst.
      simpl in H10. pose (P := H 0 (Nat.lt_0_succ _) _ _ _ H10). inversion P. congruence.
    - subst.
      assert (Datatypes.length ids0 = Datatypes.length vals0) as Helper. { auto. }
      pose (EE2 := element_exist (length eff6) vals0 H6). inversion EE2. inversion H1.
      pose (NE := nat_lt_zero _ _ H2). inversion NE.
      pose (EE3 := element_exist x1 exps (eq_sym H12)). inversion EE3.
      inversion H13. subst.
      pose (EE4 := element_exist _ _ (eq_sym H7)).
      pose (EE5 := element_exist _ _ (eq_sym H8)).
      inversion EE4 as [id0']. inversion EE5 as [id0'']. inversion H4. inversion H14. subst.
      assert (s = a /\ id0' = id0''). {
        subst.
        assert (0 < Datatypes.length (x :: x0)). {  simpl. lia. }
        pose (P := H0 0 H15).
        assert (0 < S (Datatypes.length eff)). {  simpl. lia. }
        pose (P1 := H 0 H16 (inl [nth 0 (x :: x0) ErrorValue]) (nth_def (s :: eff6) eff1 [] 1) _ P).
        destruct P1. destruct H18. simpl in H19, H18. auto.
      }
      destruct H15. subst.
      eapply IHeff with (exps := x3) (vals := vs) (vals0 := x0) (eff1 := a) 
                       (i0 := length eff6) (i := length eff) (ids := x4) (ids0 := x5); auto.
      + intros. assert (S j < S (Datatypes.length eff)). { simpl. lia. }
        pose (P := H (S j) H17 v2 eff''). simpl in P.
        pose (P1 := P _ H16). assumption.
      + intros. inversion H6. assert (S j < Datatypes.length (x :: x0)). { simpl. lia. }
        pose (P := H0 (S j) H16). assumption.
      + intuition.
      + inversion H6. auto.
      + rewrite <- H6 in H5. simpl in H5. lia.
      + rewrite <- H6 in Helper. auto.
      + simpl in *. rewrite <- H6 in H9. lia.
      + rewrite <- last_element_equal, <- last_element_equal in H10. simpl in H10. 
        inversion H6. rewrite H16. exact H10.
Qed.

(** Based on determinsim, using lists with exceptions, these are equal *)
Lemma exception_equality_single {env : Environment} {exps : list SingleExpression} (vals vals0 : list Value) 
   (ex : Exception) (eff1 : SideEffectList) (eff eff6 : list SideEffectList) (i i0 : nat) 
   (eff3 : SideEffectList) (ex0 : Exception) (eff4 : SideEffectList) (ids ids0 : list nat)
   (id id' id'' : nat) :
(forall j : nat,
     j < i ->
     forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j | -s> | id'', v2, eff'' | ->
     inl [nth j vals ErrorValue] = v2 /\ nth_def eff eff1 [] (S j) = eff'' /\ nth_def ids id 0 (S j) = id'')
->
| env, last ids0 id, nth i0 exps ErrorExp, last eff6 eff1 | -s>
| id'', inr ex0, eff4 |
->
(forall (v2 : ValueSequence + Exception) (eff'' : SideEffectList) (id'' : nat),
        | env, last ids id, nth i exps ErrorExp, last eff eff1 | -s>
        | id'', v2, eff'' | -> inr ex = v2 /\ eff3 = eff'' /\ id' = id'')
->
(forall j : nat,
      j < i0 ->
      | env, nth_def ids0 id 0 j, nth j exps ErrorExp, nth_def eff6 eff1 [] j | -s>
      | nth_def ids0 id 0 (S j), inl [nth j vals0 ErrorValue],
      nth_def eff6 eff1 [] (S j) |)
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
  intros. destruct (Compare_dec.le_gt_dec i i0).
  * case_eq (Lt.le_lt_or_eq i i0 l).
    - intros.
      pose (P1 := con_n_equality_single exps vals vals0 eff1 eff6 i i0 ids ids0 id _ _ _
                 H H2 H1 H5 H4 H3 H6 H7 H8 H9 H10 l0). inversion P1.
    - intros. subst. pose (list_equal_until_i_single exps vals vals0 eff6 eff1 _ _ _
                            H H2 e H5 H8 H7 H9 H10). auto.
  * pose (P := con_n_equality_rev_single exps vals vals0 eff1 eff6 i i0 id ids ids0 _ _ _
               H H2 H5 H4 H3 H6 H7 H8 H9 H10 g H0). inversion P.
Qed. *)
