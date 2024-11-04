(**
  This file shows the equivalence between the natural and the functional big-
  step semantics of Core Erlang.
*)

From CoreErlang.BigStep Require Import Tactics.
From CoreErlang.BigStep Require Export FunctionalBigStep.

Import ListNotations.

(**
  Equivalence between the big-step and functional big-step semantics
*)

Section Soundness.

Lemma restrict_soundness :
forall {A : Type} {env modules own_module exps a v} {id : nat} {id' eff' eff1 x x0 x1 defexp defval} {f : nat -> Environment -> (list ErlModule) -> string -> nat -> A -> SideEffectList -> ResultType},
(forall i : nat,
    i < Datatypes.length (a :: exps) ->
    exists clock : nat,
      f clock env modules own_module (nth_def (id' :: x1) id 0 i) (nth i (a :: exps) defexp)
        (nth_def (eff' :: x0) eff1 [] i) =
      Result (nth_def (id' :: x1) id 0 (S i)) (inl [nth i (v :: x) defval])
        (nth_def (eff' :: x0) eff1 [] (S i)))
->
(forall i : nat,
    i < Datatypes.length (exps) ->
    exists clock : nat,
      f clock env modules own_module (nth_def x1 id' 0 i) (nth i exps defexp)
        (nth_def x0 eff' [] i) =
      Result (nth_def x1 id' 0 (S i)) (inl [nth i x defval])
        (nth_def x0 eff' [] (S i))).
Proof.
  intros.
  assert (S i < S (length exps)) as A1.
  { simpl. lia. } pose (E := H (S i) A1). 
  destruct E. simpl nth_def in H1. simpl nth in H. exists x2. simpl. exact H1.
Qed.

Lemma fbs_expr_list_soundness :
forall {exps : list Expression} {vals eff ids env modules own_module id eff1},
(forall i : nat,
    i < Datatypes.length exps ->
    exists clock : nat,
      fbs_expr clock env modules own_module (nth_def ids id 0 i) (nth i exps ErrorExp) (nth_def eff eff1 [] i) =
      Result (nth_def ids id 0 (S i)) (inl [nth i vals ErrorValue])
        (nth_def eff eff1 [] (S i))) ->
  length exps = length vals ->
  length exps = length eff ->
  length exps = length ids
->
  exists clock, fbs_values (fbs_expr clock) env modules own_module id exps eff1 = Result (last ids id) (inl vals) (last eff eff1).
Proof.
  induction exps; intros.
  * apply eq_sym, length_zero_iff_nil in H0.
    apply eq_sym, length_zero_iff_nil in H1.
    apply eq_sym, length_zero_iff_nil in H2. subst.
    exists 1. simpl. auto.
  * pose (EE1 := element_exist _ _ H0).
    pose (EE2 := element_exist _ _ H1).
    pose (EE3 := element_exist _ _ H2).
    destruct EE1 as [v], EE2 as [eff'], EE3 as [id'], H3, H4, H5. subst.
    inversion H0. inversion H1. inversion H2.

    pose (P := H 0 (Nat.lt_0_succ _)). destruct P as [cl1]. simpl in H3.

    epose (P2 := IHexps _ _ _ _ _ _ _ _ (restrict_soundness H) _ _ _).
    Unshelve.
    2-4: auto.
    destruct P2 as [cl2].
    exists (cl1 + cl2).
    simpl fbs_values.
    apply bigger_clock_expr with (clock' := cl1 + cl2) in H3. 2: lia.
    apply bigger_clock_list with (clock' := cl1 + cl2) in H7. 
      2: lia. 2: intros; apply clock_increase_expr; auto.
    rewrite H3, H7.
    rewrite last_element_equal with (def2 := id).
    rewrite last_element_equal with (def2 := eff1). auto.
Qed.

Lemma fbs_expr_list_soundness_exception :
forall {exps : list Expression} {vals eff ids env modules own_module id eff1 id' ex eff' i},
(forall j : nat,
    j < i ->
    exists clock : nat,
      fbs_expr clock env modules own_module (nth_def ids id 0 j) (nth j exps ErrorExp) (nth_def eff eff1 [] j) =
      Result (nth_def ids id 0 (S j)) (inl [nth j vals ErrorValue])
        (nth_def eff eff1 [] (S j)))
->
(exists clock : nat,
       fbs_expr clock env modules own_module (last ids id) (nth i exps ErrorExp) (last eff eff1) =
       Result id' (inr ex) eff')
->
i < Datatypes.length exps ->
Datatypes.length vals = i ->
Datatypes.length eff = i ->
Datatypes.length ids = i
->
  exists clock, fbs_values (fbs_expr clock) env modules own_module id exps eff1 = Result id' (inr ex) eff'.
Proof.
  induction exps; intros.
  * inversion H1.
  * destruct i.
    - apply length_zero_iff_nil in H2.
      apply length_zero_iff_nil in H3.
      apply length_zero_iff_nil in H4. subst.
      destruct H0. exists x. simpl in *. rewrite H0. auto.
    - pose (P1 := element_exist _ _ (eq_sym H2)).
      pose (P2 := element_exist _ _ (eq_sym H3)).
      pose (P3 := element_exist _ _ (eq_sym H4)).
      destruct P1 as [v0']. destruct P2 as [eff0']. destruct P3 as [id0'].
      destruct H5, H6, H7. subst.
      pose (P := H 0 (Nat.lt_0_succ _)). destruct P. simpl in H5.
      simpl in H1. apply Nat.succ_lt_mono in H1.
      simpl in H2, H3, H4.
      apply eq_add_S in H2. apply eq_add_S in H3. apply eq_add_S in H4.
      rewrite <- last_element_equal, <- last_element_equal in H0.
      epose (P2 := IHexps _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H1 H2 H3 H4).
      destruct P2. exists (x2 + x3).
      simpl.
      apply bigger_clock_expr with (clock' := x2 + x3) in H5.
      apply bigger_clock_list with (clock' := x2 + x3) in H6.
      rewrite H5, H6. auto.
      1, 3: lia.
      intros. apply clock_increase_expr. auto.
  Unshelve.
  intros. epose (H (S j) _). exact e.
  Unshelve.
  lia.
Qed.

Lemma fbs_case_soundness :
forall {l id' eff2 id'' res eff3 vals env modules own_module i guard exp bindings},
(forall j : nat,
     j < i ->
     forall (gg ee : Expression) (bb : list (Var * Value)),
     match_clause vals l j = Some (gg, ee, bb) ->
     exists clock : nat,
       fbs_expr clock (add_bindings bb env) modules own_module id' gg eff2 = Result id' (inl [ffalse]) eff2) ->
match_clause vals l i = Some (guard, exp, bindings) ->
(exists clock : nat,
       fbs_expr clock (add_bindings bindings env) modules  own_module id' guard eff2 =
       Result id' (inl [ttrue]) eff2) ->
(exists clock : nat,
       fbs_expr clock (add_bindings bindings env) modules own_module id' exp eff2 = Result id'' res eff3) ->
exists clock, fbs_case l env modules own_module id' eff2 vals (fbs_expr clock) = Result id'' res eff3.
Proof.
  induction l; intros.
  * inversion H0.
  * destruct i.
    - simpl in H0. destruct H1, H2. exists (x + x0).
      destruct a, p. simpl. destruct (match_valuelist_to_patternlist vals l0).
      + inversion H0. subst.
        apply bigger_clock_expr with (clock' := x + x0) in H1. rewrite H1.
        unfold ttrue. rewrite eqb_refl, Nat.eqb_refl, list_eqb_refl.
        simpl.
        apply bigger_clock_expr with (clock' := x + x0) in H2. rewrite H2. auto.
        1,3: lia. apply effect_eqb_refl.
      + congruence.
    - simpl. destruct a, p.
      case_eq (match_clause vals ((l0, e0, e) :: l) 0); intros.
       + destruct p, p.
         pose (H 0 (Nat.lt_0_succ _) _ _ _ H3). simpl in H3. destruct e3.
         destruct (match_valuelist_to_patternlist vals l0). 2: congruence.
         inversion H3. subst.
         epose (IHl id' eff2 id'' res eff3 vals env modules own_module i guard exp bindings _ _ _ _).
         destruct e. exists (x + x0).
         apply bigger_clock_expr with (clock' := x + x0) in H4.
         apply bigger_clock_case with (clock' := x + x0) in H5.
         rewrite H4. unfold ffalse. simpl.
         replace (((id' =? id') && list_eqb effect_eqb eff2 eff2)%bool) with true.
         2: { symmetry. apply andb_true_intro. rewrite Nat.eqb_refl. rewrite effect_list_eqb_refl. auto. }
         apply H5.
         
         Unshelve.
         all: try lia.
         ** intros. eapply H with (j := S j). lia.
            simpl. exact H6.
         ** exact H0.
         ** auto.
         ** auto.
       + simpl in H3. simpl.
         destruct (match_valuelist_to_patternlist vals l0). 1: congruence.
         epose (IHl id' eff2 id'' res eff3 vals env modules own_module i guard exp bindings _ _ _ _).
         destruct e1. destruct H2. exists (x + x0).
         apply bigger_clock_expr with (clock' := x + x0) in H2.
         apply bigger_clock_case with (clock' := x + x0) in H4.
         rewrite H4. unfold ffalse. simpl. auto.
         all: lia.
         Unshelve.
         ** intros. eapply H with (j := S j). lia.
            simpl. exact H5.
         ** exact H0.
         ** auto.
         ** auto.
Qed.

Lemma fbs_case_guard_exc_soundness :
forall {l id' eff2 vals env modules own_module i guard exp bindings ex},
(forall j : nat,
     j < i ->
     forall (gg ee : Expression) (bb : list (Var * Value)),
     match_clause vals l j = Some (gg, ee, bb) ->
     exists clock : nat,
       fbs_expr clock (add_bindings bb env) modules own_module id' gg eff2 = Result id' (inl [ffalse]) eff2) ->
match_clause vals l i = Some (guard, exp, bindings) ->
(exists clock : nat,
       fbs_expr clock (add_bindings bindings env) modules  own_module id' guard eff2 =
       Result id' (inr ex) eff2) ->
exists clock, fbs_case l env modules own_module id' eff2 vals (fbs_expr clock) = Result id' (inr ex) eff2.
Proof.
  induction l; intros.
  * inversion H0.
  * destruct i.
    - simpl in H0. destruct H1 as [? ?]. exists x.
      destruct a, p. simpl. destruct (match_valuelist_to_patternlist vals l0).
      + inversion H0. subst.
        rewrite H1. rewrite Nat.eqb_refl, list_eqb_refl.
        now simpl. apply effect_eqb_refl.
      + congruence.
    - simpl. destruct a, p.
      case_eq (match_clause vals ((l0, e0, e) :: l) 0); intros.
       + destruct p, p.
         pose (H 0 (Nat.lt_0_succ _) _ _ _ H2). simpl in H2. destruct e3.
         destruct (match_valuelist_to_patternlist vals l0). 2: congruence.
         inversion H3. subst.
         epose (IHl id' eff2 vals env modules own_module i guard exp bindings _ _ _ _).
         destruct e3.
         exists (x + x0).
         apply bigger_clock_expr with (clock' := x + x0) in H5.
         apply bigger_clock_case with (clock' := x + x0) in H4.
         rewrite H4. unfold ffalse. simpl.
         replace (((id' =? id') && list_eqb effect_eqb eff2 eff2)%bool) with true.
         2: { symmetry. apply andb_true_intro. rewrite Nat.eqb_refl. rewrite effect_list_eqb_refl. auto. }
         inversion H2. subst. rewrite H5.
         rewrite Nat.eqb_refl, list_eqb_refl. simpl. reflexivity.
         apply effect_eqb_refl.

       Unshelve.
         all: try lia.

         ** intros. eapply H with (j := S j). lia.
            simpl. exact H6.
         ** exact H0.
         ** auto.
       + simpl in H2. simpl.
         destruct (match_valuelist_to_patternlist vals l0). 1: congruence.
         epose (IHl id' eff2 vals env modules own_module i guard exp bindings _ _ _ _).
         destruct e1. destruct H2. exists x.
         exact H3.
         all: lia.
         Unshelve.
         ** intros. eapply H with (j := S j). lia.
            simpl. exact H4.
         ** exact H0.
         ** auto.
Qed.

Theorem fbs_case_if_clause_sound :
forall {l env modules own_module eff2 id' vals},
(forall j : nat,
     j < Datatypes.length l ->
     forall (gg ee : Expression) (bb : list (Var * Value)),
     match_clause vals l j = Some (gg, ee, bb) ->
     exists clock : nat,
       fbs_expr clock (add_bindings bb env) modules own_module id' gg eff2 = Result id' (inl [ffalse]) eff2)
->
exists clock, fbs_case l env modules own_module id' eff2 vals (fbs_expr clock) = Result id' (inr if_clause) eff2.
Proof.
  induction l; intros.
  * exists 0. auto.
  * destruct a, p.
    case_eq (match_clause vals ((l0, e0, e) :: l) 0); intros.
    - destruct p, p.
      pose (P := H 0 (Nat.lt_0_succ _) _ _ _ H0).
      simpl in H0.
      assert (exists clock : nat,
            fbs_expr clock (add_bindings l1 env) modules own_module id' e1 eff2 = Result id' (inl [ffalse]) eff2). 
      { auto. } clear P. simpl.
      destruct (match_valuelist_to_patternlist vals l0). 2: congruence.
      inversion H0. subst. destruct H1.
      epose (IHl env modules own_module eff2 id' vals _). destruct e.
      exists (x + x0).
      apply bigger_clock_expr with (clock' := x + x0) in H1.
      apply bigger_clock_case with (clock' := x + x0) in H2.
      rewrite H1, H2.
      replace (((id' =? id') && list_eqb effect_eqb eff2 eff2)%bool) with true.
      2: { symmetry. apply andb_true_intro. rewrite Nat.eqb_refl. rewrite effect_list_eqb_refl. auto. }
      simpl. auto.
      all: lia.
      Unshelve.
      + intros. eapply H with (j := S j). simpl. lia. simpl. exact H3.
    - simpl.
      simpl in H0. destruct (match_valuelist_to_patternlist vals l0). 1: congruence.
      epose (IHl env modules own_module eff2 id' vals _). destruct e1.
      exists x. rewrite H1. auto.
      Unshelve.
      + intros. eapply H with (j := S j). simpl. lia. simpl. exact H2.
Qed.

Theorem fbs_soundness :
(forall env modules own_module id exp eff id' res eff',
  | env, modules, own_module, id, exp, eff| -e> | id', res, eff' | 
  ->
  exists clock, fbs_expr clock env modules own_module id exp eff = Result id' res eff'
  )(* 
/\
(forall env id exp eff id' res eff',
  | env, id, exp, eff| -s> | id', res, eff' |
  ->
  exists clock, fbs_single clock env id exp eff = Result id' res eff')*) .
Proof.
  intros. induction H.
  * pose (P := fbs_expr_list_soundness H3 H H0 H1). destruct P.
    exists (S x). simpl. rewrite H4, H5. auto.
  * pose (P := fbs_expr_list_soundness_exception H4 IHeval_expr H H0 H1 H2). destruct P. 
    exists (S x). simpl. auto.
  * exists 1. auto.
  * exists 1. auto.
  * exists 1. simpl. rewrite H. auto.
  * exists 1. simpl. rewrite H. auto.
  * exists 1. simpl. rewrite H,  H0, H1, H2. auto.
  * exists 1. auto.
  * pose (P := fbs_expr_list_soundness H3 H H0 H1). destruct P.
    exists (S x). simpl. rewrite H4, H5, H6. auto.
  * destruct IHeval_expr1 as [cl1], IHeval_expr2 as [cl2].
    exists (S (cl1 + cl2)). simpl.
    apply bigger_clock_expr with (clock' := cl1 + cl2) in H1.
    apply bigger_clock_expr with (clock' := cl1 + cl2) in H2.
    rewrite H1, H2. 2-3: lia. auto.
  * destruct IHeval_expr1. pose (P := fbs_case_soundness H3 H1 IHeval_expr2 IHeval_expr3). destruct P.
    exists (S (x + x0)). simpl.
    apply bigger_clock_expr with (clock' := x + x0) in H6.
    apply bigger_clock_case with (clock' := x + x0) in H7.
    rewrite H6. assumption.
    all: lia.
  * destruct IHeval_expr1. destruct IHeval_expr2.
     epose (P := fbs_expr_list_soundness H5 _ _ _).
    Unshelve. 2-4: auto.
    destruct P.  exists (S (x + x0 + x1)). simpl.
    apply bigger_clock_expr with (clock' := x + x0 + x1) in H9.
    apply bigger_clock_expr with (clock' := x + x0 + x1) in H10.
    apply bigger_clock_list with (clock' := x + x0 + x1) in H11.
    rewrite H9. rewrite H10. rewrite H11. rewrite H6.
    rewrite H7 at 1. rewrite H7 at 1. simpl. rewrite H8. reflexivity.
    2: intros; apply clock_increase_expr; auto.
    all: lia.
  * destruct IHeval_expr1. destruct IHeval_expr2. destruct IHeval_expr3.
      epose (P := fbs_expr_list_soundness H5 _ _ _).
    Unshelve. 2-4: auto.
    destruct P.  exists (S (x + x0 + x1 + x2)). simpl.

    apply bigger_clock_expr with (clock' := x + x0 + x1 + x2) in H8.
    apply bigger_clock_expr with (clock' := x + x0 + x1 + x2) in H9.
    apply bigger_clock_expr with (clock' := x + x0 + x1 + x2) in H10.
    apply bigger_clock_list with (clock' := x + x0 + x1 + x2) in H11.
    rewrite H8. rewrite H9. rewrite H11.  rewrite H6.  auto.
    2: intros; apply clock_increase_expr; auto.
    all: lia. 
  * epose (P := fbs_expr_list_soundness H3 _ _ _).
    Unshelve. 2-4: auto.
    destruct P. exists (S x). simpl. rewrite H6.
    rewrite H4 at 1. rewrite H4 at 1. rewrite <- H5. simpl. auto.
  * destruct IHeval_expr1, IHeval_expr2.
    epose (P := fbs_expr_list_soundness H5 _ _ _).
    Unshelve. 2-4: auto.
    destruct P. exists (S (x + x0 + x1)). simpl.
    apply bigger_clock_expr with (clock' := x + x0 + x1) in H7.
    apply bigger_clock_expr with (clock' := x + x0 + x1) in H8.
    apply bigger_clock_list with (clock' := x + x0 + x1) in H9.
    rewrite H7. rewrite H9.
    apply Nat.eqb_eq in H1. rewrite H1. auto.
    2: intros; apply clock_increase_expr; auto.
    all: lia.
  * destruct IHeval_expr1, IHeval_expr2. exists (S (x + x0)). simpl.
    apply bigger_clock_expr with (clock' := x + x0) in H2.
    apply bigger_clock_expr with (clock' := x + x0) in H3.
    rewrite H2, H3. apply eq_sym, Nat.eqb_eq in H0. rewrite H0. auto.
    all: lia.
  * destruct IHeval_expr1, IHeval_expr2. exists (S (x + x0)). simpl.
    apply bigger_clock_expr with (clock' := x + x0) in H1.
    apply bigger_clock_expr with (clock' := x + x0) in H2.
    rewrite H1, H2. auto.
    all: lia.
  * destruct IHeval_expr. exists (S x). simpl. auto.
  * epose (P := fbs_expr_list_soundness H4 _ _ _). destruct P. exists (S x).
    simpl. unfold exps, vals in H9. rewrite H9.
    rewrite make_map_consistent. rewrite H5. simpl. rewrite H7, H8. rewrite H6. auto.
    lia.
  * destruct IHeval_expr. exists (S x). simpl. rewrite H0. auto.
  * destruct IHeval_expr1, IHeval_expr2. exists (S (x + x0)). simpl.
    apply bigger_clock_expr with (clock' := x + x0) in H1.
    apply bigger_clock_expr with (clock' := x + x0) in H2.
    rewrite H1, H2. auto.
    all: lia.
  * epose (P := fbs_expr_list_soundness_exception H4 IHeval_expr _ _ _ _).
    destruct P. exists (S x). simpl. rewrite H6. auto.
  * destruct IHeval_expr1, IHeval_expr2. exists (S (x + x0)). simpl.
    apply bigger_clock_expr with (clock' := x + x0) in H2.
    apply bigger_clock_expr with (clock' := x + x0) in H3.
    rewrite H2, H3. apply eq_sym, Nat.eqb_eq in H0. rewrite H0. auto.
    all: lia.
  * destruct IHeval_expr1, IHeval_expr2. exists (S (x + x0)). simpl. simpl in H2.
    apply bigger_clock_expr with (clock' := x + x0) in H1.
    apply bigger_clock_expr with (clock' := x + x0) in H2.
    rewrite H1, H2. auto.
    all: lia.
  * destruct IHeval_expr. exists (S x). simpl. rewrite H0. auto.
  * destruct IHeval_expr. pose (P := fbs_case_if_clause_sound H1).
    destruct P. exists (S (x + x0)).
    apply bigger_clock_expr with (clock' := x + x0) in H2.
    apply bigger_clock_case with (clock' := x + x0) in H3.
    simpl. rewrite H2, H3. auto. all: lia.
  * destruct IHeval_expr1. pose (P := fbs_case_guard_exc_soundness H3 H1 IHeval_expr2). destruct P.
    exists (S (x + x0)). simpl.
    apply bigger_clock_expr with (clock' := x + x0) in H5.
    apply bigger_clock_case with (clock' := x + x0) in H6.
    rewrite H5. assumption.
    all: lia.
  * destruct IHeval_expr1. destruct IHeval_expr2.
    epose (P := fbs_expr_list_soundness_exception H6 IHeval_expr3 _ _ _ _). 
    destruct P. exists (S x + x0 + x1). simpl.
    apply bigger_clock_expr with (clock' := x + x0 + x1) in H8.
    apply bigger_clock_expr with (clock' := x + x0 + x1) in H9.
    apply bigger_clock_list with (clock' := x + x0 + x1) in H10.
    rewrite H8, H9, H10. reflexivity.
    2: intros; apply clock_increase_expr; auto.
    all: lia.

  * destruct IHeval_expr. exists (S x). simpl. rewrite H0. auto.
  * destruct IHeval_expr1. destruct IHeval_expr2. 
    exists (S (x + x0)). 
    apply bigger_clock_expr with (clock' := x + x0) in H1.
    apply bigger_clock_expr with (clock' := x + x0) in H2.
    simpl. rewrite H1. rewrite H2. auto. all: lia.
  * destruct IHeval_expr1. destruct IHeval_expr2.
    epose (P := fbs_expr_list_soundness H5 _ _ _). destruct P.
    apply bigger_clock_expr with (clock' := x + x0 + x1) in H9.
    apply bigger_clock_expr with (clock' := x + x0 + x1) in H10.
    apply bigger_clock_list with (clock' := x + x0 + x1) in H11.
    exists (S (x + x0 + x1)).
    simpl. rewrite H9. rewrite H10. rewrite H11. subst.
    2,4,5: lia.
    - destruct v. 1,3,4,5,6: auto.
      destruct l. 
      -- congruence.
      -- auto.
    - intros. apply clock_increase_expr. auto.

  * destruct IHeval_expr1. destruct IHeval_expr2.
    epose (P := fbs_expr_list_soundness H5 _ _ _). destruct P.
    apply bigger_clock_expr with (clock' := x + x0 + x1) in H9.
    apply bigger_clock_expr with (clock' := x + x0 + x1) in H10.
    apply bigger_clock_list with (clock' := x + x0 + x1) in H11.
    exists (S (x + x0 + x1)).
    simpl. rewrite H9. rewrite H10. rewrite H11. subst.
    2,4,5: lia.
    - destruct v'. 1,3,4,5,6: auto.
      destruct l. 
      -- congruence. 
      -- auto.
    - intros. apply clock_increase_expr. auto.

  * epose (P := fbs_expr_list_soundness_exception H4 IHeval_expr _ _ _ _). 
    destruct P. exists (S x). simpl. rewrite H6. auto.
  * destruct IHeval_expr. exists (S x). simpl. rewrite H0. auto.
  * destruct IHeval_expr1.
    epose (P := fbs_expr_list_soundness_exception H5 IHeval_expr2 _ _ _ _).
    destruct P. exists (S (x + x0)). simpl.
    apply bigger_clock_expr with (clock' := x + x0) in H7.
    apply bigger_clock_list with (clock' := x + x0) in H8.
    rewrite H7, H8. auto.
    1,3: lia. intros. apply clock_increase_expr. auto.
  * destruct IHeval_expr.
    epose (P := fbs_expr_list_soundness H4 _ _ _). destruct P.
    exists (S (x + x0)). simpl.
    apply bigger_clock_expr with (clock' := x + x0) in H8.
    apply bigger_clock_list with (clock' := x + x0) in H9.
    rewrite H8, H9. destruct v; try congruence.
    1-5: rewrite H6, H7; auto.
    1,3: lia.
    intros. apply clock_increase_expr. auto.
  * destruct IHeval_expr.
    epose (P := fbs_expr_list_soundness H4 _ _ _). destruct P.
    exists (S (x + x0)). simpl.
    apply bigger_clock_expr with (clock' := x + x0) in H8.
    apply bigger_clock_list with (clock' := x + x0) in H9.
    rewrite H8, H9.
    apply Nat.eqb_neq in H5. rewrite H5. rewrite H6, H7. auto.
    1,3: lia.
    intros. apply clock_increase_expr. auto.
  * destruct IHeval_expr. exists (S x). simpl. rewrite H0. auto.
  * destruct IHeval_expr. exists (S x). simpl. rewrite H0. auto.
  * epose (P := fbs_expr_list_soundness_exception H5 IHeval_expr _ _ _ _).
    destruct P. exists (S x). simpl. unfold exps in H7.
    rewrite H7. auto.
  Unshelve.
  all: auto.
  - unfold exps, vals. rewrite length_make_map_exps, length_make_map_vals. lia. lia.
  - unfold exps. rewrite length_make_map_exps. auto.
  - unfold exps. rewrite length_make_map_exps. auto.
  - unfold exps. rewrite length_make_map_exps. lia.
  - unfold vals. case_eq (modulo_2 (i)); intros.
    + rewrite e in H1. rewrite length_make_map_vals.
      pose (n_div_2_mod_0 _ e). rewrite e0. lia. lia.
    + rewrite e in H1. rewrite length_make_map_vals2.
      pose (n_div_2_mod_1 _ e). rewrite e0. lia. lia.
Qed.

End Soundness.


Section Correctness.

Lemma list_expr_correct :
forall {l env modules own_module id eff id' vl eff' clock},
fbs_values (fbs_expr clock) env own_module modules id l eff = Result id' (inl vl) eff'
->
(
exists idl effl, 
  length l = length vl /\
  length l = length idl /\
  length l = length effl /\
  eff' = last effl eff /\
  id' = last idl id /\
  (forall i, i < length l ->
    fbs_expr clock env own_module modules (nth_def idl id 0 i) (nth i l ErrorExp) (nth_def effl eff [] i) =
      Result (nth_def idl id 0 (S i)) (inl [nth i vl ErrorValue]) (nth_def effl eff [] (S i))
  )
)
.
Proof.
  induction l; intros.
  * inversion H. subst. exists []. exists [].
    repeat (split; auto).
    intros. inversion H0.
  * simpl in H.
    case_eq (fbs_expr clock env own_module modules id a eff); intros. destruct res.
    - rewrite H0 in H.
      destruct v. congruence. destruct v0. 2: congruence.
      case_eq (fbs_values (fbs_expr clock) env own_module modules id0 l eff0); intros. destruct res.
         + rewrite H1 in H. inversion H. subst.
           pose (IHl _ _ _ _ _ _ _ _ _ H1). inversion e. inversion H2.
           destruct H3, H4, H5, H6, H7.
           exists (id0 :: x). exists (eff0 :: x0).
           split. 2: split. 3: split. 4: split. 5: split.
           1-3 : simpl; lia.
           ** rewrite last_element_equal with (def2 := eff) in H6. auto.
           ** rewrite last_element_equal with (def2 := id) in H7. auto.
           ** intros. destruct i.
             -- simpl. assumption.
             -- simpl in H9. 
                (* setoid failure for simple rewrite *)
                assert (i < length l). { lia. }
                apply H8. assumption.
         + rewrite H1 in H. discriminate.
         + rewrite H1 in H. discriminate.
         + rewrite H1 in H. discriminate.
    - rewrite H0 in H. discriminate.
    - rewrite H0 in H. discriminate.
    - rewrite H0 in H. discriminate.
Qed.

Lemma list_expr_exception_correct :
forall {l : list Expression} {env modules own_module id eff id' ex eff' clock},
fbs_values (fbs_expr clock) env modules own_module id l eff = Result id' (inr ex) eff'
->
(
exists vals idl effl, 
  length vals < length l /\
  length vals = length idl /\
  length vals = length effl /\
  (forall i, i < length vals ->
    fbs_expr clock env modules own_module (nth_def idl id 0 i) (nth i l ErrorExp) (nth_def effl eff [] i) =
      Result (nth_def idl id 0 (S i)) (inl [nth i vals ErrorValue]) (nth_def effl eff [] (S i))
  ) /\
  fbs_expr clock env modules own_module (last idl id) (nth (length vals) l ErrorExp) (last effl eff) = Result id' (inr ex) eff'
)
.
Proof.
  induction l; intros.
  * inversion H.
  * simpl in H.
    case_eq (fbs_expr clock env modules own_module id a eff); intros. destruct res.
    - rewrite H0 in H. destruct v. congruence. destruct v0. 2: congruence.
      case_eq (fbs_values (fbs_expr clock) env modules own_module id0 l eff0); intros. destruct res.
         + rewrite H1 in H. inversion H.
         + rewrite H1 in H. inversion H. subst.
           pose (IHl env modules own_module id0 eff0 id' ex eff' clock H1).
           destruct e. destruct H2, H2.
           destruct H2, H3, H4, H5.
           exists (v::x). exists (id0::x0). exists (eff0::x1).
           split. 2: split. 3: split. 4: split.
           all: try (simpl; lia).
           ** intros. destruct i.
             -- simpl. assumption.
             -- apply H5. simpl in H7. lia.
           ** rewrite last_element_equal with (def2 := id) in H6.
              rewrite last_element_equal with (def2 := eff) in H6.
              assumption.
         + rewrite H1 in H. congruence.
         + rewrite H1 in H. congruence.
    - rewrite H0 in H. inversion H. subst.
      exists []. exists []. exists [].
      split. 2: split. 3: split. 4: split.
      all: auto.
      + simpl. lia.
      + intros. inversion H1. 
    - rewrite H0 in H. discriminate.
    - rewrite H0 in H. discriminate.
Qed.

Lemma case_correctness l env modules own_module id0 eff0 v clock id' res eff' :
  fbs_case l env modules own_module id0 eff0 v  (fbs_expr clock) = Result id' res eff'
->
  (exists i guard exp bindings, i < length l /\
    match_clause v l i = Some (guard, exp, bindings) /\
    (forall j : nat, j < i -> 
      (forall gg ee bb, match_clause v l j = Some (gg, ee, bb) -> 
        (fbs_expr clock (add_bindings bb env) modules own_module id0 gg eff0 = Result id0 (inl [ffalse]) eff0 )
      )

    ) /\
    fbs_expr clock (add_bindings bindings env) modules own_module id0 guard eff0 = Result id0 (inl [ttrue]) eff0 /\
    fbs_expr clock (add_bindings bindings env) modules own_module id0 exp eff0 = Result id' res eff')
\/
  ((forall j : nat, j < length l -> 
      (forall gg ee bb, match_clause v l j = Some (gg, ee, bb) -> 
        (fbs_expr clock (add_bindings bb env) modules own_module id0 gg eff0 = Result id0 (inl [ffalse]) eff0 )))
  /\
  res = inr if_clause /\ id' = id0 /\ eff' = eff0
  )
\/
(exists i guard exp bindings, i < length l /\
    match_clause v l i = Some (guard, exp, bindings) /\
    (forall j : nat, j < i -> 
      (forall gg ee bb, match_clause v l j = Some (gg, ee, bb) -> 
        (fbs_expr clock (add_bindings bb env) modules own_module id0 gg eff0 = Result id0 (inl [ffalse]) eff0 )
      )

    ) /\
    fbs_expr clock (add_bindings bindings env) modules own_module id0 guard eff0 = Result id0 res eff0 /\ (exists ex, res = inr ex) /\ id0 = id' /\ eff' = eff0)
.
Proof.
  induction l; intros.
  * simpl in H. inversion H. subst.
    right. left. split. 2: auto. intros. inversion H0.
  * simpl in H. destruct a, p.
    case_eq (match_valuelist_to_patternlist v l0); intros; rewrite H0 in H.
    - case_eq (fbs_expr clock (add_bindings (match_valuelist_bind_patternlist v l0) env)
        modules own_module id0 e0 eff0); intros; rewrite H1 in H.
      + destruct res0. 2: {
          break_match_hyp. 2: congruence.
          inversion H; subst; clear H.
          right. right. exists 0. do 3 eexists.
          apply Bool.andb_true_iff in Heqb as [? ?].
          apply Nat.eqb_eq in H.
          apply effect_list_eqb_eq in H2.
          subst.
          repeat split.
          1: simpl; lia.
          1: { simpl. rewrite H0. reflexivity. }
          1: { intros. lia. }
          1: { now subst. }
          1: { now eexists. }
        }
        destruct v0. congruence. destruct v1. 2: congruence.
        case_eq (((id =? id0) && list_eqb effect_eqb eff0 eff)%bool); intros; rewrite H2 in H. 2: congruence.
        destruct v0; try congruence.
        destruct l1; try congruence.
        case_eq ((s =? "true")%string); intros; rewrite H3 in H.
        ** rewrite eqb_eq in H3. apply eq_sym, Bool.andb_true_eq in H2. destruct H2.
           symmetry in H2, H4. rewrite Nat.eqb_eq in H2.
           apply effect_list_eqb_eq in H4. subst.
           left. exists 0, e0, e, (match_valuelist_bind_patternlist v l0).
           split. 2: split. 3: split. 4: split.
           -- simpl. lia.
           -- simpl. rewrite H0. auto.
           -- intros. inversion H2.
           -- auto.
           -- auto.
        ** case_eq ((s =? "false")%string); intros; rewrite H4 in H. 2: congruence.
           rewrite eqb_eq in H4. subst.
           pose (P := IHl H). destruct P.
           -- destruct H4, H4, H4, H4, H4, H5, H6, H7.
              left. exists (S x), x0, x1, x2.
              split. 2: split. 3: split. 4: split.
              all: auto.
              ++ simpl. lia.
              ++ intros. destruct j.
                 *** subst. simpl in H10. rewrite H0 in H10. inversion H10. subst.
                     unfold ffalse.
                     apply eq_sym, Bool.andb_true_eq in H2. destruct H2.
                     symmetry in H2, H11. rewrite Nat.eqb_eq in H2.
                     apply effect_list_eqb_eq in H11. subst. exact H1.
                 *** apply Nat.succ_lt_mono in H9.
                     simpl in H10.
                     pose (P := H6 j H9 _ _ _ H10). auto.
          -- right.
             destruct H4 as [H4 | H4].
             2: {
               destruct H4 as [i [g [b [bs [? [? [? [? [[ex ?] [? ?]]]]]]]]]]. subst.
               right.
               apply Bool.andb_true_iff in H2. destruct H2.
               apply effect_list_eqb_eq in H8. subst.
               apply Nat.eqb_eq in H2. subst.
               exists (S i), g, b, bs. repeat split.
               1: simpl; lia.
               1: simpl; assumption.
               1: {
                 intros. destruct j.
                 * simpl in H8. rewrite H0 in H8. inversion H8. subst.
                   assumption.
                 * eapply (H6 j). lia. simpl in H8. eassumption.
               }
               2: now eexists.
               1: assumption.
             }
             left. destruct H4, H5, H6. subst. split. 2: split. 3: split.
             all: auto.
             ++ intros. destruct j.
                *** subst. simpl in H6. rewrite H0 in H6. inversion H6. subst.
                    apply eq_sym, Bool.andb_true_eq in H2. destruct H2.
                    symmetry in H2, H7. rewrite Nat.eqb_eq in H2.
                    apply effect_list_eqb_eq in H7. subst. exact H1.
                *** simpl in H5. apply Nat.succ_lt_mono in H5.
                     simpl in H6.
                     pose (P := H4 j H5 _ _ _ H6). auto.
      + congruence.
      + congruence.
    - pose (P := IHl H). destruct P.
      + destruct H1, H1, H1, H1, H1, H2, H3, H4.
        left. exists (S x), x0, x1, x2.
        split. 2: split. 3: split. 4: split.
        all: auto.
        ** simpl. lia.
        ** intros. destruct j.
           -- subst. simpl in H7. rewrite H0 in H7. congruence.
           -- apply Nat.succ_lt_mono in H6.
              simpl in H7.
              pose (P := H3 j H6 _ _ _ H7). auto.
     + right.
       destruct H1 as [H1 | H1].
       2: {
         destruct H1 as [i [g [b [bs [? [? [? [? [[ex ?] [? ?]]]]]]]]]]. subst.
         right.
         exists (S i), g, b, bs. repeat split.
         1: simpl; lia.
         1: simpl; assumption.
         1: {
           intros. destruct j.
           * simpl in H6. rewrite H0 in H6. inversion H6.
           * eapply (H3 j). lia. simpl in H6. eassumption.
         }
         2: now eexists.
         1: assumption.
       }
       left.
       destruct H1, H2, H3. subst. split. 2: split. 3: split.
       all: auto.
       ** intros. destruct j.
          -- subst. simpl in H3. rewrite H0 in H3. congruence.
          -- simpl in H2. apply Nat.succ_lt_mono in H2.
             simpl in H3.
             pose (P := H1 j H2 _ _ _ H3). auto.
Qed.


Theorem fbs_expr_correctness :
(forall clock {env modules own_module id exp eff id' res eff'},
  fbs_expr clock env modules own_module id exp eff = Result id' res eff'
 ->
  | env, modules, own_module, id, exp, eff| -e> | id', res, eff' |).
Proof.
  induction clock; intros.
  * inversion H.
  * destruct exp; simpl in H.
    - destruct res.
      + apply list_expr_correct in H.  destruct H, H, H, H0, H1, H2, H3. 
      (* CONTINUE *)
        eapply eval_values with (vals := v) (eff := x0) (ids := x); auto. (* intros.
        eapply IHclock in H4. exact H4. exact H5. *)  
      + apply list_expr_exception_correct in H. destruct H, H, H, H, H0, H1, H2.
        eapply eval_values_ex with (vals := x) (eff := x1) (ids := x0); auto. auto.
        (*intros. eapply IHclock in H2. exact H2. exact H4. eapply IHclock in H3. exact H3. *)
    - inversion H. apply eval_nil.
    - inversion H. apply eval_lit.
    - case_eq (get_value env (inl v)); intros; rewrite H0 in H.
      2: congruence. inversion H. apply eval_var. auto.
    - case_eq (get_value env (inr f)).
      + intros. rewrite H0 in H.
        inversion H. apply eval_funid. auto.
      + intros. rewrite H0 in H. destruct get_own_modfunc eqn:MOD.
        ++ inversion H. eapply eval_funid_module. all: auto. exact MOD.
        ++ congruence.
    - inversion H. apply eval_fun.
    - case_eq (fbs_expr clock env modules own_module id exp2 eff); intros; rewrite H0 in H.
      destruct res0. destruct v. congruence. destruct v0. 2: congruence.
      + apply IHclock in H0.
        case_eq (fbs_expr clock env modules own_module id0 exp1 eff0); intros; rewrite H1 in H.
        destruct res0. destruct v0. congruence. destruct v1. 2: congruence.
        ** apply IHclock in H1. inversion H. subst.
           eapply eval_cons. exact H0. exact H1.
        ** apply IHclock in H1. inversion H. subst.
           eapply eval_cons_hd_ex. exact H0. exact H1.
        ** congruence.
        ** congruence.
      + eapply IHclock in H0. inversion H. subst.
        eapply eval_cons_tl_ex. exact H0.
      + congruence.
      + congruence.
    - case_eq (fbs_values (fbs_expr clock) env modules own_module id l eff); intros; rewrite H0 in H.
      destruct res0.
      + apply list_expr_correct in H0. destruct H0, H0, H0, H1, H2, H3, H4.
        inversion H. subst.
        eapply eval_tuple with (vals := v) (eff := x0) (ids := x); auto.
        (*intros. eapply IHclock in H5. exact H5. exact H3.*)
      + apply list_expr_exception_correct in H0. destruct H0, H0, H0, H0, H1, H2, H3.
        inversion H. subst.
        eapply eval_tuple_ex with (vals := x) (eff := x1) (ids := x0); auto. auto.
        (*intros. eapply IHclock in H3. exact H3. exact H5. eapply IHclock in H4. exact H4. *)
      + congruence.
      + congruence.
    - case_eq (fbs_expr clock env modules own_module id exp1 eff).
      + intros. rewrite H0 in H. destruct res0.
        ** destruct v; try congruence.
           destruct v0; try congruence.
           case_eq (fbs_expr clock env modules own_module id0 exp2 eff0 ).
           -- intros. rewrite H1 in H.
              destruct res0.
              ++ destruct v0; try congruence.
                 destruct v1; try congruence.
                 case_eq (fbs_values (fbs_expr clock) env modules own_module id1 l eff1).
                 *** intros. rewrite H2 in H.
                     destruct res0.
                     --- destruct v. 
                         +++ apply IHclock in H0, H1. inversion H. subst.
                             apply list_expr_correct in H2.
                             destruct H2, H2, H2, H3, H4, H5, H6.
                             eapply eval_call_mexp_badarg_ex with
                             (params:= l) (fexp:= exp2) (vals:=v1) (eff:=x0) (ids:=x) (id''':= id') (eff4:= eff'); auto.
                             exact H0. exact H1. congruence.
                         +++ destruct l0.
                             **** destruct v0.
                                   ---- apply IHclock in H0, H1. inversion H. subst.
                                        apply list_expr_correct in H2.
                                        destruct H2, H2, H2, H3, H4, H5, H6.
                                        eapply eval_call_fexp_badarg_ex with
                                        (params:= l) (fexp:= exp2) (vals:=v1) (eff:=x0) (ids:=x) (id''':= id') (eff4:= eff');  auto.
                                        exact H0. exact H1. congruence.   
                                   ---- destruct l0. 
                                        ++++ destruct get_modfunc eqn:MOD. 
                                             ***** apply IHclock in H0, H1, H.
                                                   apply list_expr_correct in H2.
                                                   destruct H2, H2, H2, H3, H4, H5, H6.
                                                   rewrite H5, H6 in H.
                                                   eapply eval_call_module with (vals := v1) (eff := x0) (ids := x); auto.
                                                   exact H0. exact H1.
                                                   exact MOD. exact H.
                                             ***** apply IHclock in H0, H1. inversion H. subst.
                                                   apply list_expr_correct in H2.
                                                   destruct H2, H2, H2, H3, H4, H5, H6.
                                                   eapply eval_call with (vals := v1) (eff := x0) (ids := x); auto.
                                                   exact H0. exact H1. auto.
                                                   rewrite <- surjective_pairing.
                                                   rewrite H5. auto. 
                                        ++++ apply IHclock in H0, H1. inversion H. subst.
                                             apply list_expr_correct in H2.
                                             destruct H2, H2, H2, H3, H4, H5, H6.
                                             eapply eval_call_fexp_badarg_ex with
                                             (params:= l) (fexp:= exp2) (vals:=v1) (eff:=x1) (ids:=x0) (id''':= id') (eff4:= eff');  auto.
                                             exact H0. exact H1. congruence.
                                   ---- apply IHclock in H0, H1. inversion H. subst.
                                        apply list_expr_correct in H2.
                                        destruct H2, H2, H2, H3, H4, H5, H6.
                                        eapply eval_call_fexp_badarg_ex with
                                        (params:= l) (fexp:= exp2) (vals:=v1) (eff:=x0) (ids:=x) (id''':= id') (eff4:= eff');  auto.
                                        exact H0. exact H1. congruence.
                                   ---- apply IHclock in H0, H1. inversion H. subst.
                                        apply list_expr_correct in H2.
                                        destruct H2, H2, H2, H3, H4, H5, H6.
                                        eapply eval_call_fexp_badarg_ex with
                                        (params:= l) (fexp:= exp2) (vals:=v1) (eff:=x0) (ids:=x) (id''':= id') (eff4:= eff');  auto.
                                        exact H0. exact H1. congruence.
                                   ---- apply IHclock in H0, H1. inversion H. subst.
                                        apply list_expr_correct in H2.
                                        destruct H2, H2, H2, H3, H4, H5, H6.
                                        eapply eval_call_fexp_badarg_ex with
                                        (params:= l) (fexp:= exp2) (vals:=v1) (eff:=x0) (ids:=x) (id''':= id') (eff4:= eff');  auto.
                                        exact H0. exact H1. congruence.
                                   ---- apply IHclock in H0, H1. inversion H. subst.
                                        apply list_expr_correct in H2.
                                        destruct H2, H2, H2, H3, H4, H5, H6.
                                        eapply eval_call_fexp_badarg_ex with
                                        (params:= l) (fexp:= exp2) (vals:=v1) (eff:=x0) (ids:=x) (id''':= id') (eff4:= eff');  auto.
                                        exact H0. exact H1. congruence.
                              **** apply IHclock in H0, H1. inversion H. subst.
                                   apply list_expr_correct in H2.
                                   destruct H2, H2, H2, H3, H4, H5, H6.
                                   eapply eval_call_mexp_badarg_ex with
                                   (params:= l) (fexp:= exp2) (vals:=v1) (eff:=x1) (ids:=x0) (id''':= id') (eff4:= eff'); auto.
                                  exact H0. exact H1. congruence.
                         +++ apply IHclock in H0, H1. inversion H. subst.
                             apply list_expr_correct in H2.
                             destruct H2, H2, H2, H3, H4, H5, H6.
                             eapply eval_call_mexp_badarg_ex with
                             (params:= l) (fexp:= exp2) (vals:=v1) (eff:=x0) (ids:=x) (id''':= id') (eff4:= eff'); auto.
                             exact H0. exact H1. congruence.
                         +++ apply IHclock in H0, H1. inversion H. subst.
                             apply list_expr_correct in H2.
                             destruct H2, H2, H2, H3, H4, H5, H6.
                             eapply eval_call_mexp_badarg_ex with
                             (params:= l) (fexp:= exp2) (vals:=v1) (eff:=x0) (ids:=x) (id''':= id') (eff4:= eff'); auto.
                             exact H0. exact H1. congruence.
                         +++ apply IHclock in H0, H1. inversion H. subst.
                             apply list_expr_correct in H2.
                             destruct H2, H2, H2, H3, H4, H5, H6.
                             eapply eval_call_mexp_badarg_ex with
                             (params:= l) (fexp:= exp2) (vals:=v1) (eff:=x0) (ids:=x) (id''':= id') (eff4:= eff'); auto.
                             exact H0. exact H1. congruence.
                         +++ apply IHclock in H0, H1. inversion H. subst.
                             apply list_expr_correct in H2.
                             destruct H2, H2, H2, H3, H4, H5, H6.
                             eapply eval_call_mexp_badarg_ex with
                             (params:= l) (fexp:= exp2) (vals:=v1) (eff:=x0) (ids:=x) (id''':= id') (eff4:= eff'); auto.
                             exact H0. exact H1. congruence.
                     --- apply IHclock in H0, H1. inversion H. subst.
                         apply list_expr_exception_correct in H2.
                         destruct H2, H2, H2, H2, H3, H4, H5.
                         eapply eval_call_ex with (vals := x) (eff := x1) (ids := x0); auto.
                         auto. exact H0. exact H1.

                *** intros; rewrite H2 in H; congruence.
                *** intros; rewrite H2 in H; congruence.
             ++ apply IHclock in H0, H1. inversion H. subst.
                eapply eval_call_fexp_ex. exact H0. exact H1.
          -- intros. rewrite H1 in H. congruence.
          -- intros. rewrite H1 in H. congruence. 
       ** apply IHclock in H0. inversion H. subst.
              eapply eval_call_mexp_ex with (params:= l) (fexp:= exp2)  in H0. auto.
      + intros. rewrite H0 in H. congruence.
      + intros. rewrite H0 in H. congruence. 
    - case_eq (fbs_values (fbs_expr clock) env modules own_module id l eff); intros; rewrite H0 in H.
      destruct res0.
      + apply list_expr_correct in H0. destruct H0, H0, H0, H1, H2, H3, H4.
        inversion H. subst.
        eapply eval_primop with (vals := v) (eff := x0) (ids := x); auto.
        (*intros. eapply IHclock in H5. exact H5. exact H3.*)
        ** rewrite <- surjective_pairing. auto.
      + apply list_expr_exception_correct in H0. destruct H0, H0, H0, H0, H1, H2, H3.
        inversion H. subst.
        eapply eval_primop_ex with (vals := x) (eff := x1) (ids := x0); auto. auto.
        (*intros. eapply IHclock in H3. exact H3. exact H5. eapply IHclock in H4. exact H4. *)
      + congruence.
      + congruence.
    - case_eq (fbs_expr clock env modules own_module id exp eff); intros; rewrite H0 in H.
      destruct res0. destruct v. congruence. destruct v0. 2: congruence.
      + apply IHclock in H0.
        case_eq (fbs_values (fbs_expr clock) env modules own_module id0 l eff0); intros; rewrite H1 in H.
        destruct res0; try (apply list_expr_correct in H1; destruct H1, H1, H1, H2, H3, H4, H5).
        ** destruct v; inversion H; subst.
          -- eapply eval_app_badfun_ex with (vals := v0) (eff := x0) (ids := x);auto.
              auto. (*exact H0. intros. eapply IHclock in H6. exact H6. exact H4.*)
              intros; try (pose (P := H6 j H4); apply fbs_expr_correctness in P; exact P). 
              congruence.
          -- eapply eval_app_badfun_ex with (vals := v0) (eff := x0) (ids := x);auto.
              auto. (*exact H0. intros. eapply IHclock in H6. exact H6. exact H4.*)
              intros; try (pose (P := H6 j H4); apply fbs_expr_correctness in P; exact P).
              congruence.
          -- case_eq (Datatypes.length vl =? Datatypes.length v0); intros; rewrite H4 in *.
            ++ apply Nat.eqb_eq in H4.
              eapply eval_app with (vals := v0) (eff := x0) (ids := x); auto.
              *** exact H0.
              *** auto.
              (****  intros. eapply IHclock in H6. exact H6. exact H5.*)
              *** apply IHclock in H8. exact H8.  
            ++ apply Nat.eqb_neq in H4. inversion H. subst.
              eapply eval_app_badarity_ex with (vals := v0) (eff := x0) (ids := x); auto.
              *** exact H0.
              (**** intros. eapply IHclock in H6. exact H6. auto.*)
 
          -- eapply eval_app_badfun_ex with (vals := v0) (eff := x0) (ids := x);auto.
              (*exact H0. intros. eapply IHclock in H6. exact H6. exact H4.*)
              intros; try (pose (P := H6 j H4); apply fbs_expr_correctness in P; exact P).
              auto.
              congruence.
          -- eapply eval_app_badfun_ex with (vals := v0) (eff := x0) (ids := x);auto.
              (*exact H0. intros. eapply IHclock in H6. exact H6. exact H4.*)
              intros; try (pose (P := H6 j H4); apply fbs_expr_correctness in P; exact P).
              auto.
              congruence.
          -- eapply eval_app_badfun_ex with (vals := v0) (eff := x0) (ids := x);auto.
          (*exact H0. intros. eapply IHclock in H6. exact H6. exact H4.*)
          intros; try (pose (P := H6 j H4); apply fbs_expr_correctness in P; exact P).
          auto.
          congruence.
        ** apply list_expr_exception_correct in H1. destruct H1, H1, H1, H1, H2, H3, H4.
           apply IHclock in H5. inversion H. subst.
           eapply eval_app_param_ex with (vals := x) (eff := x1) (ids := x0); auto.
           *** exact H1.
           *** exact H0.
        ** congruence.
        ** congruence.
      + apply IHclock in H0. inversion H. subst.
        eapply eval_app_closure_ex. auto.
      + congruence.
      + congruence.
    - case_eq (fbs_expr clock env modules own_module id exp eff); intros; rewrite H0 in H.
      destruct res0.
      + apply IHclock in H0.
        apply case_correctness in H. destruct H as [H | [H | H]].
        ** destruct H, H, H, H, H, H1, H2, H3.
           eapply eval_case with (i := x).
           -- exact H0.
           -- auto.
           -- exact H1.
           -- intros. pose (P := H2 j H5 gg ee bb H6). apply IHclock in P. exact P.
           -- apply IHclock in H3. auto.
           -- apply IHclock in H4. auto.
        ** destruct H, H1, H2. subst. eapply eval_case_clause_ex.
           -- exact H0.
           -- intros. pose (P := H j H1 gg ee bb H2). apply IHclock in P. auto.
        ** destruct H, H, H, H, H, H1, H2, H3, H4, H5, H4. subst.
           eapply IHclock in H3.
           eapply eval_case_guard_ex; try eassumption.
           -- intros. eapply H2 in H5.
              now apply IHclock in H5.
              lia.
      + apply IHclock in H0. inversion H. subst.
        apply eval_case_pat_ex. auto.
      + congruence.
      + congruence.
    - case_eq (fbs_expr clock env modules own_module id exp1 eff); intros; rewrite H0 in H.
      destruct res0.
      + case_eq (Datatypes.length v =? Datatypes.length l); intros; rewrite H1 in H.
        ** apply Nat.eqb_eq in H1. apply IHclock in H.
           apply IHclock in H0.
           eapply eval_let.
           -- exact H0.
           -- auto.
           -- exact H.
        ** congruence.
      + inversion H. subst.
        apply eval_let_ex. apply IHclock in H0. auto.
      + congruence.
      + congruence.
    - case_eq (fbs_expr clock env modules own_module id exp1 eff); intros; rewrite H0 in H.
      destruct res0. destruct v. congruence. destruct v0. 2: congruence.
      + apply IHclock in H. apply IHclock in H0.
        eapply eval_seq. exact H0. exact H.
      + inversion H. subst.
        apply eval_seq_ex. apply IHclock in H0. auto.
      + congruence.
      + congruence.
    - eapply eval_letrec. apply IHclock in H. auto.
    - case_eq (fbs_values (fbs_expr clock) env modules own_module id (make_map_exps l) eff); intros; rewrite H0 in H.
      destruct res0.
      + apply list_expr_correct in H0. destruct H0, H0, H0, H1, H2, H3, H4.
        case_eq (make_map_vals_inverse v); intros; rewrite H6 in H. 2: congruence.
        destruct p. inversion H. subst.
        pose (P := make_map_inverse_length _ _ _ H6). destruct P.
        eapply eval_map with (ids := x) (eff := x0) (kvals := l0) (vvals := l1); auto.
        ** rewrite length_make_map_exps in H0. lia.
        ** rewrite length_make_map_exps in H0. lia.
        ** rewrite length_make_map_exps in H2. lia.
        ** rewrite length_make_map_exps in H1. lia.
        ** intros. pose (P := H5 i H7). apply IHclock in P.
           apply make_map_inverse_relation in H6. subst. exact P.
        ** apply surjective_pairing.
     + apply list_expr_exception_correct in H0. destruct H0, H0, H0, H0, H1, H2, H3.
        inversion H. subst.
        apply IHclock in H4.
        assert (exists kvals vvals, x = make_map_vals kvals vvals /\ length kvals = length vvals + length x mod 2). { apply map_correcness. }
        destruct H5, H5, H5.
        eapply eval_map_ex with (ids := x0) (eff := x1) (kvals := x2) (vvals := x3); auto.
        ** rewrite length_make_map_exps in H0. lia.
        ** pose (modulo_2 (length x)). destruct o.
           -- rewrite H7 in H6. rewrite Nat.add_0_r in H6. pose (length_make_map_vals _ _ H6).
              subst. rewrite H6 in e0. pose (n_div_2_mod_0 _ H7). rewrite <- H2. lia.
           -- rewrite H7 in H6. rewrite Nat.add_1_r in H6. pose (length_make_map_vals2 _ _ H6).
              subst. rewrite <- H2. pose (n_div_2_mod_1 _ H7). lia.
        ** rewrite <- H2. pose (modulo_2 (length x)). destruct o.
           -- rewrite H7 in *. rewrite Nat.add_0_r in *. pose (length_make_map_vals _ _ H6).
              pose (n_div_2_mod_0 _ H7). subst. lia.
           -- rewrite H7 in *. rewrite Nat.add_1_r in *. pose (length_make_map_vals2 _ _ H6).
              pose (n_div_2_mod_1 _ H7). subst. lia.
        ** lia.
        ** intros. rewrite <- H2 in H7. pose (P := H3 j H7). rewrite <- H5. apply IHclock in P. auto.
        ** rewrite <- H2. auto.
      + congruence.
      + congruence.
    - case_eq (fbs_expr clock env modules own_module id exp1 eff); intros; rewrite H0 in H.
      destruct res0.
      + case_eq (Datatypes.length v =? Datatypes.length vl1); intros; rewrite H1 in H.
        2: congruence.
        apply Nat.eqb_eq in H1.
        apply IHclock in H0. apply IHclock in H.
        eapply eval_try.
        *** exact H0.
        *** auto.
        *** exact H.
      + apply IHclock in H0.
        eapply eval_catch.
        *** exact H0.
        *** apply IHclock in H. exact H.
      + congruence.
      + congruence.
Qed. 

End Correctness.
