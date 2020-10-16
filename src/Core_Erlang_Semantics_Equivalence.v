Require Core_Erlang_Proofs.
Require Core_Erlang_Functional_Big_Step.


Export Core_Erlang_Proofs.Proofs.
Export Core_Erlang_Functional_Big_Step.Functional_Big_Step.

Import List.
Import ListNotations.

Lemma restrict_soundness :
forall {A : Type} {env exps a v} {id : nat} {id' eff' eff1 x x0 x1 defexp defval} {f : nat -> Environment -> nat -> A -> SideEffectList -> ResultType},
(forall i : nat,
    i < Datatypes.length (a :: exps) ->
    exists clock : nat,
      f clock env (nth_def (id' :: x1) id 0 i) (nth i (a :: exps) defexp)
        (nth_def (eff' :: x0) eff1 [] i) =
      Result (nth_def (id' :: x1) id 0 (S i)) (inl [nth i (v :: x) defval])
        (nth_def (eff' :: x0) eff1 [] (S i)))
->
(forall i : nat,
    i < Datatypes.length (exps) ->
    exists clock : nat,
      f clock env (nth_def x1 id' 0 i) (nth i exps defexp)
        (nth_def x0 eff' [] i) =
      Result (nth_def x1 id' 0 (S i)) (inl [nth i x defval])
        (nth_def x0 eff' [] (S i))).
Proof.
  intros.
  assert (S i < S (length exps)) as A1.
  { simpl. lia. } pose (E := H (S i) A1). 
  destruct E. simpl nth_def in H1. simpl nth in H. exists x2. simpl. exact H1.
Qed.

Lemma fbs_single_list_soundness :
forall {exps vals eff ids env id eff1},
  (forall i : nat,
    i < Datatypes.length exps ->
    exists clock : nat,
      fbs_single clock env (nth_def ids id 0 i) (nth i exps ErrorExp) (nth_def eff eff1 [] i) =
      Result (nth_def ids id 0 (S i)) (inl [nth i vals ErrorValue])
        (nth_def eff eff1 [] (S i))) ->
  length exps = length vals ->
  length exps = length eff ->
  length exps = length ids
->
  exists clock, fbs_values (fbs_single clock) env id exps eff1 = Result (last ids id) (inl vals) (last eff eff1).
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

    epose (P2 := IHexps _ _ _ _ _ _ (restrict_soundness H) _ _ _).
    Unshelve.
    2-4: auto.
    destruct P2 as [cl2].
    exists (cl1 + cl2).
    simpl fbs_values.
    apply bigger_clock_single with (clock' := cl1 + cl2) in H3. 2: lia.
    apply bigger_clock_list with (clock' := cl1 + cl2) in H7. 
      2: lia. 2: intros; apply clock_increase_single; auto.
    rewrite H3, H7.
    rewrite last_element_equal with (def2 := id).
    rewrite last_element_equal with (def2 := eff1). auto.
Qed.

Lemma fbs_single_list_soundness_exception :
forall {exps vals eff ids env id eff1 id' ex eff' i},
(forall j : nat,
    j < i ->
    exists clock : nat,
      fbs_single clock env (nth_def ids id 0 j) (nth j exps ErrorExp) (nth_def eff eff1 [] j) =
      Result (nth_def ids id 0 (S j)) (inl [nth j vals ErrorValue])
        (nth_def eff eff1 [] (S j)))
->
(exists clock : nat,
       fbs_single clock env (last ids id) (nth i exps ErrorExp) (last eff eff1) =
       Result id' (inr ex) eff')
->
i < Datatypes.length exps ->
Datatypes.length vals = i ->
Datatypes.length eff = i ->
Datatypes.length ids = i
->
  exists clock, fbs_values (fbs_single clock) env id exps eff1 = Result id' (inr ex) eff'.
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
      simpl in H1. apply Lt.lt_S_n in H1.
      simpl in H2, H3, H4.
      apply eq_add_S in H2. apply eq_add_S in H3. apply eq_add_S in H4.
      rewrite <- last_element_equal, <- last_element_equal in H0.
      epose (P2 := IHexps _ _ _ _ _ _ _ _ _ _ _ H0 H1 H2 H3 H4).
      destruct P2. exists (x2 + x3).
      simpl.
      apply bigger_clock_single with (clock' := x2 + x3) in H5.
      apply bigger_clock_list with (clock' := x2 + x3) in H6.
      rewrite H5, H6. auto.
      1, 3: lia.
      intros. apply clock_increase_single. auto.
  Unshelve.
  intros. epose (H (S j) _). exact e.
  Unshelve.
  lia.
Qed.

Lemma fbs_expr_list_soundness :
forall {exps : list Expression} {vals eff ids env id eff1},
(forall i : nat,
    i < Datatypes.length exps ->
    exists clock : nat,
      fbs_expr clock env (nth_def ids id 0 i) (nth i exps ErrorExp) (nth_def eff eff1 [] i) =
      Result (nth_def ids id 0 (S i)) (inl [nth i vals ErrorValue])
        (nth_def eff eff1 [] (S i))) ->
  length exps = length vals ->
  length exps = length eff ->
  length exps = length ids
->
  exists clock, fbs_values (fbs_expr clock) env id exps eff1 = Result (last ids id) (inl vals) (last eff eff1).
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

    epose (P2 := IHexps _ _ _ _ _ _ (restrict_soundness H) _ _ _).
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
forall {exps : list Expression} {vals eff ids env id eff1 id' ex eff' i},
(forall j : nat,
    j < i ->
    exists clock : nat,
      fbs_expr clock env (nth_def ids id 0 j) (nth j exps ErrorExp) (nth_def eff eff1 [] j) =
      Result (nth_def ids id 0 (S j)) (inl [nth j vals ErrorValue])
        (nth_def eff eff1 [] (S j)))
->
(exists clock : nat,
       fbs_expr clock env (last ids id) (nth i exps ErrorExp) (last eff eff1) =
       Result id' (inr ex) eff')
->
i < Datatypes.length exps ->
Datatypes.length vals = i ->
Datatypes.length eff = i ->
Datatypes.length ids = i
->
  exists clock, fbs_values (fbs_expr clock) env id exps eff1 = Result id' (inr ex) eff'.
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
      simpl in H1. apply Lt.lt_S_n in H1.
      simpl in H2, H3, H4.
      apply eq_add_S in H2. apply eq_add_S in H3. apply eq_add_S in H4.
      rewrite <- last_element_equal, <- last_element_equal in H0.
      epose (P2 := IHexps _ _ _ _ _ _ _ _ _ _ _ H0 H1 H2 H3 H4).
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

Theorem fbs_soundness :
(forall env id exp eff id' res eff',
  | env, id, exp, eff| -e> | id', res, eff' | 
  ->
  exists clock, fbs_expr clock env id exp eff = Result id' res eff'
  )
/\
(forall env id exp eff id' res eff',
  | env, id, exp, eff| -s> | id', res, eff' |
  ->
  exists clock, fbs_single clock env id exp eff = Result id' res eff').
Proof.
  apply eval_ind; intros.
  * pose (P := fbs_single_list_soundness H e e0 e1). destruct P.
    exists (S x). simpl. rewrite H0, e3, e4. auto.
  * pose (P := fbs_single_list_soundness_exception H H0 l e e0 e1). destruct P. exists (S x). simpl. auto.
  * destruct H. exists (S x). auto.
  * exists 1. auto.
  * exists 1. auto.
  * exists 1. simpl. rewrite e. auto.
  * exists 1. simpl. rewrite e. auto.
  * exists 1. auto.
  * pose (P := fbs_expr_list_soundness H e e0 e1). destruct P.
    exists (S x). simpl. rewrite H0, e3, e4. auto.
  * destruct H as [cl1], H0 as [cl2].
    exists (S (cl1 + cl2)). simpl.
    apply bigger_clock_expr with (clock' := cl1 + cl2) in H.
    apply bigger_clock_expr with (clock' := cl1 + cl2) in H0.
    rewrite H, H0. 2-3: lia. auto.
  * admit.
  * epose (P := fbs_expr_list_soundness H _ _ _).
    Unshelve. 2-4: auto.
    destruct P. exists (S x). simpl. rewrite H0.
    rewrite e3 at 1. rewrite e3 at 1. rewrite <- e4. simpl. auto.
  * epose (P := fbs_expr_list_soundness H _ _ _).
    Unshelve. 2-4: auto.
    destruct P. exists (S x). simpl. rewrite H0.
    rewrite e3 at 1. rewrite e3 at 1. rewrite <- e4. simpl. auto.
  * destruct H, H1.
    epose (P := fbs_expr_list_soundness H0 _ _ _).
    Unshelve. 2-4: auto.
    destruct P. exists (S (x + x0 + x1)). simpl.
    apply bigger_clock_expr with (clock' := x + x0 + x1) in H.
    apply bigger_clock_expr with (clock' := x + x0 + x1) in H1.
    apply bigger_clock_list with (clock' := x + x0 + x1) in H2.
    rewrite H. rewrite H2.
    apply Nat.eqb_eq in e1. rewrite e1. auto.
    2: intros; apply clock_increase_expr; auto.
    all: lia.
  * destruct H0, H. exists (S (x + x0)). simpl.
    apply bigger_clock_expr with (clock' := x + x0) in H.
    apply bigger_clock_expr with (clock' := x + x0) in H0.
    rewrite H, H0. apply eq_sym, Nat.eqb_eq in e0. rewrite e0. auto.
    all: lia.
  * destruct H0, H. exists (S (x + x0)). simpl.
    apply bigger_clock_expr with (clock' := x + x0) in H.
    apply bigger_clock_expr with (clock' := x + x0) in H0.
    rewrite H, H0. auto.
    all: lia.
  * destruct H. exists (S x). simpl. auto.
  * epose (P := fbs_expr_list_soundness H _ _ _). destruct P. exists (S x).
    simpl. unfold exps, vals in H0. rewrite H0.
    rewrite make_map_consistent. rewrite <- e5, e4. simpl. rewrite e6, e7. auto.
    lia.
  * destruct H. exists (S x). simpl. rewrite H. auto.
  * destruct H, H0. exists (S (x + x0)). simpl.
    apply bigger_clock_expr with (clock' := x + x0) in H.
    apply bigger_clock_expr with (clock' := x + x0) in H0.
    rewrite H, H0. auto.
    all: lia.
  * epose (P := fbs_expr_list_soundness_exception H H0 _ _ _ _).
    destruct P. exists (S x). simpl. rewrite H1. auto.
  * destruct H, H0. exists (S (x + x0)). simpl.
    apply bigger_clock_expr with (clock' := x + x0) in H.
    apply bigger_clock_expr with (clock' := x + x0) in H0.
    rewrite H, H0. apply eq_sym, Nat.eqb_eq in e0. rewrite e0. auto.
    all: lia.
  * destruct H, H0. exists (S (x + x0)). simpl. simpl in H0.
    apply bigger_clock_expr with (clock' := x + x0) in H.
    apply bigger_clock_expr with (clock' := x + x0) in H0.
    rewrite H, H0. auto.
    all: lia.
  * destruct H. exists (S x). simpl. rewrite H. auto.
  * admit.
  * epose (P := fbs_expr_list_soundness_exception H H0 _ _ _ _). 
    destruct P. exists (S x). simpl. rewrite H1. auto.
  * epose (P := fbs_expr_list_soundness_exception H H0 _ _ _ _). 
    destruct P. exists (S x). simpl. rewrite H1. auto.
  * destruct H. exists (S x). simpl. rewrite H. auto.
  * destruct H.
    epose (P := fbs_expr_list_soundness_exception H0 H1 _ _ _ _).
    destruct P. exists (S (x + x0)). simpl.
    apply bigger_clock_expr with (clock' := x + x0) in H.
    apply bigger_clock_list with (clock' := x + x0) in H2.
    rewrite H, H2. auto.
    1,3: lia. intros. apply clock_increase_expr. auto.
  * destruct H.
    epose (P := fbs_expr_list_soundness H0 _ _ _). destruct P.
    exists (S (x + x0)). simpl.
    apply bigger_clock_expr with (clock' := x + x0) in H.
    apply bigger_clock_list with (clock' := x + x0) in H1.
    rewrite H, H1. destruct v; try congruence.
    1-5: rewrite e4, e5; auto.
    1,3: lia.
    intros. apply clock_increase_expr. auto.
  * destruct H.
    epose (P := fbs_expr_list_soundness H0 _ _ _). destruct P.
    exists (S (x + x0)). simpl.
    apply bigger_clock_expr with (clock' := x + x0) in H.
    apply bigger_clock_list with (clock' := x + x0) in H1.
    rewrite H, H1.
    apply Nat.eqb_neq in n0. rewrite n0. rewrite e4, e5. auto.
    1,3: lia.
    intros. apply clock_increase_expr. auto.
  * destruct H. exists (S x). simpl. rewrite H. auto.
  * destruct H. exists (S x). simpl. rewrite H. auto.
  * epose (P := fbs_expr_list_soundness_exception H H0 _ _ _ _).
    destruct P. exists (S x). simpl. unfold exps in H1.
    rewrite H1. auto.
  Unshelve.
  all: auto.
  - unfold exps, vals. rewrite length_make_map_exps, length_make_map_vals. lia. lia.
  - unfold exps. rewrite length_make_map_exps. auto.
  - unfold exps. rewrite length_make_map_exps. auto.
  - unfold exps. rewrite length_make_map_exps. lia.
  - unfold vals. case_eq (modulo_2 (i)); intros.
    + rewrite e5 in e0. rewrite length_make_map_vals.
      pose (n_div_2_mod_0 _ e5). rewrite e6. lia. lia.
    + rewrite e5 in e0. rewrite length_make_map_vals2.
      pose (n_div_2_mod_1 _ e5). rewrite e6. lia. lia.
Qed.

Theorem fbs_correctness :
(forall env id exp eff id' res eff',
  exists clock, fbs_expr clock env id exp eff = Result id' res eff'
 ->
  | env, id, exp, eff| -e> | id', res, eff' |)
/\
(forall env id exp eff id' res eff',
  exists clock, fbs_single clock env id exp eff = Result id' res eff'
 ->
  | env, id, exp, eff| -s> | id', res, eff' |).
Proof.
  apply eval_ind.
