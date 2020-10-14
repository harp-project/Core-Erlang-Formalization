Require Core_Erlang_Semantics.
Require Core_Erlang_Functional_Big_Step.


Export Core_Erlang_Semantics.Semantics.
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

Lemma fbs_expr_list_soundness :
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
    apply bigger_list_values with (clock' := cl1 + cl2) in H7. 
      2: lia. 2: apply clock_increase.
    rewrite H3, H7.
    rewrite last_element_equal with (def2 := id).
    rewrite last_element_equal with (def2 := eff1). auto.
Qed.

Lemma fbs_expr_list_soundness_exception :
forall {exps vals eff ids env id eff1 id' ex eff' i},
(forall j : nat,
    j < i ->
    exists clock : nat,
      fbs_single clock env (nth_def ids id 0 j) (nth j exps ErrorExp) (nth_def eff eff1 [] j) =
      Result (nth_def ids id 0 (S j)) (inl [nth j vals ErrorValue])
        (nth_def eff eff1 [] (S j)))
->
| env, last ids id, nth i exps ErrorExp, last eff eff1 | -s> | id', inr ex, eff' |
->
i < Datatypes.length exps ->
Datatypes.length vals = i ->
Datatypes.length eff = i ->
Datatypes.length ids = i
->
  exists clock, fbs_values (fbs_single clock) env id exps eff1 = Result id' (inr ex) eff'.
Proof.

Admitted.

Lemma fbs_single_list_soundness :
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
    apply bigger_list_values with (clock' := cl1 + cl2) in H7. 
      2: lia. 2: apply clock_increase.
    rewrite H3, H7.
    rewrite last_element_equal with (def2 := id).
    rewrite last_element_equal with (def2 := eff1). auto.
Qed.

Lemma fbs_single_list_soundness_exception :
forall {exps : list Expression} {vals eff ids env id eff1 id' ex eff' i},
(forall j : nat,
    j < i ->
    exists clock : nat,
      fbs_expr clock env (nth_def ids id 0 j) (nth j exps ErrorExp) (nth_def eff eff1 [] j) =
      Result (nth_def ids id 0 (S j)) (inl [nth j vals ErrorValue])
        (nth_def eff eff1 [] (S j)))
->
| env, last ids id, nth i exps ErrorExp, last eff eff1 | -e> | id', inr ex, eff' |
->
i < Datatypes.length exps ->
Datatypes.length vals = i ->
Datatypes.length eff = i ->
Datatypes.length ids = i
->
  exists clock, fbs_values (fbs_expr clock) env id exps eff1 = Result id' (inr ex) eff'.
Proof.

Admitted.

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
  * pose (P := fbs_expr_list_soundness H e e0 e1). destruct P.
    exists (S x). simpl. rewrite H0, e3, e4. auto.
  * pose (P := fbs_expr_list_soundness_exception H e3 l e e0 e1). destruct P. exists (S x). simpl. auto.
  * destruct H. exists (S x). auto.
  * exists 1. auto.
  * exists 1. auto.
  * exists 1. simpl. rewrite e. auto.
  * exists 1. simpl. rewrite e. auto.
  * exists 1. auto.
  * pose (P := fbs_single_list_soundness H e e0 e1). destruct P.
    exists (S x). simpl. rewrite H0, e3, e4. auto.
  * destruct H as [cl1], H0 as [cl2].
    exists (S (cl1 + cl2)). simpl.
    apply bigger_clock_expr with (clock' := cl1 + cl2) in H.
    apply bigger_clock_expr with (clock' := cl1 + cl2) in H0.
    rewrite H, H0. 2-3: lia. auto.
  * admit.
  
  
  
  
  
  
  
  
  
  * pose (P := fbs_single_list_soundness_exception H e3). destruct P. exists (S x). simpl. rewrite H1. auto.
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
