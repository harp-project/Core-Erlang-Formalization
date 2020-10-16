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

Lemma fbs_case_soundness :
forall {l id' eff2 id'' res eff3 vals env i guard exp bindings},
(forall j : nat,
     j < i ->
     forall (gg ee : Expression) (bb : list (Var * Value)),
     match_clause vals l j = Some (gg, ee, bb) ->
     exists clock : nat,
       fbs_expr clock (add_bindings bb env) id' gg eff2 = Result id' (inl [ffalse]) eff2) ->
match_clause vals l i = Some (guard, exp, bindings) ->
(exists clock : nat,
       fbs_expr clock (add_bindings bindings env) id' guard eff2 =
       Result id' (inl [ttrue]) eff2) ->
(exists clock : nat,
       fbs_expr clock (add_bindings bindings env) id' exp eff2 = Result id'' res eff3) ->
exists clock, (fix clause_eval (l1 : list (list Pattern * Expression * Expression)) : ResultType :=
   match l1 with
   | [] => Result id' (inr if_clause) eff2
   | (pl, gg, bb) :: xs =>
       if match_valuelist_to_patternlist vals pl
       then
        match
          fbs_expr clock (add_bindings (match_valuelist_bind_patternlist vals pl) env) id' gg eff2
        with
        | Result id''0 (inl [v]) eff'' =>
            match v with
            | VLit (Atom s) =>
                if (s =? "true")%string
                then
                 if ((id''0 =? id') && list_eqb effect_eqb eff2 eff'')%bool
                 then
                  fbs_expr clock (add_bindings (match_valuelist_bind_patternlist vals pl) env) id'
                    bb eff2
                 else Failure
                else if (s =? "false")%string then clause_eval xs else Failure
            | _ => Failure
            end
        | Result id''0 (inl (v :: _ :: _)) _ => Failure
        | Result id''0 (inl []) _ | Result id''0 (inr _) _ => Failure
        | _ => Failure
        end
       else clause_eval xs
   end) l = Result id'' res eff3.
Proof.
  induction l; intros.
  * inversion H0.
  * destruct i.
    - simpl in H0. destruct H1, H2. exists (x + x0).
      destruct a, p. destruct (match_valuelist_to_patternlist vals l0).
      + inversion H0. subst.
        apply bigger_clock_expr with (clock' := x + x0) in H1. rewrite H1.
        unfold ttrue. rewrite eqb_refl, Nat.eqb_refl, list_eqb_refl.
        simpl.
        apply bigger_clock_expr with (clock' := x + x0) in H2. rewrite H2. auto.
        1,3: lia. apply effect_eqb_refl.
      + congruence.
    - destruct a, p.
      case_eq (match_clause vals ((l0, e0, e) :: l) 0); intros.
       + destruct p, p.
         pose (H 0 (Nat.lt_0_succ _) _ _ _ H3). simpl in H3. destruct e3.
         destruct (match_valuelist_to_patternlist vals l0). 2: congruence.
         inversion H3. subst.
         epose (IHl id' eff2 id'' res eff3 vals env i guard exp bindings _ _ _ _).
         destruct e. exists (x + x0).
         apply bigger_clock_expr with (clock' := x + x0) in H4.
         apply bigger_clock_case with (clock' := x + x0) in H5.
         rewrite H4. unfold ffalse. simpl. apply H5.
         all: lia.
         Unshelve.
         ** intros. eapply H with (j := S j). lia.
            simpl. exact H6.
         ** exact H0.
         ** auto.
         ** auto.
       + simpl in H3. destruct (match_valuelist_to_patternlist vals l0). 1: congruence.
         epose (IHl id' eff2 id'' res eff3 vals env i guard exp bindings _ _ _ _).
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

Theorem fbs_case_if_clause_sound :
forall {l env eff2 id' vals},
(forall j : nat,
     j < Datatypes.length l ->
     forall (gg ee : Expression) (bb : list (Var * Value)),
     match_clause vals l j = Some (gg, ee, bb) ->
     exists clock : nat,
       fbs_expr clock (add_bindings bb env) id' gg eff2 = Result id' (inl [ffalse]) eff2)
->
exists clock, (fix clause_eval (l0 : list (list Pattern * Expression * Expression)) : ResultType :=
       match l0 with
       | [] => Result id' (inr if_clause) eff2
       | (pl, gg, bb) :: xs =>
           if match_valuelist_to_patternlist vals pl
           then
            match
              fbs_expr clock (add_bindings (match_valuelist_bind_patternlist vals pl) env) id'
                gg eff2
            with
            | Result id'' (inl [v]) eff'' =>
                match v with
                | VLit (Atom s) =>
                    if (s =? "true")%string
                    then
                     if ((id'' =? id') && list_eqb effect_eqb eff2 eff'')%bool
                     then
                      fbs_expr clock
                        (add_bindings (match_valuelist_bind_patternlist vals pl) env) id'
                        bb eff2
                     else Failure
                    else if (s =? "false")%string then clause_eval xs else Failure
                | _ => Failure
                end
            | Result id'' (inl (v :: _ :: _)) _ => Failure
            | Result id'' (inl []) _ | Result id'' (inr _) _ => Failure
            | _ => Failure
            end
           else clause_eval xs
       end) l = Result id' (inr if_clause) eff2.
Proof.
  induction l; intros.
  * exists 0. auto.
  * destruct a, p.
    case_eq (match_clause vals ((l0, e0, e) :: l) 0); intros.
    - destruct p, p.
      pose (P := H 0 (Nat.lt_0_succ _) _ _ _ H0).
      simpl in H0.
      assert (exists clock : nat,
            fbs_expr clock (add_bindings l1 env) id' e1 eff2 = Result id' (inl [ffalse]) eff2). 
      { auto. } clear P.
      destruct (match_valuelist_to_patternlist vals l0). 2: congruence.
      inversion H0. subst. destruct H1.
      epose (IHl env eff2 id' vals _). destruct e.
      exists (x + x0).
      apply bigger_clock_expr with (clock' := x + x0) in H1.
      apply bigger_clock_case with (clock' := x + x0) in H2.
      rewrite H1, H2. simpl. auto.
      all: lia.
      Unshelve.
      + intros. eapply H with (j := S j). simpl. lia. simpl. exact H3.
    - simpl in H0. destruct (match_valuelist_to_patternlist vals l0). 1: congruence.
      epose (IHl env eff2 id' vals _). destruct e1.
      exists x. rewrite H1. auto.
      Unshelve.
      + intros. eapply H with (j := S j). simpl. lia. simpl. exact H2.
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
  * destruct H. pose (P := fbs_case_soundness H0 e1 H1 H2). destruct P.
    exists (S (x + x0)). simpl.
    apply bigger_clock_expr with (clock' := x + x0) in H.
    apply bigger_clock_case with (clock' := x + x0) in H3.
    rewrite H. exact H3.
    all: lia.
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
  * destruct H. pose (P := fbs_case_if_clause_sound H0).
    destruct P. exists (S (x + x0)).
    apply bigger_clock_expr with (clock' := x + x0) in H.
    apply bigger_clock_case with (clock' := x + x0) in H1.
    simpl. rewrite H, H1. auto. all: lia.
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

Admitted.
