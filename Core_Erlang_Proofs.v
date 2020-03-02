(* Load Core_Erlang_Induction. *)
Load Core_Erlang_Semantics.

Module Core_Erlang_Proofs.

Import Core_Erlang_Syntax.
Import Core_Erlang_Semantics.
Import Core_Erlang_Environment.
Import Core_Erlang_Closures.
Import Core_Erlang_Helpers.
(* Import Core_Erlang_Induction. *)

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.
Import Coq.Init.Logic.
Import Omega.

Proposition plus_comm_basic (e1 e2 : Value) : eval "plus"%string [e1 ; e2] = eval "plus"%string [e2; e1].
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(reflexivity).
  all: try(destruct l); try(destruct l0); try(reflexivity).
  * rewrite <- Z.add_comm. reflexivity.
Qed.

(* Proposition and_comm_basic (e1 e2 : Value) : eval "and"%string [e1 ; e2] = eval "and"%string [e2 ; e1].
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  1-144: try(reflexivity).
  1-23: try(destruct l); try(destruct l0); try(reflexivity).
  * pose (eqf := string_dec s "false"); pose (eqf2 := string_dec s0 "false"); pose (eqt := string_dec s "true"); pose (eqt2 := string_dec s0 "true"); destruct eqf, eqf2, eqt, eqt2; subst; try(reflexivity).
    - admit.
Admitted. *)

Lemma in_combined_list : forall P : Prop, forall l l' a b,
  (forall e : Expression, forall e' : Value,
    In (e, e') ((a, b) :: combine l l') -> P) -> 
  (forall e : Expression, forall e' : Value,
    In (e, e') (combine l l') -> P).
Proof.
  intros. pose (in_cons (a, b) (e, e') (combine l l') H0). pose (H e e' i). assumption.
Qed.

Import Omega.


Proposition nat_ge_or : forall n m : nat, n >= m <-> n = m \/ n > m.
Proof.
intros. omega.
Qed.

Proposition determinism_hypo env cl exp v1 v2: 
 |env, cl, exp| -e> inl v1 ->
 (forall v2 : Value, |env, cl, exp| -e> inl v2 -> v1 = v2)
  ->
  |env, cl, exp| -e> inl v2
->
  v1 = v2
.
Proof.
  intros. apply (H0 v2 H1).
Qed.

Lemma index_case_equality (i i0 : nat) env0 cl0 patterns guards bodies v guard guard0 exp exp0 bindings bindings0 : 
  (forall j : nat,
     j < i ->
     forall (gg ee : Expression) (bb : list (Var * Value)),
     match_clause v patterns guards bodies j = Some (gg, ee, bb) ->
     forall v2 : Value + Exception, | add_bindings bb env0, cl0, gg | -e> v2 -> inl ffalse = v2)
  ->
  (forall j : nat,
     j < i0 ->
     forall (gg ee : Expression) (bb : list (Var * Value)),
     match_clause v patterns guards bodies j = Some (gg, ee, bb) ->
     | add_bindings bb env0, cl0, gg | -e> inl ffalse)
  ->
  match_clause v patterns guards bodies i = Some (guard, exp, bindings)
  ->
  match_clause v patterns guards bodies i0 = Some (guard0, exp0, bindings0)
  ->
  |add_bindings bindings0 env0, cl0, guard0| -e> inl ttrue
  ->
  |add_bindings bindings env0, cl0, guard| -e> inl ttrue
  ->
  (forall v2 : Value + Exception, |add_bindings bindings env0, cl0, guard| -e> v2 -> inl ttrue = v2)
->
  i = i0.
Proof.
  intros. pose (Nat.lt_decidable i i0). destruct d.
  * pose (H0 i H6 guard exp bindings H1). pose (H5 (inl ffalse) e). inversion e0.
  * apply not_lt in H6. apply (nat_ge_or) in H6. inversion H6.
    - assumption.
    - pose (H i0 H7 guard0 exp0 bindings0 H2 (inl ttrue) H3). inversion e.
Qed.

Lemma list_equality (env0 : Environment) (cl0 : Closures) (exps : list Expression)  : 
forall vals vals0 : list Value,
  (forall (exp : Expression) (val : Value),
    In (exp, val) (combine exps vals) -> |env0, cl0, exp| -e> inl val) ->
  (forall (exp : Expression) (val : Value),
    In (exp, val) (combine exps vals) -> forall v2 : Value, |env0, cl0, exp| -e> inl v2 -> val = v2) ->
  (forall (exp : Expression) (val : Value),
    In (exp, val) (combine exps vals0) -> |env0, cl0, exp| -e> inl val) ->
  Datatypes.length exps = Datatypes.length vals ->
  Datatypes.length exps = Datatypes.length vals0
->
  vals = vals0.
Proof.
  induction exps.
  * intros. inversion H3. inversion H2. apply eq_sym in H6. apply eq_sym in H5. apply length_zero_iff_nil in H6. apply length_zero_iff_nil in H5. subst. reflexivity.
  * intros. inversion H3. inversion H2. 
  
  (* first elements are the same *)
    pose (element_exist Value (Datatypes.length exps) vals (eq_sym H6)).
    pose (element_exist Value (Datatypes.length exps) vals0 (eq_sym H5)).
    inversion e. inversion e0. inversion H4. inversion H7. subst.
    pose (in_eq (a, x) (combine (exps) (x1))).
    pose (in_eq (a, x0) (combine (exps) (x2))).
    pose (H1 a x0 i0).
    pose (H0 a x i x0 e1). rewrite <- e2 in *.
  (* remaining lists are the same *)
  
  (* These three asserts ensure, that if something states for every element in a (b::l) list, then it states
  for every element in l too*)
    assert (
      forall (exp : Expression) (val : Value),
       In (exp, val) (combine exps x1) ->
       forall v2 : Value, |env0, cl0, exp| -e> inl v2 -> val = v2
    ).
    {
      intros. pose (in_cons (a, x) (exp, val) (combine exps x1) H8). pose (H0 exp val i1 v2 H9). assumption.
    }
    assert (
      forall (exp : Expression) (val : Value),
    In (exp, val) (combine exps x1) -> |env0, cl0, exp| -e> inl val
    ).
    {
      intros. pose (in_cons (a, x) (exp, val) (combine exps x1) H9). pose (H exp val i1). assumption.
    }
    assert (
      forall (exp : Expression) (val : Value),
     In (exp, val) (combine exps x2) -> |env0, cl0, exp| -e> inl val
    ).
    {
      intros. pose (in_cons (a, x0) (exp, val) (combine exps x2) H10). pose (H1 exp val i1). assumption.
    }
    (* simpl list lengths *)
    inversion H2.
    inversion H3.
    pose (IHexps x1 x2 H9 H8 H10 H12 H13). rewrite e3.
    reflexivity.
Qed.

(* Section Combine_Proof.

Theorem nth_in_combine : length l1 = length l2 -> n < length l1 -> In (nth n l1 d1, nth n l2 d2) (combine l1 l2).

End Combine_Proof. *)

(* Theorem In_double_combine (kl vl : list Expression) (kvals vvals : list Value) kexp kval:
  In (kexp, kval) (combine kl kvals) ->
  length kl = length vl ->
  length kl = length kvals ->
  length kl = length vvals
->
  exists vexp vval, In (kexp, kval, (vexp, vval)) (combine (combine kl kvals) (combine vl vvals)).
Proof.
  intros. remember (combine kl vl) as l. induction l.
  * pose (combine_split kl vl H0). rewrite <- Heql in e. inversion e. subst. inversion H.
  * destruct a. assert (exists x x0, kl = e::x /\ vl = e0::x0).
    {
      assert (length kl = length (combine kl vl)).
      {
         rewrite combine_length. rewrite H0. rewrite Nat.min_id. reflexivity.
      }
      rewrite <- Heql in H3. simpl in H3. pose (element_exist Expression (length l) kl H3). inversion e1. inversion H4.

      assert (length vl = length (combine kl vl)).
      {
         rewrite combine_length. rewrite H0. rewrite Nat.min_id. reflexivity.
      }
      rewrite <- Heql in H6. simpl in H6. pose (element_exist Expression (length l) vl H6). inversion e2. inversion H7.

      apply ex_intro with x0. apply ex_intro with x2. subst. inversion Heql. subst. auto.
    }
    inversion H3. inversion H4. inversion H5. subst. simpl in H2. pose (element_exist Value (length x) vvals (eq_sym H2)). inversion e1. inversion H6. subst. apply ex_intro with e0. apply ex_intro with x1. 
Qed.

Theorem destruction env cl kl vl kvals vvals :
  (forall (kexp vexp : Expression) (kval vval : Value),
     In (kexp, kval, (vexp, vval)) (combine (combine kl kvals) (combine vl vvals)) ->
     | env, cl, kexp | -e> inl kval /\ | env, cl, vexp | -e> inl vval) ->
  (length kl = length vl) ->
  (length kvals = length vvals) ->
  (length kl = length kvals)
->
  (forall kexp kval, In (kexp, kval) (combine kl kvals) -> | env, cl, kexp | -e> inl kval) /\
  (forall vexp vval, In (vexp, vval) (combine vl vvals) -> | env, cl, vexp | -e> inl vval).
Proof.
  intros. split; intros.
  * 
Qed. *)

Lemma exception_equality env cl i i0 exps vals ex ex0 vals0 :
(forall j : nat,
     j < i ->
     forall v2 : Value + Exception,
     | env, cl, nth j exps ErrorExp | -e> v2 -> inl (nth j vals ErrorValue) = v2) ->
(forall j : nat, j < i0 -> | env, cl, nth j exps ErrorExp | -e> inl (nth j vals0 ErrorValue)) ->
(forall v2 : Value + Exception, | env, cl, nth i exps ErrorExp | -e> v2 -> inr ex = v2) ->
| env, cl, nth i0 exps ErrorExp | -e> inr ex0 ->
i = i0.
Proof.
  intros. destruct (le_gt_dec i i0).
  * case_eq (le_lt_or_eq i i0 l).
    - intros. pose (H0 (i) l0). pose (H1 (inl (nth i vals0 ErrorValue)) e). inversion e0.
    - intros. assumption.
  * pose (H i0 g (inr ex0) H2). inversion e.
Qed.

Proposition nth_In_combined_list (exps : list Expression) (vals vals0 : list Value) :
length exps = length vals ->
length vals0 < length exps ->
In (nth (length vals0) exps ErrorExp, nth (length vals0) vals ErrorValue) (combine exps vals).
Proof.
  intros. rewrite <- combine_nth.
    * apply nth_In. rewrite combine_length. rewrite <- H. rewrite Nat.min_id. assumption. 
    * assumption.
Qed.

Proposition nth_to_nth env cl exps (vals vals0 : list Value) :
  (forall (exp : Expression) (val : Value),
     In (exp, val) (combine exps vals0) -> | env, cl, exp | -e> inl val) ->
  Datatypes.length exps = Datatypes.length vals0 ->
  Datatypes.length vals < Datatypes.length exps
->
  | env, cl, nth (Datatypes.length vals) exps ErrorExp | -e>
   inl (nth (Datatypes.length vals) vals0 ErrorValue).
Proof.
  intros. apply H. rewrite <- combine_nth. 2: assumption. apply nth_In. rewrite combine_length. rewrite <- H0. rewrite Nat.min_id. assumption.
Qed.

Proposition restrict_union env cl exps vals :
  (forall (exp : Expression) (val : Value),
     In (exp, val) (combine exps vals) ->
     forall v2 : Value + Exception, | env, cl, exp | -e> v2 -> inl val = v2)
->
  (forall (exp : Expression) (val : Value),
     In (exp, val) (combine exps vals) ->
     forall v2 : Value, | env, cl, exp | -e> inl v2 -> val = v2).
Proof.
  intros. pose (H exp val H0). pose (e (inl v2) H1). inversion e0. reflexivity.
Qed.

Proposition nth_to_nth_case env cl v patterns guards bodies i i0 guard guard0 exp exp0 bindings bindings0 ex:
(forall j : nat,
     j < i ->
     forall (gg ee : Expression) (bb : list (Var * Value)),
     match_clause v patterns guards bodies j = Some (gg, ee, bb) ->
     forall v2 : Value + Exception, | add_bindings bb env, cl, gg | -e> v2 -> inl ffalse = v2) ->
(forall j : nat,
      j < i0 ->
      forall (gg ee : Expression) (bb : list (Var * Value)),
      match_clause v patterns guards bodies j = Some (gg, ee, bb) -> | add_bindings bb env, cl, gg | -e> inl ffalse) ->
(forall v2 : Value + Exception,
      | add_bindings bindings env, cl, guard | -e> v2 -> inl ttrue = v2) ->
| add_bindings bindings0 env, cl, guard0 | -e> inr ex ->
match_clause v patterns guards bodies i0 = Some (guard0, exp0, bindings0) ->
match_clause v patterns guards bodies i = Some (guard, exp, bindings)
->
False.
Proof.
  intros. destruct (le_gt_dec i i0).
  * case_eq (le_lt_or_eq i i0 l).
    - intros. pose (H0 i l0 _ _ _ H4). pose (H1 (inl ffalse) e). inversion e0.
    - intros. subst. rewrite H3 in H4. inversion H4. subst. pose (H1 (inr ex) H2). inversion e.
  * pose (H i0 g guard0 exp0 bindings0 H3 (inr ex) H2). inversion e.
Qed.

Proposition nth_to_nth_case_ex env cl v patterns guards bodies i i0 guard guard0 exp exp0 bindings bindings0 ex:
(forall j : nat,
     j < i ->
     forall (gg ee : Expression) (bb : list (Var * Value)),
     match_clause v patterns guards bodies j = Some (gg, ee, bb) ->
     forall v2 : Value + Exception, | add_bindings bb env, cl, gg | -e> v2 -> inl ffalse = v2) ->
(forall j : nat,
      j < i0 ->
      forall (gg ee : Expression) (bb : list (Var * Value)),
      match_clause v patterns guards bodies j = Some (gg, ee, bb) -> | add_bindings bb env, cl, gg | -e> inl ffalse) ->
(forall v2 : Value + Exception,
               | add_bindings bindings env, cl, guard | -e> v2 -> inr ex = v2) ->
| add_bindings bindings0 env, cl, guard0 | -e> inl ttrue ->
| add_bindings bindings env, cl, guard | -e> inr ex ->
match_clause v patterns guards bodies i0 = Some (guard0, exp0, bindings0) ->
match_clause v patterns guards bodies i = Some (guard, exp, bindings)
->
False.
Proof.
  intros. destruct (le_gt_dec i i0).
  * case_eq (le_lt_or_eq i i0 l).
    - intros. pose (H0 i l0 _ _ _ H5). pose (H1 (inl ffalse) e). inversion e0.
    - intros. subst. rewrite H4 in H5. inversion H5. subst. pose (H1 (inl ttrue) H2). inversion e.
  * pose (H i0 g guard0 exp0 bindings0 H4 (inl ttrue) H2). inversion e.
Qed.

Lemma index_case_equality_ex (i i0 : nat) env0 cl0 patterns guards bodies v guard guard0 exp exp0 bindings bindings0 ex ex0 : 
  (forall j : nat,
     j < i ->
     forall (gg ee : Expression) (bb : list (Var * Value)),
     match_clause v patterns guards bodies j = Some (gg, ee, bb) ->
     forall v2 : Value + Exception, | add_bindings bb env0, cl0, gg | -e> v2 -> inl ffalse = v2)
  ->
  (forall j : nat,
     j < i0 ->
     forall (gg ee : Expression) (bb : list (Var * Value)),
     match_clause v patterns guards bodies j = Some (gg, ee, bb) ->
     | add_bindings bb env0, cl0, gg | -e> inl ffalse)
  ->
  match_clause v patterns guards bodies i = Some (guard, exp, bindings)
  ->
  match_clause v patterns guards bodies i0 = Some (guard0, exp0, bindings0)
  ->
  |add_bindings bindings0 env0, cl0, guard0| -e> inr ex0
  ->
  |add_bindings bindings env0, cl0, guard| -e> inr ex
  ->
  (forall v2 : Value + Exception, |add_bindings bindings env0, cl0, guard| -e> v2 -> inr ex = v2)
->
  i = i0.
Proof.
  intros. pose (Nat.lt_decidable i i0). destruct d.
  * pose (H0 i H6 guard exp bindings H1). pose (H5 (inl ffalse) e). inversion e0.
  * apply not_lt in H6. apply (nat_ge_or) in H6. inversion H6.
    - assumption.
    - pose (H i0 H7 guard0 exp0 bindings0 H2 (inr ex0) H3). inversion e.
Qed.

Theorem determinism : forall env cl e v1, |env, cl, e| -e> v1 -> (forall v2, |env, cl, e| -e> v2 -> v1 = v2).
Proof.
  intro. intro. intro. intro. intro H. induction H.
  (* LITERAL, VARIABLE, FUNCTION SIGNATURE, FUNCTION DEFINITION *)
  1-3: intros; inversion H; reflexivity.
  * intros. inversion H. reflexivity.

  (* TUPLE *)
  * intros. inversion H2; subst. 
    - pose (list_equality env cl exps vals vals0 H0 (restrict_union env cl exps vals H1) H7 H H4). rewrite e. reflexivity.
   - pose (H1 (nth (Datatypes.length vals0) exps ErrorExp) (nth (Datatypes.length vals0) vals ErrorValue) (nth_In_combined_list exps vals vals0 H H5)  (inr ex) H9). inversion e.

  (* LIST *)
  * intros. inversion H1. 
    - subst. pose (IHeval_expr1 (inl hdv0) H6). pose (IHeval_expr2 (inl tlv0) H8). inversion e. inversion e0. reflexivity.
    - subst. pose (IHeval_expr1 (inr ex) H7). inversion e.
    - subst. pose (IHeval_expr2 (inr ex) H8). inversion e.

  (* CASE *)
  * intros. inversion H8.
    - subst.
      (* determinism of initial expression *)
      pose (IHeval_expr1 (inl v0) H13). inversion e0. subst.
      pose (index_case_equality i i0 env cl patterns guards bodies v0 guard guard0 exp exp0 bindings bindings0 H5 H21 H3 H19 H22 H6 IHeval_expr2).
     (* Coq Hacking for possible rewrites *)
     pose H19. pose H3. rewrite e1 in e3. rewrite e2 in e3. inversion e3. rewrite H10, H11, H12 in *.
     (* clause evaluation *)
    pose (IHeval_expr3 v2 H23). assumption.
    - subst. pose (IHeval_expr1 (inr ex) H18). inversion e0.
    - subst. pose (IHeval_expr1 (inl v0) H17). inversion e0. rewrite <- H10 in *. pose (nth_to_nth_case env cl v patterns guards bodies i i0 guard guard0 exp exp0 bindings bindings0 ex H5 H20 IHeval_expr2 H21 H19 H3). inversion f.

  (* CALL *)
  * intros. inversion H3.
    - subst.
      pose (list_equality env cl params vals vals0 H0 (restrict_union env cl params vals H1) H9 H H6). rewrite e. reflexivity.
    - subst. pose (H1 (nth (Datatypes.length vals0) params ErrorExp) (nth (Datatypes.length vals0) vals ErrorValue) (nth_In_combined_list params vals vals0 H H7) (inr ex) H12). inversion e.

  (* APPLY *)
  * intros. inversion H5.
    - subst. pose (list_equality env cl params vals vals0 H2 (restrict_union env cl params vals H3) H13 H H8). rewrite e in *.
      (* The equality of the var lists *)
      pose (IHeval_expr1 (inl (VClosure ref0 var_list0 body0)) H9). inversion e0. rewrite H7, H11, H12 in *.
      (* equality of the expressions *)
      pose (IHeval_expr2 v2 H15). assumption.
    - subst. pose (IHeval_expr1 (inr ex) H11). inversion e.
    - subst. pose (H3 (nth (Datatypes.length vals0) params ErrorExp) (nth (Datatypes.length vals0) vals ErrorValue) (nth_In_combined_list params vals vals0 H H9) (inr ex) H15). inversion e.
    - subst. pose (IHeval_expr1 (inl v0) H12). inversion e. rewrite <- H7 in H14. pose (H14 ref var_list body). unfold not in n. assert (VClosure ref var_list body = VClosure ref var_list body). { auto. } pose (n H6). inversion f.
    - subst. pose (IHeval_expr1 (inl (VClosure ref0 var_list0 body0)) H9). inversion e. subst. rewrite H1 in *. rewrite <- H, H8 in *. unfold not in H14. assert (length vals0 = length vals0). { auto. } pose (H14 H6). inversion f.

  (* LET *)
  * intros. inversion H3. subst.
   - pose (list_equality env cl exps vals vals0 H0 (restrict_union env cl exps vals H1) H11 (eq_sym H) (eq_sym H9)). rewrite e0 in *.
     pose (IHeval_expr v2 H12). assumption.
   - subst. pose (H1 (nth (Datatypes.length vals0) exps ErrorExp) (nth (Datatypes.length vals0) vals ErrorValue) (nth_In_combined_list exps vals vals0 (eq_sym H) H10) (inr ex) H13). inversion e0.

  (* LETREC *)
  * intros. inversion H2. 
    - subst. pose (IHeval_expr v2 H12). assumption.

  (* (* MAP *)
  * intros. inversion H4.
    - subst.
      (* Key list equality *)
      rewrite H in *.
      
      assert((forall (exp : Expression) (val : Value),
    In (exp, val) (combine kl kvals) -> | env, cl, exp | -e> inl val)). { intros. }
      assert ((forall (exp : Expression) (val : Value),
    In (exp, val) (combine kl kvals) -> forall v2 : Value, | env, cl, exp | -e> inl v2 -> val = v2)). { admit. }
      assert ((forall (exp : Expression) (val : Value),
    In (exp, val) (combine kl kvals0) -> | env, cl, exp | -e> inl val)). { admit. }
      (* assert (forall (exp : Expression) (val : Value),
         In (exp, val) (combine kl kvals) ->
         forall v2 : Value, | env, cl, exp | -e> inl v2 -> val = v2). 
         { intros. pose (H3 exp val H7). pose (e (inl v2) H8). inversion e0. reflexivity. }
      assert (forall (exp : Expression) (val : Value),
         In (exp, val) (combine vl vvals) ->
         forall v2 : Value, | env, cl, exp | -e> inl v2 -> val = v2). 
         { intros. pose (H5 exp val H8). pose (e (inl v2) H12). inversion e0. reflexivity. }  *)
      
      pose (list_equality env cl kl kvals kvals0 H5 H6 H9 H1 H11). rewrite e in *.
      (* value list equality *)
      rewrite <- H in *.
      
      assert (forall (exp : Expression) (val : Value),
    In (exp, val) (combine vl vvals) -> | env, cl, exp | -e> inl val). { admit. }
      assert ((forall (exp : Expression) (val : Value),
    In (exp, val) (combine vl vvals) -> forall v2 : Value, | env, cl, exp | -e> inl v2 -> val = v2)). { admit. }
      assert ((forall (exp : Expression) (val : Value),
    In (exp, val) (combine vl vvals0) -> | env, cl, exp | -e> inl val)). { admit. }
      pose (list_equality env cl vl vvals vvals0 H10 H12 H14 H0 H8). rewrite e0 in *.
      reflexivity.

(* Last 2 subgoals are very similar *)
    - subst. assert (In
     (nth (Datatypes.length vvals0) kl ErrorExp, nth (Datatypes.length vvals0) kvals ErrorValue,
     (nth (Datatypes.length vvals0) vl ErrorExp, nth (Datatypes.length vvals0) vvals ErrorValue))
     (combine (combine kl kvals) (combine vl vvals))).
       { rewrite <- combine_nth. rewrite <- combine_nth. rewrite <- combine_nth. apply nth_In. rewrite combine_length. rewrite combine_length. rewrite combine_length. rewrite <- H, H0 in *. rewrite H1. rewrite Nat.min_id. rewrite Nat.min_id. rewrite H1 in *. assumption.
       + rewrite combine_length. rewrite combine_length. rewrite <- H, H0 in *. rewrite H1. rewrite Nat.min_id. reflexivity.
       + assumption.
       + rewrite <- H. assumption. }
    pose (H3 (nth (Datatypes.length vvals0) kl ErrorExp)
                      (nth (Datatypes.length vvals0) vl ErrorExp)
                      (nth (Datatypes.length vvals0) kvals ErrorValue) 
                      (nth (Datatypes.length vvals0) vvals ErrorValue) H5).
      inversion a. pose (H6 (inr ex) H15). inversion e.
    - subst. assert (In
     (nth (Datatypes.length vvals0) kl ErrorExp, nth (Datatypes.length vvals0) kvals ErrorValue,
     (nth (Datatypes.length vvals0) vl ErrorExp, nth (Datatypes.length vvals0) vvals ErrorValue))
     (combine (combine kl kvals) (combine vl vvals))).
       { rewrite <- combine_nth. rewrite <- combine_nth. rewrite <- combine_nth. apply nth_In. rewrite combine_length. rewrite combine_length. rewrite combine_length. rewrite <- H, H0 in *. rewrite H1. rewrite Nat.min_id. rewrite Nat.min_id. rewrite H1 in *. assumption.
       + rewrite combine_length. rewrite combine_length. rewrite <- H, H0 in *. rewrite H1. rewrite Nat.min_id. reflexivity.
       + assumption.
       + rewrite <- H. assumption. }
    pose (H3 (nth (Datatypes.length vvals0) kl ErrorExp)
                      (nth (Datatypes.length vvals0) vl ErrorExp)
                      (nth (Datatypes.length vvals0) kvals ErrorValue) 
                      (nth (Datatypes.length vvals0) vvals ErrorValue) H5).
      inversion a. pose (H8 (inr ex) H16). inversion e.*)

  (* LIST HEAD EXCEPTION *)
  * intros. inversion H0; subst.
    - pose (IHeval_expr (inl hdv) H5). inversion e.
    - apply IHeval_expr. assumption.
    - pose (IHeval_expr (inl vhd) H5). inversion e.

  (* LIST TAIL EXCEPTION *)
  * intros. inversion H1; subst.
    - pose (IHeval_expr2 (inl tlv) H8). inversion e.
    - pose (IHeval_expr1 (inr ex0) H7). inversion e.
    - apply IHeval_expr2. assumption.

  (* TUPLE EXCEPTION *)
  * intros. inversion H4.
    - subst.
      pose (IHeval_expr (inl (nth (Datatypes.length vals) vals0 ErrorValue)) (nth_to_nth env cl exps vals vals0 H9 H6 H0)). inversion e.
    - apply IHeval_expr. pose (exception_equality env cl i i0 exps vals ex ex0 vals0 H2 H8 IHeval_expr H11).
      rewrite e. assumption.
  
  (* CORECT TRY *)
  * intros. inversion H1.
    - subst. apply IHeval_expr2. pose (IHeval_expr1 (inl val'0) H12). inversion e0. subst. assumption.
    - subst. pose (IHeval_expr1 (inr ex) H12). inversion e0.
  
  (* CORRECT CATCH *)
  * intros. inversion H1.
    - subst. pose (IHeval_expr1 (inl val') H12). inversion e0.
    - subst. apply IHeval_expr2. pose (IHeval_expr1 (inr ex0) H12). inversion e0. subst. assumption.

  (* CASE EXCEPTIONS *)
  (** binding expression exception *)
  * intros. inversion H2.
    - subst. pose (IHeval_expr (inl v) H7). inversion e0.
    - subst. apply IHeval_expr. assumption.
    - subst. pose (IHeval_expr (inl v) H11). inversion e0.

  (** ith guard exception *)
  * intros. inversion H6.
    - pose (IHeval_expr1 (inl v0) H11). inversion e1. rewrite <- H23 in *. pose (nth_to_nth_case_ex env cl v patterns guards bodies i i0 guard guard0 exp exp0 bindings bindings0 ex H4 H19 IHeval_expr2 H20 H5 H17 H2). inversion f.
    - pose (IHeval_expr1 (inr ex0) H16). inversion e1.
    - pose (IHeval_expr1 (inl v0) H15). inversion e1. rewrite <- H21 in *.
    assert (match_clause v patterns guards bodies i0 = Some (guard0, exp0, bindings0)). { assumption. } 
    assert (match_clause v patterns guards bodies i = Some (guard, exp, bindings)). { assumption. }
    assert (| add_bindings bindings0 env, cl, guard0 | -e> inr ex0). { assumption. }
    pose (index_case_equality_ex i i0 env cl patterns guards bodies v guard guard0 exp exp0 bindings bindings0 ex ex0 H4 H18 H2 H17 H19 H5 IHeval_expr2).
    rewrite <- e2 in H20. rewrite H20 in H22. inversion H22. rewrite H25, H26, H27 in *. pose (IHeval_expr2 (inr ex0) H23). assumption.

  (* CALL EXCEPTION *)
  * intros. inversion H4.
    - subst.
      pose (IHeval_expr (inl (nth (Datatypes.length vals) vals0 ErrorValue)) (nth_to_nth env cl params vals vals0 H10 H7 H0)). inversion e.
    - apply IHeval_expr. pose (exception_equality env cl i i0 params vals ex ex0 vals0 H2 H11 IHeval_expr H13).
      rewrite e. assumption.

  (* APPLY EXCEPTION *)
  (* name evaluates to an exception *)
  * intros. inversion H0.
    - subst. pose (IHeval_expr (inl (VClosure ref var_list body)) H4). inversion e.
    - subst. apply IHeval_expr. assumption.
    - subst. pose (IHeval_expr (inl v) H5). inversion e.
    - subst. pose (IHeval_expr (inl v) H7). inversion e.
    - subst. pose (IHeval_expr (inl _) H4). inversion e.

  (* parameter exception *)
  * intros. inversion H5.
    - subst. pose (nth_to_nth env cl params vals vals0 H13 H8 H0). pose (IHeval_expr2 (inl (nth (Datatypes.length vals) vals0 ErrorValue)) e). inversion e0.
    - subst. pose (IHeval_expr1 (inr _) H11). inversion e.
    - pose (exception_equality env cl i i0 params vals ex ex0 vals0 H3 H13 IHeval_expr2 H15). rewrite e in *.
      apply IHeval_expr2. rewrite e. assumption.
    - subst. pose (nth_to_nth env cl params vals vals0 H9 H8 H0). pose (IHeval_expr2 (inl (nth (Datatypes.length vals) vals0 ErrorValue)) e). inversion e0.
    - subst. pose (nth_to_nth env cl params vals vals0 H12 H8 H0). pose (IHeval_expr2 (inl (nth (Datatypes.length vals) vals0 ErrorValue)) e). inversion e0.

  (* name evaluate to a non-closure value *)
  * intros. inversion H4.
    - subst. pose (IHeval_expr (inl (VClosure ref var_list body)) H8). inversion e. pose (H3 ref var_list body H6). inversion f.
    - subst. pose (IHeval_expr (inr ex) H10). inversion e.
    - subst. pose (nth_In_combined_list params vals vals0 H H8). pose (H1 (nth (Datatypes.length vals0) params ErrorExp) (nth (Datatypes.length vals0) vals ErrorValue) i (inr ex) H14). inversion e.
    - subst. reflexivity. (* More information is needed about the specific location *)
    - subst. pose (IHeval_expr (inl (VClosure ref var_list body)) H8). inversion e. pose (H3 ref var_list body H6). inversion f.

  (* paramlist is too short/long *)
  * intros. inversion H4.
    - subst. pose (IHeval_expr (inl (VClosure ref0 var_list0 body0)) H8). inversion e. subst.
      rewrite <- H, H7 in *. pose (H3 H9). inversion f.
    - subst. pose (IHeval_expr (inr ex) H10). inversion e.
    - subst. pose (nth_In_combined_list params vals vals0 H H8). pose (H2 (nth (Datatypes.length vals0) params ErrorExp) (nth (Datatypes.length vals0) vals ErrorValue) i (inr ex) H14). inversion e.
    - subst. pose (IHeval_expr (inl v) H11). inversion e. pose (H13 ref var_list body (eq_sym H6)). inversion f.
    - reflexivity. (* More information is needed about the location *)
  
  (* LET EXCEPTION *)
  * intros. inversion H4.
    - subst. pose (IHeval_expr (inl (nth (Datatypes.length vals) vals0 ErrorValue)) (nth_to_nth env cl exps vals vals0 H12 (eq_sym H10) H0)). inversion e0.
    - apply IHeval_expr. pose (exception_equality env cl i i0 exps vals ex ex0 vals0 H2 H13 IHeval_expr H14).
      rewrite e1. assumption.
Qed.

Ltac unfold_list exprs2 n H1 name :=
subst; simpl in H1; pose (name := element_exist Expression n exprs2 (eq_sym H1)); inversion name; inversion H0.

(* Theorem env_permutation env env' cl e t:
(env, cl, e) -e> t -> length env = length env' ->
(forall elem, In elem env -> In elem env') ->
(env', cl, e) -e> t.
Proof.


Admitted.*)

Theorem uequal_eq v0 v:
  uequal v0 v = true <-> v0 = v.
Proof.
  intros. split; intros.
  { destruct v0, v.
    * inversion H. apply eqb_eq in H1. subst. reflexivity.
    * inversion H.
    * inversion H.
    * inversion H. destruct f, f0. inversion H1. apply Bool.andb_true_iff in H2. inversion H2. apply eqb_eq in H0. apply Nat.eqb_eq in H3. subst. reflexivity.
  }
  { destruct v, v0.
    * inversion H. subst. simpl. apply eqb_refl.
    * inversion H.
    * inversion H.
    * inversion H. simpl. destruct f. simpl. rewrite eqb_refl, Nat.eqb_refl. simpl. reflexivity.
  }
Qed.

Theorem uequal_neq v0 v:
  uequal v0 v = false <-> v0 <> v.
Proof.
  split; intros.
  { destruct v0, v.
    * simpl in *. apply eqb_neq in H. unfold not in *. intros. apply H. inversion H0. reflexivity.
    * unfold not. intro. inversion H0.
    * unfold not. intro. inversion H0.
    * destruct f, f0. simpl in H. Search andb. apply Bool.andb_false_iff in H. inversion H.
      - apply eqb_neq in H0. unfold not in *. intro. apply H0. inversion H1. reflexivity.
      - apply Nat.eqb_neq in H0. unfold not in *. intro. apply H0. inversion H1. reflexivity.
  }
  { destruct v0, v.
    * simpl in *. apply eqb_neq. unfold not in *. intro. apply H. subst. reflexivity.
    * simpl. reflexivity.
    * simpl. reflexivity.
    * simpl. destruct f, f0. simpl. apply Bool.andb_false_iff. unfold not in H. case_eq ((s =? s0)%string); intros.
      - right. apply eqb_eq in H0. apply Nat.eqb_neq. unfold not. intro. apply H. subst. reflexivity.
      - left. reflexivity.
  }
Qed.

Proposition uequal_refl var :
uequal var var = true.
Proof.
  destruct var.
  * simpl. apply eqb_refl.
  * destruct f. simpl. rewrite eqb_refl, Nat.eqb_refl. simpl. reflexivity.
Qed.

Proposition uequal_sym v1 v2 :
  uequal v1 v2 = uequal v2 v1.
Proof.
  destruct v1, v2.
  * simpl. rewrite eqb_sym. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. destruct f, f0. simpl. rewrite eqb_sym, Nat.eqb_sym. reflexivity.
Qed.

Theorem env_app_get env var val:
get_value (insert_value env var val) var = inl val.
Proof.
  induction env.
  * simpl. rewrite uequal_refl. reflexivity.
  * simpl. destruct a. case_eq (uequal s var).
    - intros. simpl. rewrite uequal_refl. reflexivity.
    - intros. simpl. rewrite uequal_sym in H. rewrite H. exact IHenv.
Qed.

Theorem cl_app_get cl env x :
  get_env_from_closure x (set_closure cl x env) = env.
Proof.
  induction cl.
  * destruct x. simpl. rewrite eqb_refl, Nat.eqb_refl. simpl. reflexivity.
  * simpl. destruct a. case_eq (equal f x).
    - intros. simpl. destruct x. simpl. rewrite eqb_refl, Nat.eqb_refl. simpl. reflexivity.
    - intros. simpl. rewrite H. apply IHcl.
Qed.

Proposition list_variables_not_in x exps :
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

(* Proposition clause_variables x cs:
  ~ (In x (flat_map clause_variables cs)) ->
(forall p gg ee, In (CCons p gg ee) cs -> ~(In x (variables gg)) /\ ~ (In x (variables ee))).
Proof.
  intros. unfold not in *. split; intros; apply H.
  * induction cs.
    - inversion H0.
    - simpl. apply in_or_app. inversion H0.
      + left. subst. simpl. apply in_or_app. left. assumption.
      + right. apply IHcs.
        ** simpl in H. intros. apply H. apply in_or_app. right. assumption.
        ** assumption.
  * induction cs.
    - inversion H0.
    - simpl. apply in_or_app. inversion H0.
      + left. subst. simpl. apply in_or_app. right. assumption.
      + right. apply IHcs.
        ** simpl in H. intros. apply H. apply in_or_app. right. assumption.
        ** assumption.
Qed. *)

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

Proposition irrelevant_append env s t var val:
  s <> var ->
  get_value env (inl s) = t <->
  get_value (append_vars_to_env [var] [val] env) (inl s) = t.
Proof.
  intros; split; intro.
  * simpl. induction env.
    - simpl in *. subst. apply eqb_neq in H. rewrite H. reflexivity.
    - destruct a. assert (get_value ((s0, v) :: env) (inl s) = t). { auto. } unfold get_value in H0. case_eq (uequal (inl s) s0).
      + intro. rewrite H2 in H0. subst. inversion H2. destruct s0.
        ** apply eqb_eq in H3. subst. simpl. apply eqb_neq in H. rewrite H. simpl. rewrite eqb_refl. reflexivity.
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
        ** inversion H1. apply eqb_eq in H3. rewrite H3. apply eqb_neq in H. rewrite H. rewrite H1 in H0. simpl in H0. rewrite H in H0. assumption.
        **  rewrite H1 in H0. simpl in H0. apply eqb_neq in H. rewrite H in H0. assumption.
      + intro. destruct s0.
        ** inversion H1. case_eq ((s =? v0)%string); intro.
          -- rewrite H1 in H0. simpl in H0. rewrite H2 in H0. assumption.
          -- rewrite H1 in H0. simpl in H0. rewrite H2 in H0. exact (IHenv H0).
        ** rewrite H1 in H0. simpl in H0. exact (IHenv H0).
Qed.

Proposition irrelevant_append_eq env s var val:
  s <> var ->
  get_value env (inl s) = get_value (append_vars_to_env [var] [val] env) (inl s).
Proof.
  intros. pose (irrelevant_append env s (get_value env (inl s)) var val H). assert (get_value env (inl s) = get_value env (inl s)). reflexivity. inversion i. pose (H1 H0). apply eq_sym. assumption.
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

Proposition get_value_here env var val:
get_value (insert_value env var val) var = inl val.
Proof.
  induction env.
  * simpl. rewrite uequal_refl. reflexivity.
  * simpl. destruct a. case_eq (uequal s var); intro.
    - simpl. rewrite uequal_refl. reflexivity.
    - simpl. rewrite uequal_sym, H. assumption.
Qed.

Proposition get_value_there env var var' val:
var <> var' ->
get_value (insert_value env var val) var' = get_value env var'.
Proof.
  intro. induction env.
  * simpl. apply uequal_neq in H. rewrite uequal_sym in H. rewrite H. reflexivity.
  * simpl. destruct a. case_eq (uequal s var); intro.
    - apply uequal_eq in H0. assert (var <> var'). auto. rewrite <- H0 in H. apply uequal_neq in H. rewrite uequal_sym in H. rewrite H. simpl. apply uequal_neq in H1. rewrite uequal_sym in H1. rewrite H1. reflexivity.
    - simpl. case_eq (uequal var' s); intros.
      + reflexivity.
      + apply IHenv.
Qed.

End Core_Erlang_Proofs.