Load Core_Erlang_Induction.

Module Core_Erlang_Proofs.

Import Core_Erlang_Syntax.
Import Core_Erlang_Semantics.
Import Core_Erlang_Environment.
Import Core_Erlang_Closures.
Import Core_Erlang_Helpers.
Import Core_Erlang_Induction.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.
Import Coq.Init.Logic.
Import Omega.

Proposition plus_comm_basic (e1 e2 : Value) : eval "plus"%string [e1 ; e2] = eval "plus"%string [e2; e1].
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  1-144: try(reflexivity).
  1-23: try(destruct l); try(destruct l0); try(reflexivity).
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
 (env, cl, exp) -e> v1 ->
 (forall v2 : Value, (env, cl, exp) -e> v2 -> v1 = v2)
  ->
  (env, cl, exp) -e> v2
->
  v1 = v2
.
Proof.
  intros. apply (H0 v2 H1).
Qed.

Lemma index_case_equality (i i0 : nat) env0 cl0 cs v guard guard0 exp exp0 bindings bindings0 : 
  (forall j : nat,
     j < i ->
     match_clause v cs j = None \/
     (forall (gg ee : Expression) (bb : list (Var * Value)),
      match_clause v cs j = Some (gg, ee, bb) ->
      (add_bindings bb env0, cl0, gg) -e> ff /\
      (forall v2 : Value, (add_bindings bb env0, cl0, gg) -e> v2 -> ff = v2)))
  ->
  (forall j : nat,
      j < i0 ->
      match_clause v cs j = None \/
      (forall (gg ee : Expression) (bb : list (Var * Value)),
       match_clause v cs j = Some (gg, ee, bb) -> (add_bindings bb env0, cl0, gg) -e> ff))
  ->
  match_clause v cs i = Some (guard, exp, bindings)
  ->
  match_clause v cs i0 = Some (guard0, exp0, bindings0)
  ->
  (add_bindings bindings0 env0, cl0, guard0) -e> tt
  ->
  (add_bindings bindings env0, cl0, guard) -e> tt 
  ->
  (forall v2 : Value, (add_bindings bindings env0, cl0, guard) -e> v2 -> tt = v2)
->
  i = i0.
Proof.
  intros. pose (Nat.lt_decidable i i0). destruct d.
  * pose (H0 i H6). inversion o.
    - rewrite H7 in *. inversion H1.
    - pose (H7 guard exp bindings H1). pose (determinism_hypo (add_bindings bindings env0) cl0 guard tt ff H4 H5 e). inversion e0.
  * apply not_lt in H6. apply (nat_ge_or) in H6. inversion H6.
    - assumption.
    - pose (H i0 H7). inversion o.
      + rewrite H8 in H2. inversion H2.
      + pose (H8 guard0 exp0 bindings0 H2). inversion a. pose (H10 tt H3). inversion e.
Qed.

Lemma list_equality (env0 : Environment) (cl0 : Closures) (exps : list Expression)  : 
forall vals vals0 : list Value,
  (forall (exp : Expression) (val : Value),
    In (exp, val) (combine exps vals) -> (env0, cl0, exp) -e> val) ->
  (forall (exp : Expression) (val : Value),
    In (exp, val) (combine exps vals) -> forall v2 : Value, (env0, cl0, exp) -e> v2 -> val = v2) ->
  (forall (exp : Expression) (val : Value),
    In (exp, val) (combine exps vals0) -> (env0, cl0, exp) -e> val) ->
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
       forall v2 : Value, (env0, cl0, exp) -e> v2 -> val = v2
    ).
    {
      intros. pose (in_cons (a, x) (exp, val) (combine exps x1) H8). pose (H0 exp val i1 v2 H9). assumption.
    }
    assert (
      forall (exp : Expression) (val : Value),
    In (exp, val) (combine exps x1) -> (env0, cl0, exp) -e> val
    ).
    {
      intros. pose (in_cons (a, x) (exp, val) (combine exps x1) H9). pose (H exp val i1). assumption.
    }
    assert (
      forall (exp : Expression) (val : Value),
     In (exp, val) (combine exps x2) -> (env0, cl0, exp) -e> val
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

Theorem determinism : forall env cl e v1, (env, cl, e) -e> v1 -> (forall v2, (env, cl, e) -e> v2 -> v1 = v2).
Proof.
  intro. intro. intro. intro. intro H. induction H using eval_expr_ind2.
  (* LITERAL, VARIABLE, FUNCTION SIGNATURE, FUNCTION DEFINITION *)
  1-4: intros; inversion H; reflexivity.
  (* TUPLE *)
  * intros. inversion H2. subst. pose (list_equality env0 cl0 exps vals vals0 H0 H1 H8 H H7). rewrite e0. reflexivity.

  (* LIST *)
  * intros. inversion H1. subst. rewrite (IHeval_expr1 hdv0 H7). rewrite (IHeval_expr2 tlv0 H8). reflexivity.

  (* CASE *)
  * intros. inversion H4. subst.
    (* determinism of initial expression *)
    rewrite <- (IHeval_expr1 v0 H9) in *.
    (* determinism of clause selection (i = i0) *)
    pose (index_case_equality i i0 env0 cl0 cs v guard guard0 exp exp0 bindings bindings0 H1 H12 H0 H10 H13 H2 IHeval_expr2). 
    (* Coq Hacking for possible rewrites *)
    pose H10. rewrite <- e1 in e2. pose H0. rewrite e2 in e3. inversion e3. rewrite H6, H7, H8 in *.
    (* clause evaluation *)
    pose (IHeval_expr3 v2 H14). assumption.

  (* CALL *)
  * intros. inversion H3. subst. pose (list_equality env0 cl0 params vals vals0 H0 H1 H10 H H9). rewrite e0. reflexivity.

  (* APPLY *)
  * intros. inversion H4. subst. pose (list_equality env0 cl0 params vals vals0 H1 H2 H12 H H9). rewrite e0 in *.
   (* The equality of the var lists *)
   pose (IHeval_expr1 (VClosure ref0 var_list0 body0) H11). inversion e1. rewrite H6, H7, H8 in *.
   (* equality of the expressions *)
   pose (IHeval_expr2 v2 H13). assumption.

  (* LET *)
  * intros. inversion H3. subst. pose (list_equality env0 cl0 exps vals vals0 H0 H1 H11 (eq_sym H) (eq_sym H10)). rewrite e1 in *.
   pose (IHeval_expr v2 H12). assumption.

  (* LETREC *)
  * intros. inversion H1. subst. pose (IHeval_expr v2 H9). assumption.
  
  (* MAP *)
  * intros. inversion H6. subst.
  (* Key list equality *)
  rewrite H in *.
  pose (list_equality env0 cl0 kl kvals kvals0 H2 H3 H15 H1 H14). rewrite e0 in *.
  (* value list equality *)
  rewrite <- H in *.
  pose (list_equality env0 cl0 vl vvals vvals0 H4 H5 H16 H0 H12). rewrite e1 in *.
  reflexivity.
Qed.

Ltac unfold_list exprs2 n H1 name :=
subst; simpl in H1; pose (name := element_exist Expression n exprs2 (eq_sym H1)); inversion name; inversion H0.

Example call_comm : forall e e' cl env t,
  (env, cl, ECall "plus"%string [e ; e']) -e> t <->
  (env, cl, ECall "plus"%string [e' ; e]) -e> t.
Proof.
  intros. split.
  (* List elements *)
  1-2: intros; inversion H; subst; simpl in H5; pose (element_exist Value 1 vals (eq_sym H5)); inversion e0; inversion H0; subst; simpl in H5; inversion H5; pose (element_exist Value 0 x0 (eq_sym H2)); inversion e1; inversion H1; subst; simpl in H5; inversion H5; apply eq_sym in H4; apply length_zero_iff_nil in H4; subst;
  (* equivalence *)
  apply eval_call with ([x1;x]).
    1, 4: reflexivity.
    1, 3: intros.
    { inversion H3.
        inversion H4. rewrite H8, H9 in *. apply H6. simpl. intuition.
        
        inversion H4.
        inversion H7. rewrite H9, H10 in *. apply H6. simpl. intuition.
        inversion H7.
      }
    2, 3 : apply plus_comm_basic.
    { inversion H3.
        inversion H4. rewrite H8, H9 in *. apply H6. simpl. intuition.
        
        inversion H4.
        inversion H7. rewrite H9, H10 in *. apply H6. simpl. intuition.
        inversion H7.
      }
Qed.

Example let_1_comm (e1 e2 : Expression) (t : Value) :
  ([], [], ELet ["X"%string] [e1] (ECall "plus"%string [EVar "X"%string ; e2])) -e> t <->
  ([], [], ELet ["X"%string] [e1] (ECall "plus"%string [e2 ; EVar "X"%string])) -e> t.
Proof.
  split; intros.
  * inversion H. subst. inversion H6. pose (element_exist Value 0 vals H6). inversion e. inversion H0. subst. inversion H6. apply length_zero_iff_nil in H3. subst.
  apply eval_let with (vals := [x]).
    - reflexivity.
    - intros. inversion H2. inversion H3. subst. apply H7. assumption. inversion H3.
    - apply call_comm. assumption.
  * inversion H. subst. inversion H6. pose (element_exist Value 0 vals H6). inversion e. inversion H0. subst. inversion H6. apply length_zero_iff_nil in H3. subst.
  apply eval_let with (vals := [x]).
    - reflexivity.
    - intros. inversion H2. inversion H3. subst. apply H7. assumption. inversion H3.
    - apply call_comm. assumption.
Qed.

Example call_comm_ex : forall e e' cl env t t',
  (env, cl, ECall "plus"%string [e ; e']) -e> t ->
  (env, cl, ECall "plus"%string [e' ; e]) -e> t' ->
  t = t'.
Proof.
  intros. apply call_comm in H. pose (determinism env cl (ECall "plus" [e' ; e]) t H t' H0). assumption.
Qed.

(* For the next examples, additional theorems were needed *)

(* Theorem env_permutation env env' cl e t:
(env, cl, e) -e> t -> length env = length env' ->
(forall elem, In elem env -> In elem env') ->
(env', cl, e) -e> t.
Proof.


Admitted.

Theorem unused_variable_modification env cl e e' v t:
 (env, cl, e) -e> t -> ~ In v (variables e) ->
 (append_vars_to_env [v] [e'] env, append_vars_to_closure [v] [e'] cl env, e) -e> t.
Proof.
  intros. induction e.
  * inversion H. apply eval_lit.
  * inversion H. subst.
Admitted.

Theorem unused_variable_modification_back env cl e e' v t:
 ~ In v (variables e) ->
 (append_vars_to_env [v] [e'] env, append_vars_to_closure [v] [e'] cl env, e) -e> t ->
 (env, cl, e) -e> t.
Proof.
Admitted. *)

Example let_2_comm_concrete (e1 e2 : Expression) (t : Value) :
  ([], [], ELet ["X"%string] [ELiteral (Integer 5)] (ELet ["Y"%string] [ELiteral (Integer 6)] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]))) -e> t
<->
([], [], ELet ["X"%string] [ELiteral (Integer 6)] (ELet ["Y"%string] [ELiteral (Integer 5)] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]))) -e> t
.
Proof.
  split; intros.
  (*let value lists elements*)
  * inversion H. subst. simpl in H6. pose (element_exist Value 0 vals H6). inversion e. inversion H0. subst. inversion H6. apply length_zero_iff_nil in H2. subst. assert (x = VLiteral (Integer 5)).
  {
    assert (In ((ELiteral (Integer 5)), x) (combine [ELiteral (Integer 5)] [x])). simpl. auto.
    pose (H7 (ELiteral (Integer 5)) x H1). inversion e0. reflexivity.
  }
  subst. simpl in *. inversion H8. subst.
  simpl in H10. pose (element_exist Value 0 vals H10). inversion e0. inversion H1. subst. inversion H10. apply length_zero_iff_nil in H3. subst. assert (x = VLiteral (Integer 6)).
  {
    assert (In ((ELiteral (Integer 6)), x) (combine [ELiteral (Integer 6)] [x])). simpl. auto.
    pose (H11 (ELiteral (Integer 6)) x H2). inversion e3. reflexivity.
  }
  subst. simpl in *. inversion H12. subst.
  (* let evaluation *)
  apply eval_let with (vals := [VLiteral (Integer 6)]).
  - reflexivity.
  - intros. inversion H2; inversion H3. apply eval_lit.
  - apply eval_let with (vals := [VLiteral (Integer 5)]).
    + reflexivity.
    + intros. inversion H2; inversion H3. apply eval_lit.
    + apply eval_call with (vals := [VLiteral (Integer 6); VLiteral (Integer 5)]).
      ** reflexivity.
      ** intros. inversion H2.
        -- inversion H3. apply eval_var.
        -- inversion H3; inversion H4. apply eval_var.
      ** simpl append_vars_to_env.

      (* Call value list elements *)
      inversion H13. pose (element_exist Value 1 vals (eq_sym H3)). inversion e3. inversion H2. subst. inversion H3. pose (element_exist Value 0 x0 (eq_sym H5)). inversion e4. inversion H4. subst. inversion H3. apply eq_sym, length_zero_iff_nil in H15. subst.

      (* Back to the original goal *)
      assert (x = VLiteral (Integer 5) /\ x1 = VLiteral (Integer 6)).
      {
         assert (In ((EVar "X"%string), x) (combine [EVar "X"%string ; EVar "Y"%string] [x ; x1])). simpl. auto.
         assert (In ((EVar "Y"%string), x1) (combine [EVar "X"%string ; EVar "Y"%string] [x ; x1])). simpl. auto.
        pose (H14 (EVar "X"%string) x H9).
        pose (H14 (EVar "Y"%string) x1 H15).
        inversion e5. inversion e6. simpl. auto.
      }
      inversion H9. subst. simpl. reflexivity.
  * inversion H. subst. simpl in H6. pose (element_exist Value 0 vals H6). inversion e. inversion H0. subst. inversion H6. apply length_zero_iff_nil in H2. subst. assert (x = VLiteral (Integer 6)).
  {
    assert (In ((ELiteral (Integer 6)), x) (combine [ELiteral (Integer 6)] [x])). simpl. auto.
    pose (H7 (ELiteral (Integer 6)) x H1). inversion e0. reflexivity.
  }
  subst. simpl in *. inversion H8. subst.
  simpl in H10. pose (element_exist Value 0 vals H10). inversion e0. inversion H1. subst. inversion H10. apply length_zero_iff_nil in H3. subst. assert (x = VLiteral (Integer 5)).
  {
    assert (In ((ELiteral (Integer 5)), x) (combine [ELiteral (Integer 5)] [x])). simpl. auto.
    pose (H11 (ELiteral (Integer 5)) x H2). inversion e3. reflexivity.
  }
  subst. simpl in *. inversion H12. subst.
  (* let evaluation *)
  apply eval_let with (vals := [VLiteral (Integer 5)]).
  - reflexivity.
  - intros. inversion H2; inversion H3. apply eval_lit.
  - apply eval_let with (vals := [VLiteral (Integer 6)]).
    + reflexivity.
    + intros. inversion H2; inversion H3. apply eval_lit.
    + apply eval_call with (vals := [VLiteral (Integer 5); VLiteral (Integer 6)]).
      ** reflexivity.
      ** intros. inversion H2.
        -- inversion H3. apply eval_var.
        -- inversion H3; inversion H4. apply eval_var.
      ** simpl append_vars_to_env.

      (* Call value list elements *)
      inversion H13. pose (element_exist Value 1 vals (eq_sym H3)). inversion e3. inversion H2. subst. inversion H3. pose (element_exist Value 0 x0 (eq_sym H5)). inversion e4. inversion H4. subst. inversion H3. apply eq_sym, length_zero_iff_nil in H15. subst.

      (* Back to the original goal *)
      assert (x = VLiteral (Integer 6) /\ x1 = VLiteral (Integer 5)).
      {
         assert (In ((EVar "X"%string), x) (combine [EVar "X"%string ; EVar "Y"%string] [x ; x1])). simpl. auto.
         assert (In ((EVar "Y"%string), x1) (combine [EVar "X"%string ; EVar "Y"%string] [x ; x1])). simpl. auto.
        pose (H14 (EVar "X"%string) x H9).
        pose (H14 (EVar "Y"%string) x1 H15).
        inversion e5. inversion e6. simpl. auto.
      }
      inversion H9. subst. simpl. reflexivity.
Qed.

End Core_Erlang_Proofs.