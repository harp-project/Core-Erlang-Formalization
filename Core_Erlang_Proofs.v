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
 |env, cl, exp| -e> v1 ->
 (forall v2 : Value, |env, cl, exp| -e> v2 -> v1 = v2)
  ->
  |env, cl, exp| -e> v2
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
      |add_bindings bb env0, cl0, gg| -e> ffalse /\
      (forall v2 : Value, |add_bindings bb env0, cl0, gg| -e> v2 -> ffalse = v2)))
  ->
  (forall j : nat,
      j < i0 ->
      match_clause v cs j = None \/
      (forall (gg ee : Expression) (bb : list (Var * Value)),
       match_clause v cs j = Some (gg, ee, bb) -> |add_bindings bb env0, cl0, gg| -e> ffalse))
  ->
  match_clause v cs i = Some (guard, exp, bindings)
  ->
  match_clause v cs i0 = Some (guard0, exp0, bindings0)
  ->
  |add_bindings bindings0 env0, cl0, guard0| -e> ttrue
  ->
  |add_bindings bindings env0, cl0, guard| -e> ttrue
  ->
  (forall v2 : Value, |add_bindings bindings env0, cl0, guard| -e> v2 -> ttrue = v2)
->
  i = i0.
Proof.
  intros. pose (Nat.lt_decidable i i0). destruct d.
  * pose (H0 i H6). inversion o.
    - rewrite H7 in *. inversion H1.
    - pose (H7 guard exp bindings H1). pose (determinism_hypo (add_bindings bindings env0) cl0 guard ttrue ffalse H4 H5 e). inversion e0.
  * apply not_lt in H6. apply (nat_ge_or) in H6. inversion H6.
    - assumption.
    - pose (H i0 H7). inversion o.
      + rewrite H8 in H2. inversion H2.
      + pose (H8 guard0 exp0 bindings0 H2). inversion a. pose (H10 ttrue H3). inversion e.
Qed.

Lemma list_equality (env0 : Environment) (cl0 : Closures) (exps : list Expression)  : 
forall vals vals0 : list Value,
  (forall (exp : Expression) (val : Value),
    In (exp, val) (combine exps vals) -> |env0, cl0, exp| -e> val) ->
  (forall (exp : Expression) (val : Value),
    In (exp, val) (combine exps vals) -> forall v2 : Value, |env0, cl0, exp| -e> v2 -> val = v2) ->
  (forall (exp : Expression) (val : Value),
    In (exp, val) (combine exps vals0) -> |env0, cl0, exp| -e> val) ->
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
       forall v2 : Value, |env0, cl0, exp| -e> v2 -> val = v2
    ).
    {
      intros. pose (in_cons (a, x) (exp, val) (combine exps x1) H8). pose (H0 exp val i1 v2 H9). assumption.
    }
    assert (
      forall (exp : Expression) (val : Value),
    In (exp, val) (combine exps x1) -> |env0, cl0, exp| -e> val
    ).
    {
      intros. pose (in_cons (a, x) (exp, val) (combine exps x1) H9). pose (H exp val i1). assumption.
    }
    assert (
      forall (exp : Expression) (val : Value),
     In (exp, val) (combine exps x2) -> |env0, cl0, exp| -e> val
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

Theorem determinism : forall env cl e v1, |env, cl, e| -e> v1 -> (forall v2, |env, cl, e| -e> v2 -> v1 = v2).
Proof.
  intro. intro. intro. intro. intro H. induction H using eval_expr_ind_extended.
  (* LITERAL, VARIABLE, FUNCTION SIGNATURE, FUNCTION DEFINITION *)
  1-4: intros; inversion H; reflexivity.
  (* TUPLE *)
  * intros. inversion H2. subst. pose (list_equality env cl exps vals vals0 H0 H1 H7 H H4). rewrite e. reflexivity.

  (* LIST *)
  * intros. inversion H1. subst. rewrite (IHeval_expr1 hdv0 H6). rewrite (IHeval_expr2 tlv0 H8). reflexivity.

  (* CASE *)
  * intros. inversion H4. subst.
    (* determinism of initial expression *)
    rewrite <- (IHeval_expr1 v0 H7) in *.
    (* determinism of clause selection (i = i0) *)
    pose (index_case_equality i i0 env cl cs v guard guard0 exp exp0 bindings bindings0 H1 H9 H0 H8 H12 H2 IHeval_expr2).
    (* Coq Hacking for possible rewrites *)
    pose H8. rewrite <- e0 in e1. pose H0. rewrite e1 in e2. inversion e2. rewrite H6, H10, H11 in *.
    (* clause evaluation *)
    pose (IHeval_expr3 v2 H14). assumption.

  (* CALL *)
  * intros. inversion H3. subst. pose (list_equality env cl params vals vals0 H0 H1 H9 H H6). rewrite e. reflexivity.

  (* APPLY *)
  * intros. inversion H4. subst. pose (list_equality env cl params vals vals0 H1 H2 H11 H H7). rewrite e in *.
   (* The equality of the var lists *)
   pose (IHeval_expr1 (VClosure ref0 var_list0 body0) H8). inversion e0. rewrite H6, H9, H10 in *.
   (* equality of the expressions *)
   pose (IHeval_expr2 v2 H13). assumption.

  (* LET *)
  * intros. inversion H3. subst. pose (list_equality env cl exps vals vals0 H0 H1 H11 (eq_sym H) (eq_sym H9)). rewrite e0 in *.
   pose (IHeval_expr v2 H12). assumption.

  (* LETREC *)
  * intros. inversion H1. subst. pose (IHeval_expr v2 H9). assumption.
  
  (* MAP *)
  * intros. inversion H6. subst.
  (* Key list equality *)
  rewrite H in *.
  pose (list_equality env cl kl kvals kvals0 H2 H3 H14 H1 H11). rewrite e in *.
  (* value list equality *)
  rewrite <- H in *.
  pose (list_equality env cl vl vvals vvals0 H4 H5 H16 H0 H10). rewrite e0 in *.
  reflexivity.
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
get_value (insert_value env var val) var = val.
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

Proposition clause_variables x cs:
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
Qed.

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
get_value (insert_value env var val) var = val.
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