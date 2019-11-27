Load Core_Erlang_Semantics.

Module Core_Erlang_Proofs.

Import Core_Erlang_Syntax.
Import Core_Erlang_Semantics.
Import Core_Erlang_Environment.
Import Core_Erlang_Closures.
Import Core_Erlang_Helpers.
Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.
Import Coq.Init.Logic.
Import Omega.

Lemma plus_comm_basic (e1 e2 : Expression) (env : Environment) : eval env ("plus"%string, 2) [e1 ; e2] = eval env ("plus"%string, 2) [e2; e1].
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  1-169: try(reflexivity).
  1-25: try(destruct l); try(destruct l0); try(reflexivity).
  * rewrite <- Z.add_comm. reflexivity.
Qed.

Lemma ttt : forall p : Prop, True \/ p = True.
Proof.
  auto.
Qed.

Lemma value_consistency : forall v : Value, (proj1_sig v) val.
Proof.
  intros. pose (proj2_sig v). simpl in v0. exact v0.
Qed.

Check eval_expr_ind.
  
Section inductions.
  Axiom eval_expr_ind2
     : forall P : Environment * Closures * Expression -> Expression -> Prop,
       (forall (env : Environment) (s : Var) (cl : Closures),
        P (env, cl, EVar s) (proj1_sig (get_value env (inl s)))) ->
        
        
       (forall (env : Environment) (exprs1 exprs2 : list Expression) (cl : Closures),
        Datatypes.length exprs1 = Datatypes.length exprs2 ->
        (forall exp exp' : Expression,
         In (exp, exp') (combine exprs1 exprs2) ->
         ((env, cl, exp) -e> exp' \/ exp = exp') /\ exp' val /\
         P (env, cl, exp) exp') ->
        ETuple exprs1 <> ETuple exprs2 -> P (env, cl, ETuple exprs1) (ETuple exprs2)) ->
        
        
       (forall (env : Environment) (hd tl e' e'' : Expression) (cl : Closures),
        ((env, cl, hd) -e> e' \/ hd = e') /\ e' val /\ P (env, cl, hd) e' ->
        ((env, cl, tl) -e> e'' \/ tl = e'') /\ e'' val /\ P (env, cl, tl) e'' ->
        EList hd tl <> EList e' e'' -> P (env, cl, EList hd tl) (EList e' e'')) ->
        
        
       (forall (env : Environment) (e' : Expression) (params exprs2 : list Expression)
          (fname : FunctionSignature) (cl : Closures),
        Datatypes.length params = Datatypes.length exprs2 ->
        (forall exp exp' : Expression,
         In (exp, exp') (combine params exprs2) ->
         ((env, cl, exp) -e> exp' \/ exp = exp') /\ exp' val /\
         P (env, cl, exp) exp') ->
        eval env fname exprs2 = e' /\ e' val -> P (env, cl, ECall fname params) e') ->
        
        
        
       (forall (exprs1 : list Expression) (exprs2 : list Value) (env : Environment)
          (name : string) (args : nat) (e' : Expression) (cl : Closures),
        Datatypes.length exprs1 = Datatypes.length exprs2 ->
        Datatypes.length exprs1 = args ->
        (forall (exp : Expression) (exp' : Value),
         In (exp, exp') (combine exprs1 exprs2) ->
         ((env, cl, exp) -e> proj1_sig exp' \/ exp = proj1_sig exp') /\
         P (env, cl, exp) (proj1_sig exp')) ->
        ((append_vars_to_env (get_vars (get_value env (inr (name, args)))) exprs2
            (get_env_from_closure (inr (name, args)) cl), cl,
         get_fun_exp (get_value env (inr (name, args)))) -e> e' \/
         get_fun_exp (get_value env (inr (name, args))) = e') /\ e' val ->
         P (append_vars_to_env (get_vars (get_value env (inr (name, args)))) exprs2
            (get_env_from_closure (inr (name, args)) cl), cl,
         get_fun_exp (get_value env (inr (name, args)))) e' ->
        P (env, cl, EApplyTopLevel (name, args) exprs1) e') ->
        
        
        
       (forall (exprs1 : list Expression) (exprs2 : list Value) (env : Environment) 
          (name : Var) (e' : Expression) (cl : Closures),
        Datatypes.length exprs1 = Datatypes.length exprs2 ->
        (forall (exp : Expression) (exp' : Value),
         In (exp, exp') (combine exprs1 exprs2) ->
         ((env, cl, exp) -e> proj1_sig exp' \/ exp = proj1_sig exp') /\ P (env, cl, exp) (proj1_sig exp')) ->
        ((append_vars_to_env (get_vars (get_value env (inl name))) exprs2
            (get_env_from_closure (inl name) cl), cl, get_fun_exp (get_value env (inl name))) -e>
         e' \/ get_fun_exp (get_value env (inl name)) = e') /\ e' val ->
         P (append_vars_to_env (get_vars (get_value env (inl name))) exprs2
            (get_env_from_closure (inl name) cl), cl, get_fun_exp (get_value env (inl name))) e'
         ->
        P (env, cl, EApply name exprs1) e') ->
        
        
        
       (forall (env : Environment) (exps : list Expression) (exprs2 : list Value)
          (vars : list Var) (e e' : Expression) (cl : Closures),
        Datatypes.length exprs2 = Datatypes.length exps ->
        (forall (exp : Expression) (exp' : Value),
         In (exp, exp') (combine exps exprs2) ->
         ((env, cl, exp) -e> proj1_sig exp' \/ exp = proj1_sig exp')
         /\ P (env, cl, exp) (proj1_sig exp')) ->
        ((append_vars_to_env vars exprs2 env,
         append_vars_to_closure vars (valuelist_to_exp exprs2) cl env, e) -e> e' \/ 
         e = e') /\ e' val ->
         P (append_vars_to_env vars exprs2 env,
         append_vars_to_closure vars (valuelist_to_exp exprs2) cl env, e) e' ->
          P (env, cl, ELet vars exps e) e') ->
         
         
         
         
       (forall (env : Environment) (e e' : Expression) (fnames : list FunctionSignature)
          (funs : list Fun) (cl : Closures),
        Datatypes.length funs = Datatypes.length fnames ->
        ((append_funs_to_env fnames funs env,
         append_funs_to_closure fnames cl (append_funs_to_env fnames funs env), e) -e> e' \/
         e = e') /\ e' val ->
         P (append_funs_to_env fnames funs env,
         append_funs_to_closure fnames cl (append_funs_to_env fnames funs env), e) e'
         -> P (env, cl, ELetrec fnames funs e) e') ->
         
         
         
         
         
       (forall (kl vl : list Expression) (exprs2 : list Value) (env : Environment) (cl : Closures),
        (forall exp : Expression, In exp kl -> exp val) ->
        Datatypes.length vl = Datatypes.length kl ->
        Datatypes.length vl = Datatypes.length exprs2 ->
        (forall (exp : Expression) (exp' : Value),
         In (exp, exp') (combine vl exprs2) ->
         ((env, cl, exp) -e> proj1_sig exp' \/ exp = proj1_sig exp') /\ P (env, cl, exp) (proj1_sig exp')) ->
        P (env, cl, EMap kl vl) (EMap kl (valuelist_to_exp exprs2))) ->
       forall (p : Environment * Closures * Expression) (e : Expression), p -e> e -> P p e.

End inductions.

Check eval_expr_ind2.

Theorem andd A B C : A -> B /\ C -> A -> B.
Proof.
  intros. inversion H. assumption.
Qed.

Lemma in_combined_list : forall P : Prop, forall l l' a b,
  (forall e e' : Expression,
    In (e, e') ((a, b) :: combine l l') -> P) -> 
  (forall e e' : Expression,
    In (e, e') (combine l l') -> P).
Proof.
  intros. pose (in_cons (a, b) (e, e') (combine l l') H0). pose (H e e' i). assumption.
Qed.

Lemma trans_exp_list_equal : forall exprs exprs2 env cl,
  (forall exp : Expression,
    In exp exprs -> forall t : Expression, (env, cl, exp) -e> t -> False) ->
  (forall exp exp' : Expression,
     In (exp, exp') (combine exprs exprs2) -> ((env, cl, exp) -e> exp' \/ exp = exp') /\ exp' val) ->
   length exprs = length exprs2 ->
exprs = exprs2.
Proof.
  induction exprs; intros.
  * inversion H1. apply eq_sym in H3. apply length_zero_iff_nil in H3. rewrite H3. reflexivity.
  * inversion H1. apply eq_sym in H3. pose (element_exist Expression (Datatypes.length exprs) exprs2 H3). inversion e. inversion H2. rewrite H4 in *.
  
  (* exprs = x0 *)
  pose (IHexprs x0 env cl). simpl combine in H0. assert (
    forall exp exp' : Expression,
     In (exp, exp') (combine exprs x0) ->
     ((env, cl, exp) -e> exp' \/ exp = exp') /\ exp' val
  ).
  {
    intros. pose (in_cons (a, x) (exp, exp') (combine exprs x0) H5). apply (H0 exp exp' i).
  }
  assert (
    forall exp : Expression,
    In exp (exprs) -> forall t : Expression, (env, cl, exp) -e> t -> False
  ).
  {
    intros. pose (in_cons a exp exprs H6). apply (H exp i t). assumption.
  }
  inversion H1. pose (e0 H6 H5 H8). rewrite e1 in *.
  (* a = x *)
  pose (in_eq (a,x) (combine x0 x0)). pose (H0 a x i). inversion a0. inversion H7.
  - pose (in_eq a x0). pose (H a i0). pose (f x H10). inversion f0.
  - rewrite H10 in *. reflexivity.
Qed.

Lemma trans_val_list_equal : forall vl exprs2 env cl,
  (forall exp : Expression,
    In exp vl -> forall t : Expression, (env, cl, exp) -e> t -> False) ->
  (forall (exp : Expression) (exp' : Value),
      In (exp, exp') (combine vl exprs2) ->
      (env, cl, exp) -e> proj1_sig exp' \/ exp = proj1_sig exp') ->
   length vl = length exprs2 ->
vl = valuelist_to_exp exprs2.
Proof.
  induction vl; intros.
  * inversion H1. apply eq_sym in H3. apply length_zero_iff_nil in H3. rewrite H3. reflexivity.
  * inversion H1. apply eq_sym in H3. pose (element_exist Value (Datatypes.length vl) exprs2 H3). inversion e. inversion H2. rewrite H4 in *.
  
  (* exprs = x0 *)
  pose (IHvl x0 env cl). simpl combine in H0. assert (
    forall exp exp',
     In (exp, exp') (combine vl x0) ->
     ((env, cl, exp) -e> proj1_sig exp' \/ exp = proj1_sig exp')
  ).
  {
    intros. pose (in_cons (a, x) (exp, exp') (combine vl x0) H5). apply (H0 exp exp' i).
  }
  assert (
    forall exp : Expression,
    In exp (vl) -> forall t : Expression, (env, cl, exp) -e> t -> False
  ).
  {
    intros. pose (in_cons a exp vl H6). apply (H exp i t). assumption.
  }
  inversion H1. pose (e0 H6 H5 H8). rewrite e1 in *.
  (* a = x *)
  pose (in_eq (a,x) (combine (valuelist_to_exp x0) x0)). pose (H0 a x i). inversion o.
  - pose (in_eq a (valuelist_to_exp x0)). pose (H a i0). pose (f (proj1_sig x) H7). inversion f0.
  - rewrite H7 in *. reflexivity.
Qed.

Theorem val_no_trans : forall v, v val -> (forall env cl t, ~ (env, cl, v) -e> t).
Proof.
  unfold not. intro v. intro H. intros env. intro cl. induction H; intros.
  * inversion H.
  * inversion H.
  * inversion H1. subst. inversion H7. inversion H8. inversion H2.
    - apply (IHValueJudgement1 e' H6).
    - inversion H4.
      + apply (IHValueJudgement2 e'' H10).
      + subst. intuition.
  * inversion H1. pose (trans_exp_list_equal exprs exprs2 env cl H0 H7 H5). rewrite e in *. intuition.
  * inversion H1. pose (trans_val_list_equal vl exprs2 env cl H0 H10 H9). rewrite e in *. intuition.
Qed.

Lemma list_equality : 
forall env cl, forall l l1 l2 : list Expression,
(forall e e' : Expression, In (e, e') (combine l l1) -> (
  (env, cl, e) -e> e' \/ e = e') /\
  e' val /\
  (forall e2 : Expression, (env, cl, e) -e> e2 -> e' = e2)) ->
  
(forall e e' : Expression, In (e, e') (combine l l2) -> ((env, cl, e) -e> e' \/ e = e') /\ e' val) ->

length l = length l1 -> length l = length l2 ->

l1 = l2.
Proof.
  intro. intro. intro. induction l; intros.
  * inversion H1. inversion H2. apply eq_sym in H4. apply eq_sym in H5. apply length_zero_iff_nil in H4. apply length_zero_iff_nil in H5. subst. reflexivity.
  * inversion H1. apply eq_sym in H4. pose (element_exist Expression (Datatypes.length l) l1 H4). inversion e. inversion H3. subst. inversion H2. apply eq_sym in H6. pose (element_exist Expression (Datatypes.length l) l2 H6). inversion e0. inversion H5. subst.
  
  pose (IHl x0 x2). simpl combine in H. simpl combine in H0. assert (
    forall e e' : Expression,
    In (e, e') (combine l x0) ->
    ((env, cl, e) -e> e' \/ e = e') /\
    e' val /\ (forall e2 : Expression, (env, cl, e) -e> e2 -> e' = e2)
  ).
  {
    intros. pose (in_cons (a, x) (e2, e') (combine l x0) H7). apply (H e2 e' i).
  }
  assert (
    forall e e' : Expression,
     In (e, e') (combine l x2) -> ((env, cl, e) -e> e' \/ e = e') /\ e' val
  ).
  {
    intros. pose (in_cons (a, x1) (e2, e') (combine l x2) H8). apply (H0 e2 e' i).
  }
  inversion H1. inversion H2.
  pose (IHl x0 x2 H7 H8 H10 H11). rewrite e2 in *.
  
  
  pose (H0 a x1). pose (H a x).
  
  simpl combine in a0.
  pose (in_eq (a, x1) (combine l x2)). pose (a0 i). inversion a2.
  
  simpl combine in a1.
  pose (in_eq (a, x) (combine l x2)). pose (a1 i0). inversion a3. inversion H14. inversion H9.
  - pose (H16 x1 H17). rewrite e3 in *. reflexivity.
  - rewrite <- H17 in *. inversion H13.
    + pose (val_no_trans a H12 env cl x H18). inversion f. (*no_va_trans-zal menne*)
    + rewrite H18. reflexivity.
Qed.

(* Lemma val_unique : forall e e' : Expression, e val -> e' val ->  *)

Axiom value_eq : forall v1 v2 : Value, proj1_sig v1 = proj1_sig v2 -> v1 = v2.

Lemma val_list_equality : 
forall env cl, forall l : list Expression, forall l1 l2 : list Value,
(forall e e', In (e, e') (combine l l1) -> (
  (env, cl, e) -e> proj1_sig e' \/ e = proj1_sig e') /\
  
  (forall e2 : Expression, (env, cl, e) -e> e2 -> proj1_sig e' = e2)) ->
  
(forall e e', In (e, e') (combine l l2) -> ((env, cl, e) -e> proj1_sig e' \/ e = proj1_sig e')) ->

length l = length l1 -> length l = length l2 ->

l1 = l2.
Proof.
  intro. intro. intro. induction l; intros.
  * inversion H1. inversion H2. apply eq_sym in H4. apply eq_sym in H5. apply length_zero_iff_nil in H4. apply length_zero_iff_nil in H5. subst. reflexivity.
  * inversion H1. apply eq_sym in H4. pose (element_exist Value (Datatypes.length l) l1 H4). inversion e. inversion H3. subst. inversion H2. apply eq_sym in H6. pose (element_exist Value (Datatypes.length l) l2 H6). inversion e0. inversion H5. subst.
  
  pose (IHl x0 x2). simpl combine in H. simpl combine in H0. assert (
    forall e e',
    In (e, e') (combine l x0) ->
    ((env, cl, e) -e> proj1_sig e' \/ e = proj1_sig e') /\
    (forall e2 : Expression, (env, cl, e) -e> e2 -> proj1_sig e' = e2)
  ).
  {
    intros. pose (in_cons (a, x) (e2, e') (combine l x0) H7). apply (H e2 e' i).
  }
  assert (
    forall e e',
     In (e, e') (combine l x2) -> ((env, cl, e) -e> proj1_sig e' \/ e = proj1_sig e')
  ).
  {
    intros. pose (in_cons (a, x1) (e2, e') (combine l x2) H8). apply (H0 e2 e' i).
  }
  inversion H1. inversion H2.
  pose (IHl x0 x2 H7 H8 H10 H11). rewrite e2 in *.
  
  
  pose (H0 a x1). pose (H a x).
  
  simpl combine in a0.
  pose (in_eq (a, x) (combine l x2)). pose (a0 i). inversion a1.
  
  simpl combine in o.
  pose (in_eq (a, x1) (combine l x2)). pose (o i0). inversion o0.
  - pose (H12 (proj1_sig x1) H13). pose (value_eq x x1 e3). rewrite e4 in *. reflexivity.
  - rewrite <- H13 in *. inversion H9.
    + rewrite H13 in H14. pose (val_no_trans (proj1_sig x1) (proj2_sig x1) env cl (proj1_sig x) H14). inversion f. (*no_va_trans-zal menne*)
    + rewrite H13 in *. pose (value_eq x1 x H14). rewrite e3. reflexivity.
Qed.

Theorem determinism : forall env cl e v1, (env, cl, e) -e> v1 -> (forall v2, (env, cl, e) -e> v2 -> v1 = v2).
Proof.
  intro. intro. intro. intro. intro H. induction H using eval_expr_ind2.
  (* VARIABLE *)
  * intros. inversion H. reflexivity.

  (* TUPLE *)
  * intros. case_eq (combine exprs1 exprs2).
    - intros. inversion H2. pose (combine_split exprs1 exprs2 H). pose (combine_split exprs1 exprs3 H7). rewrite H3 in *. inversion e0. subst. intuition.
    - intros. inversion H2. subst. pose (list_equality env0 cl0 exprs1 exprs2 exprs3 H0 H9 H H7). rewrite e0 in *. reflexivity.

  (* LIST *)
  * intros. inversion H. inversion H0. inversion H4. inversion H6. inversion H2. subst. inversion H17. inversion H16. inversion H11.
    - pose (H10 e''0 H15). rewrite e0 in *. inversion H13.
      + pose (H8 e'0 H19). rewrite e1 in *. reflexivity.
      + rewrite <- H19 in *. inversion H3.
        ** pose (val_no_trans hd H14 env0 cl0  e' H20). inversion f.
        ** rewrite <- H20 in *. reflexivity.
    - rewrite <- H15 in *. inversion H13.
      + pose (H8 e'0 H19). rewrite e0 in *. inversion H5.
        ** pose (val_no_trans tl H12 env0 cl0 e'' H20). inversion f.
        ** rewrite H20 in *. reflexivity.
      + subst. unfold not in H18. assert (EList e'0 e''0 = EList e'0 e''0). reflexivity. pose (H18 H15). inversion f.

  (* CALL *)
  * intros. case_eq (combine params exprs2).
    - intros. inversion H2. pose (combine_split params exprs2 H). pose (combine_split params exprs0 H9). rewrite H3 in *. inversion e0. subst. inversion H1. inversion H11. inversion H9. apply eq_sym in H12. apply length_zero_iff_nil in H12. subst. reflexivity.
    - intros. inversion H2. pose (list_equality env0 cl0 params exprs2 exprs0 H0 H10 H H9). rewrite e0 in *. inversion H1. inversion H11. rewrite <- H12. rewrite <- H14. reflexivity.

  (* TOP LEVEL APPLY *)
  * intros. case_eq (combine exprs1 exprs2).
    - intros. inversion H3. subst. pose (combine_split exprs1 exprs3 H11). pose (combine_split exprs1 exprs2 H). rewrite H4 in *. inversion e1. subst. inversion H11. apply eq_sym in H5. apply length_zero_iff_nil in H5. subst. simpl in *. inversion H14. inversion H0.
      + pose (IHeval_expr v2 H6). exact e2.
      + rewrite H6 in *. inversion H2. inversion H7.
        ** apply (val_no_trans) in H9. inversion H9. exact H5.
        ** apply eq_sym in H9. exact H9.
   - intros. inversion H3. subst. pose (val_list_equality env0 cl0 exprs1 exprs2 exprs3 H1 H13 H H11). rewrite e0 in *. inversion H2. inversion H14. inversion H6.
     + pose (IHeval_expr v2 H8). exact e1.
     + rewrite H8 in *. inversion H2. inversion H9.
        ** apply (val_no_trans) in H15. inversion H15. exact H7.
        ** apply eq_sym in H15. exact H15.
        
  (* APPLY *)
  * intros. case_eq (combine exprs1 exprs2).
    - intros. inversion H2. subst. pose (combine_split exprs1 exprs3 H9). pose (combine_split exprs1 exprs2 H). rewrite H3 in *. inversion e1. subst. inversion H9. apply eq_sym in H5. apply length_zero_iff_nil in H5. subst. simpl in *. inversion H11. inversion H1. inversion H4.
      + pose (IHeval_expr v2 H8). exact e2.
      + rewrite H8 in *. inversion H6.
        ** apply (val_no_trans) in H12. inversion H12. exact H5.
        ** apply eq_sym in H12. exact H12.
   - intros. inversion H2. subst. pose (val_list_equality env0 cl0 exprs1 exprs2 exprs3 H0 H10 H H9). rewrite e0 in *. inversion H1. inversion H11. inversion H6.
     + pose (IHeval_expr v2 H8). exact e1.
     + rewrite H8 in *. inversion H4.
        ** apply (val_no_trans) in H12. inversion H12. exact H7.
        ** apply eq_sym in H12. exact H12.
  
  (* LET *)
  * intros. case_eq (combine exps exprs2).
    - intros. inversion H2. subst. apply eq_sym in H10. apply eq_sym in H. pose (combine_split exps exprs0 H10). pose (combine_split exps exprs2 H). rewrite H3 in *. inversion e2. subst. inversion H10. apply eq_sym in H5. apply length_zero_iff_nil in H5. subst. simpl in *. inversion H12. inversion H1. inversion H4.
      + pose (IHeval_expr v2 H8). exact e3.
      + rewrite H8 in *. inversion H6.
        ** apply (val_no_trans) in H9. inversion H9. exact H5.
        ** apply eq_sym in H9. exact H9.
   - intros. inversion H2. subst. pose (val_list_equality env0 cl0 exps exprs2 exprs0 H0 H11 (eq_sym H) (eq_sym H10)). rewrite e1 in *. inversion H1. inversion H12. inversion H6.
     + pose (IHeval_expr v2 H8). exact e2.
     + rewrite H8 in *. inversion H4.
        ** apply (val_no_trans) in H9. inversion H9. exact H7.
        ** apply eq_sym in H9. exact H9.

  (* LETREC *)
  * intros. inversion H0. inversion H1. subst. inversion H11. inversion H4.
    - pose (IHeval_expr v2 H6). exact e1.
    - subst. inversion H0. inversion H6.
      + apply val_no_trans in H8. inversion H8. exact H5.
      + apply eq_sym in H8. assumption.
  
  
  (* MAP *)
  * intros. case_eq (combine vl exprs2).
    - intros. inversion H3. pose (combine_split vl exprs2 H1). pose (combine_split vl exprs0 H12). rewrite H4 in *. inversion e0. subst. inversion H10. apply eq_sym in H6. apply length_zero_iff_nil in H6. subst. inversion H12. apply eq_sym in H6. apply length_zero_iff_nil in H6. subst. reflexivity.
    - intros. inversion H3. subst. pose (val_list_equality env0 cl0 vl exprs2 exprs0 H2 H13 H1 H12). rewrite e0 in *. reflexivity.
Qed.

Example call_comm : forall e e'  v v' cl env t,  
  (e = v \/ (env, cl, e) -e> v) /\ v val -> 
  (e' = v' \/ (env, cl, e') -e> v') /\ v' val ->
  (env, cl, ECall ("plus"%string, 2) [e ; e']) -e> t ->
  (env, cl, ECall ("plus"%string, 2) [e' ; e]) -e> t.
Proof.
  intros. inversion H1. inversion H9.
  subst. simpl in H7. pose (element_exist Expression 1 exprs2 (eq_sym H7)). inversion e0. inversion H2. subst. inversion H7. pose (element_exist Expression 0 x0 (eq_sym H4)). inversion e1. inversion H3. subst. inversion H4. apply eq_sym in H6. apply length_zero_iff_nil in H6. rewrite H6 in *. assert ([x; x1] = [v ; v']).
  * pose (H8 e x). simpl combine in a. pose (in_eq (e,x) [(e', x1)]). pose (a i). inversion a0.
  inversion H5.
    - inversion H. inversion H13.
      + subst. pose (val_no_trans v H14 env cl x H12). inversion f.
      + pose (determinism env cl e v H15 x H12). rewrite e2 in *. inversion H0. assert (In (e', x1) (combine [e; e'] [x; x1])).
      {
        simpl. auto.
      }
      pose (H8 e' x1 H18 ). inversion a1. inversion H16.
      ** rewrite H21 in *. inversion H19.
        -- apply val_no_trans in H22. inversion H22. exact H17.
        -- rewrite H22. reflexivity.
      ** inversion H19.
        -- pose (determinism env cl e' v' H21 x1 H22). rewrite e3 in *. reflexivity.
        -- rewrite H22 in *. apply val_no_trans in H21. inversion H21. exact H20.
    - subst. inversion H. inversion H6.
      + subst. inversion H0. assert (In (e', x1) (combine [v; e'] [v; x1])). { simpl. auto. } pose (H8 e' x1 H15). inversion a1. inversion H13.
        ** inversion H16.
          -- rewrite H18 in H19. apply val_no_trans in H19. inversion H19. assumption.
          -- subst. reflexivity.
        ** inversion H16.
          -- pose (determinism env cl e' v' H18 x1 H19). rewrite e in *. reflexivity.
          -- subst. apply val_no_trans in H18. inversion H18. assumption.
      + apply val_no_trans in H13. inversion H13. exact H10.

  * subst. apply eval_call with (exprs2 := [x1; x]).
    - reflexivity.
    - intros. inversion H6.
      + inversion H10.  rewrite H13 in *. rewrite H14 in *. assert (In (exp, exp') (combine [e; exp] [x; exp'])). { simpl. auto. } pose (H8 exp exp' H12). assumption.
      + inversion H10.
        ** inversion H12. rewrite H15 in *. rewrite H14 in *. assert (In (exp, exp') (combine [exp; e'] [exp'; x1])). { simpl. intuition. } pose (H8 exp exp' H13). assumption.
        ** inversion H12.
    - split.
      + apply plus_comm_basic.
      + assumption.
Qed.

Ltac unfold_list exprs2 n H1 name :=
subst; simpl in H1; pose (name := element_exist Expression n exprs2 (eq_sym H1)); inversion name; inversion H0.


Example call_comm2 : forall e e' cl env t,
  (env, cl, ECall ("plus"%string, 2) [e ; e']) -e> t <->
  (env, cl, ECall ("plus"%string, 2) [e' ; e]) -e> t.
Proof.
  split.
  * intros. inversion H. subst. inversion H7. simpl in H5. pose (element_exist Expression 1 exprs2 (eq_sym H5)). inversion e0. inversion H2. subst. inversion H5. pose (element_exist Expression 0 x0 (eq_sym H3)). inversion e1.  inversion H0. inversion H3. rewrite H4 in *. inversion H9. apply eq_sym in H10. apply length_zero_iff_nil in H10. subst.
  apply eval_call with (exprs2 := [x1; x]).
  - reflexivity.
  - intros. inversion H4.
    + inversion H8. subst. apply (H6 exp exp'). simpl. auto.
    + inversion H8.
      ** inversion H10. subst. apply (H6 exp exp'). simpl. auto.
      ** inversion H10.
  - split.
    + apply plus_comm_basic.
    + assumption.

  (* copy paszta *)
  * intros. inversion H. subst. inversion H7. simpl in H5. pose (element_exist Expression 1 exprs2 (eq_sym H5)). inversion e0. inversion H2. subst. inversion H5. pose (element_exist Expression 0 x0 (eq_sym H3)). inversion e1.  inversion H0. inversion H3. rewrite H4 in *. inversion H9. apply eq_sym in H10. apply length_zero_iff_nil in H10. subst.
  apply eval_call with (exprs2 := [x1; x]).
  - reflexivity.
  - intros. inversion H4.
    + inversion H8. subst. apply (H6 exp exp'). simpl. auto.
    + inversion H8.
      ** inversion H10. subst. apply (H6 exp exp'). simpl. auto.
      ** inversion H10.
  - split.
    + apply plus_comm_basic.
    + assumption.
Qed.

End Core_Erlang_Proofs.