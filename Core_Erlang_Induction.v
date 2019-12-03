Load Core_Erlang_Semantics.


Module Core_Erlang_Induction.

  Import Core_Erlang_Syntax.
  Import Core_Erlang_Semantics.
  Import Core_Erlang_Environment.
  Import Core_Erlang_Closures.
  Import Core_Erlang_Helpers.

  Import Lists.List.
  Import ListNotations.
  Import Strings.String.

  Check Expression_ind.
  
  Check Clause_ind.
  Check Expression_rect.

  Fixpoint expr_clause_prop (cl : Clause) (P : Expression -> Prop) : Prop :=
  match cl with
  | CCons p g e => P g /\ P e
  end
  .

  Section All.
    Variable T : Type.
    Variable P : T -> Prop.

    Fixpoint All (ls : list T) : Prop :=
      match ls with
        | [ ] => True
        | h::t => P h /\ All t
      end.
  End All.

  Axiom Expression_ind2 : forall P : Expression -> Prop,
       (forall l : Literal, P (ELiteral l)) ->
       (forall v : Var, P (EVar v)) ->
       (forall f1 : Fun, P (EFunction f1)) ->
       (forall hd : Expression, P hd -> forall tl : Expression, P tl -> P (EList hd tl)) ->
       (forall l : list Expression, (forall e : Expression, In e l -> P e) -> P (ETuple l)) ->
       (forall (f4 : FunctionSignature) (l : list Expression), (forall e : Expression, In e l -> P e) -> P (ECall f4 l)) ->
       (forall (f5 : Var) (l : list Expression), (forall e : Expression, In e l -> P e) -> P (EApply f5 l)) ->
       (forall (f6 : FunctionSignature) (l : list Expression), (forall e : Expression, In e l -> P e) -> P (EApplyTopLevel f6 l)) ->
       (forall e : Expression, P e -> (forall l : list Clause, (forall cl : Clause, expr_clause_prop cl P) -> P (ECase e l))) ->
       (forall (s : list Var) (el : list Expression) (e : Expression), (forall exp : Expression, In exp el -> P exp) -> P e -> P (ELet s el e)) ->
       (forall (fnames : list FunctionSignature) (fs : list Fun) (e : Expression),
        P e -> P (ELetrec fnames fs e)) ->
       (forall kl vl : list Expression, (forall e : Expression, In e kl -> P e) -> (forall e : Expression, In e vl -> P e) -> P (EMap kl vl))
-> forall e : Expression, P e.
  (*Variable P : Expression -> Prop.


  Hypothesis literal_case : forall l, P (ELiteral l).
  Hypothesis var_case : forall v : Var, P (EVar v).
  Hypothesis function_case : forall f: Fun, P (EFunction f).
  Hypothesis list_case : forall hd tl : Expression, P hd /\ P tl -> P (EList hd tl).
  (*Hypothesis tuple_case : forall exps : list Expression, All Expression P exps -> P (ETuple exps).*)
  Hypothesis tuple_case : forall exps : list Expression, All Expression P exps -> P (ETuple exps).
  Hypothesis call_case : forall f exps, All Expression P exps -> P (ECall f exps).
  Hypothesis apply_case : forall f exps, All Expression P exps -> P (EApply f exps).
  Hypothesis top_apply_case : forall f exps, All Expression P exps -> P (EApplyTopLevel f exps).
  Hypothesis let_case : forall sl el e, All Expression P el /\ P e -> P (ELet sl el e).
  Hypothesis letrec_case : forall fnames fs e, P e -> P (ELetrec fnames fs e).
  Hypothesis map_case : forall kl vl, All Expression P kl /\ All Expression P vl -> P (EMap kl vl).
  
  Fixpoint expr_induct (e : Expression) : P e :=
    match e with
     | ELiteral l => literal_case l
     | EVar v => var_case v
     | EFunction f => function_case f
     | EList hd tl => list_case hd tl (conj (expr_induct hd) (expr_induct tl))
     | ETuple l => tuple_case l ((fix list_ind (ls : list Expression) : All Expression P ls :=
        match ls with
        | [] => I
        | x::xs => conj (expr_induct x) (list_ind xs)
        end) l)
     | ECall f l => call_case f l ((fix list_ind (ls : list Expression) : All Expression P ls :=
        match ls with
        | [] => I
        | x::xs => conj (expr_induct x) (list_ind xs)
        end) l)
     | EApply f l => apply_case f l ((fix list_ind (ls : list Expression) : All Expression P ls :=
        match ls with
        | [] => I
        | x::xs => conj (expr_induct x) (list_ind xs)
        end) l)
     | EApplyTopLevel f l => top_apply_case f l ((fix list_ind (ls : list Expression) : All Expression P ls :=
        match ls with
        | [] => I
        | x::xs => conj (expr_induct x) (list_ind xs)
        end) l)
     | ELet s el e => let_case s el e (conj ((fix list_ind (ls : list Expression) : All Expression P ls :=
        match ls with
        | [] => I
        | x::xs => conj (expr_induct x) (list_ind xs)
        end) el) (expr_induct e))
     | ELetrec fnames fs e => letrec_case fnames fs e (expr_induct e)
     | EMap kl vl => map_case kl vl (conj (((fix list_ind (ls : list Expression) : All Expression P ls :=
        match ls with
        | [] => I
        | x::xs => conj (expr_induct x) (list_ind xs)
        end) kl)) (((fix list_ind (ls : list Expression) : All Expression P ls :=
        match ls with
        | [] => I
        | x::xs => conj (expr_induct x) (list_ind xs)
        end) vl)))
    end.*)
    
    Check eval_expr_ind.

Axiom eval_expr_ind2
     : forall P : Environment * Closures * Expression -> Expression -> Prop,
       (forall (env : Environment) (s : Var) (cl : Closures),
        P (env, cl, EVar s) (proj1_sig (get_value env (inl s)))) ->
        
        
       (forall (env : Environment) (exprs1 exprs2 : list Expression) (cl : Closures),
        Datatypes.length exprs1 = Datatypes.length exprs2 ->
        (forall exp exp' : Expression,
         In (exp, exp') (combine exprs1 exprs2) ->
         (((env, cl, exp) -e> exp' /\ P (env, cl, exp) exp') \/ exp = exp') /\ exp' val) ->
        ETuple exprs1 <> ETuple exprs2 -> P (env, cl, ETuple exprs1) (ETuple exprs2)) ->
        
        
       (forall (env : Environment) (hd tl e' e'' : Expression) (cl : Closures),
        (((env, cl, hd) -e> e' /\ P (env, cl, hd) e') \/ hd = e') /\ e' val ->
        (((env, cl, tl) -e> e'' /\ P (env, cl, tl) e'') \/ tl = e'') /\ e'' val ->
        EList hd tl <> EList e' e'' -> P (env, cl, EList hd tl) (EList e' e'')) ->
        
        
        (forall (env : Environment) (e e'' guard exp : Expression) (e' : Value) 
          (cs : list Clause) (bindings : list (Var * Value)) (cl : Closures),
        ((env, cl, e) -e> proj1_sig e' /\ P (env, cl, e) (proj1_sig e')) \/ e = proj1_sig e' ->
        match_clauses e' cs = Some (guard, exp, bindings) ->
        (add_bindings bindings env, cl, guard) -e> tt \/ guard = tt ->
        (((add_bindings bindings env, cl, exp) -e> e'' /\ P (add_bindings bindings env, cl, exp) e'') \/ exp = e'') /\ e'' val ->
        P (env, cl, ECase e cs) e'') ->
        
        
       (forall (env : Environment) (e' : Expression) (params exprs2 : list Expression)
          (fname : FunctionSignature) (cl : Closures),
        Datatypes.length params = Datatypes.length exprs2 ->
        (forall exp exp' : Expression,
         In (exp, exp') (combine params exprs2) ->
         (((env, cl, exp) -e> exp' /\ P (env, cl, exp) exp') \/ exp = exp') /\ exp' val) ->
        eval env fname exprs2 = e' /\ e' val -> P (env, cl, ECall fname params) e') ->
        
        
        
       (forall (exprs1 : list Expression) (exprs2 : list Value) (env : Environment)
          (name : string) (args : nat) (e' : Expression) (cl : Closures),
        Datatypes.length exprs1 = Datatypes.length exprs2 ->
        Datatypes.length exprs1 = args ->
        (forall (exp : Expression) (exp' : Value),
         In (exp, exp') (combine exprs1 exprs2) ->
         (((env, cl, exp) -e> proj1_sig exp' /\ P (env, cl, exp) (proj1_sig exp'))
          \/ exp = proj1_sig exp')) ->
        (((append_vars_to_env (get_vars (get_value env (inr (name, args)))) exprs2
            (get_env_from_closure (inr (name, args)) cl), cl,
         get_fun_exp (get_value env (inr (name, args)))) -e> e' /\ 
         P (append_vars_to_env (get_vars (get_value env (inr (name, args)))) exprs2
            (get_env_from_closure (inr (name, args)) cl), cl,
         get_fun_exp (get_value env (inr (name, args)))) e')
          \/
         get_fun_exp (get_value env (inr (name, args))) = e') /\ e' val
       ->
        P (env, cl, EApplyTopLevel (name, args) exprs1) e') ->
        
        
        
       (forall (exprs1 : list Expression) (exprs2 : list Value) (env : Environment) 
          (name : Var) (e' : Expression) (cl : Closures),
        Datatypes.length exprs1 = Datatypes.length exprs2 ->
        (forall (exp : Expression) (exp' : Value),
         In (exp, exp') (combine exprs1 exprs2) ->
         ((env, cl, exp) -e> proj1_sig exp' /\ P (env, cl, exp) (proj1_sig exp')) \/ exp = proj1_sig exp') ->
        (((append_vars_to_env (get_vars (get_value env (inl name))) exprs2
            (get_env_from_closure (inl name) cl), cl, get_fun_exp (get_value env (inl name))) -e>
         e' /\  P (append_vars_to_env (get_vars (get_value env (inl name))) exprs2
            (get_env_from_closure (inl name) cl), cl, get_fun_exp (get_value env (inl name))) e') \/ get_fun_exp (get_value env (inl name)) = e') /\ e' val 
      ->
        P (env, cl, EApply name exprs1) e') ->
        
        
        
       (forall (env : Environment) (exps : list Expression) (exprs2 : list Value)
          (vars : list Var) (e e' : Expression) (cl : Closures),
        Datatypes.length exprs2 = Datatypes.length exps ->
        (forall (exp : Expression) (exp' : Value),
         In (exp, exp') (combine exps exprs2) ->
         (((env, cl, exp) -e> proj1_sig exp' /\ P (env, cl, exp) (proj1_sig exp')) \/ exp = proj1_sig exp')) ->
        (((append_vars_to_env vars exprs2 env,
         append_vars_to_closure vars (valuelist_to_exp exprs2) cl env, e) -e> e' /\  P (append_vars_to_env vars exprs2 env,
         append_vars_to_closure vars (valuelist_to_exp exprs2) cl env, e) e' ) \/ 
         e = e') /\ e' val 
       ->
          P (env, cl, ELet vars exps e) e') ->
         
         
         
         
       (forall (env : Environment) (e e' : Expression) (fnames : list FunctionSignature)
          (funs : list Fun) (cl : Closures),
        Datatypes.length funs = Datatypes.length fnames ->
        (((append_funs_to_env fnames funs env,
         append_funs_to_closure fnames cl (append_funs_to_env fnames funs env), e) -e> e' /\ P (append_funs_to_env fnames funs env,
         append_funs_to_closure fnames cl (append_funs_to_env fnames funs env), e) e') \/
         e = e') /\ e' val
         -> P (env, cl, ELetrec fnames funs e) e') ->
         
         
         
         
         
       (forall (kl vl : list Expression) (exprs2 : list Value) (env : Environment) (cl : Closures),
        (forall exp : Expression, In exp kl -> exp val) ->
        Datatypes.length vl = Datatypes.length kl ->
        Datatypes.length vl = Datatypes.length exprs2 ->
        (forall (exp : Expression) (exp' : Value),
         In (exp, exp') (combine vl exprs2) ->
         (((env, cl, exp) -e> proj1_sig exp' /\  P (env, cl, exp) (proj1_sig exp') \/ exp = proj1_sig exp'))) ->
        P (env, cl, EMap kl vl) (EMap kl (valuelist_to_exp exprs2))) ->
       forall (p : Environment * Closures * Expression) (e : Expression), p -e> e -> P p e.



End Core_Erlang_Induction.