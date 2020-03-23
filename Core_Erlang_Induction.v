Load Core_Erlang_Semantics.


Module Core_Erlang_Induction.

  Import Core_Erlang_Syntax.
  Import Core_Erlang_Semantics.
  Import Core_Erlang_Environment.
 (*  Import Core_Erlang_Closures. *)
  Import Core_Erlang_Helpers.

  Import Lists.List.
  Import ListNotations.
  Import Strings.String.

  Check Expression_ind.
  Check Expression_rect.

  Check Expression_ind.

    Check eval_expr_ind.
       
    Axiom eval_expr_ind_extended : forall P : Environment -> Expression -> Value + Exception -> Prop,
    
    (** EMPTYLIST *)
       (forall env : Environment, P env EEmptyList (inl VEmptyList)) ->
    (** LITERAL *)
       (forall (env : Environment) (l : Literal), P env (ELiteral l) (inl (VLiteral l))) ->
    (** VARIABLE *)
       (forall (env : Environment) (s : Var), P env (EVar s) (get_value env (inl s))) ->
    (** FUNCTIONIDENTIFIER *)
       (forall (env : Environment) (fsig : FunctionIdentifier), P env (EFunId fsig) (get_value env (inr fsig))) ->
    (** FUNCTION *)
       (forall (env : Environment) (vl : list Var) (e : Expression), P env (EFun vl e) (inl (VClosure env [] vl e))) ->
    (** TUPLE *)
       (forall (env : Environment) (exps : list Expression) (vals : list Value),
        Datatypes.length exps = Datatypes.length vals ->
        (forall (exp : Expression) (val : Value), In (exp, val) (combine exps vals) -> | env, exp | -e> inl val) ->
        (forall (exp : Expression) (val : Value), In (exp, val) (combine exps vals) -> P env exp (inl val)) ->
        P env (ETuple exps) (inl (VTuple vals))) ->
     (** LIST *)
       (forall (env : Environment) (hd tl : Expression) (hdv tlv : Value),
        | env, hd | -e> inl hdv ->
        P env hd (inl hdv) ->
        | env, tl | -e> inl tlv -> P env tl (inl tlv) -> P env (EList hd tl) (inl (VList hdv tlv))) ->
     (** CASE *)
       (forall (env : Environment) (e guard exp : Expression) (v : Value) (v' : Value + Exception)
          (patterns : list Pattern) (guards bodies : list Expression) (bindings : list (Var * Value)) 
          (i : nat),
        | env, e | -e> inl v ->
        P env e (inl v) ->
        Datatypes.length patterns = Datatypes.length guards ->
        Datatypes.length bodies = Datatypes.length patterns ->
        i < Datatypes.length patterns ->
        match_clause v patterns guards bodies i = Some (guard, exp, bindings) ->
        (forall j : nat,
         j < i ->
         forall (gg ee : Expression) (bb : list (Var * Value)),
         match_clause v patterns guards bodies j = Some (gg, ee, bb) -> | add_bindings bb env, gg | -e> inl ffalse) ->
        (forall j : nat,
         j < i ->
         forall (gg ee : Expression) (bb : list (Var * Value)),
         match_clause v patterns guards bodies j = Some (gg, ee, bb) -> P (add_bindings bb env) gg (inl ffalse)) ->
        | add_bindings bindings env, guard | -e> inl ttrue ->
        P (add_bindings bindings env) guard (inl ttrue) ->
        | add_bindings bindings env, exp | -e> v' ->
        P (add_bindings bindings env) exp v' -> P env (ECase e patterns guards bodies) v') ->
     (** CALL *)
       (forall (env : Environment) (v : Value + Exception) (params : list Expression) (vals : list Value)
          (fname : string),
        Datatypes.length params = Datatypes.length vals ->
        (forall (exp : Expression) (val : Value), In (exp, val) (combine params vals) -> | env, exp | -e> inl val) ->
        (forall (exp : Expression) (val : Value), In (exp, val) (combine params vals) -> P env exp (inl val)) ->
        eval fname vals = v -> P env (ECall fname params) v) ->
     (** APPLICATION *)
       (forall (params : list Expression) (vals : list Value) (env : Environment) (exp body : Expression)
          (v : Value + Exception) (var_list : list Var) (ref : Environment)
          (ext : list (FunctionIdentifier * FunctionalExpression)),
        Datatypes.length params = Datatypes.length vals ->
        | env, exp | -e> inl (VClosure ref ext var_list body) ->
        P env exp (inl (VClosure ref ext var_list body)) ->
        Datatypes.length var_list = Datatypes.length vals ->
        (forall (exp0 : Expression) (val : Value), In (exp0, val) (combine params vals) -> | env, exp0 | -e> inl val) ->
        (forall (exp0 : Expression) (val : Value), In (exp0, val) (combine params vals) -> P env exp0 (inl val)) ->
        | append_vars_to_env var_list vals (get_env ref ref ext ext), body | -e> v ->
        P (append_vars_to_env var_list vals (get_env ref ref ext ext)) body v -> P env (EApply exp params) v) ->
    (** LET *)
       (forall (env : Environment) (exps : list Expression) (vals : list Value) (vars : list Var) 
          (e : Expression) (v : Value + Exception),
        Datatypes.length vals = Datatypes.length exps ->
        (forall (exp : Expression) (val : Value), In (exp, val) (combine exps vals) -> | env, exp | -e> inl val) ->
        (forall (exp : Expression) (val : Value), In (exp, val) (combine exps vals) -> P env exp (inl val)) ->
        | append_vars_to_env vars vals env, e | -e> v ->
        P (append_vars_to_env vars vals env) e v -> P env (ELet vars exps e) v) ->
     (** LETREC *)
       (forall (env : Environment) (e : Expression) (fnames : list FunctionIdentifier) (paramss : list (list Var))
          (bodies : list Expression) (v : Value + Exception),
        Datatypes.length fnames = Datatypes.length paramss ->
        Datatypes.length fnames = Datatypes.length bodies ->
        | append_funs_to_env fnames paramss bodies env env (list_functions fnames paramss bodies), e | -e> v ->
        P (append_funs_to_env fnames paramss bodies env env (list_functions fnames paramss bodies)) e v ->
        P env (ELetrec fnames paramss bodies e) v) ->
     (** MAP *)
       (forall (kl vl : list Expression) (vvals kvals kl' vl' : list Value) (env : Environment),
        Datatypes.length vl = Datatypes.length kl ->
        Datatypes.length vl = Datatypes.length vvals ->
        Datatypes.length vl = Datatypes.length kvals ->
        make_value_map kvals vvals = (kl', vl') ->
        (forall i : nat,
         i < Datatypes.length vl ->
         | env, nth i kl ErrorExp | -e> inl (nth i kvals ErrorValue) /\
         | env, nth i vl ErrorExp | -e> inl (nth i vvals ErrorValue)) ->
        (** ADDED *)
        (forall i : nat,
         i < Datatypes.length vl ->
         P env (nth i kl ErrorExp) (inl (nth i kvals ErrorValue))) ->
        (forall i : nat,
         i < Datatypes.length vl ->
         P env (nth i vl ErrorExp) (inl (nth i vvals ErrorValue)))
        (***)
         -> P env (EMap kl vl) (inl (VMap kl' vl'))) ->


     (** EXCEPTIONS *)
     (** LIST HEAD *)
       (forall (env : Environment) (hd tl : Expression) (ex : Exception),
        | env, hd | -e> inr ex -> P env hd (inr ex) -> P env (EList hd tl) (inr ex)) ->
     (** LIST TAIL *)
       (forall (env : Environment) (hd tl : Expression) (ex : Exception) (vhd : Value),
        | env, hd | -e> inl vhd ->
        P env hd (inl vhd) -> | env, tl | -e> inr ex -> P env tl (inr ex) -> P env (EList hd tl) (inr ex)) ->
     (** TUPLE *)
       (forall (env : Environment) (i : nat) (exps : list Expression) (vals : list Value) (ex : Exception),
        Datatypes.length vals = i ->
        i < Datatypes.length exps ->
        (forall j : nat, j < i -> | env, nth j exps ErrorExp | -e> inl (nth j vals ErrorValue)) ->
        (forall j : nat, j < i -> P env (nth j exps ErrorExp) (inl (nth j vals ErrorValue))) ->
        | env, nth i exps ErrorExp | -e> inr ex ->
        P env (nth i exps ErrorExp) (inr ex) -> P env (ETuple exps) (inr ex)) ->
     (** TRY *)
       (forall (env : Environment) (e e1 e2 : Expression) (v vex1 vex2 vex3 : Var) (val : Value + Exception)
          (val' : Value),
        | env, e | -e> inl val' ->
        P env e (inl val') ->
        | append_vars_to_env [v] [val'] env, e1 | -e> val ->
        P (append_vars_to_env [v] [val'] env) e1 val -> P env (ETry e e1 e2 v vex1 vex2 vex3) val) ->
     (** TRY CATCH *)
       (forall (env : Environment) (e e1 e2 : Expression) (v vex1 vex2 vex3 : Var) (val : Value + Exception)
          (ex : Exception),
        | env, e | -e> inr ex ->
        P env e (inr ex) ->
        | append_vars_to_env [vex1; vex2; vex3] [make_value_from_ex_class (fst (fst ex)); snd (fst ex); snd ex] env,
        e2 | -e> val ->
        P (append_vars_to_env [vex1; vex2; vex3] [make_value_from_ex_class (fst (fst ex)); snd (fst ex); snd ex] env)
          e2 val -> P env (ETry e e1 e2 v vex1 vex2 vex3) val) ->
     (** CASE BASE *)
       (forall (env : Environment) (e : Expression) (ex : Exception) (patterns : list Pattern)
          (guards bodies : list Expression),
        list (Var * Value) ->
        Datatypes.length patterns = Datatypes.length guards ->
        Datatypes.length patterns = Datatypes.length bodies ->
        | env, e | -e> inr ex -> P env e (inr ex) -> P env (ECase e patterns guards bodies) (inr ex)) ->
     (** CASE GUARD *)
       (forall (env : Environment) (e : Expression),
        Expression ->
        forall (guard exp : Expression) (v : Value) (ex : Exception) (patterns : list Pattern)
          (guards bodies : list Expression) (bindings : list (Var * Value)) (i : nat),
        Datatypes.length patterns = Datatypes.length guards ->
        Datatypes.length patterns = Datatypes.length bodies ->
        | env, e | -e> inl v ->
        P env e (inl v) ->
        match_clause v patterns guards bodies i = Some (guard, exp, bindings) ->
        (forall j : nat,
         j < i ->
         forall (gg ee : Expression) (bb : list (Var * Value)),
         match_clause v patterns guards bodies j = Some (gg, ee, bb) -> | add_bindings bb env, gg | -e> inl ffalse) ->
        (forall j : nat,
         j < i ->
         forall (gg ee : Expression) (bb : list (Var * Value)),
         match_clause v patterns guards bodies j = Some (gg, ee, bb) -> P (add_bindings bb env) gg (inl ffalse)) ->
        | add_bindings bindings env, guard | -e> inr ex ->
        P (add_bindings bindings env) guard (inr ex) -> P env (ECase e patterns guards bodies) (inr ex)) ->
     (** CALL *)
       (forall (env : Environment) (i : nat) (fname : string) (params : list Expression) 
          (vals : list Value) (ex : Exception),
        Datatypes.length vals = i ->
        i < Datatypes.length params ->
        (forall j : nat, j < i -> | env, nth j params ErrorExp | -e> inl (nth j vals ErrorValue)) ->
        (forall j : nat, j < i -> P env (nth j params ErrorExp) (inl (nth j vals ErrorValue))) ->
        | env, nth i params ErrorExp | -e> inr ex ->
        P env (nth i params ErrorExp) (inr ex) -> P env (ECall fname params) (inr ex)) ->
     (** APPLY CLOSURE *)
       (forall (params : list Expression) (env : Environment) (exp : Expression) (ex : Exception),
        | env, exp | -e> inr ex -> P env exp (inr ex) -> P env (EApply exp params) (inr ex)) ->
     (** APPLY PARAMETER *)
       (forall (params : list Expression) (vals : list Value) (env : Environment) (exp : Expression) 
          (ex : Exception) (i : nat) (v : Value),
        i = Datatypes.length vals ->
        i < Datatypes.length params ->
        | env, exp | -e> inl v ->
        P env exp (inl v) ->
        (forall j : nat, j < i -> | env, nth j params ErrorExp | -e> inl (nth j vals ErrorValue)) ->
        (forall j : nat, j < i -> P env (nth j params ErrorExp) (inl (nth j vals ErrorValue))) ->
        | env, nth i params ErrorExp | -e> inr ex ->
        P env (nth i params ErrorExp) (inr ex) -> P env (EApply exp params) (inr ex)) ->
     (** APPLY NON-CLOSURE *)
       (forall (params : list Expression) (vals : list Value) (env : Environment) (v : Value) (exp : Expression),
        Datatypes.length params = Datatypes.length vals ->
        (forall (exp0 : Expression) (val : Value), In (exp0, val) (combine params vals) -> | env, exp0 | -e> inl val) ->
        (forall (exp0 : Expression) (val : Value), In (exp0, val) (combine params vals) -> P env exp0 (inl val)) ->
        | env, exp | -e> inl v ->
        P env exp (inl v) ->
        (forall (ref : list ((Var + FunctionIdentifier) * Value))
           (ext : list (FunctionIdentifier * FunctionalExpression)) (var_list : list Var) 
           (body : Expression), v <> VClosure ref ext var_list body) -> P env (EApply exp params) (inr noclosure)) ->
     (** APPLY INCORRECT ARGS *)
       (forall (params : list Expression) (vals : list Value) (env : Environment) (exp body : Expression)
          (var_list : list Var) (ref : Environment) (ext : list (FunctionIdentifier * FunctionalExpression)),
        Datatypes.length params = Datatypes.length vals ->
        | env, exp | -e> inl (VClosure ref ext var_list body) ->
        P env exp (inl (VClosure ref ext var_list body)) ->
        (forall (exp0 : Expression) (val : Value), In (exp0, val) (combine params vals) -> | env, exp0 | -e> inl val) ->
        (forall (exp0 : Expression) (val : Value), In (exp0, val) (combine params vals) -> P env exp0 (inl val)) ->
        Datatypes.length var_list <> Datatypes.length vals -> P env (EApply exp params) (inr args)) ->
     (** LET *)
       (forall (env : Environment) (exps : list Expression) (vals : list Value) (vars : list Var) 
          (e : Expression) (ex : Exception) (i : nat),
        Datatypes.length vals = i ->
        i < Datatypes.length exps ->
        (forall j : nat, j < i -> | env, nth j exps ErrorExp | -e> inl (nth j vals ErrorValue)) ->
        (forall j : nat, j < i -> P env (nth j exps ErrorExp) (inl (nth j vals ErrorValue))) ->
        | env, nth i exps ErrorExp | -e> inr ex ->
        P env (nth i exps ErrorExp) (inr ex) -> P env (ELet vars exps e) (inr ex)) ->
     (** MAP KEY *)
       (forall (kl vl : list Expression) (vvals kvals : list Value) (env : Environment) (i : nat) (ex : Exception),
        Datatypes.length vl = Datatypes.length kl ->
        i = Datatypes.length vvals ->
        i = Datatypes.length kvals ->
        i < Datatypes.length vl ->
        (forall j : nat,
         j < i ->
         | env, nth j kl ErrorExp | -e> inl (nth j kvals ErrorValue) /\
         | env, nth j vl ErrorExp | -e> inl (nth j vvals ErrorValue)) ->
        (** ADDITION *)
        (forall j : nat,
         j < i ->
         P env (nth j kl ErrorExp) (inl (nth j kvals ErrorValue))) ->
        (forall j : nat,
         j < i ->
         P env (nth j vl ErrorExp) (inl (nth j vvals ErrorValue))) ->
         (***)
        | env, nth i kl ErrorExp | -e> inr ex -> P env (nth i kl ErrorExp) (inr ex) -> P env (EMap kl vl) (inr ex)) ->
     (** MAP VALUE *)
       (forall (kl vl : list Expression) (vvals kvals : list Value) (env : Environment) (i : nat) 
          (ex : Exception) (val : Value),
        Datatypes.length vl = Datatypes.length kl ->
        i = Datatypes.length vvals ->
        i = Datatypes.length kvals ->
        i < Datatypes.length vl ->
        (forall j : nat,
         j < i ->
         | env, nth j kl ErrorExp | -e> inl (nth j kvals ErrorValue) /\
         | env, nth j vl ErrorExp | -e> inl (nth j vvals ErrorValue)) ->
        (** ADDITION *)
        (forall j : nat,
         j < i ->
         P env (nth j kl ErrorExp) (inl (nth j kvals ErrorValue))) ->
        (forall j : nat,
         j < i ->
         P env (nth j vl ErrorExp) (inl (nth j vvals ErrorValue))) ->
         (***)
        | env, nth i kl ErrorExp | -e> inl val ->
        P env (nth i kl ErrorExp) (inl val) ->
        | env, nth i vl ErrorExp | -e> inr ex -> P env (nth i vl ErrorExp) (inr ex) -> P env (EMap kl vl) (inr ex)) ->
       forall (e : Environment) (e0 : Expression) (s : Value + Exception), | e, e0 | -e> s -> P e e0 s.

End Core_Erlang_Induction.