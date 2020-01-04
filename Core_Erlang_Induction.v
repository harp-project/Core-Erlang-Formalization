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

  Check Expression_ind.
  Axiom Expression_new_ind : forall P : Expression -> Prop,
       (forall l : Literal, P (ELiteral l)) ->
       (forall v : Var, P (EVar v)) ->
       (forall f1 : FunctionSignature, P (EFunSig f1)) ->
       (forall (vl : list Var) (e : Expression), P e -> P (EFun vl e)) ->
       (forall hd : Expression,
        P hd -> forall tl : Expression, P tl -> P (EList hd tl)) ->
       (forall l : list Expression, (forall e : Expression, In e l -> P e) -> P (ETuple l)) ->
       (forall (f5 : string) (l : list Expression), (forall e : Expression, In e l -> P e) -> P (ECall f5 l)) ->
       (forall exp : Expression,
        P exp -> forall l : list Expression, (forall e : Expression, In e l -> P e) -> P (EApply exp l)) ->
       (forall e : Expression,
        P e -> (forall l : list Clause, (forall cl : Clause, expr_clause_prop cl P) -> P (ECase e l))) ->
       (forall (s : list Var) (el : list Expression) (e : Expression),
        (forall e : Expression, In e el -> P e) -> P e -> P (ELet s el e)) ->
       (forall (fnames : list FunctionSignature)
          (fs : list (list Var * Expression)) (e : Expression),
        P e -> P (ELetrec fnames fs e)) ->
       (forall kl vl : list Expression,
       (forall e : Expression, In e kl -> P e) -> (forall e : Expression, In e vl -> P e) -> P (EMap kl vl)) ->
       forall e : Expression, P e.

    Check eval_expr_ind.

Axiom eval_expr_ind2
     : forall P : Environment * Closures * Expression -> Value -> Prop,
     
     (* Literal *)
       (forall (env : Environment) (l : Literal) (cl : Closures), 
       P (env, cl, ELiteral l) (VLiteral l)) 
       ->
     (* Variable *)
       (forall (env : Environment) (s : Var) (cl : Closures), 
       P (env, cl, EVar s) (get_value env (inl s))) 
       ->
     (* Function singnature *)
       (forall (env : Environment) (fsig : FunctionSignature) (cl : Closures),
        P (env, cl, EFunSig fsig) (get_value env (inr fsig))) 
        ->
     (* Function definition *)
       (forall (env : Environment) (vl : list Var) (e : Expression) (cl : Closures),
        P (env, cl, EFun vl e) (VClosure (inl ""%string) vl e)) 
        ->
     (* Tuple *)
       (forall (env : Environment) (exps : list Expression) (vals : list Value) (cl : Closures),
        Datatypes.length exps = Datatypes.length vals ->
        (forall (exp : Expression) (val : Value),
         In (exp, val) (combine exps vals) -> (env, cl, exp) -e> val) ->
        (forall (exp : Expression) (val : Value),
         In (exp, val) (combine exps vals) -> P (env, cl, exp) val) ->
        P (env, cl, ETuple exps) (VTuple vals)) 
        ->
      (* List *)
       (forall (env : Environment) (hd tl : Expression) (hdv tlv : Value) (cl : Closures),
        (env, cl, hd) -e> hdv ->
        P (env, cl, hd) hdv ->
        (env, cl, tl) -e> tlv -> 
        P (env, cl, tl) tlv -> 
        P (env, cl, EList hd tl) (VList hdv tlv))
        ->
      (* Case *)
       (forall (env : Environment) (e : Expression),
        Expression ->
        forall (guard exp : Expression) (v v' : Value) (cs : list Clause) (bindings : list (Var * Value))
          (cl : Closures) (i : nat),
        (env, cl, e) -e> v ->
        P (env, cl, e) v ->
        match_clause v cs i = Some (guard, exp, bindings) ->
        (forall j : nat,
         j < i ->
         match_clause v cs j = None \/
         (forall (gg ee : Expression) (bb : list (Var * Value)),
          match_clause v cs j = Some (gg, ee, bb) -> (add_bindings bb env, cl, gg) -e> ff 
          (* Only this is additional *)
          /\ P (add_bindings bb env, cl, gg) ff)) ->
          (***)
        (add_bindings bindings env, cl, guard) -e> tt ->
        P (add_bindings bindings env, cl, guard) tt ->
        (add_bindings bindings env, cl, exp) -e> v' ->
        P (add_bindings bindings env, cl, exp) v' -> P (env, cl, ECase e cs) v') 
        ->
     (* Call *)
       (forall (env : Environment) (v : Value) (params : list Expression) (vals : list Value)
          (fname : string) (cl : Closures),
        Datatypes.length params = Datatypes.length vals ->
        (forall (exp : Expression) (val : Value),
         In (exp, val) (combine params vals) -> (env, cl, exp) -e> val) ->
        (forall (exp : Expression) (val : Value),
         In (exp, val) (combine params vals) -> P (env, cl, exp) val) ->
        eval fname vals = v -> P (env, cl, ECall fname params) v)
        ->
     (* Apply variable *)
       (forall (params : list Expression) (vals : list Value) (env : Environment)
          (name body : Expression) (v : Value) (var_list : list Var) 
          (cl : Closures) (ref : Var + FunctionSignature),
        Datatypes.length params = Datatypes.length vals ->
        (env, cl, name) -e> VClosure ref var_list body ->
        P (env, cl, name) (VClosure ref var_list body) ->
        (forall (exp : Expression) (val : Value),
         In (exp, val) (combine params vals) -> (env, cl, exp) -e> val) ->
        (forall (exp : Expression) (val : Value),
         In (exp, val) (combine params vals) -> P (env, cl, exp) val) ->
        (append_vars_to_env var_list vals (get_env ref cl env), cl, body) -e> v ->
        P (append_vars_to_env var_list vals (get_env ref cl env), cl, body) v ->
        P (env, cl, EApply name params) v)
        ->
      (* Let *)
       (forall (env : Environment) (exps : list Expression) (vals : list Value) 
          (vars : list Var) (e : Expression) (v : Value) (cl : Closures),
        Datatypes.length vals = Datatypes.length exps ->
        (forall (exp : Expression) (val : Value),
         In (exp, val) (combine exps vals) -> (env, cl, exp) -e> val) ->
        (forall (exp : Expression) (val : Value),
         In (exp, val) (combine exps vals) -> P (env, cl, exp) val) ->
        (append_vars_to_env vars vals env, append_vars_to_closure vars vals cl env, e) -e> v ->
        P (append_vars_to_env vars vals env, append_vars_to_closure vars vals cl env, e) v ->
        P (env, cl, ELet vars exps e) v)
        ->
      (* Letrec *)
       (forall (env : Environment) (e : Expression) (fnames : list FunctionSignature)
          (funs : list (list Var * Expression)) (v : Value) (cl : Closures),
        Datatypes.length funs = Datatypes.length fnames ->
        (append_funs_to_env fnames funs env,
        append_funs_to_closure fnames cl (append_funs_to_env fnames funs env), e) -e> v ->
        P
          (append_funs_to_env fnames funs env,
          append_funs_to_closure fnames cl (append_funs_to_env fnames funs env), e) v ->
        P (env, cl, ELetrec fnames funs e) v)
        ->
     (* Map *)
       (forall (kl vl : list Expression) (vvals kvals : list Value) (env : Environment) (cl : Closures),
        Datatypes.length vl = Datatypes.length kl ->
        Datatypes.length vl = Datatypes.length vvals ->
        Datatypes.length vl = Datatypes.length kvals ->
        (forall (exp : Expression) (val : Value),
         In (exp, val) (combine kl kvals) -> (env, cl, exp) -e> val) ->
        (forall (exp : Expression) (val : Value),
         In (exp, val) (combine kl kvals) -> P (env, cl, exp) val) ->
        (forall (exp : Expression) (val : Value),
         In (exp, val) (combine vl vvals) -> (env, cl, exp) -e> val) ->
        (forall (exp : Expression) (val : Value),
         In (exp, val) (combine vl vvals) -> P (env, cl, exp) val) ->
        P (env, cl, EMap kl vl) (VMap kvals vvals)) ->
       forall (p : Environment * Closures * Expression) (v : Value), p -e> v -> P p v.

End Core_Erlang_Induction.