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
       
    Axiom eval_expr_ind_extended : forall P : Environment -> Closures -> Expression -> (Value + Exception) -> Prop,
    
    (* Literal *)
       (forall (env : Environment) (l : Literal) (cl : Closures), P env cl (ELiteral l) (inl (VLiteral l))) ->
    (* Variable *)
       (forall (env : Environment) (s : Var) (cl : Closures), P env cl (EVar s) (get_value env (inl s))) ->
    (* Function Signature *)
       (forall (env : Environment) (fsig : FunctionSignature) (cl : Closures),
        P env cl (EFunSig fsig) (get_value env (inr fsig))) ->
    (* Function *)
       (forall (env : Environment) (vl : list Var) (e : Expression) (cl : Closures),
        P env cl (EFun vl e)(inl (VClosure (inl env) vl e))) ->
    (* TUPLE *)
       (forall (env : Environment) (exps : list Expression) (vals : list Value) (cl : Closures),
        Datatypes.length exps = Datatypes.length vals ->
        (forall (exp : Expression) (val : Value), In (exp, val) (combine exps vals) -> | env, cl, exp | -e> inl val) ->
        (forall (exp : Expression) (val : Value), In (exp, val) (combine exps vals) -> P env cl exp (inl val)) ->
        P env cl (ETuple exps) (inl (VTuple vals))) ->
    (* LIST *)
       (forall (env : Environment) (hd tl : Expression) (hdv tlv : Value) (cl : Closures),
        | env, cl, hd | -e> inl hdv ->
        P env cl hd (inl hdv) -> | env, cl, tl | -e> inl tlv -> P env cl tl (inl tlv) -> P env cl (EList hd tl) (inl (VList hdv tlv))) ->
    (* CASE *)
       (forall (env : Environment) (e : Expression),
        Expression ->
        forall (guard exp : Expression) (v : Value) (v' : Value + Exception) (cs : list Clause)
          (bindings : list (Var * Value)) (cl : Closures) (i : nat),
        | env, cl, e | -e> inl v ->
        P env cl e (inl v) ->
        match_clause v cs i = Some (guard, exp, bindings) ->
        (forall j : nat,
         j < i ->
         forall (gg ee : Expression) (bb : list (Var * Value)),
         match_clause v cs j = Some (gg, ee, bb) -> | add_bindings bb env, cl, gg | -e> inl ffalse) ->
        (forall j : nat,
         j < i ->
         forall (gg ee : Expression) (bb : list (Var * Value)),
         match_clause v cs j = Some (gg, ee, bb) -> P (add_bindings bb env) cl gg (inl ffalse)) ->
        | add_bindings bindings env, cl, guard | -e> inl ttrue ->
        P (add_bindings bindings env) cl guard (inl ttrue) ->
        | add_bindings bindings env, cl, exp | -e> v' ->
        P (add_bindings bindings env) cl exp v' -> P env cl (ECase e cs) v') ->
     (* CALL *)
       (forall (env : Environment) (v : Value + Exception) (params : list Expression) (vals : list Value) 
          (fname : string) (cl : Closures),
        Datatypes.length params = Datatypes.length vals ->
        (forall (exp : Expression) (val : Value), In (exp, val) (combine params vals) -> | env, cl, exp | -e> inl val) ->
        (forall (exp : Expression) (val : Value), In (exp, val) (combine params vals) -> P env cl exp (inl val)) ->
        eval fname vals = v -> P env cl (ECall fname params) v) ->
     (* APPLY *)
       (forall (params : list Expression) (vals : list Value) (env : Environment)
          (exp body : Expression) (v : Value + Exception) (var_list : list Var) 
          (cl : Closures) (ref : Environment + FunctionSignature),
        Datatypes.length params = Datatypes.length vals ->
        | env, cl, exp | -e> inl (VClosure ref var_list body) ->
        P env cl exp (inl (VClosure ref var_list body)) ->
        Datatypes.length var_list = Datatypes.length vals ->
        (forall (exp0 : Expression) (val : Value),
         In (exp0, val) (combine params vals) -> | env, cl, exp0 | -e> inl val) ->
        (forall (exp0 : Expression) (val : Value),
         In (exp0, val) (combine params vals) -> P env cl exp0 (inl val)) ->
        | append_vars_to_env var_list vals (get_env ref cl), cl, body | -e> v ->
        P (append_vars_to_env var_list vals (get_env ref cl)) cl body v ->
        P env cl (EApply exp params) v) ->
     (* LET *)
       (forall (env : Environment) (exps : list Expression) (vals : list Value) 
          (vars : list Var) (e : Expression) (v : Value + Exception) (cl : Closures),
        Datatypes.length vals = Datatypes.length exps ->
        (forall (exp : Expression) (val : Value),
         In (exp, val) (combine exps vals) -> | env, cl, exp | -e> inl val) ->
        (forall (exp : Expression) (val : Value),
         In (exp, val) (combine exps vals) -> P env cl exp (inl val)) ->
        | append_vars_to_env vars vals env, cl, e | -e> v ->
        P (append_vars_to_env vars vals env) cl e v -> P env cl (ELet vars exps e) v) ->
     (* LETREC *)
       (forall (env : Environment) (e : Expression) (fnames : list FunctionSignature)
          (funs : list (list Var * Expression)) (v : Value + Exception) 
          (cl : Closures),
        Datatypes.length funs = Datatypes.length fnames ->
        | append_funs_to_env fnames funs env,
        append_funs_to_closure fnames cl (append_funs_to_env fnames funs env), e | -e> v ->
        P (append_funs_to_env fnames funs env)
          (append_funs_to_closure fnames cl (append_funs_to_env fnames funs env)) e v ->
        P env cl (ELetrec fnames funs e) v) ->
     (* (* MAP *)
       (forall (kl vl : list Expression) (vvals kvals : list Value) (env : Environment)
          (cl : Closures),
        Datatypes.length vl = Datatypes.length kl ->
        Datatypes.length vl = Datatypes.length vvals ->
        Datatypes.length vl = Datatypes.length kvals ->
        (forall (kexp vexp : Expression) (kval vval : Value),
         In (kexp, kval, (vexp, vval)) (combine (combine kl kvals) (combine vl vvals)) ->
         | env, cl, kexp | -e> inl kval /\ | env, cl, vexp | -e> inl vval) ->
        (forall (kexp vexp : Expression) (kval vval : Value),
        (* ADDITION *)
        In (kexp, kval, (vexp, vval)) (combine (combine kl kvals) (combine vl vvals)) ->
        P env cl kexp (inl kval) /\ P env cl vexp (inl vval)) ->
        (***)
        P env cl (EMap kl vl) (inl (VMap kvals vvals))) -> *)
    (* Exceptions *)
      (* list head *)
        (forall (env : Environment) (cl : Closures) (hd tl : Expression) (ex : Exception),
        | env, cl, hd | -e> inr ex -> P env cl hd (inr ex) -> P env cl (EList hd tl) (inr ex)) ->
      (* list tail *)
       (forall (env : Environment) (cl : Closures) (hd tl : Expression) 
          (ex : Exception) (vhd : Value),
        | env, cl, hd | -e> inl vhd ->
        P env cl hd (inl vhd) ->
        | env, cl, tl | -e> inr ex -> P env cl tl (inr ex) -> P env cl (EList hd tl) (inr ex)) ->
        
        (* tuple exception *)
        (forall (env : Environment) (cl : Closures) (i : nat) (exps : list Expression)
          (vals : list Value) (ex : Exception),
        Datatypes.length vals = i ->
        i < Datatypes.length exps ->
        (forall j : nat, j < i -> | env, cl, nth j exps ErrorExp | -e> inl (nth j vals ErrorValue)) ->
        (forall j : nat, j < i -> P env cl (nth j exps ErrorExp) (inl (nth j vals ErrorValue))) ->
        | env, cl, nth i exps ErrorExp | -e> inr ex ->
        P env cl (nth i exps ErrorExp) (inr ex) -> P env cl (ETuple exps) (inr ex)) ->
        
       (* try correct *)
        (forall (env : Environment) (cl : Closures) (e e1 e2 : Expression) 
          (v vex1 vex2 vex3 : Var) (val : Value + Exception) (val' : Value),
        | env, cl, e | -e> inl val' ->
        P env cl e (inl val') ->
        | append_vars_to_env [v] [val'] env, cl, e1 | -e> val ->
        P (append_vars_to_env [v] [val'] env) cl e1 val ->
        P env cl (ETry e e1 e2 v vex1 vex2 vex3) val) ->

      (* try exception *)
       (forall (env : Environment) (cl : Closures) (e e1 e2 : Expression) 
          (v vex1 vex2 vex3 : Var) (val : Value + Exception) (ex : Exception),
        | env, cl, e | -e> inr ex ->
        P env cl e (inr ex) ->
        | append_vars_to_env [vex1; vex2; vex3]
            [make_value_from_ex_class (fst (fst ex)); snd (fst ex); snd ex] env, cl, e2 | -e> val ->
        P
          (append_vars_to_env [vex1; vex2; vex3]
             [make_value_from_ex_class (fst (fst ex)); snd (fst ex); snd ex] env) cl e2 val ->
        P env cl (ETry e e1 e2 v vex1 vex2 vex3) val) ->

       (* call exception *)
        (forall (env : Environment) (cl : Closures) (i : nat) (fname : string)
          (params : list Expression) (vals : list Value) (ex : Exception),
        Datatypes.length vals = i ->
        i < Datatypes.length params ->
        (forall j : nat,
         j < i -> | env, cl, nth j params ErrorExp | -e> inl (nth j vals ErrorValue)) ->
        (forall j : nat, j < i -> P env cl (nth j params ErrorExp) (inl (nth j vals ErrorValue))) ->
        | env, cl, nth i params ErrorExp | -e> inr ex ->
        P env cl (nth i params ErrorExp) (inr ex) -> P env cl (ECall fname params) (inr ex)) ->

       (* apply exception 1 *)
       (forall (params : list Expression) (env : Environment) (exp : Expression) 
          (ex : Exception) (cl : Closures),
        | env, cl, exp | -e> inr ex ->
        P env cl exp (inr ex) -> P env cl (EApply exp params) (inr ex)) ->

       (* apply exception 2 *)
       (forall (params : list Expression) (vals : list Value) (env : Environment)
          (exp : Expression) (ex : Exception) (cl : Closures) (i : nat) 
          (v : Value),
        i = Datatypes.length vals ->
        i < Datatypes.length params ->
        | env, cl, exp | -e> inl v ->
        P env cl exp (inl v) ->
        (forall j : nat,
         j < i -> | env, cl, nth j params ErrorExp | -e> inl (nth j vals ErrorValue)) ->
        (forall j : nat, j < i -> P env cl (nth j params ErrorExp) (inl (nth j vals ErrorValue))) ->
        | env, cl, nth i params ErrorExp | -e> inr ex ->
        P env cl (nth i params ErrorExp) (inr ex) -> P env cl (EApply exp params) (inr ex)) ->

       (* apply exception 3 *)
       (forall (params : list Expression) (vals : list Value) (env : Environment) 
          (v : Value) (exp : Expression) (cl : Closures),
        Datatypes.length params = Datatypes.length vals ->
        (forall (exp0 : Expression) (val : Value),
         In (exp0, val) (combine params vals) -> | env, cl, exp0 | -e> inl val) ->
        (forall (exp0 : Expression) (val : Value),
         In (exp0, val) (combine params vals) -> P env cl exp0 (inl val)) ->
        | env, cl, exp | -e> inl v ->
        P env cl exp (inl v) ->
        (forall (ref : list ((Var + FunctionSignature) * Value) + FunctionSignature)
           (var_list : list Var) (body : Expression), v <> VClosure ref var_list body) ->
        P env cl (EApply exp params) (inr noclosure)) ->

       (* apply exception 4 *)
       (forall (params : list Expression) (vals : list Value) (env : Environment)
          (exp body : Expression) (var_list : list Var) (cl : Closures)
          (ref : Environment + FunctionSignature),
        Datatypes.length params = Datatypes.length vals ->
        | env, cl, exp | -e> inl (VClosure ref var_list body) ->
        P env cl exp (inl (VClosure ref var_list body)) ->
        (forall (exp0 : Expression) (val : Value),
         In (exp0, val) (combine params vals) -> | env, cl, exp0 | -e> inl val) ->
        (forall (exp0 : Expression) (val : Value),
         In (exp0, val) (combine params vals) -> P env cl exp0 (inl val)) ->
        Datatypes.length var_list <> Datatypes.length vals ->
        P env cl (EApply exp params) (inr args)) ->

       (* let exception 1 *)
       (forall (env : Environment) (exps : list Expression) (vals : list Value) 
          (vars : list Var) (e : Expression) (ex : Exception) (cl : Closures) (i : nat),
        Datatypes.length vals = i ->
        i < Datatypes.length exps ->
        (forall j : nat, j < i -> | env, cl, nth j exps ErrorExp | -e> inl (nth j vals ErrorValue)) ->
        (forall j : nat, j < i -> P env cl (nth j exps ErrorExp) (inl (nth j vals ErrorValue))) ->
        | env, cl, nth i exps ErrorExp | -e> inr ex ->
        P env cl (nth i exps ErrorExp) (inr ex) -> P env cl (ELet vars exps e) (inr ex)) ->
       
       (* let exception 1 *)
        (forall (env : Environment) (exps : list Expression) (vals : list Value) 
          (vars : list Var) (e : Expression) (ex : Exception) (cl : Closures),
        Datatypes.length vals = Datatypes.length exps ->
        (forall (exp : Expression) (val : Value),
         In (exp, val) (combine exps vals) -> | env, cl, exp | -e> inl val) ->
        (forall (exp : Expression) (val : Value),
         In (exp, val) (combine exps vals) -> P env cl exp (inl val)) ->
        | append_vars_to_env vars vals env, cl, e | -e> inr ex ->
        P (append_vars_to_env vars vals env) cl e (inr ex) -> P env cl (ELet vars exps e) (inr ex)) ->
        
       (* letrec exception *)
       (forall (env : Environment) (e : Expression) (fnames : list FunctionSignature)
          (funs : list (list Var * Expression)) (ex : Exception) (cl : Closures),
        Datatypes.length funs = Datatypes.length fnames ->
        | append_funs_to_env fnames funs env,
        append_funs_to_closure fnames cl (append_funs_to_env fnames funs env), e | -e> 
        inr ex ->
        P (append_funs_to_env fnames funs env)
          (append_funs_to_closure fnames cl (append_funs_to_env fnames funs env)) e 
          (inr ex) -> P env cl (ELetrec fnames funs e) (inr ex)) ->
      
      (* TODO: NEEDS EXTENSION*)
       forall (e : Environment) (c : Closures) (e0 : Expression) (v : Value + Exception), | e, c, e0 | -e> v -> P e c e0 v.

End Core_Erlang_Induction.