Load Core_Erlang_Closures.

(* The Semantics of Core Erlang*)
Module Core_Erlang_Semantics.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.

Import Core_Erlang_Closures.
Import Core_Erlang_Environment.
Import Core_Erlang_Helpers.
Import Core_Erlang_Syntax.


(*TODO: Need to be extended *)
Definition eval (e:Environment) (fname : FunctionSignature) (params : list Expression) : Expression :=
match fname, params with
| ("plus"%string, 2), [ELiteral (Integer a); ELiteral (Integer b)] => (ELiteral (Integer (a + b)))
| _, _ => ErrorExp
end.

(* Expression -> Coq type *)
(* Definition eval_atom (a : string) : bool :=
match a with
| "true"%string => true
| "false"%string => false
| _ => false
end.*)

Reserved Notation "e -e> e'" (at level 70).
Inductive eval_expr : Environment * Closures * Expression -> Expression -> Prop :=

(*(* reflexive rule *)
| eval_same (env: Environment) (e: Expression) (cl: Closures):
(env, cl, e) -e> e*)

(* variable evaluation rule *)
| eval_var (env:Environment) (s: Var) (cl: Closures):
(env, cl, EVar s) -e> proj1_sig (get_value env (inl s))

(* Function evaluation rule -> This is not needed. For function evaluation a value rule is more appropriate *)

(* tuple evaluation rule *)
| eval_tuple (env: Environment) (exprs1 exprs2: list Expression) (cl: Closures):
  length exprs1 = length exprs2 ->
  (
    forall exp exp' : Expression,
    In (exp, exp') (combine exprs1 exprs2) ->
    (
      (env, cl, exp) -e> exp' \/ exp = exp'
    )
    /\
    exp' val
  ) ->
  ~(ETuple exprs1 = ETuple exprs2)
->
  (env, cl, ETuple exprs1) -e> ETuple exprs2

(* list evaluation rule *)
| eval_list (env:Environment) (hd tl e' e'': Expression) (cl: Closures):
  ((env, cl, hd) -e> e' \/ hd = e') /\ e' val ->
  ((env, cl, tl) -e> e'' \/ tl = e'') /\ e'' val ->
  ~(EList hd tl = EList e' e'')
->
  (env, cl, EList hd tl) -e> EList e' e''

(* case evaluation rules *)
(*| eval_case (env: Environment) (e e' e'' guard exp: Expression) (cs: list Clause) (bindings: list (Var * Expression)) (cl: Closures):
(env, cl, e) -e> e' -> match_clauses e' cs = Some (guard, exp, bindings) ->
(add_bindings bindings env, cl, guard) -e> ELiteral (Atom "true"%string) -> (add_bindings bindings env, cl, exp) -e> e'' ->
(env, cl, ECase e cs) -e> e''*)

(* call evaluation rule *)
| eval_call (env: Environment) (e': Expression) (params exprs2: list Expression) (fname: FunctionSignature) (cl: Closures):
  length params = length exprs2 ->
  (
    forall exp exp' : Expression, 
    In (exp, exp') (combine params exprs2) -> 
    (
      (env, cl, exp) -e> exp' \/ exp = exp'
    )
    /\
    exp' val
  ) ->
  eval env fname exprs2 = e'
  /\
  e' val
->
  (env, cl, ECall fname params) -e> e'

(* Evaluation for top-level functions *)
| eval_apply_top (exprs1: list Expression) (exprs2 : list Value) (env: Environment) (name: string) (args: nat) (e': Expression) (cl: Closures):
  length exprs1 = length exprs2 -> 
  length exprs1 = args ->
  (
    forall exp exp', 
    In (exp, exp') (combine exprs1 exprs2) -> 
    (
      (env, cl, exp) -e> proj1_sig exp' \/ exp = proj1_sig exp'
    )
  )
  ->
  (
    (append_vars_to_env (get_vars  (get_value env (inr (name, args)))) 
                          exprs2
                          (get_env_from_closure (inr (name, args)) cl),
    cl,
    get_fun_exp (get_value env (inr (name, args)))) -e> e' 
    \/
    get_fun_exp (get_value env (inr (name, args))) = e'
  )
  /\
  e' val
->
  (env, cl, EApplyTopLevel (name, args) exprs1) -e> e'

(* apply for non-top level functions, these are locally defined *)
| eval_apply (exprs1: list Expression) (exprs2 : list Value) (env: Environment) (name: Var) (e': Expression) (cl: Closures):
  length exprs1 = length exprs2 ->
  (
    forall exp exp', In (exp, exp') (combine exprs1 exprs2) ->
    (
      (env, cl, exp) -e> proj1_sig exp' \/ exp = proj1_sig exp'
    )
  )
  ->
  (
    (append_vars_to_env (get_vars (get_value env (inl name)))
                         exprs2 (get_env_from_closure (inl name) cl),
      cl,
      get_fun_exp (get_value env (inl name))) -e> e'
      \/
      get_fun_exp (get_value env (inl (name))) = e'
    )
    /\
    e' val
->
  (env, cl, EApply name exprs1) -e> e'

(* let evaluation rule, maybe Value type is needed for env e1 -e> v *)
| eval_let (env: Environment) (exps: list Expression) (exprs2 : list Value) (vars: list Var) (e e': Expression) (cl: Closures):
  length exprs2 = length exps ->
  (
    forall exp exp', In (exp, exp') (combine exps exprs2) -> 
    (
      (env, cl, exp) -e> proj1_sig exp' \/ exp = proj1_sig exp'
    )
  )
  ->
  (
    (append_vars_to_env vars exprs2 env, 
     append_vars_to_closure vars (valuelist_to_exp exprs2) cl env,
     e) -e> e'
     \/
     e = e'
  )
  /\
  e' val
->
  (env, cl, ELet vars exps e) -e> e'

(* Letrec evaluation rule *)
| eval_letrec (env: Environment) (e e': Expression)  (fnames : list FunctionSignature) (funs: list Fun) (cl: Closures):
  length funs = length fnames -> (* Here the parameter functions are not evaluated *)
  (
    (append_funs_to_env fnames funs env, 
     append_funs_to_closure fnames cl (append_funs_to_env fnames funs env), 
     e) -e> e' 
     \/
     e = e'
   )
   /\
   e' val
->
  (env, cl, ELetrec fnames funs e) -e> e'


(* map evaluation rule *)
| eval_map (kl vl: list Expression) (exprs2 : list Value) (env: Environment) (cl: Closures):
  (
    forall exp : Expression, In exp kl ->
    exp val
  ) ->
  length vl = length kl ->
  length vl = length exprs2 ->
  (
    forall exp exp', In (exp, exp') (combine vl exprs2) -> 
    (
      (env, cl, exp) -e> proj1_sig exp' \/ exp = proj1_sig exp'
    )
  ) ->
  EMap kl vl <> EMap kl (valuelist_to_exp exprs2)
->
  (env, cl, EMap kl vl) -e> EMap kl (valuelist_to_exp exprs2)

(*(* coversion rules *)
| eval_tuple_to_lit env cl:
(env, cl, ETuple []) -e> ELiteral EmptyTuple

| eval_map_to_lit env cl:
(env, cl, EMap [] []) -e> ELiteral EmptyMap*)

where "e -e> e'" := (eval_expr e e')
.

Check eval_expr_ind.

(* These are the initialization function before evaluating a module *)
Fixpoint add_elements_to_env (fl : list ErlFunction) : Environment :=
match fl with
| [] => []
| (TopLevelFun sig f)::xs => insert_value_no_overwrite (add_elements_to_env xs) (inr sig) (exist _ (EFunction f) (VJ_Function _))
end.

Fixpoint initialize_proving (module : ErlModule) : Environment :=
match module with
| ErlMod s fl => add_elements_to_env fl
end.

Fixpoint add_elements_to_closure (fl : list ErlFunction) (module : ErlModule) : Closures :=
match fl with
| [] => []
| (TopLevelFun sig f)::xs => set_closure_no_overwrite (add_elements_to_closure xs module) (inr sig) (initialize_proving module)
end.

Fixpoint initialize_proving_closures (module : ErlModule) : Closures :=
match module with
| ErlMod s fl => add_elements_to_closure fl module
end.

End Core_Erlang_Semantics.