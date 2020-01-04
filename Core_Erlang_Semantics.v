Load Core_Erlang_Closures.

(* The Semantics of Core Erlang*)
Module Core_Erlang_Semantics.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.

Import Core_Erlang_Environment.
Import Core_Erlang_Helpers.
Import Core_Erlang_Syntax.
Import Core_Erlang_Closures.

(*TODO: Need to be extended *)
Definition eval (fname : string) (params : list Value) : Value :=
match fname, length params, params with
| "plus"%string, 2, [VLiteral (Integer a); VLiteral (Integer b)] => (VLiteral (Integer (a + b)))
| "fwrite"%string, 1, e => ok
| "and"%string, 2, [VLiteral (Atom a); VLiteral (Atom b)] => match a, b with
                                                             | "true"%string, "true"%string => tt
                                                             | "false"%string, "true"%string => ff
                                                             | "true"%string, "false"%string => ff
                                                             | "false"%string, "false"%string => ff
                                                             | _, _ => ErrorValue
                                                             end
| _, _, _ => ErrorValue
end.

(* Expression -> Coq type *)
(* Definition eval_atom (a : string) : bool :=
match a with
| "true"%string => true
| "false"%string => false
| _ => false
end.*)

Reserved Notation "e -e> e'" (at level 70).

(* TODO: This closure implementation does not work properly when redefining a function multiple times and calling them in one-another's body *)
Inductive eval_expr : Environment * Closures * Expression -> Value -> Prop :=

(* literal evaluation rule *)
| eval_lit (env : Environment) (l : Literal) (cl : Closures):
(env, cl, ELiteral l) -e> VLiteral l

(* variable evaluation rule *)
| eval_var (env:Environment) (s: Var) (cl : Closures):
(env, cl, EVar s) -e> get_value env (inl s)

(* Function Signature evaluation rule *)
| eval_funsig (env:Environment) (fsig : FunctionSignature) (cl : Closures):
(env, cl, EFunSig fsig) -e> get_value env (inr fsig)

(* Function evaluation *)
| eval_fun (env : Environment) (vl : list Var) (e : Expression) (cl : Closures):
(env, cl, EFun vl e) -e> VClosure (inl ""%string) vl e

(* tuple evaluation rule *)
| eval_tuple (env: Environment) (exps : list Expression) (vals : list Value) (cl : Closures):
  length exps = length vals ->
  (
    forall exp : Expression, forall val : Value,
    In (exp, val) (combine exps vals) ->
      (env, cl, exp) -e> val
  )
->
  (env, cl, ETuple exps) -e> VTuple vals

(* list evaluation rule *)
| eval_list (env:Environment) (hd tl: Expression) (hdv tlv : Value) (cl : Closures):
  (env, cl, hd) -e> hdv ->
  (env, cl, tl) -e> tlv
->
  (env, cl, EList hd tl) -e> VList hdv tlv

(* case evaluation rules *)
| eval_case (env: Environment) (e e'' guard exp: Expression) (v v' : Value) (cs: list Clause) (bindings: list (Var * Value)) (cl: Closures) (i : nat):
  (env, cl, e) -e> v ->
  match_clause v cs i = Some (guard, exp, bindings) ->
  (forall j : nat, j < i -> 
  
    match_clause v cs j = None \/ (forall gg ee bb, match_clause v cs j = Some (gg, ee, bb) -> (((add_bindings bb env, cl, gg) -e> ff )))
  
  ) ->
  (add_bindings bindings env, cl, guard) -e> tt -> 
  (add_bindings bindings env, cl, exp) -e> v'
->
  (env, cl, ECase e cs) -e> v'


(* call evaluation rule *)
| eval_call (env: Environment) (v : Value) (params : list Expression) (vals : list Value) (fname: string) (cl : Closures) :
  length params = length vals ->
  (
    forall exp : Expression, forall val : Value,
    In (exp, val) (combine params vals) -> 
    (
      (env, cl, exp) -e> val
    )
  ) ->
  eval fname vals = v
->
  (env, cl, ECall fname params) -e> v

(* apply functions*)
(* SOLVED TODO does not work on unnamed functions. Closure environment must be modified *)
| eval_apply (params : list Expression) (vals : list Value) (env : Environment) (name : Expression) (body : Expression) (v : Value) (var_list : list Var) (cl : Closures) (ref : Var + FunctionSignature) :
  length params = length vals ->
  (env, cl, name) -e> VClosure ref var_list body (* helper functions possible here??? *)
  ->
  (
    forall exp : Expression, forall val : Value,
    In (exp, val) (combine params vals) ->
    (
      (env, cl, exp) -e> val
    )
  )
  ->
  (append_vars_to_env var_list vals (get_env ref cl env), cl, body) -e> v
->
  (env, cl, EApply name params) -e> v

(* let evaluation rule *)
| eval_let (env: Environment) (exps: list Expression) (vals : list Value) (vars: list Var) (e : Expression) (v : Value) (cl : Closures) :
  length vals = length exps ->
  (
    forall exp : Expression, forall val : Value, In (exp, val) (combine exps vals) -> 
    (
      (env, cl, exp) -e> val
    )
  )
  ->
    (* The variable appending can modify the closure values (change their name reference) *)
    (append_vars_to_env vars vals env, append_vars_to_closure vars vals cl env, e) -e> v
->
  (env, cl, ELet vars exps e) -e> v

(* Letrec evaluation rule -- ENDLESS RECURSION *)
| eval_letrec (env: Environment) (e : Expression)  (fnames : list FunctionSignature) (funs: list ((list Var) * Expression)) (v : Value) (cl : Closures):
  length funs = length fnames ->
  (
    (append_funs_to_env fnames funs env, append_funs_to_closure fnames cl (append_funs_to_env fnames funs env), e) -e> v
  )
->
  (env, cl, ELetrec fnames funs e) -e> v


(* map evaluation rule *)
| eval_map (kl vl: list Expression) (vvals kvals : list Value) (env: Environment) (cl : Closures) :
  length vl = length kl ->
  length vl = length vvals ->
  length vl = length kvals ->
  (
    forall exp : Expression, forall val : Value,
    In (exp, val) (combine kl kvals) -> 
    (
      (env, cl, exp) -e> val
    )
  ) ->
  (
    forall exp : Expression, forall val : Value,
    In (exp, val) (combine vl vvals) -> 
    (
      (env, cl, exp) -e> val
    )
  )
->
  (env, cl, EMap kl vl) -e> VMap kvals vvals

where "e -e> e'" := (eval_expr e e')
.

(* (* These are the initialization function before evaluating a module *)
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
end. *)

End Core_Erlang_Semantics.