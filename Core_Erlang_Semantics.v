Load Core_Erlang_Environment.

(* The Semantics of Core Erlang*)
Module Core_Erlang_Semantics.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.

Import Core_Erlang_Environment.
Import Core_Erlang_Helpers.
Import Core_Erlang_Syntax.
(* Import Core_Erlang_Closures. *)

(*TODO: Need to be extended *)
Definition eval (fname : string) (params : list Value) : Value + Exception :=
match fname, length params, params with
| "plus"%string, 2, [VLiteral (Integer a); VLiteral (Integer b)] => inl (VLiteral (Integer (a + b)))
| "plus"%string, _, _ => inr badarith
| "fwrite"%string, 1, e => inl ok
| "fread"%string, 1, e => inl ok
| "and"%string, 2, [VLiteral (Atom a); VLiteral (Atom b)] => match a, b with
                                                             | "true"%string, "true"%string => inl ttrue
                                                             | "false"%string, "true"%string => inl ffalse
                                                             | "true"%string, "false"%string => inl ffalse
                                                             | "false"%string, "false"%string => inl ffalse
                                                             | _, _ => inr badarg
                                                             end
| _, _, _ => inr undef
end.

(* Expression -> Coq type *)
(* Definition eval_atom (a : string) : bool :=
match a with
| "true"%string => true
| "false"%string => false
| _ => false
end.*)

Reserved Notation "| env , e | -e> e'" (at level 70).

(* TODO: This closure implementation does not work properly when redefining a function multiple times and calling them in one-another's body *)
Inductive eval_expr : Environment -> Expression -> (Value + Exception) -> Prop :=
| eval_emptylist (env : Environment):
  |env, EEmptyList| -e> inl VEmptyList

(* literal evaluation rule *)
| eval_lit (env : Environment) (l : Literal):
  |env, ELiteral l| -e> inl (VLiteral l)

(* variable evaluation rule *)
| eval_var (env:Environment) (s: Var):
  |env, EVar s| -e> get_value env (inl s)

(* Function Signature evaluation rule *)
| eval_funid (env:Environment) (fsig : FunctionIdentifier):
  |env, EFunId fsig| -e> get_value env (inr fsig)

(* Function evaluation *)
| eval_fun (env : Environment) (vl : list Var) (e : Expression):
  |env, EFun vl e| -e> inl (VClosure env [] vl e)

(* tuple evaluation rule *)
| eval_tuple (env: Environment) (exps : list Expression) (vals : list Value):
  length exps = length vals ->
  (
    forall exp : Expression, forall val : Value,
    In (exp, val) (combine exps vals) ->
      |env, exp| -e> inl val
  )
->
  |env, ETuple exps| -e> inl (VTuple vals)

(* list evaluation rule *)
| eval_list (env:Environment) (hd tl: Expression) (hdv tlv : Value) :
  |env, hd| -e> inl hdv ->
  |env, tl| -e> inl tlv
->
  |env, EList hd tl| -e> inl (VList hdv tlv)

(* case evaluation rules *)
| eval_case (env: Environment) (e guard exp: Expression) (v : Value) (v' : Value + Exception) (patterns : list Pattern) (guards : list Expression) (bodies : list Expression) (bindings: list (Var * Value)) (i : nat):
  |env, e| -e> inl v ->
  length patterns = length guards ->
  length bodies = length patterns ->
  i < length patterns ->
  match_clause v patterns guards bodies i = Some (guard, exp, bindings) ->
  (forall j : nat, j < i -> 

    (forall gg ee bb, match_clause v patterns guards bodies j = Some (gg, ee, bb) -> ((|add_bindings bb env, gg| -e> inl ffalse )))

  ) ->
  |add_bindings bindings env, guard| -e> inl ttrue -> 
  |add_bindings bindings env, exp| -e> v'
->
  |env, ECase e patterns guards bodies| -e> v'


(* call evaluation rule *)
| eval_call (env: Environment) (v : Value + Exception) (params : list Expression) (vals : list Value) (fname: string) :
  length params = length vals ->
  (
    forall exp : Expression, forall val : Value,
    In (exp, val) (combine params vals) -> 
    (
      |env, exp| -e> inl val
    )
  ) ->
  eval fname vals = v
->
  |env, ECall fname params| -e> v

(* apply functions*)
| eval_apply (params : list Expression) (vals : list Value) (env : Environment) (exp : Expression) (body : Expression) (v : Value + Exception) (var_list : list Var) (ref : Environment) (ext : list (FunctionIdentifier * FunctionalExpression)) :
  length params = length vals ->
  |env, exp| -e> inl (VClosure ref ext var_list body) (* helper functions possible here??? *) ->
  length var_list = length vals
  ->
  (
    forall exp : Expression, forall val : Value,
    In (exp, val) (combine params vals) ->
    (
      |env, exp| -e> inl val
    )
  )
  ->
  |append_vars_to_env var_list vals (get_env ref ref ext ext), body| -e> v
->
  |env, EApply exp params| -e> v

(* let evaluation rule *)
| eval_let (env: Environment) (exps: list Expression) (vals : list Value) (vars: list Var) (e : Expression) (v : Value + Exception) :
  length vals = length exps ->
  (
    forall exp : Expression, forall val : Value, In (exp, val) (combine exps vals) -> 
    (
      |env, exp| -e> inl val
    )
  )
  ->
    |append_vars_to_env vars vals env, e| -e> v
->
  |env, ELet vars exps e| -e> v

(* Letrec evaluation rule *)
| eval_letrec (env: Environment) (e : Expression)  (fnames : list FunctionIdentifier) (paramss: list (list Var)) (bodies : list Expression) (v : Value + Exception) :
  length fnames = length paramss ->
  length fnames = length bodies ->
  (
     |append_funs_to_env fnames paramss bodies env env (list_functions fnames paramss bodies), e| -e> v
  )
->
  |env, ELetrec fnames paramss bodies e| -e> v


(* map evaluation rule *)
| eval_map (kl vl: list Expression) (vvals kvals kl' vl' : list Value) (env: Environment) :
  length vl = length kl ->
  length vl = length vvals ->
  length vl = length kvals ->
  make_value_map kvals vvals = (kl', vl') ->
  (
    forall i : nat, i < length vl ->
    |env, nth i kl ErrorExp| -e> inl (nth i kvals ErrorValue) /\
    |env, nth i vl ErrorExp| -e> inl (nth i vvals ErrorValue)
  )
->
  |env, EMap kl vl| -e> inl (VMap kl' vl')


  (* EXCEPTIONS *)
(* list head exception *)
| eval_list_ex_hd (env: Environment) (hd tl : Expression) (ex : Exception) :
  |env, hd| -e> inr ex 
->
  |env, EList hd tl| -e> inr ex

(* list tail exception *)
| eval_list_ex_tl (env: Environment) (hd tl : Expression) (ex : Exception) (vhd : Value) :
  |env, hd| -e> inl vhd -> |env, tl| -e> inr ex 
->
  |env, EList hd tl| -e> inr ex

(* tuple exception *)
| eval_tuple_ex (env: Environment) (i : nat) (exps : list Expression) (vals : list Value) (ex : Exception) :
   length vals = i -> i < length exps ->
  (forall j, j < i -> |env, nth j exps ErrorExp| -e> inl (nth j vals ErrorValue)) ->
  |env, nth i exps ErrorExp| -e> inr ex
->
  |env, ETuple exps| -e> inr ex


(* try *)
| eval_try (env: Environment) (e e1 e2 : Expression) (v vex1 vex2 vex3 : Var) (val : Value + Exception) (val' : Value) :
  |env, e| -e> inl val' -> |append_vars_to_env [v] [val'] env, e1| -e> val
->
  |env, ETry e e1 e2 v vex1 vex2 vex3| -e> val

| eval_try_catch (env: Environment) (e e1 e2 : Expression) (v vex1 vex2 vex3 : Var) (val : Value + Exception) (ex : Exception) :
  |env, e| -e> inr ex ->
  |append_vars_to_env [vex1; vex2; vex3] [make_value_from_ex_class (fst (fst ex)); snd (fst ex); snd ex] env, e2| -e> val
->
  |env, ETry e e1 e2 v vex1 vex2 vex3| -e> val

(* case 2x *)
(** Pattern matching exception *)
| eval_case_ex_pat (env: Environment) (e : Expression) (ex : Exception) (patterns : list Pattern) (guards : list Expression) (bodies : list Expression) (bindings: list (Var * Value)):
  length patterns = length guards ->
  length patterns = length bodies ->
  |env, e| -e> inr ex
->
  |env, ECase e patterns guards bodies| -e> inr ex

(** ith guard exception *)
| eval_case_ex_guard (env: Environment) (e e'' guard exp: Expression) (v : Value) (ex : Exception) (patterns : list Pattern) (guards : list Expression) (bodies : list Expression) (bindings: list (Var * Value)) (i : nat):
  length patterns = length guards ->
  length patterns = length bodies ->
  |env, e| -e> inl v ->
  match_clause v patterns guards bodies i = Some (guard, exp, bindings) ->
  (forall j : nat, j < i -> 

    (forall gg ee bb, match_clause v patterns guards bodies j = Some (gg, ee, bb) -> ((|add_bindings bb env, gg| -e> inl ffalse )))

  ) ->
  |add_bindings bindings env, guard| -e> inr ex
->
  |env, ECase e patterns guards bodies| -e> inr ex


(* call 1x *)
| eval_call_ex (env: Environment) (i : nat) (fname : string) (params : list Expression) (vals : list Value) (ex : Exception) :
  length vals = i -> i < length params ->
  (forall j, j < i -> 
    |env, nth j params ErrorExp| -e> inl (nth j vals ErrorValue)
  ) ->
  |env, nth i params ErrorExp| -e> inr ex

->
  |env, ECall fname params| -e> inr ex

(* apply 4x *)
(** According to ref. implementation, here it is not needed to check the arg number *)

(** if name evaluates to exception *)
| eval_apply_ex_closure_ex (params : list Expression) (env : Environment) (exp : Expression)  (ex : Exception) :
  |env, exp| -e> inr ex
->
  |env, EApply exp params| -e> inr ex

(** name and some parameters evaluate to values *)
| eval_apply_ex_params (params : list Expression) (vals : list Value) (env : Environment) (exp : Expression) (ex : Exception) (i : nat) (v : Value) :
  i = length vals -> i < length params
  ->
  |env, exp| -e> inl v ->
  (forall j, j < i -> 
    |env, nth j params ErrorExp| -e> inl (nth j vals ErrorValue)
  ) ->
  |env, nth i params ErrorExp| -e> inr ex
->
  |env, EApply exp params| -e> inr ex

(** Then we check if the name evaluates to a closure *)
| eval_apply_ex_closure (params : list Expression) (vals: list Value) (env : Environment) (v : Value) (exp : Expression) :
  length params = length vals ->
  (
    forall exp : Expression, forall val : Value,
    In (exp, val) (combine params vals) ->
    (
      |env, exp| -e> inl val
    )
  ) ->
  |env, exp| -e> inl v ->
  (forall ref ext var_list body, v <> VClosure ref ext var_list body)
->
  |env, EApply exp params| -e> inr noclosure

(** too few or too many arguments are given *)
| eval_apply_ex_param_count (params : list Expression) (vals : list Value) (env : Environment) (exp : Expression) (body : Expression) (var_list : list Var) (ref : Environment) (ext : list (FunctionIdentifier * FunctionalExpression)):
  length params = length vals ->
  |env, exp| -e> inl (VClosure ref ext var_list body) ->
  (
    forall exp : Expression, forall val : Value,
    In (exp, val) (combine params vals) ->
    (
      |env, exp| -e> inl val
    )
  ) ->
  length var_list <> length vals
->
  |env, EApply exp params| -e> inr args

(* let 1x *)
| eval_let_ex_param (env: Environment) (exps: list Expression) (vals : list Value) (vars: list Var) (e : Expression) (ex : Exception) (i : nat) :
  length vals = i -> i < length exps ->
  (forall j, j < i -> 
    |env, nth j exps ErrorExp| -e> inl (nth j vals ErrorValue)
  ) ->
  |env, nth i exps ErrorExp| -e> inr ex
->
  |env, ELet vars exps e| -e> inr ex

(* map 2x *)
| eval_map_ex_key (kl vl: list Expression) (vvals kvals : list Value) (env: Environment) (i : nat) (ex : Exception) :
  length vl = length kl ->
  i = length vvals ->
  i = length kvals ->
  i < length vl ->
  (
    forall j, j < i ->
    |env, nth j kl ErrorExp| -e> inl (nth j kvals ErrorValue) /\
    |env, nth j vl ErrorExp| -e> inl (nth j vvals ErrorValue)
  )
  ->
  |env, nth i kl ErrorExp| -e> inr ex
->
  |env, EMap kl vl| -e> inr ex

| eval_map_ex_val (kl vl: list Expression) (vvals kvals : list Value) (env: Environment) (i : nat) (ex : Exception) (val : Value) :
  length vl = length kl ->
  i = length vvals ->
  i = length kvals ->
  i < length vl ->
  (
    forall j, j < i ->
    |env, nth j kl ErrorExp| -e> inl (nth j kvals ErrorValue) /\
    |env, nth j vl ErrorExp| -e> inl (nth j vvals ErrorValue)
  )
  ->
  |env, nth i kl ErrorExp| -e> inl val
  ->
  |env, nth i vl ErrorExp| -e> inr ex
->
  |env, EMap kl vl| -e> inr ex

where "| env , e | -e> e'" := (eval_expr env e e')
.

(* These are the initialization function before evaluating a module *)
(* Fixpoint add_elements_to_env (fl : list ErlFunction) : Environment :=
match fl with
| [] => []
| (TopLevelFun sig (vl,exp))::xs => insert_value_no_overwrite (add_elements_to_env xs) (inr sig) (VClosure (inr sig) vl exp)
end.

Fixpoint initialize_proving (module : ErlModule) : Environment :=
match module with
| ErlMod s fl => add_elements_to_env fl
end.

Fixpoint add_elements_to_closure (fl : list ErlFunction) (module : ErlModule) : Closures :=
match fl with
| [] => []
| (TopLevelFun sig f)::xs => set_closure_no_overwrite (add_elements_to_closure xs module) sig (initialize_proving module)
end.

Fixpoint initialize_proving_closures (module : ErlModule) : Closures :=
match module with
| ErlMod s fl => add_elements_to_closure fl module
end. *)

End Core_Erlang_Semantics.