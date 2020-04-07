Load Core_Erlang_Side_Effects.

(* The Semantics of Core Erlang*)
Module Core_Erlang_Semantics.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.

Import Core_Erlang_Environment.
Import Core_Erlang_Helpers.
Import Core_Erlang_Syntax.
Import Core_Erlang_Side_Effects.
(* Import Core_Erlang_Closures. *)

(*TODO: Need to be extended *)
Definition eval (fname : string) (params : list Value) (eff : SideEffectList) : ((Value + Exception) * SideEffectList) :=
match fname, length params, params with
| "plus"%string, 2, [VLiteral (Integer a); VLiteral (Integer b)] => (inl (VLiteral (Integer (a + b))), eff)
| "plus"%string, _, _ => (inr badarith, eff)
| "fwrite"%string, 1, e => (inl ok, eff ++ [(Output, params)])

(* TODO: THIS CAN MODIFY THE ENVIRONMENT *)
| "fread"%string, 2, e => (inl (VTuple [ok; nth 1 params ErrorValue]), eff ++ [(Input, params)])


| "and"%string, 2, [VLiteral (Atom a); VLiteral (Atom b)] => match a, b with
                                                             | "true"%string, "true"%string => (inl ttrue, eff)
                                                             | "false"%string, "true"%string => (inl ffalse, eff)
                                                             | "true"%string, "false"%string => (inl ffalse, eff)
                                                             | "false"%string, "false"%string => (inl ffalse, eff)
                                                             | _, _ => (inr badarg, eff)
                                                             end
| _, _, _ => (inr undef, eff)
end.

(* Expression -> Coq type *)
(* Definition eval_atom (a : string) : bool :=
match a with
| "true"%string => true
| "false"%string => false
| _ => false
end.*)

Reserved Notation "| env , e , eff | -e> | e' , eff' |" (at level 70).

(* TODO: This closure implementation does not work properly when redefining a function multiple times and calling them in one-another's body *)
Inductive eval_expr : Environment -> Expression -> SideEffectList -> (Value + Exception) -> SideEffectList -> Prop :=
| eval_emptylist (env : Environment) (eff : SideEffectList):
  |env, EEmptyList, eff| -e> |inl VEmptyList, eff|

(* literal evaluation rule *)
| eval_lit (env : Environment) (l : Literal) (eff : SideEffectList):
  |env, ELiteral l, eff| -e> |inl (VLiteral l), eff|

(* variable evaluation rule *)
| eval_var (env:Environment) (s: Var) (eff : SideEffectList):
  |env, EVar s, eff| -e> |get_value env (inl s), eff|

(* Function Signature evaluation rule *)
| eval_funid (env:Environment) (fsig : FunctionIdentifier) (eff : SideEffectList):
  |env, EFunId fsig, eff| -e> |get_value env (inr fsig), eff|

(* Function evaluation *)
| eval_fun (env : Environment) (vl : list Var) (e : Expression) (eff : SideEffectList):
  |env, EFun vl e, eff| -e> |inl (VClosure env [] vl e), eff|

(* tuple evaluation rule *)
| eval_tuple (env: Environment) (exps : list Expression) (vals : list Value) (eff1 eff2 : SideEffectList) (eff : list SideEffectList):
  length exps = length vals ->
  length eff = length exps ->
  (
    forall i, i < length exps ->
      |env, nth i exps ErrorExp, concatn eff1 eff i| -e> |inl (nth i vals ErrorValue), concatn eff1 eff (S i)|
  ) ->
  eff2 = concatn eff1 eff (length vals)
->
  |env, ETuple exps, eff1| -e> |inl (VTuple vals), eff2|

(* list evaluation rule *)
| eval_list (env:Environment) (hd tl: Expression) (hdv tlv : Value) (eff1 eff2 eff3 eff4 : SideEffectList) :
  eff4 = eff1 ++ eff2 ++ eff3 ->
  |env, tl, eff1| -e> |inl tlv, eff1 ++ eff2| ->
  |env, hd, eff1 ++ eff2| -e> |inl hdv, eff4|
->
  |env, EList hd tl, eff1| -e> |inl (VList hdv tlv), eff4|

(* case evaluation rules *)
| eval_case (env: Environment) (e guard exp: Expression) (v : Value) (v' : Value + Exception) (patterns : list Pattern) (guards : list Expression) (bodies : list Expression) (bindings: list (Var * Value)) (i : nat) (eff1 eff2 eff3 eff4 : SideEffectList) :
  length patterns = length guards ->
  length bodies = length patterns ->
  |env, e, eff1| -e> |inl v, eff1 ++ eff2| ->
  i < length patterns ->
  match_clause v patterns guards bodies i = Some (guard, exp, bindings) ->
  (forall j : nat, j < i -> 

    (** THESE GUARDS MUST BE SIDE-EFFECT FREE ACCORDING TO 1.0.3 LANGUAGE SPECIFICATION *)
    (forall gg ee bb, match_clause v patterns guards bodies j = Some (gg, ee, bb) -> ((|add_bindings bb env, gg, eff1 ++ eff2| -e> |inl ffalse, eff1 ++ eff2| )))

  ) ->
  eff4 = eff1 ++ eff2 ++ eff3 ->
  |add_bindings bindings env, guard, eff1 ++ eff2| -e> |inl ttrue, eff1 ++ eff2| -> 
  |add_bindings bindings env, exp, eff1 ++ eff2| -e> |v', eff1 ++ eff2 ++ eff3|
->
  |env, ECase e patterns guards bodies, eff1| -e> |v', eff4|


(* call evaluation rule *)
| eval_call (env: Environment) (v : Value + Exception) (params : list Expression) (vals : list Value) (fname: string) (eff1 eff2: SideEffectList) (eff : list SideEffectList) :
  length params = length vals ->
  length params = length eff ->
  (
    forall i, i < length params ->
      |env, nth i params ErrorExp, concatn eff1 eff i| -e> |inl (nth i vals ErrorValue), concatn eff1 eff (S i)|
  ) ->
  eval fname vals (concatn eff1 eff (length params)) = (v, eff2)
->
  |env, ECall fname params, eff1| -e> |v, eff2|

(* apply functions*)
| eval_apply (params : list Expression) (vals : list Value) (env : Environment) (exp : Expression) (body : Expression) (v : Value + Exception) (var_list : list Var) (ref : Environment) (ext : list (FunctionIdentifier * FunctionalExpression)) (eff1 eff2 eff3 eff4 : SideEffectList) (eff : list SideEffectList) :
  length params = length vals ->
  |env, exp, eff1| -e> |inl (VClosure ref ext var_list body), eff1 ++ eff2| (* helper functions possible here??? *) ->
  length var_list = length vals
  ->
  length params = length eff ->
  (
    forall i, i < length params ->
      |env, nth i params ErrorExp, concatn (eff1 ++ eff2) eff i| -e> |inl (nth i vals ErrorValue), concatn (eff1 ++ eff2) eff (S i)|
  )
  ->
  eff4 = concatn (eff1 ++ eff2) eff (length params) ++ eff3
  ->
  |append_vars_to_env var_list vals (get_env ref ref ext ext), body, concatn (eff1 ++ eff2) eff (length params)| -e> |v, eff4|
->
  |env, EApply exp params, eff1| -e> |v, eff4|

(* let evaluation rule *)
| eval_let (env: Environment) (exps: list Expression) (vals : list Value) (vars: list Var) (e : Expression) (v : Value + Exception) (eff : list SideEffectList) (eff1 eff2 eff3 : SideEffectList) :
  length vals = length exps ->
  length exps = length eff ->
  (
    forall i, i < length exps ->
      |env, nth i exps ErrorExp, concatn eff1 eff i| -e> |inl (nth i vals ErrorValue), concatn eff1 eff (S i)|
  )
  ->
    eff3 = concatn eff1 eff (length exps) ++ eff2
  ->
    |append_vars_to_env vars vals env, e, concatn eff1 eff (length exps)| -e> |v, eff3|
->
  |env, ELet vars exps e, eff1| -e> |v, eff3|

(* Letrec evaluation rule *)
| eval_letrec (env: Environment) (e : Expression)  (fnames : list FunctionIdentifier) (paramss: list (list Var)) (bodies : list Expression) (v : Value + Exception) (eff1 eff2 eff3 : SideEffectList) :
  length fnames = length paramss ->
  length fnames = length bodies ->
  (
     |append_funs_to_env fnames paramss bodies env env (list_functions fnames paramss bodies), e, eff1| -e> |v, eff1 ++ eff2|
  ) ->
  eff3 = eff1 ++ eff2
->
  |env, ELetrec fnames paramss bodies e, eff1| -e> |v, eff3|


(* map evaluation rule *)
| eval_map (kl vl: list Expression) (vvals kvals kl' vl' : list Value) (env: Environment) (eff1 eff2 : SideEffectList) (eff : list SideEffectList) :
  length vl = length kl ->
  length vl = length vvals ->
  length vl = length kvals ->
  length eff = (length kl) * 2 ->
  make_value_map kvals vvals = (kl', vl') ->
  (
    forall i : nat, i < length vl ->
    |env, nth i kl ErrorExp, concatn eff1 eff  (2 * i)| -e> |inl (nth i kvals ErrorValue), concatn eff1 eff (S (2*i))|
  ) ->
  (
    forall i : nat, i < length vl ->
    |env, nth i vl ErrorExp, concatn eff1 eff (S (2* i))| -e> |inl (nth i vvals ErrorValue), concatn eff1 eff (S (S (2*i)))|
  ) ->
  eff2 = concatn eff1 eff ((length kvals) * 2)
->
  |env, EMap kl vl, eff1| -e> |inl (VMap kl' vl'), eff2|


  (* EXCEPTIONS *)
(* list tail exception *)
| eval_list_ex_tl (env: Environment) (hd tl : Expression) (ex : Exception) (eff1 eff2 eff3 : SideEffectList) :
  eff3 = eff1 ++ eff2 ->
  |env, tl, eff1| -e> |inr ex, eff1 ++ eff2|
->
  |env, EList hd tl, eff1| -e> |inr ex, eff3|

(* list head exception *)
| eval_list_ex_hd (env: Environment) (hd tl : Expression) (ex : Exception) (vtl : Value) (eff1 eff2 eff3 eff4 : SideEffectList) :
  eff4 = eff1 ++ eff2 ++ eff3 ->
  |env, tl, eff1| -e> |inl vtl, eff1 ++ eff2| -> 
  |env, hd, eff1 ++ eff2| -e> |inr ex, eff4|
->
  |env, EList hd tl, eff1| -e> |inr ex, eff4|

(* tuple exception *)
| eval_tuple_ex (env: Environment) (i : nat) (exps : list Expression) (vals : list Value) (ex : Exception) (eff1 eff2 eff3 : SideEffectList) (eff : list SideEffectList) :
  length vals = i -> i < length exps ->
  length eff = i ->
  (forall j, j < i -> |env, nth j exps ErrorExp, concatn eff1 eff j| -e> |inl (nth j vals ErrorValue), concatn eff1 eff (S j)|) ->
  eff3 = concatn eff1 eff i ++ eff2 ->
  |env, nth i exps ErrorExp, concatn eff1 eff i| -e> |inr ex, eff3|
->
  |env, ETuple exps, eff1| -e> |inr ex, eff3|


(* try 2x *)
| eval_try (env: Environment) (e e1 e2 : Expression) (v vex1 vex2 vex3 : Var) (val : Value + Exception) (val' : Value) (eff1 eff2 eff3 eff4 : SideEffectList) :
  |env, e, eff1| -e> |inl val', eff1 ++ eff2| ->
  eff4 = eff1 ++ eff2 ++ eff3 ->
  |append_vars_to_env [v] [val'] env, e1, eff1 ++ eff2| -e> |val, eff4|
->
  |env, ETry e e1 e2 v vex1 vex2 vex3, eff1| -e> |val, eff4|

| eval_try_catch (env: Environment) (e e1 e2 : Expression) (v vex1 vex2 vex3 : Var) (val : Value + Exception) (ex : Exception) (eff1 eff2 eff3 eff4 : SideEffectList) :
  |env, e, eff1| -e> |inr ex, eff1 ++ eff2| ->
  eff4 = eff1 ++ eff2 ++ eff3 ->
  |append_vars_to_env [vex1; vex2; vex3] [make_value_from_ex_class (fst (fst ex)); snd (fst ex); snd ex] env, e2, eff1 ++ eff2| -e> |val, eff4|
->
  |env, ETry e e1 e2 v vex1 vex2 vex3, eff1| -e> |val, eff4|


(* case 1x *)
(** Pattern matching exception *)
| eval_case_ex_pat (env: Environment) (e : Expression) (ex : Exception) (patterns : list Pattern) (guards : list Expression) (bodies : list Expression)  (eff1 eff2 eff3 : SideEffectList):
  length patterns = length guards ->
  length patterns = length bodies ->
  eff3 = eff1 ++ eff2 ->
  |env, e, eff1| -e> |inr ex, eff3|
->
  |env, ECase e patterns guards bodies, eff1| -e> |inr ex, eff3|

(** ith guard exception -> guards cannot result in exception *)
(* | eval_case_ex_guard (env: Environment) (e e'' guard exp: Expression) (v : Value) (ex : Exception) (patterns : list Pattern) (guards : list Expression) (bodies : list Expression) (bindings: list (Var * Value)) (i : nat) (eff1 eff2 eff3 : SideEffectList):
  length patterns = length guards ->
  length patterns = length bodies ->
  eff3 = eff1 ++ eff2 ->
  |env, e, eff1| -e> |inl v, eff3| ->
  match_clause v patterns guards bodies i = Some (guard, exp, bindings) ->
  (forall j : nat, j < i -> 

    (forall gg ee bb, match_clause v patterns guards bodies j = Some (gg, ee, bb) -> ((|add_bindings bb env, gg, eff3| -e> |inl ffalse, eff3| )))

  ) ->
  |add_bindings bindings env, guard, eff3| -e> |inr ex, eff3|
->
  |env, ECase e patterns guards bodies, eff1| -e> |inr ex, eff3| *)


(* call 1x *)
| eval_call_ex (env: Environment) (i : nat) (fname : string) (params : list Expression) (vals : list Value) (ex : Exception) (eff1 eff2 eff3 : SideEffectList) (eff : list SideEffectList) :
  length vals = i -> i < length params ->
  length eff = i ->
  (forall j, j < i -> 
    |env, nth j params ErrorExp, concatn eff1 eff j| -e> |inl (nth j vals ErrorValue), concatn eff1 eff (S j)|
  ) ->
  eff3 = concatn eff1 eff i ++ eff2 ->
  |env, nth i params ErrorExp, concatn eff1 eff i| -e> |inr ex, eff3|

->
  |env, ECall fname params, eff1| -e> |inr ex, eff3|

(* apply 4x *)
(** According to ref. implementation, here it is not needed to check the arg number *)

(** if name evaluates to exception *)
| eval_apply_ex_closure_ex (params : list Expression) (env : Environment) (exp : Expression)  (ex : Exception) (eff1 eff2 eff3 : SideEffectList):
  eff3 = eff1 ++ eff2 ->
  |env, exp, eff1| -e> |inr ex, eff3|
->
  |env, EApply exp params, eff1| -e> |inr ex, eff3|

(** name and some parameters evaluate to values *)
| eval_apply_ex_params (params : list Expression) (vals : list Value) (env : Environment) (exp : Expression) (ex : Exception) (i : nat) (v : Value) (eff1 eff2 eff3 eff4 : SideEffectList) (eff : list SideEffectList) :
  i = length vals -> i < length params ->
  length eff = i
  ->
  |env, exp, eff1| -e> |inl v, eff1 ++ eff2| ->
  (forall j, j < i -> 
    |env, nth j params ErrorExp, concatn (eff1 ++ eff2) eff j| -e> |inl (nth j vals ErrorValue), concatn (eff1 ++ eff2) eff (S j)|
  ) ->
  eff4 = concatn (eff1 ++ eff2) eff i ++ eff3 ->
  |env, nth i params ErrorExp, concatn (eff1 ++ eff2) eff i| -e> |inr ex, eff4|
->
  |env, EApply exp params, eff1| -e> |inr ex, eff4|

(** Then we check if the name evaluates to a closure *)
| eval_apply_ex_closure (params : list Expression) (vals: list Value) (env : Environment) (v : Value) (exp : Expression) (eff1 eff2 eff3 : SideEffectList) (eff : list SideEffectList) :
  length params = length vals ->
  length eff = length params ->
  |env, exp, eff1| -e> |inl v, eff1 ++ eff2| ->
  (
    forall j : nat, j < length params ->
    (
      |env, nth j params ErrorExp, concatn (eff1 ++ eff2) eff j| -e> |inl (nth j vals ErrorValue), concatn (eff1 ++ eff2) eff (S j)|
    )
  ) ->
  (forall ref ext var_list body, v <> VClosure ref ext var_list body) ->
  eff3 = concatn (eff1 ++ eff2) eff (length params)
->
  |env, EApply exp params, eff1| -e> |inr (replace noclosure v), eff3|

(** too few or too many arguments are given *)
| eval_apply_ex_param_count (params : list Expression) (vals : list Value) (env : Environment) (exp : Expression) (body : Expression) (var_list : list Var) (ref : Environment) (ext : list (FunctionIdentifier * FunctionalExpression)) (eff1 eff2 eff3 : SideEffectList) (eff : list SideEffectList):
  length params = length vals ->
  length eff = length params ->
  |env, exp, eff1| -e> |inl (VClosure ref ext var_list body), eff1 ++ eff2| ->
  (
    forall j : nat, j < length params ->
    (
      |env, nth j params ErrorExp, concatn (eff1 ++ eff2) eff j| -e> |inl (nth j vals ErrorValue), concatn (eff1 ++ eff2) eff (S j)|
    )
  ) ->
  length var_list <> length vals ->
  eff3 = concatn (eff1 ++ eff2) eff (length params)
->
  |env, EApply exp params, eff1| -e> |inr (replace args (VClosure ref ext var_list body)), eff3|

(* let 1x *)
| eval_let_ex_param (env: Environment) (exps: list Expression) (vals : list Value) (vars: list Var) (e : Expression) (ex : Exception) (i : nat) (eff1 eff2 eff3 : SideEffectList) (eff : list SideEffectList) :
  length vals = i -> i < length exps ->
  length eff = i ->
  (forall j, j < i -> 
    |env, nth j exps ErrorExp, concatn eff1 eff j| -e> |inl (nth j vals ErrorValue), concatn eff1 eff (S j)|
  ) ->
  eff3 = concatn eff1 eff i ++ eff2 ->
  |env, nth i exps ErrorExp, concatn eff1 eff i| -e> |inr ex, eff3|
->
  |env, ELet vars exps e, eff1| -e> |inr ex, eff3|

(* map 2x *)
| eval_map_ex_key (kl vl: list Expression) (vvals kvals : list Value) (env: Environment) (i : nat) (ex : Exception) (eff1 eff2 eff3 : SideEffectList) (eff : list SideEffectList):
  length vl = length kl ->
  i = length vvals ->
  i = length kvals ->
  i < length vl ->
  length eff = i * 2 ->
  (
    forall j, j < i ->
    |env, nth j kl ErrorExp, concatn eff1 eff (2 * j)| -e> | inl (nth j kvals ErrorValue), concatn eff1 eff (S (2 * j))|
  )
  ->
  (
    forall j, j < i ->
    |env, nth j vl ErrorExp, concatn eff1 eff (S (2 * j))| -e> |inl (nth j vvals ErrorValue), concatn eff1 eff (S (S (2 * j)))|
  )
  ->
  eff3 = concatn eff1 eff (2 * i) ++ eff2 ->
  |env, nth i kl ErrorExp, concatn eff1 eff (2 * i)| -e> |inr ex, eff3|
->
  |env, EMap kl vl, eff1| -e> |inr ex, eff3|

| eval_map_ex_val (kl vl: list Expression) (vvals kvals : list Value) (env: Environment) (i : nat) (ex : Exception) (val : Value) (eff1 eff2 eff3 eff4 : SideEffectList) (eff : list SideEffectList) :
  length vl = length kl ->
  i = length vvals ->
  i = length kvals ->
  i < length vl ->
  length eff = i * 2 ->
  (
    forall j, j < i ->
    |env, nth j kl ErrorExp, concatn eff1 eff (2 * j)| -e> | inl (nth j kvals ErrorValue), concatn eff1 eff (S (2 * j))|
  ) ->
  (
    forall j, j < i ->
    |env, nth j vl ErrorExp, concatn eff1 eff (S (2 * j))| -e> |inl (nth j vvals ErrorValue), concatn eff1 eff (S (S (2 * j)))|
  )
  ->
  |env, nth i kl ErrorExp, concatn eff1 eff (2 * i)| -e> |inl val, concatn eff1 eff (2 * i) ++ eff2|
  ->
  eff4 = concatn eff1 eff (2 * i) ++ eff2 ++ eff3
  ->
  |env, nth i vl ErrorExp, concatn eff1 eff (2 * i) ++ eff2| -e> |inr ex, eff4|
->
  |env, EMap kl vl, eff1| -e> |inr ex, eff4|

where "| env , e , eff | -e> | e' , eff' |" := (eval_expr env e eff e' eff')
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