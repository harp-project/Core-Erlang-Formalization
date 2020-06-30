Load Core_Erlang_Side_Effects.

(** The Semantics of Core Erlang *)
Module Core_Erlang_Semantics.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.

Import Core_Erlang_Environment.
Import Core_Erlang_Helpers.
Import Core_Erlang_Syntax.
Import Core_Erlang_Side_Effects.

(* TODO: Always can be extended, this function simulates inter-module calls *)
Definition eval (fname : string) (params : list Value) (eff : SideEffectList) 
   : ((Value + Exception) * SideEffectList) :=
match fname, length params, params with
(** addition *)
| "plus"%string, 2, [VLiteral (Integer a); VLiteral (Integer b)] => 
     (inl (VLiteral (Integer (a + b))), eff)
(** faulty addition *)
| "plus"%string, 2, [a; b] => (inr (badarith (VList a b)), eff)
(** writing *)
| "fwrite"%string, _, _ => (inl ok, eff ++ [(Output, params)])
(** reading *)
| "fread"%string, 2, e => (inl (VTuple [ok; nth 1 params ErrorValue]), eff ++ [(Input, params)])

(** and operator *)
| "and"%string, 2, [VLiteral (Atom a); VLiteral (Atom b)] => 
   match a, b with
   | "true"%string, "true"%string => (inl ttrue, eff)
   | "false"%string, "true"%string => (inl ffalse, eff)
   | "true"%string, "false"%string => (inl ffalse, eff)
   | "false"%string, "false"%string => (inl ffalse, eff)
   | _, _ => (inr (badarg (VList (VLiteral (Atom a)) (VLiteral (Atom b)))), eff)
   end
(** anything else *)
| _, _, _ => (inr (undef (VLiteral (Atom fname))), eff)
end.

Reserved Notation "| env , id , e , eff | -e> | id' , e' , eff' |" (at level 70).
Inductive eval_expr : Environment -> nat -> Expression -> SideEffectList -> nat ->
    (Value + Exception) -> SideEffectList -> Prop :=
| eval_emptylist (env : Environment) (eff : SideEffectList) (id : nat):
  |env, id, EEmptyList, eff| -e> |id, inl VEmptyList, eff|

(* literal evaluation rule *)
| eval_lit (env : Environment) (l : Literal) (eff : SideEffectList) (id : nat):
  |env, id, ELiteral l, eff| -e> |id, inl (VLiteral l), eff|

(* variable evaluation rule *)
| eval_var (env:Environment) (s: Var) (eff : SideEffectList) (id : nat) :
  |env, id, EVar s, eff| -e> |id, get_value env (inl s), eff|

(* Function identifier evaluation rule *)
| eval_funid (env:Environment) (fid : FunctionIdentifier) (eff : SideEffectList) (id : nat):
  |env, id, EFunId fid, eff| -e> |id, get_value env (inr fid), eff|

(* Function evaluation *)
| eval_fun (env : Environment) (vl : list Var) (e : Expression) (eff : SideEffectList) (id : nat):
  |env, id, EFun vl e, eff| -e> |S id, inl (VClosure env [] id vl e), eff|

(* tuple evaluation rule *)
| eval_tuple (env: Environment) (exps : list Expression) (vals : list Value) 
     (eff1 eff2 : SideEffectList) (eff : list SideEffectList) (ids : list nat) (id id' : nat) :
  length exps = length vals ->
  length exps = length eff ->
  length exps = length ids ->
  (
    forall i, i < length exps ->
      |env, nth_id ids id i, nth i exps ErrorExp, concatn eff1 eff i| 
     -e> 
      |nth_id ids id (S i), inl (nth i vals ErrorValue), concatn eff1 eff (S i)|
  ) ->
  eff2 = concatn eff1 eff (length vals) ->
  id' = last ids id (* if length = 0, then last id = first id *)
->
  |env, id, ETuple exps, eff1| -e> |id' , inl (VTuple vals), eff2|

(* list evaluation rule *)
| eval_list (env:Environment) (hd tl: Expression) (hdv tlv : Value) 
     (eff1 eff2 eff3 eff4 : SideEffectList) (id id' id'' : nat) :
  eff4 = eff1 ++ eff2 ++ eff3 ->
  |env, id, tl, eff1| -e> |id', inl tlv, eff1 ++ eff2| ->
  |env, id', hd, eff1 ++ eff2| -e> | id'', inl hdv, eff4|
->
  |env, id, EList hd tl, eff1| -e> |id'', inl (VList hdv tlv), eff4|

(* case evaluation rules *)
| eval_case (env: Environment) (e guard exp: Expression) (v : Value) (v' : Value + Exception) 
     (patts : list Pattern) (guards : list Expression) (bodies : list Expression) 
     (bindings: list (Var * Value)) (i : nat) (eff1 eff2 eff3 eff4 : SideEffectList) 
     (id id' id'' : nat) :
  length patts = length guards ->
  length patts = length bodies ->
  |env, id, e, eff1| -e> |id', inl v, eff1 ++ eff2| ->
  i < length patts ->
  match_clause v patts guards bodies i = Some (guard, exp, bindings) ->
  (forall j : nat, j < i -> 

    (** THESE GUARDS MUST BE SIDE-EFFECT FREE ACCORDING TO 1.0.3 LANGUAGE SPECIFICATION *)
    (** These guards cannot define functions currently (id' does not change) *)
    (forall gg ee bb, match_clause v patts guards bodies j = Some (gg, ee, bb) -> 
      ((|add_bindings bb env, id', gg, eff1 ++ eff2| -e> |id', inl ffalse, eff1 ++ eff2| ))
    )

  ) ->
  eff4 = eff1 ++ eff2 ++ eff3 ->
  |add_bindings bindings env, id', guard, eff1 ++ eff2| -e> |id', inl ttrue, eff1 ++ eff2| -> 
  |add_bindings bindings env, id', exp, eff1 ++ eff2| -e> |id'', v', eff1 ++ eff2 ++ eff3|
->
  |env, id, ECase e patts guards bodies, eff1| -e> | id'', v', eff4|


(* call evaluation rule *)
| eval_call (env: Environment) (v : Value + Exception) (params : list Expression) 
     (vals : list Value) (fname: string) (eff1 eff2: SideEffectList) (eff : list SideEffectList) 
     (ids : list nat) (id id' : nat) :
  length params = length vals ->
  length params = length eff ->
  length params = length ids ->
  (
    forall i, i < length params ->
      |env, nth_id ids id i, nth i params ErrorExp, concatn eff1 eff i| 
     -e>
      |nth_id ids id (S i), inl (nth i vals ErrorValue), concatn eff1 eff (S i)|
  ) ->
  eval fname vals (concatn eff1 eff (length params)) = (v, eff2) ->
  id' = last ids id
->
  |env, id, ECall fname params, eff1| -e> |id', v, eff2|

(* apply functions*)
| eval_apply (params : list Expression) (vals : list Value) (env : Environment) 
     (exp : Expression) (body : Expression) (v : Value + Exception) (var_list : list Var) 
     (ref : Environment) (ext : list (nat * FunctionIdentifier * FunctionExpression)) 
     (eff1 eff2 eff3 eff4 : SideEffectList) (eff : list SideEffectList) (n : nat) 
     (ids : list nat) (id id' id'' : nat) :
  length params = length vals ->
  |env, id, exp, eff1| -e> |id', inl (VClosure ref ext n var_list body), eff1 ++ eff2| ->
  length var_list = length vals
  ->
  length params = length eff ->
  length params = length ids ->
  (
    forall i, i < length params ->
      |env, nth_id ids id' i, nth i params ErrorExp, concatn (eff1 ++ eff2) eff i|
     -e>
      |nth_id ids id' (S i), inl (nth i vals ErrorValue), concatn (eff1 ++ eff2) eff (S i)|
  )
  ->
  eff4 = concatn (eff1 ++ eff2) eff (length params) ++ eff3
  ->
  |append_vars_to_env var_list vals (get_env ref ext), 
   last ids id',
   body, 
   concatn (eff1 ++ eff2) eff (length params)|
  -e>
   |id'', v, eff4|
->
  |env, id, EApply exp params, eff1| -e> |id'', v, eff4|

(* let evaluation rule *)
| eval_let (env: Environment) (exps: list Expression) (vals : list Value) (vars: list Var) 
     (e : Expression) (v : Value + Exception) (eff : list SideEffectList) 
     (eff1 eff2 eff3 : SideEffectList) (ids : list nat) (id id' : nat) :
  length exps = length vals ->
  length exps = length eff ->
  length exps = length ids ->
  (
    forall i, i < length exps ->
      |env, nth_id ids id i, nth i exps ErrorExp, concatn eff1 eff i|
     -e>
      |nth_id ids id (S i), inl (nth i vals ErrorValue), concatn eff1 eff (S i)|
  )
  ->
    eff3 = concatn eff1 eff (length exps) ++ eff2
  ->
    |append_vars_to_env vars vals env, last ids id, e, concatn eff1 eff (length exps)| 
    -e> 
    |id', v, eff3|
->
  |env, id, ELet vars exps e, eff1| -e> |id', v, eff3|

(* Letrec evaluation rule *)
| eval_letrec (env: Environment) (e : Expression)  (fids : list FunctionIdentifier) 
     (paramss: list (list Var)) (bodies : list Expression) (v : Value + Exception) 
     (eff1 eff2 eff3 : SideEffectList) (id id' : nat) :
  length fids = length paramss ->
  length fids = length bodies ->
  (
      |append_funs_to_env fids paramss bodies env id,
       id + length fids,
       e,
       eff1|
     -e>
      |id', v, eff1 ++ eff2|
  ) ->
  eff3 = eff1 ++ eff2
->
  |env, id, ELetrec fids paramss bodies e, eff1| -e> |id', v, eff3|


(* map evaluation rule *)
| eval_map (kl vl: list Expression) (vvals kvals kl' vl' : list Value) (env: Environment) 
     (eff1 eff2 : SideEffectList) (eff : list SideEffectList) (id id' : nat) (ids : list nat) :
  length kl = length vl ->
  length kl = length vvals ->
  length kl = length kvals ->
  (length kl) * 2 = length eff ->
  (length kl) * 2 = length ids ->
  make_value_map kvals vvals = (kl', vl') ->
  (
    forall i : nat, i < length vl ->
    |env, nth_id ids id (2 * i), nth i kl ErrorExp, concatn eff1 eff  (2 * i)|
   -e>
    |nth_id ids id (S (2 * i)), inl (nth i kvals ErrorValue), concatn eff1 eff (S (2*i))|
  ) ->
  (
    forall i : nat, i < length vl ->
    |env, nth_id ids id (S (2 * i)),nth i vl ErrorExp, concatn eff1 eff (S (2* i))|
   -e>
    |nth_id ids id (S (S (2 * i))),inl (nth i vvals ErrorValue), concatn eff1 eff (S (S (2*i)))|
  ) ->
  eff2 = concatn eff1 eff ((length kvals) * 2) ->
  id' = last ids id
->
  |env, id, EMap kl vl, eff1| -e> |id', inl (VMap kl' vl'), eff2|


  (* EXCEPTIONS *)
(* list tail exception *)
| eval_list_ex_tl (env: Environment) (hd tl : Expression) (ex : Exception) 
      (eff1 eff2 eff3 : SideEffectList) (id id' : nat) :
  eff3 = eff1 ++ eff2 ->
  |env, id, tl, eff1| -e> |id', inr ex, eff1 ++ eff2|
->
  |env, id, EList hd tl, eff1| -e> |id', inr ex, eff3|

(* list head exception *)
| eval_list_ex_hd (env: Environment) (hd tl : Expression) (ex : Exception) (vtl : Value) 
     (eff1 eff2 eff3 eff4 : SideEffectList) (id id' id'' : nat) :
  eff4 = eff1 ++ eff2 ++ eff3 ->
  |env, id, tl, eff1| -e> |id', inl vtl, eff1 ++ eff2| -> 
  |env, id', hd, eff1 ++ eff2| -e> |id'', inr ex, eff4|
->
  |env, id, EList hd tl, eff1| -e> |id'', inr ex, eff4|

(* tuple exception *)
| eval_tuple_ex (env: Environment) (i : nat) (exps : list Expression) (vals : list Value) 
     (ex : Exception) (eff1 eff2 eff3 : SideEffectList) (eff : list SideEffectList) 
     (id id' : nat) (ids : list nat) :
  length vals = i ->
  i < length exps ->
  length eff = i ->
  length ids = i ->
  (forall j, j < i ->
    |env, nth_id ids id j, nth j exps ErrorExp, concatn eff1 eff j|
   -e>
    |nth_id ids id (S j), inl (nth j vals ErrorValue), concatn eff1 eff (S j)|) ->
  eff3 = concatn eff1 eff i ++ eff2 ->
  |env, last ids id, nth i exps ErrorExp, concatn eff1 eff i| -e> |id', inr ex, eff3|
->
  |env, id, ETuple exps, eff1| -e> |id', inr ex, eff3|


(* try 2x *)
| eval_try (env: Environment) (e e1 e2 : Expression) (v vex1 vex2 vex3 : Var) 
      (val : Value + Exception) (val' : Value) (eff1 eff2 eff3 eff4 : SideEffectList)
      (id id' id'' : nat) :
  |env, id, e, eff1| -e> |id', inl val', eff1 ++ eff2| ->
  eff4 = eff1 ++ eff2 ++ eff3 ->
  |append_vars_to_env [v] [val'] env, id', e1, eff1 ++ eff2| -e> |id'', val, eff4|
->
  |env, id, ETry e e1 e2 v vex1 vex2 vex3, eff1| -e> |id'', val, eff4|

| eval_try_catch (env: Environment) (e e1 e2 : Expression) (v vex1 vex2 vex3 : Var) 
      (val : Value + Exception) (ex : Exception) (eff1 eff2 eff3 eff4 : SideEffectList) 
      (id id' id'' : nat) :
  |env, id, e, eff1| -e> |id', inr ex, eff1 ++ eff2| ->
  eff4 = eff1 ++ eff2 ++ eff3 ->
  |append_vars_to_env [vex1; vex2; vex3] 
                       [exclass_to_value (fst (fst ex)); snd (fst ex); snd ex] 
                       env, id', e2, eff1 ++ eff2|
 -e> 
  |id'', val, eff4|
->
  |env, id, ETry e e1 e2 v vex1 vex2 vex3, eff1| -e> |id'', val, eff4|


(* case 2x *)
(** Pattern matching exception *)
| eval_case_ex_pat (env: Environment) (e : Expression) (ex : Exception) (patterns : list Pattern) 
     (guards : list Expression) (bodies : list Expression)  (eff1 eff2 eff3 : SideEffectList) 
     (id id' : nat):
  length patterns = length guards ->
  length patterns = length bodies ->
  eff3 = eff1 ++ eff2 ->
  |env, id, e, eff1| -e> |id', inr ex, eff3|
->
  |env, id, ECase e patterns guards bodies, eff1| -e> |id', inr ex, eff3|

(** No matching clause *)
| eval_case_clause_ex (env: Environment) (e : Expression) (patterns : list Pattern) 
     (guards : list Expression) (bodies : list Expression) (v : Value) 
     (eff1 eff2 eff3 : SideEffectList) (id id' : nat):
  length patterns = length guards ->
  length patterns = length bodies ->
  eff3 = eff1 ++ eff2 ->
  |env, id, e, eff1| -e> |id', inl v, eff3| ->
  (forall j : nat, j < length patterns -> 

    (** THESE GUARDS MUST BE SIDE-EFFECT FREE ACCORDING TO 1.0.3 LANGUAGE SPECIFICATION *)
    (** These guards cannot define functions currently (id' does not change) *)
    (forall gg ee bb, match_clause v patterns guards bodies j = Some (gg, ee, bb) -> 
      ((|add_bindings bb env, id', gg, eff1 ++ eff2| -e> |id', inl ffalse, eff3| ))
    )

  )
->
|env, id, ECase e patterns guards bodies, eff1| -e> |id', inr (if_clause v), eff3|
(** ith guard exception -> guards cannot result in exception, i.e. this rule is not needed *)

(* call 1x *)
| eval_call_ex (env: Environment) (i : nat) (fname : string) (params : list Expression) 
     (vals : list Value) (ex : Exception) (eff1 eff2 eff3 : SideEffectList) 
     (eff : list SideEffectList) (id id' : nat) (ids : list nat) :
  length vals = i ->
  i < length params ->
  length eff = i ->
  length ids = i ->
  (forall j, j < i ->
    |env, nth_id ids id j, nth j params ErrorExp, concatn eff1 eff j|
   -e>
    |nth_id ids id (S j), inl (nth j vals ErrorValue), concatn eff1 eff (S j)|
  ) ->
  eff3 = concatn eff1 eff i ++ eff2 ->
  |env, last ids id, nth i params ErrorExp, concatn eff1 eff i| -e> |id', inr ex, eff3|

->
  |env, id, ECall fname params, eff1| -e> |id', inr ex, eff3|

(* apply 4x *)
(** According to ref. implementation, here it is not needed to check the arg number *)

(** if name expression evaluates to exception *)
| eval_apply_ex_closure_ex (params : list Expression) (env : Environment) (exp : Expression)  
     (ex : Exception) (eff1 eff2 eff3 : SideEffectList) (id id' : nat):
  eff3 = eff1 ++ eff2 ->
  |env, id, exp, eff1| -e> |id', inr ex, eff3|
->
  |env, id, EApply exp params, eff1| -e> |id', inr ex, eff3|

(** name expression and some parameters evaluate to values *)
| eval_apply_ex_params (params : list Expression) (vals : list Value) (env : Environment) 
     (exp : Expression) (ex : Exception) (i : nat) (v : Value) (eff1 eff2 eff3 eff4 : SideEffectList) 
     (eff : list SideEffectList) (ids : list nat) (id id' id'' : nat) :
  i = length vals ->
  i < length params ->
  length eff = i ->
  length ids = i
  ->
  |env, id, exp, eff1| -e> |id', inl v, eff1 ++ eff2| ->
  (forall j, j < i -> 
    |env, nth_id ids id' j, nth j params ErrorExp, concatn (eff1 ++ eff2) eff j|
   -e>
    |nth_id ids id' (S j), inl (nth j vals ErrorValue), concatn (eff1 ++ eff2) eff (S j)|
  ) ->
  eff4 = concatn (eff1 ++ eff2) eff i ++ eff3 ->
  |env, last ids id', nth i params ErrorExp, concatn (eff1 ++ eff2) eff i| -e> |id'', inr ex, eff4|
->
  |env, id, EApply exp params, eff1| -e> |id'', inr ex, eff4|

(** Then we check if the name expression evaluates to a closure *)
| eval_apply_ex_closure (params : list Expression) (vals: list Value) (env : Environment) (v : Value) 
     (exp : Expression) (eff1 eff2 eff3 : SideEffectList) (eff : list SideEffectList) 
     (ids : list nat) (id id' id'' : nat):
  length params = length vals ->
  length params = length eff ->
  length params = length ids ->
  |env, id, exp, eff1| -e> |id', inl v, eff1 ++ eff2| ->
  (
    forall j : nat, j < length params ->
    (
      |env, nth_id ids id' j, nth j params ErrorExp, concatn (eff1 ++ eff2) eff j|
     -e>
      |nth_id ids id' (S j), inl (nth j vals ErrorValue), concatn (eff1 ++ eff2) eff (S j)|
    )
  ) ->
  (forall ref ext var_list body n, 
     v <> VClosure ref ext n var_list body) ->
  eff3 = concatn (eff1 ++ eff2) eff (length params) ->
  id'' = last ids id'
->
  |env, id, EApply exp params, eff1| -e> |id'', inr (badfun v), eff3|

(** too few or too many arguments are given *)
| eval_apply_ex_param_count (params : list Expression) (vals : list Value) (env : Environment) 
     (exp : Expression) (body : Expression) (var_list : list Var) (ref : Environment) 
     (ext : list (nat * FunctionIdentifier * FunctionExpression)) (eff1 eff2 eff3 : SideEffectList) 
     (eff : list SideEffectList) (n : nat) (ids : list nat) (id id' id'' : nat):
  length params = length vals ->
  length params = length eff ->
  length params = length ids ->
  |env, id, exp, eff1| -e> |id', inl (VClosure ref ext n var_list body), eff1 ++ eff2| ->
  (
    forall j : nat, j < length params ->
    (
      |env, nth_id ids id' j, nth j params ErrorExp, concatn (eff1 ++ eff2) eff j|
     -e>
      |nth_id ids id' (S j), inl (nth j vals ErrorValue), concatn (eff1 ++ eff2) eff (S j)|
    )
  ) ->
  length var_list <> length vals ->
  eff3 = concatn (eff1 ++ eff2) eff (length params) ->
  id'' = last ids id'
->
  |env, id, EApply exp params, eff1| 
  -e> 
  |id'', inr (badarity (VClosure ref ext n var_list body)), eff3|

(* let 1x *)
| eval_let_ex_param (env: Environment) (exps: list Expression) (vals : list Value) (vars: list Var) 
      (e : Expression) (ex : Exception) (i : nat) (eff1 eff2 eff3 : SideEffectList) 
      (eff : list SideEffectList) (id id' : nat) (ids : list nat) :
  length vals = i ->
  i < length exps ->
  length eff = i ->
  length ids = i ->
  (forall j, j < i -> 
    |env, nth_id ids id j, nth j exps ErrorExp, concatn eff1 eff j|
   -e>
    |nth_id ids id (S j), inl (nth j vals ErrorValue), concatn eff1 eff (S j)|
  ) ->
  eff3 = concatn eff1 eff i ++ eff2 ->
  |env, last ids id, nth i exps ErrorExp, concatn eff1 eff i| -e> |id', inr ex, eff3|
->
  |env, id, ELet vars exps e, eff1| -e> |id', inr ex, eff3|

(* map 2x *)
(** Exception in key list *)
| eval_map_ex_key (kl vl: list Expression) (vvals kvals : list Value) (env: Environment) (i : nat) 
     (ex : Exception) (eff1 eff2 eff3 : SideEffectList) (eff : list SideEffectList) 
     (ids : list nat) (id id' : nat):
  length kl = length vl ->
  length vvals = i ->
  length kvals = i ->
  i < length kl ->
  length eff = i * 2 ->
  length ids = i * 2 ->
  (
    forall j, j < i ->
    |env, nth_id ids id (2*j), nth j kl ErrorExp, concatn eff1 eff (2 * j)|
   -e>
    |nth_id ids id (S(2*j)), inl (nth j kvals ErrorValue), concatn eff1 eff (S (2 * j))|
  )
  ->
  (
    forall j, j < i ->
    |env, nth_id ids id (S (2*j)), nth j vl ErrorExp, concatn eff1 eff (S (2 * j))|
   -e>
    |nth_id ids id (S (S (2*j))), inl (nth j vvals ErrorValue), concatn eff1 eff (S (S (2 * j)))|
  )
  ->
  eff3 = concatn eff1 eff (2 * i) ++ eff2 ->
  |env, last ids id, nth i kl ErrorExp, concatn eff1 eff (2 * i)| -e> |id', inr ex, eff3|
->
  |env, id, EMap kl vl, eff1| -e> |id', inr ex, eff3|

(** Exception in value list *)
| eval_map_ex_val (kl vl: list Expression) (vvals kvals : list Value) (env: Environment) (i : nat) 
     (ex : Exception) (val : Value) (eff1 eff2 eff3 eff4 : SideEffectList) 
     (eff : list SideEffectList) (ids : list nat) (id id' id'' : nat):
  length kl = length vl ->
  length vvals = i ->
  length kvals = i ->
  i < length kl ->
  length eff = i * 2 ->
  length ids = 2 * i ->
  (
    forall j, j < i ->
    |env, nth_id ids id (2*j), nth j kl ErrorExp, concatn eff1 eff (2 * j)|
   -e>
    | nth_id ids id (S (2*j)), inl (nth j kvals ErrorValue), concatn eff1 eff (S (2 * j))|
  ) ->
  (
    forall j, j < i ->
    |env, nth_id ids id (S (2*j)), nth j vl ErrorExp, concatn eff1 eff (S (2 * j))|
   -e>
    |nth_id ids id (S (S (2*j))), inl (nth j vvals ErrorValue), concatn eff1 eff (S (S (2 * j)))|
  )
 ->
  |env, last ids id, nth i kl ErrorExp, concatn eff1 eff (2 * i)| 
  -e> 
  |id', inl val, concatn eff1 eff (2 * i) ++ eff2|
 ->
  eff4 = concatn eff1 eff (2 * i) ++ eff2 ++ eff3
 ->
  |env, id', nth i vl ErrorExp, concatn eff1 eff (2 * i) ++ eff2| -e> |id'', inr ex, eff4|
->
  |env, id, EMap kl vl, eff1| -e> |id'', inr ex, eff4|

where "| env , id , e , eff | -e> | id' , e' , eff' |" := (eval_expr env id e eff id' e' eff')
.


(* These are the initialization function before evaluating a module *)
(* Fixpoint add_elements_to_env (fl : list ErlFunction) : Environment :=
match fl with
| [] => []
| (TopLevelFun sig (vl,exp))::xs => insert_value_no_overwrite 
                                    (add_elements_to_env xs) (inr sig) (VClosure (inr sig) vl exp)
end.

Fixpoint initialize_proving (module : ErlModule) : Environment :=
match module with
| ErlMod s fl => add_elements_to_env fl
end.

Fixpoint add_elements_to_closure (fl : list ErlFunction) (module : ErlModule) : Closures :=
match fl with
| [] => []
| (TopLevelFun sig f)::xs => set_closure_no_overwrite (add_elements_to_closure xs module) sig 
                            (initialize_proving module)
end.

Fixpoint initialize_proving_closures (module : ErlModule) : Closures :=
match module with
| ErlMod s fl => add_elements_to_closure fl module
end. *)

End Core_Erlang_Semantics.