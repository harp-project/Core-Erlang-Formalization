Require Core_Erlang_Side_Effects.

(** The Semantics of Core Erlang *)
Module Semantics.

Export Core_Erlang_Side_Effects.Side_Effects.
Export Core_Erlang_Environment.Environment.

Import ListNotations.

(* TODO: Always can be extended, this function simulates inter-module calls *)
Definition eval (fname : string) (params : list Value) (eff : SideEffectList) 
   : ((Value + Exception) * SideEffectList) :=
match fname, length params, params with
(** addition *)
| "plus"%string, 2, [VLit (Integer a); VLit (Integer b)] => 
     (inl (VLit (Integer (a + b))), eff)
(** faulty addition *)
| "plus"%string, 2, [a; b] => (inr (badarith (VCons a b)), eff)
(** writing *)
| "fwrite"%string, _, _ => (inl ok, eff ++ [(Output, params)])
(** reading *)
| "fread"%string, 2, e => (inl (VTuple [ok; nth 1 params ErrorValue]), eff ++ [(Input, params)])

(** and operator *)
| "and"%string, 2, [VLit (Atom a); VLit (Atom b)] => 
   match a, b with
   | "true"%string, "true"%string => (inl ttrue, eff)
   | "false"%string, "true"%string => (inl ffalse, eff)
   | "true"%string, "false"%string => (inl ffalse, eff)
   | "false"%string, "false"%string => (inl ffalse, eff)
   | _, _ => (inr (badarg (VCons (VLit (Atom a)) (VLit (Atom b)))), eff)
   end
(** anything else *)
| _, _, _ => (inr (undef (VLit (Atom fname))), eff)
end.

Reserved Notation "| env , id , e , eff | -e> | id' , e' , eff' |" (at level 70).
Inductive eval_expr : Environment -> nat -> Expression -> SideEffectList -> nat ->
    (Value + Exception) -> SideEffectList -> Prop :=
| eval_nil (env : Environment) (eff : SideEffectList) (id : nat):
  |env, id, ENil, eff| -e> |id, inl VNil, eff|

(* literal evaluation rule *)
| eval_lit (env : Environment) (l : Literal) (eff : SideEffectList) (id : nat):
  |env, id, ELit l, eff| -e> |id, inl (VLit l), eff|

(* variable evaluation rule *)
| eval_var (env:Environment) (s: Var) (eff : SideEffectList) (id : nat) (res : Value + Exception) :
  res = get_value env (inl s)
->
  |env, id, EVar s, eff| -e> |id, res, eff|

(* Function Identifier evaluation rule *)
| eval_funid (env:Environment) (fid : FunctionIdentifier) (eff : SideEffectList) 
    (res : Value + Exception) (id : nat):
  res = get_value env (inr fid)
->
  |env, id, EFunId fid, eff| -e> |id, res, eff|

(* Function evaluation *)
| eval_fun (env : Environment) (vl : list Var) (e : Expression) (eff : SideEffectList) (id : nat):
  |env, id, EFun vl e, eff| -e> |S id, inl (VClos env [] id vl e), eff|

(* tuple evaluation rule *)
| eval_tuple (env: Environment) (exps : list Expression) (vals : list Value) 
     (eff1 eff2 : SideEffectList) (eff : list SideEffectList) (ids : list nat) (id id' : nat) :
  length exps = length vals ->
  length exps = length eff ->
  length exps = length ids ->
  (
    forall i, i < length exps ->
      |env, nth_def ids id i, nth i exps ErrorExp, nth_def eff eff1 i| 
     -e> 
      |nth_def ids id (S i), inl (nth i vals ErrorValue), nth_def eff eff1 (S i)|
  ) ->
  eff2 = last eff eff1 ->
  id' = last ids id (* if length = 0, then last id = first id *)
->
  |env, id, ETuple exps, eff1| -e> |id' , inl (VTuple vals), eff2|

(* list evaluation rule *)
| eval_cons (env:Environment) (hd tl: Expression) (hdv tlv : Value) 
     (eff1 eff2 eff3 : SideEffectList) (id id' id'' : nat) :
  |env, id, tl, eff1| -e> |id', inl tlv, eff2| ->
  |env, id', hd, eff2| -e> | id'', inl hdv, eff3|
->
  |env, id, ECons hd tl, eff1| -e> |id'', inl (VCons hdv tlv), eff3|

(* case evaluation rules *)
| eval_case (env: Environment) (e guard exp: Expression) (v : Value) (v' : Value + Exception) (l : list (Pattern * Expression * Expression)) (bindings: list (Var * Value)) (i : nat) (eff1 eff2 eff3 : SideEffectList) (id id' id'' : nat) :
  |env, id, e, eff1| -e> |id', inl v, eff2| ->
  i < length l ->
  match_clause v l i = Some (guard, exp, bindings) ->
  (forall j : nat, j < i -> 

    (** THESE GUARDS MUST BE SIDE-EFFECT FREE ACCORDING TO 1.0.3 LANGUAGE SPECIFICATION *)
    (forall gg ee bb, match_clause v l j = Some (gg, ee, bb) -> 
      (|add_bindings bb env, id', gg, eff2| -e> |id', inl ffalse, eff2| ))

  ) ->
  |add_bindings bindings env, id', guard, eff2| -e> |id', inl ttrue, eff2| -> 
  |add_bindings bindings env, id', exp, eff2| -e> |id'', v', eff3|
->
  |env, id, ECase e l, eff1| -e> |id'', v', eff3|


(* call evaluation rule *)
| eval_call (env: Environment) (v : Value + Exception) (params : list Expression) 
     (vals : list Value) (fname: string) (eff1 eff2: SideEffectList) (eff : list SideEffectList) 
     (ids : list nat) (id id' : nat) :
  length params = length vals ->
  length params = length eff ->
  length params = length ids ->
  (
    forall i, i < length params ->
      |env, nth_def ids id i, nth i params ErrorExp, nth_def eff eff1 i| 
     -e>
      |nth_def ids id (S i), inl (nth i vals ErrorValue), nth_def eff eff1 (S i)|
  ) ->
  eval fname vals (last eff eff1) = (v, eff2) ->
  id' = last ids id
->
  |env, id, ECall fname params, eff1| -e> |id', v, eff2|

(* apply functions*)
| eval_app (params : list Expression) (vals : list Value) (env : Environment) 
     (exp : Expression) (body : Expression) (v : Value + Exception) (var_list : list Var) 
     (ref : Environment) (ext : list (nat * FunctionIdentifier * FunctionExpression)) (n : nat)
     (eff1 eff2 eff3 : SideEffectList) (eff : list SideEffectList) (ids : list nat) (id id' id'' : nat) :
  length params = length vals ->
  |env, id, exp, eff1| -e> |id', inl (VClos ref ext n var_list body), eff2| ->
  length var_list = length vals
  ->
  length params = length eff ->
  length params = length ids ->
  (
    forall i, i < length params ->
      |env, nth_def ids id' i, nth i params ErrorExp, nth_def eff eff2 i|
     -e>
      |nth_def ids id' (S i), inl (nth i vals ErrorValue), nth_def eff eff2 (S i)|
  )
  ->
  |append_vars_to_env var_list vals (get_env ref ext), 
   last ids id',
   body, 
   last eff eff2|
  -e>
   |id'', v, eff3|
->
  |env, id, EApp exp params, eff1| -e> |id'', v, eff3|

(* let evaluation rule *)
| eval_let (env: Environment) (l: list (Var * Expression)) (vals : list Value) (e : Expression) (v : Value + Exception) (eff : list SideEffectList) (eff1 eff2 : SideEffectList) (id id' : nat) (ids : list nat):
  length l = length vals ->
  length l = length eff ->
  length l = length ids ->
  (
    forall i, i < length l ->
      |env, nth_def ids id i, nth i (snd (split l)) ErrorExp, nth_def eff eff1 i| 
       -e> 
      | nth_def ids id (S i), inl (nth i vals ErrorValue), nth_def eff eff1 (S i)|
  )
  ->
    |append_vars_to_env (fst (split l)) vals env, last ids id, e, last eff eff1|
     -e>
    |id', v, eff2|
->
  |env, id, ELet l e, eff1| -e> |id', v, eff2|

(* Letrec evaluation rule *)
| eval_letrec (env: Environment) (e : Expression)  (l : list (FunctionIdentifier * ((list Var) * Expression))) (v : Value + Exception) (eff1 eff2 : SideEffectList) (id id' : nat) :
  (
     |append_funs_to_env l env id, id + length l, e, eff1| -e> | id', v, eff2|
  )
->
  |env, id, ELetRec l e, eff1| -e> | id', v, eff2|



(* map evaluation rule *)
| eval_map (l: list (Expression * Expression)) (vvals kvals kvals' vvals' : list Value) ( lv : list (Value * Value)) (env: Environment) (eff1 eff2 : SideEffectList) (eff : list SideEffectList) (ids : list nat) (id id' : nat) :
  length l = length vvals ->
  length l = length kvals ->
  (length l) * 2 = length eff ->
  (length l) * 2 = length ids ->
  (
    forall i : nat, i < length l ->
    |env, nth_def ids id (2 * i), nth i (fst (split l)) ErrorExp, nth_def eff eff1 (2 * i)| 
     -e>
    | nth_def ids id (S (2 * i)), inl (nth i kvals ErrorValue), nth_def eff eff1 (S (2*i))|
  ) ->
  (
    forall i : nat, i < length l ->
    |env, nth_def ids id (S (2 * i)), nth i (snd (split l)) ErrorExp, nth_def eff eff1 (S (2* i))|
     -e>
    |nth_def ids id (S (S (2 * i))), inl (nth i vvals ErrorValue), nth_def eff eff1 (S (S (2*i)))|

  ) ->
  make_value_map kvals vvals = (kvals', vvals') ->
  combine kvals' vvals' = lv ->
  length lv <= length l ->
  eff2 = last eff eff1 ->
  id' = last ids id
->
  |env, id, EMap l, eff1| -e> |id', inl (VMap lv), eff2|

(*
  (* EXCEPTIONS *)
(* list tail exception *)
| eval_cons_ex_tl (env: Environment) (hd tl : Expression) (ex : Exception) 
      (eff1 eff2 eff3 : SideEffectList) (id id' : nat) :
  eff3 = eff1 ++ eff2 ->
  |env, id, tl, eff1| -e> |id', inr ex, eff1 ++ eff2|
->
  |env, id, ECons hd tl, eff1| -e> |id', inr ex, eff3|

(* list head exception *)
| eval_cons_ex_hd (env: Environment) (hd tl : Expression) (ex : Exception) (vtl : Value) 
     (eff1 eff2 eff3 eff4 : SideEffectList) (id id' id'' : nat) :
  eff4 = eff1 ++ eff2 ++ eff3 ->
  |env, id, tl, eff1| -e> |id', inl vtl, eff1 ++ eff2| -> 
  |env, id', hd, eff1 ++ eff2| -e> |id'', inr ex, eff4|
->
  |env, id, ECons hd tl, eff1| -e> |id'', inr ex, eff4|

(* tuple exception *)
| eval_tuple_ex (env: Environment) (i : nat) (exps : list Expression) (vals : list Value) 
     (ex : Exception) (eff1 eff2 eff3 : SideEffectList) (eff : list SideEffectList) 
     (id id' : nat) (ids : list nat) :
  length vals = i ->
  i < length exps ->
  length eff = i ->
  length ids = i ->
  (forall j, j < i ->
    |env, nth_def ids id j, nth j exps ErrorExp, concatn eff1 eff j|
   -e>
    |nth_def ids id (S j), inl (nth j vals ErrorValue), concatn eff1 eff (S j)|) ->
  eff3 = nth_def eff eff1 i ++ eff2 ->
  |env, last ids id, nth i exps ErrorExp, nth_def eff eff1 i| -e> |id', inr ex, eff3|
->
  |env, id, ETuple exps, eff1| -e> |id', inr ex, eff3|


(* try 2x *)
| eval_try (env: Environment) (l : list (Expression * Var)) (e1 e2 : Expression) (vex1 vex2 vex3 : Var) (val : Value + Exception) (eff : list SideEffectList)
      (vals : list Value) (eff1 eff2 eff3 : SideEffectList) (id id' : nat) (ids : list nat) :
  length l = length vals ->
  length l = length eff ->
  length l = length ids ->
  (
    forall i, i < length l ->
      |env, nth_def ids id i, nth i (fst (split l)) ErrorExp, nth_def eff eff1 i| -e> | nth_def ids id (S i), inl (nth i vals ErrorValue), nth_def eff eff1 (S i)|
  ) ->
  eff3 = concatn eff1 eff (length eff) ++ eff2 ->
  |append_vars_to_env (snd (split l)) vals env, last ids id, e1, concatn eff1 eff (length eff)| -e> | id', val, eff3|
->
  |env, id, ETry l e1 e2 vex1 vex2 vex3, eff1| -e> | id', val, eff3|

(* catch *)
| eval_catch (env: Environment) (l : list (Expression * Var)) (e1 e2 : Expression) (vex1 vex2 vex3 : Var) 
      (val : Value + Exception) (vals : list Value) (ex : Exception) (eff1 eff2 eff3 eff4 : SideEffectList) (eff : list SideEffectList) (i : nat) (id id' : nat) (ids : list nat) :
  i < length l ->
  length vals = i ->
  length eff = i ->
  length ids = i ->
  (
    forall j, j < i ->
      |env, nth_def ids id j, nth j (fst (split l)) ErrorExp, concatn eff1 eff j| -e> |nth_def ids id (S j), inl (nth j vals ErrorValue), concatn eff1 eff (S j)|
  ) ->
  | env, last ids id, nth i (fst (split l)) ErrorExp, nth_def eff eff1 i| -e> |id', inr ex, nth_def eff eff1 i ++ eff2| ->
  eff4 = nth_def eff eff1 i ++ eff2 ++ eff3 ->
  |append_vars_to_env [vex1; vex2; vex3] 
                       [exclass_to_value (fst (fst ex)); snd (fst ex); snd ex] 
                       env, last ids id, e2, nth_def eff eff1 i ++ eff2|
 -e> 
  |id', val, eff4|
->
  |env, id, ETry l e1 e2 vex1 vex2 vex3, eff1| -e> |id', val, eff4|


(* case 2x *)
(** Pattern matching exception *)
| eval_case_ex_pat (env: Environment) (e : Expression) (ex : Exception) (l : list (Pattern * Expression * Expression))  (eff1 eff2 eff3 : SideEffectList)  (id id' : nat):
  eff3 = eff1 ++ eff2 ->
  |env, id, e, eff1| -e> |id', inr ex, eff3|
->
  |env, id, ECase e l, eff1| -e> |id', inr ex, eff3|

(** No matching clause *)
| eval_case_clause_ex (env: Environment) (e : Expression) (l : list (Pattern* Expression * Expression)) (v : Value) (eff1 eff2 eff3 : SideEffectList) (id id' : nat):
  eff3 = eff1 ++ eff2 ->
  |env, id, e, eff1| -e> | id', inl v, eff3| ->
  (forall j : nat, j < length l -> 

    (** THESE GUARDS MUST BE SIDE-EFFECT FREE ACCORDING TO 1.0.3 LANGUAGE SPECIFICATION *)
    (forall gg ee bb, match_clause v l j = Some (gg, ee, bb) -> 
      ((|add_bindings bb env, id', gg, eff1 ++ eff2| -e> | id', inl ffalse, eff3| ))

    )

  )
->
|env, id, ECase e l, eff1| -e> | id', inr (if_clause v), eff3|
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
    |env, nth_def ids id j, nth j params ErrorExp, concatn eff1 eff j|
   -e>
    |nth_def ids id (S j), inl (nth j vals ErrorValue), concatn eff1 eff (S j)|
  ) ->
  eff3 = nth_def eff eff1 i ++ eff2 ->
  |env, last ids id, nth i params ErrorExp, nth_def eff eff1 i| -e> |id', inr ex, eff3|

->
  |env, id, ECall fname params, eff1| -e> |id', inr ex, eff3|

(* apply 4x *)
(** According to ref. implementation, here it is not needed to check the arg number *)

(** if name expression evaluates to exception *)
| eval_app_ex_closure_ex (params : list Expression) (env : Environment) (exp : Expression)  
     (ex : Exception) (eff1 eff2 eff3 : SideEffectList) (id id' : nat):
  eff3 = eff1 ++ eff2 ->
  |env, id, exp, eff1| -e> |id', inr ex, eff3|
->
  |env, id, EApp exp params, eff1| -e> |id', inr ex, eff3|

(** name expression and some parameters evaluate to values *)
| eval_app_ex_params (params : list Expression) (vals : list Value) (env : Environment) 
     (exp : Expression) (ex : Exception) (i : nat) (v : Value) (eff1 eff2 eff3 eff4 : SideEffectList) 
     (eff : list SideEffectList) (ids : list nat) (id id' id'' : nat) :
  i = length vals ->
  i < length params ->
  length eff = i ->
  length ids = i
  ->
  |env, id, exp, eff1| -e> |id', inl v, eff1 ++ eff2| ->
  (forall j, j < i -> 
    |env, nth_def ids id' j, nth j params ErrorExp, concatn (eff1 ++ eff2) eff j|
   -e>
    |nth_def ids id' (S j), inl (nth j vals ErrorValue), concatn (eff1 ++ eff2) eff (S j)|
  ) ->
  eff4 = concatn (eff1 ++ eff2) eff i ++ eff3 ->
  |env, last ids id', nth i params ErrorExp, concatn (eff1 ++ eff2) eff i| -e> |id'', inr ex, eff4|
->
  |env, id, EApp exp params, eff1| -e> |id'', inr ex, eff4|

(** Then we check if the name expression evaluates to a closure *)
| eval_app_ex_closure (params : list Expression) (vals: list Value) (env : Environment) (v : Value) 
     (exp : Expression) (eff1 eff2 eff3 : SideEffectList) (eff : list SideEffectList) 
     (ids : list nat) (id id' id'' : nat):
  length params = length vals ->
  length params = length eff ->
  length params = length ids ->
  |env, id, exp, eff1| -e> |id', inl v, eff1 ++ eff2| ->
  (
    forall j : nat, j < length params ->
    (
      |env, nth_def ids id' j, nth j params ErrorExp, concatn (eff1 ++ eff2) eff j|
     -e>
      |nth_def ids id' (S j), inl (nth j vals ErrorValue), concatn (eff1 ++ eff2) eff (S j)|
    )
  ) ->
  (forall ref ext var_list body n, 
     v <> VClos ref ext n var_list body) ->
  eff3 = concatn (eff1 ++ eff2) eff (length params) ->
  id'' = last ids id'
->
  |env, id, EApp exp params, eff1| -e> |id'', inr (badfun v), eff3|

(** too few or too many arguments are given *)
| eval_app_ex_param_count (params : list Expression) (vals : list Value) (env : Environment) 
     (exp : Expression) (body : Expression) (var_list : list Var) (ref : Environment) 
     (ext : list (nat * FunctionIdentifier * FunctionExpression)) (eff1 eff2 eff3 : SideEffectList) 
     (eff : list SideEffectList) (n : nat) (ids : list nat) (id id' id'' : nat):
  length params = length vals ->
  length params = length eff ->
  length params = length ids ->
  |env, id, exp, eff1| -e> |id', inl (VClos ref ext n var_list body), eff1 ++ eff2| ->
  (
    forall j : nat, j < length params ->
    (
      |env, nth_def ids id' j, nth j params ErrorExp, concatn (eff1 ++ eff2) eff j|
     -e>
      |nth_def ids id' (S j), inl (nth j vals ErrorValue), concatn (eff1 ++ eff2) eff (S j)|
    )
  ) ->
  length var_list <> length vals ->
  eff3 = concatn (eff1 ++ eff2) eff (length params) ->
  id'' = last ids id'
->
  |env, id, EApp exp params, eff1| 
  -e> 
  |id'', inr (badarity (VClos ref ext n var_list body)), eff3|

(* let 1x *)
| eval_let_ex_param (env: Environment) (l: list (Var * Expression)) (vals : list Value) (e : Expression) (ex : Exception) (i : nat) (eff1 eff2 eff3 : SideEffectList) (eff : list SideEffectList) (id id' : nat) (ids : list nat) :
  length vals = i -> 
  i < length l ->
  length eff = i ->
  length ids = i ->
  (forall j, j < i -> 
    |env, nth_def ids id j, nth j (snd (split l)) ErrorExp, concatn eff1 eff j| -e> |nth_def ids id (S j), inl (nth j vals ErrorValue), concatn eff1 eff (S j)|
  ) ->
  eff3 = nth_def eff eff1 i ++ eff2 ->
  |env, last ids id, nth i (snd (split l)) ErrorExp, nth_def eff eff1 i| -e> |id', inr ex, eff3|
->
  |env, id, ELet l e, eff1| -e> | id', inr ex, eff3|

(* map 2x *)
(** Exception in key list *)
| eval_map_ex_key (l: list (Expression * Expression)) (vvals kvals : list Value) (env: Environment) (i : nat) (ex : Exception) (eff1 eff2 eff3 : SideEffectList) (eff : list SideEffectList) (ids : list nat) (id id' : nat):
  length vvals = i ->
  length kvals = i ->
  i < length l ->
  length eff = i * 2 ->
  length ids = i * 2 ->
  (
    forall j, j < i ->
    |env, nth_def ids id (2*j), nth j (fst (split l)) ErrorExp, concatn eff1 eff (2 * j)| -e> | nth_def ids id (S (2*j)), inl (nth j kvals ErrorValue), concatn eff1 eff (S (2 * j))|
  )
  ->
  (
    forall j, j < i ->
    |env, nth_def ids id (S(2*j)), nth j (snd (split l)) ErrorExp, concatn eff1 eff (S (2 * j))| -e> | nth_def ids id (S (S (2*j))), inl (nth j vvals ErrorValue), concatn eff1 eff (S (S (2 * j)))|
  )
  ->
  eff3 = concatn eff1 eff (2 * i) ++ eff2 ->
  |env, last ids id, nth i (fst (split l)) ErrorExp, concatn eff1 eff (2 * i)| -e> | id', inr ex, eff3|
->
  |env, id, EMap l, eff1| -e> | id', inr ex, eff3|

(** Exception in value list *)
|  eval_map_ex_val (l: list (Expression * Expression)) (vvals kvals : list Value) (env: Environment) (i : nat) (ex : Exception) (val : Value) (eff1 eff2 eff3 eff4 : SideEffectList) (eff : list SideEffectList) (ids : list nat) (id id' id'' : nat):
  length vvals = i ->
  length kvals = i ->
  i < length l ->
  length eff = i * 2 ->
  length ids = i * 2 ->
  (
    forall j, j < i ->
    |env, nth_def ids id (2*j), nth j (fst (split l)) ErrorExp, concatn eff1 eff (2 * j)| -e> | nth_def ids id (S (2*j)),  inl (nth j kvals ErrorValue), concatn eff1 eff (S (2 * j))|
  ) ->
  (
    forall j, j < i ->
    |env, nth_def ids id (S (2*j)), nth j (snd (split l)) ErrorExp, concatn eff1 eff (S (2 * j))| -e> | nth_def ids id (S (S (2*j))), inl (nth j vvals ErrorValue), concatn eff1 eff (S (S (2 * j)))|
  )
  ->
  |env, last ids id, nth i (fst (split l)) ErrorExp, concatn eff1 eff (2 * i)| -e> |id', inl val, concatn eff1 eff (2 * i) ++ eff2|
  ->
  eff4 = concatn eff1 eff (2 * i) ++ eff2 ++ eff3
  ->
  |env, id', nth i (snd (split l)) ErrorExp, concatn eff1 eff (2 * i) ++ eff2| -e> | id'', inr ex, eff4|
->
  |env, id, EMap l, eff1| -e> |id'', inr ex, eff4|

*)
where "| env , id , e , eff | -e> | id' , e' , eff' |" := (eval_expr env id e eff id' e' eff')
.


(* These are the initialization function before evaluating a module *)
(* Fixpoint add_elements_to_env (fl : list ErlFunction) : Environment :=
match fl with
| [] => []
| (TopLevelFun sig (vl,exp))::xs => insert_value_no_overwrite (add_elements_to_env xs) (inr sig) (VClos (inr sig) vl exp)
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

End Semantics.