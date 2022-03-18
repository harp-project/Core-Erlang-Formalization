Require Core_Erlang_Auxiliaries.

(** The Semantics of Core Erlang *)
Module Semantics.

Export Core_Erlang_Auxiliaries.Auxiliaries.
Export Core_Erlang_Environment.Environment.

Import ListNotations.

Reserved Notation "| env , id , e , eff | -e> | id' , e' , eff' |" (at level 70).
(* Reserved Notation "| env , id , e , eff | -s> | id' , e' , eff' |" (at level 70). *)
Inductive eval_expr : Environment -> nat -> Expression -> SideEffectList -> nat ->
    (ValueSequence + Exception) -> SideEffectList -> Prop :=
(* valuelist evaluation *)
| eval_values env exps vals eff ids eff1 id eff' id':
  length exps = length vals ->
  length exps = length eff ->
  length exps = length ids ->
  (
    forall i, i < length exps ->
    |env, nth_def ids id 0 i, nth i exps ErrorExp, nth_def eff eff1 [] i|
     -e> 
    |nth_def ids id 0 (S i), inl [nth i vals ErrorValue], nth_def eff eff1 [] (S i)|
  ) ->
  id' = last ids id ->
  eff' = last eff eff1
->
  |env, id, EValues exps, eff1| -e> |id', inl vals, eff'|

(* valuelist exception *)

| eval_values_ex env exps ex vals eff ids eff1 id eff' id' i:
  i < length exps ->
  length vals = i ->
  length eff = i ->
  length ids = i ->
  (
    forall j, j < i ->
    |env, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j|
     -e> 
    |nth_def ids id 0 (S j), inl [nth j vals ErrorValue], nth_def eff eff1 [] (S j)|
  ) ->
  |env, last ids id, nth i exps ErrorExp, last eff eff1| -e> |id', inr ex, eff'|
->
  |env, id, EValues exps, eff1| -e> |id', inr ex, eff'|

(* 
| eval_single env id e eff1 id' res eff':
  |env, id, e, eff1| -s> |id', res, eff'|
->
  |env, id, ESingle e, eff1| -e> |id', res, eff'|

where "| env , id , e , eff | -e> | id' , e' , eff' |" := (eval_expr env id e eff id' e' eff')
with eval_singleexpr : Environment -> nat -> SingleExpression -> SideEffectList -> nat ->
    (ValueSequence + Exception) -> SideEffectList -> Prop := *)

| eval_nil (env : Environment) (eff : SideEffectList) (id : nat):
  |env, id, ENil, eff| -e> |id, inl [VNil], eff|

(* literal evaluation rule *)
| eval_lit (env : Environment) (l : Literal) (eff : SideEffectList) (id : nat):
  |env, id, ELit l, eff| -e> |id, inl [VLit l], eff|

(* variable evaluation rule *)
| eval_var (env:Environment) (s: Var) (eff : SideEffectList) (id : nat) 
      (res : ValueSequence) :
  get_value env (inl s) = Some res
->
  |env, id, EVar s, eff| -e> |id, inl res, eff|

(* Function Identifier evaluation rule *)
| eval_funid (env:Environment) (fid : FunctionIdentifier) (eff : SideEffectList) 
    (res : ValueSequence) (id : nat):
  get_value env (inr fid) = Some res
->
  |env, id, EFunId fid, eff| -e> |id, inl res, eff|

(* Function evaluation *)
| eval_fun (env : Environment) (vl : list Var) (e : Expression) (eff : SideEffectList) (id : nat):
  |env, id, EFun vl e, eff| -e> |S id, inl [VClos env [] id vl e], eff|

(* tuple evaluation rule *)
| eval_tuple (env: Environment) (exps : list Expression) (vals : list Value) 
     (eff1 eff2 : SideEffectList) (eff : list SideEffectList) (ids : list nat) (id id' : nat) :
  length exps = length vals ->
  length exps = length eff ->
  length exps = length ids ->
  (
    forall i, i < length exps ->
      |env, nth_def ids id 0 i, nth i exps ErrorExp, nth_def eff eff1 [] i| 
     -e> 
      |nth_def ids id 0 (S i), inl [nth i vals ErrorValue], nth_def eff eff1 [] (S i)|
  ) ->
  eff2 = last eff eff1 ->
  id' = last ids id (* if length = 0, then last id = first id *)
->
  |env, id, ETuple exps, eff1| -e> |id' , inl [VTuple vals], eff2|

(* list evaluation rule *)
| eval_cons (env:Environment) (hd tl: Expression) (hdv tlv : Value) 
     (eff1 eff2 eff3 : SideEffectList) (id id' id'' : nat) :
  |env, id, tl, eff1| -e> |id', inl [tlv], eff2| ->
  |env, id', hd, eff2| -e> | id'', inl [hdv], eff3|
->
  |env, id, ECons hd tl, eff1| -e> |id'', inl [VCons hdv tlv], eff3|

(* case evaluation rules *)
| eval_case (env: Environment) (guard exp: Expression) (e : Expression) (vals : ValueSequence) (res : ValueSequence + Exception) (l : list (list Pattern * Expression * Expression)) (bindings: list (Var * Value)) (i : nat) (eff1 eff2 eff3 : SideEffectList) (id id' id'' : nat) :
  |env, id, e, eff1| -e> |id', inl vals, eff2| ->
  i < length l ->
  match_clause vals l i = Some (guard, exp, bindings) ->
  (forall j : nat, j < i -> 

    (** THESE GUARDS MUST BE SIDE-EFFECT FREE ACCORDING TO 1.0.3 LANGUAGE SPECIFICATION *)
    (forall gg ee bb, match_clause vals l j = Some (gg, ee, bb) -> 
      (|add_bindings bb env, id', gg, eff2| -e> |id', inl [ffalse], eff2| ))

  ) ->
  |add_bindings bindings env, id', guard, eff2| -e> |id', inl [ttrue], eff2| -> 
  |add_bindings bindings env, id', exp, eff2| -e> |id'', res, eff3|
->
  |env, id, ECase e l, eff1| -e> |id'', res, eff3|


(* call evaluation rule *)
| eval_call (env: Environment) (res : ValueSequence + Exception) (params : list Expression) 
     (vals : list Value) (mexp : Expression) (fexp: Expression) (mname fname : string) (eff1 eff2 eff3 eff4 : SideEffectList) (eff : list SideEffectList) 
     (ids : list nat) (id id' id'' id''' : nat) :
  length params = length vals ->
  length params = length eff ->
  length params = length ids ->
  |env, id, mexp, eff1| -e> |id', inl [VLit (Atom mname)], eff2| -> 
  |env, id', fexp, eff2| -e> |id'', inl [VLit (Atom fname)], eff3| -> 
  (
    forall i, i < length params ->
      |env, nth_def ids id'' 0 i, nth i params ErrorExp, nth_def eff eff3 [] i| 
     -e>
      |nth_def ids id'' 0 (S i), inl [nth i vals ErrorValue], nth_def eff eff3 [] (S i)|
  ) ->
  eval mname fname vals (last eff eff3) = (res, eff4) ->
  id''' = last ids id''
->
  |env, id, ECall mexp fexp params, eff1| -e> |id''', res, eff4|

(* primop evaluation rule *)
| eval_primop (env: Environment) (res : ValueSequence + Exception) (params : list Expression) 
     (vals : list Value) (fname: string) (eff1 eff2: SideEffectList) (eff : list SideEffectList) 
     (ids : list nat) (id id' : nat) :
  length params = length vals ->
  length params = length eff ->
  length params = length ids ->
  (
    forall i, i < length params ->
      |env, nth_def ids id 0 i, nth i params ErrorExp, nth_def eff eff1 [] i| 
     -e>
      |nth_def ids id 0 (S i), inl [nth i vals ErrorValue], nth_def eff eff1 [] (S i)|
  ) ->
  primop_eval fname vals (last eff eff1) = (res, eff2) ->
  id' = last ids id
->
  |env, id, EPrimOp fname params, eff1| -e> |id', res, eff2|

(* apply functions*)
| eval_app (params : list Expression) (vals : list Value) (env : Environment) 
     (exp : Expression) (body : Expression) (res : ValueSequence + Exception) (var_list : list Var) 
     (ref : Environment) (ext : list (nat * FunctionIdentifier * FunctionExpression)) (n : nat)
     (eff1 eff2 eff3 : SideEffectList) (eff : list SideEffectList) (ids : list nat) (id id' id'' : nat) :
  length params = length vals ->
  |env, id, exp, eff1| -e> |id', inl [VClos ref ext n var_list body], eff2| ->
  length var_list = length vals
  ->
  length params = length eff ->
  length params = length ids ->
  (
    forall i, i < length params ->
      |env, nth_def ids id' 0 i, nth i params ErrorExp, nth_def eff eff2 [] i|
     -e>
      |nth_def ids id' 0 (S i), inl [nth i vals ErrorValue], nth_def eff eff2 [] (S i)|
  )
  ->
  |append_vars_to_env var_list vals (get_env ref ext), 
   last ids id',
   body, 
   last eff eff2|
  -e>
   |id'', res, eff3|
->
  |env, id, EApp exp params, eff1| -e> |id'', res, eff3|

(* let evaluation rule *)
| eval_let (env: Environment) (l: list Var) (vals : ValueSequence) (e1 e2 : Expression) (res : ValueSequence + Exception) (eff1 eff' eff'' : SideEffectList) (id id' id'' : nat) :
  |env, id, e1, eff1| -e> |id', inl vals, eff'| ->
  length l = length vals ->
  |append_vars_to_env l vals env, id', e2, eff'| -e> |id'', res, eff''|
->
  |env, id, ELet l e1 e2, eff1| -e> |id'', res, eff''|

(* evaluation of sequence (do expressions) *)
| eval_seq (env : Environment) (e1 e2: Expression) (v1 : Value) (v2 : ValueSequence + Exception)
     (eff1 eff2 eff3 : SideEffectList) (id id' id'' : nat) :
   (* THE FIRST RESULT SHOULD BE A SINGLE VALUE *)
  |env, id, e1, eff1| -e> |id', inl [v1], eff2| ->
  |env, id', e2, eff2| -e> |id'', v2, eff3|
->
  | env, id, ESeq e1 e2, eff1 | -e> |id'', v2, eff3|

(* Letrec evaluation rule *)
| eval_letrec (env: Environment) (e : Expression)  (l : list (FunctionIdentifier * ((list Var) * Expression))) (res : ValueSequence + Exception) (eff1 eff2 : SideEffectList) (id id' : nat) :
  (
     |append_funs_to_env l env id, id + length l, e, eff1| -e> | id', res, eff2|
  )
->
  |env, id, ELetRec l e, eff1| -e> | id', res, eff2|



(* map evaluation rule *)
| eval_map (l: list (Expression * Expression)) (vvals kvals kvals' vvals' : list Value) ( lv : list (Value * Value)) (env: Environment) (eff1 eff2 : SideEffectList) (eff : list SideEffectList) (ids : list nat) (id id' : nat) :
  length l = length vvals ->
  length l = length kvals ->
  (length l) * 2 = length eff ->
  (length l) * 2 = length ids ->
  let exps := make_map_exps l in
  let vals := make_map_vals kvals vvals in
  (
    forall i : nat, i < length exps  ->
    |env, nth_def ids id 0 i, nth i exps ErrorExp, nth_def eff eff1 [] i| 
     -e>
    | nth_def ids id 0 (S i), inl [nth i vals ErrorValue], nth_def eff eff1 [] (S i)|
  ) ->
  make_value_map kvals vvals = (kvals', vvals') ->
  combine kvals' vvals' = lv ->
  eff2 = last eff eff1 ->
  id' = last ids id
->
  |env, id, EMap l, eff1| -e> |id', inl [VMap lv], eff2|


  (* EXCEPTIONS *)
(* list tail exception *)
| eval_cons_tl_ex (env: Environment) (hd tl : Expression) (ex : Exception) 
      (eff1 eff2 : SideEffectList) (id id' : nat) :
  |env, id, tl, eff1| -e> |id', inr ex, eff2|
->
  |env, id, ECons hd tl, eff1| -e> |id', inr ex, eff2|

(* list head exception *)
| eval_cons_hd_ex (env: Environment) (hd tl : Expression) (ex : Exception) (vtl : Value) 
     (eff1 eff2 eff3 : SideEffectList) (id id' id'' : nat) :
  |env, id, tl, eff1| -e> |id', inl [vtl], eff2| -> 
  |env, id', hd, eff2| -e> |id'', inr ex, eff3|
->
  |env, id, ECons hd tl, eff1| -e> |id'', inr ex, eff3|


(* tuple exception *)
| eval_tuple_ex (env: Environment) (i : nat) (exps : list Expression) (vals : list Value) 
     (ex : Exception) (eff1 eff2 : SideEffectList) (eff : list SideEffectList) 
     (id id' : nat) (ids : list nat) :
  i < length exps ->
  length vals = i ->
  length eff = i ->
  length ids = i ->
  (forall j, j < i ->
    |env, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j|
   -e>
    |nth_def ids id 0 (S j), inl [nth j vals ErrorValue], nth_def eff eff1 [] (S j)|) ->
  |env, last ids id, nth i exps ErrorExp, last eff eff1| -e> |id', inr ex, eff2|
->
  |env, id, ETuple exps, eff1| -e> |id', inr ex, eff2|


(* try 2x *)
| eval_try (env: Environment) (vl1 vl2 : list Var) (e1 e2 e3 : Expression) (res : ValueSequence + Exception) (vals : ValueSequence) (eff1 eff2 eff3 : SideEffectList) (id id' id'' : nat) :
  |env, id, e1, eff1| -e> | id', inl vals, eff2| ->
  length vl1 = length vals ->
  |append_vars_to_env vl1 vals env, id', e2, eff2 | -e> | id'', res, eff3|
->
  |env, id, ETry e1 vl1 e2 vl2 e3, eff1| -e> | id'', res, eff3|


(* catch *)
| eval_catch (env: Environment) (vl1 vl2 : list Var) (e1 e2 e3 : Expression) (res : ValueSequence + Exception) (eff1 eff2 eff3 : SideEffectList) (id id' id'' : nat) (ex : Exception) :
  |env, id, e1, eff1| -e> |id', inr ex, eff2| ->
  |append_try_vars_to_env vl2 [exclass_to_value (fst (fst ex)); snd (fst ex); snd ex] env, id', e3, eff2|
 -e> 
  |id'', res, eff3|
->
  |env, id, ETry e1 vl1 e2 vl2 e3, eff1| -e> |id'', res, eff3|


(* case 2x *)
(** Pattern matching exception *)
| eval_case_pat_ex (env: Environment) (e : Expression) (ex : Exception) (l : list (list Pattern * Expression * Expression)) (eff1 eff2 : SideEffectList) (id id' : nat):
  |env, id, e, eff1| -e> |id', inr ex, eff2|
->
  |env, id, ECase e l, eff1| -e> |id', inr ex, eff2|

(** No matching clause *)
| eval_case_clause_ex (env: Environment) (e : Expression) (l : list (list Pattern * Expression * Expression)) (vals : ValueSequence) (eff1 eff2 : SideEffectList) (id id' : nat):
  |env, id, e, eff1| -e> |id', inl vals, eff2| ->
  (forall j : nat, j < length l -> 

    (** THESE GUARDS MUST BE SIDE-EFFECT FREE ACCORDING TO 1.0.3 LANGUAGE SPECIFICATION *)
    (forall gg ee bb, match_clause vals l j = Some (gg, ee, bb) -> 
      ((|add_bindings bb env, id', gg, eff2| -e> | id', inl [ffalse], eff2| ))

    )

  )
->
  |env, id, ECase e l, eff1| -e> | id', inr (if_clause), eff2|
(** ith guard exception -> guards cannot result in exception, i.e. this rule is not needed *)


(* call 1x *)
| eval_call_ex (env: Environment) (i : nat) (mexp: Expression) (fexp : Expression) (v v': Value)  (params : list Expression) 
     (vals : list Value) (ex : Exception) (eff1 eff2 eff3 eff4 : SideEffectList) 
     (eff : list SideEffectList) (id id' id'' id''' : nat) (ids : list nat) :
  i < length params ->
  length vals = i ->
  length eff = i ->
  length ids = i ->
  |env, id, mexp, eff1| -e> |id', inl [v], eff2| -> 
  |env, id', fexp, eff2| -e> |id'', inl [v'], eff3| -> 
  (forall j, j < i ->
    |env, nth_def ids id'' 0 j, nth j params ErrorExp, nth_def eff eff3 [] j|
   -e>
    |nth_def ids id'' 0 (S j), inl [nth j vals ErrorValue], nth_def eff eff3 [] (S j)|
  ) ->
  |env, last ids id'', nth i params ErrorExp, last eff eff3| -e> |id''', inr ex, eff4|

->
  |env, id, ECall mexp fexp params, eff1| -e> |id''', inr ex, eff4|

(* Call: exception in module evaluation *)
| eval_call_mexp_ex (env : Environment) (mexp : Expression) (fexp : Expression) (params : list Expression)
    (ex : Exception) (eff1 eff2 : SideEffectList) (id id' : nat):
  |env, id, mexp, eff1| -e> |id', inr ex, eff2|
  ->
  |env, id, ECall mexp fexp params, eff1| -e> |id', inr ex, eff2|

(* Call: exception in (module's) function evaluation *)
| eval_call_fexp_ex (env : Environment) (mexp : Expression) (fexp : Expression) (v: Value) (params : list Expression)
    (ex : Exception) (eff1 eff2 eff3 : SideEffectList) (id id' id'' : nat):
  |env, id, mexp, eff1|  -e> |id', inl [v], eff2| -> 
  |env, id', fexp, eff2| -e> |id'', inr ex, eff3|
->
|env, id, ECall mexp fexp params, eff1| -e> |id'', inr ex, eff3|

(* Call: evaluated module exception is not atom *)
| eval_call_mexp_badarg_ex  (env : Environment) (mexp : Expression) (fexp : Expression) (v v': Value) (params : list Expression)
  (vals : list Value) ( eff1 eff2 eff3 eff4 : SideEffectList) (eff : list SideEffectList) (id id' id'' id''' : nat) (ids : list nat) :
    length params = length vals ->
    length params = length eff ->
    length params = length ids ->
    |env, id, mexp, eff1| -e> |id', inl [v], eff2| -> 
    |env, id', fexp, eff2| -e> |id'', inl [v'], eff3| -> 
    (
      forall i, i < length params ->
        |env, nth_def ids id'' 0 i, nth i params ErrorExp, nth_def eff eff3 [] i| 
       -e>
        |nth_def ids id'' 0 (S i), inl [nth i vals ErrorValue], nth_def eff eff3 [] (S i)|
    ) ->
    (forall (mname : string) ,
    v <> VLit (Atom mname)) ->
    eff4 = last eff eff3 ->
    id''' = last ids id'' ->
  |env, id, ECall mexp fexp params, eff1| -e> |id''', (inr (badarg v)), eff4|

(* Call: evaluated function exception is not atom *)
| eval_call_fexp_fun_clause_ex (env : Environment) (mexp : Expression) (fexp : Expression) (mname : string) (v': Value) (params : list Expression)
(vals : list Value) ( eff1 eff2 eff3 eff4 : SideEffectList) (eff : list SideEffectList) (id id' id'' id''' : nat) (ids : list nat) :
  length params = length vals ->
  length params = length eff ->
  length params = length ids ->
  |env, id, mexp, eff1| -e> |id', inl [VLit (Atom mname)], eff2| -> 
  |env, id', fexp, eff2| -e> |id'', inl [v'], eff3| -> 
  (
    forall i, i < length params ->
      |env, nth_def ids id'' 0 i, nth i params ErrorExp, nth_def eff eff3 [] i| 
     -e>
      |nth_def ids id'' 0 (S i), inl [nth i vals ErrorValue], nth_def eff eff3 [] (S i)|
  ) ->
  (forall (fname : string) ,
  v' <> VLit (Atom fname)) ->
  eff4 = last eff eff3 ->
  id''' = last ids id'' ->
|env, id, ECall mexp fexp params, eff1| -e> |id''', (inr (fun_clause v')), eff4|




(* TODO:  exceptions
            - valuelist exception (DONE)
            - mexp exception      (HELP: app)
            - fexp exception      (HELP: app)
            - mexp is not atom
            - fexp is not atom
            - no module found (later)
            - no function found (later)
            - eval is not working
*)


(* primop 1x *)
| eval_primop_ex (env: Environment) (i : nat) (fname : string) (params : list Expression) 
     (vals : list Value) (ex : Exception) (eff1 eff2 : SideEffectList) 
     (eff : list SideEffectList) (id id' : nat) (ids : list nat) :
  i < length params ->
  length vals = i ->
  length eff = i ->
  length ids = i ->
  (forall j, j < i ->
    |env, nth_def ids id 0 j, nth j params ErrorExp, nth_def eff eff1 [] j|
   -e>
    |nth_def ids id 0 (S j), inl [nth j vals ErrorValue], nth_def eff eff1 [] (S j)|
  ) ->
  |env, last ids id, nth i params ErrorExp, last eff eff1| -e> |id', inr ex, eff2|

->
  |env, id, EPrimOp fname params, eff1| -e> |id', inr ex, eff2|


(* apply 4x *)
(** According to ref. implementation, here it is not needed to check the arg number *)

(** if name expression evaluates to exception *)
| eval_app_closure_ex (params : list Expression) (env : Environment) (exp : Expression)  
     (ex : Exception) (eff1 eff2 : SideEffectList) (id id' : nat):
  |env, id, exp, eff1| -e> |id', inr ex, eff2|
->
  |env, id, EApp exp params, eff1| -e> |id', inr ex, eff2|

(** name expression and some parameters evaluate to values *)
| eval_app_param_ex (params : list Expression) (vals : list Value) (env : Environment) 
     (exp : Expression) (ex : Exception) (i : nat) (v : Value) (eff1 eff2 eff3 : SideEffectList) 
     (eff : list SideEffectList) (ids : list nat) (id id' id'' : nat) :
  i < length params ->
  length vals = i ->
  length eff = i ->
  length ids = i
  ->
  |env, id, exp, eff1| -e> |id', inl [v], eff2| ->
  (forall j, j < i -> 
    |env, nth_def ids id' 0 j, nth j params ErrorExp, nth_def eff eff2 [] j|
   -e>
    |nth_def ids id' 0 (S j), inl [nth j vals ErrorValue], nth_def eff eff2 [] (S j)|
  ) ->
  |env, last ids id', nth i params ErrorExp, last eff eff2| -e> |id'', inr ex, eff3|
->
  |env, id, EApp exp params, eff1| -e> |id'', inr ex, eff3|

(** Then we check if the name expression evaluates to a closure *)
| eval_app_badfun_ex (params : list Expression) (vals: list Value) (env : Environment) (v : Value) 
     (exp : Expression) (eff1 eff2 eff3 : SideEffectList) (eff : list SideEffectList) 
     (ids : list nat) (id id' id'' : nat):
  length params = length vals ->
  length params = length eff ->
  length params = length ids ->
  |env, id, exp, eff1| -e> |id', inl [v], eff2| ->
  (
    forall j : nat, j < length params ->
    (
      |env, nth_def ids id' 0 j, nth j params ErrorExp, nth_def eff eff2 [] j|
     -e>
      |nth_def ids id' 0 (S j), inl [nth j vals ErrorValue], nth_def eff eff2 [] (S j)|
    )
  ) ->
  (forall ref ext var_list body n, 
     v <> VClos ref ext n var_list body) ->
  eff3 = last eff eff2 ->
  id'' = last ids id'
->
  |env, id, EApp exp params, eff1| -e> |id'', inr (badfun v), eff3|

(** too few or too many arguments are given *)
| eval_app_badarity_ex (params : list Expression) (vals : list Value) (env : Environment) 
     (exp : Expression) (body : Expression) (var_list : list Var) (ref : Environment) 
     (ext : list (nat * FunctionIdentifier * FunctionExpression)) (eff1 eff2 eff3 : SideEffectList) 
     (eff : list SideEffectList) (n : nat) (ids : list nat) (id id' id'' : nat):
  length params = length vals ->
  length params = length eff ->
  length params = length ids ->
  |env, id, exp, eff1| -e> |id', inl [VClos ref ext n var_list body], eff2| ->
  (
    forall j : nat, j < length params ->
    (
      |env, nth_def ids id' 0 j, nth j params ErrorExp, nth_def eff eff2 [] j|
     -e>
      |nth_def ids id' 0 (S j), inl [nth j vals ErrorValue], nth_def eff eff2 [] (S j)|
    )
  ) ->
  length var_list <> length vals ->
  eff3 = last eff eff2 ->
  id'' = last ids id'
->
  |env, id, EApp exp params, eff1| 
  -e> 
  |id'', inr (badarity (VClos ref ext n var_list body)), eff3|

(* let 1x *)
| eval_let_ex (env: Environment) (vl: list Var) (e1 e2 : Expression) (ex : Exception) (eff1 eff2 : SideEffectList) (id id' : nat) :
  |env, id, e1, eff1| -e> |id', inr ex, eff2|
->
  |env, id, ELet vl e1 e2, eff1| -e> | id', inr ex, eff2|

(* sequence 1x *)
| eval_seq_ex (env : Environment) (e1 e2: Expression) (ex : Exception)
     (eff1 eff2 : SideEffectList) (id id' : nat) :
  |env, id, e1, eff1| -e> |id', inr ex, eff2|
->
  | env, id, ESeq e1 e2, eff1 | -e> |id', inr ex, eff2|


(* map 2x *)
(** Exception in key list *)
| eval_map_ex (l: list (Expression * Expression)) (vvals kvals : list Value) (env: Environment) (i : nat) (ex : Exception) (eff1 eff2 : SideEffectList) (eff : list SideEffectList) (ids : list nat) (id id' : nat):
  i < 2 * (length l) ->
  (* This method is simpler to handle in proofs, but not in the tactic:

  (length vvals = length kvals \/ S (length vvals) = length kvals) ->
  length kvals + length vvals = i ->

  *)
  length vvals = i / 2 ->
  length kvals = i / 2 + i mod 2 ->
  length eff = i ->
  length ids = i ->
  let exps := make_map_exps l in
  let vals := make_map_vals kvals vvals in
  (
    forall j, j < i ->
    |env, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j| -e> | nth_def ids id 0 (S j), inl [nth j vals ErrorValue], nth_def eff eff1 [] (S j)|
  )
  ->
  |env, last ids id, nth i exps ErrorExp, last eff eff1| -e> | id', inr ex, eff2|
->
  |env, id, EMap l, eff1| -e> | id', inr ex, eff2|

where "| env , id , e , eff | -e> | id' , e' , eff' |" := (eval_expr env id e eff id' e' eff')
.

(* Scheme eval_expr_ind2 := Induction for eval_expr Sort Prop
with eval_singleexpr_ind2 := Induction for eval_singleexpr Sort Prop.

Combined Scheme eval_ind from eval_expr_ind2, eval_singleexpr_ind2. *)

(* TODO: These are the initialization function before evaluating a module *)
(* Fixpoint add_elements_to_env (fl : list ErlFunction) : Environment :=
match fl with
| [] => []
| (TopLevelFun sig vl exp)::xs => insert_value_no_overwrite (add_elements_to_env xs) (inr sig) (VClos (inr sig) vl exp)
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

Reserved Notation "e --e-> v" (at level 50).
Inductive eval_to_result : Expression -> ValueSequence + Exception -> Prop :=
| eval_expr_intro e v : (exists n eff, | [], 0, e, [] | -e> |n, v, eff|) -> e --e-> v
where "e --e-> v" := (eval_to_result e v).

Definition valid_result (res : ValueSequence + Exception) :=
match res with
| inl vals => length vals =? 1
| _ => true
end.

(* Definition eval_to e :=
  exists res, e --e-> res /\ valid_expression e = true /\ valid_result res = true. *)


End Semantics.