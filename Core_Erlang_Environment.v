Load Core_Erlang_Helpers.

(** Environment and its functions *)
Module Core_Erlang_Environment.

Import Lists.List.
Import ListNotations.
Import Strings.String.

Import Core_Erlang_Syntax.
Import Core_Erlang_Helpers.
Import Core_Erlang_Equalities.

Definition Environment : Type := list ((Var + FunctionIdentifier) * Value).

Fixpoint count_closures (env : Environment) : nat :=
match env with
| [] => 0
| (_, VClosure _ _ _ _ _)::xs => S (count_closures xs)
| _::xs => count_closures xs
end.

(** Get *)
Fixpoint get_value (env : Environment) (key : (Var + FunctionIdentifier)) : (Value + Exception) :=
match env with
| [ ] => inr novar
| (k,v)::xs => if uequal key k then inl v else get_value xs key
end.

Fixpoint insert_value (env : Environment) (key : (Var + FunctionIdentifier)) (value : Value) :=
match env with
  | [] => [(key, value)]
  | (k,v)::xs => if uequal k key then (key,value)::xs else (k,v)::(insert_value xs key value)
end.

(** Set with overwrite *)
(* Fixpoint insert_closure (env : Environment) (key : (Var + FunctionIdentifier)) (value : Value) (count : nat) : Environment :=
match value with
| VClosure def ext n ps b =>
  match env with
  | [] => [(key, VClosure def ext count ps b)]
  | (k,v)::xs => if uequal k key 
                 then match v with
                      | VClosure _ _ n _ _ => (key, VClosure def ext n ps b)::xs
                      | _ => (key, VClosure def ext count ps b)::xs
                      end
                 else (k,v)::(insert_value xs key value count)
  end
| _ =>
  match env with
  | [] => [(key, value)]
  | (k,v)::xs => if uequal k key then (key,value)::xs else (k,v)::(insert_value xs key value count)
  end
end. *)

(** Set without overwrite *)
(* Fixpoint insert_value_no_overwrite (env : Environment) (key : (Var + FunctionIdentifier)) (value : Value) : Environment :=
match env with
| [] => [(key, value)]
| (k,v)::xs => if uequal k key then env else (k,v)::(insert_value xs key value)
end.
 *)

(* Merge environments *)
(* Fixpoint env_fold (e1 e2: Environment) : Environment :=
match e1 with
| [] => e2
| (k,v)::xs => env_fold xs (insert_value e2 k v)
end. *)

(** Add additional bindings *)
(** We used here: when binding, variables must be unique *)
Fixpoint add_bindings (bindings : list (Var * Value)) (env : Environment) : Environment :=
match bindings with
| [] => env
| (v, e)::xs => add_bindings xs (insert_value env (inl v) e)
end.

(** Add bindings with two lists *)
Fixpoint append_vars_to_env (vl : list Var) (el : list Value) (d : Environment) : Environment :=
match vl, el with
| [], [] => d
| v::vs, e::es => append_vars_to_env vs es (insert_value d (inl v) e)
| _, _ => []
end.

(** Not Overwriting insert *)
(** Overwriting does not fit with this recursion *)
Fixpoint insert_function (id : nat) (v : FunctionIdentifier) (p : list Var) (b : Expression) 
 (l : list (nat * FunctionIdentifier * FunctionExpression)) : list (nat * FunctionIdentifier * FunctionExpression) :=
match l with
| [] => [(id, v, (p, b))]
| (id', k, v0)::xs => if equal k v then (id', k, v0)::xs else (id', k, v0)::(insert_function id v p b xs)
end.

(** Lists represented functions *)
Fixpoint list_functions (vl : list FunctionIdentifier) (paramss : list (list Var)) 
      (bodies : list Expression) (last_id : nat) : list (nat * FunctionIdentifier * FunctionExpression) :=
match vl, paramss, bodies with
| [], [], [] => []
| v::vs, varl::ps, e::bs => insert_function last_id v varl e (list_functions vs ps bs (S last_id))
| _, _, _ => []
end.

(* (** Inserting closures *)
Fixpoint insert_closure (name : FunctionIdentifier) (env def : Environment) (deffuns : list (FunctionIdentifier * FunctionExpression)) (params : list Var) (count : nat)
      (body :  Expression) : Environment :=
match env with
| [] => [(inr name, VClosure def deffuns count varl e)]
| (k,v)::xs => if uequal k (inr name) then (key,value)::xs else (k,v)::(insert_value xs key value)
end. *)

(** Add functions *)
Fixpoint append_funs_to_env_base (vl : list FunctionIdentifier) (paramss : list (list Var)) 
      (bodies : list Expression) (d : Environment) (def : Environment) 
      (deffuns : list (nat * FunctionIdentifier * FunctionExpression)) (last_id : nat) : Environment :=
match vl, paramss, bodies with
| [], [], [] => d
| v::vs, varl::ps, e::bs => append_funs_to_env_base vs ps bs 
                              (insert_value d (inr v) (VClosure def deffuns last_id varl e)) def deffuns (S last_id)
| _, _, _ => []
end.

Definition append_funs_to_env (vl : list FunctionIdentifier) (paramss : list (list Var)) 
      (bodies : list Expression) (d : Environment) (last_id : nat) : Environment :=
append_funs_to_env_base vl paramss bodies d d (list_functions vl paramss bodies last_id) last_id
.

(** Examples *)
Compute append_vars_to_env ["A"%string; "A"%string]
                           [(VEmptyMap); (VEmptyTuple)]
                           [(inl "A"%string, VEmptyMap)].

Compute append_funs_to_env [("f1"%string,0); ("f2"%string,0); ("f1"%string, 0)]
                           [[];[];[]] 
                           [ErrorExp; ErrorExp; ErrorExp]
                           [(inl "X"%string, ErrorValue)] 0.

Compute insert_function 2 ("f1"%string, 0) [] ErrorExp (list_functions
                              [("f1"%string,0); ("f2"%string,0); ("f1"%string, 0)]
                              [[];[];[]]
                              [ErrorExp; ErrorExp; ErrorExp] 0).

(** Environment construction from the extension and the reference *)
Fixpoint get_env_base (env def : Environment) (ext defext : list (nat * FunctionIdentifier * FunctionExpression))
   : Environment :=
match ext with
| [] => env
| (id, f1, (pl, b))::xs => get_env_base (insert_value env (inr f1) (VClosure def defext id pl b)) def xs defext
end.

Definition get_env (env : Environment) (ext : list (nat * FunctionIdentifier * FunctionExpression))
   : Environment :=
  get_env_base env env ext ext
.

End Core_Erlang_Environment.