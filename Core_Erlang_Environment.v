Load Core_Erlang_Helpers.

(* Environment and its functions *)
Module Core_Erlang_Environment.

Import Lists.List.
Import ListNotations.
Import Strings.String.

Import Core_Erlang_Syntax.
Import Core_Erlang_Helpers.

Definition Environment : Type := list ((Var + FunctionSignature) * Value).

(* get *)
Fixpoint get_value (env : Environment) (key : (Var + FunctionSignature)) : (Value + Exception) :=
match env with
| [ ] => inr novar
| (k,v)::xs => if uequal key k then inl v else get_value xs key
end.

(* set with overwrite *)
Fixpoint insert_value (env : Environment) (key : (Var + FunctionSignature)) (value : Value) : Environment :=
match env with
| [] => [(key, value)]
| (k,v)::xs => if uequal k key then (key,value)::xs else (k,v)::(insert_value xs key value)
end.

(* set without overwrite *)
Fixpoint insert_value_no_overwrite (env : Environment) (key : (Var + FunctionSignature)) (value : Value) : Environment :=
match env with
| [] => [(key, value)]
| (k,v)::xs => if uequal k key then env else (k,v)::(insert_value xs key value)
end.

(* Merge environments *)
Fixpoint env_fold (e1 e2: Environment) : Environment :=
match e1 with
| [] => e2
| (k,v)::xs => env_fold xs (insert_value e2 k v)
end.

(* Add additional bindings *)
(* We used here: when binding, variables must be unique *)
Fixpoint add_bindings (bindings : list (Var * Value)) (env : Environment) : Environment :=
match bindings with
| [] => env
| (v, e)::xs => add_bindings xs (insert_value env (inl v) e)
end.

(* Add bindings with two lists *)
Fixpoint append_vars_to_env (vl : list Var) (el : list Value) (d : Environment) : Environment :=
match vl, el with
| [], [] => d
| v::vs, e::es => append_vars_to_env vs es (insert_value d (inl v) e)
| _, _ => []
end.

(* Add functions *)
Fixpoint append_funs_to_env (vl : list FunctionSignature) (paramss : list (list Var)) (bodies : list Expression) (d : Environment) : Environment :=
match vl, paramss, bodies with
| [], [], [] => d
| v::vs, varl::ps, e::bs => append_funs_to_env vs ps bs (insert_value d (inr v) (VClosure (inr v) varl e))
| _, _, _ => []
end.

(* Examples *)
Compute append_vars_to_env ["A"%string; "A"%string] [(VLiteral EmptyMap); (VLiteral EmptyTuple)] [(inl "A"%string, VLiteral EmptyMap)].

End Core_Erlang_Environment.