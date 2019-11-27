Load Core_Erlang_Helpers.

(* Environment and it's functions *)
Module Core_Erlang_Environment.

Import Lists.List.
Import ListNotations.
Import Strings.String.

Import Core_Erlang_Syntax.
Import Core_Erlang_Helpers.

Definition Environment : Type := list ((Var + FunctionSignature) * Value).

(* get *)
Fixpoint get_value (env : Environment) (key : (Var + FunctionSignature)) : Value :=
match env with
| [ ] => ErrorValue
| (k,v)::xs => if uequal key k then v else get_value xs key
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

(* Fixpoint env_list_fold (l : list Environment) : Environment :=
match l with
| [] => []
-| x::xs => env_fold (env_list_fold xs) x (* DO NOT CHANGE THIS ORDER *)
end.*)

(* Fixpoint build_env (vl : list Var) (el : list Expression) : Environment :=
match vl, el with
| [], [] => []
| v::vs, e::es => insert_value_no_overwrite (build_env vs es) (inl v) e
| _, _ => []
end.

Compute env_list_fold [build_env ["A"%string; "A"%string] [ELiteral EmptyMap; ELiteral EmptyMap] ;
                  (build_env ["A"%string; "A"%string] [ELiteral EmptyMap; ELiteral EmptyTuple])].*)


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
Fixpoint append_funs_to_env (vl : list FunctionSignature) (el : list Fun) (d : Environment) : Environment :=
match vl, el with
| [], [] => d
| v::vs, f::es => append_funs_to_env vs es (insert_value d (inr v) (exist _ (EFunction f) (VJ_Function f))) (*We box the function*)
| _, _ => []
end.

(* Examples *)
Compute append_vars_to_env ["A"%string; "A"%string] [exist _ (ELiteral EmptyMap) (VJ_Literal _); exist _ (ELiteral EmptyTuple) (VJ_Literal _)] [(inl "A"%string, exist _ (ELiteral EmptyTuple) (VJ_Literal _))].

End Core_Erlang_Environment.