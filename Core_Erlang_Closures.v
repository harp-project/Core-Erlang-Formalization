Load Core_Erlang_Environment.

(* Closures and functions *)
Module Core_Erlang_Closures.

Import Lists.List.
Import ListNotations.
Import Strings.String.

Import Core_Erlang_Helpers.
Import Core_Erlang_Environment.
Import Core_Erlang_Syntax.

Definition Closures : Type := list ((Var + FunctionSignature) * Environment).

(* Add closure to the existing ones *)
Fixpoint set_closure (cl: Closures) (v : (Var + FunctionSignature)) (env : Environment) : Closures :=
match cl with
| [] => [(v, env)]
| (k, e)::xs => if uequal k v then (v, env)::xs else ((k, e)::(set_closure xs v env))
end.

(* Add closure without overwriting the existing ones *)
Fixpoint set_closure_no_overwrite (cl: Closures) (v : (Var + FunctionSignature)) (env : Environment) : Closures :=
match cl with
| [] => [(v, env)]
| (k, e)::xs => if uequal k v then cl else ((k, e)::(set_closure xs v env))
end.

(* Check, if the closure associated with the name exists, and delete it *)
Fixpoint check_closure (cl: Closures) (v : Var + FunctionSignature) : Closures :=
match cl with
| [] => []
| (k, env)::xs => if uequal k v then check_closure xs v else (k, env) :: (check_closure xs v)
end.

(* Append closures to the existiong ones with variable declaration signature *)
(* We never use both together, so its better to have them separated -> easier to maintain *)
Fixpoint append_vars_to_closure (vars : list Var) (exps : list Expression) (cl : Closures) (env : Environment) : Closures :=
match vars, exps with
| [], [] => cl
| v::vs, (EFunction _)::es => append_vars_to_closure vs es (set_closure cl (inl v) env) env
| v::vs, _::es => append_vars_to_closure vs es (check_closure cl (inl v)) env
| _, _ => []
end.

(* Append closures to the existiong ones with function declaration signature *)
Fixpoint append_funs_to_closure (fnames : list FunctionSignature) (cl : Closures) (env : Environment) : Closures :=
match fnames with
| [] => cl
| x::xs => append_funs_to_closure xs (set_closure cl (inr x) env) env
end.

(* Get *)
Fixpoint get_env_from_closure (v: Var + FunctionSignature) (cl : Closures) : Environment :=
match cl with
| [] => []
| (k, env)::xs => if uequal k v then env else get_env_from_closure v xs
end.

(* Get the accessable closures *)
(* Fixpoint get_next_closure (v : Var + FunctionSignature) (cl : Closures) : Closures :=
match cl with
| [] => []
| (k, env)::xs => if uequal k v then [] else (k, env)::(get_next_closure v xs)
end.*)

(* Examples *)
Compute append_vars_to_closure ["X"%string] [EFunction (FunDecl [] (EApply "Y"%string []))]
  [(inl "Y"%string, [(inl "Z"%string, exist _ (ELiteral EmptyList) (VJ_Literal _))])]
  [(inl "Z"%string, exist _ (ELiteral EmptyList) (VJ_Literal _)); (inl "Y"%string, exist _ (EFunction _) (VJ_Function _))].

End Core_Erlang_Closures.