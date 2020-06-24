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

Fixpoint insert_original_value (env : Environment) (key : (Var + FunctionIdentifier)) (value : Value) :=
match env with
  | [] => [(key, value)]
  | (k,v)::xs => if uequal k key then (key,value)::xs else (k,v)::(insert_original_value xs key value)
end.

(** Set with overwrite *)
Fixpoint insert_value (env : Environment) (key : (Var + FunctionIdentifier)) (value : Value) (count : nat) : Environment :=
match value with
| VClosure def ext n ps b =>
  match env with
  | [] => [(key, VClosure def ext count ps b)]
  | (k,v)::xs => if uequal k key then (key, VClosure def ext (count - 1) ps b)::xs else (k,v)::(insert_value xs key value count)
  end
| _ =>
  match env with
  | [] => [(key, value)]
  | (k,v)::xs => if uequal k key then (key,value)::xs else (k,v)::(insert_value xs key value count)
  end
end.

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
| (v, e)::xs => add_bindings xs (insert_original_value env (inl v) e)
end.

(** Add bindings with two lists *)
Fixpoint append_vars_to_env (vl : list Var) (el : list Value) (d : Environment) : Environment :=
match vl, el with
| [], [] => d
| v::vs, e::es => append_vars_to_env vs es (insert_original_value d (inl v) e)
| _, _ => []
end.

(** Overwriting insert *)
Fixpoint insert_function (v : FunctionIdentifier) (p : list Var) (b : Expression) 
 (l : list (FunctionIdentifier * FunctionExpression)) : list (FunctionIdentifier * FunctionExpression) :=
match l with
| [] => [(v, (p, b))]
| (k, v0)::xs => if equal k v then (v, (p, b))::xs else (k, v0)::(insert_function v p b xs)
end.

(** Lists represented functions *)
Fixpoint list_functions (vl : list FunctionIdentifier) (paramss : list (list Var)) 
      (bodies : list Expression) : list (FunctionIdentifier * FunctionExpression) :=
match vl, paramss, bodies with
| [], [], [] => []
| v::vs, varl::ps, e::bs => insert_function v varl e (list_functions vs ps bs)
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
(* TODO: insert_value should be modified, for equal closures *)
Fixpoint append_funs_to_env (vl : list FunctionIdentifier) (paramss : list (list Var)) 
      (bodies : list Expression) (d : Environment) (def : Environment) 
      (deffuns : list (FunctionIdentifier * FunctionExpression)) : Environment :=
match vl, paramss, bodies with
| [], [], [] => d
| v::vs, varl::ps, e::bs => append_funs_to_env vs ps bs 
                              (insert_value d (inr v) (VClosure def deffuns 0 varl e) (count_closures d)) def deffuns
| _, _, _ => []
end.

(** Examples *)
Compute append_vars_to_env ["A"%string; "A"%string]
                           [(VEmptyMap); (VEmptyTuple)]
                           [(inl "A"%string, VEmptyMap)].

Compute append_funs_to_env [("f1"%string,0); ("f1"%string,0); ("f2"%string, 0)]
                           [[];[];[]] 
                           [ErrorExp; ErrorExp; ErrorExp]
                           [(inl "X"%string, ErrorValue)]
                           [(inl "X"%string, ErrorValue)]
                           (list_functions
                              [("f1"%string,0); ("f2"%string,0); ("f3"%string, 0)]
                              [[];[];[]]
                              [ErrorExp; ErrorExp; ErrorExp]).

(** Environment construction from the extension and the reference *)
Fixpoint get_env (env def : Environment) (ext defext : list (FunctionIdentifier * FunctionExpression))
   : Environment :=
match ext with
| [] => env
| (f1, (pl, b))::xs => get_env (insert_value env (inr f1) (VClosure def defext 0 pl b) (count_closures env)) def xs defext
end.

End Core_Erlang_Environment.