(**
  This file defines variable environment for the big-step semantics of Core Erlang.
*)
From CoreErlang.BigStep Require Export Helpers.

(** Environment and its functions *)
Import ListNotations.

Definition Environment : Type := list ((Var + FunctionIdentifier) * Value).

Fixpoint count_closures (env : Environment) : nat :=
match env with
| [] => 0
| (_, VClos _ _ _ _ _)::xs => S (count_closures xs)
| _::xs => count_closures xs
end.

(** Get *)
Fixpoint get_value (env : Environment) (key : (Var + FunctionIdentifier)) 
   : option ValueSequence :=
match env with
| [ ] => None
| (k,v)::xs => if var_funid_eqb key k then Some [v] else get_value xs key
end.

(** Insert *)
(* DEPRICATED *)
Definition insert_value (env : Environment) (key : (Var + FunctionIdentifier)) 
   (value : Value) : Environment :=
(key, value) :: env.

(** Zip **)
Fixpoint zip {A B : Type} (al : list A) (bl : list B) : list (A * B) :=
match al, bl with
| a :: al', b :: bl' => (a, b) :: zip al' bl'
| _, _ => []
end.

(** Add additional bindings *)
(** We used here: when binding, variables must be unique *)
Definition add_bindings (bindings : list (Var * Value)) (env : Environment) : Environment :=
map (fun '(var, val) => (inl var, val)) bindings ++ env.

(** Add bindings with two lists *)
Definition append_vars_to_env (vl : list Var) (el : list Value) (d : Environment) 
   : Environment :=
zip (map inl vl) el ++ d.


Definition append_try_vars_to_env (vl : list Var) (el : list Value) (d : Environment) 
   : Environment :=
match el with
| [] => []
| e::es =>
if length vl =? 2 then append_vars_to_env vl es d else append_vars_to_env vl el d
end.

Goal append_try_vars_to_env ["X"%string; "Y"%string] [VNil; VNil; VNil] []
= [(inl "X"%string, VNil); (inl "Y"%string, VNil)].
Proof. reflexivity. Qed.

(** Not Overwriting insert *)
(** Overwriting does not fit with this recursion *)
(* DEPRICATED *)
Definition insert_function (id : nat) (v : FunctionIdentifier) (p : list Var) (b : Expression) 
   (l : list (nat * FunctionIdentifier * FunctionExpression)) 
    : list (nat * FunctionIdentifier * FunctionExpression) :=
(id, v, (p, b)) :: l.

(** Lists represented functions *)
(* DEPRICATED *)
Fixpoint list_functions_old (vl : list FunctionIdentifier) (paramss : list (list Var)) 
      (bodies : list Expression) (last_id : nat) 
      : list (nat * FunctionIdentifier * FunctionExpression) :=
match vl, paramss, bodies with
| v::vs, varl::ps, e::bs => (last_id, v, (varl, e)) :: list_functions_old vs ps bs (S last_id)
| _, _, _ => []
end.

(* DEPRICATED *)
Fixpoint list_functions (last_id : nat)
      (l : list (FunctionIdentifier * ((list Var) * Expression)))
      : list (nat * FunctionIdentifier * FunctionExpression) :=
match l with
| (fid, (vars, e)) :: l' => (last_id, fid, (vars, e)) :: list_functions (S last_id) l'
| [] => []
end.

(** Add functions *)
(* DEPRICATED *)
Fixpoint append_funs_to_env_base (vl : list FunctionIdentifier) (paramss : list (list Var)) 
      (bodies : list Expression) (d : Environment) (def : Environment) 
      (deffuns : list (nat * FunctionIdentifier * FunctionExpression)) (last_id : nat) 
      : Environment :=
match vl, paramss, bodies with
| [], [], [] => d
| v::vs, varl::ps, e::bs => append_funs_to_env_base vs ps bs 
                              (insert_value d (inr v) 
                                           (VClos def deffuns last_id varl e)) 
                                           def deffuns (S last_id)
| _, _, _ => []
end.

(* DEPRICATED *)
Definition append_funs_to_env_old (l : list (FunctionIdentifier * ((list Var) * Expression))) (d : Environment) (last_id : nat) : Environment :=
append_funs_to_env_base (fst (split l)) (fst (split (snd (split l)))) (snd (split (snd (split l)))) d d 
                       (list_functions_old (fst (split l)) (fst (split (snd (split l)))) (snd (split (snd (split l)))) last_id)
                       last_id
.

Definition get_env (env : Environment)
   (ext : list (nat * FunctionIdentifier * FunctionExpression))
   : Environment :=
map
  (fun '(n, fid, (vars, e)) =>
    ((inr fid), (VClos env ext n vars e)))
  ext
++ env.

Definition append_funs_to_env (l : list (FunctionIdentifier * ((list Var) * Expression))) (d : Environment) (last_id : nat) : Environment :=
get_env d (list_functions last_id l).


(** Examples *)
(* Goal append_vars_to_env ["A"%string; "A"%string]
                           [(VEmptyMap); (VEmptyTuple)]
                           [(inl "A"%string, VEmptyMap)]
= [(inl "A"%string, VTuple [])].
Proof. Admitted.
Goal append_funs_to_env [(("f1"%string,0), ([], ErrorExp)) ; 
                            (("f2"%string,0), ([], ErrorExp)) ;
                            (("f1"%string,0), ([], ErrorExp)) ]
                           [(inl "X"%string, ErrorValue)] 0
=
[(inl "X"%string, VLit (Atom "error"));
       (inr ("f1"%string, 0),
       VClos [(inl "X"%string, VLit (Atom "error"))]
         [(2, ("f1"%string, 0), ([], ELit (Atom "error")));
         (1, ("f2"%string, 0), ([], ELit (Atom "error")))] 2 [] (ELit (Atom "error")));
       (inr ("f2"%string, 0),
       VClos [(inl "X"%string, VLit (Atom "error"))]
         [(2, ("f1"%string, 0), ([], ELit (Atom "error")));
         (1, ("f2"%string, 0), ([], ELit (Atom "error")))] 1 [] (ELit (Atom "error")))].
Proof. Admitted.
Goal insert_function 2 ("f1"%string, 0) [] ErrorExp (list_functions_old
                              [("f1"%string,0); ("f2"%string,0); ("f1"%string, 0)]
                              [[];[];[]]
                              [ErrorExp; ErrorExp; ErrorExp] 0)
= [(2, ("f1"%string, 0), ([], ELit (Atom "error")));
       (1, ("f2"%string, 0), ([], ELit (Atom "error")))].
Proof. Admitted. *)

(** Environment construction from the extension and the reference *)
(* DEPRICATED *)
Fixpoint get_env_base (env def : Environment) 
   (ext defext : list (nat * FunctionIdentifier * FunctionExpression))
   : Environment :=
match ext with
| [] => env
| (id, f1, (pl, b))::xs => get_env_base (insert_value env (inr f1) (VClos def defext id pl b)) def xs defext
end.

(* DEPRICATED *)
Definition get_env_old (env : Environment) 
   (ext : list (nat * FunctionIdentifier * FunctionExpression))
   : Environment :=
  get_env_base env env ext ext
.
