(* BIGSTEP
From Coq Require Export ZArith.BinInt.
From Coq Require Export Strings.String.
From Coq Require Export Structures.OrderedTypeEx.
From Coq Require Export Numbers.DecimalString.

Export Lists.List.

Import Numbers.DecimalString.
Import ListNotations.

Definition Var : Type := string.

Inductive Literal : Type :=
| Atom (s: string)
| Integer (x : Z)
(* | Float (q : R) *).


Inductive Pattern : Type :=
| PVar     (v : Var)
| PLit (l : Literal)
| PCons  (hd tl : Pattern)
| PTuple (l : list Pattern)
| PMap (l : list (Pattern * Pattern))
| PNil.

Definition PEmptyTuple : Pattern := PTuple [].

Definition FunctionIdentifier : Type := string * nat.

Inductive Expression : Type :=
| EValues (el : list Expression)
(* | ESingle (e : SingleExpression)
with SingleExpression : Type := *)
| ENil
| ELit    (l : Literal)
| EVar    (v : Var)
| EFunId  (f : FunctionIdentifier)
| EFun    (vl : list Var) (e : Expression)
| ECons   (hd tl : Expression)
| ETuple  (l : list Expression)
(** Initially: for built-in functions : *)
| ECall   (m : Expression) (f : Expression) (l : list Expression) (*TODO: string -> exp *)
| EPrimOp (f : string)  (l : list Expression) (* only one string*)
(** For function applications: *)
| EApp    (exp: Expression)     (l : list Expression)
| ECase   (e : Expression) (l : list ((list Pattern) * Expression * Expression))
| ELet    (l : list Var) (e1 e2 : Expression)
(** For sequencing: do expressions (ESeq) *)
| ESeq    (e1 e2 : Expression)
| ELetRec (l : list (FunctionIdentifier * ((list Var) * Expression))) (e : Expression)
| EMap    (l : list (Expression * Expression))
| ETry    (e1 : Expression) (vl1 : list Var) (e2 : Expression) (vl2 : list Var) (e2 : Expression).

(* Coercion ESingle : SingleExpression >-> Expression.
Notation "^ e" := (ESingle e) (at level 20). *)

Definition EEmptyMap : Expression := EMap [].
Definition EEmptyTuple : Expression := ETuple [].

(* Module syntax *)

(*

(* Syntax of top level functions. *)
Definition TopLevelFunction : Type := FunctionIdentifier * (list Var *  Expression).

(* Syntax of attributes. An attribute  consists of a name and a value. *)
Definition ErlAttribute : Type := string * string.

(* Syntax of modules. Properties: Name, function identifiers, attributes, functions *)
Definition ErlModule : Type := string * (list FunctionIdentifier) * (list ErlAttribute) * (list TopLevelFunction).
*)



(* NOT USED *)
Record FunctionIdent := mkFunctionIdent { (* refactor next time ??!?*)
  func_name : string;
  arity : nat
}.

(* Syntax of attributes. An attribute  consists of a name and a value. *)
Definition ErlAttribute : Type := string * string.


(* Syntax of top level functions. *)
Record TopLevelFunction := mkTopLevelFunc {
  identifier : FunctionIdentifier;
  varl : list Var;
  body : Expression
}.

(* Syntax of modules. Properties: Name, function identifiers, attributes, functions *)
Record ErlModule  := mkModule {
  name : string ;
  funcIds : (list FunctionIdentifier) ;
  attrs : (list ErlAttribute) ;
  funcs : (list TopLevelFunction)
} .











Definition FunctionExpression : Type := list Var * Expression.

(** What expressions are in normal form 
    According to CE lang spec. value sequences cannot be nested
*)
Inductive Value : Type :=
| VNil
| VLit     (l : Literal)
| VClos    (env : list ((Var + FunctionIdentifier) * Value))
           (ext : list (nat * FunctionIdentifier * FunctionExpression))
           (id : nat)
           (vl : list Var)
           (e : Expression)
           (fid : option FunctionIdentifier)
| VCons    (vhd vtl : Value)
| VTuple   (vl : list Value)
| VMap     (l : list (Value * Value)).


(** Semantic domain *)
Definition ValueSequence := list Value.

(** Helper definitions *)
Definition VEmptyMap : Value := VMap [].
Definition VEmptyTuple : Value := VTuple [].

Definition ErrorValue : Value := (VLit (Atom "error"%string)).
(* Definition ErrorExp2 : Expression := (ELit (Atom "error"%string)). *)
Definition ErrorExp : Expression := (ELit (Atom "error"%string)).
Definition ErrorPat : Pattern := PLit(Atom "error"%string).
Definition ttrue : Value := VLit (Atom "true").
Definition ffalse : Value := VLit (Atom "false").
Definition ok : Value := VLit (Atom "ok").

Definition pretty_print_literal (l : Literal) : string :=
match l with
 | Atom s => "'" ++ s ++ "'"
 | Integer x => NilZero.string_of_int (Z.to_int x)
end.


Fixpoint pretty_print_value (v : Value) : string :=
match v with
 | VNil => "[]"
 | VLit l => pretty_print_literal l
 | VClos env ext id vl e fid => "'closure'"
 | VCons vhd vtl => "[" ++ pretty_print_value vhd ++ "|" ++ pretty_print_value vtl ++ "]"
 | VTuple vl => "{" ++ 
    (fix print_list vl : string :=
    match vl with
     | []    => ""%string
     | [x]   => pretty_print_value x
     | x::xs => (pretty_print_value x ++ ","%string ++ print_list xs)%string
    end
    ) vl 
    ++ "}"
 | VMap l => "#{" ++ 
    (fix print_list vl : string :=
    match vl with
     | []         => ""%string
     | [(x, y)]   => (pretty_print_value x ++ "=>" ++ pretty_print_value y)%string
     | (x, y)::xs => (pretty_print_value x ++ "=>" ++ pretty_print_value y ++ "," ++ print_list xs)%string
    end
    ) l
    ++ "}"
end.

Local Definition l1 : Value := VCons ttrue VNil.
Local Definition l2 : Value := VCons ttrue ttrue.
Local Definition l3 : Value := VCons (VCons ttrue ttrue) ttrue.
Local Definition l4 : Value := VCons ttrue (VCons ttrue (VCons ttrue VNil)).
Local Definition l5 : Value := VCons ttrue (VCons ttrue ttrue).

Compute (pretty_print_value (VTuple [VLit (Integer 55); VLit (Integer 55); VLit (Integer 55); ttrue; ffalse])).
Compute (pretty_print_value (VMap [(VLit (Integer 55), VLit (Integer 55)); (VLit (Integer 56), ttrue); (ffalse, ffalse)])).
Compute pretty_print_value VNil.
Compute pretty_print_value l1.
Compute pretty_print_value l2.
Compute pretty_print_value l3.
Compute pretty_print_value l4.
Compute pretty_print_value l5.

(** Exception representation *)
Inductive ExceptionClass : Type :=
| Error | Throw | Exit.

(** Exception class to value converter *)
Definition exclass_to_value (ex : ExceptionClass) : Value :=
match ex with
| Error => VLit (Atom "error"%string)
| Throw => VLit (Atom "throw"%string)
| Exit => VLit (Atom "exit"%string)
end.

Definition pp_exception_class (cl : ExceptionClass) : string :=
match cl with
| Error => "error"
| Throw => "throw"
| Exit  => "exit"
end.


(** Exception class, 1st Value : cause, 2nd Value : further details *)
Definition Exception : Type := ExceptionClass * Value * Value.

Definition pp_exception (e : Exception) : string :=
match e with
| (class, reason, info) => "{" ++ pp_exception_class class  ++ "," ++
                                  pretty_print_value reason ++ "," ++
                                  pretty_print_value info   ++ "}"
end.

Definition badarith (v : Value) : Exception :=
  (Error, VLit (Atom "badarith"%string), v).
Definition badarg (v : Value) : Exception :=
  (Error, VLit (Atom "badarg"%string), v).
Definition undef (v : Value) : Exception :=
  (Error, VLit (Atom "undef"%string), v).
Definition badfun (v : Value) : Exception := 
  (Error,VLit (Atom "badfun"%string), v).
Definition badarity (v : Value) : Exception := 
  (Error,VLit (Atom "badarity"%string), v).
Definition if_clause : Exception := 
  (Error, VLit (Atom "if_clause"%string), ErrorValue).
Definition fun_clause (v : Value) : Exception :=
    (Error, VLit (Atom "function_clause"%string), v).

Inductive degree_num : Set :=
| Num (n : nat)
| Any.

Definition max_degree (d1 d2 : degree_num) : degree_num :=
match d1, d2 with
| Num n1, Num n2 => Num (max n1 n2)
| Any, Num n => Num n
| Num n, Any => Num n
| Any, Any => Any
end.


Fixpoint degree (e : Expression) : degree_num :=
match e with
| EValues l => (Num (length l))
(* | ESingle e => single_degree e
end
with single_degree (e : SingleExpression) : degree_num :=
match e with *)
 | ENil => Num 1
 | ELit l => Num 1
 | EVar v => Num 1
 | EFunId f => Num 1
 | EFun vl e => Num 1
 | ECons hd tl => Num 1
 | ETuple l => Num 1
 | ECall m f l => Num 1
 | EPrimOp f l => Any
 | EApp exp l => Num 1
 | ECase e l => fold_right (fun '(a, b, c) r => max_degree r (degree c)) Any l
 | ELet l e1 e2 => degree e2
 | ESeq e1 e2 => degree e2
 | ELetRec l e => degree e
 | EMap l => Num 1
 | ETry e1 vl1 e2 vl2 e3 => max_degree (degree e2) (degree e3)
end.

Definition match_degree (d1 d2 : degree_num) : bool :=
match d1, d2 with
| Num n1, Num n2 => Nat.eqb n1 n2
| _, _ => true
end.

(* Compute match_degree (Num 4) (Num 5). *)

Definition which_degree (d1 d2 : degree_num) : option degree_num :=
match d1, d2 with
| Num n1, Num n2 => if Nat.eqb n1 n2 then Some (Num n1) else None
| Num n, Any => Some (Num n)
| Any, Num n => Some (Num n)
| Any, Any => Some Any
end.


(* Compute which_degree (Num 4) (Num 5).
Compute which_degree (Num 4) (Num 4).
Compute which_degree Any (Num 4).
Compute which_degree (Num 4) Any.
Compute which_degree Any Any. *)
(* 
Definition valid_single_expression (e : SingleExpression) : bool :=
match e with
 | ENil => true
 | ELit l => true
 | EVar v => true
 | EFunId f => true
 | EFun vl e => match_degree (degree e) (Num 1)
 | ECons hd tl => match_degree (degree hd) (Num 1) && match_degree (degree tl) (Num 1)
 | ETuple l => fold_right (fun 'x r => andb r (match_degree (degree x) (Num 1))) true l
 | ECall f l => fold_right (fun 'x r => andb r (match_degree (degree x) (Num 1))) true l
 | EPrimOp f l => fold_right (fun 'x r => andb r (match_degree (degree x) (Num 1))) true l
 | EApp exp l => match_degree (degree exp) (Num 1) && 
                 fold_right (fun 'x r => andb r (match_degree (degree x) (Num 1))) true l
 | ECase e l => let maxim := fold_right max_degree Any (map degree (map snd l)) in 
                  fold_right (fun '(x, y, z) r => andb r (match_degree (degree z) maxim)) true l
 | ELet l e1 e2 => match_degree (degree e1) (Num (length l))
 | ESeq e1 e2 => match_degree (degree e1) (Num 1)
 | ELetRec l e => true
 | EMap l => true
 | ETry e1 vl1 e2 vl2 e3 => match_degree (degree e2) (degree e3)
end. *)

(* Definition valid_expression (e : Expression) : bool :=
match e with
 | EValues el => false
 | ESingle e => valid_single_expression e
end. *)


Module ValueNotations.

Import ListNotations.

Notation "' s '" := (VLit (Atom s)) (at level 1).
Notation "` i" := (VLit (Integer i)) (at level 1).
Notation "{ }" := (VTuple []) (at level 1).
Notation "{ x , .. , z }" := (VTuple (cons x .. (cons z nil) .. )) (at level 50).

Notation "@[ @]" := (VNil) (at level 1).
Notation "@[ a | b @]" := (VCons a b) (at level 50).

Notation "x ==> x'" := (@pair Value Value x x') (at level 70).
Notation "#{ }" := (VMap []) (at level 1).
Notation "#{ x , .. , z }" := (VMap (cons x .. (cons z nil) .. )) (at level 50).

(* 
Check VMap [].
Check VMap [(' "asd", ' "asd")].
Check VTuple [].
Check VTuple [' "asd"].
Check VTuple [' "bsc"; ' "asd"].
Check { ' "asd", ' "bsc" }. 
*)


(* Notation "< x , y , .. , z >" := (cons x (cons y .. (cons z nil) .. )) (at level 50). *)
(* 
Check VTuple [].

Check VCons '"asd" VNil.

Check VMap [('"asd", '"asd"); ('"asd", '"asd"); ('"asd", VLit (Integer 7))].
Check VCons '"asd" (VCons '"asd" VNil).

Check VTuple ['"asd"; '"asd"; '"asd"].
 *)
End ValueNotations.




From CoreErlang.BigStep Require Export Helpers.

(** Environment and its functions *)
Import ListNotations.

Definition Environment : Type := list ((Var + FunctionIdentifier) * Value).

Fixpoint count_closures (env : Environment) : nat :=
match env with
| [] => 0
| (_, VClos _ _ _ _ _ _)::xs => S (count_closures xs)
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
Fixpoint insert_value (env : Environment) (key : (Var + FunctionIdentifier)) 
   (value : Value) : Environment :=
match env with
  | [] => [(key, value)]
  | (k,v)::xs => if var_funid_eqb k key then (key,value)::xs else (k,v)::(insert_value xs key value)
end.

(** Add additional bindings *)
(** We used here: when binding, variables must be unique *)
Fixpoint add_bindings (bindings : list (Var * Value)) (env : Environment) : Environment :=
match bindings with
| [] => env
| (v, e)::xs => add_bindings xs (insert_value env (inl v) e)
end.

(** Add bindings with two lists *)
Fixpoint append_vars_to_env (vl : list Var) (el : list Value) (d : Environment) 
   : Environment :=
match vl, el with
| [], [] => d
| v::vs, e::es => append_vars_to_env vs es (insert_value d (inl v) e)
| _, _ => []
end.


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
Fixpoint insert_function (id : nat) (v : FunctionIdentifier) (p : list Var) (b : Expression) 
   (l : list (nat * FunctionIdentifier * FunctionExpression)) 
    : list (nat * FunctionIdentifier * FunctionExpression) :=
match l with
| [] => [(id, v, (p, b))]
| (id', k, v0)::xs => if funid_eqb k v then (id', k, v0)::xs 
                                   else (id', k, v0)::(insert_function id v p b xs)
end.

(** Lists represented functions *)
Fixpoint list_functions (vl : list FunctionIdentifier) (paramss : list (list Var)) 
      (bodies : list Expression) (last_id : nat) 
      : list (nat * FunctionIdentifier * FunctionExpression) :=
match vl, paramss, bodies with
| [], [], [] => []
| v::vs, varl::ps, e::bs => insert_function last_id v varl e 
                                 (list_functions vs ps bs (S last_id))
| _, _, _ => []
end.

(** Add functions *)
Fixpoint append_funs_to_env_base (vl : list FunctionIdentifier) (paramss : list (list Var)) 
      (bodies : list Expression) (d : Environment) (def : Environment) 
      (deffuns : list (nat * FunctionIdentifier * FunctionExpression)) (last_id : nat) 
      : Environment :=
match vl, paramss, bodies with
| [], [], [] => d
| v::vs, varl::ps, e::bs => append_funs_to_env_base vs ps bs 
                              (insert_value d (inr v) 
                                           (VClos def deffuns last_id varl e (Some v))) 
                                           def deffuns (S last_id)
| _, _, _ => []
end.

Definition append_funs_to_env (l : list (FunctionIdentifier * ((list Var) * Expression))) (d : Environment) (last_id : nat) : Environment :=
append_funs_to_env_base (fst (split l)) (fst (split (snd (split l)))) (snd (split (snd (split l)))) d d 
                       (list_functions (fst (split l)) (fst (split (snd (split l)))) (snd (split (snd (split l)))) last_id)
                       last_id
.

(** Examples *)
Goal append_vars_to_env ["A"%string; "A"%string]
                           [(VEmptyMap); (VEmptyTuple)]
                           [(inl "A"%string, VEmptyMap)]
= [(inl "A"%string, VTuple [])].
Proof. reflexivity. Qed.
Goal append_funs_to_env [(("f1"%string,0), ([], ErrorExp)) ; 
                            (("f2"%string,0), ([], ErrorExp)) ;
                            (("f1"%string,0), ([], ErrorExp)) ]
                           [(inl "X"%string, ErrorValue)] 0
=
[(inl "X"%string, VLit (Atom "error"));
       (inr ("f1"%string, 0),
       VClos [(inl "X"%string, VLit (Atom "error"))]
         [(2, ("f1"%string, 0), ([], ELit (Atom "error")));
         (1, ("f2"%string, 0), ([], ELit (Atom "error")))] 2 [] (ELit (Atom "error")) (Some ("f1"%string, 0)));
       (inr ("f2"%string, 0),
       VClos [(inl "X"%string, VLit (Atom "error"))]
         [(2, ("f1"%string, 0), ([], ELit (Atom "error")));
         (1, ("f2"%string, 0), ([], ELit (Atom "error")))] 1 [] (ELit (Atom "error")) (Some ("f2"%string, 0)))].
Proof. reflexivity. Qed.
Goal insert_function 2 ("f1"%string, 0) [] ErrorExp (list_functions
                              [("f1"%string,0); ("f2"%string,0); ("f1"%string, 0)]
                              [[];[];[]]
                              [ErrorExp; ErrorExp; ErrorExp] 0)
= [(2, ("f1"%string, 0), ([], ELit (Atom "error")));
       (1, ("f2"%string, 0), ([], ELit (Atom "error")))].
Proof. reflexivity. Qed.

(** Environment construction from the extension and the reference *)
Fixpoint get_env_base (env def : Environment) 
   (ext defext : list (nat * FunctionIdentifier * FunctionExpression))
   : Environment :=
match ext with
| [] => env
| (id, f1, (pl, b))::xs => get_env_base (insert_value env (inr f1) (VClos def defext id pl b None)) def xs defext
end.

Definition get_env (env : Environment) 
   (ext : list (nat * FunctionIdentifier * FunctionExpression))
   : Environment :=
  get_env_base env env ext ext
.






From CoreErlang.BigStep Require Export ModuleAuxiliaries.

(** The Semantics of Core Erlang *)
Import ListNotations.

Reserved Notation "| env , modules , own_module , id , e , eff | -e> | id' , e' , eff' |" (at level 70).
(* Reserved Notation "| env , id , e , eff | -s> | id' , e' , eff' |" (at level 70). *)
Inductive eval_expr : Environment -> list ErlModule -> string -> nat -> Expression -> SideEffectList -> nat ->
    (ValueSequence + Exception) -> SideEffectList -> Prop :=
(* valuelist evaluation *)
| eval_values env modules own_module exps vals eff ids eff1 id eff' id':
  length exps = length vals ->
  length exps = length eff ->
  length exps = length ids ->
  (
    forall i, i < length exps ->
    |env, modules , own_module, nth_def ids id 0 i, nth i exps ErrorExp, nth_def eff eff1 [] i|
     -e> 
    |nth_def ids id 0 (S i), inl [nth i vals ErrorValue], nth_def eff eff1 [] (S i)|
  ) ->
  id' = last ids id ->
  eff' = last eff eff1
->
  |env, modules , own_module, id, EValues exps, eff1| -e> |id', inl vals, eff'|

(* valuelist exception *)

| eval_values_ex env modules own_module exps ex vals eff ids eff1 id eff' id' i:
  i < length exps ->
  length vals = i ->
  length eff = i ->
  length ids = i ->
  (
    forall j, j < i ->
    |env, modules , own_module, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j|
     -e> 
    |nth_def ids id 0 (S j), inl [nth j vals ErrorValue], nth_def eff eff1 [] (S j)|
  ) ->
  |env, modules , own_module,  last ids id, nth i exps ErrorExp, last eff eff1| -e> |id', inr ex, eff'|
->
  |env, modules , own_module, id, EValues exps, eff1| -e> |id', inr ex, eff'|

(* 
| eval_single env id e eff1 id' res eff':
  |env, id, e, eff1| -s> |id', res, eff'|
->
  |env, id, ESingle e, eff1| -e> |id', res, eff'|

where "| env , id , e , eff | -e> | id' , e' , eff' |" := (eval_expr env id e eff id' e' eff')
with eval_singleexpr : Environment -> nat -> SingleExpression -> SideEffectList -> nat ->
    (ValueSequence + Exception) -> SideEffectList -> Prop := *)

| eval_nil (env : Environment) (modules : list ErlModule) (own_module : string)  (eff : SideEffectList) (id : nat):
  |env, modules , own_module, id, ENil, eff| -e> |id, inl [VNil], eff|

(* literal evaluation rule *)
| eval_lit (env : Environment) (modules : list ErlModule) (own_module : string) (l : Literal) (eff : SideEffectList) (id : nat):
  |env, modules , own_module, id, ELit l, eff| -e> |id, inl [VLit l], eff|

(* variable evaluation rule *)
| eval_var (env : Environment) (modules : list ErlModule) (own_module : string) (s: Var) (eff : SideEffectList) (id : nat) 
      (res : ValueSequence) :
  get_value env (inl s) = Some res
->
  |env, modules , own_module, id, EVar s, eff| -e> |id, inl res, eff|

(* Function Identifier evaluation rule *)
| eval_funid (env : Environment) (modules : list ErlModule) (own_module : string) (fid : FunctionIdentifier) (eff : SideEffectList) 
    (res : ValueSequence) (id : nat):
  get_value env (inr fid) = Some res
->
  |env, modules , own_module, id, EFunId fid, eff| -e> |id, inl res, eff|

| eval_funid_module (env : Environment) (modules : list ErlModule) (own_module : string) (fid : FunctionIdentifier) (eff : SideEffectList)
     (func : TopLevelFunction) (body_func : Expression) (varl_func : list Var) (id : nat):
  get_value env (inr fid) = None
->
  get_own_modfunc own_module (fst fid) (snd fid) (  modules ++ stdlib) = Some func
->
  varl_func = (varl func)
->
  body_func = (body func)
->
  |env, modules , own_module, id, EFunId fid, eff| -e> |id, inl [VClos env [] id (varl_func) (body_func) None], eff|

(* Function evaluation *)
| eval_fun (env : Environment) (modules : list ErlModule) (own_module : string) (vl : list Var) (e : Expression) (eff : SideEffectList) (id : nat):
  |env, modules , own_module, id, EFun vl e, eff| -e> |S id, inl [VClos env [] id vl e None], eff|

(* tuple evaluation rule *)
| eval_tuple (env : Environment) (modules : list ErlModule) (own_module : string) (exps : list Expression) (vals : list Value) 
     (eff1 eff2 : SideEffectList) (eff : list SideEffectList) (ids : list nat) (id id' : nat) :
  length exps = length vals ->
  length exps = length eff ->
  length exps = length ids ->
  (
    forall i, i < length exps ->
      |env, modules , own_module, nth_def ids id 0 i, nth i exps ErrorExp, nth_def eff eff1 [] i| 
     -e> 
      |nth_def ids id 0 (S i), inl [nth i vals ErrorValue], nth_def eff eff1 [] (S i)|
  ) ->
  eff2 = last eff eff1 ->
  id' = last ids id (* if length = 0, then last id = first id *)
->
  |env, modules , own_module, id, ETuple exps, eff1| -e> |id' , inl [VTuple vals], eff2|

(* list evaluation rule *)
| eval_cons (env : Environment) (modules : list ErlModule) (own_module : string) (hd tl: Expression) (hdv tlv : Value) 
     (eff1 eff2 eff3 : SideEffectList) (id id' id'' : nat) :
  |env, modules , own_module, id, tl, eff1| -e> |id', inl [tlv], eff2| ->
  |env, modules , own_module, id', hd, eff2| -e> | id'', inl [hdv], eff3|
->
  |env, modules , own_module, id, ECons hd tl, eff1| -e> |id'', inl [VCons hdv tlv], eff3|

(* case evaluation rules *)
| eval_case (env : Environment) (modules : list ErlModule) (own_module : string) (guard exp: Expression) (e : Expression) (vals : ValueSequence) (res : ValueSequence + Exception) (l : list (list Pattern * Expression * Expression)) (bindings: list (Var * Value)) (i : nat) (eff1 eff2 eff3 : SideEffectList) (id id' id'' : nat) :
  |env, modules , own_module, id, e, eff1| -e> |id', inl vals, eff2| ->
  i < length l ->
  match_clause vals l i = Some (guard, exp, bindings) ->
  (forall j : nat, j < i -> 

    (** THESE GUARDS MUST BE SIDE-EFFECT FREE ACCORDING TO 1.0.3 LANGUAGE SPECIFICATION *)
    (forall gg ee bb, match_clause vals l j = Some (gg, ee, bb) -> 
      (|add_bindings bb env, modules , own_module, id', gg, eff2| -e> |id', inl [ffalse], eff2| ))

  ) ->
  |add_bindings bindings env, modules , own_module, id', guard, eff2| -e> |id', inl [ttrue], eff2| -> 
  |add_bindings bindings env, modules , own_module, id', exp, eff2| -e> |id'', res, eff3|
->
  |env, modules , own_module, id, ECase e l, eff1| -e> |id'', res, eff3|


(* call evaluation rule *)
| eval_call (env : Environment) (modules : list ErlModule) (own_module : string) (res : ValueSequence + Exception) (params : list Expression) 
     (vals : list Value) (mexp : Expression) (fexp: Expression) (mname fname : string) (eff1 eff2 eff3 eff4 : SideEffectList) (eff : list SideEffectList) 
     (ids : list nat) (id id' id'' id''' : nat) :
  length params = length vals ->
  length params = length eff ->
  length params = length ids ->
  |env, modules , own_module, id, mexp, eff1| -e> |id', inl [VLit (Atom mname)], eff2| -> 
  |env, modules , own_module, id', fexp, eff2| -e> |id'', inl [VLit (Atom fname)], eff3| -> 
  (
    forall i, i < length params ->
      |env, modules , own_module, nth_def ids id'' 0 i, nth i params ErrorExp, nth_def eff eff3 [] i| 
     -e>
      |nth_def ids id'' 0 (S i), inl [nth i vals ErrorValue], nth_def eff eff3 [] (S i)|
  ) ->
  get_modfunc mname fname (length vals) (modules ++ stdlib) = None ->
  eval mname fname vals (last eff eff3) = (res, eff4) ->
  id''' = last ids id''
->
  |env, modules , own_module, id, ECall mexp fexp params, eff1| -e> |id''', res, eff4|

| eval_call_module (env : Environment) (modules : list ErlModule) (own_module : string) (res : ValueSequence + Exception) (params : list Expression) 
     (vals : list Value) (mexp : Expression) (fexp: Expression) (mname fname : string) (func : TopLevelFunction) (eff1 eff2 eff3 eff4 : SideEffectList) (eff : list SideEffectList) 
     (ids : list nat) (id id' id'' id''' : nat) :
  length params = length vals ->
  length params = length eff ->
  length params = length ids ->
  |env, modules , own_module, id, mexp, eff1| -e> |id', inl [VLit (Atom mname)], eff2| -> 
  |env, modules , own_module, id', fexp, eff2| -e> |id'', inl [VLit (Atom fname)], eff3| -> 
  (
    forall i, i < length params ->
      |env, modules , own_module, nth_def ids id'' 0 i, nth i params ErrorExp, nth_def eff eff3 [] i| 
     -e>
      |nth_def ids id'' 0 (S i), inl [nth i vals ErrorValue], nth_def eff eff3 [] (S i)|
  ) ->
  get_modfunc mname fname (length vals) (modules ++ stdlib) = Some func
    ->
  | append_vars_to_env (varl func) vals [], modules , mname,
   last ids id'',
   (body func), 
   last eff eff3|
  -e>
   |id''', res, eff4|

  ->
  |env, modules , own_module, id, ECall mexp fexp params, eff1| -e> |id''', res, eff4|



(* primop evaluation rule *)
| eval_primop (env : Environment) (modules : list ErlModule) (own_module : string) (res : ValueSequence + Exception) (params : list Expression) 
     (vals : list Value) (fname: string) (eff1 eff2: SideEffectList) (eff : list SideEffectList) 
     (ids : list nat) (id id' : nat) :
  length params = length vals ->
  length params = length eff ->
  length params = length ids ->
  (
    forall i, i < length params ->
      |env, modules , own_module, nth_def ids id 0 i, nth i params ErrorExp, nth_def eff eff1 [] i| 
     -e>
      |nth_def ids id 0 (S i), inl [nth i vals ErrorValue], nth_def eff eff1 [] (S i)|
  ) ->
  primop_eval fname vals (last eff eff1) = (res, eff2) ->
  id' = last ids id
->
  |env, modules , own_module, id, EPrimOp fname params, eff1| -e> |id', res, eff2|

(* apply functions*)
| eval_app (params : list Expression) (vals : list Value) (env : Environment) (modules : list ErlModule) (own_module : string) 
     (exp : Expression) (body : Expression) (res : ValueSequence + Exception) (var_list : list Var) 
     (ref : Environment) (ext : list (nat * FunctionIdentifier * FunctionExpression)) (n : nat)
     (eff1 eff2 eff3 : SideEffectList) (eff : list SideEffectList) (ids : list nat) (id id' id'' : nat) (f : option FunctionIdentifier) :
  length params = length vals ->
  |env, modules , own_module, id, exp, eff1| -e> |id', inl [VClos ref ext n var_list body f], eff2| ->
  length var_list = length vals
  ->
  length params = length eff ->
  length params = length ids ->
  (
    forall i, i < length params ->
      |env, modules , own_module, nth_def ids id' 0 i, nth i params ErrorExp, nth_def eff eff2 [] i|
     -e>
      |nth_def ids id' 0 (S i), inl [nth i vals ErrorValue], nth_def eff eff2 [] (S i)|
  )
  ->
  |append_vars_to_env var_list vals (get_env ref ext), 
  modules , own_module,
   last ids id',
   body, 
   last eff eff2|
  -e>
   |id'', res, eff3|
->
  |env, modules , own_module, id, EApp exp params, eff1| -e> |id'', res, eff3|

(* let evaluation rule *)
| eval_let (env : Environment) (modules : list ErlModule) (own_module : string) (l: list Var) (vals : ValueSequence) (e1 e2 : Expression) (res : ValueSequence + Exception) (eff1 eff' eff'' : SideEffectList) (id id' id'' : nat) :
  |env, modules , own_module, id, e1, eff1| -e> |id', inl vals, eff'| ->
  length l = length vals ->
  |append_vars_to_env l vals env, modules , own_module, id', e2, eff'| -e> |id'', res, eff''|
->
  |env, modules , own_module, id, ELet l e1 e2, eff1| -e> |id'', res, eff''|

(* evaluation of sequence (do expressions) *)
| eval_seq (env : Environment) (modules : list ErlModule) (own_module : string) (e1 e2: Expression) (v1 : Value) (v2 : ValueSequence + Exception)
     (eff1 eff2 eff3 : SideEffectList) (id id' id'' : nat) :
   (* THE FIRST RESULT SHOULD BE A SINGLE VALUE *)
  |env, modules , own_module, id, e1, eff1| -e> |id', inl [v1], eff2| ->
  |env, modules , own_module, id', e2, eff2| -e> |id'', v2, eff3|
->
  | env, modules , own_module, id, ESeq e1 e2, eff1 | -e> |id'', v2, eff3|

(* Letrec evaluation rule *)
| eval_letrec (env : Environment) (modules : list ErlModule) (own_module : string) (e : Expression)  (l : list (FunctionIdentifier * ((list Var) * Expression))) (res : ValueSequence + Exception) (eff1 eff2 : SideEffectList) (id id' : nat) :
  (
     |append_funs_to_env l env id, modules , own_module, id + length l, e, eff1| -e> | id', res, eff2|
  )
->
  |env, modules , own_module, id, ELetRec l e, eff1| -e> | id', res, eff2|



(* map evaluation rule *)
| eval_map (l: list (Expression * Expression)) (vvals kvals kvals' vvals' : list Value) ( lv : list (Value * Value)) (env : Environment) (modules : list ErlModule) (own_module : string) (eff1 eff2 : SideEffectList) (eff : list SideEffectList) (ids : list nat) (id id' : nat) :
  length l = length vvals ->
  length l = length kvals ->
  (length l) * 2 = length eff ->
  (length l) * 2 = length ids ->
  let exps := make_map_exps l in
  let vals := make_map_vals kvals vvals in
  (
    forall i : nat, i < length exps  ->
    |env, modules , own_module, nth_def ids id 0 i, nth i exps ErrorExp, nth_def eff eff1 [] i| 
     -e>
    | nth_def ids id 0 (S i), inl [nth i vals ErrorValue], nth_def eff eff1 [] (S i)|
  ) ->
  make_value_map kvals vvals = (kvals', vvals') ->
  combine kvals' vvals' = lv ->
  eff2 = last eff eff1 ->
  id' = last ids id
->
  |env, modules , own_module, id, EMap l, eff1| -e> |id', inl [VMap lv], eff2|


  (* EXCEPTIONS *)
(* list tail exception *)
| eval_cons_tl_ex (env : Environment) (modules : list ErlModule) (own_module : string) (hd tl : Expression) (ex : Exception) 
      (eff1 eff2 : SideEffectList) (id id' : nat) :
  |env, modules , own_module, id, tl, eff1| -e> |id', inr ex, eff2|
->
  |env, modules , own_module, id, ECons hd tl, eff1| -e> |id', inr ex, eff2|

(* list head exception *)
| eval_cons_hd_ex (env : Environment) (modules : list ErlModule) (own_module : string) (hd tl : Expression) (ex : Exception) (vtl : Value) 
     (eff1 eff2 eff3 : SideEffectList) (id id' id'' : nat) :
  |env, modules , own_module, id, tl, eff1| -e> |id', inl [vtl], eff2| -> 
  |env, modules , own_module, id', hd, eff2| -e> |id'', inr ex, eff3|
->
  |env, modules , own_module, id, ECons hd tl, eff1| -e> |id'', inr ex, eff3|


(* tuple exception *)
| eval_tuple_ex (env : Environment) (modules : list ErlModule) (own_module : string) (i : nat) (exps : list Expression) (vals : list Value) 
     (ex : Exception) (eff1 eff2 : SideEffectList) (eff : list SideEffectList) 
     (id id' : nat) (ids : list nat) :
  i < length exps ->
  length vals = i ->
  length eff = i ->
  length ids = i ->
  (forall j, j < i ->
    |env, modules , own_module, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j|
   -e>
    |nth_def ids id 0 (S j), inl [nth j vals ErrorValue], nth_def eff eff1 [] (S j)|) ->
  |env, modules , own_module, last ids id, nth i exps ErrorExp, last eff eff1| -e> |id', inr ex, eff2|
->
  |env, modules , own_module, id, ETuple exps, eff1| -e> |id', inr ex, eff2|


(* try 2x *)
| eval_try (env : Environment) (modules : list ErlModule) (own_module : string) (vl1 vl2 : list Var) (e1 e2 e3 : Expression) (res : ValueSequence + Exception) (vals : ValueSequence) (eff1 eff2 eff3 : SideEffectList) (id id' id'' : nat) :
  |env, modules , own_module, id, e1, eff1| -e> | id', inl vals, eff2| ->
  length vl1 = length vals ->
  |append_vars_to_env vl1 vals env, modules , own_module, id', e2, eff2 | -e> | id'', res, eff3|
->
  |env, modules , own_module, id, ETry e1 vl1 e2 vl2 e3, eff1| -e> | id'', res, eff3|


(* catch *)
| eval_catch (env : Environment) (modules : list ErlModule) (own_module : string) (vl1 vl2 : list Var) (e1 e2 e3 : Expression) (res : ValueSequence + Exception) (eff1 eff2 eff3 : SideEffectList) (id id' id'' : nat) (ex : Exception) :
  |env, modules , own_module, id, e1, eff1| -e> |id', inr ex, eff2| ->
  |append_try_vars_to_env vl2 [exclass_to_value (fst (fst ex)); snd (fst ex); snd ex] env, modules , own_module, id', e3, eff2|
 -e> 
  |id'', res, eff3|
->
  |env, modules , own_module, id, ETry e1 vl1 e2 vl2 e3, eff1| -e> |id'', res, eff3|


(* case 2x *)
(** Pattern matching exception *)
| eval_case_pat_ex (env : Environment) (modules : list ErlModule) (own_module : string) (e : Expression) (ex : Exception) (l : list (list Pattern * Expression * Expression)) (eff1 eff2 : SideEffectList) (id id' : nat):
  |env, modules , own_module, id, e, eff1| -e> |id', inr ex, eff2|
->
  |env, modules , own_module, id, ECase e l, eff1| -e> |id', inr ex, eff2|

(** No matching clause *)
| eval_case_clause_ex (env : Environment) (modules : list ErlModule) (own_module : string) (e : Expression) (l : list (list Pattern * Expression * Expression)) (vals : ValueSequence) (eff1 eff2 : SideEffectList) (id id' : nat):
  |env, modules , own_module, id, e, eff1| -e> |id', inl vals, eff2| ->
  (forall j : nat, j < length l -> 

    (** THESE GUARDS MUST BE SIDE-EFFECT FREE ACCORDING TO 1.0.3 LANGUAGE SPECIFICATION *)
    (forall gg ee bb, match_clause vals l j = Some (gg, ee, bb) -> 
      ((|add_bindings bb env, modules , own_module, id', gg, eff2| -e> | id', inl [ffalse], eff2| ))

    )

  )
->
  |env, modules , own_module, id, ECase e l, eff1| -e> | id', inr (if_clause), eff2|
(** ith guard exception -> guards cannot result in exception, i.e. this rule is not needed *)


(* call 1x *)
| eval_call_ex (env : Environment) (modules : list ErlModule) (own_module : string) (i : nat) (mexp: Expression) (fexp : Expression) (v v': Value)  (params : list Expression) 
     (vals : list Value) (ex : Exception) (eff1 eff2 eff3 eff4 : SideEffectList) 
     (eff : list SideEffectList) (id id' id'' id''' : nat) (ids : list nat) :
  i < length params ->
  length vals = i ->
  length eff = i ->
  length ids = i ->
  |env, modules , own_module, id, mexp, eff1| -e> |id', inl [v], eff2| -> 
  |env, modules , own_module, id', fexp, eff2| -e> |id'', inl [v'], eff3| -> 
  (forall j, j < i ->
    |env, modules , own_module, nth_def ids id'' 0 j, nth j params ErrorExp, nth_def eff eff3 [] j|
   -e>
    |nth_def ids id'' 0 (S j), inl [nth j vals ErrorValue], nth_def eff eff3 [] (S j)|
  ) ->
  |env, modules , own_module, last ids id'', nth i params ErrorExp, last eff eff3| -e> |id''', inr ex, eff4|

->
  |env, modules , own_module, id, ECall mexp fexp params, eff1| -e> |id''', inr ex, eff4|

(* Call: exception in module evaluation *)
| eval_call_mexp_ex (env : Environment) (modules : list ErlModule) (own_module : string) (mexp : Expression) (fexp : Expression) (params : list Expression)
    (ex : Exception) (eff1 eff2 : SideEffectList) (id id' : nat):
  |env, modules , own_module, id, mexp, eff1| -e> |id', inr ex, eff2|
  ->
  |env, modules , own_module, id, ECall mexp fexp params, eff1| -e> |id', inr ex, eff2|

(* Call: exception in (module's) function evaluation *)
| eval_call_fexp_ex (env : Environment) (modules : list ErlModule) (own_module : string) (mexp : Expression) (fexp : Expression) (v: Value) (params : list Expression)
    (ex : Exception) (eff1 eff2 eff3 : SideEffectList) (id id' id'' : nat):
  |env, modules , own_module, id, mexp, eff1|  -e> |id', inl [v], eff2| -> 
  |env, modules , own_module, id', fexp, eff2| -e> |id'', inr ex, eff3|
->
|env, modules , own_module, id, ECall mexp fexp params, eff1| -e> |id'', inr ex, eff3|

(* Call: evaluated module exception is not atom *)
| eval_call_mexp_badarg_ex  (env : Environment) (modules : list ErlModule) (own_module : string) (mexp : Expression) (fexp : Expression) (v v': Value) (params : list Expression)
  (vals : list Value) ( eff1 eff2 eff3 eff4 : SideEffectList) (eff : list SideEffectList) (id id' id'' id''' : nat) (ids : list nat) :
    length params = length vals ->
    length params = length eff ->
    length params = length ids ->
    |env, modules , own_module, id, mexp, eff1| -e> |id', inl [v], eff2| -> 
    |env,  modules , own_module, id', fexp, eff2| -e> |id'', inl [v'], eff3| -> 
    (
      forall i, i < length params ->
        |env,  modules , own_module, nth_def ids id'' 0 i, nth i params ErrorExp, nth_def eff eff3 [] i| 
       -e>
        |nth_def ids id'' 0 (S i), inl [nth i vals ErrorValue], nth_def eff eff3 [] (S i)|
    ) ->
    (forall (mname : string) ,
    v <> VLit (Atom mname)) ->
    eff4 = last eff eff3 ->
    id''' = last ids id'' ->
  |env, modules , own_module, id, ECall mexp fexp params, eff1| -e> |id''', (inr (badarg v)), eff4|

(* Call: evaluated function exception is not atom *)
| eval_call_fexp_badarg_ex (env : Environment) (modules : list ErlModule) (own_module : string) (mexp : Expression) (fexp : Expression) (mname : string) (v': Value) (params : list Expression)
(vals : list Value) ( eff1 eff2 eff3 eff4 : SideEffectList) (eff : list SideEffectList) (id id' id'' id''' : nat) (ids : list nat) :
  length params = length vals ->
  length params = length eff ->
  length params = length ids ->
  |env, modules , own_module, id, mexp, eff1| -e> |id', inl [VLit (Atom mname)], eff2| -> 
  |env, modules , own_module, id', fexp, eff2| -e> |id'', inl [v'], eff3| -> 
  (
    forall i, i < length params ->
      |env, modules , own_module, nth_def ids id'' 0 i, nth i params ErrorExp, nth_def eff eff3 [] i| 
     -e>
      |nth_def ids id'' 0 (S i), inl [nth i vals ErrorValue], nth_def eff eff3 [] (S i)|
  ) ->
  (forall (fname : string) ,
  v' <> VLit (Atom fname)) ->
  eff4 = last eff eff3 ->
  id''' = last ids id'' ->
|env, modules , own_module, id, ECall mexp fexp params, eff1| -e> |id''', (inr (badarg v')), eff4|





(* primop 1x *)
| eval_primop_ex (env : Environment) (modules : list ErlModule) (own_module : string) (i : nat) (fname : string) (params : list Expression) 
     (vals : list Value) (ex : Exception) (eff1 eff2 : SideEffectList) 
     (eff : list SideEffectList) (id id' : nat) (ids : list nat) :
  i < length params ->
  length vals = i ->
  length eff = i ->
  length ids = i ->
  (forall j, j < i ->
    |env, modules , own_module, nth_def ids id 0 j, nth j params ErrorExp, nth_def eff eff1 [] j|
   -e>
    |nth_def ids id 0 (S j), inl [nth j vals ErrorValue], nth_def eff eff1 [] (S j)|
  ) ->
  |env, modules , own_module, last ids id, nth i params ErrorExp, last eff eff1| -e> |id', inr ex, eff2|

->
  |env, modules , own_module, id, EPrimOp fname params, eff1| -e> |id', inr ex, eff2|


(* apply 4x *)
(** According to ref. implementation, here it is not needed to check the arg number *)

(** if name expression evaluates to exception *)
| eval_app_closure_ex (params : list Expression) (env : Environment) (modules : list ErlModule) (own_module : string) (exp : Expression)  
     (ex : Exception) (eff1 eff2 : SideEffectList) (id id' : nat):
  |env, modules , own_module, id, exp, eff1| -e> |id', inr ex, eff2|
->
  |env, modules , own_module, id, EApp exp params, eff1| -e> |id', inr ex, eff2|

(** name expression and some parameters evaluate to values *)
| eval_app_param_ex (params : list Expression) (vals : list Value) (env : Environment) (modules : list ErlModule) (own_module : string) 
     (exp : Expression) (ex : Exception) (i : nat) (v : Value) (eff1 eff2 eff3 : SideEffectList) 
     (eff : list SideEffectList) (ids : list nat) (id id' id'' : nat) :
  i < length params ->
  length vals = i ->
  length eff = i ->
  length ids = i
  ->
  |env, modules , own_module, id, exp, eff1| -e> |id', inl [v], eff2| ->
  (forall j, j < i -> 
    |env, modules , own_module, nth_def ids id' 0 j, nth j params ErrorExp, nth_def eff eff2 [] j|
   -e>
    |nth_def ids id' 0 (S j), inl [nth j vals ErrorValue], nth_def eff eff2 [] (S j)|
  ) ->
  |env, modules , own_module, last ids id', nth i params ErrorExp, last eff eff2| -e> |id'', inr ex, eff3|
->
  |env, modules , own_module, id, EApp exp params, eff1| -e> |id'', inr ex, eff3|

(** Then we check if the name expression evaluates to a closure *)
| eval_app_badfun_ex (params : list Expression) (vals: list Value) (env : Environment) (modules : list ErlModule) (own_module : string) (v : Value) 
     (exp : Expression) (eff1 eff2 eff3 : SideEffectList) (eff : list SideEffectList) 
     (ids : list nat) (id id' id'' : nat) (f : option FunctionIdentifier) :
  length params = length vals ->
  length params = length eff ->
  length params = length ids ->
  |env, modules , own_module, id, exp, eff1| -e> |id', inl [v], eff2| ->
  (
    forall j : nat, j < length params ->
    (
      |env, modules , own_module, nth_def ids id' 0 j, nth j params ErrorExp, nth_def eff eff2 [] j|
     -e>
      |nth_def ids id' 0 (S j), inl [nth j vals ErrorValue], nth_def eff eff2 [] (S j)|
    )
  ) ->
  (forall ref ext var_list body n, 
     v <> VClos ref ext n var_list body f) ->
  eff3 = last eff eff2 ->
  id'' = last ids id'
->
  |env, modules , own_module, id, EApp exp params, eff1| -e> |id'', inr (badfun v), eff3|

(** too few or too many arguments are given *)
| eval_app_badarity_ex (params : list Expression) (vals : list Value) (env : Environment) (modules : list ErlModule) (own_module : string) 
     (exp : Expression) (body : Expression) (var_list : list Var) (ref : Environment) 
     (ext : list (nat * FunctionIdentifier * FunctionExpression)) (eff1 eff2 eff3 : SideEffectList) 
     (eff : list SideEffectList) (n : nat) (ids : list nat) (id id' id'' : nat) (f : option FunctionIdentifier) :
  length params = length vals ->
  length params = length eff ->
  length params = length ids ->
  |env, modules , own_module, id, exp, eff1| -e> |id', inl [VClos ref ext n var_list body f], eff2| ->
  (
    forall j : nat, j < length params ->
    (
      |env, modules , own_module, nth_def ids id' 0 j, nth j params ErrorExp, nth_def eff eff2 [] j|
     -e>
      |nth_def ids id' 0 (S j), inl [nth j vals ErrorValue], nth_def eff eff2 [] (S j)|
    )
  ) ->
  length var_list <> length vals ->
  eff3 = last eff eff2 ->
  id'' = last ids id'
->
  |env, modules , own_module, id, EApp exp params, eff1| 
  -e> 
  |id'', inr (badarity (VClos ref ext n var_list body f)), eff3|

(* let 1x *)
| eval_let_ex (env : Environment) (modules : list ErlModule) (own_module : string) (vl: list Var) (e1 e2 : Expression) (ex : Exception) (eff1 eff2 : SideEffectList) (id id' : nat) :
  |env, modules , own_module, id, e1, eff1| -e> |id', inr ex, eff2|
->
  |env, modules , own_module, id, ELet vl e1 e2, eff1| -e> | id', inr ex, eff2|

(* sequence 1x *)
| eval_seq_ex (env : Environment) (modules : list ErlModule) (own_module : string) (e1 e2: Expression) (ex : Exception)
     (eff1 eff2 : SideEffectList) (id id' : nat) :
  |env, modules , own_module, id, e1, eff1| -e> |id', inr ex, eff2|
->
  | env, modules , own_module, id, ESeq e1 e2, eff1 | -e> |id', inr ex, eff2|


(* map 2x *)
(** Exception in key list *)
| eval_map_ex (l: list (Expression * Expression)) (vvals kvals : list Value) (env : Environment) (modules : list ErlModule) (own_module : string) (i : nat) (ex : Exception) (eff1 eff2 : SideEffectList) (eff : list SideEffectList) (ids : list nat) (id id' : nat):
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
    |env, modules , own_module, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j| -e> | nth_def ids id 0 (S j), inl [nth j vals ErrorValue], nth_def eff eff1 [] (S j)|
  )
  ->
  |env, modules , own_module, last ids id, nth i exps ErrorExp, last eff eff1| -e> | id', inr ex, eff2|
->
  |env, modules , own_module, id, EMap l, eff1| -e> | id', inr ex, eff2|

where "| env , modules , own_module , id , e , eff | -e> | id' , e' , eff' |" := (eval_expr env modules own_module id e eff id' e' eff')
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
| eval_expr_intro e v : (exists n eff, | [], [], "", 0, e, [] | -e> |n, v, eff|) -> e --e-> v
where "e --e-> v" := (eval_to_result e v).

Definition valid_result (res : ValueSequence + Exception) :=
match res with
| inl vals => length vals =? 1
| _ => true
end.
*)

(* FRAMESTACK
From Coq Require ZArith.BinInt.
From Coq Require Strings.String.
From Coq Require Export FunctionalExtensionality.

(*Require Import Utf8.*)

Export ZArith.BinInt.
Export Strings.String.
Export Lists.List.
Require Export Coq.Structures.OrderedType.
Require Export Coq.micromega.Lia
               Coq.Lists.List
               Coq.Arith.PeanoNat.

From CoreErlang Require Export Basics.

Import ListNotations.

Definition PID : Set := nat.

Inductive Lit : Set :=
| Atom (s: string)
| Integer (x : Z)
(* | Float (q : R) *).

Coercion Atom : string >-> Lit.
Coercion Integer : Z >-> Lit.

Inductive Pat : Set :=
| PVar
(* | PPid (p : PID) *)
| PLit (l : Lit)
| PCons  (hd tl : Pat)
| PTuple (l : list Pat)
| PMap (l : list (Pat * Pat))
| PNil.

Definition FunId : Set := nat * nat.
Definition Var : Set := nat.

Inductive Exp : Set :=
| VVal (e : Val)
| EExp (e : NonVal)

with Val: Set := 
| VNil
| VLit    (l : Lit)
| VPid    (p : PID)
| VCons   (hd tl : Val)
| VTuple  (l : list Val)
| VMap    (l : list (Val * Val))
(* | VValues (el : list ValExp) *)
(* VValues will need to be seperate to avoid VValues in VValues. *)
| VVar    (n : Var)
| VFunId  (n : FunId)
(* Function normalforms: closures. These values contain the body, formal parameter count   *)
| VClos   (ext : list (nat * nat * Exp))
          (id : nat) (* Function reference number *)
          (params : nat) (* Parameter count *)
          (e : Exp)
(* Scoping vl + length ext *)

with NonVal : Set :=
| EFun    (vl : nat) (e : Exp) (* One step reduction *)
| EValues (el : list Exp)
| ECons   (hd tl : Exp)
| ETuple  (l : list Exp)
| EMap    (l : list (Exp * Exp))
| ECall   (m f : Exp) (l : list Exp)
| EPrimOp (f : string)    (l : list Exp)
| EApp    (exp: Exp)     (l : list Exp)
| ECase   (e : Exp) (l : list ((list Pat) * Exp * Exp))
| ELet    (l : nat) (e1 e2 : Exp)
| ESeq    (e1 e2 : Exp)

| ELetRec (l : list (nat * Exp)) (e : Exp) (* One step reduction *)
| ETry    (e1 : Exp) (vl1 : nat) (e2 : Exp) (vl2 : nat) (e3 : Exp)

(* Concurrency *)
(* | EReceive (l : list (list Pat * Exp * Exp)) (* Core Erlang syntax allows list Pat
                                           here; however, its semantics is
                                           undefined *) *)
(* receive is a syntax sugar since OTP 24 *)
.

Coercion EExp : NonVal >-> Exp.
Notation "˝ v" := (VVal v) (at level 11).
Notation "° n" := (EExp n) (at level 11).

Definition inf :=
  ELetRec
    [(0, °EApp (˝VFunId (0, 0)) [])]
    (EApp (˝VFunId (0, 0)) []).

(** Shorthands: *)
Definition VEmptyMap : Val := VMap [].
Definition VEmptyTuple : Val := VTuple [].
Definition EEmptyMap : Exp := EMap [].
Definition EEmptyTuple : Exp := ETuple [].

Definition ErrorVal : Val := (VLit (Atom "error"%string)).
(* Definition ErrorExp2 : Expression := (ELit (Atom "error"%string)). *)
Definition ErrorExp : Val := (VLit (Atom "error"%string)).
Definition ErrorPat : Pat := PLit(Atom "error"%string).
Notation "'ttrue'"        := (VLit "true"%string).
Notation "'ffalse'"       := (VLit "false"%string).
Notation "'ok'"           := (VLit "ok"%string).
Notation "'link'"         := (VLit "link"%string).
Notation "'spawn'"        := (VLit "spawn"%string).
Notation "'spawn_link'"   := (VLit "spawn_link"%string).
Notation "'unlink'"       := (VLit "unlink"%string).
Notation "'exit'"         := (VLit "exit"%string).
Notation "'send'"         := (VLit "!"%string).
Notation "'normal'"       := (VLit "normal"%string).
Notation "'kill'"         := (VLit "kill"%string).
Notation "'killed'"       := (VLit "killed"%string).
Notation "'EXIT'"         := (VLit "EXIT"%string).
Notation "'self'"         := (VLit "self"%string).
Notation "'ok'"           := (VLit "ok"%string).
Notation "'process_flag'" := (VLit "process_flag"%string).
Notation "'trap_exit'"    := (VLit "trap_exit"%string).
Notation "'erlang'"       := (VLit "erlang"%string).
Notation "'infinity'"     := (VLit "infinity"%string).


(** Exception representation *)
Inductive ExcClass : Set :=
| Error | Throw | Exit.

(** Exception class to value converter *)
Definition exclass_to_value (ex : ExcClass) : Val :=
match ex with
| Error => VLit (Atom "error"%string)
| Throw => VLit (Atom "throw"%string)
| Exit => VLit (Atom "exit"%string)
end.

(** Exception class, 1st Value : cause, 2nd Value : further details *)
Definition Exception : Set := ExcClass * Val * Val.

Definition badarith (v : Val) : Exception :=
  (Error, VLit (Atom "badarith"%string), v).
Definition badarg (v : Val) : Exception :=
  (Error, VLit (Atom "badarg"%string), v).
Definition undef (v : Val) : Exception :=
  (Error, VLit (Atom "undef"%string), v).
Definition badfun (v : Val) : Exception := 
  (Error,VLit (Atom "badfun"%string), v).
Definition badarity (v : Val) : Exception := 
  (Error,VLit (Atom "badarity"%string), v).
Definition if_clause : Exception := 
  (Error, VLit (Atom "if_clause"%string), ErrorVal).
Definition timeout_value v : Exception :=
  (Error, VLit (Atom "timeout_value"), v).

Definition ValSeq := list Val.

Inductive Redex : Type :=
| RExp (e : Exp)
| RValSeq (vs : ValSeq)
| RExc (e : Exception)
| RBox.

Definition convert_to_closlist (l : list (nat * nat * Exp)) : (list Val) :=
  map (fun '(id,vc,e) => (VClos l id vc e)) l.




From CoreErlang Require Export ScopingLemmas Maps Matching.

Import ListNotations.

(** FrameStack *)
(** Based on Pitts' work: https://www.cl.cam.ac.uk/~amp12/papers/opespe/opespe-lncs.pdf *)

Inductive FrameIdent :=
| IValues
| ITuple
| IMap
| ICall (m f : Val)
| IPrimOp (f : string)
| IApp (v : Val).

Inductive Frame : Set :=
| FCons1 (hd : Exp) (* [e1 | □] *)
| FCons2 (tl : Val) (* [□ | v2] *)
| FParams (ident : FrameIdent) (vl : list Val) (el : list Exp) (* (v₁, ..., vₖ, □, eₖ₊₂, ..., eₙ) *)
| FApp1 (l : list Exp)  (* apply □(e₁, ..., eₙ) *)
| FCallMod (f : Exp) (l : list Exp) (* call □:f(e₁, ..., eₙ) *)
| FCallFun (m : Val) (l : list Exp) (* call v:□(e₁, ..., eₙ) *)
| FCase1 (l : list ((list Pat) * Exp * Exp))
(* | FCase2   (lv : list Val)
           (lp : list Pat)
           (ex : Exp)
           (le : list ((list Pat) * Exp * Exp))
           (lvp : list Val) *)
           (* the result of the pattern matching, only needed in the reduction rules
         ^---- Not a good solution, because if this frame is used outside
               of a bigger context, lvp is not known to be the result of
               the pattern matching *)
| FCase2   (lv : list Val)
           (* (lp : list Pat) *)
           (ex : Exp)
           (le : list ((list Pat) * Exp * Exp))
| FLet   (l : nat) (e : Exp) (* let <x₁, ..., xₙ> = □ in e *)
| FSeq   (e : Exp)           (* do □ e *)
| FTry (vl1 : nat) (e2 : Exp) (vl2 : nat) (e3 : Exp)
  (* try □ of <x₁, ..., xₙ> -> e₂ catch <xₙ₊₁, ..., xₙ₊ₘ> -> e₃ *)
(* Concurrent frames for receive - this is not used in the sequential semantics
   These are very similar to the frames for case, but we define them separately
   for the separation of concerns.
*)
(* | FReceive1 (l1 l2 : list ((list Pat) * Exp * Exp)) (mb : list Val)
(* receive p₁ when g₁ -> b₁;
               ...
           pᵢ when gᵢ -> bᵢ;
           pᵢ₊₁ when gᵢ₊₁ -> bᵢ₊₁;
               ...
           pₙ when gₙ -> bₙ
   end [v₁, ..., vₖ] <- this is the processed part of the mailbox
*)
| FReceive2 (l1 : list ((list Pat) * Exp * Exp))
            (v : Val) (b :Exp) (* <- currently the mailbox value v is
                                     matched against the ith clause, 
                                     and the guard is evaluated *)
            (l2 : list ((list Pat) * Exp * Exp)) (mb : list Val) *)
.

Inductive ICLOSED : FrameIdent -> Prop :=
| iclosed_values : ICLOSED IValues
| iclosed_tuple : ICLOSED ITuple
| iclosed_map : ICLOSED IMap
| iclosed_app v : VALCLOSED v -> ICLOSED (IApp v)
| iclosed_call m f : VALCLOSED m -> VALCLOSED f -> ICLOSED (ICall m f)
| iclosed_primop f : ICLOSED (IPrimOp f).

Inductive FCLOSED : Frame -> Prop :=
| fclosed_cons1 e : EXPCLOSED e -> FCLOSED (FCons1 e)
| fclosed_cons2 v : VALCLOSED v -> FCLOSED (FCons2 v)
| fclosed_params ident vl el :
  ICLOSED ident ->
  Forall (fun v => VALCLOSED v) vl ->
  Forall (fun e => EXPCLOSED e) el ->
  (* map invariant (even with this, the semantics of maps is a bit tricky) *)
  (ident = IMap -> exists n, length el + length vl = 1 + 2 * n)
  (* without this, we cannot be sure that the lists of expressions
     and values build up a map correctly (after applying ˝deflatten_list˝) *)
->
  FCLOSED (FParams ident vl el)
| fclosed_app1 l : Forall (fun e => EXPCLOSED e) l -> FCLOSED (FApp1 l)
| fclosed_callmod f l : EXPCLOSED f -> Forall (fun e => EXPCLOSED e) l -> FCLOSED (FCallMod f l)
| fclosed_callfun m l : VALCLOSED m -> Forall (fun e => EXPCLOSED e) l -> FCLOSED (FCallFun m l)
| fclosed_case1 l : 
  Forall (fun '(pl, g, b) => EXP PatListScope pl ⊢ g /\ EXP PatListScope pl ⊢ b) l
->
  FCLOSED (FCase1 l)
| fclosed_case2 vl (* pl *) e rest :
  Forall (fun v => VALCLOSED v) vl ->
  EXPCLOSED e ->
  (* (exists vs, match_pattern_list pl vl = Some vs) -> (* frame invariant! *) *)
  Forall (fun '(pl, g, b) => EXP PatListScope pl ⊢ g /\ EXP PatListScope pl ⊢ b) rest
->
  FCLOSED (FCase2 vl (* pl *) e rest)
| fclosed_let vars e : EXP vars ⊢ e -> FCLOSED (FLet vars e)
| fclosed_seq e : EXPCLOSED e -> FCLOSED (FSeq e)
| fclosed_try vars1 vars2 e2 e3 :
  EXP vars1 ⊢ e2 -> EXP vars2 ⊢ e3
->
  FCLOSED (FTry vars1 e2 vars2 e3)

(* | fclosed_receive1 l1 l2 mb : 
  Forall (fun '(pl, g, b) => EXP PatListScope pl ⊢ g /\ EXP PatListScope pl ⊢ b) l1 ->
  Forall (fun '(pl, g, b) => EXP PatListScope pl ⊢ g /\ EXP PatListScope pl ⊢ b) l2 ->
  Forall (fun v => VALCLOSED v) mb
->
  FCLOSED (FReceive1 l1 l2 mb)

| fclosed_receive2 l1 v e l2 mb :
  VALCLOSED v ->
  EXPCLOSED e ->
  Forall (fun '(pl, g, b) => EXP PatListScope pl ⊢ g /\ EXP PatListScope pl ⊢ b) l1 ->
  Forall (fun '(pl, g, b) => EXP PatListScope pl ⊢ g /\ EXP PatListScope pl ⊢ b) l2 ->
  Forall (fun v => VALCLOSED v) mb
->
  FCLOSED (FReceive2 l1 v e l2 mb) *)
.

Proposition clause_scope l :
  (forall i : nat,
  i < Datatypes.length l ->
  EXP PatListScope (nth i (map (fst >>> fst) l) [])
  ⊢ nth i (map (fst >>> snd) l) (˝ VNil)) ->
  (forall i : nat,
        i < Datatypes.length l ->
        EXP PatListScope (nth i (map (fst >>> fst) l) [])
        ⊢ nth i (map snd l) (˝ VNil)) ->
   Forall (fun '(pl, g, b) => EXP PatListScope pl ⊢ g /\ EXP PatListScope pl ⊢ b) l.
Proof.
  induction l; intros; auto.
  constructor.
  * destruct a, p. split.
    - apply (H 0). slia.
    - apply (H0 0). slia.
  * apply IHl; intros; (apply (H (S i)) + apply (H0 (S i))); slia.
Qed.

Proposition clause_scope_rev l :
  Forall (fun '(pl, g, b) => EXP PatListScope pl ⊢ g /\ EXP PatListScope pl ⊢ b) l
  ->
  (forall i : nat,
  i < Datatypes.length l ->
  EXP PatListScope (nth i (map (fst >>> fst) l) [])
  ⊢ nth i (map (fst >>> snd) l) (˝ VNil)) /\
  (forall i : nat,
        i < Datatypes.length l ->
        EXP PatListScope (nth i (map (fst >>> fst) l) [])
        ⊢ nth i (map snd l) (˝ VNil))
   .
Proof.
  intros. induction H; simpl; split; intros; try lia; destruct_foralls.
  * destruct i.
    - now destruct x, p, H.
    - apply IHForall. lia.
  * destruct i.
    - now destruct x, p, H0.
    - apply IHForall. lia.
Qed.

Definition to_Exp (ident : FrameIdent) (l : list Exp) : Exp :=
match ident with
| IValues => EValues l
| ITuple => ETuple l
| IMap => EMap (deflatten_list l)
| IApp v => EApp (˝v) l
| ICall m f => ECall (˝m) (˝f) l
| IPrimOp f => EPrimOp f l
end.

(*
  TODO: note to myself: after evaluating the base expression of case,
        do the pattern matching + substitution in all subbranches
*)

Definition plug_f (F : Frame) (e : Exp) : Exp :=
match F with
 | FCons1 hd   => °(ECons hd e)
 | FCons2 tl   => °(ECons e (˝tl))
 | FParams ident vl el => to_Exp ident (map VVal vl ++ [e] ++ el)
 | FApp1 l      => °(EApp e l)
 | FCallMod f l => °(ECall e f l)
 | FCallFun m l => °(ECall (˝m) e l)
 | FCase1 l     => °(ECase e l)
 | FCase2 lv (* lp *) ex le =>
   (** This is basically an if-then-else translation from Erlang: *)
   °(ECase (°EValues []) [([], e, ex);
                        ([], ˝ttrue, °ECase (°EValues (map VVal lv)) le)])
   (** We chosed this approach, since frames have to satisfy an implicit
       invariant: their □ has to be substituted by closed expressions.
       This way, ˝e˝ is handled as closed, since the corresponding pattern
       does not include variables. *)
 | FLet l ex            => °(ELet l e ex)
 | FSeq ex              => °(ESeq e ex)
 | FTry vl1 e2 vl2 e3   => °(ETry e vl1 e2 vl2 e3)
  (** concurrent frames (mailbox is ignored): *)
(*  | FReceive1 l1 l2 mb => EReceive (l1 ++ l2) (* This frame in itself is a complete
                                                receive expression *)
 | FReceive2 l1 v b l2 mb => EReceive (l1 ++ l2) (* Receive frames include the
                                                    current clause also as the 
                                                    last item of l1! *) *)
end.

Definition FrameStack := list Frame.

Definition FSCLOSED (fs : FrameStack) := Forall FCLOSED fs.

#[global]
Hint Constructors ICLOSED : core.

Ltac destruct_frame_scope :=
  match goal with
  | [H : FSCLOSED (_ :: _) |- _] => inversion H; subst; clear H
  | [H : FSCLOSED [] |- _] => clear H
  | [H : FCLOSED (FCons1 _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FCons2 _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FParams _ _ _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FApp1 _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FCallFun _ _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FCallMod _ _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FCase1 _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FCase2 _ _ (* _ *) _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FLet _ _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FSeq _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FTry _ _ _ _) |- _] => inversion H; subst; clear H
(*   | [H : FCLOSED (FReceive1 _ _ _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FReceive2 _ _ _ _ _) |- _] => inversion H; subst; clear H *)
  end.

Ltac destruct_scopes :=
  repeat destruct_frame_scope;
  repeat destruct_redex_scope.

Ltac scope_solver_step :=
  match goal with 
  | |- EXP _ ⊢ _ => constructor; simpl; auto
  | |- VAL _ ⊢ _ => constructor; simpl; auto
  | |- RED _ ⊢ _ => constructor; simpl; auto
  | |- NVAL _ ⊢ _ => constructor; simpl; auto
  | |- ICLOSED _ => constructor; simpl; auto
  | |- forall i, i < _ -> _ => simpl; intros
  | |- Forall FCLOSED _ => constructor; simpl
  | |- Forall (fun v => VAL _ ⊢ v) _ => constructor; simpl
  | |- Forall (fun v => EXP _ ⊢ v) _ => constructor; simpl
  | |- Forall _ _ => constructor; simpl
  | |- _ /\ _ => split
  | |- FSCLOSED _ => constructor; simpl
  | |- FCLOSED _ => constructor; simpl
  | [H : ?i < _ |- _] => inv H; simpl in *; auto; try lia
  | [H : ?i <= _ |- _] => inv H; simpl in *; auto; try lia
  | [H : EXP ?n1 ⊢ ?e |- EXP ?n2 ⊢ ?e] => try now (eapply (loosen_scope_exp n2 n1 ltac:(lia)) in H)
  | [H : VAL ?n1 ⊢ ?e |- VAL ?n2 ⊢ ?e] => try now (eapply (loosen_scope_val n2 n1 ltac:(lia)) in H)
  | [H : NVAL ?n1 ⊢ ?e |- NVAL ?n2 ⊢ ?e] => try now (eapply (loosen_scope_nonval n2 n1 ltac:(lia)) in H)
  end.
Ltac scope_solver := repeat scope_solver_step; try lia.

Lemma inf_scope :
  forall Γ, NVAL Γ ⊢ inf.
Proof.
  intros. unfold inf. scope_solver.
Qed.

#[global]
Hint Resolve inf_scope : core.

Opaque inf.


From CoreErlang.FrameStack Require Export Frames.
From CoreErlang Require Export Auxiliaries Matching.

Import ListNotations.

Definition create_result (ident : FrameIdent) (vl : list Val) (eff : SideEffectList)
  : option (Redex * SideEffectList) :=
match ident with
| IValues => Some (RValSeq vl, eff)
| ITuple => Some (RValSeq [VTuple vl], eff)
| IMap => Some (RValSeq [VMap (make_val_map (deflatten_list vl))], eff)
| ICall m f => match m, f with
               | VLit (Atom module), VLit (Atom func) => eval module func vl []
               | _, _ => Some (RExc (badfun (VTuple [m; f])), eff)
               end
| IPrimOp f => primop_eval f vl []
| IApp (VClos ext id vars e) =>
  if Nat.eqb vars (length vl)
  then Some (RExp (e.[list_subst (convert_to_closlist ext ++ vl) idsubst]), eff)
  else Some (RExc (badarity (VClos ext id vars e)), eff)
| IApp v => Some (RExc (badfun v), eff)
end.

Proposition FrameIdent_eq_dec :
  forall id1 id2 : FrameIdent, {id1 = id2} + {id1 <> id2}.
Proof.
  decide equality; try apply string_dec.
  all: apply Val_eq_dec.
Qed.

(** Receives are specially handled by Core Erlang in case of exceptions, thus
    propagation is described in the process-local level *)
Definition isPropagatable (f : Frame) : bool :=
match f with
 | FTry _ _ _ _ (* | FReceive1 _ _ _ | FReceive2 _ _ _ _ _ *) => false
 | _ => true
end.


(* Note: for simplicity, this semantics allows guards to evaluate
   to exceptions, which is not allowed in normal Core Erlang. *)
Reserved Notation "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" (at level 50).
Inductive step : FrameStack -> Redex -> FrameStack -> Redex -> Prop :=
(**  Reduction rules *)

(** Cooling: single value *)
| cool_value v xs:
  VALCLOSED v -> (* to filter out variables *)
  ⟨ xs, ˝v ⟩ --> ⟨ xs, RValSeq [v] ⟩

(************************************************)
(* heating should be separate for all complex expressions (to be
   syntax-driven).
   Only the intermediate and last steps can be extracted: *)
| eval_step_params xs ident (el : list Exp) (vl : list Val) (v : Val) (e : Exp):
  ⟨FParams ident vl (e :: el) :: xs, RValSeq [v]⟩ -->
  ⟨FParams ident (vl ++ [v]) el :: xs, e⟩

(* technical rule to avoid duplication for 0 subexpressions : *)
| eval_step_params_0 xs ident e el vl:
  ident <> IMap ->
  ⟨FParams ident vl (e::el) ::xs, RBox⟩ --> ⟨FParams ident vl el :: xs, e⟩

(* 0 subexpression in complex expressions: *)
| eval_cool_params_0 xs ident (vl : list Val) (res : Redex) (eff' : SideEffectList) : 
  ident <> IMap ->
  Some (res, eff') = create_result ident vl [] -> (* TODO: side effects *)
  ⟨FParams ident vl [] ::xs, RBox⟩ --> ⟨xs, res⟩

| eval_cool_params xs ident (vl : list Val) (v : Val) (res : Redex) (eff' : SideEffectList):
  Some (res, eff') = create_result ident (vl ++ [v]) [] ->(* TODO: side effects *)
  ⟨FParams ident vl [] :: xs, RValSeq [v]⟩ --> ⟨xs, res⟩

(************************************************)
(* Heating constructs with list subexpressions: *)
| eval_heat_values (el : list Exp) (xs : list Frame):
  ⟨ xs, EValues el ⟩ --> ⟨ (FParams IValues [] el)::xs, RBox ⟩

| eval_heat_tuple (el : list Exp) (xs : list Frame):
  ⟨ xs, ETuple el ⟩ --> ⟨ (FParams ITuple [] el)::xs, RBox ⟩

(* This is handled separately, to satisfy the invariant in FCLOSED for maps *)
| eval_heat_map_0 (xs : list Frame):
  ⟨ xs, EMap [] ⟩ --> ⟨ xs, RValSeq [VMap []] ⟩

| eval_heat_map (e1 e2 : Exp) (el : list (Exp * Exp)) (xs : list Frame):
  ⟨ xs, EMap ((e1, e2) :: el) ⟩ -->
  ⟨ (FParams IMap [] (e2 :: flatten_list el))::xs, e1 ⟩

| eval_heat_call_mod (el : list Exp) (xs : list Frame) (m f : Exp) :
  ⟨ xs, ECall m f el ⟩ --> ⟨ FCallMod f el :: xs, m ⟩

| eval_heat_call_fun (el : list Exp) (xs : list Frame) (v : Val) (f : Exp) :
  ⟨ FCallMod f el :: xs, RValSeq [v] ⟩ --> ⟨ FCallFun v el :: xs, f ⟩

| eval_heat_call_params (el : list Exp) (xs : list Frame) (m f : Val):
  ⟨ FCallFun m el :: xs, RValSeq [f] ⟩ --> ⟨ (FParams (ICall m f) [] el)::xs, RBox ⟩

| eval_heat_primop (el : list Exp) (xs : list Frame) f:
  ⟨ xs, EPrimOp f el ⟩ --> ⟨ (FParams (IPrimOp f) [] el)::xs, RBox ⟩

| eval_heat_app2 (el : list Exp) (xs : list Frame) (v : Val):
  ⟨ FApp1 el :: xs, RValSeq [v] ⟩ --> ⟨ (FParams (IApp v) [] el)::xs, RBox ⟩

(************************************************)
(**  App *)
| eval_heat_app xs e l:
  ⟨xs, EApp e l⟩ --> ⟨FApp1 l :: xs, e⟩ 
(**  List *)
(**  Cooling *)

| eval_cool_cons_1 (hd : Exp) (tl : Val) xs :
  ⟨ (FCons1 hd)::xs, RValSeq [tl] ⟩ --> ⟨ (FCons2 tl)::xs, RExp hd ⟩

| eval_cool_cons_2 (hd tl : Val) xs :
  ⟨ (FCons2 tl)::xs, RValSeq [hd] ⟩ --> ⟨ xs, RValSeq [VCons hd tl] ⟩

(**  Heating *)
| eval_heat_cons (hd tl : Exp) xs :
  ⟨ xs, ECons hd tl ⟩ --> ⟨ (FCons1 hd)::xs, RExp tl ⟩

(**  Let *)
(**  Cooling *)
| eval_cool_let l e2 vs xs :
  length vs = l ->
  ⟨ (FLet l e2)::xs, RValSeq vs ⟩ --> ⟨ xs, RExp (e2.[ list_subst vs idsubst ]) ⟩

(**  Heating *)
| eval_heat_let l e1 e2 xs :
  ⟨ xs, ELet l e1 e2 ⟩ --> ⟨ (FLet l e2)::xs, RExp e1 ⟩

(**  Seq *)
(**  Cooling *)
| eval_cool_seq e2 v xs :
  ⟨ (FSeq e2)::xs, RValSeq [v] ⟩ --> ⟨ xs, RExp e2 ⟩
(**  Heating *)
| eval_heat_seq e1 e2 xs :
  ⟨ xs, ESeq e1 e2 ⟩ --> ⟨ (FSeq e2)::xs, RExp e1 ⟩


(**  Fun *)
(**  Cooling *)
| eval_cool_fun e vl xs :
  ⟨ xs, EFun vl e ⟩ --> ⟨ xs, RValSeq [ VClos [] 0 vl e ] ⟩
  (* TODO : id <> 0 usually *)


(**  Case *)
(**  Heating *)
| eval_heat_case e l xs:
  ⟨ xs, ECase e l ⟩ --> ⟨ (FCase1 l)::xs, RExp e ⟩

(**  Cooling *)
(* reduction started or it is already ongoing, the first pattern matched,
   e1 the guard needs to be evaluated. vs' (the result of the pattern
   matching is stored in the frame) *)
| eval_step_case_match lp e1 e2 l vs vs' xs :
  match_pattern_list lp vs = Some vs' ->
  ⟨ (FCase1 ((lp,e1,e2)::l))::xs, RValSeq vs ⟩ -->
  ⟨ (FCase2 vs e2.[list_subst vs' idsubst] l)::xs, RExp (e1.[list_subst vs' idsubst]) ⟩

(* reduction started or it is already ongoing, the first pattern doesn't 
   match, so we check the next pattern *)
| eval_step_case_not_match lp e1 e2 l vs xs :
  match_pattern_list lp vs = None ->
  ⟨ (FCase1 ((lp,e1,e2)::l))::xs, RValSeq vs ⟩ -->
  ⟨ (FCase1 l)::xs, RValSeq vs ⟩

(* reduction is ongoing, the pattern matched, and the guard is true, thus 
   the reduction continues inside the given clause *)
| eval_step_case_true vs e' l xs :
  ⟨ (FCase2 vs e' l)::xs, RValSeq [ VLit (Atom "true") ] ⟩ --> 
  ⟨ xs, RExp e' ⟩

(* reduction is ongoing, the pattern matched, and the guard is false, thus
   we check the next pattern. *)
| eval_step_case_false vs e' l xs :
  ⟨ (FCase2 vs e' l)::xs, RValSeq [ VLit (Atom "false") ] ⟩ --> ⟨ (FCase1 l)::xs, RValSeq vs ⟩

(** Exceptions *)
| eval_cool_case_empty vs xs:
  ⟨ (FCase1 [])::xs, RValSeq vs ⟩ --> ⟨ xs, RExc if_clause ⟩

(**  LetRec *)
(**  Cooling *)
(**  Heating *)
| eval_heat_letrec l e lc xs :
  convert_to_closlist (map (fun '(x,y) => (0,x,y)) l) = lc ->
  (* TODO: for now the funids are 0 coded in *)
  ⟨ xs, ELetRec l e ⟩ --> ⟨ xs, RExp e.[list_subst lc idsubst] ⟩


(**  Try *)
(**  Cooling *)
| eval_cool_try_ok vl1 e2 vl2 e3 vs xs:
  vl1 = length vs ->
  ⟨ (FTry vl1 e2 vl2 e3)::xs, RValSeq vs ⟩ --> ⟨ xs, RExp e2.[ list_subst vs idsubst ] ⟩
| eval_cool_try_err vl1 e2 e3 class reason details xs:
  (* in Core Erlang exceptions always have 3 parts *)
  ⟨ (FTry vl1 e2 3 e3)::xs, RExc (class, reason, details) ⟩ -->
  ⟨ xs, RExp e3.[ list_subst [exclass_to_value class; reason; details] idsubst ] ⟩
(**  Heating *)
| eval_heat_try e1 vl1 e2 vl2 e3 xs :
  ⟨ xs, ETry e1 vl1 e2 vl2 e3 ⟩ --> ⟨ (FTry vl1 e2 vl2 e3)::xs, RExp e1 ⟩
  
(** Exceptions *)
(** Propogation *)
| eval_prop_exc F exc xs :
  isPropagatable F = true ->
  ⟨ F::xs, RExc exc ⟩ --> ⟨ xs, RExc exc ⟩
  (* TODO: details could be appended here to the stack trace *)

where "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" := (step fs e fs' e').


Reserved Notation "⟨ fs , e ⟩ -[ k ]-> ⟨ fs' , e' ⟩" (at level 50).
Inductive step_rt : FrameStack -> Redex -> nat -> FrameStack -> Redex -> Prop :=
| step_refl fs e : ⟨ fs, e ⟩ -[ 0 ]-> ⟨ fs, e ⟩
| step_trans fs e fs' e' fs'' e'' k:
  ⟨ fs, e ⟩ --> ⟨ fs', e'⟩ -> ⟨fs', e'⟩ -[ k ]-> ⟨fs'', e''⟩
  ->
  ⟨ fs, e ⟩ -[S k]-> ⟨fs'', e''⟩
where "⟨ fs , e ⟩ -[ k ]-> ⟨ fs' , e' ⟩" := (step_rt fs e k fs' e').

Definition step_any (fs : FrameStack) (e : Redex) (r : Redex) : Prop :=
  exists k, is_result r /\ ⟨fs, e⟩ -[k]-> ⟨[], r⟩.
Notation "⟨ fs , e ⟩ -->* v" := (step_any fs e v) (at level 50).

*)




From CoreErlang.Eq.Tactics Require Export T1ParamZero.
From CoreErlang.Eq.Tactics Require Export T2ParamSingle.
From CoreErlang.Eq.Tactics Require Export T3ParamMultiple.
From CoreErlang.Eq.Tactics Require Export T4Name.
From CoreErlang.Eq.Tactics Require Export T5Transform.
From CoreErlang.Eq.Tactics Require Export T6Destruct.
From CoreErlang Require Export Basics.
From CoreErlang.BigStep Require Export BigStep.
From CoreErlang.FrameStack Require Export SubstSemanticsLemmas.
Require Export stdpp.list.

Import BigStep.

(* STRUCTURE:
* List
  - length_lt_split
* Injection
  - cons_inj
  - vcons_inj
  - vtuple_inj
  - vmap_inj
*)












Section List.



  Lemma length_lt_split :
    forall A B (al : list A) (bl : list B),
        length al < length bl
    ->  exists bl1 bl2 : list B,
            bl = bl1 ++ bl2
        /\  length bl1 = length al.
  Proof.
    (* #1 Exists: intro/exists/split *)
    itr - A B al bl Hl.
    exi - (firstn (length al) bl)
          (skipn (length al) bl).
    spl.
    * (* #2.1 Equality: rewrite *)
      by rewrite take_drop.
    * (* #2.2 Length: rewrite/reflexivity/lia *)
      rwr - firstn_length_le.
      - rfl.
      - lia.
  Qed.



End List.









Section Injection.



  Lemma cons_inj :
    forall
      (T : Type)
      (x y : T)
      (xs ys : list T),
        x :: xs = y :: ys
    ->  x = y /\ xs = ys.
  Proof.
    (* #1 Inversion: intro/inversion/auto + clear *)
    itr.
    ivc - H.
    ato.
  Qed.



  Lemma vcons_inj :
    forall
      (T : Type)
      (f : T -> Val)
      (x1 x2 : T)
      (y : Val),
        Syntax.VCons (f x1) (f x2) = y
    ->  exists z1 z2,
            (f x1) = z1
        /\  (f x2) = z2
        /\  y = Syntax.VCons z1 z2.
  Proof.
    (* #1 Exists: intro/exists/auto *)
    itr.
    exi - (f x1) (f x2).
    ato.
  Qed.



  Lemma vtuple_inj :
    forall
      (T : Type)
      (f : T -> Val)
      (x : T)
      (xl : list T)
      (y : Val),
        Syntax.VTuple ((f x) :: (map f xl)) = y
    ->  exists z zl,
            (f x) = z
        /\  (map f xl) = zl
        /\  y = Syntax.VTuple (z :: zl).
  Proof.
    (* #1 Exists: intro/exists/auto *)
    itr.
    exi - (f x) (map f xl).
    ato.
  Qed.



  Lemma vmap_inj :
    forall
      (T : Type)
      (f : T -> Val)
      (x1 x2 : T)
      (xll : list (T * T))
      (y : Val),
        Syntax.VMap (((f x1), (f x2)) :: (map (prod_map f f) xll)) = y
    ->  exists z1 z2 zll,
            (f x1) = z1
        /\  (f x2) = z2
        /\  (map (prod_map f f) xll) = zll
        /\  y = Syntax.VMap ((z1, z2) :: zll).
  Proof.
    (* #1 Exists: intro/exists/auto *)
    itr.
    exi - (f x1) (f x2) (map (prod_map f f) xll).
    ato.
  Qed.



End Injection.
















Import BigStep.

(* STRUCTURE:
* Value
  - ind_val
* Expression
  - ind_exp
*)












Section Induction_Value.



  Variables
    (P : Value -> Prop).



  Hypotheses
    (HNil : P VNil)

    (HLit :
      forall l,
        P (VLit l))

    (HCons :
      forall hd tl,
          P hd
      ->  P tl
      ->  P (VCons hd tl))

    (HClos :
      forall ref ext id params body funid,
          Forall (fun x => P (snd x)) ref
      ->  P (VClos ref ext id params body funid))

    (HTuple :
      forall l,
          Forall P l
      ->  P (VTuple l))

    (HMap :
      forall l,
          Forall (fun x => P (fst x) /\ P (snd x)) l
      ->  P (VMap l)).



  Theorem ind_val :
    forall v, P v.
  Proof.
    induction v using Value_ind2 with
      (Q := Forall P)
      (R := Forall (fun x => P (fst x) /\ P (snd x)))
      (W := Forall (fun x => P (snd x)));
      intuition.
  Defined.



End Induction_Value.









Section Induction_Expression.



  Variables
    (P : Expression -> Prop).



  Hypotheses
    (HValues :
      forall el,
          Forall P el
      ->  P (EValues el))

    (HNil : P ENil)

    (HLit :
      forall l,
          P (ELit l))

    (HVar :
      forall v,
          P (EVar v))

    (HFunId :
      forall f,
        P (EFunId f))

    (HFun :
      forall vl e,
          P e
      ->  P (EFun vl e))

    (HCons :
      forall hd tl,
          P hd
      ->  P tl
      ->  P (ECons hd tl))

    (HTuple :
      forall l,
          Forall P l
      ->  P (ETuple l))

    (HCall :
      forall m f l,
          P m
      ->  P f
      ->  Forall P l
      ->  P (ECall m f l))

    (HPrimOp :
      forall f l,
          Forall P l
      ->  P (EPrimOp f l))

    (HApp :
      forall exp l,
          P exp
      ->  Forall P l
      ->  P (EApp exp l))

    (HCase :
      forall e l,
          P e
      ->  Forall (fun x => P (snd (fst x)) /\ P (snd x)) l
      ->  P (ECase e l))

    (HLet :
      forall l e1 e2,
          P e1
      ->  P e2
      ->  P (ELet l e1 e2))

    (HSeq :
      forall e1 e2,
          P e1
      ->  P e2
      ->  P (ESeq e1 e2))

    (HLetRec :
      forall l e,
          P e
      ->  Forall (fun x => P (snd (snd x))) l
      ->  P (ELetRec l e))

    (HMap :
      forall l,
          Forall (fun x => P (fst x) /\ P (snd x)) l
      ->  P (EMap l))

    (HTry :
      forall e1 vl1 e2 vl2 e3,
          P e1
      ->  P e2
      ->  P e3
      ->  P (ETry e1 vl1 e2 vl2 e3)).



  Theorem ind_exp :
    forall e, P e.
  Proof.
    induction e using Expression_ind2 with
      (Q := Forall P)
      (R := Forall (fun x => P (fst x) /\ P (snd x)))
      (W := Forall (fun x => P (snd (fst x)) /\ P (snd x)))
      (Z := Forall (fun x => P (snd (snd x))));
      intuition.
  Defined.



End Induction_Expression.

























(* STRUCTURE:
* Insert
  - map_insert_unfold (BigStep)
  - map_insert_length_le (FrameStack)
* MakeLength
  - make_value_map_length (BigStep)
  - make_val_map_length (FrameStack)
* MakeCons
  - make_value_map_cons (BigStep)
  - make_val_map_cons (FrameStack)
*)












Section Insert.



  Import BigStep.

  Lemma map_insert_unfold :
    forall k v kl vl,
      map_insert k v kl vl
    = match kl with
      | [] => match vl with
              | [] => ([k], [v])
              | _ :: _ => ([], [])
              end
      | k' :: ks =>
          match vl with
          | [] => ([], [])
          | v' :: vs =>
              if Value_ltb k k'
              then (k :: k' :: ks, v :: v' :: vs)
              else
               if Value_eqb k k'
               then (k' :: ks, v' :: vs)
               else (k' :: (map_insert k v ks vs).1,
                     v' :: (map_insert k v ks vs).2)
          end
      end.
  Proof.
    (* #1 Destruct Trivial: intro/destruct/trivial *)
    itr.
    des - kl; des - vl :- trv.
  Qed.



  Import SubstSemantics.

  Lemma map_insert_length_le :
    forall k k' v v' vl,
      length (map_insert k v vl) <= length ((k', v') :: vl).
  Proof.
    (* #1 Induction List: intro/induction + simpl/lia *)
    itr.
    ind - vl as [| (key, var) vl IHvl]: sli |> smp.
    (* #2 Destruct Key: destruct/apply + simpl/lia *)
    des > (k <ᵥ key): sli.
    des > (k =ᵥ key): sli.
    bpp - le_n_S.
  Qed.



End Insert.










Section MakeLength.




  Import BigStep.

  Lemma make_value_map_length :
    forall kvl vvl,
        length kvl = length vvl
    ->  length (make_value_map kvl vvl).1
      = length (make_value_map kvl vvl).2.
  Proof.
    (* #1 Destruct Lists: intro/destruct/inversion
        + simpl/congruence + subst/clear *)
    itr - kvl vvl Hlength.
    des - kvl as [| kv kvl];des - vvl as [| vv vvl]
       :- smp - Hlength; con + smp.
    ivc - Hlength as Hlength: H0.
    (* #2 Unfold Map_Insert: refold/rewrite *)
    rfl - make_value_map.
    rwr - map_insert_unfold.
    (* #3 Destruct Elements: destruct + trivial/simpl *)
    des > ((make_value_map kvl vvl).1);
    des > ((make_value_map kvl vvl).2).
    1-3: trv.
    des > (Value_ltb kv v);
    des > (Value_eqb kv v).
    1-3: smp; trv.
    all: admit.
  Admitted.



  Import SubstSemantics.

  Lemma make_val_map_length :
    forall vl,
      length (make_val_map vl) <= length vl.
  Proof.
    (* #1 Induction List: intro/induction + simpl/lia *)
    itr.
    ind - vl as [| (k, v) vl Hvl_cons]: sli |> smp.
    (* #2 Destruct Key: destruct/apply + apply/simpl *)
    des > (make_val_map vl) as [| (k', v') vl']: app - le_n_S |> smp.
    des > (k <ᵥ k'): smp *; app - le_n_S.
    des > (k =ᵥ k'): smp *; app - le_S |> smp.
    app - le_n_S.
    (* #3 Transivity: pose/lia *)
    pse - map_insert_length_le as Hvl_insert: k k' v v' vl'.
    lia.
  Qed.



End MakeLength.









Section MakeCons.



  Import BigStep.

  Theorem make_value_map_cons :
    forall kv kvl vv vvl mkvl mvvl,
        length kvl = length vvl
    ->  make_value_map (kv :: kvl) (vv :: vvl) = (mkvl, mvvl)
    ->  mkvl <> [] /\ mvvl <> [].
  Proof.
    (* #1 Unfold Map_Insert: intro/simpl/rewrite *)
    itr - kv kvl vv vvl mkvl mvvl Hlength Hmake.
    smp - Hmake.
    rwr - map_insert_unfold in Hmake.
    (* #2 Pose Length: pose + clear *)
    psc - make_value_map_length as Hlength_make: kvl vvl Hlength.
    (* #3 Destruct Maps: destruct
        + simpl/symmetry/apply/rewrite/inversion/subst/split/auto *)
    des > ((make_value_map kvl vvl).1).
    {
      smp - Hlength_make.
      sym - Hlength_make.
      app - length_zero_iff_nil as Hempty in Hlength_make.
      rwr - Hempty in *.
      ivs - Hmake.
      spl; ato.
    }
    des > ((make_value_map kvl vvl).2): ivs - Hlength_make.
    (* #4 Destuct Key Eq: destruct + inversion/subst/split/auto *)
    des > (Value_ltb kv v); des > (Value_eqb kv v); ivs - Hmake; spl; ato.
  Qed.



  Import SubstSemantics.

  Theorem make_val_map_cons :
    forall v1 v2 vl,
        (v1, v2) :: vl = make_val_map ((v1, v2) :: vl)
    ->  vl = make_val_map vl.
  Proof.
    (* #1 Destruct Make: intro/inversion/unfold/destruct + inversion *)
    itr - v1 v2 vl Hcons.
    ivc - Hcons as Hcons: H0.
    ufl - Maps.map_insert in Hcons.
    des > (make_val_map vl) as [| (v1', v2') vl'] Hmake: ivr - Hcons.
    (* #2 Destruct Key: destruct + inversion *)
    des > (v1 <ᵥ v1'): ivr - Hcons.
    des > (v1 =ᵥ v1') as Heq; ivc - Hcons.
    * (* #2.1 Insert Key Equals: pose/rewrite/simpl/lia *)
      pse - make_val_map_length as Hlen: vl'.
      cwr - Hmake in Hlen.
      smp - Hlen.
      sli.
    * (* #2.1 Insert Key Bigger: rewrite/congruence*)
      rwr - Val_eqb_refl in Heq.
      con.
  Qed.



End MakeCons.






















Import SubstSemantics.

(* STRUCTURE:
* WellFormedMap
  - wfm_val
  - wfm_val_valseq
  - wfm_val_exception
  - wfm_val_result
*)












Section WellFormedMap.



  Fixpoint wfm_val
    (v : Val)
    : Prop
    :=
  match v with

  | VCons hd tl =>
      wfm_val hd
    /\
      wfm_val tl

  | VTuple l =>
      foldr
        (fun v acc => wfm_val v /\ acc)
        True
        l

  | VMap l =>
      l = make_val_map l
    /\
      foldr
        (fun v acc => PBoth wfm_val v /\ acc)
        True
        l

  | _ => True

  end.



  Definition wfm_valseq
    (vs : ValSeq)
    : Prop
    :=
  foldr (fun v acc => wfm_val v /\ acc) True vs.



  Definition wfm_exception
    (exc : Exception)
    : Prop
    :=
  match exc with
  | (excc, v1, v2) => wfm_val v1 /\ wfm_val v2
  end.



  Definition wfm_result
    (res : Redex)
    : Prop
    :=
  match res with
  | RValSeq vs => wfm_valseq vs
  | RExc exc => wfm_exception exc
  | _ => True
  end.



End WellFormedMap.















Import SubstSemantics.

(* STRUCTURE:
* Induction
  - wfm_vcons
  - wfm_vtuple
  - wfm_vmap
* Transform
  - wfm_val_to_result
  - wfm_valseq_to_result
  - wfm_exception_to_result
  - wfm_val_to_forall
*)












Section Induction.



  Theorem wfm_vcons :
    forall v1 v2,
        Forall wfm_val [VCons v1 v2]
    ->  Forall wfm_val [v1]
    /\  Forall wfm_val [v2].
  Proof.
    (* #1 Destruct Foralls: intro/inversion *)
    itr - v1 v2 HForall.
    ivc - HForall as Hv1v2: H1 / H2.
    (* #2 Destruct & Split: destruct/split/auto *)
    des - Hv1v2 as [Hv1 Hv2].
    spl; ato.
  Qed.



  Theorem wfm_vtuple :
    forall v vl,
        Forall wfm_val [VTuple (v :: vl)]
    ->  Forall wfm_val [v]
    /\  Forall wfm_val [VTuple vl].
  Proof.
    (* #1 Destruct Foralls: intro/inversion *)
    itr - v vl HForall.
    ivc - HForall as Hvvl: H1 / H2.
    (* #2 Destruct & Split: destruct/split/auto *)
    des - Hvvl as [Hv Hvl].
    spl; ato.
  Qed.



  Theorem wfm_vmap :
    forall v1 v2 vl,
        Forall wfm_val [VMap ((v1, v2) :: vl)]
    ->  Forall wfm_val [v1]
    /\  Forall wfm_val [v2]
    /\  Forall wfm_val [VMap vl].
  Proof.
    (* #1 Destruct Foralls: intro/inversion *)
    itr - v1 v2 vl HForall.
    ivc - HForall as Hv1v2vl: H1 / H2.
    (* #2 Destruct & Split: destruct/split/constructor/auto *)
    des - Hv1v2vl as [Hmake [[Hv1 Hv2] Hvl]].
    do 4 (spl + cns; ato).
    (* #3 Prove Eqvivalence by Lemma: clear/pose *)
    clr - Hv1 Hv2 Hvl.
    bse - make_val_map_cons: v1 v2 vl Hmake.
  Qed.



End Induction.









Section Transform.



  Lemma wfm_val_to_result :
    forall v,
        wfm_val v
    ->  wfm_result (RValSeq [v]).
  Proof.
    (* #1 Auto: intro/cbn/auto *)
    itr; abn.
  Qed.



  Lemma wfm_valseq_to_result :
    forall vs,
        wfm_valseq vs
    ->  wfm_result (RValSeq vs).
  Proof.
    (* #1 Auto: intro/cbn/auto *)
    itr; abn.
  Qed.



  Lemma wfm_exception_to_result :
    forall exc,
        wfm_exception exc
    ->  wfm_result (RExc exc).
  Proof.
    (* #1 Auto: intro/cbn/auto *)
    itr; abn.
  Qed.



  Lemma wfm_val_to_forall :
    forall v,
        wfm_val v
    ->  Forall wfm_val [v].
  Proof.
    (* #1 Auto: intro/cbn/auto *)
    itr; abn.
  Qed.



End Transform.










Import BigStep.

(* STRUCTURE:
* Remove
  - rem_keys
  - rem_vars
  - rem_fids
  - rem_exp_ext_fids
  - rem_val_ext_fids
  - rem_exp_ext_both
  - rem_val_ext_both
*)












Section Remove.



  Definition rem_keys
    (keys : list (Var + FunctionIdentifier))
    (env : Environment)
    : Environment
    :=
    filter
      (fun '(k, v) =>
        negb (existsb
          (fun x => (var_funid_eqb x k))
          keys))
      env.



  Definition rem_vars
    (vars : list Var)
    (env : Environment)
    : Environment
    :=
  rem_keys (map inl vars) env.



  Definition rem_fids
    (fids : list FunctionIdentifier)
    (env : Environment)
    : Environment
    :=
  rem_keys (map inr fids) env.



  Definition rem_exp_ext_fids
    (ext : list (FunctionIdentifier * FunctionExpression))
    (env : Environment)
    : Environment
    :=
  rem_fids (map fst ext) env.



  Definition rem_val_ext_fids
    (ext : list (nat * FunctionIdentifier * FunctionExpression))
    (env : Environment)
    : Environment
    :=
  rem_fids (map (snd ∘ fst) ext) env.



  Definition rem_exp_ext_both
    (vars : list Var)
    (ext : list (FunctionIdentifier * FunctionExpression))
    (env : Environment)
    : Environment
    :=
  rem_exp_ext_fids ext (rem_vars vars env).



  Definition rem_val_ext_both
    (vars : list Var)
    (ext : list (nat * FunctionIdentifier * FunctionExpression))
    (env : Environment)
    : Environment
    :=
  rem_val_ext_fids ext (rem_vars vars env).



End Remove.



















Import BigStep.

(* STRUCTURE:
* Remove
  - rem_keys_cons_env
* GetValue
  - get_value_singleton
  - get_value_singleton_length
  - get_value_cons
  - get_value_in
*)












Section Remove.



  Lemma rem_keys_cons_env :
    forall keys k v env env',
        env' = rem_keys keys ((k, v) :: env)
    ->  env' = rem_keys keys env
    \/  env' = (k, v) :: rem_keys keys env.
  Proof.
    (* #1 Simplify: intro/simple *)
    itr - keys k v env env' Hcons.
    smp *.
    (* #2 Destruct Exists: destruct/right/left *)
    des >
      (negb
        (existsb (λ x : Var + FunctionIdentifier, var_funid_eqb x k) keys)).
    * by rgt.
    * by lft.
  Qed.



End Remove.









Section GetValue.



  Theorem get_value_singleton :
    forall env key vs,
        get_value env key = Some vs
    ->  exists value, vs = [value].
  Proof.
    (* #1 Induction on Environment: intro/induction + intro/simpl/congruence*)
    itr - env key vs.
    ind - env as [| [k v] env IHenv] :> itr - Hget; smp - Hget :- con.
    (* #2 Destruct Key Equality: destruct + apply *)
    des > (var_funid_eqb key k) as Hkey :- app - IHenv.
    (* #3 Exists Value: exists/inversion *)
    exi - v.
    bvs - Hget.
  Qed.



  Theorem get_value_singleton_length :
    forall env key l,
        get_value env key = Some l
    ->  length l = 1.
  Proof.
    (* #1 Pose by Previous: intro/pose/inversion *)
    itr - env key vs Hget.
    pse - get_value_singleton as Hsingl: env key vs Hget.
    bvs - Hsingl.
  Qed.



  Theorem get_value_cons :
    forall env key k var v,
        get_value ((k, v) :: env) key = Some [var]
    ->  get_value [(k, v)] key = Some [var] 
    \/  get_value env key = Some [var].
  Proof.
    (* #1 Destruct Key Equality: intro/simpl/destruct/auto *)
    itr - env key k var v Hcons.
    smp *.
    des > (var_funid_eqb key k) as Heqb_key; ato.
  Qed.



  Theorem get_value_in :
    forall env key var,
        get_value env key = Some [var]
    ->  In (key , var) env.
  Proof.
    (* #1 Induction on Environment: intro/induction + intro/inversion *)
    itr - env.
    ind - env as [| [k v] env IHenv] :> itr - key var Hget :- ivc - Hget.
    (* #2 Destruct Get_Value: apply/destruct *)
    app - get_value_cons in Hget.
    des - Hget as [Hget | Hget].
    * (* #3.1 Destruct Key Equality: clear/simpl/destruct + congruence *)
      clr - IHenv.
      smp *.
      des > (var_funid_eqb key k) as Hkey :- con.
      (* #4.1 Rewrite Var & FunId: left/inversion/apply/rewrite *)
      lft.
      ivc - Hget.
      app - var_funid_eqb_eq in Hkey.
      bwr - Hkey.
    * (* #3.2 Pose In_Cons: specialize/pose *)
      spc - IHenv: key var Hget.
      by pose proof in_cons (k, v) (key, var) env IHenv.
  Qed.



End GetValue.




























Import SubstSemantics.

(* STRUCTURE:
* Succ
  - scope_vl_succ
  - scope_vl_succ_id
* Induction
  - scope_cons
  - scope_tuple
  - scope_map
*)












Section Succ.



  Theorem scope_vl_succ :
    forall A i vl (f : A -> Val),
          (i < length vl
      ->  VALCLOSED (nth i (map f vl) VNil))
    ->    (S i < S (length vl)
      ->  VALCLOSED (nth i (map f vl) VNil)).
  Proof.
    (* #1 Pose: intro/pose/destruct/ *)
    itr - A i vl f Hvl Hsucc_lt.
    pse - Nat.succ_lt_mono as Hmono_succ_lt: i (base.length vl).
    des - Hmono_succ_lt as [_ Hfrom_succ_lt].
    (* #2 Apply: apply *)
    app - Hfrom_succ_lt in Hsucc_lt as Hlt; clr - Hfrom_succ_lt.
    bpp - Hvl in Hlt.
  Qed.



  Theorem scope_vl_succ_id :
    forall i vl,
          (i < length vl
      ->  VALCLOSED (nth i vl VNil))
    ->    (S i < S (length vl)
      ->  VALCLOSED (nth i vl VNil)).
  Proof.
    (* #1 Assert: intro/assert/remember + apply *)
    itr - i vl Hvl.
    ass > (map id vl = vl) as Hid: apply Basics.map_id.
    rem - n as Hn: (base.length vl).
    (* #2 Rewrite: rewrite *)
    cwl + Hid in Hvl.
    cwr - Hn in *.
    (* #3 Pose by Previus: pose *)
    by pose proof scope_vl_succ Val i vl id Hvl.
  Qed.



End Succ.









Section Induction.



  Theorem scope_cons :
    forall v1 v2,
        is_result (RValSeq [v1])
    ->  is_result (RValSeq [v2])
    ->  is_result (RValSeq [VCons v1 v2]).
  Proof.
    (* #1 Inversion: intro/inversion/destruct_foralls *)
    itr - v1 v2 Hv1 Hv2.
    ivc - Hv1 as Hv1: H0.
    ivc - Hv2 as Hv2: H0.
    des_for - Hv1 Hv2: H3 H1.
    (* #2 Finish: pose *)
    ato.
  Qed.



  Theorem scope_tuple :
    forall v vl,
        is_result (RValSeq [v])
    ->  is_result (RValSeq [VTuple vl])
    ->  is_result (RValSeq [VTuple (v :: vl)]).
  Proof.
    (* #1 Inversion: intro/inversion/destruct_foralls *)
    itr - v vl Hv Hvl.
    ivc - Hv as Hv: H0.
    ivc - Hvl as Hvl: H0.
    des_for - Hv Hvl: H3 H1.
    (* #3 Constructor: constructor *)
    do 3 cns.
    (* #4 Simplify: intro/simpl *)
    itr - i Hl.
    smp *.
    (* #5 Destruct: destruct + exact *)
    des - i: exa - Hv.
    (* #6 Inversion: inversion *)
    ivc - Hvl as Hvl: H1 / v Hv.
    (* #7 Finish: pose *)
    bse - scope_vl_succ_id: i vl (Hvl i) Hl.
  Qed.



  Theorem scope_map :
    forall v1 v2 vl,
        is_result (RValSeq [v1])
    ->  is_result (RValSeq [v2])
    ->  is_result (RValSeq [VMap vl])
    ->  is_result (RValSeq [VMap ((v1, v2) :: vl)]).
  Proof.
    (* #1 Inversion: intro/inversion/destruct_foralls *)
    itr - v1 v2 vl Hv1 Hv2 Hvl.
    ivc - Hv1 as Hv1: H0.
    ivc - Hv2 as Hv2: H0.
    ivc - Hvl as Hvl: H0.
    des_for - Hv1 Hv2 Hvl: H5 H3 H1.
    (* #3 Constructor: constructor *)
    do 3 cns.
    * (* #4.1 Simplify: intro/simpl *)
      itr - i Hl.
      smp *.
      (* #5.1 Destruct: clear/destruct + exact *)
      clr - Hv2 v2.
      des - i: exa - Hv1.
      (* #6.1 Inversion: inversion *)
      ivc - Hvl as Hvl: H0 / H2 v1 Hv1.
      (* #7.1 Finish: pose *)
      by pose proof scope_vl_succ (Val * Val) i vl fst (Hvl i) Hl.
    * (* #4.2 Simplify: intro/simpl *)
      itr - i Hl.
      smp *.
      (* #5.2 Destruct: clear/destruct + exact *)
      clr - Hv1 v1.
      des - i: exa - Hv2.
      (* #6.2 Inversion: inversion *)
      ivc - Hvl as Hvl: H2 / H0 v2 Hv2.
      (* #7.2 Finish: pose *)
      by pose proof scope_vl_succ (Val * Val) i vl snd (Hvl i) Hl.
  Qed.



End Induction.



















Import SubstSemantics.

(* STRUCTURE:
* Help
  - scope_solver_triv
  - scope_solver_by
  - scope_solver_cons
  - scope_solver_tuple
  - scope_solver_map
* Main
  - scope
*)












(* Help: *)

Ltac scope_solver_triv :=
  constructor;
  solve [scope_solver].

Ltac scope_solver_by H1 :=
  solve [exact H1].

Ltac scope_solver_cons v1 v2 Hresult_v1 Hresult_v2 :=
  pose proof scope_cons v1 v2 Hresult_v1 Hresult_v2;
  solve [auto].

Ltac scope_solver_tuple v vl Hresult_v Hresult_vl :=
  pose proof scope_tuple v vl Hresult_v Hresult_vl;
  solve [auto].

Ltac scope_solver_map v1 v2 vl Hresult_v1 Hresult_v2 Hresult_vl :=
  pose proof scope_map v1 v2 vl Hresult_v1 Hresult_v2 Hresult_vl;
  solve [auto].









(* Main: *)

Tactic Notation "scope"
  :=
  eexists;
  split;
  [ scope_solver_triv
  | idtac ].

Tactic Notation "scope"
  "-"   ident(I1)
  :=
  eexists;
  split;
  [ scope_solver_by I1
  | clear I1].

Tactic Notation "scope"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4)
  :=
  eexists;
  split;
  [ (scope_solver_cons I1 I2 I3 I4
  + scope_solver_tuple I1 I2 I3 I4)
  | clear I3 I4].

Tactic Notation "scope"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5) ident(I6)
  :=
  eexists;
  split;
  [ scope_solver_map I1 I2 I3 I4 I5 I6
  | clear I4 I5 I6].























Import SubstSemantics.

(* STRUCTURE:
* Help
  - do_framestack_step
  - do_framestack_transitive
* Main
  - step
*)












(* Help: *)


Ltac do_framestack_step
  :=
  (econstructor;
  [ (constructor; auto + scope_solver + congruence)
  + (econstructor; constructor)
  + (econstructor;
    [ congruence
    | constructor ])
  | simpl ])
  + (cbn; constructor).



Ltac do_framestack_transitive H
  :=
  eapply transitive_eval;
  [ eapply frame_indep_core in H;
    exact H
  | clear H;
    simpl ].









(* Main: *)

Tactic Notation "step"
  :=
  repeat do_framestack_step.

Tactic Notation "step"
  "-"   hyp(H)
  :=
  repeat do_framestack_step;
  (solve [exact H] + do_framestack_transitive H).

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2 I3.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2 I3 I4.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
    clear I1 I2 I3 I4 I5.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2 I3 I4 I5 I6.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2 I3 I4 I5 I6 I7.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2 I3 I4 I5 I6 I7 I8.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10.

Tactic Notation "step"
  ":"   tactic(T)
  :=
  repeat do_framestack_step + T.

Tactic Notation "step"
  ":"   tactic(T)
  "/"   ident(I1)
  :=
  repeat do_framestack_step + T;
  clear I1.

Tactic Notation "step"
  ":"   tactic(T)
  "/"   ident(I1) ident(I2)
  :=
  repeat (do_framestack_step + T);
  clear I1 I2.

Tactic Notation "step"
  ":"   tactic(T)
  "/"   ident(I1) ident(I2) ident(I3)
  :=
  repeat (do_framestack_step + T);
  clear I1 I2 I3.

Tactic Notation "step"
  ":"   tactic(T)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4)
  :=
  repeat (do_framestack_step + T);
  clear I1 I2 I3 I4.

Tactic Notation "step"
  ":"   tactic(T)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
  :=
  repeat (do_framestack_step + T);
  clear I1 I2 I3 I4 I5.









Import SubstSemantics.

(* STRUCTURE:
* Ident
  - ident_result
  - ident_partial
  - ident_reverse
*)












Section Ident.



  Theorem ident_result :
    forall ident el r vl v' vl' eff Fs,
        create_result ident (vl' ++ v' :: vl) [] = Some (r , eff)
    ->  list_biforall
          (fun e v => ⟨ [] , RExp e ⟩ -->* RValSeq [v])
          el
          vl
    ->  exists k,
          ⟨ FParams ident vl' el :: Fs, RValSeq [v'] ⟩
          -[ k ]->
          ⟨ Fs, r ⟩.
  Proof.
    (* #1 Induction: intro/generalize/revert/induction *)
    itr - ident el.
    ind - el as [| e el Hfs_vl];
      itr - r vl v' vl' eff Fs Hcreate Hbiforall; ivc - Hbiforall.
    * (* #2.1 Constructor: exists/constructor *)
      eei.
      do 2 ens.
      (* #3.1 Exact: symmetry/exact *)
      sym.
      exa - Hcreate.
    * (* #2.2 Specialize: rename/assert/rewrite/specialize *)
      ren - v vl Hfs_v Hbiforall: hd' tl' H1 H3.
      ass > ((vl' ++ v' :: v :: vl) = ((vl' ++ [v']) ++ v :: vl))
        as Hrewrite: rwl - app_assoc; by rewrite <- app_cons_swap.
      cwr - Hrewrite in Hcreate.
      spc - Hfs_vl: r vl v (vl' ++ [v']) eff Fs Hcreate Hbiforall.
      (* #3.2 Destruct: destruct *)
      des - Hfs_v as [kv [_ Hstep_v]].
      des - Hfs_vl as [kvl Hstep_vl].
      (* #4.2 FrameStack: eexist/step *)
      eei.
      step - Hstep_v / kv.
      step - Hstep_vl.
  Qed.



  Theorem ident_partial :
    forall ident el e' el' vl v' vl' Fs,
        list_biforall
          (fun e v => ⟨ [] , RExp e ⟩ -->* RValSeq [v])
          el
          vl
    ->  exists k,
          ⟨ FParams ident vl' (el ++ e' :: el') :: Fs, RValSeq [v'] ⟩
          -[ k ]->
          ⟨ FParams ident (vl' ++ v' :: vl) el' :: Fs, RExp e' ⟩.
  Proof.
    (* #1 Induction: intro/generalize/revert/induction *)
    itr - ident el.
    ind - el as [| e el Hfs_vl];
      itr - e' el' vl v' vl' Fs Hbiforall; ivc - Hbiforall.
    * (* #2.1 Constructor: exists/constructor *)
      eei.
      do 2 ens.
    * (* #2.2 Specialize: rename/assert/rewrite/specialize *)
      ren - v vl Hfs_v Hbiforall: hd' tl' H1 H3.
      ass > ((vl' ++ v' :: v :: vl) = ((vl' ++ [v']) ++ v :: vl))
        as Hrewrite: rwl - app_assoc; by rewrite <- app_cons_swap.
      spc - Hfs_vl: e' el' vl v (vl' ++ [v']) Fs Hbiforall.
      cwl - Hrewrite in Hfs_vl.
      (* #3.2 Destruct: destruct *)
      des - Hfs_v as [kv [_ Hstep_v]].
      des - Hfs_vl as [kvl Hstep_vl].
      (* #4.2 FrameStack: eexist/step *)
      eei.
      step - Hstep_v / kv.
      step - Hstep_vl.
  Qed.



  Theorem ident_reverse :
    forall el e' vl' ident k r,
        ⟨ [FParams ident vl' el], RExp e' ⟩ -[ k ]-> ⟨ [], RValSeq r ⟩
    ->  ident = ITuple \/ ident = IMap
    ->  exists v' vl eff,
            create_result ident (vl' ++ v' :: vl) [] = Some (RValSeq r, eff)
        /\  list_biforall
              (fun (e : Exp) (v : Val) => ⟨ [], RExp e ⟩ -->* RValSeq [v])
              (e' :: el)
              (v' :: vl).
  Proof.
    ind - el; itr - e' vl' ident k r Hstep Hident.
    * ivc - Hident.
      - ivc - Hstep as Hstep1 Hstep2: H H0.
        ivc - Hstep1 as Hstep: Hstep2.
        all: adm.
      - adm.
    * ivc - Hident.
      - ivc - Hstep as Hstep1 Hstep2: H H0.
        ivc - Hstep1 as Hstep: Hstep2.
        all: adm.
    (* Not Provable *)
  Admitted.



End Ident.























Import BigStep.

(* STRUCTURE:
* Generic
  - measure_list
  - measure_map
  - is_none
* Inductive
  - measure_exp_case
  - measure_exp_ext
  - measure_val_env
* Main
  - measure_exp
  - measure_val
  - measure_env
  - measure_env_exp
*)












Section Generic.



  Definition measure_list
    {T : Type}
    (measure : T -> nat)
    (l : list T)
    : nat 
    :=
  list_sum (map measure l).



  Definition measure_map
    {T : Type}
    (measure : T -> nat)
    (ll : list (T * T))
    : nat
    :=
  list_sum (map (fun '(x, y) => (measure x) + (measure y)) ll).



  Definition is_none
    {T : Type}
    (o : option T)
    : bool 
    :=
  match o with
  | Some _ => false
  | None => true
  end.



End Generic.









Section Inductive.



  Definition measure_exp_case
    (measure_exp : Expression -> nat)
    (case : list ((list Pattern) * Expression * Expression))
    : nat
    :=
  list_sum
    (map (fun '(pl, e1, e2) => (measure_exp e1) + (measure_exp e2)) case).



  Definition measure_exp_ext
    {T : Type}
    (measure_exp : Expression -> nat)
    (ext : list (T * FunctionExpression))
    : nat
    :=
  list_sum (map (measure_exp ∘ snd ∘ snd) ext).



  Definition measure_val_env
    (measure_val : Value -> nat)
    (env : Environment)
    : nat
    :=
  list_sum (map (measure_val ∘ snd) env).



End Inductive.









Section Main.



  Fixpoint measure_exp
    (e : Expression)
    : nat
    :=
  match e with

  | ENil => 1
  | ELit _ => 1
  | EVar _ => 1
  | EFunId _ => 1

  | EFun _ e => 1
    + measure_exp e

  | ECons e1 e2 => 1
    + measure_exp e1
    + measure_exp e2

  | ESeq e1 e2 => 1
    + measure_exp e1
    + measure_exp e2

  | ELet _ e1 e2 => 1
    + measure_exp e1
    + measure_exp e2

  | ETry e1 _ e2 _ e3 => 1
    + measure_exp e1
    + measure_exp e2
    + measure_exp e3

  | EValues el => 1
    + measure_list measure_exp el

  | ETuple el => 1
    + measure_list measure_exp el

  | EPrimOp _ el => 1
    + measure_list measure_exp el

  | EMap ell =>  1
    + measure_map measure_exp ell

  | EApp e el => 1
    + measure_exp e
    + measure_list measure_exp el

  | ECall e1 e2 el => 1
    + measure_exp e1
    + measure_exp e2
    + measure_list measure_exp el

  | ECase e case => 1
    + measure_exp e
    + measure_exp_case measure_exp case

  | ELetRec ext e => 1
    + measure_exp e
    + measure_exp_ext measure_exp ext

  end.



  Fixpoint measure_val
    (v : Value) 
    : nat
    :=
  match v with

  | VNil => 1
  | VLit l => 1

  | VCons v1 v2 => 1
    + measure_val v1
    + measure_val v2

  | VTuple vl => 1
    + measure_list measure_val vl

  | VMap vll => 1
    + measure_map measure_val vll

  | VClos env ext _ _ e fid => 1
    + measure_exp e
    + measure_exp_ext measure_exp ext
    + measure_val_env measure_val env

  end.



  Definition measure_env
    (env : Environment)
    : nat
    :=
  list_sum (map (measure_val ∘ snd) env).



  Definition measure_env_exp
    (env : Environment)
    (e : Expression)
    : nat
    :=
  measure_exp e
  + measure_env env.



End Main.































Import BigStep.

(* STRUCTURE:
* Inductive
  - bval_to_bexp_ext
* Main
  - bval_to_bexp
*)












Section Inductive.



  Definition bval_to_bexp_ext
	  (ext : list (nat * FunctionIdentifier * FunctionExpression))
	  : list (FunctionIdentifier * (list Var * Expression))
	  :=
  map
	  (fun '(n, fid, (vl, e)) => (fid, (vl, e)))
	  ext.



End Inductive.









Section Main.



  Fixpoint bval_to_bexp
	  (subst_env : Environment -> Expression -> Expression)
	  (v : Value)
	  : Expression
	  :=
  match v with

  | VNil =>
    ENil

  | VLit lit =>
    ELit lit

  | VCons v1 v2 =>
    ECons
    	(bval_to_bexp subst_env v1)
    	(bval_to_bexp subst_env v2)

  | VTuple vl =>
    ETuple
  	  (map (bval_to_bexp subst_env) vl)

  | VMap vll =>
    EMap
    	(map
      	(prod_map
        	(bval_to_bexp subst_env)
        	(bval_to_bexp subst_env))
      	vll)

  | VClos env ext _ vars e fid =>
    match ext, fid with
    | _ :: _, Some fid' =>
      (subst_env
        env
        (ELetRec (bval_to_bexp_ext ext) (EFunId fid')))
    | _, _ =>
      (subst_env
        env
        (EFun vars e))
    end

  end.



End Main.












Import BigStep.

(* STRUCTURE:
* Subst
  - subst_env
*)












Section Subst.



  Fixpoint subst_env
	  (fuel : nat)
	  (env : Environment)
	  (e : Expression)
	  : Expression
	  :=
  match fuel with
  | O => e
  | S fuel' =>

    match e with

    | ENil =>
      ENil

    | ELit lit =>
      ELit lit

    | ECons e1 e2 =>
      ECons
        (subst_env fuel' env e1)
        (subst_env fuel' env e2)

    | ESeq e1 e2 =>
      ESeq
        (subst_env fuel' env e1)
        (subst_env fuel' env e2)

    | EValues el =>
      EValues
        (map (subst_env fuel' env) el)

    | ETuple el =>
      ETuple
        (map (subst_env fuel' env) el)

    | EPrimOp s el =>
      EPrimOp s
        (map (subst_env fuel' env) el)

    | EApp e el =>
      EApp
        (subst_env fuel' env e)
        (map (subst_env fuel' env) el)

    | ECall e1 e2 el =>
      ECall
        (subst_env fuel' env e1)
        (subst_env fuel' env e2)
        (map (subst_env fuel' env) el)

    | EMap ell =>
      EMap
        (map
          (prod_map
            (subst_env fuel' env)
            (subst_env fuel' env))
          ell)

    | ECase e case =>
      ECase
        (subst_env fuel' env e)
        (map
          (fun '(pl, e1, e2) =>
            (pl,
            (subst_env fuel' env e1),
            (subst_env fuel' env e2)))
          case)

    | EFun vars e =>
      EFun
        vars
        (subst_env fuel' (rem_vars vars env) e)

    | ELet vars e1 e2 =>
      ELet
        vars
        (subst_env fuel' env e1)
        (subst_env fuel' (rem_vars vars env) e2)

    | ETry e1 vars1 e2 vars2 e3 =>
      ETry
        (subst_env fuel' env e1)
        vars1
        (subst_env fuel' (rem_vars vars1 env) e2)
        vars2
        (subst_env fuel' (rem_vars vars2 env) e3)

    | ELetRec ext e =>
      ELetRec
        (map
          (fun '(fid, (vars, body)) =>
            (fid,
            (vars,
            (subst_env fuel' (rem_exp_ext_both vars ext env) body))))
          ext)
        (subst_env fuel' (rem_exp_ext_fids ext env) e)

    | EVar var =>
      match (get_value env (inl var)) with
      | Some [v] => bval_to_bexp (subst_env fuel') v
      | _ => e
      end

    | EFunId fid =>
      match (get_value env (inr fid)) with
      | Some [v] => bval_to_bexp (subst_env fuel') v
      | _ => e
      end

    end
  end.



End Subst.





























Import BigStep.

(* STRUCTURE:
* Subst
  - subst_env_step
*)












Section Subst.


  (*NOTUSED*)
  Lemma subst_env_step :
    forall fuel env e,
      subst_env (1 + fuel) env e
    = match e with

      | ENil =>
        ENil

      | ELit lit =>
        ELit lit

      | ECons e1 e2 =>
        ECons
          (subst_env fuel env e1)
          (subst_env fuel env e2)

      | ESeq e1 e2 =>
        ESeq
          (subst_env fuel env e1)
          (subst_env fuel env e2)

      | EValues el =>
        EValues
          (map (subst_env fuel env) el)

      | ETuple el =>
        ETuple
          (map (subst_env fuel env) el)

      | EPrimOp s el =>
        EPrimOp s
          (map (subst_env fuel env) el)

      | EApp e el =>
        EApp
          (subst_env fuel env e)
          (map (subst_env fuel env) el)

      | ECall e1 e2 el =>
        ECall
          (subst_env fuel env e1)
          (subst_env fuel env e2)
          (map (subst_env fuel env) el)

      | EMap ell =>
        EMap
          (map
            (prod_map
              (subst_env fuel env)
              (subst_env fuel env))
            ell)

      | ECase e case =>
        ECase
          (subst_env fuel env e)
          (map
            (fun '(pl, e1, e2) =>
              (pl,
              (subst_env fuel env e1),
              (subst_env fuel env e2)))
            case)

      | EFun vars e =>
        EFun
          vars
          (subst_env fuel (rem_vars vars env) e)

      | ELet vars e1 e2 =>
        ELet
          vars
          (subst_env fuel env e1)
          (subst_env fuel (rem_vars vars env) e2)

      | ETry e1 vars1 e2 vars2 e3 =>
        ETry
          (subst_env fuel env e1)
          vars1
          (subst_env fuel (rem_vars vars1 env) e2)
          vars2
          (subst_env fuel (rem_vars vars2 env) e3)

      | ELetRec ext e =>
        ELetRec
          (map
            (fun '(fid, (vars, body)) =>
              (fid,
              (vars,
              (subst_env fuel (rem_exp_ext_both vars ext env) body))))
            ext)
          (subst_env fuel (rem_exp_ext_fids ext env) e)

      | EVar var =>
          match (get_value env (inl var)) with
          | Some [v] => bval_to_bexp (subst_env fuel) v
          | _ => e
          end

      | EFunId fid =>
          match (get_value env (inr fid)) with
          | Some [v] => bval_to_bexp (subst_env fuel) v
          | _ => e
          end

      end.
  Proof.
    trv.
  Qed.



End Subst.










































Import BigStep.

(* STRUCTURE:
* Transform
  - literal_to_lit
  - vars_of_pattern_list
* Sum
  - sum_eqb
  - subst_env_step
* NameSub
  - name_sub
  - NameSub
* AddNames
  - add_name
  - add_names
* Adds
  - add_vars
  - add_fids
  - add_exp_ext_fids
  - add_val_ext_fids
  - add_exp_ext_both
  - add_val_ext_both
* Main
  - bpat_to_fbat
  - bexp_to_fexp
  - bval_to_fval
*)












Section Transfrom.



    Definition literal_to_lit
      (lit : Literal)
      : Lit
      :=
    match lit with
     | Atom s => s
     | Integer x => x
    end.



    Definition vars_of_pattern_list
      (pl : list Pattern)
      : list Var
      :=
    fold_right
      (fun x acc => variable_occurances x ++ acc)
      nil
      pl.



End Transfrom.












Section Sum.



  Definition sum_eqb
    {A B : Type}
    (eqbA : A -> A -> bool)
    (eqbB : B -> B -> bool)
    (a b : A + B)
    : bool
    :=
  match a, b with
  | inl a', inl b' => eqbA a' b'
  | inr a', inr b' => eqbB a' b'
  | _, _ => false
  end.



End Sum.












Section NameSub.



  Definition name_sub
    {T}
    {dec : T -> T -> bool}
    :=
  T -> nat.



  Definition NameSub
    :=
  @name_sub
    (Var + FunctionIdentifier)
    (sum_eqb eqb (prod_eqb eqb Nat.eqb)).



End NameSub.












Section AddNames.



  Definition add_name
    {T dec}
    (name : T)
    (fns : @name_sub _ dec)
    :=
  fun x =>
    if dec x name
    then 0
    else S (fns x).



  Definition add_names
    {T}
    {dec : T -> T -> bool}
    (names : list T)
    (fns : name_sub)
    : name_sub
    :=
  fold_right
    (@add_name _ dec)
    fns
    names.



End AddNames.












Section Adds.



  Definition add_vars
    (vars : list Var)
    (fns : NameSub)
    : NameSub
    :=
  add_names (map inl vars) fns.



  Definition add_fids
    (fids : list FunctionIdentifier)
    (fns : NameSub)
    : NameSub
    :=
  add_names (map inr fids) fns.



  Definition add_exp_ext_fids
    (ext : list (FunctionIdentifier * FunctionExpression))
    (fns : NameSub)
    : NameSub
    :=
  add_fids (map fst ext) fns.



  Definition add_val_ext_fids
    (ext : list (nat * FunctionIdentifier * FunctionExpression))
    (fns : NameSub)
    : NameSub
    :=
  add_fids (map (snd ∘ fst) ext) fns.



  Definition add_exp_ext_both
    (vars : list Var)
    (ext : list (FunctionIdentifier * FunctionExpression))
    (fns : NameSub)
    : NameSub
    :=
  add_exp_ext_fids ext (add_vars vars fns).



  Definition add_val_ext_both
    (vars : list Var)
    (ext : list (nat * FunctionIdentifier * FunctionExpression))
    (fns : NameSub)
    : NameSub
    :=
  add_val_ext_fids ext (add_vars vars fns).



  Definition add_pats
    (pats : list Pattern)
    (fns : NameSub)
    : NameSub
    :=
  add_vars (vars_of_pattern_list pats) fns.



End Adds.


















Section Main.






  Fixpoint bpat_to_fpat
    (p : Pattern)
    : Pat
    :=
  match p with

  | PNil =>
    Syntax.PNil

  | PVar _ =>
    Syntax.PVar

  | PLit lit =>
    Syntax.PLit
      (literal_to_lit lit)

  | PCons p1 p2 =>
    Syntax.PCons
      (bpat_to_fpat p1)
      (bpat_to_fpat p2)

  | PTuple pl =>
    Syntax.PTuple
      (map bpat_to_fpat pl)

  | PMap pll =>
    Syntax.PMap
      (map
        (prod_map
          bpat_to_fpat
          bpat_to_fpat)
        pll)

  end.









  Fixpoint bexp_to_fexp
    (fns : NameSub)
    (e : Expression)
    : Exp
    :=
  match e with

  | ENil =>
    ˝Syntax.VNil

  | ELit lit =>
    ˝Syntax.VLit
      (literal_to_lit lit)

  | ECons e1 e2 =>
    Syntax.ECons
      (bexp_to_fexp fns e1)
      (bexp_to_fexp fns e2)

  | ESeq e1 e2 =>
    Syntax.ESeq
      (bexp_to_fexp fns e1)
      (bexp_to_fexp fns e2)

  | EValues el =>
    Syntax.EValues
      (map (bexp_to_fexp fns) el)

  | ETuple el =>
    Syntax.ETuple
      (map (bexp_to_fexp fns) el)

  | EPrimOp s el =>
    Syntax.EPrimOp
      s
      (map (bexp_to_fexp fns) el)

  | EApp e el =>
    Syntax.EApp
      (bexp_to_fexp fns e)
      (map (bexp_to_fexp fns) el)

  | ECall e1 e2 el =>
    Syntax.ECall
      (bexp_to_fexp fns e1)
      (bexp_to_fexp fns e2)
      (map (bexp_to_fexp fns) el)

  | EMap ell =>
    Syntax.EMap
      (map
        (prod_map
          (bexp_to_fexp fns)
          (bexp_to_fexp fns))
        ell)

  | EFun vars e =>
    Syntax.EFun
      (length vars)
      (bexp_to_fexp (add_vars vars fns) e)

  | ELet vars e1 e2 =>
    Syntax.ELet
      (length vars)
      (bexp_to_fexp fns e1)
      (bexp_to_fexp (add_vars vars fns) e2)

  | ETry e1 vars1 e2 vars2 e3 =>
    Syntax.ETry
      (bexp_to_fexp fns e1)
      (length vars1)
      (bexp_to_fexp (add_vars vars1 fns) e2)
      (length vars2)
      (bexp_to_fexp (add_vars vars2 fns) e3)

  | ELetRec ext e =>
    Syntax.ELetRec
      (map
        (fun '(_, (vars, body)) =>
          (length vars,
          bexp_to_fexp (add_exp_ext_both vars ext fns) body))
        ext)
      (bexp_to_fexp (add_exp_ext_fids ext fns) e)

  | ECase e case =>
    Syntax.ECase
      (bexp_to_fexp fns e)
      (map 
        (fun '(pats, e1, e2) =>
          ((map bpat_to_fpat pats),
          bexp_to_fexp (add_pats pats fns) e1,
          bexp_to_fexp (add_pats pats fns) e2))
        case)

  | EVar var =>
    ˝Syntax.VVar
      (fns (inl var))

  | EFunId fid =>
    ˝Syntax.VFunId
      ((fns (inr fid)), snd fid)

  end.









  Fixpoint bval_to_fval
    (fns : NameSub)
    (v : Value)
    : Val
    :=
  match v with

  | VNil =>
    Syntax.VNil

  | VLit lit =>
    Syntax.VLit
      (literal_to_lit lit)

  | VCons v1 v2 =>
    Syntax.VCons
      (bval_to_fval fns v1)
      (bval_to_fval fns v2)

  | VTuple vl =>
    Syntax.VTuple
      (map (bval_to_fval fns) vl)

  | VMap vll =>
    Syntax.VMap
      (map
        (prod_map
          (bval_to_fval fns)
          (bval_to_fval fns))
        vll)

  | VClos env ext _ vars e fid =>
    match ext, fid with
    | _ :: _, Some _ =>
      Syntax.VClos
        (map
          (fun '(n, fid', (vars', body)) =>
            (n,
            length vars',
            bexp_to_fexp
              (add_val_ext_both vars' ext fns)
              (subst_env
                (measure_env_exp (rem_val_ext_both vars' ext env) body)
                (rem_val_ext_both vars' ext env)
                body)))
          ext)
        0
        (length vars)
        (bexp_to_fexp
          (add_val_ext_both vars ext fns)
          (subst_env
            (measure_env_exp (rem_val_ext_fids ext env) e)
            (rem_val_ext_fids ext env)
            e))
    | _, _ =>
      Syntax.VClos
        []
        0
        (length vars)
        (bexp_to_fexp
          (add_vars vars fns)
          (subst_env
            (measure_env_exp (rem_vars vars env) e)
            (rem_vars vars env)
            e))
    end

  end.






End Main.


























Import BigStep.

(* STRUCTURE:
* Convert
  - bexp_to_fexp_subst
  - bvs_to_fvs
  - bec_to_fec
  - bexc_to_fexc
  - bresult_to_fresult
*)












Section Convert.



  Definition bexp_to_fexp_subst
    fns
    (env : Environment)
    (e : Expression)
    : Exp
    :=
  bexp_to_fexp
    fns
    (subst_env
      (measure_env_exp env e)
      env
      e).



  Definition bvs_to_fvs
    fns
    (vs : ValueSequence)
    : ValSeq
    :=
  map
    (bval_to_fval fns)
    vs.



  Definition bec_to_fec
    (ec : ExceptionClass)
    : ExcClass
    :=
  match ec with
  | Error =>  CoreErlang.Syntax.Error
  | Throw =>  CoreErlang.Syntax.Throw
  | Exit =>   CoreErlang.Syntax.Exit
  end.



  Definition bexc_to_fexc
    fns
    (exc : Exception)
    : CoreErlang.Syntax.Exception
    :=
  match exc with
  | (ec, v1, v2) =>
      (bec_to_fec ec,
      bval_to_fval fns v1,
      bval_to_fval fns v2)
  end.



  Definition bresult_to_fresult
    fns
    (result : (ValueSequence + Exception))
    : Redex
    :=
  match result with
  | inl vs =>   RValSeq (bvs_to_fvs fns vs)
  | inr exc =>  RExc (bexc_to_fexc fns exc)
  end.



End Convert.






















From CoreErlang.Eq.BsFs Require Export B17ConvertDefinitions.

Import BigStep.

(* STRUCTURE:
* Trivial
  - trv_le_solver
* Less or Equal
  - ass_le
  - as_le_trn
* Measure Reduction Value Solver
  - mred_solver
* Measure Reduction Expression Solver
  - mred_solver
*)












(* Trivial *)

Ltac trv_le_solver := 
  smp;
  try unfold measure_env_exp;
  try unfold measure_env;
  try unfold measure_list;
  try unfold measure_map;
  try rewrite map_app, list_sum_app;
  sli.






(* Less or Equal *)

Tactic Notation "ass_le"
  "as"  ident(Ile)
  ":"   constr(Cle)
  :=
  assert Cle as Ile by trv_le_solver.

Tactic Notation "ass_le"
  ">"   constr(Cle)
  "as"  ident(Ile)
  ":"   hyp(Hm1) hyp(Hm2)
  :=
  assert Cle as Ile by
    (rewrite Hm1, Hm2;
    trv_le_solver).

Tactic Notation "ass_le"
  ">"   constr(Cle)
  "as"  ident(Ile)
  ":"   hyp(Hm1) hyp(Hm2) hyp(Hm3)
  :=
  assert Cle as Ile by
    (rewrite Hm1, Hm2, Hm3;
    trv_le_solver).



Tactic Notation "ass_le_trn"
  ">"   constr(Cle_n1_n3)
  "as"  ident(Ile_n1_n3)
  ":"   hyp(Hle_n1_n2) hyp(Hle_n2_n3)
  :=
  assert Cle_n1_n3 as Ile_n1_n3 by
    (eapply Nat.le_trans;
      [exact Hle_n1_n2 | exact Hle_n2_n3]).

Tactic Notation "ass_le_trn"
  ">"   constr(Cle_n1_n4)
  "as"  ident(Ile_n1_n4)
  ":"   hyp(Hle_n1_n2) hyp(Hle_n2_n3) hyp(Hle_n3_n4)
  :=
  assert Cle_n1_n4 as Ile_n1_n4 by
    (eapply Nat.le_trans;
      [eapply Nat.le_trans;
        [exact Hle_n1_n2 | exact Hle_n2_n3]
      | exact Hle_n3_n4]).






(* Measure Reduction Value Solver *)

Tactic Notation "mred_solver"
  "-" ident(v) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(mv) constr(n1) constr(n2)
  :=
  ass_le as Hle1: (mv <= n1);
  ass_le as Hle2: (mv <= n2);
  solve [ase - theorem: v n1 n2 Hle1 Hle2].

Tactic Notation "mred_solver"
  "-" ident(v) ident(n1) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(mv) constr(n2)
  :=
  ass_le as Hle2: (mv <= n2);
  solve [ase - theorem: v n1 n2 Hle1 Hle2].

Tactic Notation "mred_solver"
  "-" ident(v) ident(n1) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(n2)
  :=
  ass_le as Hle2: (n2 <= n2);
  solve [ase - theorem: v n1 n2 Hle1 Hle2].

Tactic Notation "mred_solver"
  "-" ident(v) ident(Hle)
  ":" constr(theorem) constr(mv) constr(n)
  :=
  ass_le as Hle: (mv <= n);
  solve [ase - theorem: v n Hle].






(* Measure Reduction Expression Solver *)

Tactic Notation "mred_solver"
  "-" ident(env) ident(e) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(me) constr(n1) constr(n2)
  :=
  ass_le as Hle1: (me <= n1);
  ass_le as Hle2: (me <= n2);
  solve [ase - theorem: env e n1 n2 Hle1 Hle2].

Tactic Notation "mred_solver"
  "-" ident(env) ident(e) ident(n1) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(me) constr(n2)
  :=
  ass_le as Hle2: (me <= n2);
  solve [ase - theorem: env e n1 n2 Hle1 Hle2].

Tactic Notation "mred_solver"
  "-" ident(env) ident(e) ident(n1) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(n2)
  :=
  ass_le as Hle2: (n2 <= n2);
  solve [ase - theorem: env e n1 n2 Hle1 Hle2].

Tactic Notation "mred_solver"
  "-" ident(env) ident(e) ident(Hle)
  ":" constr(theorem) constr(me) constr(n)
  :=
  ass_le as Hle: (me <= n);
  solve [ase - theorem: env e n Hle].

Tactic Notation "mred_solver"
  ">" constr(env) ident(e) ident(Hle)
  ":" constr(theorem) constr(me) constr(n)
  :=
  ass_le as Hle: (me <= n);
  solve [ase - theorem: env e n Hle].
























From CoreErlang.Eq.BsFs Require Export B18MeasureReductionTactics.

Import BigStep.

(* STRUCTURE:
* Help
  - measure_exp_notzero
* Environment
  - measure_env_eq
  - measure_env_rem_keys_le
  - measure_env_rem_vars_le
  - measure_env_rem_fids_le
  - measure_env_rem_exp_ext_fids_le
  - measure_env_rem_val_ext_fids_le
  - measure_env_rem_exp_ext_both_le
  - measure_env_rem_val_ext_both_le
* Value
  - mred_vcons
  - mred_vtuple
  - mred_vmap
  - mred_vclos
  - mred_val
* Expression
  - mred_exp
* Seperate
  - mred_exp_seperate
  - mred_exp_onlyexp
  - mred_exp_onlyenv
* Mappers
  - mred_val_list
  - mred_val_map
  - mred_exp_list
  - mred_exp_map
* Minimum
  - mred_val_min
  - mred_val_list_min
  - mred_val_map_min
  - mred_exp_min
  - mred_exp_onlyexp_min
  - mred_exp_onlyenv_min
  - mred_exp_list_min
  - mred_exp_map_min
  - mred_exp_list_split_min
  - mred_exp_map_split_min
* Inductive Value
  - mred_vcons_v1
  - mred_vcons_v2
  - mred_v1v2_v1 ?
  - mred_v1v2_v2 ?
  - mred_vtuple_v
  - mred_vtuple_vl
  - mred_vvl_v
  - mred_vvl_vl
  - mred_vmap_v1
  - mred_vmap_v2
  - mred_vmap_vll
  - mred_v1v2vll_v1
  - mred_v1v2vll_v2
  - mred_v1v2vll_vll
* Inductive Expression
  - mred_e_rem_vars
  - mred_eext_e_rem_vars
  - mred_e1e2_e1
  - mred_e1e2_e2
  - mred_e1e2_e2_rem_vars
  - mred_e1e2e3_e1
  - mred_e1e2e3_e2_rem_vars
  - mred_e1e2e3_e3_rem_vars
  - mred_eel_e
  - mred_eel_el
  - mred_e1e2ell_e1
  - mred_e1e2ell_e2
  - mred_e1e2ell_ell
  - mred_expel_exp
  - mred_expel_el
*)












Section Help.



  Lemma measure_exp_notzero :
    forall e,
      measure_exp e <> 0.
  Proof.
    (* #1 Induction: intro/induction + simpl/congruence *)
    itr.
    ind - e; smp; con.
  Qed.



End Help.












Section Environment.



  Lemma measure_env_eq :
    forall env,
      measure_env env = measure_val_env measure_val env.
  Proof.
    (* #1 Trivial: intro/unfold/trival *)
    itr.
    ufl - measure_env measure_val_env.
    trv.
  Qed.



  Lemma measure_env_rem_keys_le :
    forall env keys,
    measure_env (rem_keys keys env) <= measure_env env.
  Proof.
    (* #1 Induction on Environment: intro/induction + simpl *)
    itr.
    ind - env as [| [k v] env Hle_e1k_e1]: smp.
    (* #2 Pose Cons: remember/pose/subst *)
    rem - env' as Heq_env:
      (rem_keys keys ((k, v) :: env)).
    pse - rem_keys_cons_env as Hcons: keys k v env env' Heq_env.
    sbt.
    (* #3 Destruct Cons: destuct + rewrite *)
    des - Hcons; cwr - H in *.
    * (* #4.1 Assert Le: assert/lia + trv_le_solver *)
      ass - as Hle_e1_e2: trv_le_solver >
        (measure_env env <= measure_env ((k, v) :: env)).
      lia.
    * (* #4.2 Solve by Lia: unfold/simpl/lia *)
      ufl + measure_env in Hle_e1k_e1.
      sli.
  Qed.



  Lemma measure_env_rem_vars_le :
    forall env vars,
    measure_env (rem_vars vars env) <= measure_env env.
  Proof.
    (* #1 Prove by Previus Theorem: intro/unfold/pose *)
    itr.
    ufl - rem_vars.
    bse - measure_env_rem_keys_le.
  Qed.



  Lemma measure_env_rem_fids_le :
    forall env fids,
    measure_env (rem_fids fids env) <= measure_env env.
  Proof.
    (* #1 Prove by Previus Theorem: intro/unfold/pose *)
    itr.
    ufl - rem_fids.
    bse - measure_env_rem_keys_le.
  Qed.



  Lemma measure_env_rem_exp_ext_fids_le :
    forall env ext,
    measure_env (rem_exp_ext_fids ext env) <= measure_env env.
  Proof.
    (* #1 Prove by Previus Theorem: intro/unfold/pose *)
    itr.
    ufl - rem_exp_ext_fids.
    bse - measure_env_rem_fids_le.
  Qed.



  Lemma measure_env_rem_val_ext_fids_le :
    forall env ext,
    measure_env (rem_val_ext_fids ext env) <= measure_env env.
  Proof.
    (* #1 Prove by Previus Theorem: intro/unfold/pose *)
    itr.
    ufl - rem_val_ext_fids.
    bse - measure_env_rem_fids_le.
  Qed.



  Lemma measure_env_rem_exp_ext_both_le :
    forall env vars ext,
    measure_env (rem_exp_ext_both vars ext env) <= measure_env env.
  Proof.
    (* #1 Prove by Previus Theorems: intro/unfold/pose/lia *)
    itr.
    ufl - rem_exp_ext_both.
    pse - measure_env_rem_vars_le as Hvars: env vars.
    pse - measure_env_rem_exp_ext_fids_le as Hext: (rem_vars vars env) ext.
    lia.
  Qed.



  Lemma measure_env_rem_val_ext_both_le :
    forall env vars ext,
    measure_env (rem_val_ext_both vars ext env) <= measure_env env.
  Proof.
    (* #1 Prove by Previus Theorems: intro/unfold/pose/lia *)
    itr.
    ufl - rem_val_ext_both.
    pse - measure_env_rem_vars_le as Hvars: env vars.
    pse - measure_env_rem_val_ext_fids_le as Hext: (rem_vars vars env) ext.
    lia.
  Qed.



End Environment.












Section Value.



  Theorem mred_vcons :
      forall v1 v2 n1 n2,
          measure_val (VCons v1 v2) <= n1
      ->  measure_val (VCons v1 v2) <= n2
      ->  ( measure_val v1 <= n1
        ->  measure_val v1 <= n2
        ->  bval_to_bexp (subst_env n1) v1
          = bval_to_bexp (subst_env n2) v1)
      ->  ( measure_val v2 <= n1
        ->  measure_val v2 <= n2
        ->  bval_to_bexp (subst_env n1) v2
          = bval_to_bexp (subst_env n2) v2)
      ->  bval_to_bexp (subst_env n1) (VCons v1 v2)
        = bval_to_bexp (subst_env n2) (VCons v1 v2).
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - v1 v2 n1 n2 Hle_v1v2_n1 Hle_v1v2_n2 Heq_v1 Heq_v2.
    (* #2 Remember: destruct/simpl/remember *)
    rem - mv1 mv2 mv1v2 as Hmv1 Hmv2 Hmv1v2:
      (measure_val v1)
      (measure_val v2)
      (measure_val (VCons v1 v2)).
    (* #3 Assert: assert *)
    ass_le > (mv1 <= mv1v2) as Hle_v1_v1v2: Hmv1 Hmv1v2.
    ass_le > (mv2 <= mv1v2) as Hle_v2_v1v2: Hmv2 Hmv1v2.
    ass_le_trn > (mv1 <= n1) as Hle_v1_n1: Hle_v1_v1v2 Hle_v1v2_n1.
    ass_le_trn > (mv1 <= n2) as Hle_v1_n2: Hle_v1_v1v2 Hle_v1v2_n2.
    ass_le_trn > (mv2 <= n1) as Hle_v2_n1: Hle_v2_v1v2 Hle_v1v2_n1.
    ass_le_trn > (mv2 <= n2) as Hle_v2_n2: Hle_v2_v1v2 Hle_v1v2_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmv1 Hmv2 Hmv1v2 in *.
    clr + Heq_v1 Heq_v2 Hle_v1_n1 Hle_v1_n2 Hle_v2_n1 Hle_v2_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_v1: Hle_v1_n1 Hle_v1_n2.
    spc - Heq_v2: Hle_v2_n1 Hle_v2_n2.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_v1 Heq_v2.
  Qed.






  Theorem mred_vtuple :
    forall vl n1 n2,
        measure_val (VTuple vl) <= n1
    ->  measure_val (VTuple vl) <= n2
    ->  Forall (fun v =>
            measure_val v <= n1
        ->  measure_val v <= n2
        ->  bval_to_bexp (subst_env n1) v
          = bval_to_bexp (subst_env n2) v)
          vl
    ->  bval_to_bexp (subst_env n1) (VTuple vl)
      = bval_to_bexp (subst_env n2) (VTuple vl).
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - vl n1 n2 Hle_vvl_n1 Hle_vvl_n2 HForall.
    ind - vl as [| v vl Heq_vl]: bmp.
    ivc - HForall as Heq_v HForall: H1 H2.
    (* #2 Remember: destruct/simpl/remember *)
    rem - mv mvl mvvl as Hmv Hmvl Hmvvl:
      (measure_val v)
      (measure_val (VTuple vl))
      (measure_val (VTuple (v :: vl))).
    (* #3 Assert: assert *)
    ass_le > (mv <= mvvl) as Hle_v_vvl: Hmv Hmvvl.
    ass_le > (mvl <= mvvl) as Hle_vl_vvl: Hmvl Hmvvl.
    ass_le_trn > (mv <= n1) as Hle_v_n1: Hle_v_vvl Hle_vvl_n1.
    ass_le_trn > (mv <= n2) as Hle_v_n2: Hle_v_vvl Hle_vvl_n2.
    ass_le_trn > (mvl <= n1) as Hle_vl_n1: Hle_vl_vvl Hle_vvl_n1.
    ass_le_trn > (mvl <= n2) as Hle_vl_n2: Hle_vl_vvl Hle_vvl_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmv Hmvl Hmvvl in *.
    clr + Heq_v Heq_vl HForall Hle_v_n1 Hle_v_n2 Hle_vl_n1 Hle_vl_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_v: Hle_v_n1 Hle_v_n2.
    spc - Heq_vl: Hle_vl_n1 Hle_vl_n2 HForall.
    inj - Heq_vl as Heq_vl.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_v Heq_vl.
  Qed.






  Theorem mred_vmap :
    forall vll n1 n2,
        measure_val (VMap vll) <= n1
    ->  measure_val (VMap vll) <= n2
    ->  Forall (fun v =>
           (measure_val v.1 <= n1
        ->  measure_val v.1 <= n2
        ->  bval_to_bexp (subst_env n1) v.1
          = bval_to_bexp (subst_env n2) v.1)
        /\ (measure_val v.2 <= n1
        ->  measure_val v.2 <= n2
        ->  bval_to_bexp (subst_env n1) v.2
          = bval_to_bexp (subst_env n2) v.2))
          vll
    ->  bval_to_bexp (subst_env n1) (VMap vll)
      = bval_to_bexp (subst_env n2) (VMap vll).
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - vll n1 n2 Hle_vvll_n1 Hle_vvll_n2 HForall.
    ind - vll as [| v vll Heq_vll]: bmp.
    ivc - HForall as Heq_v HForall: H1 H2.
    (* #2 Remember: destruct/simpl/remember *)
    des - v as [v1 v2].
    des - Heq_v as [Heq_v1 Heq_v2].
    smp - Heq_v1 Heq_v2.
    rem - mv1 mv2 mv mvll mvvll as Hmv1 Hmv2 Hmv Hmvll Hmvvll:
      (measure_val v1)
      (measure_val v2)
      (measure_val v1 + measure_val v2)
      (measure_val (VMap vll))
      (measure_val (VMap ((v1, v2) :: vll))).
    (* #3 Assert: assert *)
    ass_le > (mv1 <= mv) as Hle_v1_v: Hmv1 Hmv.
    ass_le > (mv2 <= mv) as Hle_v2_v: Hmv2 Hmv.
    ass_le > (mv <= mvvll) as Hle_v_vvll: Hmv Hmvvll.
    ass_le > (mvll <= mvvll) as Hle_vll_vvll: Hmvll Hmvvll.
    ass_le_trn > (mv1 <= n1) as Hle_v1_n1: Hle_v1_v Hle_v_vvll Hle_vvll_n1.
    ass_le_trn > (mv1 <= n2) as Hle_v1_n2: Hle_v1_v Hle_v_vvll Hle_vvll_n2.
    ass_le_trn > (mv2 <= n1) as Hle_v2_n1: Hle_v2_v Hle_v_vvll Hle_vvll_n1.
    ass_le_trn > (mv2 <= n2) as Hle_v2_n2: Hle_v2_v Hle_v_vvll Hle_vvll_n2.
    ass_le_trn > (mvll <= n1) as Hle_vll_n1: Hle_vll_vvll Hle_vvll_n1.
    ass_le_trn > (mvll <= n2) as Hle_vll_n2: Hle_vll_vvll Hle_vvll_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmv1 Hmv2 Hmv Hmvll Hmvvll in *.
    clr + Heq_v1 Heq_v2 Heq_vll HForall
      Hle_v1_n1 Hle_v1_n2 Hle_v2_n1 Hle_v2_n2 Hle_vll_n1 Hle_vll_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_v1: Hle_v1_n1 Hle_v1_n2.
    spc - Heq_v2: Hle_v2_n1 Hle_v2_n2.
    spc - Heq_vll: Hle_vll_n1 Hle_vll_n2 HForall.
    inj - Heq_vll as Heq_vll.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_v1 Heq_v2 Heq_vll.
  Qed.






  Theorem mred_vclos :
    forall env ext id vars e fid n1 n2,
        measure_val (VClos env ext id vars e fid) <= n1
    ->  measure_val (VClos env ext id vars e fid) <= n2
    ->  Forall (fun x =>
            measure_val x.2 <= n1
        ->  measure_val x.2 <= n2
        ->  bval_to_bexp (subst_env n1) x.2
          = bval_to_bexp (subst_env n2) x.2)
          env
    ->  bval_to_bexp (subst_env n1) (VClos env ext id vars e fid)
      = bval_to_bexp (subst_env n2) (VClos env ext id vars e fid).
  Proof.
    itr - env ext id vars e fid n1 n2 Hle_env_n1 Hle_env_n2 HForall.
    (* Problem: HForall only talks about env, but not of e & ext *)
    admit.
    (* Not Provable / Not True *)
  Admitted.






  Theorem mred_val :
    forall v n1 n2,
        measure_val v <= n1
    ->  measure_val v <= n2
    ->  bval_to_bexp (subst_env n1) v
      = bval_to_bexp (subst_env n2) v.
  Proof.
    (* #1 Value Induction: intro/induction + cbn *)
    itr - v n1 n2 Hn1 Hn2.
    ind ~ ind_val - v :- sbn.
    (* #2 Cons: pose *)
    1: bse - mred_vcons:  v1 v2 n1 n2
                          Hn1 Hn2 IHv1 IHv2.
    (* #3 Tuple: pose *)
    2: bse - mred_vtuple: l n1 n2
                          Hn1 Hn2 H.
    (* #4 Map: pose *)
    2: bse - mred_vmap:   l n1 n2
                          Hn1 Hn2 H.
    (* #5 Closure: pose *)
    bse - mred_vclos:     ref ext id params body funid n1 n2
                          Hn1 Hn2 H.
  Qed.



End Value.












Section Expression.



  Theorem mred_exp :
    forall env e n1 n2,
        measure_env_exp env e <= n1
    ->  measure_env_exp env e <= n2
    ->  subst_env n1 env e
      = subst_env n2 env e.
  Proof.
    (* Not Provable / Not True *)
  Admitted.



End Expression.












Section Separate.



  Theorem mred_exp_separate :
    forall env e ne1 ne2 nenv1 nenv2,
        measure_exp e <= ne1
    ->  measure_exp e <= ne2
    ->  measure_env env <= nenv1
    ->  measure_env env <= nenv2
    ->  subst_env (ne1 + nenv1) env e
      = subst_env (ne2 + nenv2) env e.
  Proof.
    (* #1 Pose Larger or Equal Mono: intro/pose + clear *)
    itr - env e ne1 ne2 nenv1 nenv2 Hle_e1 Hle_e2 Hle_env1 Hle_env2.
    psc - Nat.add_le_mono as Hle1:
      (measure_exp e) ne1
      (measure_env env) nenv1
      Hle_e1 Hle_env1.
    psc - Nat.add_le_mono as Hle2:
      (measure_exp e) ne2
      (measure_env env) nenv2
      Hle_e2 Hle_env2.
    (* #2 Prove by Previus Theorem: pose/unfold/specialize *)
    pse - mred_exp as Heq: env e (ne1 + nenv1) (ne2 + nenv2).
    ufl - measure_env_exp in Heq.
    bpe - Heq: Hle1 Hle2.
  Qed.



  Theorem mred_exp_only_exp :
    forall env e n1 n2,
        measure_exp e <= n1
    ->  measure_exp e <= n2
    ->  subst_env (n1 + measure_env env) env e
      = subst_env (n2 + measure_env env) env e.
  Proof.
    (* #1 Prove by Previus Theorem: intro/assert/pose *)
    itr - env e n1 n2 Hle1 Hle2.
    ass > (measure_env env <= measure_env env) as Hle_env: lia.
    bse - mred_exp_separate:  env e n1 n2 (measure_env env) (measure_env env)
                              Hle1 Hle2 Hle_env Hle_env.
  Qed.



  Theorem mred_exp_only_env :
    forall env e n1 n2,
        measure_env env <= n1
    ->  measure_env env <= n2
    ->  subst_env (measure_exp e + n1) env e
      = subst_env (measure_exp e + n2) env e.
  Proof.
    (* #1 Prove by Previus Theorem: intro/assert/pose *)
    itr - env e n1 n2 Hle1 Hle2.
    ass > (measure_exp e <= measure_exp e) as Hle_e: lia.
    bse - mred_exp_separate:  env e (measure_exp e) (measure_exp e) n1 n2 
                              Hle_e Hle_e Hle1 Hle2.
  Qed.



End Separate.












Section Mappers.



  Theorem mred_val_list :
    forall vl n1 n2,
        list_sum (map measure_val vl) <= n1
    ->  list_sum (map measure_val vl) <= n2
    ->  map (bval_to_bexp (subst_env n1)) vl
      = map (bval_to_bexp (subst_env n2)) vl.
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - vl n1 n2 Hle_vvl_n1 Hle_vvl_n2.
    ind - vl as [| v vl Heq_vl]: bmp.
    (* #2 Remember: destruct/simpl/remember *)
    rem - mv mvl mvvl as Hmv Hmvl Hmvvl:
      (measure_val v)
      (list_sum (map measure_val vl))
      (list_sum (map measure_val (v :: vl))).
    (* #3 Assert: assert *)
    ass_le > (mv <= mvvl) as Hle_v_vvl: Hmv Hmvvl.
    ass_le > (mvl <= mvvl) as Hle_vl_vvl: Hmvl Hmvvl.
    ass_le_trn > (mv <= n1) as Hle_v_n1: Hle_v_vvl Hle_vvl_n1.
    ass_le_trn > (mv <= n2) as Hle_v_n2: Hle_v_vvl Hle_vvl_n2.
    ass_le_trn > (mvl <= n1) as Hle_vl_n1: Hle_vl_vvl Hle_vvl_n1.
    ass_le_trn > (mvl <= n2) as Hle_vl_n2: Hle_vl_vvl Hle_vvl_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmv Hmvl Hmvvl in *.
    clr + Heq_vl Hle_v_n1 Hle_v_n2 Hle_vl_n1 Hle_vl_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_vl: Hle_vl_n1 Hle_vl_n2.
    psc - mred_val as Heq_v: v n1 n2 Hle_v_n1 Hle_v_n2.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_v Heq_vl.
  Qed.






  Theorem mred_val_map :
    forall vll n1 n2,
        list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vll)
          <= n1
    ->  list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vll)
          <= n2
    ->  map
          (prod_map
            (bval_to_bexp (subst_env n1))
            (bval_to_bexp (subst_env n1)))
          vll
      = map
          (prod_map
            (bval_to_bexp (subst_env n2))
            (bval_to_bexp (subst_env n2)))
          vll.
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - vll n1 n2 Hle_vvll_n1 Hle_vvll_n2.
    ind - vll as [| v vll Heq_vll]: bmp.
    (* #2 Remember: destruct/simpl/remember *)
    des - v as [v1 v2].
    rem - mv1 mv2 mv mvll mvvll as Hmv1 Hmv2 Hmv Hmvll Hmvvll:
      (measure_val v1)
      (measure_val v2)
      (measure_val v1 + measure_val v2)
      (list_sum (map (fun '(x, y) => measure_val x + measure_val y) vll))
      (list_sum (map (fun '(x, y) => measure_val x + measure_val y)
        ((v1, v2) :: vll))).
    (* #3 Assert: assert *)
    ass_le > (mv1 <= mv) as Hle_v1_v: Hmv1 Hmv.
    ass_le > (mv2 <= mv) as Hle_v2_v: Hmv2 Hmv.
    ass_le > (mv <= mvvll) as Hle_v_vvll: Hmv Hmvvll.
    ass_le > (mvll <= mvvll) as Hle_vll_vvll: Hmvll Hmvvll.
    ass_le_trn > (mv1 <= n1) as Hle_v1_n1: Hle_v1_v Hle_v_vvll Hle_vvll_n1.
    ass_le_trn > (mv1 <= n2) as Hle_v1_n2: Hle_v1_v Hle_v_vvll Hle_vvll_n2.
    ass_le_trn > (mv2 <= n1) as Hle_v2_n1: Hle_v2_v Hle_v_vvll Hle_vvll_n1.
    ass_le_trn > (mv2 <= n2) as Hle_v2_n2: Hle_v2_v Hle_v_vvll Hle_vvll_n2.
    ass_le_trn > (mvll <= n1) as Hle_vll_n1: Hle_vll_vvll Hle_vvll_n1.
    ass_le_trn > (mvll <= n2) as Hle_vll_n2: Hle_vll_vvll Hle_vvll_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmv1 Hmv2 Hmv Hmvll Hmvvll in *.
    clr + Heq_vll Hle_v1_n1 Hle_v1_n2 Hle_v2_n1 Hle_v2_n2 Hle_vll_n1 Hle_vll_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_vll: Hle_vll_n1 Hle_vll_n2.
    psc - mred_val as Heq_v1: v1 n1 n2 Hle_v1_n1 Hle_v1_n2.
    psc - mred_val as Heq_v2: v2 n1 n2 Hle_v2_n1 Hle_v2_n2.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_v1 Heq_v2 Heq_vll.
  Qed.






  Theorem mred_exp_list :
    forall env el n1 n2,
        list_sum (map measure_exp el) + measure_env env <= n1
    ->  list_sum (map measure_exp el) + measure_env env <= n2
    ->  map (subst_env n1 env) el
      = map (subst_env n2 env) el.
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - env el n1 n2 Hle_eel_n1 Hle_eel_n2.
    ind - el as [| e el Heq_el]: bmp.
    (* #2 Remember: destruct/simpl/remember *)
    rem - menv me mel meel as Hmenv Hme Hmel Hmeel:
      (measure_env env)
      (measure_exp e)
      (list_sum (map measure_exp el))
      (list_sum (map measure_exp (e :: el))).
    (* #3 Assert: assert *)
    ass_le > (me + menv <= meel + menv) as Hle_e_eel: Hme Hmeel Hmenv.
    ass_le > (mel + menv <= meel + menv) as Hle_el_eel: Hmel Hmeel Hmenv.
    ass_le_trn > (me + menv <= n1) as Hle_e_n1: Hle_e_eel Hle_eel_n1.
    ass_le_trn > (me + menv <= n2) as Hle_e_n2: Hle_e_eel Hle_eel_n2.
    ass_le_trn > (mel + menv <= n1) as Hle_el_n1: Hle_el_eel Hle_eel_n1.
    ass_le_trn > (mel + menv <= n2) as Hle_el_n2: Hle_el_eel Hle_eel_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmenv Hme Hmel Hmeel in *.
    clr + Heq_el Hle_e_n1 Hle_e_n2 Hle_el_n1 Hle_el_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_el: Hle_el_n1 Hle_el_n2.
    psc - mred_exp as Heq_e: env e n1 n2 Hle_e_n1 Hle_e_n2.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_e Heq_el.
  Qed.






  Theorem mred_exp_map :
    forall env ell n1 n2,
        list_sum (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) ell)
           + measure_env env <= n1
    ->  list_sum (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) ell)
          + measure_env env <= n2
    ->  map
          (prod_map
            (subst_env n1 env)
            (subst_env n1 env))
          ell
      = map
          (prod_map
            (subst_env n2 env)
            (subst_env n2 env))
          ell.
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - env ell n1 n2 Hle_eell_n1 Hle_eell_n2.
    ind - ell as [| e ell Heq_ell]: bmp.
    (* #2 Remember: destruct/simpl/remember *)
    des - e as [e1 e2].
    rem - menv me1 me2 me mell meell as Hmenv Hme1 Hme2 Hme Hmell Hmeell:
      (measure_env env)
      (measure_exp e1)
      (measure_exp e2)
      (measure_exp e1 + measure_exp e2)
      (list_sum (map (fun '(x, y) => measure_exp x + measure_exp y) ell))
      (list_sum (map (fun '(x, y) => measure_exp x + measure_exp y)
        ((e1, e2) :: ell))).
    (* #3 Assert: assert *)
    ass_le > (me1 + menv <= me + menv) as Hle_e1_e: Hme1 Hme Hmenv.
    ass_le > (me2 + menv <= me + menv) as Hle_e2_e: Hme2 Hme Hmenv.
    ass_le > (me + menv <= meell + menv) as Hle_e_eell: Hme Hmeell Hmenv.
    ass_le > (mell + menv <= meell + menv) as Hle_ell_eell: Hmell Hmeell Hmenv.
    ass_le_trn > (me1 + menv <= n1) as Hle_e1_n1: Hle_e1_e Hle_e_eell Hle_eell_n1.
    ass_le_trn > (me1 + menv <= n2) as Hle_e1_n2: Hle_e1_e Hle_e_eell Hle_eell_n2.
    ass_le_trn > (me2 + menv <= n1) as Hle_e2_n1: Hle_e2_e Hle_e_eell Hle_eell_n1.
    ass_le_trn > (me2 + menv <= n2) as Hle_e2_n2: Hle_e2_e Hle_e_eell Hle_eell_n2.
    ass_le_trn > (mell + menv <= n1) as Hle_ell_n1: Hle_ell_eell Hle_eell_n1.
    ass_le_trn > (mell + menv <= n2) as Hle_ell_n2: Hle_ell_eell Hle_eell_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmenv Hme1 Hme2 Hme Hmell Hmeell in *.
    clr + Heq_ell Hle_e1_n1 Hle_e1_n2 Hle_e2_n1 Hle_e2_n2 Hle_ell_n1 Hle_ell_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_ell: Hle_ell_n1 Hle_ell_n2.
    psc - mred_exp as Heq_e1: env e1 n1 n2 Hle_e1_n1 Hle_e1_n2.
    psc - mred_exp as Heq_e2: env e2 n1 n2 Hle_e2_n1 Hle_e2_n2.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_e1 Heq_e2 Heq_ell.
  Qed.



End Mappers.












Section Minimum.



  Theorem mred_val_min :
    forall v n,
        measure_val v <= n
    ->  bval_to_bexp (subst_env n) v
    =   bval_to_bexp (subst_env (measure_val v)) v.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr - v n Hle1.
    mred_solver - v n Hle1 Hle2:
      mred_val
      (measure_val v)
      (measure_val v).
  Qed.






  Theorem mred_val_list_min :
    forall vl n,
        list_sum (map measure_val vl) <= n
    ->  map (bval_to_bexp (subst_env n)) vl
      = map (bval_to_bexp (subst_env (list_sum (map measure_val vl)))) vl.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr - vl n Hle1.
    mred_solver - vl n Hle1 Hle2:
      mred_val_list
      (list_sum (map measure_val vl)).
  Qed.






  Theorem mred_val_map_min :
    forall vll n,
        list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vll)
          <= n
    ->  map
          (prod_map
            (bval_to_bexp (subst_env n))
            (bval_to_bexp (subst_env n)))
          vll
      = map
          (prod_map
            (bval_to_bexp
              (subst_env
                (list_sum
                  (map
                    (fun '(x, y) => (measure_val x) + (measure_val y))
                    vll))))
            (bval_to_bexp
              (subst_env
                (list_sum
                  (map
                    (fun '(x, y) => (measure_val x) + (measure_val y))
                    vll)))))
          vll.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr - vll n Hle1.
    mred_solver - vll n Hle1 Hle2:
      mred_val_map
      (list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vll)).
  Qed.






  Theorem mred_exp_min :
    forall env e n,
        measure_env_exp env e <= n
    ->  subst_env n env e
    =   subst_env (measure_env_exp env e) env e.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr -  env e n Hle1.
    mred_solver - env e n Hle1 Hle2:
      mred_exp
      (measure_env_exp env e).
  Qed.






  Theorem mred_exp_only_exp_min :
    forall env e n m,
        measure_exp e <= n
    ->  measure_env env <= m
    ->  subst_env (n + m) env e
    =   subst_env (measure_exp e + m) env e.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr -  env e n m Hle_e Hle_env.
    app - mred_exp_separate; lia.
  Qed.






  Theorem mred_exp_only_env_min :
    forall env e n m,
        measure_exp e <= n
    ->  measure_env env <= m
    ->  subst_env (n + m) env e
    =   subst_env (n + measure_env env) env e.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr -  env e n m Hle_e Hle_env.
    app - mred_exp_separate; lia.
  Qed.





  Theorem mred_exp_list_min :
    forall env el n,
        list_sum (map measure_exp el) + measure_env env <= n
    ->  map (subst_env n env) el
      = map (subst_env (list_sum (map measure_exp el) + measure_env env) env)
         el.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr -  env el n Hle1.
    mred_solver - env el n Hle1 Hle2:
      mred_exp_list
      (list_sum (map measure_exp el) + measure_env env).
  Qed.






  Theorem mred_exp_map_min :
    forall env ell n,
        list_sum (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) ell)
           + measure_env env <= n
    ->  map
          (prod_map
            (subst_env n env)
            (subst_env n env))
          ell
      = map
          (prod_map
            (subst_env
              (list_sum
                (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) ell)
                + measure_env env)
              env)
            (subst_env
              (list_sum
                (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) ell)
                + measure_env env)
              env))
          ell.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr -  env ell n Hle1.
    mred_solver - env ell n Hle1 Hle2:
      mred_exp_map
      (list_sum (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) ell)
        + measure_env env).
  Qed.






  Theorem mred_exp_list_split_min :
    forall fns env el1 el2,
      map
        (bexp_to_fexp fns)
        (map
          (subst_env
            (measure_list measure_exp (el1 ++ el2) + measure_env env)
            env)
          (el1 ++ el2))
    = map
        (bexp_to_fexp fns)
        (map
          (subst_env
            (measure_list measure_exp el1 + measure_env env)
            env)
          el1)
      ++
      map
        (bexp_to_fexp fns)
        (map
          (subst_env
            (measure_list measure_exp el2 + measure_env env)
            env)
          el2).
  Proof.
    (* #1 Intro: intro *)
    itr.
    (* #2 Rewrite Applicative: rewrite *)
    do 2 rwr - map_app.
    (* #3 Measure Reduction: rewrite *)
    rewrite mred_exp_list_min with (el := el1).
    rewrite mred_exp_list_min with (el := el2).
    (* #4 Trivial: trv_le_solver/trivial*)
    2-3: trv_le_solver.
    trv.
  Qed.






  Theorem mred_exp_map_split_min :
    forall fns env ell1 ell2,
      map
        (prod_map
          (bexp_to_fexp fns)
          (bexp_to_fexp fns))
        (map
          (prod_map
            (subst_env
              (measure_map measure_exp (ell1 ++ ell2) + measure_env env)
              env)
            (subst_env
              (measure_map measure_exp (ell1 ++ ell2) + measure_env env)
              env))
          (ell1 ++ ell2))
    = map
        (prod_map
          (bexp_to_fexp fns)
          (bexp_to_fexp fns))
        (map
          (prod_map
            (subst_env
              (measure_map measure_exp ell1 + measure_env env)
              env)
            (subst_env
              (measure_map measure_exp ell1 + measure_env env)
              env))
          ell1)
      ++
      map
        (prod_map
          (bexp_to_fexp fns)
          (bexp_to_fexp fns))
        (map
          (prod_map
            (subst_env
              (measure_map measure_exp ell2 + measure_env env)
              env)
            (subst_env
              (measure_map measure_exp ell2 + measure_env env)
              env))
          ell2).
  Proof.
    (* #1 Intro: intro *)
    itr.
    (* #2 Rewrite Applicative: rewrite *)
    do 2 rwr - map_app.
    (* #3 Measure Reduction: rewrite *)
    rewrite mred_exp_map_min with (ell := ell1).
    rewrite mred_exp_map_min with (ell := ell2).
    (* #4 Trivial: trv_le_solver/trivial*)
    2-3: trv_le_solver.
    trv.
  Qed.



End Minimum.











Section Inductive_Value.



  Theorem mred_vcons_v1 :
    forall v1 v2,
      bval_to_bexp (subst_env (measure_val (VCons v1 v2))) v1
    = bval_to_bexp (subst_env (measure_val v1)) v1.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - v1 Hle:
      mred_val_min
      (measure_val v1)
      (measure_val (VCons v1 v2)).
  Qed.



  Theorem mred_vcons_v2 :
    forall v1 v2,
      bval_to_bexp (subst_env (measure_val (VCons v1 v2))) v2
    = bval_to_bexp (subst_env (measure_val v2)) v2.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - v2 Hle:
      mred_val_min
      (measure_val v2)
      (measure_val (VCons v1 v2)).
  Qed.






  Theorem mred_v1v2_v1 :
    forall v1 v2,
      bval_to_bexp (subst_env (measure_val v1 + measure_val v2)) v1
    = bval_to_bexp (subst_env (measure_val v1)) v1.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - v1 Hle:
      mred_val_min
      (measure_val v1)
      (measure_val v1 + measure_val v2).
  Qed.



  Theorem mred_v1v2_v2 :
    forall v1 v2,
      bval_to_bexp (subst_env (measure_val v1 + measure_val v2)) v2
    = bval_to_bexp (subst_env (measure_val v2)) v2.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - v2 Hle:
      mred_val_min
      (measure_val v2)
      (measure_val v1 + measure_val v2).
  Qed.









  Theorem mred_vtuple_v :
    forall v vl,
      bval_to_bexp (subst_env (measure_val (VTuple (v :: vl)))) v
    = bval_to_bexp (subst_env (measure_val v)) v.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - v Hle:
      mred_val_min
      (measure_val v)
      (measure_val (VTuple (v :: vl))).
  Qed.



  Theorem mred_vtuple_vl :
    forall v vl,
      map (bval_to_bexp (subst_env (measure_val (VTuple (v :: vl))))) vl
    = map (bval_to_bexp (subst_env (measure_val (VTuple vl)))) vl.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - vl Hle1 Hle2:
      mred_val_list
      (list_sum (map measure_val vl))
      (measure_val (VTuple vl))
      (measure_val (VTuple (v :: vl))).
  Qed.






  Theorem mred_vvl_v :
    forall v vl,
      bval_to_bexp (subst_env (measure_val v + measure_list measure_val vl)) v
    = bval_to_bexp (subst_env (measure_val v)) v.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - v Hle:
      mred_val_min
      (measure_val v)
      (measure_val v + measure_list measure_val vl).
  Qed.



  Theorem mred_vvl_vl :
    forall v vl,
      map
        (bval_to_bexp
          (subst_env (measure_val v + measure_list measure_val vl))) vl
    = map (bval_to_bexp (subst_env (measure_list measure_val vl))) vl.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - vl Hle:
      mred_val_list_min
      (measure_list measure_val vl)
      (measure_val v + measure_list measure_val vl).
  Qed.









  Theorem mred_vmap_v1 :
    forall v1 v2 vll,
      bval_to_bexp (subst_env (measure_val (VMap ((v1, v2) :: vll)))) v1
    = bval_to_bexp (subst_env (measure_val v1)) v1.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - v1 Hle:
      mred_val_min
      (measure_val v1)
      (measure_val (VMap ((v1, v2) :: vll))).
  Qed.



  Theorem mred_vmap_v2 :
    forall v1 v2 vll,
      bval_to_bexp (subst_env (measure_val (VMap ((v1, v2) :: vll)))) v2
    = bval_to_bexp (subst_env (measure_val v2)) v2.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - v2 Hle:
      mred_val_min
      (measure_val v2)
      (measure_val (VMap ((v1, v2) :: vll))).
  Qed.



  Theorem mred_vmap_vll :
    forall v1 v2 vll,
      map
        (prod_map
          (bval_to_bexp (subst_env (measure_val (VMap ((v1, v2) :: vll)))))
          (bval_to_bexp (subst_env (measure_val (VMap ((v1, v2) :: vll))))))
        vll
    =
      map
        (prod_map
          (bval_to_bexp (subst_env (measure_val (VMap vll))))
          (bval_to_bexp (subst_env (measure_val (VMap vll)))))
        vll.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - vll Hle1 Hle2:
      mred_val_map
      (list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vll))
      (measure_val (VMap vll))
      (measure_val (VMap ((v1, v2) :: vll))).
  Qed.






  Theorem mred_v1v2vll_v1 :
    forall v1 v2 vll,
      bval_to_bexp
        (subst_env
          (measure_val v1 + measure_val v2 + measure_map measure_val vll)) v1
    = bval_to_bexp (subst_env (measure_val v1)) v1.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - v1 Hle:
      mred_val_min
      (measure_val v1)
      (measure_val v1 + measure_val v2 + measure_map measure_val vll).
  Qed.



  Theorem mred_v1v2vll_v2 :
    forall v1 v2 vll,
      bval_to_bexp
        (subst_env
          (measure_val v1 + measure_val v2 + measure_map measure_val vll)) v2
    = bval_to_bexp (subst_env (measure_val v2)) v2.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - v2 Hle:
      mred_val_min
      (measure_val v2)
      (measure_val v1 + measure_val v2 + measure_map measure_val vll).
  Qed.



  Theorem mred_v1v2vll_vll :
    forall v1 v2 vll,
      map
        (prod_map
          (bval_to_bexp
            (subst_env
              (measure_val v1 + measure_val v2 + measure_map measure_val vll)))
          (bval_to_bexp
            (subst_env
              (measure_val v1 + measure_val v2 + measure_map measure_val vll))))
        vll
    =
      map
        (prod_map
          (bval_to_bexp (subst_env (measure_map measure_val vll)))
          (bval_to_bexp (subst_env (measure_map measure_val vll))))
        vll.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - vll Hle:
      mred_val_map_min
      (measure_map measure_val vll)
      (measure_val v1 + measure_val v2 + measure_map measure_val vll).
  Qed.



End Inductive_Value.












Section Inductive_Expression.



  Theorem mred_e_rem_vars :
    forall vars env e,
      subst_env (measure_exp e + measure_env env)
        (rem_vars vars env) e
    = subst_env (measure_env_exp (rem_vars vars env) e)
        (rem_vars vars env) e.
  Proof.
    (* #1 Measure Reduction Environment: intro/assert/pose/rewrite
      + lia/clear/trivial *)
    itr.
    ass > (measure_exp e <= measure_exp e) as Hle_e: lia.
    pse - measure_env_rem_vars_le as Hle_env: env vars.
    psc - mred_exp_only_env_min as Heq_env: (rem_vars vars env) e
      (measure_exp e) (measure_env env)
      Hle_e Hle_env.
    bwr - Heq_env.
  Qed.



  Theorem mred_eext_e_rem_vars :
    forall vars env e
      (ext : list (nat * FunctionIdentifier * FunctionExpression)),
      subst_env
        (measure_exp e + measure_exp_ext measure_exp ext + measure_env env)
        (rem_vars vars env) e
    = subst_env (measure_env_exp (rem_vars vars env) e)
        (rem_vars vars env) e.
  Proof.
    (* #1 Measure Reduction Separate: intro/pose/apply + lia/assumption *)
    itr.
    pse - measure_env_rem_vars_le as Hle_env: env vars.
    app - mred_exp_separate; lia + asm.
  Qed.









  Theorem mred_e1e2_e1 :
    forall env e1 e2,
      subst_env (measure_exp e1 + measure_exp e2 + measure_env env) env e1
    = subst_env (measure_env_exp env e1) env e1.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - env e1 Hle:
      mred_exp_min
      (measure_env_exp env e1)
      (measure_exp e1 + measure_exp e2 + measure_env env).
  Qed.



  Theorem mred_e1e2_e2 :
    forall env e1 e2,
      subst_env (measure_exp e1 + measure_exp e2 + measure_env env) env e2
    = subst_env (measure_env_exp env e2) env e2.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - env e2 Hle:
      mred_exp_min
      (measure_env_exp env e2)
      (measure_exp e1 + measure_exp e2 + measure_env env).
  Qed.



  Theorem mred_e1e2_e2_rem_vars :
    forall vars env e1 e2,
      subst_env (measure_exp e1 + measure_exp e2 + measure_env env)
        (rem_vars vars env) e2
    = subst_env (measure_env_exp (rem_vars vars env) e2)
        (rem_vars vars env) e2.
  Proof.
    (* #1 Measure Reduction Environment: intro/assert/pose/rewrite
      + lia/clear *)
    itr.
    ass > (measure_exp e2 <= measure_exp e1 + measure_exp e2) as Hle_e2: lia.
    pse - measure_env_rem_vars_le as Hle_env: env vars.
    psc - mred_exp_only_env_min as Heq_env: (rem_vars vars env) e2
      (measure_exp e1 + measure_exp e2) (measure_env env)
      Hle_e2 Hle_env.
    cwr - Heq_env.
    (* #2 Measure Reduction Solver: mred_solver *)
    mred_solver > (rem_vars vars env) e2 Hle:
      mred_exp_min
      (measure_env_exp (rem_vars vars env) e2)
      (measure_exp e1 + measure_exp e2 + measure_env (rem_vars vars env)).
  Qed.









  Theorem mred_e1e2e3_e1 :
    forall env e1 e2 e3,
      subst_env (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env env) env e1
    = subst_env (measure_env_exp env e1) env e1.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - env e1 Hle:
      mred_exp_min
      (measure_env_exp env e1)
      (measure_exp e1 + measure_exp e2 + measure_exp e3 + measure_env env).
  Qed.



  Theorem mred_e1e2e3_e2_rem_vars :
    forall vars env e1 e2 e3,
      subst_env (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env env) (rem_vars vars env) e2
    = subst_env (measure_env_exp (rem_vars vars env) e2)
        (rem_vars vars env) e2.
  Proof.
    (* #1 Measure Reduction Environment: intro/assert/pose/rewrite
      + lia/clear *)
    itr.
    ass > (measure_exp e2 ≤ measure_exp e1 + measure_exp e2 + measure_exp e3)
      as Hle_e2: lia.
    pse - measure_env_rem_vars_le as Hle_env: env vars.
    psc - mred_exp_only_env_min as Heq_env: (rem_vars vars env) e2
      (measure_exp e1 + measure_exp e2 + measure_exp e3) (measure_env env)
      Hle_e2 Hle_env.
    cwr - Heq_env.
    (* #2 Measure Reduction Solver: mred_solver *)
    mred_solver > (rem_vars vars env) e2 Hle:
      mred_exp_min
      (measure_env_exp (rem_vars vars env) e2)
      (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env (rem_vars vars env)).
  Qed.



  Theorem mred_e1e2e3_e3_rem_vars :
    forall vars env e1 e2 e3,
      subst_env (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env env) (rem_vars vars env) e3
    = subst_env (measure_env_exp (rem_vars vars env) e3)
        (rem_vars vars env) e3.
  Proof.
    (* #1 Measure Reduction Environment: intro/assert/pose/rewrite
      + lia/clear *)
    itr.
    ass > (measure_exp e3 ≤ measure_exp e1 + measure_exp e2 + measure_exp e3)
      as Hle_e3: lia.
    pse - measure_env_rem_vars_le as Hle_env: env vars.
    psc - mred_exp_only_env_min as Heq_env: (rem_vars vars env) e3
      (measure_exp e1 + measure_exp e2 + measure_exp e3) (measure_env env)
      Hle_e3 Hle_env.
    (* #2 Measure Reduction Solver: mred_solver *)
    cwr - Heq_env.
    mred_solver > (rem_vars vars env) e3 Hle:
      mred_exp_min
      (measure_env_exp (rem_vars vars env) e3)
      (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env (rem_vars vars env)).
  Qed.









  Theorem mred_eel_e :
    forall env e el,
      subst_env (measure_list measure_exp (e :: el) + measure_env env) env e
    = subst_env (measure_env_exp env e) env e.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - env e Hle:
      mred_exp_min
      (measure_env_exp env e)
      (measure_list measure_exp (e :: el) + measure_env env).
  Qed.



  Theorem mred_eel_el :
    forall env e el,
      map
        (subst_env (measure_list measure_exp (e :: el) + measure_env env) env)
        el
    = map (subst_env (measure_list measure_exp el + measure_env env) env) el.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - env el Hle:
      mred_exp_list_min
      (measure_list measure_exp el + measure_env env)
      (measure_list measure_exp (e :: el) + measure_env env).
  Qed.









  Theorem mred_e1e2ell_e1 :
    forall env e1 e2 ell,
      subst_env
        (measure_map measure_exp ((e1, e2) :: ell) + measure_env env) env e1
    = subst_env (measure_env_exp env e1) env e1.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - env e1 Hle:
      mred_exp_min
      (measure_env_exp env e1)
      (measure_map measure_exp ((e1, e2) :: ell) + measure_env env).
  Qed.



  Theorem mred_e1e2ell_e2 :
    forall env e1 e2 ell,
      subst_env
        (measure_map measure_exp ((e1, e2) :: ell) + measure_env env) env e2
    = subst_env (measure_env_exp env e2) env e2.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - env e2 Hle:
      mred_exp_min
      (measure_env_exp env e2)
      (measure_map measure_exp ((e1, e2) :: ell) + measure_env env).
  Qed.



  Theorem mred_e1e2ell_ell :
    forall env e1 e2 ell,
      map
        (prod_map
          (subst_env
            (measure_map measure_exp ((e1, e2) :: ell) + measure_env env) env)
          (subst_env
            (measure_map measure_exp ((e1, e2) :: ell) + measure_env env) env))
        ell
    = map
        (prod_map
          (subst_env (measure_map measure_exp ell + measure_env env) env)
          (subst_env (measure_map measure_exp ell + measure_env env) env))
        ell.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - env ell Hle:
      mred_exp_map_min
      (measure_map measure_exp ell + measure_env env)
      (measure_map measure_exp ((e1, e2) :: ell) + measure_env env).
  Qed.









  Theorem mred_expel_exp :
    forall env exp el,
      subst_env
        (measure_exp exp + measure_list measure_exp el + measure_env env)
        env
        exp
    = subst_env (measure_env_exp env exp) env exp.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - env exp Hle:
      mred_exp_min
      (measure_env_exp env exp)
      (measure_exp exp + measure_list measure_exp el + measure_env env).
  Qed.



  Theorem mred_expel_el :
    forall env exp el,
      map
        (subst_env
          (measure_exp exp + measure_list measure_exp el + measure_env env)
          env)
        el
    = map (subst_env (measure_list measure_exp el + measure_env env) env) el.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - env el Hle:
      mred_exp_list_min
      (measure_list measure_exp el + measure_env env)
      (measure_exp exp + measure_list measure_exp el + measure_env env).
  Qed.



  Theorem mred_eext_ext_rem_both :
    forall vars env e
      (ext : list (nat * FunctionIdentifier * FunctionExpression)),
      subst_env
        (measure_exp e + measure_exp_ext measure_exp ext + measure_env env)
        (rem_vars vars env) e
    = subst_env (measure_env_exp (rem_vars vars env) e)
        (rem_vars vars env) e.
  Proof.
    (* #1 Measure Reduction Separate: intro/pose/apply + lia/assumption *)
    itr.
    pse - measure_env_rem_vars_le as Hle_env: env vars.
    app - mred_exp_separate; lia + asm.
  Qed.



End Inductive_Expression.