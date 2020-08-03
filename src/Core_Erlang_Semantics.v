Require Core_Erlang_Side_Effects.

(** The Semantics of Core Erlang *)
Module Semantics.

Export Core_Erlang_Side_Effects.Side_Effects.
Export Core_Erlang_Environment.Environment.

Import ListNotations.

(** For biuilt-in arithmetic calls *)
Definition eval_arith (fname : string) (params : list Value) : Value + Exception :=
match fname, params with
(** addition *)
| "+"%string, [VLit (Integer a); VLit (Integer b)] => inl (VLit (Integer (a + b)))
| "+"%string, [a; b]                               => inr (badarith (VCons a b))
(** subtraction *)
| "-"%string, [VLit (Integer a); VLit (Integer b)] => inl (VLit (Integer (a - b)))
| "-"%string, [a; b]                               => inr (badarith (VCons a b))
(** anything else *)
| _         , _                                    => inr (undef (VLit (Atom fname)))
end.

(** For IO maniputaion: *)
Definition eval_io (fname : string) (params : list Value) (eff : SideEffectList) 
   : ((Value + Exception) * SideEffectList) :=
match fname, length params, params with
(** writing *)
| "fwrite"%string, 1, _ => (inl ok                                    , eff ++ [(Output, params)])
(** reading *)
| "fread"%string , 2, e => (inl (VTuple [ok; nth 1 params ErrorValue]), eff ++ [(Input, params)])
(** anything else *)
| _              , _, _ => (inr (undef (VLit (Atom fname)))           , eff)
end.

Definition eval_logical (fname : string) (params : list Value) : Value + Exception :=
match fname, params with
(** logical and *)
| "and"%string, [a; b] => 
   match a, b with
   | VLit (Atom "true") , VLit (Atom "true")    => inl ttrue
   | VLit (Atom "false"), VLit (Atom "true")    => inl ffalse
   | VLit (Atom "true") , VLit (Atom "false")   => inl ffalse
   | VLit (Atom "false"), VLit (Atom "false")   => inl ffalse
   | _                         , _              => inr (badarg (VCons a b))
   end
(** logical or *)
| "or"%string, [a; b] =>
   match a, b with
   | VLit (Atom "true") , VLit (Atom "true")    => inl ttrue
   | VLit (Atom "false"), VLit (Atom "true")    => inl ttrue
   | VLit (Atom "true") , VLit (Atom "false")   => inl ttrue
   | VLit (Atom "false"), VLit (Atom "false")   => inl ffalse
   | _                         , _              => inr (badarg (VCons a b))
   end
(** logical not *)
| "not"%string, [a] =>
   match a with
   | VLit (Atom "true")  => inl ffalse
   | VLit (Atom "false") => inl ttrue
   | _                   => inr (badarg a)
   end
(** anything else *)
| _ , _ => inr (undef (VLit (Atom fname)))
end.

Definition eval_equality (fname : string) (params : list Value) : Value + Exception :=
match fname, params with
| "=="%string,  [v1; v2] (* TODO: with floats, this one should be adjusted *)
| "=:="%string, [v1; v2] => if bValue_eq_dec v1 v2 then inl ttrue else inl ffalse
| "/="%string,  [v1; v2] (* TODO: with floats, this one should be adjusted *)
| "=/="%string, [v1; v2] => if bValue_eq_dec v1 v2 then inl ffalse else inl ttrue
(** anything else *)
| _ , _ => inr (undef (VLit (Atom fname)))
end.

Fixpoint eval_append (v1 v2 : Value) : Value + Exception :=
match v1, v2 with
| VNil, VNil => inl VNil
| VNil, VCons x y => inl (VCons x y)
| VCons x y, VNil => inl (VCons x y)
| VCons x y, VCons x' y' =>
  match y with
  | VCons z w => match eval_append y (VCons x' y') with
                 | inr ex => inr ex
                 | inl res => inl (VCons x res)
                 end
  | VNil      => inl (VCons x (VCons x' y'))
  | z         => inl (VCons x (VCons y (VCons x' y')))
  end
| _, _ => inr (badarg (VCons v1 v2))
end.

Fixpoint subtract_elem (v1 v2 : Value) : Value :=
match v1 with
| VNil => VNil
| VCons x y =>
  match y with
  | VNil => if bValue_eq_dec x v2 then VNil else VCons x y
  | VCons z w => if bValue_eq_dec x v2 then y else VCons x y
  | z => if bValue_eq_dec x v2 then VCons z VNil else if bValue_eq_dec z v2 then VCons x VNil else VCons x y
  end
| _ => ErrorValue
end.

Fixpoint eval_subtract (v1 v2 : Value) : Value + Exception :=
match v1, v2 with
| VNil, VNil => inl VNil
| VNil, VCons x y => inl VNil
| VCons x y, VNil => inl (VCons x y)
| VCons x y, VCons x' y' => 
   match y' with
   | VNil => inl (subtract_elem (VCons x y) x')
   | VCons z w => eval_subtract (subtract_elem (VCons x y) x') y'
   | z => inl (subtract_elem (subtract_elem (VCons x y) x') z)
   end
| _        , _         => inr (badarg (VCons v1 v2))
end.

Definition eval_transform_list (fname : string) (params : list Value) : Value + Exception :=
match fname, params with
| "++"%string, [v1; v2] => eval_append v1 v2
| "--"%string, [v1; v2] => eval_subtract v1 v2
| _ , _ => inr (undef (VLit (Atom fname)))
end.

Fixpoint transform_tuple (v : Value) : Value + Exception :=
match v with
| VTuple l => inl ((fix unfold_list l :=
                   match l with
                   | [] => VNil
                   | x::xs => VCons x (unfold_list xs)
                   end) l)
| _        => inr (badarg v)
end.

Fixpoint transform_list (v : Value) : list Value + Exception :=
match v with
| VNil      => inl []
| VCons x y => match y with
               | VNil => inl [x]
               | VCons z w => match (transform_list y) with
                              | inr ex => inr ex
                              | inl res => inl (x::res)
                              end
               | z => inl [x; z]
               end
| _         => inr (badarg v)
end.

Definition eval_list_tuple (fname : string) (params : list Value) : Value + Exception :=
match fname, params with
| "tuple_to_list"%string, [v] => transform_tuple v
| "list_to_tuple"%string, [v] => match (transform_list v) with
                                 | inr ex => inr ex
                                 | inl l => inl (VTuple l)
                                 end
| _                     , _   => inr (undef (VLit (Atom fname)))
end.

Definition eval_cmp (fname : string) (params : list Value) : Value + Exception :=
match fname, params with
| "<"%string,  [v1; v2] => if value_less v1 v2 then inl ttrue else inl ffalse
| "<="%string, [v1; v2] => if orb (value_less v1 v2) (bValue_eq_dec v1 v2) 
                           then inl ttrue else inl ffalse
| ">"%string,  [v1; v2] => if value_less v2 v1 then inl ttrue else inl ffalse
| ">="%string, [v1; v2] => if orb (value_less v2 v1) (bValue_eq_dec v1 v2) 
                           then inl ttrue else inl ffalse
(** anything else *)
| _ , _ => inr (undef (VLit (Atom fname)))
end.

(* TODO: Always can be extended, this function simulates inter-module calls *)
Definition eval (fname : string) (params : list Value) (eff : SideEffectList) 
   : ((Value + Exception) * SideEffectList) :=
match fname with
| "+"%string      | "-"%string     => (eval_arith fname params, eff)
| "fwrite"%string | "fread"%string => eval_io fname params eff
| "and"%string    | "or"%string
| "not"%string                     => (eval_logical fname params, eff)
| "=="%string     | "=:="%string
| "/="%string     | "=/="%string   => (eval_equality fname params, eff)
| "++"%string     | "--"%string    => (eval_transform_list fname params, eff)
| "tuple_to_list"%string
| "list_to_tuple"%string           => (eval_list_tuple fname params, eff)
| "<"%string      | ">"%string 
| "<="%string     | ">="%string    => (eval_cmp fname params, eff)
(** anything else *)
| _                                => (inr (undef (VLit (Atom fname))), eff)
end.

(** Tests *)

Compute (eval "+" [VLit (Integer 1); VLit (Integer 2)]) [] = (inl (VLit (Integer 3)), []).
Compute (eval "-" [VLit (Integer 1); VLit (Integer 2)]) [] = (inl (VLit (Integer (-1))), []).
Compute (eval "+" [VLit (Atom "foo"); VLit (Integer 2)]) [] 
    = (inr (badarith (VCons (VLit (Atom "foo")) (VLit (Integer 2)))), []).
Compute (eval "+" [VLit (Integer 1); VLit (Atom "foo")]) [] 
    = (inr (badarith (VCons (VLit (Integer 2)) (VLit (Atom "foo")))), []).
Compute (eval "-" [VLit (Atom "foo"); VLit (Integer 2)]) [] 
    = (inr (badarith (VCons (VLit (Atom "foo")) (VLit (Integer 2)))), []).
Compute (eval "-" [VLit (Integer 1); VLit (Atom "foo")]) [] 
    = (inr (badarith (VCons (VLit (Integer 2)) (VLit (Atom "foo")))), []).
Compute (eval "-" [VLit (Atom "foo")]) [] 
    = (inr (undef (VLit (Atom "-"))), []).
Compute (eval "+" [VLit (Atom "foo")]) [] 
    = (inr (undef (VLit (Atom "+"))), []).

Compute (eval "not" [ttrue]) [] = (inl ffalse, []).
Compute (eval "not" [ffalse]) [] = (inl ttrue, []).
Compute (eval "not" [VLit (Integer 5)]) [] = (inr (badarg (VLit (Integer 5))), []).
Compute (eval "not" [VLit (Integer 5); VEmptyTuple]) [] = (inr (undef (VLit (Atom "not"))), []).

Compute (eval "and" [ttrue; ttrue]) [] = (inl ttrue, []).
Compute (eval "and" [ttrue; ffalse]) [] = (inl ffalse, []).
Compute (eval "and" [ffalse; ttrue]) [] = (inl ffalse, []).
Compute (eval "and" [ffalse; ffalse]) [] = (inl ffalse, []).
Compute (eval "and" [ttrue; VEmptyTuple]) [] = (inr (badarg (VCons (VLit (Atom "true")) (VTuple []))), []).
Compute (eval "and" [ttrue]) [] = (inr (undef (VLit (Atom "and"))), []).

Compute (eval "or" [ttrue; ttrue]) [] = (inl ttrue, []).
Compute (eval "or" [ttrue; ffalse]) [] = (inl ttrue, []).
Compute (eval "or" [ffalse; ttrue]) [] = (inl ttrue, []).
Compute (eval "or" [ffalse; ffalse]) [] = (inl ffalse, []).
Compute (eval "or" [ttrue; VEmptyTuple]) [] = (inr (badarg (VCons (VLit (Atom "true")) (VTuple []))), []).
Compute (eval "or" [ttrue]) [] = (inr (undef (VLit (Atom "or"))), []).

Compute (eval "fwrite" [ttrue]) [] = (inl ok, [(Output, [ttrue])]).
Compute (eval "fwrite" [VMap [(ttrue, ttrue)]]) [] = (inl ok, [(Output, [VMap [(ttrue, ttrue)]])]).
Compute (eval "fwrite" []) [] = (inr (undef (VLit (Atom "fwrite"))), []).

Compute (eval "fread" [VLit (Atom "foo.txt"); ttrue]) [] = 
   (inl (VTuple [ok; ttrue]), [(Input, [VLit (Atom "foo.txt"); ttrue])]).
Compute (eval "fread" [VLit (Atom "foo.txt"); VMap [(ttrue, ttrue)]]) [] = 
   (inl (VTuple [ok; VMap [(ttrue, ttrue)]]), [(Input, [VLit (Atom "foo.txt"); VMap [(ttrue, ttrue)]])]).
Compute (eval "fread" []) [] = (inr (undef (VLit (Atom "fread"))), []).

Compute (eval "==" [ttrue; ttrue]) [] = (inl ttrue, []).
Compute (eval "==" [ttrue; ffalse]) [] = (inl ffalse, []).
Compute (eval "==" [VClos [] [] 1 [] EEmptyMap; ttrue]) [] = (inl ffalse, []).
Compute (eval "==" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 2 [] EEmptyMap]) [] = (inl ffalse, []).
Compute (eval "==" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl ttrue, []).

Compute (eval "/=" [ttrue; ttrue]) [] = (inl ffalse, []).
Compute (eval "/=" [ttrue; ffalse]) [] = (inl ttrue, []).
Compute (eval "/=" [VClos [] [] 1 [] EEmptyMap; ttrue]) [] = (inl ttrue, []).
Compute (eval "/=" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 2 [] EEmptyMap]) [] = (inl ttrue, []).
Compute (eval "/=" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl ffalse, []).
Compute (eval "/=" [ttrue]) [] = (inr (undef (VLit (Atom "/="))), []).

Definition l1 : Value := VCons ttrue VNil.
Definition l2 : Value := VCons ttrue ttrue.
Definition l3 : Value := VCons (VCons ttrue ttrue) ttrue.
Definition l4 : Value := VCons ttrue (VCons ttrue (VCons ttrue VNil)).
Definition l5 : Value := VCons ttrue (VCons ttrue ttrue).

Compute (eval "++" [ttrue; ttrue]) [] = (inr (badarg _), []).
Compute (eval "++" [l1; l1]) [].
Compute (eval "++" [l1; l2]) [].
Compute (eval "++" [l1; l3]) [].
Compute (eval "++" [l3; l3]) [].

Compute (eval "--" [ttrue; ttrue]) [] = (inr (badarg _), []).
Compute (eval "--" [l1; l1]) [].
Compute (eval "--" [l1; l2]) [].
Compute (eval "--" [l1; l3]) [].
Compute (eval "--" [l3; l3]) [].
Compute (eval "--" [l3; l1]) [].

Compute (eval "tuple_to_list" [VTuple [ttrue; ttrue; ttrue; l1]] []).
Compute (eval "tuple_to_list" [VTuple [ttrue; ttrue; l5; l1]] []).
Compute (eval "tuple_to_list" [VTuple [ttrue; l3; ttrue; l1]] []).
Compute (eval "tuple_to_list" [VTuple [ttrue; ttrue; l2; l1]] []).
Compute (eval "tuple_to_list" [ttrue] []).

Compute (eval "list_to_tuple" [l1] []).
Compute (eval "list_to_tuple" [l2] []).
Compute (eval "list_to_tuple" [l3] []).
Compute (eval "list_to_tuple" [l4] []).
Compute (eval "list_to_tuple" [l5] []).

Compute (eval "<" [ttrue; ttrue]) [] = (inl ffalse, []).
Compute (eval "<" [ttrue; ffalse]) [] = (inl ffalse, []).
Compute (eval "<" [VClos [] [] 1 [] EEmptyMap; VEmptyMap]) [] = (inl ttrue, []).
Compute (eval "<" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 2 [] EEmptyMap]) [] = (inl ttrue, []).
Compute (eval "<" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl ffalse, []).

Compute (eval "<=" [ttrue; ttrue]) [] = (inl ttrue, []).
Compute (eval "<=" [ttrue; ffalse]) [] = (inl ffalse, []).
Compute (eval "<=" [VClos [] [] 1 [] EEmptyMap; VEmptyMap]) [] = (inl ttrue, []).
Compute (eval "<=" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 2 [] EEmptyMap]) [] = (inl ttrue, []).
Compute (eval "<=" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl ttrue, []).

Compute (eval ">" [ttrue; ttrue]) [] = (inl ffalse, []).
Compute (eval ">" [ffalse; ttrue]) [] = (inl ffalse, []).
Compute (eval ">" [VEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl ttrue, []).
Compute (eval ">" [VClos [] [] 2 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl ttrue, []).
Compute (eval ">" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl ffalse, []).

Compute (eval ">=" [ttrue; ttrue]) [] = (inl ttrue, []).
Compute (eval ">=" [ffalse; ttrue]) [] = (inl ffalse, []).
Compute (eval ">=" [VEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl ttrue, []).
Compute (eval ">=" [VClos [] [] 2 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl ttrue, []).
Compute (eval ">=" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl ttrue, []).

(** End of tests *)

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
      |env, nth_def ids id 0 i, nth i exps ErrorExp, nth_def eff eff1 [] i| 
     -e> 
      |nth_def ids id 0 (S i), inl (nth i vals ErrorValue), nth_def eff eff1 [] (S i)|
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
| eval_case (env: Environment) (guard exp: Expression) (exps : list Expression) (vals : list Value) (v' : Value + Exception) (l : list (list Pattern * Expression * Expression)) (bindings: list (Var * Value)) (i : nat) (eff : list SideEffectList) (eff1 eff2 : SideEffectList) (ids : list nat) (id id' : nat) :
  length exps = length vals ->
  length exps = length eff ->
  length exps = length ids ->
  (
    forall i, i < length exps ->
    |env, nth_def ids id 0 i, nth i exps ErrorExp, nth_def eff eff1 [] i| 
     -e> 
    |nth_def ids id 0 (S i), inl (nth i vals ErrorValue), nth_def eff eff1 [] (S i)|
  ) ->
  i < length l ->
  match_clause vals l i = Some (guard, exp, bindings) ->
  (forall j : nat, j < i -> 

    (** THESE GUARDS MUST BE SIDE-EFFECT FREE ACCORDING TO 1.0.3 LANGUAGE SPECIFICATION *)
    (forall gg ee bb, match_clause vals l j = Some (gg, ee, bb) -> 
      (|add_bindings bb env, last ids id, gg, last eff eff1| -e> |last ids id, inl ffalse, last eff eff1| ))

  ) ->
  |add_bindings bindings env, last ids id, guard, last eff eff1| -e> |last ids id, inl ttrue, last eff eff1| -> 
  |add_bindings bindings env, last ids id, exp, last eff eff1| -e> |id', v', eff2|
->
  |env, id, ECase exps l, eff1| -e> |id', v', eff2|


(* call evaluation rule *)
| eval_call (env: Environment) (v : Value + Exception) (params : list Expression) 
     (vals : list Value) (fname: string) (eff1 eff2: SideEffectList) (eff : list SideEffectList) 
     (ids : list nat) (id id' : nat) :
  length params = length vals ->
  length params = length eff ->
  length params = length ids ->
  (
    forall i, i < length params ->
      |env, nth_def ids id 0 i, nth i params ErrorExp, nth_def eff eff1 [] i| 
     -e>
      |nth_def ids id 0 (S i), inl (nth i vals ErrorValue), nth_def eff eff1 [] (S i)|
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
      |env, nth_def ids id' 0 i, nth i params ErrorExp, nth_def eff eff2 [] i|
     -e>
      |nth_def ids id' 0 (S i), inl (nth i vals ErrorValue), nth_def eff eff2 [] (S i)|
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
      |env, nth_def ids id 0 i, nth i (snd (split l)) ErrorExp, nth_def eff eff1 [] i| 
       -e> 
      | nth_def ids id 0 (S i), inl (nth i vals ErrorValue), nth_def eff eff1 [] (S i)|
  )
  ->
    |append_vars_to_env (fst (split l)) vals env, last ids id, e, last eff eff1|
     -e>
    |id', v, eff2|
->
  |env, id, ELet l e, eff1| -e> |id', v, eff2|

(* evaluation of sequence (do expressions) *)
| eval_seq (env : Environment) (e1 e2: Expression) (v1 : Value) (v2 : Value + Exception)
     (eff1 eff2 eff3 : SideEffectList) (id id' id'' : nat) :
  |env, id, e1, eff1| -e> |id', inl v1, eff2| ->
  |env, id', e2, eff2| -e> |id'', v2, eff3|
->
  | env, id, ESeq e1 e2, eff1 | -e> |id'', v2, eff3|

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
    |env, nth_def ids id 0 (2 * i), nth i (fst (split l)) ErrorExp, nth_def eff eff1 [] (2 * i)| 
     -e>
    | nth_def ids id 0 (S (2 * i)), inl (nth i kvals ErrorValue), nth_def eff eff1 [] (S (2*i))|
  ) ->
  (
    forall i : nat, i < length l ->
    |env, nth_def ids id 0 (S (2 * i)), nth i (snd (split l)) ErrorExp, nth_def eff eff1 [] (S (2* i))|
     -e>
    |nth_def ids id 0 (S (S (2 * i))), inl (nth i vvals ErrorValue), nth_def eff eff1 [] (S (S (2*i)))|

  ) ->
  make_value_map kvals vvals = (kvals', vvals') ->
  combine kvals' vvals' = lv ->
  length lv <= length l ->
  eff2 = last eff eff1 ->
  id' = last ids id
->
  |env, id, EMap l, eff1| -e> |id', inl (VMap lv), eff2|


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
  |env, id, tl, eff1| -e> |id', inl vtl, eff2| -> 
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
    |nth_def ids id 0 (S j), inl (nth j vals ErrorValue), nth_def eff eff1 [] (S j)|) ->
  |env, last ids id, nth i exps ErrorExp, last eff eff1| -e> |id', inr ex, eff2|
->
  |env, id, ETuple exps, eff1| -e> |id', inr ex, eff2|


(* try 2x *)
| eval_try (env: Environment) (l : list (Expression * Var)) (e1 e2 : Expression) (vex1 vex2 vex3 : Var) (val : Value + Exception) (eff : list SideEffectList)
      (vals : list Value) (eff1 eff2 : SideEffectList) (id id' : nat) (ids : list nat) :
  length l = length vals ->
  length l = length eff ->
  length l = length ids ->
  (
    forall i, i < length l ->
      |env, nth_def ids id 0 i, nth i (fst (split l)) ErrorExp, nth_def eff eff1 [] i| -e> | nth_def ids id 0 (S i), inl (nth i vals ErrorValue), nth_def eff eff1 [] (S i)|
  ) ->
  |append_vars_to_env (snd (split l)) vals env, last ids id, e1, last eff eff1 |
   -e>
  | id', val, eff2|
->
  |env, id, ETry l e1 e2 vex1 vex2 vex3, eff1| -e> | id', val, eff2|


(* catch *)
| eval_catch (env: Environment) (l : list (Expression * Var)) (e1 e2 : Expression) (vex1 vex2 vex3 : Var) 
      (val : Value + Exception) (vals : list Value) (ex : Exception) (eff1 eff2 eff3 : SideEffectList) (eff : list SideEffectList) (i : nat) (id id' : nat) (ids : list nat) :
  i < length l ->
  length vals = i ->
  length eff = i ->
  length ids = i ->
  (
    forall j, j < i ->
      |env, nth_def ids id 0 j, nth j (fst (split l)) ErrorExp, nth_def eff eff1 [] j| -e> |nth_def ids id 0 (S j), inl (nth j vals ErrorValue), nth_def eff eff1 [] (S j)|
  ) ->
  | env, last ids id, nth i (fst (split l)) ErrorExp, last eff eff1| -e> |id', inr ex, eff2| ->
  |append_vars_to_env [vex1; vex2; vex3] 
                       [exclass_to_value (fst (fst ex)); snd (fst ex); snd ex] 
                       env, last ids id, e2, eff2|
 -e> 
  |id', val, eff3|
->
  |env, id, ETry l e1 e2 vex1 vex2 vex3, eff1| -e> |id', val, eff3|


(* case 2x *)
(** Pattern matching exception *)
| eval_case_pat_ex (env: Environment) (exps : list Expression) (vals : list Value) (ex : Exception) (l : list (list Pattern * Expression * Expression)) (eff : list SideEffectList) (eff1 eff2 : SideEffectList) (ids : list nat) (i id id' : nat):
  i < length exps ->
  length vals = i ->
  length eff = i ->
  length ids = i ->
  (forall j, j < i ->
    |env, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j|
   -e>
    |nth_def ids id 0 (S j), inl (nth j vals ErrorValue), nth_def eff eff1 [] (S j)|) ->
  |env, last ids id, nth i exps ErrorExp, last eff eff1| -e> |id', inr ex, eff2|
->
  |env, id, ECase exps l, eff1| -e> |id', inr ex, eff2|

(** No matching clause *)
| eval_case_clause_ex (env: Environment) (exps : list Expression) (l : list (list Pattern * Expression * Expression)) (vals : list Value) (eff : list SideEffectList) (eff1 eff2 : SideEffectList) (ids : list nat) (id id' : nat):
  length exps = length vals ->
  length exps = length eff ->
  length exps = length ids ->
  (
    forall i, i < length exps ->
    |env, nth_def ids id 0 i, nth i exps ErrorExp, nth_def eff eff1 [] i| 
     -e> 
    |nth_def ids id 0 (S i), inl (nth i vals ErrorValue), nth_def eff eff1 [] (S i)|
  ) ->
  eff2 = last eff eff1 ->
  id' = last ids id ->
  (forall j : nat, j < length l -> 

    (** THESE GUARDS MUST BE SIDE-EFFECT FREE ACCORDING TO 1.0.3 LANGUAGE SPECIFICATION *)
    (forall gg ee bb, match_clause vals l j = Some (gg, ee, bb) -> 
      ((|add_bindings bb env, id', gg, eff2| -e> | id', inl ffalse, eff2| ))

    )

  )
->
|env, id, ECase exps l, eff1| -e> | id', inr (if_clause), eff2|
(** ith guard exception -> guards cannot result in exception, i.e. this rule is not needed *)

(* call 1x *)
| eval_call_ex (env: Environment) (i : nat) (fname : string) (params : list Expression) 
     (vals : list Value) (ex : Exception) (eff1 eff2 : SideEffectList) 
     (eff : list SideEffectList) (id id' : nat) (ids : list nat) :
  i < length params ->
  length vals = i ->
  length eff = i ->
  length ids = i ->
  (forall j, j < i ->
    |env, nth_def ids id 0 j, nth j params ErrorExp, nth_def eff eff1 [] j|
   -e>
    |nth_def ids id 0 (S j), inl (nth j vals ErrorValue), nth_def eff eff1 [] (S j)|
  ) ->
  |env, last ids id, nth i params ErrorExp, last eff eff1| -e> |id', inr ex, eff2|

->
  |env, id, ECall fname params, eff1| -e> |id', inr ex, eff2|


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
  i = length vals ->
  length eff = i ->
  length ids = i
  ->
  |env, id, exp, eff1| -e> |id', inl v, eff2| ->
  (forall j, j < i -> 
    |env, nth_def ids id' 0 j, nth j params ErrorExp, nth_def eff eff2 [] j|
   -e>
    |nth_def ids id' 0 (S j), inl (nth j vals ErrorValue), nth_def eff eff2 [] (S j)|
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
  |env, id, exp, eff1| -e> |id', inl v, eff2| ->
  (
    forall j : nat, j < length params ->
    (
      |env, nth_def ids id' 0 j, nth j params ErrorExp, nth_def eff eff2 [] j|
     -e>
      |nth_def ids id' 0 (S j), inl (nth j vals ErrorValue), nth_def eff eff2 [] (S j)|
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
  |env, id, exp, eff1| -e> |id', inl (VClos ref ext n var_list body), eff2| ->
  (
    forall j : nat, j < length params ->
    (
      |env, nth_def ids id' 0 j, nth j params ErrorExp, nth_def eff eff2 [] j|
     -e>
      |nth_def ids id' 0 (S j), inl (nth j vals ErrorValue), nth_def eff eff2 [] (S j)|
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
| eval_let_ex (env: Environment) (l: list (Var * Expression)) (vals : list Value) (e : Expression) (ex : Exception) (i : nat) (eff1 eff2 : SideEffectList) (eff : list SideEffectList) (id id' : nat) (ids : list nat) :
  i < length l ->
  length vals = i -> 
  length eff = i ->
  length ids = i ->
  (forall j, j < i -> 
    |env, nth_def ids id 0 j, nth j (snd (split l)) ErrorExp, nth_def eff eff1 [] j| -e> |nth_def ids id 0 (S j), inl (nth j vals ErrorValue), nth_def eff eff1 [] (S j)|
  ) ->
  |env, last ids id, nth i (snd (split l)) ErrorExp, last eff eff1| -e> |id', inr ex, eff2|
->
  |env, id, ELet l e, eff1| -e> | id', inr ex, eff2|

(* sequence 1x *)
| eval_seq_ex (env : Environment) (e1 e2: Expression) (ex : Exception)
     (eff1 eff2 : SideEffectList) (id id' : nat) :
  |env, id, e1, eff1| -e> |id', inr ex, eff2|
->
  | env, id, ESeq e1 e2, eff1 | -e> |id', inr ex, eff2|


(* map 2x *)
(** Exception in key list *)
| eval_map_key_ex (l: list (Expression * Expression)) (vvals kvals : list Value) (env: Environment) (i : nat) (ex : Exception) (eff1 eff2 : SideEffectList) (eff : list SideEffectList) (ids : list nat) (id id' : nat):
  i < length l ->
  length vvals = i ->
  length kvals = i ->
  length eff = i * 2 ->
  length ids = i * 2 ->
  (
    forall j, j < i ->
    |env, nth_def ids id 0 (2*j), nth j (fst (split l)) ErrorExp, nth_def eff eff1 [] (2 * j)| -e> | nth_def ids id 0 (S (2*j)), inl (nth j kvals ErrorValue), nth_def eff eff1 [] (S (2 * j))|
  )
  ->
  (
    forall j, j < i ->
    |env, nth_def ids id 0 (S(2*j)), nth j (snd (split l)) ErrorExp, nth_def eff eff1 [] (S (2 * j))| -e> | nth_def ids id 0 (S (S (2*j))), inl (nth j vvals ErrorValue), nth_def eff eff1 [] (S (S (2 * j)))|
  )
  ->
  |env, last ids id, nth i (fst (split l)) ErrorExp, last eff eff1| -e> | id', inr ex, eff2|
->
  |env, id, EMap l, eff1| -e> | id', inr ex, eff2|

(** Exception in value list *)
|  eval_map_val_ex (l: list (Expression * Expression)) (vvals kvals : list Value) (env: Environment) (i : nat) (ex : Exception) (val : Value) (eff1 eff2 eff3 : SideEffectList) (eff : list SideEffectList) (ids : list nat) (id id' id'' : nat):
  i < length l ->
  length vvals = i ->
  length kvals = i ->
  length eff = i * 2 ->
  length ids = i * 2 ->
  (
    forall j, j < i ->
    |env, nth_def ids id 0 (2*j), nth j (fst (split l)) ErrorExp, nth_def eff eff1 [] (2 * j)| -e> | nth_def ids id 0 (S (2*j)),  inl (nth j kvals ErrorValue), nth_def eff eff1 [] (S (2 * j))|
  ) ->
  (
    forall j, j < i ->
    |env, nth_def ids id 0 (S (2*j)), nth j (snd (split l)) ErrorExp, nth_def eff eff1 [] (S (2 * j))| -e> | nth_def ids id 0 (S (S (2*j))), inl (nth j vvals ErrorValue), nth_def eff eff1 [] (S (S (2 * j)))|
  )
  ->
  |env, last ids id, nth i (fst (split l)) ErrorExp, last eff eff1| -e> |id', inl val, eff2|
  ->
  |env, id', nth i (snd (split l)) ErrorExp, eff2| -e> | id'', inr ex, eff3|
->
  |env, id, EMap l, eff1| -e> |id'', inr ex, eff3|


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