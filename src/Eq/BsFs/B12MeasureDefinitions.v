From CoreErlang.Eq.BsFs Require Export B11IdentLemmas.

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
  - measure_case
  - measure_ext
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



  Definition measure_case
    (case : list ((list Pattern) * Expression * Expression))
    : nat
    :=
  list_sum
    (map (fun '(pl, e1, e2) => (measure_exp e1) + (measure_exp e2)) case).



  Definition measure_ext
    (ext : list (FunctionIdentifier * (list Var * Expression)))
    : nat
    :=
  list_sum (map (measure_exp ∘ snd ∘ snd) ext).



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