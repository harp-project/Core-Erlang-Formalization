From CoreErlang.BigStep Require Import Syntax Environment.

(**
* Help
  - Generic
    + measure_list
    + measure_map
  - Expression
    + measure_case
    + measure_letrec
  - Value
    + measure_env
* Main
  - measure_exp
  - measure_val
  - measure_env_exp
*)



Section Help.



  Section Generic.

    Definition measure_list
      {A : Type}
      (f : A -> nat)
      (al : list A)
      : nat 
      :=
    list_sum (map f al).

    Definition measure_map
      {A : Type}
      (f : A -> nat)
      (aml : list (A * A))
      : nat
      :=
    list_sum (map (fun '(a1, a2) => (f a1) + (f a2)) aml).

  End Generic.



  Section Expression.

    Definition measure_case
      (f : Expression -> nat)
      (cl : list ((list Pattern) * Expression * Expression))
      : nat
      :=
    list_sum (map (fun '(pl, g, b) => (f g) + (f b)) cl).

    Definition measure_letrec
      (f : Expression -> nat)
      (lrl : list (FunctionIdentifier * (list Var * Expression)))
      : nat
      :=
    list_sum (map (fun '(fid, (vl, b)) => (f b)) lrl).

  End Expression.



  Section Value.

    Definition measure_env
      (f : Value -> nat)
      (env : Environment)
      : nat
      :=
    list_sum (map (fun '(vf, v) => (f v)) env).

  End Value.



End Help.






Section Main.



  Fixpoint measure_exp
    (e : Expression)
    : nat
    :=
  match e with
  | ENil => 1
  | ELit l => 1
  | EVar v => 1
  | EFunId f => 1

  | EFun vl e => 1
      + measure_exp e

  | ECons hd tl => 1
      + measure_exp hd
      + measure_exp tl

  | ESeq e1 e2 => 1
      + measure_exp e1
      + measure_exp e2

  | ELet l e1 e2 => 1
      + measure_exp e1
      + measure_exp e2

  | ETry e1 vl1 e2 vl2 e3 => 1
      + measure_exp e1
      + measure_exp e2
      + measure_exp e3

  | EValues el => 1
      + measure_list measure_exp el

  | EPrimOp f l => 1
      + measure_list measure_exp l

  | ETuple l => 1
      + measure_list measure_exp l

  | EMap l =>  1
      + measure_map measure_exp l

  | EApp exp l => 1
      + measure_exp exp
      + measure_list measure_exp l

  | ECall m f l => 1
      + measure_exp m
      + measure_exp f
      + measure_list measure_exp l

  | ECase e l => 1
      + measure_exp e
      + measure_case measure_exp l

  | ELetRec l e => 1
      + measure_exp e
      + measure_letrec measure_exp l
  end.



  Fixpoint measure_val
    (v : Value) 
    : nat
    :=
  match v with
  | VNil => 1
  | VLit l => 1

  | VCons hd tl => 1
      + measure_val hd
      + measure_val tl

  | VTuple l => 1
      + measure_list measure_val l

  | VMap l => 1
      + measure_map measure_val l

  | VClos env ext id vl e fid => 1
      + measure_exp e
      + measure_env measure_val env
  end.



  Definition measure_env_exp
    (env : Environment)
    (e : Expression)
    : nat
    :=
  measure_env measure_val env
  + measure_exp e.



End Main.