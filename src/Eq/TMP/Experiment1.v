(*
From CoreErlang.Eq.Tactics Require Export T1ParamZero.
From CoreErlang.Eq.Tactics Require Export T2ParamSingle.
From CoreErlang.Eq.Tactics Require Export T3ParamMultiple.
From CoreErlang.Eq.Tactics Require Export T4Name.
From CoreErlang.Eq.Tactics Require Export T5Transform.
From CoreErlang.Eq.Tactics Require Export T6Destruct.
From CoreErlang Require Export Basics. *)
From CoreErlang.BigStep Require Export BigStep.
From CoreErlang.FrameStack Require Export SubstSemanticsLemmas.
Require Export stdpp.list.

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
  - erase_exp
  - erase_valX
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






  Fixpoint erase_pat
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
      (erase_pat p1)
      (erase_pat p2)

  | PTuple pl =>
    Syntax.PTuple
      (map erase_pat pl)

  | PMap pll =>
    Syntax.PMap
      (map
        (prod_map
          erase_pat
          erase_pat)
        pll)

  end.









  Fixpoint erase_exp
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
      (erase_exp fns e1)
      (erase_exp fns e2)

  | ESeq e1 e2 =>
    Syntax.ESeq
      (erase_exp fns e1)
      (erase_exp fns e2)

  | EValues el =>
    Syntax.EValues
      (map (erase_exp fns) el)

  | ETuple el =>
    Syntax.ETuple
      (map (erase_exp fns) el)

  | EPrimOp s el =>
    Syntax.EPrimOp
      s
      (map (erase_exp fns) el)

  | EApp e el =>
    Syntax.EApp
      (erase_exp fns e)
      (map (erase_exp fns) el)

  | ECall e1 e2 el =>
    Syntax.ECall
      (erase_exp fns e1)
      (erase_exp fns e2)
      (map (erase_exp fns) el)

  | EMap ell =>
    Syntax.EMap
      (map
        (prod_map
          (erase_exp fns)
          (erase_exp fns))
        ell)

  | EFun vars e =>
    Syntax.EFun
      (length vars)
      (erase_exp (add_vars vars fns) e)

  | ELet vars e1 e2 =>
    Syntax.ELet
      (length vars)
      (erase_exp fns e1)
      (erase_exp (add_vars vars fns) e2)

  | ETry e1 vars1 e2 vars2 e3 =>
    Syntax.ETry
      (erase_exp fns e1)
      (length vars1)
      (erase_exp (add_vars vars1 fns) e2)
      (length vars2)
      (erase_exp (add_vars vars2 fns) e3)

  | ELetRec ext e =>
    Syntax.ELetRec
      (map
        (fun '(_, (vars, body)) =>
          (length vars,
          erase_exp (add_exp_ext_both vars ext fns) body))
        ext)
      (erase_exp (add_exp_ext_fids ext fns) e)

  | ECase e case =>
    Syntax.ECase
      (erase_exp fns e)
      (map 
        (fun '(pats, e1, e2) =>
          ((map erase_pat pats),
          erase_exp (add_pats pats fns) e1,
          erase_exp (add_pats pats fns) e2))
        case)

  | EVar var =>
    ˝Syntax.VVar
      (fns (inl var))

  | EFunId fid =>
    ˝Syntax.VFunId
      ((fns (inr fid)), snd fid)

  end.











(*
  Definition tmp_val
    (fns : NameSub)
    (v : Value)
    : Val
    :=
  Syntax.VNil.



  Definition erase_exp_envX
    (env : Environment)
    (fns : NameSub)
    (e : Expression)
    : Exp
    :=
  (erase_exp (add_names (map fst env) fns) e)
  .[list_subst (map (tmp_val fns) (map snd env)) idsubst].
















  Fixpoint erase_valX
    (fns : NameSub)
    (v : Value)
    : Val
    :=
  let
    erase_exp_env
      (env : Environment)
      (fns : NameSub)
      (e : Expression)
      : Exp
      :=
    (erase_exp (add_names (map fst env) fns) e)
    .[list_subst (map (tmp_val fns) (map snd env)) idsubst]
  in
  match v with

  | VNil =>
    Syntax.VNil

  | VLit lit =>
    Syntax.VLit
      (literal_to_lit lit)

  | VCons v1 v2 =>
    Syntax.VCons
      (erase_valX fns v1)
      (erase_valX fns v2)

  | VTuple vl =>
    Syntax.VTuple
      (map (erase_valX fns) vl)

  | VMap vll =>
    Syntax.VMap
      (map
        (prod_map
          (erase_valX fns)
          (erase_valX fns))
        vll)

  | VClos env ext _ vars e fid =>
    match ext, fid with
    | _ :: _, Some _ =>
      Syntax.VClos
        (map
          (fun '(n, fid', (vars', body)) =>
            (n,
            length vars',
            erase_exp_env
              (rem_val_ext_both vars' ext env)
              (add_val_ext_both vars' ext fns)
              body))
          ext)
        0
        (length vars)
        (erase_exp_env
          (rem_val_ext_fids ext env)
          (add_val_ext_fids ext fns)
          e)
    | _, _ =>
      Syntax.VClos
        []
        0
        (length vars)
        (erase_exp_env
          (rem_vars vars env)
          (add_vars vars fns)
          e)
    end

  end.
*)
(*
(rem_vars vars env)
*)



  Fixpoint erase_val
    (n : nat)
    (fns : NameSub)
    (v : Value)
    : Val
    :=
  let
    erase_exp_env
      (n : nat)
      (env : Environment)
      (fns : NameSub)
      (e : Expression)
      : Exp
      :=
    match n with
    | 0 => ˝Syntax.VNil
    | S n' =>
      (erase_exp (add_names (map fst env) fns) e)
      .[list_subst (map (erase_val n' fns) (map snd env)) idsubst]
    end
  in
  match n with
  | 0 => Syntax.VNil
  | S n' =>
    match v with

    | VNil =>
      Syntax.VNil

    | VLit lit =>
      Syntax.VLit
        (literal_to_lit lit)

    | VCons v1 v2 =>
      Syntax.VCons
        (erase_val n' fns v1)
        (erase_val n' fns v2)

    | VTuple vl =>
      Syntax.VTuple
        (map (erase_val n' fns) vl)

    | VMap vll =>
      Syntax.VMap
        (map
          (prod_map
            (erase_val n' fns)
            (erase_val n' fns))
          vll)

    | VClos env ext _ vars e fid =>
      match ext, fid with
      | _ :: _, Some _ =>
        Syntax.VClos
          (map
            (fun '(n, fid', (vars', body)) =>
              (n,
              length vars',
              erase_exp_env
                n'
                (rem_val_ext_both vars' ext env)
                (add_val_ext_both vars' ext fns)
                body))
            ext)
          0
          (length vars)
          (erase_exp_env
            n'
            (rem_val_ext_fids ext env)
            (add_val_ext_fids ext fns)
            e)
      | _, _ =>
        Syntax.VClos
          []
          0
          (length vars)
          (erase_exp_env
            n'
            (rem_vars vars env)
            (add_vars vars fns)
            e)
      end
    end
  end.



  Definition erase_names
    (env : Environment)
    (fns : NameSub)
    (e : Expression)
    : Exp
    :=
  (erase_exp
    (add_names (map fst env) fns)
    e)
  .[list_subst
    (map (fun x => erase_val (measure_val x) fns x) (map snd env))
    idsubst].



Open Scope string_scope.

Compute erase_names [] (fun _ => 0) (ECons ENil (ELit (Integer 1))).
Compute erase_names [(inl "X", (VLit (Integer 2)))] (fun _ => 0) (ECons ENil (EVar "X")).
Compute erase_names [(inl "X", (VLit (Integer 2)))] (fun _ => 0) (EFun ["X"] (EVar "X")).
Compute erase_names [(inl "X", (VLit (Integer 2)))] (fun _ => 0) (ECons (EVar "X") (EFun ["X"] (EVar "X"))).





End Main.