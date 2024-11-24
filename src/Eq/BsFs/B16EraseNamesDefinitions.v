From CoreErlang.Eq.BsFs Require Export B15SubstituteEnvironmentLemmas.

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