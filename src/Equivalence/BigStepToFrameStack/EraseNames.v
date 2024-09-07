From CoreErlang.BigStep Require Export BigStep.
From CoreErlang.FrameStack Require Export SubstSemantics.

Import BigStep.
Import ListNotations.

(**
* Help
  - Simple
    + name_sub
    + sum_eqb
    + literal_to_lit
    + vars_of_pattern_list
  - Add
    + add_name
    + add_names
    + add_vars
    + add_fids
* Main
  - erase_names_pat
  - erase_names_exp
*)

(**
TODO: erase_names_val
*)



Section Help.



  Section Simple.

    Definition name_sub
      {T}
      {dec : T -> T -> bool}
      :=
    T -> nat.

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

    Definition literal_to_lit
      (l : Literal)
      : Lit
      :=
    match l with
     | Atom s => s
     | Integer x => x
    end.

    Definition vars_of_pattern_list
      (l : list Pattern)
      : list Var
      :=
    fold_right 
      (fun x acc => variable_occurances x ++ acc)
      nil
      l.

  End Simple.



  Section Add.

    Definition add_name
      {T dec}
      (v : T)
      (σ : @name_sub _ dec)
      :=
    fun x =>
      if dec x v
      then 0
      else S (σ x).

    Definition add_names
      {T}
      {dec : T -> T -> bool}
      (vl : list T)
      (σ : name_sub)
      : name_sub
      :=
    fold_right
      (@add_name _ dec)
      σ
      vl.

    Definition add_vars
      (vl : list string)
      (σ : @name_sub
        (string + FunctionIdentifier)
        (sum_eqb eqb (prod_eqb eqb Nat.eqb)))
      : @name_sub
        (string + FunctionIdentifier)
        (sum_eqb eqb (prod_eqb eqb Nat.eqb))
      :=
    add_names (map inl vl) σ.

    Definition add_fids
      (vl : list FunctionIdentifier)
      (σ : @name_sub
        (string + FunctionIdentifier)
        (sum_eqb eqb (prod_eqb eqb Nat.eqb)))
      : @name_sub
        (string + FunctionIdentifier)
        (sum_eqb eqb (prod_eqb eqb Nat.eqb))
      :=
      add_names (map inr vl) σ.

  End Add.



End Help.






Section Main.



  Fixpoint erase_names_pat
    (p : Pattern)
    : Pat
    :=
  match p with
  | PNil => Syntax.PNil
  | PVar v => Syntax.PVar

  | PLit l => Syntax.PLit
      (literal_to_lit l)

  | PCons hd tl => Syntax.PCons
      (erase_names_pat hd)
      (erase_names_pat tl)

  | PTuple l => Syntax.PTuple
      (map erase_names_pat l)

  | PMap l => Syntax.PMap
      (map (fun '(x, y) => (erase_names_pat x, erase_names_pat y)) l)
  end.



  Fixpoint erase_names_exp
    (σᵥ : @name_sub
      (string + FunctionIdentifier)
      (sum_eqb eqb (prod_eqb eqb Nat.eqb)))
    (e : Expression)
    : Exp
    :=
  match e with
  | ENil => ˝Syntax.VNil

  | ELit l => ˝Syntax.VLit
      (literal_to_lit l)

  | EVar v => ˝Syntax.VVar
      (σᵥ (inl v))

  | EFunId f => ˝Syntax.VFunId
      ((σᵥ (inr f)), snd f)

  | EValues el => Syntax.EValues
      (map (erase_names_exp σᵥ) el)

  | EFun vl e => Syntax.EFun
      (length vl)
      (erase_names_exp (add_vars vl σᵥ) e)

  | ECons hd tl => Syntax.ECons
      (erase_names_exp σᵥ hd)
      (erase_names_exp σᵥ tl)

  | ETuple l => Syntax.ETuple
      (map (erase_names_exp σᵥ) l)

  | ECall m f l => Syntax.ECall
      (erase_names_exp σᵥ m)
      (erase_names_exp σᵥ f)
      (map (erase_names_exp σᵥ) l)

  | EPrimOp f l => Syntax.EPrimOp
      f
      (map (erase_names_exp σᵥ) l)

  | EApp exp l => Syntax.EApp
      (erase_names_exp σᵥ exp)
      (map (erase_names_exp σᵥ) l)

  | ECase e l => Syntax.ECase
      (erase_names_exp σᵥ e)
      (map 
        (fun '(pl, g, b) =>
          ((map erase_names_pat pl),
          erase_names_exp (add_vars (vars_of_pattern_list pl) σᵥ) g,
          erase_names_exp (add_vars (vars_of_pattern_list pl) σᵥ) b))
        l)

  | ELet l e1 e2 => Syntax.ELet
      (length l)
      (erase_names_exp σᵥ e1)
      (erase_names_exp (add_vars l σᵥ) e2)

  | ESeq e1 e2 => Syntax.ESeq
      (erase_names_exp σᵥ e1)
      (erase_names_exp σᵥ e2)

  | ELetRec l e => Syntax.ELetRec
      (map
        (fun '(fid, (vl, b)) =>
          (length vl,
          erase_names_exp 
            (add_names (map (inr ∘ fst) l ++ map inl vl) σᵥ)
            e))
        l)
      (erase_names_exp (add_fids (map fst l) σᵥ) e)

  | EMap l => Syntax.EMap
      (map
        (fun '(x, y) =>
          (erase_names_exp σᵥ x,
          erase_names_exp σᵥ y))
      l)

  | ETry e1 vl1 e2 vl2 e3 => Syntax.ETry
      (erase_names_exp σᵥ e1)
      (length vl1) (erase_names_exp (add_vars vl1 σᵥ) e2)
      (length vl2) (erase_names_exp (add_vars vl1 σᵥ) e3)
  end.



  Fixpoint erase_names_val
    (σᵥ : @name_sub
      (string + FunctionIdentifier)
      (sum_eqb eqb (prod_eqb eqb Nat.eqb)))
    (v : Value)
    : Val
    :=
  match v with
  | VNil => Syntax.VNil

  | VLit l => Syntax.VLit
      (literal_to_lit l)

  | VClos env ext id vl e fid => Syntax.VClos
      (map
        (fun '(n, fid, fe) =>
          (n,
          snd fid,
          erase_names_exp σᵥ (snd fe)))
        ext)
      id
      (length vl)
      (erase_names_exp σᵥ e)

  | VCons vhd vtl => Syntax.VCons
      (erase_names_val σᵥ vhd)
      (erase_names_val σᵥ vtl)

  | VTuple vl => Syntax.VTuple
      (map (erase_names_val σᵥ) vl)

  | VMap l => Syntax.VMap
      (map
        (fun '(x, y) =>
          (erase_names_val σᵥ x,
          erase_names_val σᵥ y))
        l)
  end.



End Main.