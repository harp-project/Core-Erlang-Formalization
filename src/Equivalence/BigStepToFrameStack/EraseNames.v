From CoreErlang.BigStep Require Import BigStep.
From CoreErlang.FrameStack Require Import SubstSemantics.



Import ListNotations.



(**

* Helpers
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






Section Helpers.



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
     | BigStep.Syntax.Atom s => s
     | BigStep.Syntax.Integer x => x
    end.

    Definition vars_of_pattern_list
      (l : list Pattern)
      : list BigStep.Syntax.Var 
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



End Helpers.






Section Main.



  Fixpoint erase_names_pat
    (p : Pattern)
    : Pat
    :=
  match p with
  | BigStep.Syntax.PNil => PNil
  |
   BigStep.Syntax.PVar v => PVar

  | BigStep.Syntax.PLit l => PLit
      (literal_to_lit l)

  | BigStep.Syntax.PCons hd tl => PCons
      (erase_names_pat hd)
      (erase_names_pat tl)

  | BigStep.Syntax.PTuple l => PTuple
      (map erase_names_pat l)

  | BigStep.Syntax.PMap l => PMap
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
  | ENil => ˝VNil

  | ELit l => ˝VLit
      (literal_to_lit l)

  | EVar v => ˝VVar
      (σᵥ (inl v))

  | EFunId f => ˝VFunId
      ((σᵥ (inr f)), snd f)

  | BigStep.Syntax.EValues el => EValues
      (map (erase_names_exp σᵥ) el)

  | BigStep.Syntax.EFun vl e => EFun
      (length vl)
      (erase_names_exp (add_vars vl σᵥ) e)
  | BigStep.Syntax.ECons hd tl => ECons
      (erase_names_exp σᵥ hd)
      (erase_names_exp σᵥ tl)

  | BigStep.Syntax.ETuple l => ETuple
      (map (erase_names_exp σᵥ) l)

  | BigStep.Syntax.ECall m f l => ECall
      (erase_names_exp σᵥ m)
      (erase_names_exp σᵥ f)
      (map (erase_names_exp σᵥ) l)

  | BigStep.Syntax.EPrimOp f l => EPrimOp
      f
      (map (erase_names_exp σᵥ) l)

  | BigStep.Syntax.EApp exp l => EApp
      (erase_names_exp σᵥ exp)
      (map (erase_names_exp σᵥ) l)

  | BigStep.Syntax.ECase e l => ECase 
      (erase_names_exp σᵥ e)
      (map 
        (fun '(pl, g, b) =>
          ((map erase_names_pat pl), 
          erase_names_exp (add_vars (vars_of_pattern_list pl) σᵥ) g,
          erase_names_exp (add_vars (vars_of_pattern_list pl) σᵥ) b))
        l)

  | BigStep.Syntax.ELet l e1 e2 => ELet
      (length l)
      (erase_names_exp σᵥ e1)
      (erase_names_exp (add_vars l σᵥ) e2)

  | BigStep.Syntax.ESeq e1 e2 => ESeq
      (erase_names_exp σᵥ e1)
      (erase_names_exp σᵥ e2)

  | BigStep.Syntax.ELetRec l e => ELetRec
      (map
        (fun '(fid, (vl, b)) =>
          (length vl,
          erase_names_exp (add_names (map (inr ∘ fst) l ++ map inl vl) σᵥ) e))
        l)
      (erase_names_exp (add_fids (map fst l) σᵥ) e)

  | BigStep.Syntax.EMap l => EMap
      (map
        (fun '(x, y) =>
          (erase_names_exp σᵥ x,
          erase_names_exp σᵥ y))
      l)

  | BigStep.Syntax.ETry e1 vl1 e2 vl2 e0 => ETry
      (erase_names_exp σᵥ e1)
      (length vl1) (erase_names_exp (add_vars vl1 σᵥ) e2)
      (length vl2) (erase_names_exp (add_vars vl1 σᵥ) e0)
  end.



End Main.