From CoreErlang.TMP.EqBF Require Export Base.

Import BigStep.








(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: ERASENAMES ///////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



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
  - bpat_to_fpat
  - bexp_to_fexp
*)






Section EraseNames_Help.



  Section EraseNames_Help_Simple.

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

  End EraseNames_Help_Simple.



  Section EraseNames_Help_Add.

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

  End EraseNames_Help_Add.



End EraseNames_Help.




(*
  Definition bval_to_bexp_ext
	  (f : (@name_sub
      (string + FunctionIdentifier)
      (sum_eqb eqb (prod_eqb eqb Nat.eqb)))
      -> Environment -> Expression -> Expression)
	  (σᵥ : @name_sub
      (string + FunctionIdentifier)
      (sum_eqb eqb (prod_eqb eqb Nat.eqb)))
	  (env : Environment)
	  (ext : list (nat * FunctionIdentifier * FunctionExpression))
	  : list (FunctionIdentifier * (list Var * Expression))
	  :=
  map
	  (fun '(n, fid, (vl, e)) =>
    	(fid,
      	(vl,
      	(f σᵥ (rem_vars vl env) e))))
	  ext.

  Fixpoint bval_to_bexp
	  (f : Environment -> Expression -> Expression)
	  (v : Value)
	  : Expression
	  :=
  match v with
  | VNil => ENil

  | VLit l => ELit l

  | VCons hd tl => ECons
    	(bval_to_bexp f hd)
    	(bval_to_bexp f tl)

  | VTuple l => ETuple
  	  (map (bval_to_bexp f) l)

  | VMap l => EMap
    	(map
      	(prod_map
        	(bval_to_bexp f)
        	(bval_to_bexp f))
      	l)

  | VClos env ext id vl e fid =>
    	match ext, fid with
    	| [], _ => EFun
        	vl
        	(f (rem_vars vl env) e)

    	(* This is None in option version *)
    	| _, None => EFun
        	vl
        	(f (rem_vars vl env) e)

    	| _, Some fid' => ELetRec
        	(bval_to_bexp_ext
          	f
          	(rem_nfifes ext env)
          	ext)
        	(EFunId fid')
    	end
  end.
*)


Section EraseNames_Main.



  Fixpoint bpat_to_fpat
    (p : Pattern)
    : Pat
    :=
  match p with
  | PNil => Syntax.PNil
  | PVar v => Syntax.PVar

  | PLit l => Syntax.PLit
      (literal_to_lit l)

  | PCons hd tl => Syntax.PCons
      (bpat_to_fpat hd)
      (bpat_to_fpat tl)

  | PTuple l => Syntax.PTuple
      (map bpat_to_fpat l)

  | PMap l => Syntax.PMap
      (map (fun '(x, y) => (bpat_to_fpat x, bpat_to_fpat y)) l)
  end.



  Fixpoint bval_to_fval
    (bexp_to_fexp : (@name_sub
      (string + FunctionIdentifier)
      (sum_eqb eqb (prod_eqb eqb Nat.eqb)))
      -> Environment
      -> Expression
      -> Exp)
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

  | VClos env ext id vl e fid => Syntax.VNil
    Syntax.VClos
      (map
        (fun '(n, fid, (vl, b)) =>
          (n,
          length vl,
          bexp_to_fexp
            (add_names (map (inr ∘ snd ∘ fst) ext ++ map inl vl) σᵥ)
            (subst_env
              (measure_env_exp (rem_fid fid (rem_vars vl env)) b)
              (rem_fid fid (rem_vars vl env))
              b)))
        ext)
      0
      (length vl)
      (bexp_to_fexp
        (add_names (map (inr ∘ snd ∘ fst) ext ++ map inl vl) σᵥ)
        (subst_env (measure_env_exp (rem_vars vl env) e) (rem_vars vl env) e))

  | VCons vhd vtl => Syntax.VCons
      (bval_to_fval bexp_to_fexp σᵥ vhd)
      (bval_to_fval bexp_to_fexp σᵥ vtl)

  | VTuple vl => Syntax.VTuple
      (map (bval_to_fval bexp_to_fexp σᵥ) vl)

  | VMap l => Syntax.VMap
      (map
        (fun '(x, y) =>
          (bval_to_fval bexp_to_fexp σᵥ x,
          bval_to_fval bexp_to_fexp σᵥ y))
        l)
  end.



  (* History: ETry: at e3 it used vl1 instead of vl2 *)
  Fixpoint bexp_to_fexp
    (σᵥ : @name_sub
      (string + FunctionIdentifier)
      (sum_eqb eqb (prod_eqb eqb Nat.eqb)))
    (env : Environment)
    (e : Expression)
    : Exp
    :=
  match e with
  | ENil => ˝Syntax.VNil

  | ELit l => ˝Syntax.VLit
      (literal_to_lit l)

  | EVar v =>
      match (get_value env (inl var)) with
      | Some [v] => bval_to_bexp (subst_env fuel') v
      | _ => ˝Syntax.VVar
                (σᵥ (inl v))
      end
  
  
  

  | EFunId f => ˝Syntax.VFunId
      ((σᵥ (inr f)), snd f)

  | EValues el => Syntax.EValues
      (map (bexp_to_fexp σᵥ env) el)
(*
  | EFun vl e => Syntax.EFun
      (length vl)
      (bexp_to_fexp (add_vars vl σᵥ) e)

  | ECons hd tl => Syntax.ECons
      (bexp_to_fexp σᵥ hd)
      (bexp_to_fexp σᵥ tl)

  | ETuple l => Syntax.ETuple
      (map (bexp_to_fexp σᵥ) l)

  | ECall m f l => Syntax.ECall
      (bexp_to_fexp σᵥ m)
      (bexp_to_fexp σᵥ f)
      (map (bexp_to_fexp σᵥ) l)

  | EPrimOp f l => Syntax.EPrimOp
      f
      (map (bexp_to_fexp σᵥ) l)

  | EApp exp l => Syntax.EApp
      (bexp_to_fexp σᵥ exp)
      (map (bexp_to_fexp σᵥ) l)

  | ECase e l => Syntax.ECase
      (bexp_to_fexp σᵥ e)
      (map 
        (fun '(pl, g, b) =>
          ((map bpat_to_fpat pl),
          bexp_to_fexp (add_vars (vars_of_pattern_list pl) σᵥ) g,
          bexp_to_fexp (add_vars (vars_of_pattern_list pl) σᵥ) b))
        l)

  | ELet l e1 e2 => Syntax.ELet
      (length l)
      (bexp_to_fexp σᵥ e1)
      (bexp_to_fexp (add_vars l σᵥ) e2)

  | ESeq e1 e2 => Syntax.ESeq
      (bexp_to_fexp σᵥ e1)
      (bexp_to_fexp σᵥ e2)

  | ELetRec l e => Syntax.ELetRec
      (map
        (fun '(fid, (vl, b)) =>
          (length vl,
          bexp_to_fexp
            (add_names (map (inr ∘ fst) l ++ map inl vl) σᵥ)
            b))
        l)
      (bexp_to_fexp (add_fids (map fst l) σᵥ) e)

  | EMap l => Syntax.EMap
      (map
        (fun '(x, y) =>
          (bexp_to_fexp σᵥ x,
          bexp_to_fexp σᵥ y))
      l)

  | ETry e1 vl1 e2 vl2 e3 => Syntax.ETry
      (bexp_to_fexp σᵥ e1)
      (length vl1) (bexp_to_fexp (add_vars vl1 σᵥ) e2)
      (length vl2) (bexp_to_fexp (add_vars vl2 σᵥ) e3)
*)
  | _ => ˝Syntax.VNil
  end.


  (* Update
  * id = 0 (no id in Fs)
  * Clos e: add_vars added OLD: (add_fids (map (snd ∘ fst) ext) σᵥ)
  * Clos env: env -> (rem_vars vl env) & (rem_fid fid env)
  *)
  Fixpoint bval_to_fval
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
        (fun '(n, fid, (vl, b)) =>
          (n,
          length vl,
          bexp_to_fexp
            (add_names (map (inr ∘ snd ∘ fst) ext ++ map inl vl) σᵥ)
            (subst_env
              (measure_env_exp (rem_fid fid (rem_vars vl env)) b)
              (rem_fid fid (rem_vars vl env))
              b)))
        ext)
      0
      (length vl)
      (bexp_to_fexp
        (add_names (map (inr ∘ snd ∘ fst) ext ++ map inl vl) σᵥ)
        (subst_env (measure_env_exp (rem_vars vl env) e) (rem_vars vl env) e))

  | VCons vhd vtl => Syntax.VCons
      (bval_to_fval σᵥ vhd)
      (bval_to_fval σᵥ vtl)

  | VTuple vl => Syntax.VTuple
      (map (bval_to_fval σᵥ) vl)

  | VMap l => Syntax.VMap
      (map
        (fun '(x, y) =>
          (bval_to_fval σᵥ x,
          bval_to_fval σᵥ y))
        l)
  end.



End EraseNames_Main.










