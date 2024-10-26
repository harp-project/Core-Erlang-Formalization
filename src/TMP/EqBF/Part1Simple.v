From CoreErlang.TMP.EqBF Require Export Base.

Import BigStep.













(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: VALTOEXP /////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* Help
  - bval_to_bexp_ext
* Main
  - bval_to_bexp
*)






Section ValToExp_Help.



  Definition bval_to_bexp_ext
	  (f : Environment -> Expression -> Expression)
	  (env : Environment)
	  (ext : list (nat * FunctionIdentifier * FunctionExpression))
	  : list (FunctionIdentifier * (list Var * Expression))
	  :=
  map
	  (fun '(n, fid, (vl, e)) =>
    	(fid,
      	(vl,
      	(f (rem_vars vl env) e))))
	  ext.



End ValToExp_Help.






Section ValToExp_Main.



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



End ValToExp_Main.













(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: SUBSTITUTE ///////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* Main
  - subst_env
  - subst_env2
*)




Section Substitue.



  Fixpoint subst_env
	  (fuel : nat)
	  (env : Environment)
	  (e : Expression)
	  : Expression
	  :=
  match fuel with
  (* This is None in option version *)
  | O => e
  | S fuel' =>
      match e with
      | ENil => e
      | ELit l => e

      | EValues el => EValues
          (map (subst_env fuel' env) el)

      | EFun vl e => EFun
          vl
          (subst_env fuel' env e)

      | ECons hd tl => ECons
          (subst_env fuel' env hd)
          (subst_env fuel' env tl)

      | ETuple l => ETuple
          (map (subst_env fuel' env) l)

      | ECall m f l => ECall
          (subst_env fuel' env m)
          (subst_env fuel' env f)
          (map (subst_env fuel' env) l)

      | EPrimOp f l => EPrimOp
          f
          (map (subst_env fuel' env) l)

      | EApp exp l => EApp
          (subst_env fuel' env exp)
          (map (subst_env fuel' env) l)

      | ECase e l => ECase
          (subst_env fuel' env e)
          (map
            (fun '(pl, g, b) =>
              (pl,
              (subst_env fuel' env g),
              (subst_env fuel' env b)))
            l)

      | ELet l e1 e2 => ELet
          l
          (subst_env fuel' env e1)
          (subst_env fuel' (rem_vars l env) e2)

      | ESeq e1 e2 => ESeq
          (subst_env fuel' env e1)
          (subst_env fuel' env e2)

      | ELetRec l e => ELetRec
          (map
            (fun '(fid, (vl, b)) =>
              (fid,
              (vl,
              (subst_env fuel' (rem_both l vl env) b))))
            l)
          (subst_env fuel' (rem_fids l env) e)

      | EMap l => EMap
          (map
            (prod_map
              (subst_env fuel' env)
              (subst_env fuel' env))
            l)

      | ETry e1 vl1 e2 vl2 e3 => ETry
          (subst_env fuel' env e1)
          vl1
          (subst_env fuel' (rem_vars vl1 env) e2)
          vl2
          (subst_env fuel' (rem_vars vl2 env) e3)

      | EVar var =>
          match (get_value env (inl var)) with
          | Some [v] => bval_to_bexp (subst_env fuel') v
          | Some vs => EValues
              (map (bval_to_bexp (subst_env fuel')) vs)
          | _ => e
          end

      | EFunId fid =>
          match (get_value env (inr fid)) with
          | Some [v] => bval_to_bexp (subst_env fuel') v
          | Some vs => EValues
              (map (bval_to_bexp (subst_env fuel')) vs)
          | _ => e
          end
      end
  end.



End Substitue.













(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: SUBSTITUTELEMMAS /////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* Main
  - subst_env_empty
*)






Section SubstituteLemmas.



  (*NotUsing*)
  Theorem subst_env_empty :
    forall n e,
      subst_env n [] e = e.
  Proof.
    intros.
    generalize dependent n.
    ind + ind_exp - e.
    * (* Values *)
      rename H into HForall.
      induction el as [| e el IHel]; intros; destruct n; cbn.
      1-3: reflexivity.
      inv HForall.
      rename H1 into He.
      rename H2 into HForall.
      specialize (IHel HForall (S n)).
      clear HForall.
      cbn.
      f_equal.
      rewrite He.
      clear He.
      cbn in IHel.
      injection IHel; intros Hel.
      clear IHel.
      rewrite Hel.
      reflexivity.
    * destruct n; by cbn.
    * destruct n; by cbn.
    * destruct n; by cbn.
    * destruct n; by cbn.
    * (* Fun *)
      destruct n; cbn.
      - reflexivity.
      - specialize (IHe n).
        rewrite IHe.
        reflexivity.
    * (* Cons *)
      destruct n; cbn.
      - reflexivity.
      - specialize (IHe1 n).
        specialize (IHe2 n).
        rewrite IHe1.
        rewrite IHe2.
        reflexivity.
    * (* Tuple *)
      rename H into HForall.
      induction l as [| e el IHel]; intros; destruct n; cbn.
      1-3: reflexivity.
      inv HForall.
      rename H1 into He.
      rename H2 into HForall.
      specialize (IHel HForall (S n)).
      clear HForall.
      cbn.
      f_equal.
      rewrite He.
      clear He.
      cbn in IHel.
      injection IHel; intros Hel.
      clear IHel.
      rewrite Hel.
      reflexivity.
    * (* Call *)
      rename H into HForall.
      induction l as [| e el IHel]; intros; destruct n; cbn.
      2: rewrite IHe1; by rewrite IHe2.
      1-2: reflexivity.
      rewrite IHe1.
      rewrite IHe2.
      inv HForall.
      rename H1 into He.
      rename H2 into HForall.
      specialize (IHel HForall (S n)).
      clear HForall.
      cbn.
      f_equal.
      rewrite He.
      clear He.
      cbn in IHel.
      injection IHel; intros Hel.
      clear IHel.
      rewrite Hel.
      reflexivity.
    * (* PrimOp *)
      rename H into HForall.
      induction l as [| e el IHel]; intros; destruct n; cbn.
      1-3: reflexivity.
      inv HForall.
      rename H1 into He.
      rename H2 into HForall.
      specialize (IHel HForall (S n)).
      clear HForall.
      cbn.
      f_equal.
      rewrite He.
      clear He.
      cbn in IHel.
      injection IHel; intros Hel.
      clear IHel.
      rewrite Hel.
      reflexivity.
    * (* App *)
      rename e into e'.
      rename H into HForall.
      induction l as [| e el IHel]; intros; destruct n; cbn.
      2: by rewrite IHe.
      1-2: reflexivity.
      inv HForall.
      rename H1 into He.
      rename H2 into HForall.
      specialize (IHel HForall (S n)).
      clear HForall.
      cbn in IHel.
      inv IHel.
      clear H0.
      rename H1 into Hel.
      rewrite IHe.
      rewrite IHe.
      rewrite He.
      rewrite Hel.
      rewrite Hel.
      reflexivity.
    * (* Case *)
      rename e into e'.
      rename H into HForall.
      induction l as [| e el IHel]; intros; destruct n; cbn.
      2: by rewrite IHe.
      1-2: reflexivity.
      inv HForall.
      destruct e as [e e2].
      destruct e as [p e1].
      destruct H1.
      cbn in *.
      rename H into He1.
      rename H0 into He2.
      rename H2 into HForall.
      specialize (IHel HForall (S n)).
      clear HForall IHe.
      cbn in IHel.
      injection IHel; intros Hel He.
      clear IHel.
      rewrite He.
      rewrite Hel.
      rewrite He1.
      rewrite He2.
      reflexivity.
    * (* Let *)
      destruct n; cbn.
      - reflexivity.
      - rewrite rem_vars_empty.
        rewrite IHe1.
        rewrite IHe2.
        reflexivity.
    * (* Seq *)
      destruct n; cbn.
      - reflexivity.
      - rewrite IHe1.
        rewrite IHe2.
        reflexivity.
    * (* LetRec *)
      rename e into e'.
      rename H into HForall.
      induction l as [| e el IHel]; intros; destruct n.
      2: cbn; by rewrite IHe.
      1-2: reflexivity.
      inv HForall.
      destruct e as [f e].
      destruct e as [l e].
      cbn in H1.
      rename H1 into He.
      rename H2 into HForall.
      specialize (IHel HForall (S n)).
      clear HForall.
      cbn in IHel.
      injection IHel; intros Hefid Hel.
      clear IHel.
      simpl.
      rewrite rem_fids_empty.
      rewrite IHe.
      rewrite rem_both_empty.
      rewrite He.
      cbn.
      do 2 f_equal.
      rewrite <- Hel at 2.
      apply map_ext.
      intros [fid [vl b]].
      do 3 f_equal.
      rewrite rem_fids_fold.
      rewrite rem_vars_empty.
      rewrite rem_fids_empty.
      rewrite rem_both_empty.
      reflexivity.
    * (* Map *)
      rename H into HForall.
      induction l as [| e el IHel]; intros; destruct n; cbn.
      1-3: reflexivity.
      inv HForall.
      destruct e as [e1 e2].
      destruct H1.
      rename H into He1.
      rename H0 into He2.
      rename H2 into HForall.
      specialize (IHel HForall (S n)).
      clear HForall.
      cbn.
      f_equal.
      rewrite He1.
      rewrite He2.
      clear He1 He2.
      cbn in *.
      injection IHel; intros Hel.
      clear IHel.
      rewrite Hel.
      reflexivity.
    * (* Try *)
      destruct n; cbn.
      - reflexivity.
      - rewrite rem_vars_empty.
        rewrite rem_vars_empty.
        rewrite IHe1.
        rewrite IHe2.
        rewrite IHe3.
        reflexivity.
  Qed.



End SubstituteLemmas.















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


  (* History: ETry: at e3 it used vl1 instead of vl2 *)
  Fixpoint bexp_to_fexp
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
      (map (bexp_to_fexp σᵥ) el)

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
  end.



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
            (subst_env (measure_env_exp env b) env b)))
        ext)
      id
      (length vl)
      (bexp_to_fexp
        (add_fids (map (snd ∘ fst) ext) σᵥ)
        (subst_env (measure_env_exp env e) env e))

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













(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: CONVERT //////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* Main
  - bexp_to_fexp_subst
  - bvs_to_fvs
  - bexcc_to_fexcc
  - bexc_to_fexc
  - bres_to_fres
*)






Section Convert.



  Definition bexp_to_fexp_subst
    f
    (env : Environment)
    (e : Expression)
    : Exp
    :=
  bexp_to_fexp
    f
    (subst_env
      (measure_env_exp
        env
        e)
      env
      e).



  Definition bvs_to_fvs
    f
    (vs : ValueSequence)
    : ValSeq
    :=
  map
    (bval_to_fval f)
    vs.



  Definition bec_to_fec
    (ec : ExceptionClass)
    : CoreErlang.Syntax.ExcClass
    :=
  match ec with
  | Error => CoreErlang.Syntax.Error
  | Throw => CoreErlang.Syntax.Throw
  | Exit => CoreErlang.Syntax.Exit
  end.


  (* History: excc part separated in a new bexcc_to_fexcc *)
  Definition bexc_to_fexc
    f
    (exc : Exception)
    : CoreErlang.Syntax.Exception
    :=
  match exc with
  | (ec, v1, v2) =>
      (bec_to_fec ec,
      bval_to_fval f v1,
      bval_to_fval f v2)
  end.



  Definition bres_to_fres
    f
    (res : (ValueSequence + Exception))
    : Redex
    :=
  match res with
  | inl vs =>
      match (bvs_to_fvs f vs) with
      | vs' => RValSeq vs'
      end
  | inr exc => 
      match (bexc_to_fexc f exc) with
      | exc' => RExc exc'
      end
  end.



End Convert.