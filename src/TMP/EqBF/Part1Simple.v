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


(*
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
*)

  Definition bval_to_bexp_ext
	  (ext : list (nat * FunctionIdentifier * FunctionExpression))
	  : list (FunctionIdentifier * (list Var * Expression))
	  :=
  map
	  (fun '(n, fid, (vl, e)) => (fid, (vl, e)))
	  ext.


End ValToExp_Help.






Section ValToExp_Main.



  Fixpoint bval_to_bexp
	  (subst_env : Environment -> Expression -> Expression)
	  (v : Value)
	  : Expression
	  :=
  match v with

  | VNil =>
    ENil

  | VLit l =>
    ELit l

  | VCons hd tl =>
    ECons
    	(bval_to_bexp subst_env hd)
    	(bval_to_bexp subst_env tl)

  | VTuple l =>
    ETuple
  	  (map (bval_to_bexp subst_env) l)

  | VMap l =>
    EMap
    	(map
      	(prod_map
        	(bval_to_bexp subst_env)
        	(bval_to_bexp subst_env))
      	l)

  | VClos env ext id vl e fid =>

      match ext, fid with

      | _ :: _, Some fid' =>
        (subst_env
          env
          (ELetRec
            (bval_to_bexp_ext ext)
            (EFunId fid')))

      | _, _ =>
        (subst_env
          env
          (EFun vl e))

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

Print prod_map.



Section Substitue.



  (* Update:
  * EFun -> (rem_fids l env)
  *)
  Fixpoint subst_env
	  (fuel : nat)
	  (env : Environment)
	  (e : Expression)
	  : Expression
	  :=
  match fuel with

  (* This branch won't matter, because measure_env_exp gives enought fuel *)
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

      | ECase e pleel =>
        ECase
          (subst_env fuel' env e)
          (map
            (fun '(pl, e1, e2) =>
              (pl,
              (subst_env fuel' env e1),
              (subst_env fuel' env e2)))
            pleel)

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

      | ECase e pleel =>
        ECase
          (subst_env fuel env e)
          (map
            (fun '(pl, e1, e2) =>
              (pl,
              (subst_env fuel env e1),
              (subst_env fuel env e2)))
            pleel)

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
      - rewrite IHe1.
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
      rewrite IHe.
      ufl - rem_exp_ext_both.
      smp.
      rewrite He.
      cbn.
      do 2 f_equal.
      rewrite <- Hel at 2.
      apply map_ext.
      intros [fid [vl b]].
      do 3 f_equal.
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
      - rewrite IHe1.
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



  Section EraseNames_Help_Transfrom.

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

  End EraseNames_Help_Transfrom.



  Section EraseNames_Help_Sum.

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

  End EraseNames_Help_Sum.



  Section EraseNames_Help_NameSub.

    Definition name_sub
      {T}
      {dec : T -> T -> bool}
      :=
    T -> nat.

    Definition NameSub :=
      @name_sub
        (Var + FunctionIdentifier)
        (sum_eqb eqb (prod_eqb eqb Nat.eqb)).

  End EraseNames_Help_NameSub.



  Section EraseNames_Help_AddNames.

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

  End EraseNames_Help_AddNames.



  Section EraseNames_Help_Adds.

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

  End EraseNames_Help_Adds.



End EraseNames_Help.






Section EraseNames_Main.



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


  (* History: ETry: at e3 it used vl1 instead of vl2 *)
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
        (fun '(fid, (vars, body)) =>
          (length vars,
          bexp_to_fexp (add_exp_ext_both vars ext fns) body))
        ext)
      (bexp_to_fexp (add_exp_ext_fids ext fns) e)

  | ECase e pleel =>
    Syntax.ECase
      (bexp_to_fexp fns e)
      (map 
        (fun '(pats, e1, e2) =>
          ((map bpat_to_fpat pats),
          bexp_to_fexp (add_pats pats fns) e1,
          bexp_to_fexp (add_pats pats fns) e2))
        pleel)

  | EVar var =>
    ˝Syntax.VVar
      (fns (inl var))

  | EFunId fid =>
    ˝Syntax.VFunId
      ((fns (inr fid)), snd fid)

  end.


  (* Update
  * id = 0 (no id in Fs)
  * Clos e: add_vars added OLD: (add_fids (map (snd ∘ fst) ext) fns)
  * Clos env: env -> (rem_vars vl env) & (rem_fid fid env)
  *)
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

  | VClos env ext id vars e fid =>

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
    : CoreErlang.Syntax.ExcClass
    :=
  match ec with
  | Error => CoreErlang.Syntax.Error
  | Throw => CoreErlang.Syntax.Throw
  | Exit => CoreErlang.Syntax.Exit
  end.


  (* History: excc part separated in a new bexcc_to_fexcc *)
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



  Definition bres_to_fres
    fns
    (res : (ValueSequence + Exception))
    : Redex
    :=
  match res with
  | inl vs => RValSeq (bvs_to_fvs fns vs)
  | inr exc => RExc (bexc_to_fexc fns exc)
  end.



End Convert.