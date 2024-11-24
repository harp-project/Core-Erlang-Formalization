From CoreErlang.Eq.BsFs Require Export B19MeasureReductionLemmas.

Import BigStep.

(* STRUCTURE:
* Convert Length
  - bvs_to_fvs_length
* Simplify
  - add_exp_ext_fids_smp
* Mappers
  - bval_to_fval_vtuple
  - bval_to_fval_vmap
* AddVars Value
  - bval_to_fval_add_vars_vcons
  - bval_to_fval_add_vars_vtuple
  - bval_to_fval_add_vars_vmap
  - bval_to_fval_add_vars
* AddVars Expression
  - bexp_to_fexp_add_vars_comm
  - bexp_to_fexp_add_vars
*)












Section ConvertLength.



  Lemma bvs_to_fvs_length :
    forall fns vs,
      Datatypes.length (bvs_to_fvs fns vs)
    = Datatypes.length vs.
  Proof.
    itr.
    ind - vs as [| v vs Hvs]: bmp |> smp.
    bwr - Hvs.
  Qed.



End ConvertLength.









Section Simplify.



  Lemma add_exp_ext_fids_smp :
    forall n env l
      (ext : list (FunctionIdentifier * FunctionExpression))
      (f : list Var
        -> list (FunctionIdentifier * FunctionExpression)
        -> Environment
        -> Environment),
      add_exp_ext_fids
        (map
          (fun '(fid, (vars, body)) =>
             (fid,
              (vars,
               subst_env n (f vars l env) body)))
          ext)
    = add_fids (map fst ext).
  Proof.
    (* #1 Unfold: intro/undfold/f_equal *)
    itr.
    ufl - add_exp_ext_fids.
    feq.
    (* #2 Induction Extension: induction/f_equal/apply + simpl *)
    ind - ext as [| [a [b c]] ext' IH] :> smp.
    feq.
    app - IH.
  Qed.



End Simplify.









Section Mappers.



  Lemma bval_to_fval_vtuple :
    forall f bvl fvl,
        map (bval_to_fval f) bvl = fvl
    <-> bval_to_fval f (VTuple bvl) = Syntax.VTuple fvl.
  Proof.
    itr.
    spl; itr.
    * smp; f_equal; exact H.
    * smp - H; inj - H as H; exact H.
  Qed.



  Lemma bval_to_fval_vmap :
    forall f bvll fvll,
        (map (prod_map (bval_to_fval f) (bval_to_fval f)) bvll) = fvll
    <-> bval_to_fval f (VMap bvll) = Syntax.VMap fvll.
  Proof.
    itr.
    spl; itr.
    * smp; f_equal; exact H.
    * smp - H; inj - H as H; exact H.
  Qed.



End Mappers.









Section AddVars_Value.



  Theorem bval_to_fval_add_vars_vcons :
    forall bv1 bv2 vars f,
        (forall fv,
            bval_to_fval f bv1 = fv
        ->  bval_to_fval (add_vars vars f) bv1 = fv)
    ->  (forall fv,
            bval_to_fval f bv2 = fv
        ->  bval_to_fval (add_vars vars f) bv2 = fv)
    ->  (forall fv,
            bval_to_fval f (VCons bv1 bv2) = fv
        ->  bval_to_fval (add_vars vars f) (VCons bv1 bv2) = fv).
  Proof.
    (* #1 Intro: intro/induction/destruct/inversion/simpl *)
    itr - bv1 bv2 vars f Heq_v1 Heq_v2 fv Heq.
    smp + Heq.
    (* #2 Apply: apply/inversion/destruct/rewrite *)
    app - vcons_inj in Heq.
    ivc - Heq as fv1 Heq: x H.
    ivc - Heq as fv2 Heq: x H.
    des - Heq as [Hv1 [Hv2 Heq]].
    cwr - Heq.
    (* #3 Specialize: specialize/apply *)
    spc - Heq_v1: fv1 Hv1.
    spc - Heq_v2: fv2 Hv2.
    (* #4 Rewrite: f_equal/rewrite/assumption *)
    f_equal; asm.
  Qed.



  Theorem bval_to_fval_add_vars_vtuple :
    forall bvl vars f,
        Forall (fun bv =>
            (forall fv,
                  bval_to_fval f bv = fv
              ->  bval_to_fval (add_vars vars f) bv = fv))
          bvl
    ->  (forall fv,
            bval_to_fval f (VTuple bvl) = fv
        ->  bval_to_fval (add_vars vars f) (VTuple bvl) = fv).
  Proof.
    (* #1 Intro: intro/induction/destruct/inversion/simpl *)
    itr - bvl vars f HForall.
    ind - bvl as [| bv bvl Heq_vl]: itr; bmp |> smp.
    itr - fv' Heq.
    ivr - HForall; clr - HForall H H0 x l; ren - Heq_v HForall: H1 H2.
    smp + Heq.
    (* #2 Apply: apply/inversion/destruct/rewrite *)
    app - vtuple_inj in Heq.
    ivc - Heq as fv Heq: x H.
    ivc - Heq as fvl Heq: x H.
    des - Heq as [Hv [Hvl Heq]].
    cwr - Heq in *.
    (* #3 Specialize: specialize/apply *)
    app - bval_to_fval_vtuple in Hvl.
    spc - Heq_v: fv Hv.
    spc - Heq_vl: HForall (Syntax.VTuple fvl) Hvl.
    app - bval_to_fval_vtuple in Heq_vl.
    (* #4 Rewrite: f_equal/rewrite/assumption *)
    f_equal.
    bwr - Heq_v Heq_vl.
  Qed.



  Theorem bval_to_fval_add_vars_vmap :
    forall bvll vars f,
        Forall (fun bv =>
            (forall fv,
                bval_to_fval f bv.1 = fv
            ->  bval_to_fval (add_vars vars f) bv.1 = fv)
        /\  (forall fv,
                bval_to_fval f bv.2 = fv
            ->  bval_to_fval (add_vars vars f) bv.2 = fv))
          bvll
    ->  (forall fv,
            bval_to_fval f (VMap bvll) = fv
        ->  bval_to_fval (add_vars vars f) (VMap bvll) = fv).
  Proof.
    (* #1 Intro: intro/induction/destruct/inversion/simpl *)
    itr - bvll vars f HForall.
    ind - bvll as [| bv bvl Heq_vll]: itr; bmp |> smp.
    des - bv as [bv1 bv2].
    itr - fv' Heq.
    ivr - HForall; clr - HForall H H0 x l; ren - Heq_v HForall: H1 H2.
    des - Heq_v as [Heq_v1 Heq_v2].
    smp + Heq Heq_v1 Heq_v2.
    (* #2 Apply: apply/inversion/destruct/rewrite *)
    app - vmap_inj in Heq.
    ivc - Heq as fv1 Heq: x H.
    ivc - Heq as fv2 Heq: x H.
    ivc - Heq as fvll Heq: x H.
    des - Heq as [Hv1 [Hv2 [Hvll Heq]]].
    cwr - Heq in *.
    (* #3 Specialize: specialize/apply *)
    app - bval_to_fval_vmap in Hvll.
    spc - Heq_v1: fv1 Hv1.
    spc - Heq_v2: fv2 Hv2.
    spc - Heq_vll: HForall (Syntax.VMap fvll) Hvll.
    app - bval_to_fval_vmap in Heq_vll.
    (* #4 Rewrite: f_equal/rewrite/assumption *)
    f_equal.
    bwr - Heq_v1 Heq_v2 Heq_vll.
  Qed.



  Theorem bval_to_fval_add_vars :
    forall bv vars f fv,
        bval_to_fval f bv = fv
    ->  bval_to_fval (add_vars vars f) bv = fv.
  Proof.
    (* #1 Intro: intro/induction using ind_val *)
    itr - bv vars f.
    ind ~ ind_val - bv.
    (* #2 Nil & Lit: *)
    1-2: itr - fv Heq; ivr - Heq; bbn.
    (* #3 Cons: *)
    1: bse - bval_to_fval_add_vars_vcons: bv1 bv2 vars f IHbv1 IHbv2.
    (* #4 Tuple: *)
    2: bse - bval_to_fval_add_vars_vtuple: l vars f H.
    (* #5 Map: *)
    2: bse - bval_to_fval_add_vars_vmap: l vars f H.
    (* #6 Clos: *)
    1: admit.
    (* Not Provable / Not True *)
  Admitted.



  Theorem bvs_to_fvs_add_vars :
    forall bvs fvs vars f,
        bvs_to_fvs f bvs = fvs
    ->  bvs_to_fvs (add_vars vars f) bvs = fvs.
  Proof.
    (* #1 Intro: intro/induction/destruct/inversion/simpl *)
    itr - bvs.
    ind - bvs as [| bv bvs IHbvs]: itr; bvs - H.
    itr - fvs vars f Heq.
    des - fvs as [| fv fvs]: ivs - Heq.
    smp + Heq.
    (* #2 Apply: apply/inversion/destruct/rewrite *)
    app - cons_inj in Heq.
    des - Heq as [Hv Hvs].
    (* #3 Specialize: specialize/apply *)
    psc - bval_to_fval_add_vars as Heq_v: bv vars f fv Hv.
    spc - IHbvs as Heq_vs: fvs vars f Hvs.
    (* #4 Rewrite: f_equal/rewrite/assumption *)
    bwr - Heq_v Heq_vs.
  Qed.



End AddVars_Value.









Section AddVars_Expression.



  Theorem bexp_to_fexp_add_vars_comm :
    forall e env vars1 vars2 fns,
      bexp_to_fexp
        (add_vars vars1 (add_vars vars2 fns))
        (subst_env (measure_exp e + measure_env env) env e)
    = bexp_to_fexp
        (add_vars vars2 (add_vars vars1 fns))
        (subst_env (measure_exp e + measure_env env) env e).
  Proof.
    (* #1 Expression Induction: *)
    itr - e.
    ind ~ ind_exp - e; itr.
    all: admit.
    (* Not Provable / Not True *)
  Admitted.



  Theorem bexp_to_fexp_add_vars :
    forall e fns vars vs env,
      bexp_to_fexp_subst fns (append_vars_to_env vars vs env) e
    = (bexp_to_fexp_subst (add_vars vars fns) (rem_vars vars env) e)
      .[list_subst (bvs_to_fvs fns vs) idsubst].
  Proof.
    (* #0 Expression Induction: *)
    itr - e.
    ind ~ ind_exp - e
      :- itr; sbn
      |> itr; ufl - bexp_to_fexp_subst in *; smp.
    5: { (* Cons *)
      (* +1 Simplify: rename *)
      ren - Heq_e1 Heq_e2: IHe1 IHe2.
      (* +2 Measure Reduction: rewrite *)
      do 2 rwr - mred_e1e2_e1.
      do 2 rwr - mred_e1e2_e2.
      (* +3 Specialize: specialize *)
      spe - Heq_e1: fns vars vs env.
      spc - Heq_e2: fns vars vs env.
      (* +4 Rewrite Induction: unfold/rewrite *)
      ufl - measure_env_exp in *.
      bwr - Heq_e1 Heq_e2.
    }
    11: { (* Seq *)
      (* +1 Simplify: rename *)
      ren - Heq_e1 Heq_e2: IHe1 IHe2.
      (* +2 Measure Reduction: rewrite *)
      do 2 rwr - mred_e1e2_e1.
      do 2 rwr - mred_e1e2_e2.
      (* +3 Specialize: specialize *)
      spe - Heq_e1: fns vars vs env.
      spc - Heq_e2: fns vars vs env.
      (* +4 Rewrite Induction: unfold/rewrite *)
      ufl - measure_env_exp in *.
      bwr - Heq_e1 Heq_e2.
    }
    10: { (* Let *)
      (* +1 Simplify: rename *)
      ren - Heq_e1 Heq_e2: IHe1 IHe2.
      (* +2 Measure Reduction: rewrite *)
      do 2 rwr - mred_e1e2_e1.
      do 2 rwr - mred_e1e2_e2_rem_vars.
      (* +3 Specialize: specialize *)
      spe - Heq_e1: fns vars vs env.
      spc - Heq_e2: fns vars vs env.
      (* +4 Rewrite Induction: unfold/rewrite *)
      ufl - measure_env_exp in *.
      adm. (* Add/Rem Vars not Commutative *)
    }
    12: { (* Try*)
      (* +1 Simplify: rename *)
      ren - Heq_e1 Heq_e2 Heq_e3: IHe1 IHe2 IHe3.
      (* +2 Measure Reduction: rewrite *)
      do 2 rwr - mred_e1e2e3_e1.
      do 2 rwr - mred_e1e2e3_e2_rem_vars.
      do 2 rwr - mred_e1e2e3_e3_rem_vars.
      (* +3 Specialize: specialize *)
      spe - Heq_e1: fns vars vs env.
      spc - Heq_e2: fns vars vs env.
      spc - Heq_e3: fns vars vs env.
      (* +4 Rewrite Induction: unfold/rewrite *)
      ufl - measure_env_exp in *.
      adm. (* Add/Rem Vars not Commutative *)
    }
    all: admit.
    (* Not Provable / Not True *)
  Admitted.



  Theorem bexp_to_fexp_add_fids :
    forall e fns ext id env,
      bexp_to_fexp_subst fns (append_funs_to_env ext env id) e
    = (bexp_to_fexp_subst (add_fids (map fst ext) fns) (rem_exp_ext_fids ext env) e)
      .[list_subst
        (convert_to_closlist
          (map (λ '(x, y), (0, x, y))
            (map
              (λ '(_, (vars, body)),
                (base.length vars,
                bexp_to_fexp (add_fids (map fst ext) (add_vars vars fns)) body))
                (map
                  (λ '(fid, (vars, body)),
                     (fid,
                     (vars,
                     subst_env
                      (measure_env_exp (rem_exp_ext_both vars ext env) body)
                      (rem_exp_ext_both vars ext env)
                      body)))
                  ext)))) idsubst].
  Proof.
  Admitted.



End AddVars_Expression.