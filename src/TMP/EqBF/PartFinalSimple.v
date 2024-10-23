From CoreErlang.TMP.EqBF Require Export Part3Simple.

Import BigStep.











(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: EQUIVALENCE  /////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)









Section Equivalence_Atoms1.



  Theorem eq_bs_to_fs_suc_nil :
    forall fns r env,
        bres_to_fres fns (inl [VNil]) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env ENil ⟩ -->* r.
  Proof.
    itr - fns r env Hres.
    ivc - Hres.
    framestack_scope.
    framestack_step.
  Qed.



  Theorem eq_bs_to_fs_suc_lit :
    forall fns r env l,
        bres_to_fres fns (inl [VLit l]) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ELit l) ⟩ -->* r.
  Proof.
    itr - fns r env l Hres.
    ivc - Hres.
    framestack_scope.
    framestack_step.
  Qed.



End Equivalence_Atoms1.









Section Equivalence_Atoms2.



  Theorem eq_bs_to_fs_suc_var :
    forall fns r env var vs,
        get_value env (inl var) = Some vs
    ->  bres_to_fres fns (inl vs) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EVar var) ⟩ -->* r.
  Proof.
    itr - fns r env var vs Hget Hres.
    sbn *.
    ivc - Hres.
    rwr - Hget.
    des - vs as [|v vs].
    1: app - get_value_singelton_length in Hget; smp - Hget; con.
    des - vs as [|v' vs].
    2: app - get_value_singelton_length in Hget; smp - Hget; con.
    admit. (* Skip: because refacor might change it anyway*)
  Admitted.



  Theorem eq_bs_to_fs_su1_funid :
    forall fns r env fid vs,
        get_value env (inr fid) = Some vs
    ->  bres_to_fres fns (inl vs) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EFunId fid) ⟩ -->* r.
  Proof.
    itr - fns r env fid vs Hget Hres.
    sbn *.
    ivc - Hres.
    rwr - Hget.
    des - vs as [|v vs].
    1: app - get_value_singelton_length in Hget; smp - Hget; con.
    des - vs as [|v' vs].
    2: app - get_value_singelton_length in Hget; smp - Hget; con.
    admit. (* Skip: because refacor might change it anyway*)
  Admitted.



  Theorem eq_bs_to_fs_su2_funid :
    forall fns r env fid id func varl_func body_func own_module modules,
        varl_func = varl func
    ->  body_func = body func
    ->  get_own_modfunc own_module fid.1 fid.2 (modules ++ stdlib) = Some func
    ->  get_value env (inr fid) = None
    ->  bres_to_fres fns (inl [VClos env [] id varl_func body_func None]) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EFunId fid) ⟩ -->* r.
  Proof.
    itr - fns r env fid id func varl_func body_func own_module modules
          Hvarl Hbody Hmod Hget Hres.
    sbn *.
    adm.
    (*
    clr - Hwfm.
    ivc - Hres.
    sbn.
    rwr - H.
    ufl - measure_env_exp.
    sbn.
    ufl - get_own_modfunc in H0.
    *)
  Admitted.



End Equivalence_Atoms2.









Section Equivalence_Doubles1.



  Theorem eq_bs_to_fs_suc_cons :
    forall fns r env e1 e2 v1 v2,
        (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inl [v2]) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e2 ⟩ -->* r)
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inl [v1]) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e1 ⟩ -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inl [VCons v1 v2]) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ECons e1 e2) ⟩ -->* r.
  Proof.
    (* +1 Inversion: clear?/rename?/inversion/simple *)
    itr - fns r env e1 e2 v1 v2 Hfs_v2 Hfs_v1 Hwfm Hres.
    ivc - Hres.
    sbn *.
    (* +2 Measure Reduction?: rewrite *)
    rwr - mred_e1e2_e1.
    rwr - mred_e1e2_e2.
    (* +3 Well Formed Map?: simpl?/apply/destruct *)
    des - Hwfm as [[Hwfm_v1 Hwfm_v2] _].
    app - fs_wfm_val_to_result in Hwfm_v1.
    app - fs_wfm_val_to_result in Hwfm_v2.
    (* +4 Remember?: remember/rewrite? *)
    rem - v1' v2' as Hv1' Hv2':
      (bval_to_fval fns v1)
      (bval_to_fval fns v2).
    (* +5 Specialize?: specialize/rewrite? *)
    spc - Hfs_v1: fns (RValSeq [v1']) Hwfm_v1.
    spc - Hfs_v2: fns (RValSeq [v2']) Hwfm_v2.
    rwl - Hv1' Hv2' in *.
    spe_rfl - Hfs_v1 Hfs_v2.
    (* +6 Destruct?: destruct *)
    des - Hfs_v1 as [kv1 [Hres_v1 Hstep_v1]].
    des - Hfs_v2 as [kv2 [Hres_v2 Hstep_v2]].
    (* +7 Scope: exists/split/tactic *)
    framestack_scope - v1' v2' Hres_v1 Hres_v2.
    (* +12 Step: clear/do_step/constructor?/trans?/exact? *)
    framestack_step - Hstep_v2 / kv2 Hv2' v2.
    framestack_step - Hstep_v1 / kv1 Hv1' v1.
    framestack_step.
  Qed.



  Theorem eq_bs_to_fs_ex1_cons :
    forall fns r env e1 e2 v2 exc,
        (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inl [v2]) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e2 ⟩ -->* r)
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inr exc) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e1 ⟩ -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inr exc) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ECons e1 e2) ⟩ -->* r.
  Proof.
  Admitted.



  Theorem eq_bs_to_fs_ex2_cons :
    forall fns r env e1 e2 exc,
        (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inr exc) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e2 ⟩ -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inr exc) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ECons e1 e2) ⟩ -->* r.
  Proof.
    (* +1 Inversion: clear?/rename?/inversion/simple *)
    itr - fns r env e1 e2 exc Hfs_exc Hwfm_exc Hres.
    ivc - Hres.
    sbn *.
    (* +2 Measure Reduction?: rewrite *)
    rwr - mred_e1e2_e1.
    rwr - mred_e1e2_e2.
    (* +3 Well Formed Map?: simpl?/apply/destruct *)
    ufl - bres_to_fres in Hwfm_exc.
    (* +4 Remember?: remember/rewrite? *)
    rem - exc' as Hexc':
      (bexc_to_fexc fns exc).
    (* +5 Specialize?: specialize/rewrite? *)
    spe - Hfs_exc: fns (RExc exc') Hwfm_exc.
    rwl - Hexc' in *.
    spe_rfl - Hfs_exc.
    (* +6 Destruct?: destruct *)
    des - Hfs_exc as [kexc [Hres_exc Hstep_exc]].
    (* +7 Scope: exists/split/tactic *)
    framestack_scope - Hres_exc.
    (* +12 Step: clear/do_step/constructor?/trans?/exact? *)
    framestack_step - Hstep_exc / kexc Hexc' exc.
    framestack_step.
  Admitted.



  Theorem eq_bs_to_fs_suc_seq :
    forall fns r env e1 e2 v1 v2,
        (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inl [v1]) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e1 ⟩ -->* r)
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns v2 = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e2 ⟩ -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns v2 = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ESeq e1 e2) ⟩ -->* r.
  Proof.
    (* +1 Inversion: clear?/rename?/inversion/simple *)
    itr - fns r env e1 e2 v1 v2 Hfs_v1 Hfs_v2 Hwfm_v2 Hres.
    ivc - Hres.
    sbn *.
    (* +2 Measure Reduction?: rewrite *)
    rwr - mred_e1e2_e1.
    rwr - mred_e1e2_e2.
    (* +3 Well Formed Map?: simpl?/apply/destruct *)
    assert (fs_wfm_val (bval_to_fval fns v1)) as Hwfm_v1
      by admit.
    app - fs_wfm_val_to_result in Hwfm_v1.
    (* +4 Remember?: remember/rewrite? *)
    rem - v1' v2' as Hv1' Hv2':
      (bval_to_fval fns v1)
      (bres_to_fres fns v2).
    (* +5 Specialize?: specialize/rewrite? *)
    spe - Hfs_v1: fns (RValSeq [v1']) Hwfm_v1.
    spe - Hfs_v2: fns v2' Hwfm_v2.
    rwl - Hv1' Hv2' in *.
    spe_rfl - Hfs_v1 Hfs_v2.
    (* +6 Destruct?: destruct *)
    des - Hfs_v1 as [kv1 [_ Hstep_v1]].
    des - Hfs_v2 as [kv2 [Hres_v2 Hstep_v2]].
    (* +7 Scope: exists/split/tactic *)
    framestack_scope - Hres_v2.
    (* +12 Step: clear/do_step/constructor?/trans?/exact? *)
    framestack_step - Hstep_v1 / kv1 Hv1' v1.
    framestack_step - Hstep_v2 / kv2 Hv2' v2.
    framestack_step.
  Admitted.



  Theorem eq_bs_to_fs_exc_seq :
    forall fns r env e1 e2 exc,
        (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inr exc) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e1 ⟩ -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inr exc) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ESeq e1 e2) ⟩ -->* r.
  Proof.
  Admitted.



End Equivalence_Doubles1.









Section Equivalence_Doubles2.



  Theorem eq_bs_to_fs_suc_let :
    forall fns r env e1 e2 v1 v2 vars,
        (Datatypes.length vars = Datatypes.length v1)
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inl v1) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e1 ⟩ -->* r)
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns v2 = r
        ->  ⟨ [], bexp_to_fexp_subst fns (append_vars_to_env vars v1 env) e2 ⟩
              -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns v2 = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ELet vars e1 e2) ⟩ -->* r.
  Proof.
    (* +1 Inversion: clear?/rename?/inversion/simple *)
    itr - fns r env e1 e2 v1 v2 vars Hlen Hfs_v1 Hfs_v2 Hwfm_v2 Hres.
    ivc - Hres.
    sbn *.
    (* +2 Measure Reduction?: rewrite *)
    rwr - mred_e1e2_e1.
    replace
      (subst_env (measure_exp e1 + measure_exp e2 + measure_env env)
        (rem_vars vars env) e2)
      with
      (subst_env (measure_exp e2 + measure_env (rem_vars vars env))
        (rem_vars vars env) e2)
      by admit.
    (* +3 Well Formed Map?: simpl?/apply/destruct *)
    assert (fs_wfm_valseq (bvs_to_fvs fns v1)) as Hwfm_v1
      by admit.
    app - fs_wfm_valseq_to_result in Hwfm_v1.
    (* +4 Remember?: remember/rewrite? *)
    rem - v1' v2' as Hv1' Hv2':
      (bvs_to_fvs fns v1)
      (bres_to_fres fns v2).
    (* +5 Specialize?: specialize/rewrite? *)
    spe - Hfs_v1: fns (RValSeq v1') Hwfm_v1.
    spe - Hfs_v2: fns v2' Hwfm_v2.
    rwl - Hv1' Hv2' in *.
    spe_rfl - Hfs_v1 Hfs_v2.
    (* +6 Destruct?: destruct *)
    des - Hfs_v1 as [kv1 [_ Hstep_v1]].
    des - Hfs_v2 as [kv2 [Hres_v2 Hstep_v2]].
    rwr - bexp_to_fexp_add_vars in Hstep_v2.
    rwl - Hv1' in Hstep_v2.
    ufl - bexp_to_fexp_subst measure_env_exp in *.
    (* +7 Scope: exists/split/tactic *)
    framestack_scope - Hres_v2.
    (* +12 Step: clear/do_step/constructor?/trans?/exact? *)
    framestack_step - Hstep_v1 / kv1.
    framestack_step.
    1: cwr - Hv1' Hlen; bse - bvs_to_fvs_length.
    framestack_step - Hstep_v2.
  Admitted.



  Theorem eq_bs_to_fs_exc_let :
    forall fns r env e1 e2 vars exc,
        (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inr exc) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e1 ⟩ -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inr exc) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ELet vars e1 e2) ⟩ -->* r.
  Proof.
  Admitted.



  Theorem eq_bs_to_fs_suc_try :
    forall fns r env e1 e2 e3 v1 v2 vars1 vars2,
        (Datatypes.length vars1 = Datatypes.length v1)
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inl v1) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e1 ⟩ -->* r)
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns v2 = r
        ->  ⟨ [], bexp_to_fexp_subst fns (append_vars_to_env vars1 v1 env) e2 ⟩
              -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns v2 = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ETry e1 vars1 e2 vars2 e3) ⟩ -->* r.
  Proof.
    (* +1 Inversion: clear?/rename?/inversion/simple *)
    itr - fns r env e1 e2 e3 v1 v2 vars1 vars2 Hlen Hfs_v1 Hfs_v2 Hwfm_v2 Hres.
    ivc - Hres.
    sbn *.
    (* +2 Measure Reduction?: rewrite *)
    replace
      (subst_env (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env env) env e1)
      with
      (subst_env (measure_exp e1 + measure_env env) env e1)
      by admit.
    replace
      (subst_env (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env env) (rem_vars vars1 env) e2)
      with
      (subst_env (measure_exp e2 + measure_env (rem_vars vars1 env))
        (rem_vars vars1 env) e2)
      by admit.
    (* +3 Well Formed Map?: simpl?/apply/destruct *)
    assert (fs_wfm_valseq (bvs_to_fvs fns v1)) as Hwfm_v1
      by admit.
    app - fs_wfm_valseq_to_result in Hwfm_v1.
    (* +4 Remember?: remember/rewrite? *)
    rem - v1' v2' as Hv1' Hv2':
      (bvs_to_fvs fns v1)
      (bres_to_fres fns v2).
    (* +5 Specialize?: specialize/rewrite? *)
    spe - Hfs_v1: fns (RValSeq v1') Hwfm_v1.
    spe - Hfs_v2: fns v2' Hwfm_v2.
    rwl - Hv1' Hv2' in *.
    spe_rfl - Hfs_v1 Hfs_v2.
    (* +6 Destruct?: destruct *)
    des - Hfs_v1 as [kv1 [_ Hstep_v1]].
    des - Hfs_v2 as [kv2 [Hres_v2 Hstep_v2]].
    rwr - bexp_to_fexp_add_vars in Hstep_v2.
    rwl - Hv1' in Hstep_v2.
    ufl - bexp_to_fexp_subst measure_env_exp in *.
    (* +7 Scope: exists/split/tactic *)
    framestack_scope - Hres_v2.
    (* +12 Step: clear/do_step/constructor?/trans?/exact? *)
    framestack_step - Hstep_v1 / kv1.
    framestack_step.
    1: cwr - Hv1' Hlen; ase - bvs_to_fvs_length.
    framestack_step - Hstep_v2.
  Admitted.



  Theorem eq_bs_to_fs_exc_try :
    forall fns r env e1 e2 e3 v3 vars1 vars2 exc,
        (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inr exc) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e1 ⟩ -->* r)
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns v3 = r
        ->  ⟨ [], bexp_to_fexp_subst fns (append_try_vars_to_env vars2
              [exclass_to_value exc.1.1; exc.1.2; exc.2] env) e3 ⟩
              -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns v3 = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ETry e1 vars1 e2 vars2 e3) ⟩ -->* r.
  Proof.
  Admitted.



End Equivalence_Doubles2.









Section Equivalence_Lists.



  Theorem eq_bs_to_fs_suc_tuple :
    forall fns r env el vl,
        (Datatypes.length el = Datatypes.length vl)
    ->  (forall i,
            i < Datatypes.length el
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i vl ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env (nth i el ErrorExp) ⟩
                  -->* r))
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inl [VTuple vl]) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ETuple el) ⟩ -->* r.
  Proof.
    itr - fns r env el vl Hlen Hfs Hwfm Hres.
    ivc - Hres.
    des - el as [|e el].
    * clr - Hfs Hwfm.
      smp - Hlen.
      sym - Hlen.
      app + length_zero_iff_nil as Hempty in Hlen.
      ivc - Hempty.
      smp; eei; spl.
      - scope_solver_triv.
      - framestack_step.
    * des - vl: smp *; con.
      ufl - bexp_to_fexp_subst measure_env_exp.
      smp.
      (* Measure Reduction *)
      rwr - mred_eel_e.
      rwr - mred_eel_el.
      (* WellForemd *)
      ass - as Hwfm_v: des - Hwfm as [[H _] _] >
        (fs_wfm_val (bval_to_fval fns v)).
      app - fs_wfm_val_to_result in Hwfm_v.
      (* Remember *)
      rem - v' vl' as Hv' Hvl':
        (bval_to_fval fns v)
        (map (bval_to_fval fns) vl).
      (* Pose *)
      pse - create_result_tuple as Hcreate: v' vl'.
      pse - list_biforall_tuple_nth as Hlist: fns env e el v vl v' vl'
                                              Hv' Hvl' Hlen Hwfm Hfs.
      clr - Hlen Hwfm.
      pose proof framestack_ident
        ITuple
        (map (bexp_to_fexp fns)
          (map (subst_env (measure_list measure_exp el + measure_env env) env)
            el))
        (RValSeq [Syntax.VTuple (v' :: vl')])
        vl' v' [] [] []
        Hcreate Hlist
        as Hfs_vl.
      clr - Hcreate Hlist.
      (*Specialzie*)
      ass - as Hl: sli >
        (0 < Datatypes.length (e :: el)).
      ass - as He: smp; rwr - Hv' >
        (bres_to_fres fns (inl [nth 0 (v :: vl) ErrorValue]) = RValSeq [v']).
      spc - Hfs as Hfs_v: 0 Hl fns (RValSeq [v']) Hwfm_v He.
      smp - Hfs_v.
      (*destruct*)
      des - Hfs_v as [kv [Hres_v Hstep_v]].
      des - Hfs_vl as [kvl Hstep_vl].
      (*Scope*)
      eei; spl.
      1: admit.
      (* Step *)
      framestack_step - Hstep_v / kv.
      framestack_step - Hstep_vl.
  Admitted.



End Equivalence_Lists.












Section Equivalence_Main.



  Theorem eq_bs_to_fs :
    forall env modules own_module id id' e e' eff eff',
        (eval_expr env modules own_module id e eff id' e' eff')
    ->  forall fns r,
          fs_wfm_result r
      ->  bres_to_fres fns e' = r
      ->  ⟨ [], (bexp_to_fexp_subst fns env e) ⟩ -->* r.
  Proof.
    (* #1 Intro: intro/induction *)
    itr - env modules own_module id id' e e' eff eff' bs.
    ind - bs; itr - fns r Hwfm Hres.
    (* #2 Atoms #1: (Nil, Lit) {SAME} *)
    3:  bse - eq_bs_to_fs_suc_nil:    fns r env
                                      Hres.
    3:  bse - eq_bs_to_fs_suc_lit:    fns r env l
                                      Hres.
    (* #3 Atoms #2: (Var, FunId) {MOSTLY} *)
    3:  bse - eq_bs_to_fs_suc_var:    fns r env s res
                                      H Hres.
    3:  bse - eq_bs_to_fs_su1_funid:  fns r env fid res
                                      H Hres.
    3:  bse - eq_bs_to_fs_su2_funid:  fns r env fid id func
                                      varl_func body_func own_module modules
                                      H1 H2 H0 H Hres.
    (* #4 Doubles #1: [e1;e2] (Cons, Seq) {SIMILIAR}*)
    5:  bse - eq_bs_to_fs_suc_cons:   fns r env hd tl hdv tlv
                                      IHbs1 IHbs2 Hwfm Hres.
    15: bse - eq_bs_to_fs_ex1_cons:   fns r env hd tl vtl ex
                                      IHbs1 IHbs2 Hwfm Hres.
    14: bse - eq_bs_to_fs_ex2_cons:   fns r env hd tl ex
                                      IHbs Hwfm Hres.
    11: bse - eq_bs_to_fs_suc_seq:    fns r env e1 e2 v1 v2
                                      IHbs1 IHbs2 Hwfm Hres.
    29: bse - eq_bs_to_fs_exc_seq:    fns r env e1 e2 ex
                                      IHbs Hwfm Hres.
    (* #5 Doubles #2: [e1;e2] (Let, Try) {SIMILIAR} *)
    10: bse - eq_bs_to_fs_suc_let:    fns r env e1 e2 vals res l
                                      H IHbs1 IHbs2 Hwfm Hres.
    27: bse - eq_bs_to_fs_exc_let:    fns r env e1 e2 vl ex
                                      IHbs Hwfm Hres.
    13: bse - eq_bs_to_fs_suc_try:    fns r env e1 e2 e3 vals res vl1 vl2
                                      H IHbs1 IHbs2 Hwfm Hres.
    13: bse - eq_bs_to_fs_exc_try:    fns r env e1 e2 e3 res vl1 vl2 ex
                                      IHbs1 IHbs2 Hwfm Hres.
    (* #6 Lists: [el] (Tuple) *)
    4: bse - eq_bs_to_fs_suc_tuple:   fns r env exps vals
                                      H H3 Hwfm Hres.
  Admitted.



End Equivalence_Main.







(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: OLD  /////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

(*

    (* Var *)
    * cbn in *.
      rewrite H.
      destruct
        (bvs_to_fvs f res)
        eqn:Hr.
      - inv H0.
        destruct res; cbn in *.
        + apply Environment.get_value_singelton_length in H. 
          cbn in H. 
          congruence.
        + destruct res; cbn in *.
          all: admit.
          (*
          ** rewrite measure_reduction with (n2 := measure_val v0).
             {
               apply bs_to_fs_val_reduction.
               admit.
               (*assumption.*)
             }
             {
               clear Hr f id v eff own_module modules.
               apply get_value_some_than_is_elem in H.
               apply In_split in H.
               destruct H as [env1].
               destruct H as [env2].
               rewrite H.
               remember
                 (λ '(_, y), measure_val y)
                 as _measure.
               pose proof map_app _measure env1 ((inl s, v0) :: env2).
               rewrite H0.
               clear H0.
               pose proof list_sum_app (map _measure env1) (map _measure ((inl s, v0) :: env2)).
               rewrite H0.
               clear H0.
               simpl.
               inv Heq_measure.
               slia.
             }
             slia.
          ** apply Environment.get_value_singelton_length in H.
             cbn in H.
             congruence.
             *)
      - admit. (* congruence. *)
    (* FunId *)
    * (* cbn in *.
      rewrite H.
      destruct
        (bs_to_fs_valseq f subst_env res) 
        eqn:Hr.
      - inv H0.
        destruct res; cbn in *.
        + apply Environment.get_value_singelton_length in H. 
          cbn in H.
          congruence.
        + destruct res; cbn in *.
          ** rewrite measure_reduction with (n2 := measure_val v0).
             {
               apply bs_to_fs_val_reduction.
               admit.
               (*assumption.*)
             }
             {
               clear Hr f id v eff own_module modules.
               apply get_value_some_than_is_elem in H.
               apply In_split in H.
               destruct H as [env1].
               destruct H as [env2].
               rewrite H.
               remember
                 (λ '(_, y), measure_val y)
                 as _measure.
               pose proof map_app _measure env1 ((inr fid, v0) :: env2).
               rewrite H0.
               clear H0.
               pose proof list_sum_app (map _measure env1) (map _measure ((inr fid, v0) :: env2)).
               rewrite H0.
               clear H0.
               simpl.
               inv Heq_measure.
               slia.
             }
             slia.
          ** apply Environment.get_value_singelton_length in H.
             cbn in H.
             congruence.
      - congruence. *)
      admit.
*)