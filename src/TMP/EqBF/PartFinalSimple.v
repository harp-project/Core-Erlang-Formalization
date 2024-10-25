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
    (* #1 Inversion Result: intro/inversion *)
    itr - fns r env Hresult.
    ivc - Hresult.
    (* #2 FrameStack Proof: scope/step *)
    framestack_scope.
    framestack_step.
  Qed.



  Theorem eq_bs_to_fs_suc_lit :
    forall fns r env l,
        bres_to_fres fns (inl [VLit l]) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ELit l) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion *)
    itr - fns r env l Hresult.
    ivc - Hresult.
    (* #2 FrameStack Proof: scope/step *)
    framestack_scope.
    framestack_step.
  Qed.



End Equivalence_Atoms1.









Section Equivalence_Atoms2.



  Theorem eq_bs_to_fs_suc_var :
    forall fns r env var vs,
        get_value env (inl var) = Some vs
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inl vs) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EVar var) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion *)
    itr - fns r env var vs Hget Hwfm Hresult.
    ivc - Hresult.
    (* #2 Rewrite Get: cbn/rewrite *)
    sbn.
    rwr - Hget.
    (* #3 Destruct Match: destruct/simple *)
    des - vs as [|v vs]:
      app - get_value_singelton_length in Hget; smp - Hget; con.
    des - vs as [|v0 vs]:
      app - get_value_singelton_length in Hget; smp - Hget; con.
    smp.
    (* #4 Measure Reduction: apply/destruct/assert/pose/rewrite *)
    app - get_value_in in Hget.
    app - In_split in Hget.
    des - Hget as [env1]; ren - Hget: H.
    des - Hget as [env2]; ren - Hget: H.
    ass > (measure_val v <= measure_env (env1 ++ (inl var, v) :: env2)) as Hle:
      triv_nle_solver.
    psc - mred_val_min as Hmred_v: v
      (measure_env (env1 ++ (inl var, v) :: env2)) Hle.
    cwr - Hget Hmred_v.
    (* #5 Well Formed Map: destruct/apply *)
    des - Hwfm as [Hwfm_v _].
    app - fs_wfm_val_to_forall in Hwfm_v.
    (* #6 Remember Values: remember *)
    rem - v' as Heq_v:
      (bval_to_fval fns v).
    (* #7 Pose Reduction: symmetry/pose *)
    sym - Heq_v.
    bse - bs_to_fs_equivalence_reduction: v fns v' Hwfm_v Heq_v.
  Qed.



  Theorem eq_bs_to_fs_su1_funid :
    forall fns r env fid vs,
        get_value env (inr fid) = Some vs
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inl vs) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EFunId fid) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion *)
    itr - fns r env var vs Hget Hwfm Hresult.
    ivc - Hresult.
    (* #2 Rewrite Get: cbn/rewrite *)
    sbn.
    rwr - Hget.
    (* #3 Destruct Match: destruct/simple *)
    des - vs as [|v vs]:
      app - get_value_singelton_length in Hget; smp - Hget; con.
    des - vs as [|v0 vs]:
      app - get_value_singelton_length in Hget; smp - Hget; con.
    smp.
    (* #4 Measure Reduction: apply/destruct/assert/pose/rewrite *)
    app - get_value_in in Hget.
    app - In_split in Hget.
    des - Hget as [env1]; ren - Hget: H.
    des - Hget as [env2]; ren - Hget: H.
    ass > (measure_val v <= measure_env (env1 ++ (inr var, v) :: env2)) as Hle:
      triv_nle_solver.
    psc - mred_val_min as Hmred_v: v
      (measure_env (env1 ++ (inr var, v) :: env2)) Hle.
    cwr - Hget Hmred_v.
    (* #5 Well Formed Map: destruct/apply *)
    des - Hwfm as [Hwfm_v _].
    app - fs_wfm_val_to_forall in Hwfm_v.
    (* #6 Remember Values: remember *)
    rem - v' as Heq_v:
      (bval_to_fval fns v).
    (* #7 Pose Reduction: symmetry/pose *)
    sym - Heq_v.
    bse - bs_to_fs_equivalence_reduction: v fns v' Hwfm_v Heq_v.
  Qed.



  Theorem eq_bs_to_fs_su2_funid :
    forall fns r env fid id func varl_func body_func own_module modules,
        varl_func = varl func
    ->  body_func = body func
    ->  get_own_modfunc own_module fid.1 fid.2 (modules ++ stdlib) = Some func
    ->  get_value env (inr fid) = None
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inl [VClos env [] id varl_func body_func None]) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EFunId fid) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion *)
    itr - fns r env fid id func varl_func body_func own_module modules
          Hvarl Hbody Hmod Hget Hwfm Hresult.
    ivc - Hresult.
    (* #2 Rewrite Get: cbn/rewrite *)
    sbn.
    (* cwr - Hget *) (* its do same, but somehow doesnt work ??? *)
    (* #3 Destruct Match: destruct/simple *)
    cma : adm.
    clr - H.
    (*fid*)
    clr - Hget Hwfm.
    des - fid.
    smp *.
    (* FrameStack *)
    eei; spl.
    1: adm.
    framestack_step.
    {
      sbn.
      adm.
      (* 0 > fns (inr fid) : this probably false ? *)
    }
    (*
    clr - Hwfm.
    ivc - Hresult.
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
    forall fns r env e1 e2 v2 v1,
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
    (* #1 Inversion Result: intro/inversion *)
    itr - fns r env e1 e2 v2 v1 Hfs_v2 Hfs_v1 Hwfm Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn *.
    rwr - mred_e1e2_e2
          mred_e1e2_e1.
    (* #3 Well Formed Map: destruct/apply *)
    des - Hwfm as [[Hwfm_v1 Hwfm_v2] _].
    app - fs_wfm_val_to_result in Hwfm_v2.
    app - fs_wfm_val_to_result in Hwfm_v1.
    (* #4 Remember Values: Remember Values *)
    rem - v2' v1' as Heq_v2 Heq_v1:
      (bval_to_fval fns v2)
      (bval_to_fval fns v1).
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite *)
    spc - Hfs_v2: fns (RValSeq [v2']) Hwfm_v2.
    spc - Hfs_v1: fns (RValSeq [v1']) Hwfm_v1.
    rwl - Heq_v2 Heq_v1 in *.
    spe_rfl - Hfs_v2 Hfs_v1.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v2 as [kv2 [Hscope_v2 Hstep_v2]].
    des - Hfs_v1 as [kv1 [Hscope_v1 Hstep_v1]].
    (* #7 FrameStack Proof: scope/step *)
    framestack_scope - v1' v2' Hscope_v1 Hscope_v2.
    framestack_step - Hstep_v2 / kv2 Heq_v2 v2 e2.
    framestack_step - Hstep_v1 / kv1 Heq_v1 v1 e1 env fns.
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
    (* #1 Inversion Result: intro/inversion *)
    itr - fns r env e1 e2 v2 exc Hfs_v2 Hfs_exc Hwfm_exc Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn *.
    rwr - mred_e1e2_e2
          mred_e1e2_e1.
    (* #3 Well Formed Map: assert/apply/unfold *)
    ass > (fs_wfm_val (bval_to_fval fns v2)) as Hwfm_v2: adm.
    app - fs_wfm_val_to_result in Hwfm_v2.
    ufl - bres_to_fres in Hwfm_exc.
    (* #4 Remember Values: Remember Values *)
    rem - v2' exc' as Heq_v2 Heq_exc:
      (bval_to_fval fns v2)
      (bexc_to_fexc fns exc).
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite *)
    spc - Hfs_v2: fns (RValSeq [v2']) Hwfm_v2.
    spc - Hfs_exc: fns (RExc exc') Hwfm_exc.
    rwl - Heq_v2 Heq_exc in *.
    spe_rfl - Hfs_v2 Hfs_exc.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v2 as [kv2 [_ Hstep_v2]].
    des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
    (* #7 FrameStack Proof: scope/step *)
    framestack_scope - Hscope_exc.
    framestack_step - Hstep_v2 / kv2 Heq_v2 v2 e2.
    framestack_step - Hstep_exc / kexc Heq_exc exc e1 env fns.
    framestack_step.
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
    (* #1 Inversion Result: intro/inversion *)
    itr - fns r env e1 e2 exc Hfs_exc Hwfm_exc Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn *.
    rwr - mred_e1e2_e2
          mred_e1e2_e1.
    (* #3 Well Formed Map: unfold *)
    ufl - bres_to_fres in Hwfm_exc.
    (* #4 Remember Values: Remember Values *)
    rem - exc' as Heq_exc:
      (bexc_to_fexc fns exc).
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite *)
    spc - Hfs_exc: fns (RExc exc') Hwfm_exc.
    rwl - Heq_exc in *.
    spe_rfl - Hfs_exc.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
    (* #7 FrameStack Proof: scope/step *)
    framestack_scope - Hscope_exc.
    framestack_step - Hstep_exc / kexc Heq_exc exc e2.
    framestack_step.
  Qed.



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
    (* #1 Inversion Result: intro/inversion *)
    itr - fns r env e1 e2 v1 v2 Hfs_v1 Hfs_v2 Hwfm_v2 Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn *.
    rwr - mred_e1e2_e1
          mred_e1e2_e2.
    (* #3 Well Formed Map: assert/apply *)
    ass > (fs_wfm_val (bval_to_fval fns v1)) as Hwfm_v1: adm.
    app - fs_wfm_val_to_result in Hwfm_v1.
    (* #4 Remember Values: Remember Values *)
    rem - v1' v2' as Heq_v1 Heq_v2:
      (bval_to_fval fns v1)
      (bres_to_fres fns v2).
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite *)
    spc - Hfs_v1: fns (RValSeq [v1']) Hwfm_v1.
    spc - Hfs_v2: fns v2' Hwfm_v2.
    rwl - Heq_v1 Heq_v2 in *.
    spe_rfl - Hfs_v1 Hfs_v2.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v1 as [kv1 [_ Hstep_v1]].
    des - Hfs_v2 as [kv2 [Hscope_v2 Hstep_v2]].
    (* #7 FrameStack Proof: scope/step *)
    framestack_scope - Hscope_v2.
    framestack_step - Hstep_v1 / kv1 Heq_v1 v1 e1.
    framestack_step - Hstep_v2 / kv2 Heq_v2 v2 e2 env fns v1'.
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
    (* #1 Inversion Result: intro/inversion *)
    itr - fns r env e1 e2 exc Hfs_exc Hwfm_exc Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn *.
    rwr - mred_e1e2_e1
          mred_e1e2_e2.
    (* #3 Well Formed Map: unfold *)
    ufl - bres_to_fres in Hwfm_exc.
    (* #4 Remember Values: Remember Values *)
    rem - exc' as Heq_exc:
      (bexc_to_fexc fns exc).
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite *)
    spc - Hfs_exc: fns (RExc exc') Hwfm_exc.
    rwl - Heq_exc in *.
    spe_rfl - Hfs_exc.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
    (* #7 FrameStack Proof: scope/step *)
    framestack_scope - Hscope_exc.
    framestack_step - Hstep_exc / kexc Heq_exc exc e1.
    framestack_step.
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
    (* #1 Inversion Result: intro/inversion *)
    itr - fns r env e1 e2 v1 v2 vars Hlen Hfs_v1 Hfs_v2 Hwfm_v2 Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn *.
    rwr - mred_e1e2_e1
          mred_e1e2_e2_vars.
    (* #3 Well Formed Map: assert/apply *)
    ass > (fs_wfm_valseq (bvs_to_fvs fns v1)) as Hwfm_v1: adm.
    app - fs_wfm_valseq_to_result in Hwfm_v1.
    (* +4 Remember Values: remember *)
    rem - v1' v2' as Heq_v1 Heq_v2:
      (bvs_to_fvs fns v1)
      (bres_to_fres fns v2).
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite *)
    spc - Hfs_v1: fns (RValSeq v1') Hwfm_v1.
    spc - Hfs_v2: fns v2' Hwfm_v2.
    rwl - Heq_v1 Heq_v2 in *.
    spe_rfl - Hfs_v1 Hfs_v2.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v1 as [kv1 [_ Hstep_v1]].
    des - Hfs_v2 as [kv2 [Hscope_v2 Hstep_v2]].
    (* #7 Rewrite Add Vars: rewrite/unfold *)
    rwr - bexp_to_fexp_add_vars in Hstep_v2.
    rwl - Heq_v1 in Hstep_v2.
    ufl - bexp_to_fexp_subst measure_env_exp in *.
    (* #8 FrameStack Proof: scope/step *)
    framestack_scope - Hscope_v2.
    framestack_step - Hstep_v1 / kv1 e1.
    framestack_step: rwr - Heq_v1 Hlen; bse - bvs_to_fvs_length
      / Hlen Heq_v1 v1.
    framestack_step - Hstep_v2.
  Admitted.



  Theorem eq_bs_to_fs_exc_let :
    forall fns r env e1 e2 exc vars,
        (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inr exc) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e1 ⟩ -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inr exc) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ELet vars e1 e2) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion *)
    itr - fns r env e1 e2 exc vars Hfs_exc Hwfm_exc Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn *.
    rwr - mred_e1e2_e1
          mred_e1e2_e2_vars.
    (* #3 Well Formed Map: unfold *)
    ufl - bres_to_fres in Hwfm_exc.
    (* #4 Remember Values: Remember Values *)
    rem - exc' as Heq_exc:
      (bexc_to_fexc fns exc).
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite *)
    spc - Hfs_exc: fns (RExc exc') Hwfm_exc.
    rwl - Heq_exc in *.
    spe_rfl - Hfs_exc.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
    (* #7 FrameStack Proof: scope/step *)
    framestack_scope - Hscope_exc.
    framestack_step - Hstep_exc / kexc Heq_exc exc e1.
    framestack_step.
  Qed.



  (* Difference from Let: measure_reduction/ framestack tactic: auto - by *)
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
    (* #1 Inversion Result: intro/inversion *)
    itr - fns r env e1 e2 e3 v1 v2 vars1 vars2 Hlen Hfs_v1 Hfs_v2 Hwfm_v2
          Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn *.
    rwr - mred_e1e2e3_e1
          mred_e1e2e3_e2_vars
          mred_e1e2e3_e3_vars.
    (* #3 Well Formed Map: assert/apply *)
    ass > (fs_wfm_valseq (bvs_to_fvs fns v1)) as Hwfm_v1: adm.
    app - fs_wfm_valseq_to_result in Hwfm_v1.
    (* +4 Remember Values: remember *)
    rem - v1' v2' as Heq_v1 Heq_v2:
      (bvs_to_fvs fns v1)
      (bres_to_fres fns v2).
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite *)
    spc - Hfs_v1: fns (RValSeq v1') Hwfm_v1.
    spc - Hfs_v2: fns v2' Hwfm_v2.
    rwl - Heq_v1 Heq_v2 in *.
    spe_rfl - Hfs_v1 Hfs_v2.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v1 as [kv1 [_ Hstep_v1]].
    des - Hfs_v2 as [kv2 [Hscope_v2 Hstep_v2]].
    (* #7 Rewrite Add Vars: rewrite/unfold *)
    rwr - bexp_to_fexp_add_vars in Hstep_v2.
    rwl - Heq_v1 in Hstep_v2.
    ufl - bexp_to_fexp_subst measure_env_exp in *.
    (* #8 FrameStack Proof: scope/step *)
    framestack_scope - Hscope_v2.
    framestack_step - Hstep_v1 / kv1 e1.
    framestack_step: rwr - Heq_v1 Hlen; ase - bvs_to_fvs_length
      / Hlen Heq_v1 v1.
    framestack_step - Hstep_v2.
  Admitted.

(*
IHbs1 : ∀ (fns : name_sub) (r : Redex),
          fs_wfm_result r
          → bres_to_fres fns (inr ex) = r → ⟨ [], bexp_to_fexp_subst fns env e1 ⟩ -->* r
IHbs2 : ∀ (fns : name_sub) (r : Redex),
          fs_wfm_result r
          → bres_to_fres fns res = r
            → ⟨ [],
              bexp_to_fexp_subst fns
                (append_try_vars_to_env vl2 [exclass_to_value ex.1.1; ex.1.2; ex.2] env) e3
              ⟩ -->* r
*)

  Theorem eq_bs_to_fs_exc_try :
    forall fns r env e1 e2 e3 exc v3 vars1 vars2,
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
    (* #1 Inversion Result: intro/inversion *)
    itr - fns r env e1 e2 e3 exc v3 vars1 vars2 Hfs_exc Hfs_v3 Hwfm_v3 Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn *.
    rwr - mred_e1e2e3_e1
          mred_e1e2e3_e2_vars
          mred_e1e2e3_e3_vars.
    (* #3 Well Formed Map: assert/apply *)
    ass > (fs_wfm_exception (bexc_to_fexc fns exc)) as Hwfm_exc: adm.
    app - fs_wfm_exception_to_result in Hwfm_exc.
    (* +4 Remember Values: remember *)
    rem - exc' v3' as Heq_exc Heq_v3:
      (bexc_to_fexc fns exc)
      (bres_to_fres fns v3).
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite *)
    spc - Hfs_exc: fns exc' Hwfm_exc.
    spc - Hfs_v3: fns v3' Hwfm_v3.
    rwl - Heq_exc Heq_v3 in *.
    spe_rfl - Hfs_exc Hfs_v3.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_exc as [kexc [_ Hstep_exc]].
    des - Hfs_v3 as [kv3 [Hscope_v3 Hstep_v3]].
    (* #7 Destruct Vars Length: destruct *)
    des > (Datatypes.length vars2 =? 2) as Hlen_vars2.
    * (* #8.1 Rewrite Add Vars: rewrite/unfold *)
      rwr - bexp_to_fexp_add_vars in Hstep_v3.
      ufl - bexp_to_fexp_subst measure_env_exp in *.
      (* #9.1 FrameStack Proof: scope/step *)
      framestack_scope - Hscope_v3.
      framestack_step.
      framestack_step - Hstep_exc / kexc e1.
      framestack_step.
      smp. (* false = true *)
      adm.
      adm.
    * (* #8.2 Rewrite Add Vars: rewrite/unfold *)
      rwr - bexp_to_fexp_add_vars in Hstep_v3.
      ufl - bexp_to_fexp_subst measure_env_exp in *.
      (* #9.2 FrameStack Proof: scope/step *)
      framestack_scope - Hscope_v3.
      framestack_step.
      framestack_step - Hstep_exc / kexc e1.
      framestack_step.
      smp. (* false = true *)
      adm.
      adm.
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
    (* #1 Inversion Result: intro/inversion *)
    itr - fns r env el vl Hlen Hfs Hwfm Hresult.
    ivc - Hresult.
    (* #2 Destruct Expression List: destruct *)
    des - el as [|e el].
    * (* #3.1 Fix Result: clear/simple/symmetry/apply/inversion *)
      clr - Hfs Hwfm.
      smp - Hlen.
      sym - Hlen.
      app + length_zero_iff_nil as Hempty in Hlen.
      ivc - Hempty.
      (* #4.1 FrameStack Proof: scope/step *)
      framestack_scope.
      framestack_step.
    * (* #3.2 Fix Result: destruct + smp/congruence *)
      des - vl: smp *; con.
      (* #4.2 Measure Reduction: unfold/simpl/rewrite *)
      ufl - bexp_to_fexp_subst measure_env_exp.
      smp.
      rwr - mred_eel_e
            mred_eel_el.
      (* #5.2 Well Formed Map: assert/apply *)
      ass - as Hwfm_v: des - Hwfm as [[H _] _] >
        (fs_wfm_val (bval_to_fval fns v)).
      app - fs_wfm_val_to_result in Hwfm_v.
      (* #6.2 Remember Values: remember *)
      rem - v' vl' as Hv' Heq_vl:
        (bval_to_fval fns v)
        (map (bval_to_fval fns) vl).
      (* #7.2 Pose Ident Theorem: pose + clear *)
      pse - create_result_tuple as Hcreate: v' vl'.
      pse - list_biforall_tuple_nth as Hlist:
        fns env e el v vl v' vl'
        Hv' Heq_vl Hlen Hwfm Hfs;
        clr - Hlen Hwfm.
      pose proof framestack_ident
        ITuple
        (map (bexp_to_fexp fns)
          (map (subst_env (measure_list measure_exp el + measure_env env) env)
            el))
        (RValSeq [Syntax.VTuple (v' :: vl')])
        vl' v' [] [] []
        Hcreate Hlist
        as Hfs_vl;
        clr - Hcreate Hlist.
      (* #8.2 Specialize Inductive Hypothesis: assert/specialize/simpl *)
      ass - as Hl: sli >
        (0 < Datatypes.length (e :: el)).
      ass - as He: smp; rwr - Hv' >
        (bres_to_fres fns (inl [nth 0 (v :: vl) ErrorValue]) = RValSeq [v']).
      spc - Hfs as Hfs_v: 0 Hl fns (RValSeq [v']) Hwfm_v He.
      smp - Hfs_v.
      (* #9.2 Destruct Inductive Hypothesis: destruct *)
      des - Hfs_v as [kv [Hscope_v Hstep_v]].
      des - Hfs_vl as [kvl Hstep_vl].
      (* #10.2 FrameStack Proof: scope/step *)
      eei; spl.
      1: admit. (*Needs to modify main proof, it need is_result r predicate *)
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
    (* #1 Inversion Result: intro/induction *)
    itr - env modules own_module id id' e e' eff eff' bs.
    ind - bs; itr - fns r Hwfm Hresult.
    (* #2 Atoms #1: (Nil, Lit) {SAME} *)
    3:  bse - eq_bs_to_fs_suc_nil:    fns r env
                                      Hresult.
    3:  bse - eq_bs_to_fs_suc_lit:    fns r env l
                                      Hresult.
    (* #3 Atoms #2: (Var, FunId) {MOSTLY} *)
    3:  bse - eq_bs_to_fs_suc_var:    fns r env s res
                                      H Hwfm Hresult.
    3:  bse - eq_bs_to_fs_su1_funid:  fns r env fid res
                                      H Hwfm Hresult.
    3:  bse - eq_bs_to_fs_su2_funid:  fns r env fid id func
                                      varl_func body_func own_module modules
                                      H1 H2 H0 H Hwfm Hresult.
    (* #4 Doubles #1: [e1;e2] (Cons, Seq) {SIMILIAR}*)
    5:  bse - eq_bs_to_fs_suc_cons:   fns r env hd tl tlv hdv
                                      IHbs1 IHbs2 Hwfm Hresult.
    15: bse - eq_bs_to_fs_ex1_cons:   fns r env hd tl vtl ex
                                      IHbs1 IHbs2 Hwfm Hresult.
    14: bse - eq_bs_to_fs_ex2_cons:   fns r env hd tl ex
                                      IHbs Hwfm Hresult.
    11: bse - eq_bs_to_fs_suc_seq:    fns r env e1 e2 v1 v2
                                      IHbs1 IHbs2 Hwfm Hresult.
    29: bse - eq_bs_to_fs_exc_seq:    fns r env e1 e2 ex
                                      IHbs Hwfm Hresult.
    (* #5 Doubles #2: [e1;e2] (Let, Try) {SIMILIAR} *)
    10: bse - eq_bs_to_fs_suc_let:    fns r env e1 e2 vals res l
                                      H IHbs1 IHbs2 Hwfm Hresult.
    27: bse - eq_bs_to_fs_exc_let:    fns r env e1 e2 ex vl
                                      IHbs Hwfm Hresult.
    13: bse - eq_bs_to_fs_suc_try:    fns r env e1 e2 e3 vals res vl1 vl2
                                      H IHbs1 IHbs2 Hwfm Hresult.
    13: bse - eq_bs_to_fs_exc_try:    fns r env e1 e2 e3 ex res vl1 vl2
                                      IHbs1 IHbs2 Hwfm Hresult.
    (* #6 Lists: [el] (Tuple) *)
    4: bse - eq_bs_to_fs_suc_tuple:   fns r env exps vals
                                      H H3 Hwfm Hresult.
  Admitted.



End Equivalence_Main.