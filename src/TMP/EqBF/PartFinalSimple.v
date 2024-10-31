From CoreErlang.TMP.EqBF Require Export Part3Simple.

Import BigStep.










  Theorem list_biforall_vtuple_nth2 :
    forall fns env e el el' v vl v' vl',
        v' = bval_to_fval fns v
    ->  vl' = map (bval_to_fval fns) vl
    ->  Datatypes.length (e :: el) = Datatypes.length (v :: vl)
    ->  fs_wfm_result (bres_to_fres fns (inl [VTuple (v :: vl)]))
    ->  (forall i,
            i < Datatypes.length (e :: el)
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i (v :: vl) ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env (nth i (e :: el ++ el') ErrorExp) ⟩
                  -->* r))
    ->  list_biforall
          (fun e v => ⟨ [], RExp e ⟩ -->* RValSeq [v])
          (map
            (bexp_to_fexp fns)
            (map
              (subst_env (measure_list measure_exp el + measure_env env) env) 
              el))
          vl'.
  Proof.
    (* #1 Intro: intro/subst/generalize *)
    itr - fns env e0 el el' v0 vl v' vl' Hv' Hvl' Hlen Hwfm Hfs.
    sbt.
    gen - vl.
    (* #2 Induction: induction + destruct/simpl/congruence/constructor*)
    ind - el as [| e1 el IHel] :> itr; des - vl as [| v1 vl]; smp + Hlen
        :- con + cns.
    cns.
    * (* #3.1 Measure Reduction: rewrite *)
      rwr - mred_eel_e.
      (* #4.1 Prepare for Specialize: simpl/destruct/apply/assert *)
      smp - Hwfm.
      des - Hwfm as [[_ [Hwfm_v1 _]] _].
      app - fs_wfm_val_to_result in Hwfm_v1.
      ass > (1 < Datatypes.length (e0 :: e1 :: el)) as Hl: sli.
      (* #5.1 Specialize: specialize *)
      spc - Hfs: 1 Hl fns (RValSeq [bval_to_fval fns v1]) Hwfm_v1.
      spe_rfl - Hfs.
      (* #6.1 Prove by Hypothesis: simpl/assumption *)
      smp - Hfs.
      asm.
    * (* #3.2 Measure Reduction: rewrite *)
      rwr - mred_eel_el.
      (* #4.2 Apply Indutive Hypothesis: apply + simpl/inversion/subst/tauto *)
      app - IHel: smp; ivs - Hlen | smp + Hwfm; tau.
      (* #5.2 Destruct: clear/destruct/intro/inversion *)
      clr - IHel Hwfm fns.
      des - i; itr - Hl' fns r Hwfm Hres; ivc - Hres.
      - (* #6.2.1 Prepare for Specialize: clear/simpl/destruct/apply/assert *)
        clr - Hl'.
        smp - Hwfm.
        des - Hwfm as [Hwfm_v0 _].
        app - fs_wfm_val_to_result in Hwfm_v0.
        ass > (0 < Datatypes.length (e0 :: e1 :: el)) as Hl: sli.
        (* #7.2.1 Specialize: specialize *)
        spc - Hfs: 0 Hl fns (RValSeq [bval_to_fval fns v0]) Hwfm_v0.
        spe_rfl - Hfs.
        (* #8.2.1 Prove by Hypothesis: simpl/assumption *)
        smp + Hfs.
        asm.
      - (* #6.2.2 Prepare for Specialize: clear/simpl/destruct/apply/assert *)
        smp - Hl' Hwfm.
        ass > (S (S i) < Datatypes.length (e0 :: e1 :: el)) as Hl: sli.
        clr - Hl'.
        (* #7.2.2 Specialize: specialize *)
        spc - Hfs: (S (S i)) Hl fns
          (bres_to_fres fns (inl [nth (S (S i)) (v0 :: v1 :: vl) ErrorValue])).
        smp - Hfs.
        spc - Hfs: Hwfm.
        spe_rfl - Hfs.
        (* #8.2.2 Prove by Hypothesis: simpl/assumption *)
        smp + Hfs.
        asm.
  Qed.


  (* For tuple exception *)
  Theorem framestack_ident_partial :
    forall ident el e' el' vl v' vl' Fs,
        list_biforall
          (fun e v => ⟨ [] , RExp e ⟩ -->* RValSeq [v])
          el
          vl
    ->  exists k,
          ⟨ FParams ident vl' (el ++ e' :: el') :: Fs, RValSeq [v'] ⟩ -[ k ]->
          ⟨ FParams ident (vl' ++ v' :: vl) el' :: Fs, RExp e' ⟩.
  Proof.
    (* #1 Induction: intro/generalize/revert/induction *)
    itr - ident el.
    ind - el as [| e el Hfs_vl];
      itr - e' el' vl v' vl' Fs Hbiforall; ivc - Hbiforall.
    * (* #2.1 Constructor: exists/constructor *)
      eei.
      do 2 ens.
    * (* #2.2 Specialize: rename/assert/rewrite/specialize *)
      ren - v vl Hfs_v Hbiforall: hd' tl' H1 H3.
      ass > ((vl' ++ v' :: v :: vl) = ((vl' ++ [v']) ++ v :: vl))
        as Hrewrite: rwl - app_assoc; by rewrite <- app_cons_swap.
      spc - Hfs_vl: e' el' vl v (vl' ++ [v']) Fs Hbiforall.
      cwl - Hrewrite in Hfs_vl.
      (* #3.2 Destruct: destruct *)
      des - Hfs_v as [kv [_ Hstep_v]].
      des - Hfs_vl as [kvl Hstep_vl].
      (* #4.2 Constructor: exists/constructor *)
      eei.
      (* #5.2 Do Step: fs_transitive/exact *)
      framestack_step - Hstep_v / kv.
      framestack_step - Hstep_vl.
  Qed.


  Lemma split_list :
    forall fns env el el',
      map
        (bexp_to_fexp fns)
        (map
          (subst_env
            (measure_list measure_exp (el ++ el') + measure_env env)
            env)
          (el ++ el'))
    = map
        (bexp_to_fexp fns)
        (map
          (subst_env
            (measure_list measure_exp el + measure_env env)
            env)
          el) ++
      map
        (bexp_to_fexp fns)
        (map
          (subst_env
            (measure_list measure_exp el' + measure_env env)
            env)
          el').
  Proof.
    (* #1 Intro: intro *)
    itr.
    (* #2 Rewrite Applicative: rewrite *)
    do 2 rwr - map_app.
    (* #3 Measure Reduction: rewrite/triv_nle_solver *)
    rwr - mred_exp_list_min.
    rewrite mred_exp_list_min with (el := el').
    2-3: triv_nle_solver.
    (* #4 Prove by Unfold: unfold *)
    by unfold measure_list.
  Qed.

(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: EQUIVALENCE  /////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)









Section Equivalence_Help.



  Theorem list_biforall_vtuple_nth_le :
    forall fns env e el el' v vl v' vl',
        v' = bval_to_fval fns v
    ->  vl' = map (bval_to_fval fns) vl
    ->  Datatypes.length (e :: el) = Datatypes.length (v :: vl)
    ->  fs_wfm_result (bres_to_fres fns (inl [VTuple (v :: vl)]))
    ->  (forall i,
            i < Datatypes.length (e :: el)
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i (v :: vl) ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env
                    (nth i (e :: el ++ el') ErrorExp) ⟩
                  -->* r))
    ->  list_biforall
          (fun e v => ⟨ [], RExp e ⟩ -->* RValSeq [v])
          (map
            (bexp_to_fexp fns)
            (map
              (subst_env (measure_list measure_exp el + measure_env env) env) 
              el))
          vl'.
  Proof.
    (* #1 Intro: intro/subst/generalize *)
    itr - fns env e0 el el' v0 vl v' vl' Hv' Hvl' Hlen Hwfm Hfs.
    sbt.
    gen - vl.
    (* #2 Induction: induction + destruct/simpl/congruence/constructor*)
    ind - el as [| e1 el IHel] :> itr; des - vl as [| v1 vl]; smp + Hlen
        :- con + cns.
    cns.
    * (* #3.1 Measure Reduction: rewrite *)
      rwr - mred_eel_e.
      (* #4.1 Prepare for Specialize: simpl/destruct/apply/assert *)
      smp - Hwfm.
      des - Hwfm as [[_ [Hwfm_v1 _]] _].
      app - fs_wfm_val_to_result in Hwfm_v1.
      ass > (1 < Datatypes.length (e0 :: e1 :: el)) as Hl: sli.
      (* #5.1 Specialize: specialize *)
      spc - Hfs: 1 Hl fns (RValSeq [bval_to_fval fns v1]) Hwfm_v1.
      spe_rfl - Hfs.
      (* #6.1 Prove by Hypothesis: simpl/assumption *)
      smp - Hfs.
      asm.
    * (* #3.2 Measure Reduction: rewrite *)
      rwr - mred_eel_el.
      (* #4.2 Apply Indutive Hypothesis: apply + simpl/inversion/subst/tauto *)
      app - IHel: smp; ivs - Hlen | smp + Hwfm; tau.
      (* #5.2 Destruct: clear/destruct/intro/inversion *)
      clr - IHel Hwfm fns.
      des - i; itr - Hl' fns r Hwfm Hres; ivc - Hres.
      - (* #6.2.1 Prepare for Specialize: clear/simpl/destruct/apply/assert *)
        clr - Hl'.
        smp - Hwfm.
        des - Hwfm as [Hwfm_v0 _].
        app - fs_wfm_val_to_result in Hwfm_v0.
        ass > (0 < Datatypes.length (e0 :: e1 :: el)) as Hl: sli.
        (* #7.2.1 Specialize: specialize *)
        spc - Hfs: 0 Hl fns (RValSeq [bval_to_fval fns v0]) Hwfm_v0.
        spe_rfl - Hfs.
        (* #8.2.1 Prove by Hypothesis: simpl/assumption *)
        smp + Hfs.
        asm.
      - (* #6.2.2 Prepare for Specialize: clear/simpl/destruct/apply/assert *)
        smp - Hl' Hwfm.
        ass > (S (S i) < Datatypes.length (e0 :: e1 :: el)) as Hl: sli.
        clr - Hl'.
        (* #7.2.2 Specialize: specialize *)
        spc - Hfs: (S (S i)) Hl fns
          (bres_to_fres fns (inl [nth (S (S i)) (v0 :: v1 :: vl) ErrorValue])).
        smp - Hfs.
        spc - Hfs: Hwfm.
        spe_rfl - Hfs.
        (* #8.2.2 Prove by Hypothesis: simpl/assumption *)
        smp + Hfs.
        asm.
  Qed.



  Theorem list_biforall_vtuple_nth_eq :
    forall fns env e el v vl v' vl',
        v' = bval_to_fval fns v
    ->  vl' = map (bval_to_fval fns) vl
    ->  Datatypes.length (e :: el) = Datatypes.length (v :: vl)
    ->  fs_wfm_result (bres_to_fres fns (inl [VTuple (v :: vl)]))
    ->  (forall i,
            i < Datatypes.length (e :: el)
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i (v :: vl) ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env (nth i (e :: el) ErrorExp) ⟩
                  -->* r))
    ->  list_biforall
          (fun e v => ⟨ [], RExp e ⟩ -->* RValSeq [v])
          (map
            (bexp_to_fexp fns)
            (map
              (subst_env (measure_list measure_exp el + measure_env env) env) 
              el))
          vl'.
  Proof.
    (* #1 Intro: intro/subst/generalize *)
    itr - fns env e el v vl v' vl' Heq_v Heq_vl Hlength Hwfm Hfs_nth.
    (* #2 Rewrite Add Nil: remember/assert/rewrite + rewrite *)
    rem - length_el as Hlength_el: (Datatypes.length (e :: el)).
    ass > (e :: el = e :: el ++ []) as Heq_el: rwr - app_nil_r.
    cwr - Heq_el in Hfs_nth.
    cwr - Hlength_el in *.
    (* #3 Pose by Previus Theorem: pose *)
    by pose proof list_biforall_vtuple_nth_le
      fns env e el [] v vl v' vl'
      Heq_v Heq_vl Hlength Hwfm Hfs_nth.
  Qed.



End Equivalence_Help.









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
    setoid_rewrite Hget.
    (* #3 Destruct Fid: cleardestruct/simpl *)
    clr - Hget Hwfm.
    des - fid.
    smp *.
    (* #4 FrameStack Proof: exists/split/step *)
    eei; spl.
    1: adm.
    framestack_step.
    {
      sbn.
      adm. (* 0 > fns (inr fid) : this probably false ? *)
    }
    (* Main Proof: extra modulo predicate *)
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
  Qed.



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
    (* #4 Remember Values: remember *)
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
    (* TMP FIX: *)
    (* #7 Assert Vars Length: assert/rewrite/simple *)
    ass > (length vars2 = 3) as Hlen_vars2: adm.
    cwr - Hlen_vars2 in *.
    smp - Hstep_v3.
    (* #8 Rewrite Add Vars: rewrite/unfold *)
    rwr - bexp_to_fexp_add_vars in Hstep_v3.
    ufl - bexp_to_fexp_subst measure_env_exp in *.
    (* #9 Translate Values: unfold/rewrite/clear/destruct/simpl/remember *)
    ufl - bvs_to_fvs in *.
    cwr - Heq_exc in *; clr - exc'.
    des - exc as [[ec vr] vd].
    smp *.
    rem - vr' vd' as Heq_vr Heq_vd:
      (bval_to_fval fns vr)
      (bval_to_fval fns vd);
      clr - Heq_vr Heq_vd  Heq_v3 vr vd v3.
    (* #10 FrameStack Proof: scope/step *)
    framestack_scope - Hscope_v3.
    framestack_step.
    framestack_step - Hstep_exc / kexc e1.
    (* #11 Handle Error: constructor/unfold/destruct/simple *)
    ens : apply eval_cool_try_err.
    ufl - exclass_to_value Syntax.exclass_to_value in *.
    des - ec; smp *.
    (* #12 FrameStack Proof 2: step *)
    * framestack_step - Hstep_v3.
    * framestack_step - Hstep_v3.
    * framestack_step - Hstep_v3.
  Admitted.



End Equivalence_Doubles2.









Section Equivalence_Lists.



  Theorem eq_bs_to_fs_nil_tuple :
    forall fns env vl,
        (Datatypes.length ([] : list Expression) = Datatypes.length vl)
    ->  ⟨ [], bexp_to_fexp_subst fns env (ETuple []) ⟩
          -->* bres_to_fres fns (inl [VTuple vl]).
  Proof.
    (* #1 Rewrite Value List: inro/simpl/symmetry/apply/inversion *)
    itr - fns env vl Hlength_vl.
    smp - Hlength_vl.
    sym - Hlength_vl.
    app + length_zero_iff_nil as Hempty_vl in Hlength_vl.
    ivc - Hempty_vl.
    (* #2 FrameStack Proof: scope/step *)
    framestack_scope.
    framestack_step.
  Qed.



  Theorem eq_bs_to_fs_suc_tuple :
    forall fns r env el vl,
        (Datatypes.length el = Datatypes.length vl)
    ->  (forall i,
            i < Datatypes.length el
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i vl ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env (nth i el ErrorExp) ⟩ -->* r))
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inl [VTuple vl]) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ETuple el) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion *)
    itr - fns r env el vl Hlength Hfs Hwfm Hresult.
    ivc - Hresult.
    (* #2 Destruct Expression List: destruct *)
    des - el as [|e el]: pse - eq_bs_to_fs_nil_tuple: fns env vl Hlength.
    (* #3 Fix Result: destruct + smp/congruence *)
    des - vl: smp *; con.
    (* #4 Measure Reduction: unfold/simpl/rewrite *)
    ufl - bexp_to_fexp_subst measure_env_exp.
    smp.
    rwr - mred_eel_e
          mred_eel_el.
    (* #5 Well Formed Map: assert/apply *)
    ass - as Hwfm_v: des - Hwfm as [[H _] _] >
      (fs_wfm_val (bval_to_fval fns v)).
    app - fs_wfm_val_to_result in Hwfm_v.
    (* #6 Remember Values: remember *)
    rem - v' vl' as Hv' Heq_vl:
      (bval_to_fval fns v)
      (map (bval_to_fval fns) vl).
    (* #7 Pose Ident Theorem: pose + clear *)
    pse - create_result_vtuple as Hcreate: v' vl'.
    pse - list_biforall_vtuple_nth_eq as Hlist:
      fns env e el v vl v' vl'
      Hv' Heq_vl Hlength Hwfm Hfs;
      clr - Hlength Hwfm.
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
    (* #8 Specialize Inductive Hypothesis: assert/specialize/simpl *)
    ass - as Hl: sli >
      (0 < Datatypes.length (e :: el)).
    ass - as He: smp; rwr - Hv' >
      (bres_to_fres fns (inl [nth 0 (v :: vl) ErrorValue]) = RValSeq [v']).
    spc - Hfs as Hfs_v: 0 Hl fns (RValSeq [v']) Hwfm_v He.
    smp - Hfs_v.
    (* #9 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v as [kv [Hscope_v Hstep_v]].
    des - Hfs_vl as [kvl Hstep_vl].
    (* #10 FrameStack Proof: scope/step *)
    eei; spl.
    1: admit. (*Needs to modify main proof, it need is_result r predicate *)
    framestack_step - Hstep_v / kv.
    framestack_step - Hstep_vl.
  Admitted.



  Lemma length_split :
    forall A B (al : list A) (bl : list B),
      length al < length bl ->
      exists bl1 bl2 : list B, bl = bl1 ++ bl2 /\ length bl1 = length al.
  Proof.
    itr - A B al bl Hl.
    exi - (firstn (length al) bl)  (skipn (length al) bl).
    spl.
    * by rewrite take_drop.
    * rwr - firstn_length_le.
      - rfl.
      - lia.
  Qed.



  Theorem eq_bs_to_fs_exc_tuple :
    forall fns r env el vl exc j,
        j < Datatypes.length el
    ->  (Datatypes.length vl = j)
    ->  (forall i,
            i < j
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i vl ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env (nth i el ErrorExp) ⟩ -->* r))
    ->  (forall fns r,
         fs_wfm_result r
         → bres_to_fres fns (inr exc) = r
           → ⟨ [], bexp_to_fexp_subst fns env (nth j el ErrorExp) ⟩ -->* r
        )
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inr exc) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ETuple el) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion *)
    itr - fns r env el vl exc j Hl_el Hlength_vl Hfs Hfs_exc Hwfm_exc
          Hresult.
    ivc - Hresult.
    (* Split*)
    pse - length_split as Hsplit_el: Value Expression vl el Hl_el.
    des - Hsplit_el as [el1 [el2 [Heq_el Hlength_vl]]].
    cwr - Heq_el in *; clr - el.
    (* Destruct Exp List *)
    des - el2 as [| e' el']: rwr - app_nil_r in Hl_el; lia.
    des - vl as [| v vl].
    * (* Formalize *)
      app - length_zero_iff_nil as Hempty_vl in Hlength_vl.
      ivc - Hempty_vl.
      rwr - app_nil_l in *.
      clr - Hl_el.
      (* measure_reduction *)
      ufl - bexp_to_fexp_subst measure_env_exp.
      smp.
      rwr - mred_eel_e
          mred_eel_el.
      (*specialzie*)
      spc - Hfs_exc: fns (bres_to_fres fns (inr exc)) Hwfm_exc.
      spe_rfl - Hfs_exc.
      smp - Hfs_exc.
      (* destruct*)
      des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
      framestack_scope - Hscope_exc.
      framestack_step - Hstep_exc.
      framestack_step.
    * (*Formalize*)
      des - el1 as [| e el]: ivc - Hlength_vl.
      
      (* # Measure Reduction: unfold/simpl/rewrite *)
      ufl - bexp_to_fexp_subst measure_env_exp.
      smp.
      rwr - mred_eel_e
            mred_eel_el.
      rwr - split_list.
      smp.
      rwr - mred_eel_e
            mred_eel_el.
      (* #5 Well Formed Map: assert/apply *)
      ass - as Hwfm_vvl : adm >
        (fs_wfm_result (bres_to_fres fns (inl [VTuple (v :: vl)]))).
      ass - as Hwfm_v: des - Hwfm_vvl as [[H _] _] >
      (fs_wfm_val (bval_to_fval fns v)).
      app - fs_wfm_val_to_result in Hwfm_v.
        (* (fs_wfm_result (RValSeq [Syntax.VTuple
          ((bval_to_fval fns v) :: (map (bval_to_fval fns) vl))])). *)
      (* #6 Remember Values: remember *)
      rem - v' vl' exc' as Heq_v Heq_vl Heq_exc:
        (bval_to_fval fns v)
        (map (bval_to_fval fns) vl)
        (bres_to_fres fns (inr exc)).
      (* #7 Pose Ident Theorem: pose + clear *)
      rwl - Hlength_vl in Hfs.
      pse - list_biforall_vtuple_nth_le as Hlist:
        fns env e el (e' :: el') v vl v' vl'
        Heq_v Heq_vl Hlength_vl Hwfm_vvl Hfs;
        clr - Hwfm_vvl.
      pose proof framestack_ident_partial
        ITuple
        (map (bexp_to_fexp fns)
          (map (subst_env (measure_list measure_exp el + measure_env env) env)
            el))
        (bexp_to_fexp_subst fns env e')
        (map (bexp_to_fexp fns)
          (map (subst_env (measure_list measure_exp el' + measure_env env) env)
            el'))
        vl' v' [] [] Hlist
        as Hfs_vl;
        clr - Hlist.
      (* #8 Specialize Inductive Hypothesis: assert/specialize/simpl *)
      ass - as Hl: sli >
        (0 < Datatypes.length (e :: el)).
      ass - as He: smp; rwr - Heq_v >
        (bres_to_fres fns (inl [nth 0 (v :: vl) ErrorValue]) = RValSeq [v']).
      spc - Hfs as Hfs_v: 0 Hl fns (RValSeq [v']) Hwfm_v He.
      smp - Hfs_v.
      spc - Hfs_exc: fns exc' Hwfm_exc (symmetry Heq_exc).
      rwl - Hlength_vl in Hfs_exc.
      rwr - nth_middle in Hfs_exc.
      (* #9 Destruct Inductive Hypothesis: destruct *)
      des - Hfs_v as [kv [Hscope_v Hstep_v]].
      des - Hfs_vl as [kvl Hstep_vl].
      des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
      smp - Heq_exc.
      cwr - Heq_exc in *.
      (* #10 FrameStack Proof: scope/step *)
      framestack_scope - Hscope_exc.
      framestack_step - Hstep_v / kv.
      framestack_step - Hstep_vl.
      framestack_step - Hstep_exc.
      framestack_step.
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
    4:  bse - eq_bs_to_fs_suc_tuple:   fns r env exps vals
                                       H H3 Hwfm Hresult.
    11: bse - eq_bs_to_fs_exc_tuple:   fns r env exps vals ex i
                                       H H0 H4 IHbs Hwfm Hresult.
  Admitted.



End Equivalence_Main.