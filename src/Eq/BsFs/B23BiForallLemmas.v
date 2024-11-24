From CoreErlang.Eq.BsFs Require Export B22RememberSubstituteTactics.

Import BigStep.

(* STRUCTURE:
* Simple
  - biforall_vtuple
  - biforall_vmap
* Forall Lesser or Equal
  - biforall_values_nth_le
  - biforall_vtuple_nth_le
* Forall Equal
  - biforall_values_nth_eq
  - biforall_vtuple_nth_eq
*)












Section Simple.



  Theorem biforall_vtuple :
    forall fns kvl vl vl',
        vl' = map (bval_to_fval fns) vl
    ->  ⟨ [], bexp_to_fexp fns
          (bval_to_bexp (subst_env (measure_val (VTuple vl))) (VTuple vl)) ⟩
        -[ kvl ]-> ⟨ [], RValSeq [Syntax.VTuple vl'] ⟩
    ->  list_biforall
          (fun e v => ⟨ [], RExp e ⟩ -->* RValSeq [v])
          (map
            (bexp_to_fexp fns)
            (map (bval_to_bexp (subst_env (measure_val (VTuple vl)))) vl))
          vl'.
  Proof.
    (* #1 Rewrite Equivality: intro/rewrite *)
    itr - fns kvl vl vl' Heq_vl Hstep.
    cwr - Heq_vl in *.
    (* #2 Simplify: refold *)
    rfl - bval_to_bexp
          bexp_to_fexp in Hstep.
    (* #3 Inversion Step: inversion/remember_subst *)
    ivc - Hstep as Hstep1 Hstep2: H H0.
    rem_sbt: (VTuple vl).
    ivc - Hstep1 as Hstep: Hstep2.
    ivc - Hstep as Hstep1 Hstep2: H H0.
    rem_sbt: (VTuple vl).
    ivc - Hstep1 as Hexp Hnot Hstep: H2 H5 Hstep2.
    * (* #4.1 Fix List: destruct/simpl + inversion *)
      des - vl: ivr - Hexp.
      simpl map in Hstep.
      (* #5.1 Pose Reverse: assert/pose + left/clear *)
      ass - as Hident: lft >
        (ITuple = ITuple \/ ITuple = IMap).
      psc - ident_reverse: el e
        ([] : list Val)
        ITuple k0
        ([Syntax.VTuple (bval_to_fval fns v :: map (bval_to_fval fns) vl)])
        Hstep Hident.
      (* #6.1 Solve by Reverse: destruct/rename/inversion + assumption *)
      do 3 des - H.
      ren - v0 vl0 eff0: x x0 x1.
      des - H as [Hcreate Hbiforall].
      bvs - Hcreate.
    * (* #4.2 Prove by Contraction: rename/inversion/constructor *)
      ren - Hcreate: H6.
      ivc - Hcreate.
      ivc - Hstep.
      1: cns.
      ren - Hstep1 Hstep2: H H0.
      ivc - Hstep1.
  Qed.






  Theorem biforall_vmap :
    forall fns kvl vl vl',
        vl' = make_val_map vl'
    ->  vl' = map (prod_map (bval_to_fval fns) (bval_to_fval fns)) vl
    ->  ⟨ [], bexp_to_fexp fns
          (bval_to_bexp (subst_env (measure_val (VMap vl))) (VMap vl)) ⟩
        -[ kvl ]-> ⟨ [], RValSeq [Syntax.VMap vl'] ⟩
    ->  list_biforall
          (fun e v => ⟨ [], RExp e ⟩ -->* RValSeq [v])
          (flatten_list
            (map
              (prod_map
                  (bexp_to_fexp fns)
                  (bexp_to_fexp fns))
              (map
                (prod_map
                  (bval_to_bexp (subst_env (measure_val (VMap vl))))
                  (bval_to_bexp (subst_env (measure_val (VMap vl)))))
                 vl)))
          (flatten_list vl').
  Proof.
    (* #1 Rewrite Equivality: intro/rewrite *)
    itr - fns kvl vl vl' Heq_map Heq_vl Hstep.
    cwr - Heq_vl in *; clr - vl'.
    (* #2 Simplify: refold *)
    rfl - bval_to_bexp
          bexp_to_fexp in Hstep.
    (* #3 Inversion Step: inversion/remember_subst/constructor/rename + clear *)
    ivc - Hstep as Hstep1 Hstep2: H H0.
    rem_sbt: (VMap vl).
    ivc - Hstep1 as Hstep Heq_list: Hstep2 H1.
    {
      ivc - Hstep.
      1: cns.
      ren - Hstep1 Hstep2: H H0.
      ivc - Hstep1.
    }
    rem_sbt: (VMap vl).
    (* #4 Fix List: destruct/simpl/inversion + inversion/subst/clear *)
    des - vl as [| [v1 v2] vl]: ivs - Heq_list.
    smp ~ map - Heq_map.
    smp ~ map - Hstep.
    smp + Heq_list.
    ivc - Heq_list.
    (* #5 Measure Reduction: rewrite *)
    rwr - mred_vmap_v1
          mred_vmap_v2
          mred_vmap_vll
          in *.
    (* #6 Pose Reverse: rewrite/assert/pose + left/clear *)
    rwr - Heq_map in Hstep.
    ass - as Hident: rgt >
      (IMap = ITuple \/ IMap = IMap).
    psc - ident_reverse: 
      (bexp_to_fexp fns (bval_to_bexp (subst_env (measure_val v2)) v2)
        :: flatten_list
          (map (prod_map (bexp_to_fexp fns) (bexp_to_fexp fns))
            (map
              (prod_map (bval_to_bexp (subst_env (measure_val (VMap vl))))
                (bval_to_bexp (subst_env (measure_val (VMap vl))))) vl)))
      (bexp_to_fexp fns (bval_to_bexp (subst_env (measure_val v1)) v1))
      ([] : list Val)
      IMap k
      ([Syntax.VMap
        (make_val_map
          ((bval_to_fval fns v1, bval_to_fval fns v2)
            :: map (prod_map (bval_to_fval fns) (bval_to_fval fns)) vl))])
      Hstep Hident.
    (* #6.1 Solve by Reverse: destruct/rename/inversion + assumption *)
    do 3 des - H.
    ren - v0 vl0 eff0: x x0 x1.
    des - H as [Hcreate Hbiforall].
    ivs - Hcreate.
    admit.
    (* Not Solvable *)
  Admitted.



End Simple.









Section Forall_LesserOrEqual.



  Theorem biforall_values_nth_le :
    forall fns env e el1 el2 v vl1 v' vl1',
        v' = bval_to_fval fns v
    ->  vl1' = map (bval_to_fval fns) vl1
    ->  Datatypes.length (e :: el1) = Datatypes.length (v :: vl1)
    ->  fs_wfm_result (bresult_to_fresult fns (inl (v :: vl1)))
    ->  (forall i,
            i < Datatypes.length (e :: el1)
        ->  (forall fns r,
                fs_wfm_result r
            ->  bresult_to_fresult fns (inl [nth i (v :: vl1) ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env
                    (nth i (e :: el1 ++ el2) ErrorExp) ⟩
                  -->* r))
    ->  list_biforall
          (fun e v => ⟨ [], RExp e ⟩ -->* RValSeq [v])
          (map
            (bexp_to_fexp fns)
            (map
              (subst_env (measure_list measure_exp el1 + measure_env env) env) 
              el1))
          vl1'.
  Proof.
    (* #1 Intro: intro/subst/generalize *)
    itr - fns env e0 el1 el2 v0 vl1 v0' vl1' Heq_v Heq_vl Hlength Hwfm Hfs_nth.
    sbt.
    gen - vl1.
    (* #2 Induction: induction + destruct/simpl/congruence/constructor*)
    ind - el1 as [| e1 el1 IHel1] :> itr; des - vl1 as [| v1 vl1]; smp + Hlength
        :- con + cns.
    cns.
    * (* #3.1 Measure Reduction: clear/rewrite *)
      clr - IHel1 Hlength.
      rwr - mred_eel_e.
      (* #4.1 Prepare for Specialize: simpl/destruct/apply/assert *)
      smp - Hwfm.
      des - Hwfm as [_ [Hwfm_v1]].
      app - fs_wfm_val_to_result in Hwfm_v1.
      ass > (1 < Datatypes.length (e0 :: e1 :: el1)) as Hnlt: sli.
      (* #5.1 Specialize: specialize *)
      spc - Hfs_nth as Hfs_v1:
        1 Hnlt fns (RValSeq [bval_to_fval fns v1]) Hwfm_v1.
      spe_rfl - Hfs_v1.
      (* #6.1 Prove by Hypothesis: simpl/assumption *)
      smp - Hfs_v1.
      asm.
    * (* #3.2 Measure Reduction: rewrite *)
      rwr - mred_eel_el.
      (* #4.2 Apply Indutive Hypothesis: apply + simpl/inversion/subst/tauto *)
      app - IHel1.
      1: smp; bvs - Hlength.
      1: smp + Hwfm; tau.
      (* #5.2 Destruct: clear/destruct/intro/inversion *)
      clr - IHel1 Hwfm fns.
      des - i; itr - Hnlt' fns r Hwfm_vi Hresult; ivc - Hresult.
      - (* #6.2.1 Prepare for Specialize: clear/simpl/destruct/apply/assert *)
        clr - Hnlt'.
        smp - Hwfm_vi.
        des - Hwfm_vi as [Hwfm_v0 _].
        app - fs_wfm_val_to_result in Hwfm_v0.
        ass > (0 < Datatypes.length (e0 :: e1 :: el1)) as Hnlt: sli.
        (* #7.2.1 Specialize: specialize *)
        spc - Hfs_nth as Hfs_v0: 
          0 Hnlt fns (RValSeq [bval_to_fval fns v0]) Hwfm_v0.
        spe_rfl - Hfs_v0.
        (* #8.2.1 Prove by Hypothesis: simpl/assumption *)
        smp + Hfs_v0.
        asm.
      - (* #6.2.2 Prepare for Specialize: clear/simpl/destruct/apply/assert *)
        smp + Hnlt' Hwfm_vi.
        ass > (S (S i) < Datatypes.length (e0 :: e1 :: el1)) as Hnlt: sli.
        clr - Hnlt'.
        (* #7.2.2 Specialize: specialize *)
        spc - Hfs_nth as Hfs_vi: (S (S i)) Hnlt fns
          (bresult_to_fresult fns
            (inl [nth (S (S i)) (v0 :: v1 :: vl1) ErrorValue])).
        smp - Hfs_vi.
        spc - Hfs_vi: Hwfm_vi.
        spe_rfl - Hfs_vi.
        (* #8.2.2 Prove by Hypothesis: assumption *)
        asm.
  Qed.






  Theorem biforall_vtuple_nth_le :
    forall fns env e el1 el2 v vl1 v' vl1',
        v' = bval_to_fval fns v
    ->  vl1' = map (bval_to_fval fns) vl1
    ->  Datatypes.length (e :: el1) = Datatypes.length (v :: vl1)
    ->  fs_wfm_result (bresult_to_fresult fns (inl [VTuple (v :: vl1)]))
    ->  (forall i,
            i < Datatypes.length (e :: el1)
        ->  (forall fns r,
                fs_wfm_result r
            ->  bresult_to_fresult fns (inl [nth i (v :: vl1) ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env
                    (nth i (e :: el1 ++ el2) ErrorExp) ⟩
                  -->* r))
    ->  list_biforall
          (fun e v => ⟨ [], RExp e ⟩ -->* RValSeq [v])
          (map
            (bexp_to_fexp fns)
            (map
              (subst_env (measure_list measure_exp el1 + measure_env env) env) 
              el1))
          vl1'.
  Proof.
    (* #1 Intro: intro/subst/generalize *)
    itr - fns env e0 el1 el2 v0 vl1 v0' vl1' Heq_v Heq_vl Hlength Hwfm Hfs_nth.
    sbt.
    gen - vl1.
    (* #2 Induction: induction + destruct/simpl/congruence/constructor*)
    ind - el1 as [| e1 el1 IHel1] :> itr; des - vl1 as [| v1 vl1]; smp + Hlength
        :- con + cns.
    cns.
    * (* #3.1 Measure Reduction: clear/rewrite *)
      clr - IHel1 Hlength.
      rwr - mred_eel_e.
      (* #4.1 Prepare for Specialize: simpl/destruct/apply/assert *)
      smp - Hwfm.
      des - Hwfm as [[_ [Hwfm_v1 _]] _].
      app - fs_wfm_val_to_result in Hwfm_v1.
      ass > (1 < Datatypes.length (e0 :: e1 :: el1)) as Hnlt: sli.
      (* #5.1 Specialize: specialize *)
      spc - Hfs_nth as Hfs_v1:
        1 Hnlt fns (RValSeq [bval_to_fval fns v1]) Hwfm_v1.
      spe_rfl - Hfs_v1.
      (* #6.1 Prove by Hypothesis: simpl/assumption *)
      smp - Hfs_v1.
      asm.
    * (* #3.2 Measure Reduction: rewrite *)
      rwr - mred_eel_el.
      (* #4.2 Apply Indutive Hypothesis: apply + simpl/inversion/subst/tauto *)
      app - IHel1.
      1: smp; bvs - Hlength.
      1: smp + Hwfm; tau.
      (* #5.2 Destruct: clear/destruct/intro/inversion *)
      clr - IHel1 Hwfm fns.
      des - i; itr - Hnlt' fns r Hwfm_vi Hresult; ivc - Hresult.
      - (* #6.2.1 Prepare for Specialize: clear/simpl/destruct/apply/assert *)
        clr - Hnlt'.
        smp - Hwfm_vi.
        des - Hwfm_vi as [Hwfm_v0 _].
        app - fs_wfm_val_to_result in Hwfm_v0.
        ass > (0 < Datatypes.length (e0 :: e1 :: el1)) as Hnlt: sli.
        (* #7.2.1 Specialize: specialize *)
        spc - Hfs_nth as Hfs_v0: 
          0 Hnlt fns (RValSeq [bval_to_fval fns v0]) Hwfm_v0.
        spe_rfl - Hfs_v0.
        (* #8.2.1 Prove by Hypothesis: simpl/assumption *)
        smp + Hfs_v0.
        asm.
      - (* #6.2.2 Prepare for Specialize: clear/simpl/destruct/apply/assert *)
        smp + Hnlt' Hwfm_vi.
        ass > (S (S i) < Datatypes.length (e0 :: e1 :: el1)) as Hnlt: sli.
        clr - Hnlt'.
        (* #7.2.2 Specialize: specialize *)
        spc - Hfs_nth as Hfs_vi: (S (S i)) Hnlt fns
          (bresult_to_fresult fns
            (inl [nth (S (S i)) (v0 :: v1 :: vl1) ErrorValue])).
        smp - Hfs_vi.
        spc - Hfs_vi: Hwfm_vi.
        spe_rfl - Hfs_vi.
        (* #8.2.2 Prove by Hypothesis: assumption *)
        asm.
  Qed.




End Forall_LesserOrEqual.









Section Forall_Equal.



  Theorem biforall_values_nth_eq :
    forall fns env e el v vl v' vl',
        v' = bval_to_fval fns v
    ->  vl' = map (bval_to_fval fns) vl
    ->  Datatypes.length (e :: el) = Datatypes.length (v :: vl)
    ->  fs_wfm_result (bresult_to_fresult fns (inl (v :: vl)))
    ->  (forall i,
            i < Datatypes.length (e :: el)
        ->  (forall fns r,
                fs_wfm_result r
            ->  bresult_to_fresult fns (inl [nth i (v :: vl) ErrorValue]) = r
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
    by pose proof biforall_values_nth_le
      fns env e el [] v vl v' vl'
      Heq_v Heq_vl Hlength Hwfm Hfs_nth.
  Qed.






  Theorem biforall_vtuple_nth_eq :
    forall fns env e el v vl v' vl',
        v' = bval_to_fval fns v
    ->  vl' = map (bval_to_fval fns) vl
    ->  Datatypes.length (e :: el) = Datatypes.length (v :: vl)
    ->  fs_wfm_result (bresult_to_fresult fns (inl [VTuple (v :: vl)]))
    ->  (forall i,
            i < Datatypes.length (e :: el)
        ->  (forall fns r,
                fs_wfm_result r
            ->  bresult_to_fresult fns (inl [nth i (v :: vl) ErrorValue]) = r
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
    by pose proof biforall_vtuple_nth_le
      fns env e el [] v vl v' vl'
      Heq_v Heq_vl Hlength Hwfm Hfs_nth.
  Qed.



End Forall_Equal.