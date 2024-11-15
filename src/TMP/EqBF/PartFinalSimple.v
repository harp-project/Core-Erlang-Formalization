From CoreErlang.TMP.EqBF Require Export Part3Simple.

Import BigStep.















(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: EQUIVALENCE  /////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(** STRUCTURE:
* Help
  - list_biforall_vtuple_nth_le
  - list_biforall_vtuple_nth_eq
* Atoms1
  - eq_bs_to_fs_suc_nil
  - eq_bs_to_fs_suc_lit
* Atoms2
  - eq_bs_to_fs_suc_var
  - eq_bs_to_fs_su1_funid
  - eq_bs_to_fs_su2_funid
* Closures
  - eq_bs_to_fs_suc_fun
  - eq_bs_to_fs_suc_letrec
* Double1
  - eq_bs_to_fs_suc_cons
  - eq_bs_to_fs_ex1_cons
  - eq_bs_to_fs_ex2_cons
  - eq_bs_to_fs_suc_seq
  - eq_bs_to_fs_exc_seq
* Double2
  - eq_bs_to_fs_suc_let
  - eq_bs_to_fs_exc_let
  - eq_bs_to_fs_suc_try
  - eq_bs_to_fs_exc_try
* List1
  - eq_bs_to_fs_nil_tuple
  - eq_bs_to_fs_suc_tuple
  - eq_bs_to_fs_exc_tuple
  - eq_bs_to_fs_nil_values
  - eq_bs_to_fs_suc_values
  - eq_bs_to_fs_exc_values
* List2
  - eq_bs_to_fs_nil_map
  - eq_bs_to_fs_suc_map
  - eq_bs_to_fs_exc_map
  - eq_bs_to_fs_nil_primop
  - eq_bs_to_fs_suc_primop
  - eq_bs_to_fs_exc_primop
*)









Section Equivalence_Help.



  (* Solved *)
  Theorem list_biforall_vtuple_nth_le :
    forall fns env e el1 el2 v vl1 v' vl1',
        v' = bval_to_fval fns v
    ->  vl1' = map (bval_to_fval fns) vl1
    ->  Datatypes.length (e :: el1) = Datatypes.length (v :: vl1)
    ->  fs_wfm_result (bres_to_fres fns (inl [VTuple (v :: vl1)]))
    ->  (forall i,
            i < Datatypes.length (e :: el1)
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i (v :: vl1) ErrorValue]) = r
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
      app - IHel1: smp; ivs - Hlength | smp + Hwfm; tau.
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
          (bres_to_fres fns (inl [nth (S (S i)) (v0 :: v1 :: vl1) ErrorValue])).
        smp - Hfs_vi.
        spc - Hfs_vi: Hwfm_vi.
        spe_rfl - Hfs_vi.
        (* #8.2.2 Prove by Hypothesis: assumption *)
        asm.
  Qed.



  (* Solved *)
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



  (* Solved *)
  Theorem list_biforall_values_nth_le :
    forall fns env e el1 el2 v vl1 v' vl1',
        v' = bval_to_fval fns v
    ->  vl1' = map (bval_to_fval fns) vl1
    ->  Datatypes.length (e :: el1) = Datatypes.length (v :: vl1)
    ->  fs_wfm_result (bres_to_fres fns (inl (v :: vl1)))
    ->  (forall i,
            i < Datatypes.length (e :: el1)
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i (v :: vl1) ErrorValue]) = r
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
      app - IHel1: smp; ivs - Hlength | smp + Hwfm; tau.
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
          (bres_to_fres fns (inl [nth (S (S i)) (v0 :: v1 :: vl1) ErrorValue])).
        smp - Hfs_vi.
        spc - Hfs_vi: Hwfm_vi.
        spe_rfl - Hfs_vi.
        (* #8.2.2 Prove by Hypothesis: assumption *)
        asm.
  Qed.



  (* Solved *)
  Theorem list_biforall_values_nth_eq :
    forall fns env e el v vl v' vl',
        v' = bval_to_fval fns v
    ->  vl' = map (bval_to_fval fns) vl
    ->  Datatypes.length (e :: el) = Datatypes.length (v :: vl)
    ->  fs_wfm_result (bres_to_fres fns (inl (v :: vl)))
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
    by pose proof list_biforall_values_nth_le
      fns env e el [] v vl v' vl'
      Heq_v Heq_vl Hlength Hwfm Hfs_nth.
  Qed.

(*
env : Environment
ke, ve : Expression
el : list (Expression * Expression)
kv : Value
kvl : list Value
vv : Value
vvl : list Value
mkv : Value
mkvl : list Value
mvv : Value
mvvl : list Value
Hlength_kvl : Datatypes.length ((ke, ve) :: el) = Datatypes.length (kv :: kvl)
Hlength_vvl : Datatypes.length ((ke, ve) :: el) = Datatypes.length (vv :: vvl)
Hmake_vl : make_value_map (kv :: kvl) (vv :: vvl) = (mkv :: mkvl, mvv :: mvvl)
Hfs_nth : ∀ i : nat,
            i < Datatypes.length (make_map_exps ((ke, ve) :: el))
            → ∀ (fns : name_sub) (r : Redex),
                fs_wfm_result r
                → bres_to_fres fns (inl [nth i (make_map_vals (kv :: kvl) (vv :: vvl)) ErrorValue]) =
                  r
                  → ⟨ [],
                    bexp_to_fexp_subst fns env (nth i (make_map_exps ((ke, ve) :: el)) ErrorExp)
                    ⟩ -->* r
kv' : Val
Heq_kv : kv' = bval_to_fval fns mkv
vv' : Val
Heq_vv : vv' = bval_to_fval fns mvv
vl' : list (Val * Val)
Heq_vl : vl' = map (λ '(x, y), (bval_to_fval fns x, bval_to_fval fns y)) (combine mkvl mvvl)
Hmake_vvl : (kv', vv') :: vl' = make_val_map ((kv', vv') :: vl')
Hwfm_kv : fs_wfm_result [kv']
Hwfm_vv : fs_wfm_result [vv']
Hlength : Datatypes.length kvl = Datatypes.length vvl
Hwfm_vl : vl' = make_val_map vl'
Hcreate : create_result IMap ([kv'] ++ vv' :: flatten_list vl') [] =
          Some ([Syntax.VMap (make_val_map ((kv', vv') :: vl'))], [])
______________________________________(1/1)
⟨ [],
° Syntax.EMap
    ((bexp_to_fexp fns (subst_env (measure_env_exp env ke) env ke),
      bexp_to_fexp fns (subst_env (measure_env_exp env ve) env ve))
     :: map (λ '(x, y), (bexp_to_fexp fns x, bexp_to_fexp fns y))
          (map
             (prod_map (subst_env (measure_map measure_exp el + measure_env env) env)
                (subst_env (measure_map measure_exp el + measure_env env) env)) el)) ⟩ -->*
[Syntax.VMap ((kv', vv') :: vl')]
*)

(*
  Theorem list_biforall_vmap_nth_le1 :
    forall fns env ke ve el1 el2 kv vv kvl1 vvl1 kv' vv' vl1' vl',
        (* v' = bval_to_fval fns v
    ->  vl1' = map (bval_to_fval fns) vl1
    ->   *)Datatypes.length ((ke, ve) :: el1) = Datatypes.length ((kv, vv) :: vl1)
    ->  fs_wfm_result (bres_to_fres fns (inl [VTuple (v :: vl1)]))
    ->  (forall i,
            i < Datatypes.length ((ke, ve) :: el1)
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns
                  (inl [nth i
                    (make_map_vals (kv :: kvl1) (vv :: vvl1) ErrorValue])) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env
                    (nth i (make_map_exps ((ke, ve) :: el1 ++ el2)) ErrorExp) ⟩
                  -->* r))
    ->  list_biforall
          (fun e v => ⟨ [], RExp e ⟩ -->* RValSeq [v])
          (flatten_list
            (map
              (fun '(x, y) => (bexp_to_fexp fns x, bexp_to_fexp fns y))
              (map
                (prod_map
                  (subst_env
                    (measure_list measure_exp el1 + measure_env env)
                    env)
                  (subst_env
                    (measure_list measure_exp el1 + measure_env env)
                    env))
                 el1)))
          (flatten_list vl1).
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
      app - IHel1: smp; ivs - Hlength | smp + Hwfm; tau.
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
          (bres_to_fres fns (inl [nth (S (S i)) (v0 :: v1 :: vl1) ErrorValue])).
        smp - Hfs_vi.
        spc - Hfs_vi: Hwfm_vi.
        spe_rfl - Hfs_vi.
        (* #8.2.2 Prove by Hypothesis: assumption *)
        asm.
  Qed.
*)


End Equivalence_Help.









Section Equivalence_Atoms1.



  (* Solved *)
  Theorem eq_bs_to_fs_suc_nil :
    forall fns r env,
        bres_to_fres fns (inl [VNil]) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env ENil ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env Hresult.
    ivc - Hresult.
    (* #2 FrameStack Proof: scope/step *)
    framestack_scope.
    framestack_step.
  Qed.



  (* Solved *)
  Theorem eq_bs_to_fs_suc_lit :
    forall fns r env lit,
        bres_to_fres fns (inl [VLit lit]) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ELit lit) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env lit Hresult.
    ivc - Hresult.
    (* #2 FrameStack Proof: scope/step *)
    framestack_scope.
    framestack_step.
  Qed.



End Equivalence_Atoms1.









Section Equivalence_Atoms2.



  (* Solved *)
  Theorem eq_bs_to_fs_suc_var :
    forall fns r env var vs,
        get_value env (inl var) = Some vs
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inl vs) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EVar var) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env var vs Hget Hwfm Hresult.
    ivc - Hresult.
    (* #2 Rewrite Get: cbn/rewrite *)
    sbn.
    rwr - Hget.
    (* #3 Destruct Match: destruct/simple + apply/simpl/congruence *)
    des - vs as [|v vs]:
      app - get_value_singelton_length in Hget; smp - Hget; con.
    des - vs as [|v0 vs]:
      app - get_value_singelton_length in Hget; smp - Hget; con.
    smp.
    (* #4 Measure Reduction: apply/destruct/assert/pose/rewrite + clear/triv *)
    app - get_value_in in Hget as HIn.
    app - In_split in HIn as Heq_env.
    des - Heq_env as [env1]; ren - Heq_env: H.
    des - Heq_env as [env2]; ren - Heq_env: H.
    cwr - Heq_env; clr - env.
    ass - as Hnle: triv_nle_solver >
      (measure_val v <= measure_env (env1 ++ (inl var, v) :: env2)).
    psc - mred_val_min as Hmred_v: v
      (measure_env (env1 ++ (inl var, v) :: env2)) Hnle.
    cwr - Hmred_v; clr - env1 env2 var.
    (* #5 Well Formed Map: destruct/apply *)
    des - Hwfm as [Hwfm_v _].
    app - fs_wfm_val_to_forall in Hwfm_v.
    (* #6 Remember Values: remember *)
    rem - v' as Heq_v:
      (bval_to_fval fns v).
    (* #7 Pose Reduction: symmetry/pose *)
    bse - bs_to_fs_equivalence_reduction: v fns v' Hwfm_v Heq_v.
  Qed.



    (* Solved *)
  Theorem eq_bs_to_fs_su1_funid :
    forall fns r env fid vs,
        get_value env (inr fid) = Some vs
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inl vs) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EFunId fid) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env var vs Hget Hwfm Hresult.
    ivc - Hresult.
    (* #2 Rewrite Get: cbn/rewrite *)
    sbn.
    rwr - Hget.
    (* #3 Destruct Match: destruct/simple + apply/simpl/congruence *)
    des - vs as [|v vs]:
      app - get_value_singelton_length in Hget; smp - Hget; con.
    des - vs as [|v0 vs]:
      app - get_value_singelton_length in Hget; smp - Hget; con.
    smp.
    (* #4 Measure Reduction: apply/destruct/assert/pose/rewrite + clear/triv *)
    app - get_value_in in Hget as HIn.
    app - In_split in HIn as Heq_env.
    des - Heq_env as [env1]; ren - Heq_env: H.
    des - Heq_env as [env2]; ren - Heq_env: H.
    cwr - Heq_env; clr - env.
    ass - as Hnle: triv_nle_solver >
      (measure_val v <= measure_env (env1 ++ (inr var, v) :: env2)).
    psc - mred_val_min as Hmred_v: v
      (measure_env (env1 ++ (inr var, v) :: env2)) Hnle.
    cwr - Hmred_v; clr - env1 env2 var.
    (* #5 Well Formed Map: destruct/apply *)
    des - Hwfm as [Hwfm_v _].
    app - fs_wfm_val_to_forall in Hwfm_v.
    (* #6 Remember Values: remember *)
    rem - v' as Heq_v:
      (bval_to_fval fns v).
    (* #7 Pose Reduction: symmetry/pose *)
    bse - bs_to_fs_equivalence_reduction: v fns v' Hwfm_v Heq_v.
  Qed.



  (* Admitted: modules own_module *)
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
    (* #1 Inversion Result: intro/inversion + subst/clear *)
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









Section Equivalence_Closures.



  (* Solved: except Scope *)
  Theorem eq_bs_to_fs_suc_fun :
    forall fns r env e vars id,
        bres_to_fres fns (inl [VClos env [] id vars e None]) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EFun vars e) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env e vars id Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn.
    rwr - mred_e_vars.
    (* #3 FrameStack Proof: scope/step *)
    eei; spl.
    1: {
      cns.
      cns.
      2: cns.
      cns.
      {
        itr.
        smp - H.
        lia.
      }
      smp.
      rwr - Nat.add_0_r.
      admit.
    } (* Scope *)
    framestack_step.
  Admitted.


Lemma add_exp_ext_fids_simpl :
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
    itr.
    ufl - add_exp_ext_fids.
    f_equal.
    ind - ext as [| [a [b c]] ext' IH] :> smp.
    feq.
    app - IH.
  Qed.


  (* Admitted: add_fids needs to be implemented *)
  Theorem eq_bs_to_fs_suc_letrec :
    forall fns r env e l result id,
        (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns result = r
        ->  ⟨ [], bexp_to_fexp_subst fns (append_funs_to_env l env id) e ⟩
              -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns result = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ELetRec l e) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env e l result id Hfs Hwfm Hresult.
    ivc - Hresult.
    (* #2 Simplify: cbn/unfold *)
    sbn.
    rfl - add_exp_ext_both.
    rwr - add_exp_ext_fids_simpl.
    replace
      (subst_env
        (measure_exp e + measure_exp_ext measure_exp l + measure_env env)
        (rem_exp_ext_fids l env) e)
      with
      (subst_env
        (measure_exp e + measure_env (rem_exp_ext_fids l env))
        (rem_exp_ext_fids l env) e).
    2: adm.
    replace
      (map
        (λ '(fid, (vars, body)),
          (fid,
          (vars,
          subst_env
            (measure_exp e + measure_exp_ext measure_exp l + measure_env env)
            (rem_exp_ext_both vars l env) body))) l)
      with
      (map
        (λ '(fid, (vars, body)),
          (fid,
          (vars,
          subst_env
            (measure_exp body + measure_env env)
            (rem_exp_ext_both vars l env) body))) l).
    2: adm.
    (* #3 Specalize *)
    spc - Hfs: fns (bres_to_fres fns result) Hwfm. (* fns? *)
    spe_rfl - Hfs.
    (* #4 Destruct *)
    des - Hfs as [k [Hscope Hstep]].
    (* #5 Rewrite Add Fids: rewrite/unfold *)
    
    (* rwr - bexp_to_fexp_add_fids in Hstep.
    ufl - bexp_to_fexp_subst measure_env_exp in *. *)
    (* #6 FrameStack Proof: scope/step *)
    framestack_scope - Hscope.
    framestack_step.
    (*framestack_step - Hstep. *)
    admit.
  Admitted.



End Equivalence_Closures.









Section Equivalence_Doubles1.



  (* Solved *)
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
    (* #1 Inversion Result: intro/inversion + subst/clear *)
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
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite + clear *)
    spc - Hfs_v2: fns (RValSeq [v2']) Hwfm_v2.
    spc - Hfs_v1: fns (RValSeq [v1']) Hwfm_v1.
    cwl - Heq_v2 Heq_v1 in *; clr - v2 v1.
    spe_rfl - Hfs_v2 Hfs_v1.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v2 as [kv2 [Hscope_v2 Hstep_v2]].
    des - Hfs_v1 as [kv1 [Hscope_v1 Hstep_v1]].
    (* #7 FrameStack Proof: scope/step + clear *)
    framestack_scope - v1' v2' Hscope_v1 Hscope_v2.
    framestack_step - Hstep_v2 / kv2 e2.
    framestack_step - Hstep_v1 / kv1 e1 env fns.
    framestack_step.
  Qed.



  (* Solved: only WFM asserted *)
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
    (* #1 Inversion Result: intro/inversion + subst/clear *)
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
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite + clear *)
    spc - Hfs_v2: fns (RValSeq [v2']) Hwfm_v2.
    spc - Hfs_exc: fns (RExc exc') Hwfm_exc.
    cwl - Heq_v2 Heq_exc in *; clr - v2 exc.
    spe_rfl - Hfs_v2 Hfs_exc.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v2 as [kv2 [_ Hstep_v2]].
    des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
    (* #7 FrameStack Proof: scope/step + clear *)
    framestack_scope - Hscope_exc.
    framestack_step - Hstep_v2 / kv2 e2.
    framestack_step - Hstep_exc / kexc e1 env fns.
    framestack_step.
  Admitted.



  (* Solved *)
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
    (* #1 Inversion Result: intro/inversion + subst/clear *)
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
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite + clear *)
    spc - Hfs_exc: fns (RExc exc') Hwfm_exc.
    cwl - Heq_exc in *; clr - exc.
    spe_rfl - Hfs_exc.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
    (* #7 FrameStack Proof: scope/step + clear *)
    framestack_scope - Hscope_exc.
    framestack_step - Hstep_exc / kexc e2.
    framestack_step.
  Qed.



  (* Solved: only WFM asserted *)
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
    (* #1 Inversion Result: intro/inversion + subst/clear *)
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
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite + clear *)
    spc - Hfs_v1: fns (RValSeq [v1']) Hwfm_v1.
    spc - Hfs_v2: fns v2' Hwfm_v2.
    cwl - Heq_v1 Heq_v2 in *; clr - v1 v2.
    spe_rfl - Hfs_v1 Hfs_v2.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v1 as [kv1 [_ Hstep_v1]].
    des - Hfs_v2 as [kv2 [Hscope_v2 Hstep_v2]].
    (* #7 FrameStack Proof: scope/step + clear *)
    framestack_scope - Hscope_v2.
    framestack_step - Hstep_v1 / kv1 e1.
    framestack_step - Hstep_v2 / kv2 e2 env fns v1'.
    framestack_step.
  Admitted.



  (* Solved *)
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
    (* #1 Inversion Result: intro/inversion + subst/clear *)
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
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite + clear *)
    spc - Hfs_exc: fns (RExc exc') Hwfm_exc.
    cwl - Heq_exc in *; clr - exc.
    spe_rfl - Hfs_exc.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
    (* #7 FrameStack Proof: scope/step + clear *)
    framestack_scope - Hscope_exc.
    framestack_step - Hstep_exc / kexc e1.
    framestack_step.
  Qed.



End Equivalence_Doubles1.









Section Equivalence_Doubles2.



  (* Solved *)
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
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env e1 e2 v1 v2 vars Hlength Hfs_v1 Hfs_v2 Hwfm_v2 Hresult.
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
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite + clear *)
    spc - Hfs_v1: fns (RValSeq v1') Hwfm_v1.
    spc - Hfs_v2: fns v2' Hwfm_v2.
    rwl - Heq_v1 Heq_v2 in *; clr - Heq_v2 v2.
    spe_rfl - Hfs_v1 Hfs_v2.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v1 as [kv1 [_ Hstep_v1]].
    des - Hfs_v2 as [kv2 [Hscope_v2 Hstep_v2]].
    (* #7 Rewrite Add Vars: rewrite/unfold *)
    rwr - bexp_to_fexp_add_vars in Hstep_v2.
    rwl - Heq_v1 in Hstep_v2.
    ufl - bexp_to_fexp_subst measure_env_exp in *.
    (* #8 FrameStack Proof: scope/step + rewrite/pose/clear *)
    framestack_scope - Hscope_v2.
    framestack_step - Hstep_v1 / kv1 e1.
    framestack_step: rwr - Heq_v1 Hlength; bse - bvs_to_fvs_length
      / Hlength Heq_v1 v1.
    framestack_step - Hstep_v2.
  Admitted.



  (* Solved *)
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
    (* #1 Inversion Result: intro/inversion + subst/clear *)
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
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite + clear *)
    spc - Hfs_exc: fns (RExc exc') Hwfm_exc.
    cwl - Heq_exc in *; clr - exc.
    spe_rfl - Hfs_exc.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
    (* #7 FrameStack Proof: scope/step + clear *)
    framestack_scope - Hscope_exc.
    framestack_step - Hstep_exc / kexc e1.
    framestack_step.
  Qed.



  (* Solved: only WFM asserted *)
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
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env e1 e2 e3 v1 v2 vars1 vars2 Hlength Hfs_v1 Hfs_v2 Hwfm_v2
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
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite + clear *)
    spc - Hfs_v1: fns (RValSeq v1') Hwfm_v1.
    spc - Hfs_v2: fns v2' Hwfm_v2.
    rwl - Heq_v1 Heq_v2 in *; clr - Heq_v2 v2.
    spe_rfl - Hfs_v1 Hfs_v2.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v1 as [kv1 [_ Hstep_v1]].
    des - Hfs_v2 as [kv2 [Hscope_v2 Hstep_v2]].
    (* #7 Rewrite Add Vars: rewrite/unfold *)
    rwr - bexp_to_fexp_add_vars in Hstep_v2.
    rwl - Heq_v1 in Hstep_v2.
    ufl - bexp_to_fexp_subst measure_env_exp in *.
    (* #8 FrameStack Proof: scope/step + rewrite/pose/clear *)
    framestack_scope - Hscope_v2.
    framestack_step - Hstep_v1 / kv1 e1.
    framestack_step: rwr - Heq_v1 Hlength; ase - bvs_to_fvs_length
      / Hlength Heq_v1 v1 vars2 e3.
    framestack_step - Hstep_v2.
  Admitted.



  (* Solved: only WFM & Vars2 length asserted *)
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
    (* #1 Inversion Result: intro/inversion + subst/clear *)
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
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite + clear *)
    spc - Hfs_exc: fns exc' Hwfm_exc.
    spc - Hfs_v3: fns v3' Hwfm_v3.
    rwl - Heq_exc Heq_v3 in *; clr - Heq_v3 v3.
    spe_rfl - Hfs_exc Hfs_v3.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_exc as [kexc [_ Hstep_exc]].
    des - Hfs_v3 as [kv3 [Hscope_v3 Hstep_v3]].
    (* TMP FIX: *)
    (* #7 Assert Vars Length: assert/rewrite/simple + clear *)
    ass > (length vars2 = 3) as Hlength_vars2: adm.
    cwr - Hlength_vars2 in *.
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
      clr - Heq_vr Heq_vd vr vd.
    (* #10 FrameStack Proof: scope/step *)
    framestack_scope - Hscope_v3.
    framestack_step.
    framestack_step - Hstep_exc / kexc e1.
    (* #11 Handle Error: constructor/unfold/destruct/simple + apply/clear *)
    ens : apply eval_cool_try_err |> clr - e2 vars1.
    ufl - exclass_to_value Syntax.exclass_to_value in *.
    des - ec; smp *.
    (* #12 FrameStack Proof 2: step *)
    * framestack_step - Hstep_v3.
    * framestack_step - Hstep_v3.
    * framestack_step - Hstep_v3.
  Admitted.



End Equivalence_Doubles2.









Section Equivalence_Lists1.



  (* Solved *)
  Theorem eq_bs_to_fs_nil_tuple :
    forall fns env vl,
        (Datatypes.length ([] : list Expression) = Datatypes.length vl)
    ->  ⟨ [], bexp_to_fexp_subst fns env (ETuple []) ⟩
          -->* bres_to_fres fns (inl [VTuple vl]).
  Proof.
    (* #1 Rewrite Value List: inro/simpl/symmetry/apply/inversion
      + subst/clear *)
    itr - fns env vl Hlength_vl.
    smp - Hlength_vl.
    sym - Hlength_vl.
    app - length_zero_iff_nil as Hempty_vl in Hlength_vl.
    ivc - Hempty_vl.
    (* #2 FrameStack Proof: scope/step *)
    framestack_scope.
    framestack_step.
  Qed.



  (* Solved: only VALSCOPE asserted *)
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
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env el vl Hlength Hfs_nth Hwfm Hresult.
    ivc - Hresult.
    (* #2 Destruct Expression List: destruct + pose *)
    des - el as [|e el]: pse - eq_bs_to_fs_nil_tuple: fns env vl Hlength.
    (* #3 Fix Result: destruct + simpl/congruence *)
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
    rem - v' vl' as Heq_v Heq_vl:
      (bval_to_fval fns v)
      (map (bval_to_fval fns) vl).
    (* #7 Pose Ident Theorem: pose + clear *)
    pse - create_result_vtuple as Hcreate: v' vl'.
    pse - list_biforall_vtuple_nth_eq as Hbiforall:
      fns env e el v vl v' vl'
      Heq_v Heq_vl Hlength Hwfm Hfs_nth;
      clr - Hlength Hwfm Heq_vl.
    pose proof framestack_ident
      ITuple
      (map (bexp_to_fexp fns)
        (map (subst_env (measure_list measure_exp el + measure_env env) env)
          el))
      (RValSeq [Syntax.VTuple (v' :: vl')])
      vl' v' [] [] []
      Hcreate Hbiforall
      as Hfs_vl;
      clr - Hcreate Hbiforall.
    (* #8 Specialize Inductive Hypothesis: assert/specialize/simpl + clear *)
    ass - as Hnlt: sli >
      (0 < Datatypes.length (e :: el)).
    ass - as Heq_nth: smp; rwr - Heq_v >
      (bres_to_fres fns (inl [nth 0 (v :: vl) ErrorValue]) = RValSeq [v']);
      clr - Heq_v.
    spc - Hfs_nth as Hfs_v: 0 Hnlt fns (RValSeq [v']) Hwfm_v Heq_nth;
      clr - v vl.
    smp - Hfs_v.
    (* #9 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v as [kv [_ Hstep_v]].
    des - Hfs_vl as [kvl Hstep_vl].
    (* #10 FrameStack Proof: scope/step + clear *)
    eei; spl.
    1: admit. (*Needs to modify main proof, it need is_result r predicate *)
    framestack_step - Hstep_v / kv e.
    framestack_step - Hstep_vl.
  Admitted.



  (* Solved: only WFM asserted *)
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
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env el vl exc j Hl_el Hlength_vl Hfs_nth Hfs_exc Hwfm_exc
          Hresult.
    ivc - Hresult.
    (* #2 Split List: pose/destruct/rewrite + clear *)
    pse - length_l_split as Hsplit_el: Value Expression vl el Hl_el.
    des - Hsplit_el as [el1 [el2 [Heq_el Hlength_vl]]].
    cwr - Heq_el in *; clr - el.
    (* #3 Destruct Lists: destruct + rewrite/lia/clear *)
    des - el2 as [| e2 el2]: rwr - app_nil_r in Hl_el; lia |> clr - Hl_el.
    des - vl as [| v vl].
    * (* #4.1 Formalize List: clear/apply/inversion/rewrite + subst/clear *)
      clr - Hfs_nth.
      app - length_zero_iff_nil as Hempty_vl in Hlength_vl.
      ivc - Hempty_vl.
      rwr - app_nil_l in *.
      (* #5.1 Measure_Reduction: unfold/simpl/rewrite *)
      ufl - bexp_to_fexp_subst measure_env_exp.
      smp.
      rwr - mred_eel_e
          mred_eel_el.
      (* #6.1 Specialize Inductive Hypothesis: specialize/simpl + clear *)
      spc - Hfs_exc: fns (bres_to_fres fns (inr exc)) Hwfm_exc.
      spe_rfl - Hfs_exc.
      smp - Hfs_exc.
      (* #7.1 Remember Values: remember + clear *)
      rem - exc' as Heq_exc:
        (bexc_to_fexc fns exc);
        clr - Heq_exc exc.
      (* #8.1 Destruct Inductive Hypothesis: destruct *)
      des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
      (* #9.1 FrameStack Proof: scope/step + clear *)
      framestack_scope - Hscope_exc.
      framestack_step - Hstep_exc / kexc e2.
      framestack_step.
    * (* #4.2 Formalize List: destruct/rewrite + inversion/subst *)
      des - el1 as [| e1 el1]: ivs - Hlength_vl.
      rwl - Hlength_vl in *.
      (* #5.2 Measure_Reduction: unfold/simpl/rewrite *)
      ufl - bexp_to_fexp_subst measure_env_exp.
      smp.
      rwr - mred_eel_e
            mred_eel_el
            mred_exp_list_split.
      smp.
      rwr - mred_eel_e
            mred_eel_el.
      simpl bres_to_fres in Hfs_exc, Hwfm_exc.
      (* #6.2 Well Formed Map: assert/apply + destruct *)
      ass - as Hwfm_vvl : adm >
        (fs_wfm_result (bres_to_fres fns (inl [VTuple (v :: vl)]))).
      ass - as Hwfm_v: des - Hwfm_vvl as [[H _] _] >
        (fs_wfm_val (bval_to_fval fns v)).
      app - fs_wfm_val_to_result in Hwfm_v.
      (* #7.2 Remember Values: remember *)
      rem - v' vl' exc' as Heq_v Heq_vl Heq_exc:
        (bval_to_fval fns v)
        (map (bval_to_fval fns) vl)
        (bexc_to_fexc fns exc).
      (* #8.2 Pose Ident Theorem: pose + clear *)
      pse - list_biforall_vtuple_nth_le as Hbiforall:
        fns env e1 el1 (e2 :: el2) v vl v' vl'
        Heq_v Heq_vl Hlength_vl Hwfm_vvl Hfs_nth;
        clr - Heq_vl Hlength_vl Hwfm_vvl.
      pose proof framestack_ident_partial
        ITuple
        (map (bexp_to_fexp fns)
          (map (subst_env (measure_list measure_exp el1 + measure_env env) env)
            el1))
        (bexp_to_fexp_subst fns env e2)
        (map (bexp_to_fexp fns)
          (map (subst_env (measure_list measure_exp el2 + measure_env env) env)
            el2))
        vl' v' [] [] Hbiforall
        as Hfs_vl;
        clr - Hbiforall.
      (* #9.2 Specialize Inductive Hypothesis: assert/specialize/simpl/rewrite
        + clear *)
      ass - as Hnlt: sli >
        (0 < Datatypes.length (e1 :: el1)).
      ass - as Heq_nth: smp; rwr - Heq_v >
        (bres_to_fres fns (inl [nth 0 (v :: vl) ErrorValue]) = RValSeq [v']);
        clr - Heq_v.
      spc - Hfs_nth as Hfs_v: 0 Hnlt fns (RValSeq [v']) Hwfm_v Heq_nth;
        clr - v vl.
      smp - Hfs_v.
      spc - Hfs_exc: fns exc' Hwfm_exc.
      cwl - Heq_exc in Hfs_exc; clr - exc.
      spe_rfl - Hfs_exc.
      rwr - nth_middle in Hfs_exc.
      (* #10.2 Destruct Inductive Hypothesis: destruct/simpl/rewrite + clear *)
      des - Hfs_v as [kv [_ Hstep_v]].
      des - Hfs_vl as [kvl Hstep_vl].
      des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
      (* #11.2 FrameStack Proof: scope/step + clear *)
      framestack_scope - Hscope_exc.
      framestack_step - Hstep_v / kv e1.
      framestack_step - Hstep_vl / kvl el1.
      framestack_step - Hstep_exc / kexc e2.
      framestack_step.
  Admitted.



  (* Solved *)
  Theorem eq_bs_to_fs_nil_values :
    forall fns env vl,
        (Datatypes.length ([] : list Expression) = Datatypes.length vl)
    ->  ⟨ [], bexp_to_fexp_subst fns env (EValues []) ⟩
          -->* bres_to_fres fns (inl vl).
  Proof.
    (* #1 Rewrite Value List: inro/simpl/symmetry/apply/inversion
      + subst/clear *)
    itr - fns env vl Hlength_vl.
    smp - Hlength_vl.
    sym - Hlength_vl.
    app - length_zero_iff_nil as Hempty_vl in Hlength_vl.
    ivc - Hempty_vl.
    (* #2 FrameStack Proof: scope/step *)
    framestack_scope.
    framestack_step.
  Qed.



  (* Solved: only VALSCOPE asserted *)
  Theorem eq_bs_to_fs_suc_values :
    forall fns r env el vl,
        (Datatypes.length el = Datatypes.length vl)
    ->  (forall i,
            i < Datatypes.length el
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i vl ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env (nth i el ErrorExp) ⟩ -->* r))
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inl vl) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EValues el) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env el vl Hlength Hfs_nth Hwfm Hresult.
    ivc - Hresult.
    (* #2 Destruct Expression List: destruct + pose *)
    des - el as [|e el]: pse - eq_bs_to_fs_nil_values: fns env vl Hlength.
    (* #3 Fix Result: destruct + simpl/congruence *)
    des - vl: smp *; con.
    (* #4 Measure Reduction: unfold/simpl/rewrite *)
    ufl - bexp_to_fexp_subst measure_env_exp.
    smp.
    rwr - mred_eel_e
          mred_eel_el.
    (* #5 Well Formed Map: assert/apply *)
    ass - as Hwfm_v: des - Hwfm as [H _] >
      (fs_wfm_val (bval_to_fval fns v)).
    app - fs_wfm_val_to_result in Hwfm_v.
    (* #6 Remember Values: remember *)
    rem - v' vl' as Heq_v Heq_vl:
      (bval_to_fval fns v)
      (bvs_to_fvs fns vl).
    (* #7 Pose Ident Theorem: pose + clear *)
    pse - create_result_values as Hcreate: v' vl'.
    pse - list_biforall_values_nth_eq as Hbiforall:
      fns env e el v vl v' vl'
      Heq_v Heq_vl Hlength Hwfm Hfs_nth;
      clr - Hlength Hwfm Heq_vl.
    pose proof framestack_ident
      IValues
      (map (bexp_to_fexp fns)
        (map (subst_env (measure_list measure_exp el + measure_env env) env)
          el))
      (RValSeq (v' :: vl'))
      vl' v' [] [] []
      Hcreate Hbiforall
      as Hfs_vl;
      clr - Hcreate Hbiforall.
    (* #8 Specialize Inductive Hypothesis: assert/specialize/simpl + clear *)
    ass - as Hnlt: sli >
      (0 < Datatypes.length (e :: el)).
    ass - as Heq_nth: smp; rwr - Heq_v >
      (bres_to_fres fns (inl [nth 0 (v :: vl) ErrorValue]) = RValSeq [v']);
      clr - Heq_v.
    spc - Hfs_nth as Hfs_v: 0 Hnlt fns (RValSeq [v']) Hwfm_v Heq_nth;
      clr - v vl.
    smp - Hfs_v.
    (* #9 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v as [kv [_ Hstep_v]].
    des - Hfs_vl as [kvl Hstep_vl].
    (* #10 FrameStack Proof: scope/step + clear *)
    eei; spl.
    1: admit. (*Needs to modify main proof, it need is_result r predicate *)
    framestack_step - Hstep_v / kv e.
    framestack_step - Hstep_vl.
  Admitted.



  (* Solved: only WFM asserted *)
  Theorem eq_bs_to_fs_exc_values :
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
    ->  ⟨ [], bexp_to_fexp_subst fns env (EValues el) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env el vl exc j Hl_el Hlength_vl Hfs_nth Hfs_exc Hwfm_exc
          Hresult.
    ivc - Hresult.
    (* #2 Split List: pose/destruct/rewrite + clear *)
    pse - length_l_split as Hsplit_el: Value Expression vl el Hl_el.
    des - Hsplit_el as [el1 [el2 [Heq_el Hlength_vl]]].
    cwr - Heq_el in *; clr - el.
    (* #3 Destruct Lists: destruct + rewrite/lia/clear *)
    des - el2 as [| e2 el2]: rwr - app_nil_r in Hl_el; lia |> clr - Hl_el.
    des - vl as [| v vl].
    * (* #4.1 Formalize List: clear/apply/inversion/rewrite + subst/clear *)
      clr - Hfs_nth.
      app - length_zero_iff_nil as Hempty_vl in Hlength_vl.
      ivc - Hempty_vl.
      rwr - app_nil_l in *.
      (* #5.1 Measure_Reduction: unfold/simpl/rewrite *)
      ufl - bexp_to_fexp_subst measure_env_exp.
      smp.
      rwr - mred_eel_e
          mred_eel_el.
      (* #6.1 Specialize Inductive Hypothesis: specialize/simpl + clear *)
      spc - Hfs_exc: fns (bres_to_fres fns (inr exc)) Hwfm_exc.
      spe_rfl - Hfs_exc.
      smp - Hfs_exc.
      (* #7.1 Remember Values: remember + clear *)
      rem - exc' as Heq_exc:
        (bexc_to_fexc fns exc);
        clr - Heq_exc exc.
      (* #8.1 Destruct Inductive Hypothesis: destruct *)
      des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
      (* #9.1 FrameStack Proof: scope/step + clear *)
      framestack_scope - Hscope_exc.
      framestack_step - Hstep_exc / kexc e2.
      framestack_step.
    * (* #4.2 Formalize List: destruct/rewrite + inversion/subst *)
      des - el1 as [| e1 el1]: ivs - Hlength_vl.
      rwl - Hlength_vl in *.
      (* #5.2 Measure_Reduction: unfold/simpl/rewrite *)
      ufl - bexp_to_fexp_subst measure_env_exp.
      smp.
      rwr - mred_eel_e
            mred_eel_el
            mred_exp_list_split.
      smp.
      rwr - mred_eel_e
            mred_eel_el.
      simpl bres_to_fres in Hfs_exc, Hwfm_exc.
      (* #6.2 Well Formed Map: assert/apply + destruct *)
      ass - as Hwfm_vvl : adm >
        (fs_wfm_result (bres_to_fres fns (inl (v :: vl)))).
      ass - as Hwfm_v: des - Hwfm_vvl as [H _] >
        (fs_wfm_val (bval_to_fval fns v)).
      app - fs_wfm_val_to_result in Hwfm_v.
      (* #7.2 Remember Values: remember *)
      rem - v' vl' exc' as Heq_v Heq_vl Heq_exc:
        (bval_to_fval fns v)
        (map (bval_to_fval fns) vl)
        (bexc_to_fexc fns exc).
      (* #8.2 Pose Ident Theorem: pose + clear *)
      pse - list_biforall_values_nth_le as Hbiforall:
        fns env e1 el1 (e2 :: el2) v vl v' vl'
        Heq_v Heq_vl Hlength_vl Hwfm_vvl Hfs_nth;
        clr - Heq_vl Hlength_vl Hwfm_vvl.
      pose proof framestack_ident_partial
        IValues
        (map (bexp_to_fexp fns)
          (map (subst_env (measure_list measure_exp el1 + measure_env env) env)
            el1))
        (bexp_to_fexp_subst fns env e2)
        (map (bexp_to_fexp fns)
          (map (subst_env (measure_list measure_exp el2 + measure_env env) env)
            el2))
        vl' v' [] [] Hbiforall
        as Hfs_vl;
        clr - Hbiforall.
      (* #9.2 Specialize Inductive Hypothesis: assert/specialize/simpl/rewrite
        + clear *)
      ass - as Hnlt: sli >
        (0 < Datatypes.length (e1 :: el1)).
      ass - as Heq_nth: smp; rwr - Heq_v >
        (bres_to_fres fns (inl [nth 0 (v :: vl) ErrorValue]) = RValSeq [v']);
        clr - Heq_v.
      spc - Hfs_nth as Hfs_v: 0 Hnlt fns (RValSeq [v']) Hwfm_v Heq_nth;
        clr - v vl.
      smp - Hfs_v.
      spc - Hfs_exc: fns exc' Hwfm_exc.
      cwl - Heq_exc in Hfs_exc; clr - exc.
      spe_rfl - Hfs_exc.
      rwr - nth_middle in Hfs_exc.
      (* #10.2 Destruct Inductive Hypothesis: destruct/simpl/rewrite + clear *)
      des - Hfs_v as [kv [_ Hstep_v]].
      des - Hfs_vl as [kvl Hstep_vl].
      des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
      (* #11.2 FrameStack Proof: scope/step + clear *)
      framestack_scope - Hscope_exc.
      framestack_step - Hstep_v / kv e1.
      framestack_step - Hstep_vl / kvl el1.
      framestack_step - Hstep_exc / kexc e2.
      framestack_step.
  Admitted.



End Equivalence_Lists1.









Section Equivalence_Lists2.



  (* Solved *)
  Theorem eq_bs_to_fs_nil_map :
    forall fns env kvl vvl mkvl mvvl,
        (Datatypes.length ([] : list Expression) = Datatypes.length kvl)
    ->  (Datatypes.length ([] : list Expression) = Datatypes.length vvl)
    ->  (make_value_map kvl vvl = (mkvl, mvvl))
    ->  ⟨ [], bexp_to_fexp_subst fns env (EMap []) ⟩
          -->* bres_to_fres fns (inl [VMap (combine mkvl mvvl)]).
  Proof.
    (* #1 Rewrite Value List: inro/simpl/symmetry/apply/inversion
      + subst/clear *)
    itr - fns env  kvl vvl mkvl mvvl Hlength_kvl Hlength_vvl Hmake_vl.
    smp - Hlength_kvl Hlength_vvl.
    sym - Hlength_kvl Hlength_vvl.
    app - length_zero_iff_nil as Hempty_kvl in Hlength_kvl.
    app - length_zero_iff_nil as Hempty_vvl in Hlength_vvl.
    ivc - Hempty_kvl.
    ivc - Hmake_vl.
    (* #2 FrameStack Proof: scope/step *)
    framestack_scope.
    framestack_step.
  Qed.



  (* Admitted: make_value_map*)
  Theorem eq_bs_to_fs_suc_map :
    forall fns r env el vl kvl vvl mkvl mvvl
           (mel := make_map_exps el : list Expression)
           (mvl := make_map_vals kvl vvl : list Value),
        (Datatypes.length el = Datatypes.length kvl)
    ->  (Datatypes.length el = Datatypes.length vvl)
    ->  (make_value_map kvl vvl = (mkvl, mvvl))
    ->  (combine mkvl mvvl = vl)
    ->  (forall i,
            i < Datatypes.length mel
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i mvl ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env (nth i mel ErrorExp) ⟩ -->* r))
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inl [VMap vl]) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EMap el) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion/subst + subst/clear *)
    itr - fns r env el vl kvl vvl mkvl mvvl mel mvl
          Hlength_kvl Hlength_vvl Hmake_vl Hcombine_vl Hfs_nth Hwfm Hresult.
    ivc - Hresult.
    subst mel mvl.
    (* #2 Destruct Expression List: destruct + pose *)
    des - el as [| [ke ve] el]:
      pse - eq_bs_to_fs_nil_map:  fns env kvl vvl mkvl mvvl
                                  Hlength_kvl Hlength_vvl Hmake_vl.
    (* #3 Fix Result: destruct + simpl/congruence *)
    des - kvl as [| kv kvl]: smp *; con.
    des - vvl as [| vv vvl]: smp *; con.
    ass - as Hlength: rwr - Hlength_kvl in Hlength_vvl; ivs - Hlength_vvl >
      (Datatypes.length kvl = Datatypes.length vvl).
    pse - make_value_map_cons as Hnot_empty:
      kv kvl vv vvl mkvl mvvl Hlength Hmake_vl.
    des - Hnot_empty as [Hnot_empty_mkvl Hnot_empty_mvvl].
    des - mkvl as [| mkv mkvl]: con.
    des - mvvl as [| mvv mvvl]: con.
    clr - Hnot_empty_mkvl Hnot_empty_mvvl.
    (* #4 Measure Reduction: unfold/simpl/rewrite *)
    ufl - bexp_to_fexp_subst measure_env_exp.
    smp.
    rwr - mred_e1e2el_e1
          mred_e1e2el_e2
          mred_e1e2el_el.
    (* #5 Well Formed Map: destruct/simpl/assert/apply *)
    des - Hwfm as [[Hmake_vvl [[Hwfm_kv Hwfm_vv] Hwfm]] _].
    simpl map in Hmake_vvl.
    smp - Hwfm_kv Hwfm_vv.
    ass - as Hwfm_vl: app - make_val_map_cons in Hmake_vvl >
      (map
        (prod_map (bval_to_fval fns) (bval_to_fval fns))
        (combine mkvl mvvl)
      =
      make_val_map
        (map
          (prod_map (bval_to_fval fns) (bval_to_fval fns))
          (combine mkvl mvvl)));
      clr - Hwfm.
    app - fs_wfm_val_to_result in Hwfm_kv.
    app - fs_wfm_val_to_result in Hwfm_vv.
    (* #6 Remember Values: remember *)
    rem - kv' vv' vl' as Heq_kv Heq_vv Heq_vl:
      (bval_to_fval fns mkv)
      (bval_to_fval fns mvv)
      (map (λ '(x, y), (bval_to_fval fns x, bval_to_fval fns y))
        (combine mkvl mvvl)).
    (* #7 Pose Ident Theorem: pose + clear *)
    pse - create_result_vmap as Hcreate: kv' vv' vl'.
    (* rwl - Hmake_vvl in Hcreate. *)
    (*
    pse - list_biforall_vtuple_nth_eq as Hbiforall:
      fns env e el v vl v' vl'
      Heq_v Heq_vl Hlength Hwfm Hfs_nth;
      clr - Hlength Hwfm Heq_vl.
    pose proof framestack_ident
      ITuple
      (map (bexp_to_fexp fns)
        (map (subst_env (measure_list measure_exp el + measure_env env) env)
          el))
      (RValSeq [Syntax.VTuple (v' :: vl')])
      vl' v' [] [] []
      Hcreate Hbiforall
      as Hfs_vl;
      clr - Hcreate Hbiforall.
    (* #8 Specialize Inductive Hypothesis: assert/specialize/simpl + clear *)
    ass - as Hnlt: sli >
      (0 < Datatypes.length (e :: el)).
    ass - as Heq_nth: smp; rwr - Heq_v >
      (bres_to_fres fns (inl [nth 0 (v :: vl) ErrorValue]) = RValSeq [v']);
      clr - Heq_v.
    spc - Hfs_nth as Hfs_v: 0 Hnlt fns (RValSeq [v']) Hwfm_v Heq_nth;
      clr - v vl.
    smp - Hfs_v.
    (* #9 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v as [kv [_ Hstep_v]].
    des - Hfs_vl as [kvl Hstep_vl].
    (* #10 FrameStack Proof: scope/step + clear *)
    eei; spl.
    1: admit. (*Needs to modify main proof, it need is_result r predicate *)
    framestack_step - Hstep_v / kv e.
    framestack_step - Hstep_vl.
    *)
  Admitted.



(*
primop_eval_is_result
*)

(*
Lemma primop_create :
  forall fns env fname vl result eff1 eff2 eff3 r,
      primop_eval fname vl (last eff1 eff2) = (result, eff3)
  ->  create_result (IPrimOp fname) (bvs_to_fvs fns vl) = Some (RValSeq r, (beff_to_feff fns eff3)). 
*)

(* need some like:
  create_result (IPrimOp fname) vl = Some (e, eff)

maybe:
primop_eval fname vl (last eff1 eff2) = (result, eff3)
-> create_result (IPrimOp fname) vl = Some (e, eff3)
*)

Search "primop".

  (* Admitted: Some = None -> need create_result congruence *)
  Lemma primop_result :
    forall fns env fname,
      ⟨ [], bexp_to_fexp_subst fns env (EPrimOp fname []) ⟩ -->*
        bres_to_fres fns (inr (undef (VLit (Atom fname)))).
  Proof.
    itr.
    framestack_scope.
    framestack_step.
    ens.
    {
      eapply eval_cool_params_0.
      1: con.
      smp.
      ufl - Auxiliaries.primop_eval.
      des > (Auxiliaries.convert_primop_to_code fname).
      4-7: adm.
      1-2: des > (Auxiliaries.eval_primop_error fname []).
      2, 4: adm.
      3: trv.
      1-2: adm.
    }
    framestack_step.
  Admitted.



  (* Dependently Solved: primop_result *)
  Theorem eq_bs_to_fs_nil_primop :
    forall fns env vl fname result eff1 eff2 eff3,
        (Datatypes.length ([] : list Expression) = Datatypes.length vl)
    ->  (Datatypes.length ([] : list Expression) = Datatypes.length eff1)
    ->  primop_eval fname vl (last eff1 eff2) = (result, eff3)
    ->  ⟨ [], bexp_to_fexp_subst fns env (EPrimOp fname []) ⟩
          -->* bres_to_fres fns result.
  Proof.
    (* #1 Rewrite Value List: inro/simpl/symmetry/apply/inversion
      + subst/clear *)
    itr - fns env vl fname result eff1 eff2 eff3
          Hlength_vl Hlength_eff1 Hprimop.
    smp - Hlength_vl Hlength_eff1.
    sym - Hlength_vl Hlength_eff1.
    app - length_zero_iff_nil as Hempty_vl in Hlength_vl.
    app - length_zero_iff_nil as Hempty_eff1 in Hlength_eff1.
    ivc - Hempty_vl.
    smp - Hprimop.
    ufl - primop_eval in Hprimop.
    des > (convert_primop_to_code fname); ivc - Hprimop.
    1-39: bse - primop_result: fns env fname.
  Qed.



  (* Admitted: create_result *)
  Theorem eq_bs_to_fs_suc_primop :
    forall fns r env el vl fname result eff1 eff2 eff3,
        (Datatypes.length el = Datatypes.length vl)
    ->  (Datatypes.length el = Datatypes.length eff1)
    ->  primop_eval fname vl (last eff1 eff2) = (result, eff3)
    ->  (forall i,
            i < Datatypes.length el
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i vl ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env (nth i el ErrorExp) ⟩ -->* r))
    ->  fs_wfm_result r
    ->  bres_to_fres fns result = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EPrimOp fname el) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env el vl fname result eff1 eff2 eff3
          Hlength_vl Hlength_eff1 Hprimop Hfs_nth Hwfm Hresult.
    ivc - Hresult.
    (* #2 Destruct Expression List: destruct + pose *)
    des - el as [|e el]:
      pse - eq_bs_to_fs_nil_primop: fns env vl fname result eff1 eff2 eff3
                                    Hlength_vl Hlength_eff1 Hprimop.
    (* #3 Fix Result: destruct + simpl/congruence *)
    des - vl: smp *; con.
    (* #4 Measure Reduction: unfold/simpl/rewrite *)
    ufl - bexp_to_fexp_subst measure_env_exp.
    smp.
    rwr - mred_eel_e
          mred_eel_el.
  Admitted.



End Equivalence_Lists2.









Section Equivalence_App.

(*
env : Environment
modules : list ErlModule
own_module : string
exp, body : Expression
res : ValueSequence + Exception
var_list : list Var
ref : Environment
ext : list (nat * FunctionIdentifier * FunctionExpression)
n : nat
eff1, eff2, eff3 : SideEffectList
eff : list SideEffectList
ids : list nat
id, id', id'' : nat
f : option FunctionIdentifier
H : Datatypes.length params = Datatypes.length vals
bs1 : | env, modules, own_module, id, exp, eff1 | -e> | id',
      inl [VClos ref ext n var_list body f], eff2 |
H0 : Datatypes.length var_list = Datatypes.length vals
H1 : Datatypes.length params = Datatypes.length eff
H2 : Datatypes.length params = Datatypes.length ids
H3 : ∀ i : nat,
       i < Datatypes.length params
       → | env, modules, own_module, nth_def ids id' 0 i, nth i params ErrorExp,
         nth_def eff eff2 [] i | -e> | nth_def ids id' 0 (S i), inl [nth i vals ErrorValue],
         nth_def eff eff2 [] (S i) |
H4 : ∀ i : nat,
       i < Datatypes.length params
       → ∀ (fns : name_sub) (r : Redex),
           fs_wfm_result r
           → bres_to_fres fns (inl [nth i vals ErrorValue]) = r
             → ⟨ [], bexp_to_fexp_subst fns env (nth i params ErrorExp) ⟩ -->* r
bs2 : | append_vars_to_env var_list vals (get_env ref ext), modules, own_module,
      last ids id', body, last eff eff2 | -e> | id'', res, eff3 |
IHbs1 : ∀ (fns : name_sub) (r : Redex),
          fs_wfm_result r
          → bres_to_fres fns (inl [VClos ref ext n var_list body f]) = r
            → ⟨ [], bexp_to_fexp_subst fns env exp ⟩ -->* r
IHbs2 : ∀ (fns : name_sub) (r : Redex),
          fs_wfm_result r
          → bres_to_fres fns res = r
            → ⟨ [],
              bexp_to_fexp_subst fns (append_vars_to_env var_list vals (get_env ref ext))
                body ⟩ -->* r
fns : name_sub
r : Redex
Hwfm : fs_wfm_result r
Hresult : bres_to_fres fns res = r
______________________________________(1/1)
⟨ [], bexp_to_fexp_subst fns env (EApp exp params) ⟩ -->* r

*)



(*
Hlength : Datatypes.length [] = Datatypes.length vl
Hfs_nth : ∀ i : nat,
            i < Datatypes.length []
            → ∀ (fns : name_sub) (r : Redex),
                fs_wfm_result r
                → bres_to_fres fns (inl [nth i vl ErrorValue]) = r
                  → ⟨ [], bexp_to_fexp_subst fns env (nth i [] ErrorExp) ⟩ -->* r
Hfs_exp : ∀ (fns : name_sub) (r : Redex),
            fs_wfm_result r
            → bres_to_fres fns (inl [VClos ref ext n vars body fid]) = r
              → ⟨ [], bexp_to_fexp_subst fns env exp ⟩ -->* r
Hfs_el : ∀ (fns : name_sub) (r : Redex),
           fs_wfm_result r
           → bres_to_fres fns result = r
             → ⟨ [],
               bexp_to_fexp_subst fns (append_vars_to_env vars vl (get_env ref ext)) exp
               ⟩ -->* r
Hwfm : fs_wfm_result (bres_to_fres fns result)
______________________________________(1/2)
⟨ [], bexp_to_fexp_subst fns env (ETuple []) ⟩ -->* bres_to_fres fns result
*)

Lemma append_vars_to_env_empty : 
  forall vars env,
    append_vars_to_env vars [] env
  = match vars with
   | [] => env
   | v :: vs => []
   end.
Proof.
  itr.
  ass - as Hunfold: des - vars; ufl - append_vars_to_env >
  (append_vars_to_env vars [] env =
  match vars with
   | [] => match ([] : list Value) with
           | [] => env
           | _ :: _ => []
           end
   | v :: vs =>
       match [] with
       | [] => []
       | e :: es => append_vars_to_env vs es (insert_value env (inl v) e)
       end
   end).
   bwr - Hunfold.
Qed.



(*
⟨ [],
   (bexp_to_fexp_subst (add_vars vars fns) (rem_vars vars (get_env ref ext)) body).[
   list_subst (bvs_to_fvs fns []) idsubst] ⟩ -[ kbody ]-> ⟨ [], 
   bres_to_fres fns result ⟩
*)



Theorem bexp_to_fexp_subst_get_env :
  forall fns env vars ext e,
      (bexp_to_fexp_subst
          (add_vars vars fns)
          (rem_vars vars (get_env env ext)) e)
          .[list_subst (bvs_to_fvs fns []) idsubst]
  =  (bexp_to_fexp_subst
        (add_names (map (inr ∘ snd ∘ fst) ext ++ map inl vars) fns)
        (rem_vars vars env) e).
Proof.
  itr.
  ind + ind_exp - e.
  2: { (*ENil*)
    bbn.
  }
  2: { (*ELit*)
    bbn.
  }
  5: { (*ECons*)
    rfl - bexp_to_fexp_subst.
    sbn *.
    do 2 rwr - mred_e1e2_e1
          mred_e1e2_e2.
    ufl - bexp_to_fexp_subst measure_env_exp in *.
    bwr - IHe1 IHe2.
  }
  4: { (*EFUN*)
    rfl - bexp_to_fexp_subst.
    sbn *.
    ufl - add_vars.
    admit.
    (* rwr - IHe. *)
  }
Admitted.

(*
Theorem bexp_to_fexp_subst_get_env :
  forall fns env vars ext e k result,
      ⟨ [], (bexp_to_fexp_subst
          (add_vars vars fns)
          (rem_vars vars (get_env env ext)) e)
          .[list_subst (bvs_to_fvs fns []) idsubst] ⟩
        -[ k ]->
      ⟨ [], bres_to_fres fns result ⟩
  =  ⟨ [], (bexp_to_fexp_subst
        (add_names (map (inr ∘ snd ∘ fst) ext ++ map inl vars) fns)
        (rem_vars vars env) e) ⟩
        -[ k ]->
      ⟨ [], bres_to_fres fns result ⟩.
Proof.
  itr.
  ind + ind_exp - e.
  2: { (*ENil*)
    bbn.
  }
  2: { (*ELit*)
    bbn.
  }
  5: { (*ECons*)
    rfl - bexp_to_fexp_subst.
    sbn.
    do 2 rwr - mred_e1e2_e1
          mred_e1e2_e2.
    ufl - bexp_to_fexp_subst measure_env_exp in *.
    rwr - IHe1.
    ivc - Hfs.
    * framestack_step.
  }
Admitted.
*)


  (* Solved *)
  Theorem eq_bs_to_fs_nil_app :
    forall fns env exp vl result ref ext n vars body fid,
        (Datatypes.length ([] : list Expression) = Datatypes.length vl)
    ->  (forall i,
            i < Datatypes.length ([] : list Expression)
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i vl ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env (nth i [] ErrorExp) ⟩ -->* r))
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inl [VClos ref ext n vars body fid]) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env exp ⟩ -->* r)
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns result = r
        ->  ⟨ [], bexp_to_fexp_subst fns
              (append_vars_to_env vars vl (get_env ref ext)) body ⟩ -->* r)
    ->  ⟨ [], bexp_to_fexp_subst fns env (EApp exp []) ⟩
          -->* bres_to_fres fns result.
  Proof.
    (* #1 Rewrite Value List: inro/simpl/symmetry/apply/inversion
      + subst/clear *)
    itr - fns env exp vl result ref ext n vars body fid
          Hlength_vl Hfs_nth Hfs_exp Hfs_body.
    smp - Hlength_vl.
    sym - Hlength_vl.
    app - length_zero_iff_nil as Hempty_vl in Hlength_vl.
    ivc - Hempty_vl.
    (* #2 Measure Reduction: unfold/simpl/rewrite *)
    ufl - bexp_to_fexp_subst measure_env_exp.
    smp.
    unfold measure_list.
    smp.
    rwr - Nat.add_0_r.
    (* rwr - append_vars_to_env_empty in Hfs_body. *)
    (* #3 Well Formed Map: assert/apply *)
    ass - as Hwfm_vclos: adm >
      (fs_wfm_result (bres_to_fres fns (inl [VClos ref ext n vars body fid]))).
    ass - as Hwfm_vl: adm >
      (fs_wfm_result (bres_to_fres fns result)).
    (* #4 Specialize Inductive Hypothesis: specialize + clear *)
    spc - Hfs_exp: fns
      (bres_to_fres fns (inl [VClos ref ext n vars body fid])) Hwfm_vclos.
    spc - Hfs_body: fns (bres_to_fres fns result) Hwfm_vl.
    spe_rfl - Hfs_exp Hfs_body.
    (* #5 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_exp as [kexp [_ Hstep_exp]].
    des - Hfs_body as [kbody [Hscope_body Hstep_body]].
    (* #6 Rewrite Add Vars: rewrite/unfold *)
    rwr - bexp_to_fexp_add_vars in Hstep_body.
    smp - Hstep_body.
    simpl idsubst in Hstep_body.
    ufl - bexp_to_fexp_subst measure_env_exp in *.
    (* #2 FrameStack Proof: scope/step *)
    des - fid. des - ext.
    framestack_scope - Hscope_body.
    framestack_step - Hstep_exp / kexp.
    ufl - add_vars measure_env_exp in Hstep_body.
    ufl - measure_env_exp.
    (*
    (bexp_to_fexp (add_names (map inl vars) fns)
      (subst_env (measure_exp body + measure_env
          (rem_vars vars (get_env ref ext)))
         (rem_vars vars (get_env ref ext)) body))
    bexp_to_fexp (add_names (map (inr ∘ snd ∘ fst) ext ++ map inl vars) fns)
      (subst_env (measure_exp body + measure_env
          (rem_vars vars ref))
        (rem_vars vars ref) body))
    *)
    admit.
  Admitted.


Print get_env.
(*get_env_base env env ext ext*)
Print get_env_base.

Lemma empty_ext :
  forall env,
    get_env env [] = env.
Proof.
  itr.
  ufl - get_env.
  bmp.
Qed.
(*
match ext with
| [] => env
| (id, f1, (pl, b)) :: xs =>
    get_env_base (insert_value env (inr f1) (VClos def defext id pl b None)) def xs defext
end
*)

(* get_env instead of rem_fid rem_vars ?*)
(* Probably causes infinite loop*)
(*
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
*)



  (* Solved: only VALSCOPE asserted *)
  Theorem eq_bs_to_fs_suc_app :
    forall fns r env exp el vl result ref ext n vars body fid,
        (Datatypes.length el = Datatypes.length vl)
    ->  (forall i,
            i < Datatypes.length el
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i vl ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env (nth i el ErrorExp) ⟩ -->* r))
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inl [VClos ref ext n vars body fid]) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env exp ⟩ -->* r)
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns result = r
        ->  ⟨ [], bexp_to_fexp_subst fns
              (append_vars_to_env vars vl (get_env ref ext)) body ⟩ -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns result = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EApp exp el) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env exp el vl result ref ext n vars body fid
          Hlength Hfs_nth Hfs_exp Hfs_body Hwfm Hresult.
    ivc - Hresult.
    (* #2 Destruct Expression List: destruct + pose *)
    des - el as [|e el].
    
    1: adm.
    eei; spl.
    1: adm.
    
  Admitted.

(*

    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env el vl Hlength Hfs_nth Hwfm Hresult.
    ivc - Hresult.
    (* #2 Destruct Expression List: destruct + pose *)
    des - el as [|e el]: pse - eq_bs_to_fs_nil_tuple: fns env vl Hlength.
    (* #3 Fix Result: destruct + simpl/congruence *)
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
    rem - v' vl' as Heq_v Heq_vl:
      (bval_to_fval fns v)
      (map (bval_to_fval fns) vl).
    (* #7 Pose Ident Theorem: pose + clear *)
    pse - create_result_vtuple as Hcreate: v' vl'.
    pse - list_biforall_vtuple_nth_eq as Hbiforall:
      fns env e el v vl v' vl'
      Heq_v Heq_vl Hlength Hwfm Hfs_nth;
      clr - Hlength Hwfm Heq_vl.
    pose proof framestack_ident
      ITuple
      (map (bexp_to_fexp fns)
        (map (subst_env (measure_list measure_exp el + measure_env env) env)
          el))
      (RValSeq [Syntax.VTuple (v' :: vl')])
      vl' v' [] [] []
      Hcreate Hbiforall
      as Hfs_vl;
      clr - Hcreate Hbiforall.
    (* #8 Specialize Inductive Hypothesis: assert/specialize/simpl + clear *)
    ass - as Hnlt: sli >
      (0 < Datatypes.length (e :: el)).
    ass - as Heq_nth: smp; rwr - Heq_v >
      (bres_to_fres fns (inl [nth 0 (v :: vl) ErrorValue]) = RValSeq [v']);
      clr - Heq_v.
    spc - Hfs_nth as Hfs_v: 0 Hnlt fns (RValSeq [v']) Hwfm_v Heq_nth;
      clr - v vl.
    smp - Hfs_v.
    (* #9 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v as [kv [_ Hstep_v]].
    des - Hfs_vl as [kvl Hstep_vl].
    (* #10 FrameStack Proof: scope/step + clear *)
    eei; spl.
    1: admit. (*Needs to modify main proof, it need is_result r predicate *)
    framestack_step - Hstep_v / kv e.
    framestack_step - Hstep_vl.
*)


  (* Solved *) (* Almost same as ex2_cons *)
  Theorem eq_bs_to_fs_ex1_app :
    forall fns r env exp el exc,
        (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inr exc) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env exp ⟩ -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inr exc) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EApp exp el) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env exp el exc Hfs_exc Hwfm_exc Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn *.
    rwr - mred_expel_exp
          mred_expel_el.
    (* #3 Well Formed Map: unfold *)
    ufl - bres_to_fres in Hwfm_exc.
    (* #4 Remember Values: Remember Values *)
    rem - exc' as Heq_exc:
      (bexc_to_fexc fns exc).
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite + clear *)
    spc - Hfs_exc: fns (RExc exc') Hwfm_exc.
    cwl - Heq_exc in *; clr - exc.
    spe_rfl - Hfs_exc.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
    (* #7 FrameStack Proof: scope/step + clear *)
    framestack_scope - Hscope_exc.
    framestack_step - Hstep_exc / kexc exp.
    framestack_step.
  Qed.



End Equivalence_App.













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
    (* #3 Atoms #2: (Var, FunId) {ALMOST} *)
    3:  bse - eq_bs_to_fs_suc_var:    fns r env s res
                                      H Hwfm Hresult.
    3:  bse - eq_bs_to_fs_su1_funid:  fns r env fid res
                                      H Hwfm Hresult.
    3:  bse - eq_bs_to_fs_su2_funid:  fns r env fid id func
                                      varl_func body_func own_module modules
                                      H1 H2 H0 H Hwfm Hresult.
    (* #4 Closures: (Fun, LetRec) {DIFFERENT} *)
    3:  bse - eq_bs_to_fs_suc_fun:    fns r env e vl id
                                      Hresult.
    12: bse - eq_bs_to_fs_suc_letrec: fns r env e l res id
                                      IHbs Hwfm Hresult.
    (* #5 Doubles #1: [e1;e2] (Cons, Seq) {SIMILIAR}*)
    4:  bse - eq_bs_to_fs_suc_cons:   fns r env hd tl tlv hdv
                                      IHbs1 IHbs2 Hwfm Hresult.
    13: bse - eq_bs_to_fs_ex1_cons:   fns r env hd tl vtl ex
                                      IHbs1 IHbs2 Hwfm Hresult.
    12: bse - eq_bs_to_fs_ex2_cons:   fns r env hd tl ex
                                      IHbs Hwfm Hresult.
    10: bse - eq_bs_to_fs_suc_seq:    fns r env e1 e2 v1 v2
                                      IHbs1 IHbs2 Hwfm Hresult.
    27: bse - eq_bs_to_fs_exc_seq:    fns r env e1 e2 ex
                                      IHbs Hwfm Hresult.
    (* #6 Doubles #2: [e1;e2] (Let, Try) {SIMILIAR} *)
    9: bse - eq_bs_to_fs_suc_let:    fns r env e1 e2 vals res l
                                      H IHbs1 IHbs2 Hwfm Hresult.
    25: bse - eq_bs_to_fs_exc_let:    fns r env e1 e2 ex vl
                                      IHbs Hwfm Hresult.
    11: bse - eq_bs_to_fs_suc_try:    fns r env e1 e2 e3 vals res vl1 vl2
                                      H IHbs1 IHbs2 Hwfm Hresult.
    11: bse - eq_bs_to_fs_exc_try:    fns r env e1 e2 e3 ex res vl1 vl2
                                      IHbs1 IHbs2 Hwfm Hresult.
    (* #7 Lists #1: [el] (Tuple, Values) {ALMOST} *)
    3:  bse - eq_bs_to_fs_suc_tuple:   fns r env exps vals
                                       H H3 Hwfm Hresult.
    9: bse - eq_bs_to_fs_exc_tuple:   fns r env exps vals ex i
                                       H H0 H4 IHbs Hwfm Hresult.
    1: bse - eq_bs_to_fs_suc_values:   fns r env exps vals
                                       H H3 Hwfm Hresult.
    1: bse - eq_bs_to_fs_exc_values:   fns r env exps vals ex i
                                       H H0 H4 IHbs Hwfm Hresult.
    (* #6 Lists #2: [el] (Map, PrimOp) {ALMOST} *)
    6:  { 
      (* pse - eq_bs_to_fs_suc_map: fns r env l lv kvals vvals kvals' vvals' H0.
          smp - H9. 
          spe - *) adm. }
    18: { adm. }
    4: bse - eq_bs_to_fs_suc_primop:  fns r env params vals fname res
                                      eff eff1 eff2
                                      H H0 H4 H3 Hwfm Hresult.
    12: { adm. }
    (* #7 Applications: [e;el] (App) *)
    4:  { adm. }
    11: bse - eq_bs_to_fs_ex1_app: fns r env exp params ex IHbs Hwfm Hresult.
    11: { adm. }
    11: { adm. }
    11: { adm. }
    (* #8 Calls: [e1;e2;el] (Call) *)
    2:  { adm. }
    2:  { adm. }
    4:  { adm. }
    4:  { adm. }
    4:  { adm. }
    4:  { adm. }
    4:  { adm. }
    (* #9 Cases: [e;pattern] (Case) *)
    1:  { adm. }
    1:  { adm. }
    1:  { adm. }
  Admitted.

(* Admitted:
* FunId 2: modulo
* Fun & Letrec
* PrimOp
*)



End Equivalence_Main.