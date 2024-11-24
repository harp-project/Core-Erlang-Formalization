From CoreErlang.Eq.BsFs Require Export B23BiForallLemmas.

Import BigStep.

(* STRUCTURE:
* Atoms
  - value_reduction_vnil
  - value_reduction_vlit
* Cons
  - value_reduction_vcons
* Tuple
  - value_reduction_vtuple_nil
  - value_reduction_vtuple
* Map
  - value_reduction_vmap_nil
  - value_reduction_vmap
* Clos
  - value_reduction_vclos
* Main
  - value_reduction
*)












Section Atoms.



  Theorem value_reduction_vnil :
    forall fns v',
        v' = bval_to_fval fns VNil
    ->  ⟨ [], bexp_to_fexp fns
                (bval_to_bexp
                  (subst_env (measure_val VNil))
                  VNil) ⟩
          -->* RValSeq [v'].
  Proof.
    (* #1 Inversion Result: intro/inversion *)
    itr - fns v' Hresult.
    ivc - Hresult.
    (* #2 Simplify: simpl/clear *)
    smp; clr - fns.
    (* #3 FrameStack Proof: scope/step *)
    scope.
    step.
  Qed.



  Theorem value_reduction_vlit :
    forall fns v' l,
        v' = bval_to_fval fns (VLit l)
    ->  ⟨ [], bexp_to_fexp fns
                (bval_to_bexp
                  (subst_env (measure_val (VLit l)))
                  (VLit l)) ⟩
          -->* RValSeq [v'].
  Proof.
    (* #1 Inversion Result: intro/inversion *)
    itr - fns v' l Hresult.
    ivc - Hresult.
    (* #2 Simplify: simpl/clear *)
    smp; clr - fns.
    (* #3 FrameStack Proof: scope/step *)
    scope.
    step.
  Qed.



End Atoms.









Section Cons.



  Theorem value_reduction_vcons :
    forall fns v' v1 v2,
        (forall v,
            Forall fs_wfm_val [v]
        ->  v = bval_to_fval fns v1
        ->  ⟨ [], bexp_to_fexp fns
                    (bval_to_bexp
                      (subst_env (measure_val v1))
                      v1) ⟩
              -->* RValSeq [v])
    ->  (forall v,
            Forall fs_wfm_val [v]
        ->  v = bval_to_fval fns v2
        ->  ⟨ [], bexp_to_fexp fns
                    (bval_to_bexp
                      (subst_env (measure_val v2))
                      v2) ⟩
              -->* RValSeq [v])
    ->  Forall fs_wfm_val [v']
    ->  v' = bval_to_fval fns (VCons v1 v2)
    ->  ⟨ [], bexp_to_fexp fns
                (bval_to_bexp
                  (subst_env (measure_val (VCons v1 v2)))
                   (VCons v1 v2)) ⟩
          -->* RValSeq [v'].
  Proof.
    (* #1 Inversion Result: intro/inversion *)
    itr - fns v' v1 v2 Hfs_v1 Hfs_v2 Hwfm Hresult.
    ivc - Hresult.
    (* #2 Simplify: refold *)
    rfl + bval_to_fval
          bval_to_bexp
          bexp_to_fexp in Hwfm.
    (* #3 Measure Reduction: rewrite *)
    rwr - mred_vcons_v1
          mred_vcons_v2.
    (* #4 Well Formed Map: apply/destruct *)
    app - fs_wfm_vcons in Hwfm.
    des - Hwfm as [Hwfm_v1 Hwfm_v2].
    (* #5 Remember Values: remember/clear *)
    rem - v1' v2' as Heq_v1 Heq_v2:
      (bval_to_fval fns v1)
      (bval_to_fval fns v2);
      clr - Heq_v1 Heq_v2.
    (* #7 Specialize Inductive Hypothesis: specialize *)
    spc - Hfs_v1: v1' Hwfm_v1.
    spc - Hfs_v2: v2' Hwfm_v2.
    spe_rfl - Hfs_v1 Hfs_v2.
    (* #8 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v1 as [kv1 [Hscope_v1 Hstep_v1]].
    des - Hfs_v2 as [kv2 [Hscope_v2 Hstep_v2]].
    (* #9 FrameStack Proof: scope/step *)
    scope - v1' v2' Hscope_v1 Hscope_v2.
    step - Hstep_v2 / kv2 v2.
    step - Hstep_v1 / kv1 v1 fns.
    step.
  Qed.



End Cons.









Section Tuple.



  Theorem value_reduction_vtuple_nil :
    forall fns,
      ⟨ [], bexp_to_fexp fns
              (bval_to_bexp
                (subst_env (measure_val (VTuple [])))
                 (VTuple [])) ⟩
        -->* RValSeq [bval_to_fval fns (VTuple [])].
  Proof.
    (* #1 FrameStack Proof: scope/step *)
    scope.
    step.
  Qed.



  Theorem value_reduction_vtuple :
    forall fns v' vl,
        (Forall (fun v => forall v'',
            Forall fs_wfm_val [v'']
        ->  v'' = bval_to_fval fns v
        ->  ⟨ [], bexp_to_fexp fns
                    (bval_to_bexp
                      (subst_env (measure_val v))
                      v) ⟩
              -->* RValSeq [v''])
          vl)
    ->  Forall fs_wfm_val [v']
    ->  v' = bval_to_fval fns (VTuple vl)
    ->  ⟨ [], bexp_to_fexp fns
                (bval_to_bexp
                  (subst_env (measure_val (VTuple vl)))
                   (VTuple vl)) ⟩
          -->* RValSeq [v'].
  Proof.
    (* #1 Inversion Result: intro/inversion *)
    itr - fns v' vl HForall Hwfm Hresult.
    ivc - Hresult.
    (* #2 Induction on Value List: induction + pose *)
    ind - vl as [| v vl Hfs_vl]:
      pse - value_reduction_vtuple_nil: fns.
    (* #3 Inversion Forall: inversion *)
    ivc - HForall as Hfs_v HForall: H1 H2.
    (* #4 Simplify: refold/remember/simpl *)
    rfl - bval_to_fval
          bval_to_bexp
          bexp_to_fexp.
    rfl - bval_to_fval in Hwfm Hfs_vl.
    rem_sbt_smp: (VTuple (v :: vl)).
    smp - Hwfm.
    (* #5 Measure Reduction: rewrite *)
    rwr - mred_vtuple_v
          mred_vtuple_vl.
    (* #6 Well Formed Map: apply/destruct *)
    app - fs_wfm_vtuple in Hwfm.
    des - Hwfm as [Hwfm_v Hwfm_vl].
    (* #7 Remember Values: remember/clear *)
    rem - v' vl' as Heq_v Heq_vl:
      (bval_to_fval fns v)
      (map (bval_to_fval fns) vl);
      clr - Heq_v.
    (* #7 Specialize Inductive Hypothesis: specialize *)
    spc - Hfs_v: v' Hwfm_v.
    spc - Hfs_vl: HForall Hwfm_vl.
    spe_rfl - Hfs_v.
    (* #8 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v as [kv [Hscope_v Hstep_v]].
    des - Hfs_vl as [kvl [Hscope_vl Hstep_vl]].
      (* #7 Pose Ident Theorem: pose + clear *)
    pse - create_result_vtuple as Hcreate: v' vl'.
    psc - biforall_vtuple as Hlist: fns kvl vl vl' Heq_vl Hstep_vl.
    pose proof ident_result
      ITuple
      (map (bexp_to_fexp fns)
        (map (bval_to_bexp (subst_env (measure_val (VTuple vl)))) vl))
      (RValSeq [Syntax.VTuple (v' :: vl')])
      vl' v' [] [] []
      Hcreate Hlist
      as Hident_vl;
      clr - kvl Hcreate Hlist.
    (* #8 Destruct Ident Hypothesis: destruct *)
    des - Hident_vl as [kvl Hstep_vl].
    (* #9 FrameStack Proof: scope/step *)
    scope - v' vl' Hscope_v Hscope_vl.
    rem_sbt: v (VTuple vl).
    step - Hstep_v / kv v sbt1.
    step - Hstep_vl.
  Qed.



End Tuple.









Section Map.



  Theorem value_reduction_vmap_nil :
    forall fns,
      ⟨ [], bexp_to_fexp fns
              (bval_to_bexp
                (subst_env (measure_val (VMap [])))
                 (VMap [])) ⟩
        -->* RValSeq [bval_to_fval fns (VMap [])].
  Proof.
    (* #1 FrameStack Proof: scope/step *)
    scope.
    step.
  Qed.



  Theorem value_reduction_vmap :
    forall fns v' vl,
        (Forall (fun v =>
            (forall v'',
                Forall fs_wfm_val [v'']
            ->  v'' = bval_to_fval fns v.1
            ->  ⟨ [], bexp_to_fexp fns
                        (bval_to_bexp
                          (subst_env (measure_val v.1))
                          v.1) ⟩
                  -->* RValSeq [v''])
        /\  (forall v'',
                Forall fs_wfm_val [v'']
            ->  v'' = bval_to_fval fns v.2
            ->  ⟨ [], bexp_to_fexp fns
                        (bval_to_bexp
                          (subst_env (measure_val v.2))
                          v.2) ⟩
                  -->* RValSeq [v'']))
              vl)
    ->  Forall fs_wfm_val [v']
    ->  v' = bval_to_fval fns (VMap vl)
    ->  ⟨ [], bexp_to_fexp fns
                (bval_to_bexp
                  (subst_env (measure_val (VMap vl)))
                   (VMap vl)) ⟩
          -->* RValSeq [v'].
  Proof.
    (* #1 Inversion Result: intro/inversion *)
    itr - fns v' vl HForall Hwfm Hresult.
    ivc - Hresult.
    (* #2 Induction on Value List: induction + pose *)
    ind - vl as [| [v1 v2] vl Hfs_vl]:
      pse - value_reduction_vmap_nil: fns.
    (* #3 Inversion Forall: inversion/destruct *)
    ivc - HForall as Hfs_v HForall: H1 H2.
    des - Hfs_v as [Hfs_v1 Hfs_v2].
    (* #4 Simplify: refold/remember/simpl *)
    rfl - bval_to_fval
          bval_to_bexp
          bexp_to_fexp.
    rfl - bval_to_fval in Hwfm Hfs_vl.
    rem_sbt_smp: (VMap ((v1, v2) :: vl)).
    smp - Hwfm Hfs_v1 Hfs_v2.
    (* #5 Measure Reduction: rewrite *)
    rwr - mred_vmap_v1
          mred_vmap_v2
          mred_vmap_vll.
    (* #6 Well Formed Map: inversion/destruct/apply *)
    ivs - Hwfm as Hwfm_v1v2vl: H1 / H2.
    des - Hwfm_v1v2vl as [Heq_map _].
    app - fs_wfm_vmap in Hwfm.
    des - Hwfm as [Hwfm_v1 [Hwfm_v2 Hwfm_vl]].
    (* #7 Remember Values: remember/clear *)
    rem - v1' v2' vl' as Heq_v1 Heq_v2 Heq_vl:
      (bval_to_fval fns v1)
      (bval_to_fval fns v2)
      (map (prod_map (bval_to_fval fns) (bval_to_fval fns)) vl);
      clr - Heq_v1 Heq_v2.
    (* #7 Specialize Inductive Hypothesis: specialize *)
    spc - Hfs_v1: v1' Hwfm_v1.
    spc - Hfs_v2: v2' Hwfm_v2.
    spc - Hfs_vl: HForall Hwfm_vl.
    spe_rfl - Hfs_v1 Hfs_v2.
    (* #8 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v1 as [kv1 [Hscope_v1 Hstep_v1]].
    des - Hfs_v2 as [kv2 [Hscope_v2 Hstep_v2]].
    des - Hfs_vl as [kvl [Hscope_vl Hstep_vl]].
    (* #7 Pose Ident Theorem: pose/rewrite + clear *)
    pse - make_val_map_cons as Heq_map_vl: v1' v2' vl' Heq_map.
    pse - create_result_vmap as Hcreate: v1' v2' vl'.
    psc - biforall_vmap as Hlist: fns kvl vl vl' Heq_map_vl Heq_vl Hstep_vl.
    pose proof ident_result
      IMap
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
      (RValSeq [Syntax.VMap (make_val_map ((v1', v2') :: vl'))])
      (flatten_list vl') v2' [v1'] [] []
      Hcreate Hlist
      as Hident_vl;
      clr - kvl Hcreate Hlist.
    cwl - Heq_map in Hident_vl.
    (* #8 Destruct Ident Hypothesis: destruct *)
    des - Hident_vl as [kvl Hstep_vl].
    (* #9 FrameStack Proof: scope/step *)
    scope - v1' v2' vl' Hscope_v1 Hscope_v2 Hscope_vl.
    rem_sbt: v1 v2 (VMap vl).
    step - Hstep_v1 / kv1 v1 sbt1.
    step - Hstep_v2 / kv2 v2 sbt2.
    step - Hstep_vl.
  Qed.



End Map.








Section Clos.



  (* Admitted: Scopes & LetRec *)
  Theorem value_reduction_vclos :
    forall fns v' env ext id vars e fid,
        (Forall (fun v =>
            forall v'',
                Forall fs_wfm_val [v'']
            ->  v'' = bval_to_fval fns v.2
            ->  ⟨ [], bexp_to_fexp fns
                        (bval_to_bexp
                          (subst_env (measure_val v.2))
                          v.2) ⟩
                  -->* RValSeq [v''])
              env)
    ->  Forall fs_wfm_val [v']
    ->  v' = bval_to_fval fns (VClos env ext id vars e fid)
    ->  ⟨ [], bexp_to_fexp fns
                (bval_to_bexp
                  (subst_env (measure_val (VClos env ext id vars e fid)))
                   (VClos env ext id vars e fid)) ⟩
          -->* RValSeq [v'].
  Proof.
    (* #1 Inversion Result: intro/inversion *)
    itr - fns v' env ext id vars e fid HForall Hwfm Hresult.
    ivc - Hresult.
    (* #2 Simplify: refold/remember/simpl *)
    rfl - bval_to_fval
          bval_to_bexp.
    (* #3 Destruct Matching: destuct/refold *)
    des - ext; [idtac | des - fid].
    1: { (* EFun: ext = [] *)
      (* #4.1 Measure Reduction: simpl/rewrite *)
      smp.
      rwl - measure_env_eq.
      rwr - mred_eext_e_rem_vars.
      (* #5.1 FrameStack Proof: scope/step *)
      eei; spl.
      1: adm.
      step.
    }
    2: { (* EFun: fid = None *)
      (* #4.2 Measure Reduction: simpl/rewrite *)
      smp.
      rwl - measure_env_eq.
      rwr - mred_eext_e_rem_vars.
      (* #5.2 FrameStack Proof: scope/step *)
      eei; spl.
      1: adm.
      step.
    }
    1: { (* ELetRec *)
      (* #4.3 Simplify: refold/simpl/rewrite/rename/remember + clear *)
      rfl - bexp_to_fexp
            measure_val.
      ren - ext': ext.
      rem - ext as Hext:
        (p :: ext');
        clr - Hext.
      do 2 rwl - Nat.add_assoc.
      rwr - subst_env_step.
      rfl - bexp_to_fexp.
      (* #5.3 Measure Reduction: *)
      rfl - add_exp_ext_both.
      rwr - add_exp_ext_fids_smp.
      (* TODO: implement measure reduction for ext *)
      (* #5.3 FrameStack Proof: scope/step *)
      eei; spl.
      1: adm.
      step.
      adm.
    }
  Admitted.



End Clos.









Section Main.



  Theorem value_reduction :
    forall v fns v',
      Forall fs_wfm_val [v'] ->
      v' = bval_to_fval fns v
      -> ⟨ [], bexp_to_fexp fns
          (bval_to_bexp (subst_env (measure_val v))
          v) ⟩
         -->* RValSeq [v'].
  Proof.
    (* #1 Value Induction: intros/induction v using ind_val *)
    itr - v fns.
    ind ~ ind_val - v; itr - v' Hwfm Hresult.
    (* #2 Atoms: (Nil, Lit) {SAME} *)
    1: bse - value_reduction_vnil:    fns v'
                                      Hresult.
    1: bse - value_reduction_vlit:    fns v' l
                                      Hresult.
    (* #3 Doubles: [v1; v2] (Cons) *)
    1: bse - value_reduction_vcons:   fns v' v1 v2
                                      IHv1 IHv2 Hwfm Hresult.
    (* #4 Lists: [(v; vl)] (Tuple, Map) {STRUCTURE} *)
    2: bse - value_reduction_vtuple:  fns v' l
                                      H Hwfm Hresult.
    2: bse - value_reduction_vmap:    fns v' l
                                      H Hwfm Hresult.
    (* #5 Complexes: (Clos) *)
    1: bse - value_reduction_vclos:   fns v' ref ext id params body funid
                                      H Hwfm Hresult.
  Qed.



End Main.