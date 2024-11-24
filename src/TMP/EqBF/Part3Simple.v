From CoreErlang.TMP.EqBF Require Export Part2Simple.

Import BigStep.













(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: EQUIVALENCEREDUCTION /////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(** STRUCTURE:
* Tactics
  - rem_sbt
  - rem_sbt_smp
* Help
  - create_result_vtuple
  - create_result_vmap
  - list_biforall_vtuple
  - list_biforall_vmap
* Main Small
  - eq_bs_to_fs_reduction_vnil
  - eq_bs_to_fs_reduction_vlit
  - eq_bs_to_fs_reduction_vcons
  - eq_bs_to_fs_reduction_vtuple_nil
  - eq_bs_to_fs_reduction_vtuple
  - eq_bs_to_fs_reduction_vmap_nil
  - eq_bs_to_fs_reduction_vmap
  - eq_bs_to_fs_reduction_vmap_clos
* Main Big
  - bs_to_fs_equivalence_reduction
*)






(* Section: EquivalenceReduction_Tactics. *)



Tactic Notation "rem_sbt"
  ":"   constr(v)
  :=
  remember
    (subst_env (measure_val v))
    as sbt
    eqn:Hsbt.

Tactic Notation "rem_sbt"
  ":"   constr(v1) constr(v2)
  :=
  remember
    (subst_env (measure_val v1))
    as sbt1
    eqn:Hsbt1;
  remember
    (subst_env (measure_val v2))
    as sbt2
    eqn:Hsbt2;
  clear Hsbt1 Hsbt2.

Tactic Notation "rem_sbt"
  ":"   constr(v1) constr(v2) constr(v3)
  :=
  remember
    (subst_env (measure_val v1))
    as sbt1
    eqn:Hsbt1;
  remember
    (subst_env (measure_val v2))
    as sbt2
    eqn:Hsbt2;
  remember
    (subst_env (measure_val v3))
    as sbt3
    eqn:Hsbt3;
  clear Hsbt1 Hsbt2 Hsbt3.



Tactic Notation "rem_sbt_smp"
  ":" constr(v)
  :=
  remember
    (subst_env (measure_val v))
    as sbt
    eqn:Hsbt;
  simpl;
  inversion Hsbt;
  subst;
  clear_refl.



(* End: EquivalenceReduction_Tactics. *)






Section EquivalenceReduction_Help.



  Lemma create_result_vtuple :
    forall v vl,
      create_result ITuple ([] ++ v :: vl) []
    = Some (RValSeq [Syntax.VTuple (v :: vl)], []).
  Proof.
   trv.
  Qed.



  Lemma create_result_vmap :
    forall v1 v2 vl,
      create_result IMap ([v1] ++ v2 :: (flatten_list vl)) []
    = Some (RValSeq [Syntax.VMap (make_val_map ((v1, v2) :: vl))], []).
  Proof.
    (* #1 Simply: intro/simpl/f_equal *)
    itr.
    smp.
    f_equal.
    (* Rewrite Lemma: rewrite *)
    bwr - flatten_deflatten.
  Qed.



  Lemma create_result_values :
    forall v vl,
      create_result IValues ([] ++ v :: vl) []
    = Some (RValSeq (v :: vl), []).
  Proof.
   trv.
  Qed.



  Theorem list_biforall_vtuple :
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
    * (* #4.1 Prove by Pose Reverse: pose/destruct/rename/simpl/inversion *)
      (* des - vl: ivr - Hexp.
      simpl map in Hstep.
      pse - create_result_vtuple:
        (bval_to_fval fns v)
        (map (bval_to_fval fns) vl). *)
      pose proof framestack_ident_rev _ _ _ _ _ _ Hstep.
      do 4 des - H.
      ren - Hcreate Hlist v'' vl'' eff: H H0 x x0 x1.
      smp - Hcreate.
      bvs - Hcreate.
    * (* #4.2 Prove by Contraction: rename/inversion/constructor *)
      ren - Hcreate: H6.
      ivc - Hcreate.
      ivc - Hstep.
      1: cns.
      ren - Hstep1 Hstep2: H H0.
      ivc - Hstep1.
  Qed.



  Theorem list_biforall_vmap :
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
    (* #3 Inversion Step: inversion/remember_subst *)
    ivc - Hstep as Hstep1 Hstep2: H H0.
    rem_sbt: (VMap vl).
    ivc - Hstep1 as Hstep Heq_list: Hstep2 H1.
    {
      ivc - Hstep.
      {
        cns.
      }
      ren - Hstep1 Hstep2: H H0.
      ivc - Hstep1.
    }
    rem_sbt: (VMap vl).
    (* #4 Fix List *)
    des - vl as [| [v1 v2] vl]: ivs - Heq_list.
    smp + Heq_list.
    ivc - Heq_list.
    (* Pose *)
    (* simpl map in Heq_map.
    pse - create_result_vmap:
        (bval_to_fval fns v1)
        (bval_to_fval fns v2)
        (map (prod_map (bval_to_fval fns) (bval_to_fval fns)) vl). *)
    pose proof framestack_ident_rev _ _ _ _ _ _ Hstep.
    do 4 des - H.
    clr - Hstep k.
    (* Rename*)
    ren - Hcreate Hlist v'' vl'' eff: H H0 x x0 x1.
    (* Inversion Create*)
    ivc - Hcreate as Heq_map': H0.
    des - vl'': ivc - Heq_map'.
    (* Rewrite Eq Map *)
    simpl map in Heq_map.
    simpl map in Heq_map'.
    rwr - Heq_map in Heq_map'.
    (* Remember *)
    rwr + mred_vmap_v1
          mred_vmap_v2
          mred_vmap_vl in Hlist.
    
    rwl - Heq_map in Heq_map'.
    (*
    rem_sbt: (VMap vl).
    ivs - Hlist.
    rem_sbt: (VMap vl).
    ivs - H4.
    cns.
    2: cns.
    *)
    (*
    rem - e1 e2 el as Heq_e1 Heq_e2 Heq_el:
      (bexp_to_fexp fns (bval_to_bexp (subst_env (measure_val v1)) v1))
      (bexp_to_fexp fns (bval_to_bexp (subst_env (measure_val v2)) v2))
      (map
        (fun '(x, y) => (bexp_to_fexp fns x, bexp_to_fexp fns y))
        (map
          (prod_map
            (bval_to_bexp (subst_env (measure_val (VMap vl))))
            (bval_to_bexp (subst_env (measure_val (VMap vl)))))
          vl));
       clr - Heq_e1 Heq_e2 Heq_el.
    rem - v1' v2' vl' as Heq_v1 Heq_v2 Heq_vl:
      (bval_to_fval fns v1)
      (bval_to_fval fns v2)
      (map (fun '(x, y) => (bval_to_fval fns x, bval_to_fval fns y)) vl);
      clr - Heq_v1 Heq_v2 Heq_vl v1 v2 vl fns.
    rwl - Heq_map in Heq_map'.
    *)
    (* ALMOST *)
    (*
      Maps.map_insert v'' v (make_val_map (deflatten_list vl'')) =
      Maps.map_insert v1' v2' (make_val_map vl')

      list_biforall (λ (e0 : Exp) (v : Val), ⟨ [], e0 ⟩ -->* [v]) (e1 :: e2 :: flatten_list el)
        (v'' :: v :: vl'')
      ______________________________________(1/1)
      list_biforall (λ (e : Exp) (v0 : Val), ⟨ [], e ⟩ -->* [v0]) (e1 :: e2 :: flatten_list el)
        (v1' :: v2' :: flatten_list vl')
    *)
  Admitted.



(*
  Theorem list_biforall_vtuple :
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
    * (* #4.1 Prove by Pose Reverse: pose/destruct/rename/simpl/inversion *)
      des - vl: ivr - Hexp.
      simpl map in Hstep.
      pse - create_result_vtuple as Hcreate:
        (bval_to_fval fns v)
        (map (bval_to_fval fns) vl).
      ass - as Hident: lft >
        (ITuple = ITuple \/ ITuple = IMap).
      bse - ident_reverse: el e
        ([] : list Val)
        (bval_to_fval fns v)
        (map (bval_to_fval fns) vl)
        ITuple k0
        ([Syntax.VTuple (bval_to_fval fns v :: map (bval_to_fval fns) vl)])
        ([] : SideEffects.SideEffectList)
        Hstep Hident Hcreate.
    * (* #4.2 Prove by Contraction: rename/inversion/constructor *)
      ren - Hcreate: H6.
      ivc - Hcreate.
      ivc - Hstep.
      1: cns.
      ren - Hstep1 Hstep2: H H0.
      ivc - Hstep1.
  Qed.



  Theorem list_biforall_vmap :
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
    (* #3 Inversion Step: inversion/remember_subst *)
    ivc - Hstep as Hstep1 Hstep2: H H0.
    rem_sbt: (VMap vl).
    ivc - Hstep1 as Hstep Heq_list: Hstep2 H1.
    {
      ivc - Hstep.
      {
        cns.
      }
      ren - Hstep1 Hstep2: H H0.
      ivc - Hstep1.
    }
    rem_sbt: (VMap vl).
    (* #4 Fix List *)
    des - vl as [| [v1 v2] vl]: ivs - Heq_list.
    smp + Heq_list.
    ivc - Heq_list.
    rwr - mred_vmap_v1
          mred_vmap_v2
          mred_vmap_vll
          in Hstep.
    ivc - Hstep as Hstep1 Hstep2: H H0.
    rem_sbt: (VMap vl).
    ivc - Hstep1 as Hstep: Hstep2.
    all: admit.
  Admitted.
*)



End EquivalenceReduction_Help.






Section EquivalenceReduction_Main_Small.



  Theorem eq_bs_to_fs_reduction_vnil :
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
    framestack_scope.
    framestack_step.
  Qed.


  Theorem eq_bs_to_fs_reduction_vlit :
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
    framestack_scope.
    framestack_step.
  Qed.



  Theorem eq_bs_to_fs_reduction_vcons :
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
    framestack_scope - v1' v2' Hscope_v1 Hscope_v2.
    framestack_step - Hstep_v2 / kv2 v2.
    framestack_step - Hstep_v1 / kv1 v1 fns.
    framestack_step.
  Qed.



  Theorem eq_bs_to_fs_reduction_vtuple_nil :
    forall fns,
      ⟨ [], bexp_to_fexp fns
              (bval_to_bexp
                (subst_env (measure_val (VTuple [])))
                 (VTuple [])) ⟩
        -->* RValSeq [bval_to_fval fns (VTuple [])].
  Proof.
    (* #1 FrameStack Proof: scope/step *)
    framestack_scope.
    framestack_step.
  Qed.



  Theorem eq_bs_to_fs_reduction_vtuple :
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
      pse - eq_bs_to_fs_reduction_vtuple_nil: fns.
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
    psc - list_biforall_vtuple as Hlist: fns kvl vl vl' Heq_vl Hstep_vl.
    pose proof framestack_ident
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
    framestack_scope - v' vl' Hscope_v Hscope_vl.
    rem_sbt: v (VTuple vl).
    framestack_step - Hstep_v / kv v sbt1.
    framestack_step - Hstep_vl.
  Qed.



  Theorem eq_bs_to_fs_reduction_vmap_nil :
    forall fns,
      ⟨ [], bexp_to_fexp fns
              (bval_to_bexp
                (subst_env (measure_val (VMap [])))
                 (VMap [])) ⟩
        -->* RValSeq [bval_to_fval fns (VMap [])].
  Proof.
    (* #1 FrameStack Proof: scope/step *)
    framestack_scope.
    framestack_step.
  Qed.



  Theorem eq_bs_to_fs_reduction_vmap :
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
      pse - eq_bs_to_fs_reduction_vmap_nil: fns.
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
          mred_vmap_vl.
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
    psc - list_biforall_vmap as Hlist: fns kvl vl vl' Heq_map_vl Heq_vl Hstep_vl.
    pose proof framestack_ident
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
    framestack_scope - v1' v2' vl' Hscope_v1 Hscope_v2 Hscope_vl.
    rem_sbt: v1 v2 (VMap vl).
    framestack_step - Hstep_v1 / kv1 v1 sbt1.
    framestack_step - Hstep_v2 / kv2 v2 sbt2.
    framestack_step - Hstep_vl.
  Qed.


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

  Theorem eq_bs_to_fs_reduction_vclos :
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
      (* #4.1 Simplify: refold/rewrite *)
      smp.
      (* rfl - bexp_to_fexp
            measure_val.
      pse - measure_ext_empty as Hempty.
      cwr - Hempty.
      rwr - orb_true_l.
      simpl subst_env. *)
      rwl - measure_env_eq.
      (* #5.1 Measure Reduction: rewrite *)
      rwr - mred_e_vars.
      (* #6.1 Framestack Scope: framestack_scope/exists/split *)
      eei; spl.
      1: adm.
      (* #7.1 Framestack Step: framestack_step *)
      framestack_step.
    }
    2: { (* EFun: fid = None *)
      (* #4.2 Simplify: simpl/rewrite *)
      smp.
      rwr - orb_true_r.
      rwl - measure_env_eq.
      (* #5.2 Measure Reduction: rewrite *)
      rwr - mred_e_vars.
      (* #6.2 Framestack Scope: framestack_scope/exists/split *)
      eei; spl.
      1: adm.
      (* #7.2 Framestack Step: framestack_step *)
      framestack_step.
    }
    1: { (* ELetRec *)
      (* #4.3 Simplify: simpl/rewrite *)
      rfl - bexp_to_fexp
            measure_val.
      rwr - measure_ext_notempty.
      simpl is_none.
      rwr - orb_false_l.
      rwl - Nat.add_assoc.
      ren - ext': ext.
      rem - ext as Hext:
        (p :: ext');
        clr - Hext.
      rwr - subst_env_step.
      rfl - bexp_to_fexp.
      admit.
      (* eei; spl.
      1: adm.
      framestack_step. *)
    }
    (* ⟨ [],
° Syntax.ELetRec
    (map
       (λ '(_, (vars0, body)),
          (Datatypes.length vars0,
           bexp_to_fexp
             (add_exp_ext_both vars0
                (map
                   (λ '(fid0, (vars1, body0)),
                      (fid0,
                       (vars1,
                        subst_env
                          (measure_exp_ext measure_exp ext + measure_val_env measure_val env)
                          (rem_exp_ext_both vars1 (bval_to_bexp_ext ext) env) body0)))
                   (bval_to_bexp_ext ext)) fns) body))
       (map
          (λ '(fid, (vars0, body)),
             (fid,
              (vars0,
               subst_env (measure_exp_ext measure_exp ext + measure_val_env measure_val env)
                 (rem_exp_ext_both vars0 (bval_to_bexp_ext ext) env) body)))
          (bval_to_bexp_ext ext)))
    (bexp_to_fexp
       (add_exp_ext_fids
          (map
             (λ '(fid, (vars0, body)),
                (fid,
                 (vars0,
                  subst_env
                    (measure_exp_ext measure_exp ext + measure_val_env measure_val env)
                    (rem_exp_ext_both vars0 (bval_to_bexp_ext ext) env) body)))
             (bval_to_bexp_ext ext)) fns)
       (subst_env (measure_exp_ext measure_exp ext + measure_val_env measure_val env)
          (rem_exp_ext_fids (bval_to_bexp_ext ext) env) (EFunId f))) ⟩ -->*
[Syntax.VClos
   (map
      (λ '(n, _, (vars', body)),
         (n, Datatypes.length vars',
          bexp_to_fexp (add_val_ext_both vars' ext fns)
            (subst_env (measure_env_exp (rem_val_ext_both vars' ext env) body)
               (rem_val_ext_both vars' ext env) body))) ext) 0 (Datatypes.length vars)
   (bexp_to_fexp (add_val_ext_both vars ext fns)
      (subst_env (measure_env_exp (rem_val_ext_fids ext env) e) (rem_val_ext_fids ext env) e))]
    } *)
    (*
    ⟨ [],
(bexp_to_fexp
   (add_exp_ext_fids
      (map
         (λ '(fid, (vars0, body)),
            (fid,
             (vars0,
              subst_env (measure_exp_ext measure_exp ext + measure_val_env measure_val env)
                (rem_exp_ext_both vars0 (bval_to_bexp_ext ext) env) body)))
         (bval_to_bexp_ext ext)) fns)
   (subst_env (measure_exp_ext measure_exp ext + measure_val_env measure_val env)
      (rem_exp_ext_fids (bval_to_bexp_ext ext) env) (EFunId f))).[
list_subst
  (convert_to_closlist
     (map (λ '(x, y), (0, x, y))
        (map
           (λ '(_, (vars0, body)),
              (Datatypes.length vars0,
               bexp_to_fexp
                 (add_exp_ext_both vars0
                    (map
                       (λ '(fid0, (vars1, body0)),
                          (fid0,
                           (vars1,
                            subst_env
                              (measure_exp_ext measure_exp ext +
                               measure_val_env measure_val env)
                              (rem_exp_ext_both vars1 (bval_to_bexp_ext ext) env) body0)))
                       (bval_to_bexp_ext ext)) fns) body))
           (map
              (λ '(fid, (vars0, body)),
                 (fid,
                  (vars0,
                   subst_env
                     (measure_exp_ext measure_exp ext + measure_val_env measure_val env)
                     (rem_exp_ext_both vars0 (bval_to_bexp_ext ext) env) body)))
              (bval_to_bexp_ext ext))))) idsubst] ⟩ -[ ?k ]-> ⟨ [],
[Syntax.VClos
   (map
      (λ '(n, _, (vars', body)),
         (n, Datatypes.length vars',
          bexp_to_fexp (add_val_ext_both vars' ext fns)
            (subst_env (measure_env_exp (rem_val_ext_both vars' ext env) body)
               (rem_val_ext_both vars' ext env) body))) ext) 0 (Datatypes.length vars)
   (bexp_to_fexp (add_val_ext_both vars ext fns)
      (subst_env (measure_env_exp (rem_val_ext_fids ext env) e) (rem_val_ext_fids ext env) e))]
⟩

    *)
  Admitted.



End EquivalenceReduction_Main_Small.






Section EquivalenceReduction_Main_Big.



  Theorem bs_to_fs_equivalence_reduction :
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
    ind + ind_val - v; itr - v' Hwfm Hresult.
    (* #2 Atoms: (Nil, Lit) {SAME} *)
    1: bse - eq_bs_to_fs_reduction_vnil: fns v' Hresult.
    1: bse - eq_bs_to_fs_reduction_vlit: fns v' l Hresult.
    (* #3 Doubles: [v1; v2] (Cons) *)
    1: bse - eq_bs_to_fs_reduction_vcons: fns v' v1 v2 IHv1 IHv2 Hwfm Hresult.
    (* #4 Lists: [(v; vl)] (Tuple, Map) {STRUCTURE} *)
    2: bse - eq_bs_to_fs_reduction_vtuple: fns v' l H Hwfm Hresult.
    2: bse - eq_bs_to_fs_reduction_vmap: fns v' l H Hwfm Hresult.
    (* #5 Complexes: (Clos) *)
    1: bse - eq_bs_to_fs_reduction_vclos: fns v' ref ext id params body funid
                                          H Hwfm Hresult.
  Qed.



End EquivalenceReduction_Main_Big.