From CoreErlang.TMP.EqBF Require Export Part2Simple.

Import BigStep.













(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: EQUIVALENCEREDUCTION /////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* Tactics
  - Do Step
    + do_step
    + do_step1
  - Do Tran
    + do_trans
    + do_step_trans
  - Remember Subst
    + rem_sbt
    + rem_sbt_
    + rem_sbt_smp
    + rem_sbt_step
  - Specialize Reflexivity
    + spe_rfl
* Help
  - create_result_tuple
  - list_biforall_tuple
* Main Small
* Main Big
  - bs_to_fs_equivalence_reduction
*)






(* Section: EquivalenceReduction_Tactics. *)



(* Do Step: *)

Ltac do_step
  :=
  econstructor;
  [ constructor; auto
  | simpl ].

Ltac do_step1 :=
  econstructor;
  [ econstructor;
    [ congruence
    | constructor ]
  | simpl ].



(* Do Trans: *)

Tactic Notation "do_trans"
  "-" ident(Hstep)
  :=
  eapply transitive_eval;
  [ eapply frame_indep_core in Hstep;
    exact Hstep
  | .. ].

Tactic Notation "do_trans"
  "-" ident(Hstep) ident(k) ident(Hsbt) ident(sbt) ident(Hv) ident(v)
  :=
  eapply transitive_eval;
  [ eapply frame_indep_core in Hstep;
    exact Hstep
  | clear Hstep k Hsbt sbt Hv v;
    simpl ].



Tactic Notation "do_step_trans"
  "-" ident(Hstep)
  :=
  do_step;
  eapply transitive_eval;
  [ eapply frame_indep_core in Hstep;
    exact Hstep
  | clear Hstep;
    simpl ].

Tactic Notation "do_step_trans"
  "-" ident(Hstep) ident(k) ident(Hv) ident(v)
  :=
  do_step;
  eapply transitive_eval;
  [ eapply frame_indep_core in Hstep;
    exact Hstep
  | clear Hstep k Hv v;
    simpl ].

Tactic Notation "do_step_trans"
  "-" ident(Hstep) ident(k)
  :=
  do_step;
  eapply transitive_eval;
  [ eapply frame_indep_core in Hstep;
    exact Hstep
  | clear Hstep k;
    simpl ].



(* Remember Subst: *)

Tactic Notation "rem_sbt"
  "-"   ident(name)
  "as"  ident(Hname)
  ":"   constr(v)
  :=
  remember
    (subst_env (measure_val v))
    as sbt
    eqn:Hsbt.



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



Tactic Notation "rem_sbt_step"
  ":" constr(v)
  :=
  remember
    (subst_env (measure_val v))
    as sbt
    eqn:Hsbt;
  simpl;
  do_step;
  inversion Hsbt;
  subst;
  clear_refl.



(* Specialize Reflexivity: *)

Tactic Notation "spe_rfl"
  "-" hyp(H1)
  :=
  specialize (H1 eq_refl).

Tactic Notation "spe_rfl"
  "-" hyp(H1) hyp(H2)
  :=
  specialize (H1 eq_refl);
  specialize (H2 eq_refl).

Tactic Notation "spe_rfl"
  "-" hyp(H1) hyp(H2) hyp(H3)
  :=
  specialize (H1 eq_refl);
  specialize (H2 eq_refl);
  specialize (H3 eq_refl).



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
    ->  vl' = map (fun '(x, y) => (bval_to_fval fns x, bval_to_fval fns y)) vl
    ->  ⟨ [], bexp_to_fexp fns
          (bval_to_bexp (subst_env (measure_val (VMap vl))) (VMap vl)) ⟩
        -[ kvl ]-> ⟨ [], RValSeq [Syntax.VMap vl'] ⟩
    ->  list_biforall
          (fun e v => ⟨ [], RExp e ⟩ -->* RValSeq [v])
          (flatten_list
            (map
              (fun '(x, y) => (bexp_to_fexp fns x, bexp_to_fexp fns y))
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
    pose proof framestack_ident_rev _ _ _ _ _ _ Hstep.
    do 4 des - H.
    clr - Hstep k.
    (* Rename*)
    ren - Hcreate Hlist v'' vl'' eff: H H0 x x0 x1.
    (* Inversion Create*)
    ivc - Hcreate as Heq_map': H0.
    des - vl'': ivc - Heq_map'.
    (* Rewrite Eq Map *)
    smp - Heq_map Heq_map'.
    cwr - Heq_map in Heq_map'.
    (* Remember *)
    rwr + mred_vmap_v1
          mred_vmap_v2
          mred_vmap_vl in Hlist.
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



  (*Not Using*)
  (*
  Theorem list_biforall_vtuple2 :
    forall f vl vl',
        vl' = map (bval_to_fval f) vl
    ->  ⟨ [], bexp_to_fexp f
          (bval_to_bexp (subst_env (measure_val (VTuple vl))) (VTuple vl)) ⟩
        -->* RValSeq [Syntax.VTuple vl']
    ->  list_biforall
          (fun e v => ⟨ [], RExp e ⟩ -->* RValSeq [v])
          (map
            (bexp_to_fexp f)
            (map (bval_to_bexp (subst_env (measure_val (VTuple vl)))) vl))
          vl'.
  Proof.
    itr - f vl vl' Hvl' Hfs.
    des - Hfs as [kvl [Hres Hstep]].
    rfl - bval_to_bexp bexp_to_fexp in Hstep.
    ivc - Hvl'.
    rfl - bval_to_bexp.
    ivc - Hstep as Hstep1 Hstep2: H H0.
    rem_sbt: (VTuple vl).
    ivc - Hstep1 as Hstep: Hstep2.
    ivc - Hstep as Hstep1 Hstep2: H H0.
    rem_sbt: (VTuple vl).
    ivc - Hstep1 as Hexp Hnot Hstep: H2 H5 Hstep2.
    2: {
      ren - Hcreate: H6.
      ivc - Hcreate.
      ivc - Hstep.
      1: cns.
      ren - Hstep1 Hstep2: H H0.
      ivc - Hstep1.
    }
    ass - as Hfs: exi - k0; spl; asm >
      (⟨ [FParams ITuple [] el], e ⟩ -->*
      RValSeq [Syntax.VTuple (map (bval_to_fval f) vl)]).
    pose proof framestack_ident_rev2 _ _ _ _ _ Hfs.
    do 4 des - H.
    ren - Hcreate Hlist v'' vl'' eff: H H0 x x0 x1.
    smp - Hcreate.
    bvs - Hcreate.
  Qed.
  *)



  Theorem list_biforall_vtuple_nth :
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
    itr - fns env e0 el v0 vl v' vl' Hv' Hvl' Hlen Hwfm Hfs.
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



  Theorem list_biforall_vtuple_nth2 :
    forall fns env e el el' v vl v' vl',
        v' = bval_to_fval fns v
    ->  vl' = map (bval_to_fval fns) vl
    ->  Datatypes.length (e :: el) = Datatypes.length (v :: vl)
    ->  fs_wfm_result (bres_to_fres fns (inl [VTuple (v :: vl)]))
    ->  (forall i,
            i < Datatypes.length (e :: el ++ el')
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
      ass > (1 < Datatypes.length (e0 :: e1 :: el ++ el')) as Hl: sli.
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
        ass > (0 < Datatypes.length (e0 :: e1 :: el ++ el')) as Hl: sli.
        (* #7.2.1 Specialize: specialize *)
        spc - Hfs: 0 Hl fns (RValSeq [bval_to_fval fns v0]) Hwfm_v0.
        spe_rfl - Hfs.
        (* #8.2.1 Prove by Hypothesis: simpl/assumption *)
        smp + Hfs.
        asm.
      - (* #6.2.2 Prepare for Specialize: clear/simpl/destruct/apply/assert *)
        smp - Hl' Hwfm.
        ass > (S (S i) < Datatypes.length (e0 :: e1 :: el ++ el')) as Hl: sli.
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
      (map (fun '(x, y) => (bval_to_fval fns x, bval_to_fval fns y)) vl);
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
          (fun '(x, y) => (bexp_to_fexp fns x, bexp_to_fexp fns y))
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
    (* #4 Simplify: refold/remember/simpl *)
    rfl - bval_to_fval
          bval_to_bexp.
    (* destruct ext*)
    des - ext.
  * rfl - bexp_to_fexp.
    replace
      (measure_val (VClos env [] id vars e fid)) with
      (measure_env_exp env e) by admit.
    eei; spl.
    1: adm.
    framestack_step.
    (*0 = id?*)
    (* modify bval_to_fval or bexp_to_fexp or bval_to_bexp*)
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