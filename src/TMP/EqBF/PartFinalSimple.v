From CoreErlang.TMP.EqBF Require Export Part3Simple.

Import BigStep.













(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: EQUIVALENCE  /////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

Lemma bvs_to_fvs_length :
  forall fns vs,
    Datatypes.length (bvs_to_fvs fns vs)
  = Datatypes.length vs.
Proof.
  itr.
  ind - vs as [| v vs Hvs]: bmp | smp.
  bwr - Hvs.
Qed.

Lemma length_zero_empty :
  forall A (al : list A),
    0 = Datatypes.length al
->  al = [].
Proof.
  itr.
  ind - al: rfl.
  smp - H.
  con.
Qed.

Lemma bval_to_fval_list :
  forall fns v v',
    bval_to_fval fns v = v'
->  map (bval_to_fval fns) [v] = [v'].
Proof.
  itr.
  smp.
  bwr - H.
Qed.

Lemma bval_to_fval_list2 :
  forall fns v v',
    v' = bval_to_fval fns v
->  map (bval_to_fval fns) [v] = [v'].
Proof.
  itr.
  smp.
  bwr - H.
Qed.


(*
| env, modules, own_module, id, e, eff | -e> | id', e', eff' |
*)


Theorem equivalence_bigstep_framestack1 :
  forall env modules own_module id id' e e' eff eff',
    (eval_expr env modules own_module id e eff id' e' eff')
->  forall f r,
      bres_to_fres f e' = r
  ->  well_formed_map_fs_result r
  ->  ⟨ [], (bexp_to_fexp_subst f env e) ⟩ -->* r.
Proof.
  (* #1 Intro: intro/induction *)
  itr - env modules own_module id id' e e' eff eff' Hbig_step.
  ind - Hbig_step; itr - fns r Hresult Hwfm.
  (* #2 Atoms #1: (Nil & Lit) {SAME} *)
  3: { (* Nil *)
    eex; spl; ivc - Hresult.
    1: scope_solver_triv.
    do_step; cns.
  }
  3: { (* Lit *)
    eex; spl; ivc - Hresult.
    1: scope_solver_triv.
    do_step; cns.
  }
  (* #3 Atom #2: (Var & FunId) {ALMOST} *)
  3: { (* Var *)
    ren - Hget: H.
    sbn *.
    ivc - Hresult.
    rwr - Hget.
    des - res as [|v vs].
    1: app - get_value_singelton_length in Hget; smp - Hget; con.
    des - vs as [|v' vs].
    2: app - get_value_singelton_length in Hget; smp - Hget; con.
    admit. (* Skip: because refacor might change it anyway*)
  }
  3: { (* FunId *)
    ren - Hget: H.
    sbn *.
    ivc - Hresult.
    rwr - Hget.
    des - res as [|v vs].
    1: app - get_value_singelton_length in Hget; smp - Hget; con.
    des - vs as [|v' vs].
    2: app - get_value_singelton_length in Hget; smp - Hget; con.
    admit. (* Skip: because refacor might change it anyway*)
  }
  (* #4 Doubles #1: [e1;e2] (Cons, Seq) {SIMILIAR}*)
  6: { (* Cons *)
    (* +1 Inversion: clear?/rename?/inversion/simple *)
    clr - Hbig_step1 Hbig_step2.
    ren - e1 e2 v1 v2 Hframe_stack1 Hframe_stack2:
      hd tl hdv tlv IHHbig_step2 IHHbig_step1.
    ivc - Hresult.
    sbn *.
    (* +2 Measure Reduction?: rewrite *)
    rwr - mred_e1e2_e1.
    rwr - mred_e1e2_e2.
    (* +3 Well Formed Map?: simpl?/apply/destruct *)
    des - Hwfm as [[Hv1_wfm Hv2_wfm] _].
    app - well_formed_map_fs_to_result in Hv1_wfm.
    app - well_formed_map_fs_to_result in Hv2_wfm.
    (* +4 Remember?: remember/rewrite? *)
    rem - v1' v2' as Hv1' Hv2':
      (bval_to_fval fns v1)
      (bval_to_fval fns v2).
    (* +5 Specialize?: specialize/rewrite? *)
    spe - Hframe_stack1: fns (RValSeq [v1']).
    spe - Hframe_stack2: fns (RValSeq [v2']).
    rwl - Hv1' Hv2' in *.
    spe_rfl - Hframe_stack1 Hframe_stack2.
    spc - Hframe_stack1: Hv1_wfm.
    spc - Hframe_stack2: Hv2_wfm.
    (* +6 Destruct?: destruct *)
    des - Hframe_stack1 as [kv1 [Hv1_res Hv1_step]].
    des - Hframe_stack2 as [kv2 [Hv2_res Hv2_step]].
    (* +7 Scope: exists/split/tactic *)
    eex; spl.
    1: scope_solver_cons - v1' v2' Hv1_res Hv2_res.
    (* +12 Step: clear/do_step/constructor?/trans?/exact? *)
    clr - Hv1_res Hv2_res.
    do_step_trans - Hv2_step kv2 Hv2' v2.
    do_step_trans - Hv1_step kv1 Hv1' v1.
    do_step.
    cns.
  }
  12: { (* Seq *)
    (* +1 Inversion: clear?/rename?/inversion/simple *)
    clr - Hbig_step1 Hbig_step2.
    ren - Hframe_stack1 Hframe_stack2 Hv2_wfm: IHHbig_step1 IHHbig_step2 Hwfm.
    ivc - Hresult.
    sbn *.
    (* +2 Measure Reduction?: rewrite *)
    rwr - mred_e1e2_e1.
    rwr - mred_e1e2_e2.
    (* +3 Well Formed Map?: simpl?/apply/destruct *)
    assert (well_formed_map_fs (bval_to_fval fns v1)) as Hv1_wfm
      by admit.
    app - well_formed_map_fs_to_result in Hv1_wfm.
    (* +4 Remember?: remember/rewrite? *)
    rem - v1' v2' as Hv1' Hv2':
      (bval_to_fval fns v1)
      (bres_to_fres fns v2).
    (* +5 Specialize?: specialize/rewrite? *)
    spe - Hframe_stack1: fns (RValSeq [v1']).
    spe - Hframe_stack2: fns v2'.
    rwl - Hv1' Hv2' in *.
    spe_rfl - Hframe_stack1 Hframe_stack2.
    spc - Hframe_stack1: Hv1_wfm.
    spc - Hframe_stack2: Hv2_wfm.
    (* +6 Destruct?: destruct *)
    des - Hframe_stack1 as [kv1 [Hv1_res Hv1_step]].
    des - Hframe_stack2 as [kv2 [Hv2_res Hv2_step]].
    (* +7 Scope: exists/split/tactic *)
    eex; spl.
    1: asm.
    (* +12 Step: clear/do_step/constructor?/trans?/exact? *)
    clr - Hv1_res Hv2_res.
    do_step_trans - Hv1_step kv1 Hv1' v1.
    do_step_trans - Hv2_step kv2 Hv2' v2.
    cns.
  }
  (* #4 Doubles #2: [e1;e2] (Let, Try) {SIMILIAR}*)
  11: { (* Let *)
    (* +1 Inversion: clear?/rename?/inversion/simple *)
    clr - Hbig_step1 Hbig_step2.
    ren - Hframe_stack1 Hframe_stack2 Hlength Hv2_wfm:
      IHHbig_step1 IHHbig_step2 H Hwfm.
    ivc - Hresult.
    sbn *.
    (* +2 Measure Reduction?: rewrite *)
    rwr - mred_e1e2_e1.
    replace
      (subst_env (measure_exp e1 + measure_exp e2 + measure_env env)
        (rem_vars l env) e2)
      with
      (subst_env (measure_exp e2 + measure_env (rem_vars l env))
        (rem_vars l env) e2)
      by admit.
    (* rwr - mred_e1e2_e2. *)
    (* +3 Well Formed Map?: simpl?/apply/destruct *)
    assert (well_formed_map_fs_valseq (bvs_to_fvs fns vals)) as Hv1_wfm
      by admit.
    app - well_formed_map_fs_valseq_to_result in Hv1_wfm.
    (* +4 Remember?: remember/rewrite? *)
    rem - v1' v2' as Hv1' Hv2':
      (bvs_to_fvs fns vals)
      (bres_to_fres fns res).
    (* +5 Specialize?: specialize/rewrite? *)
    spe - Hframe_stack1: fns (RValSeq v1').
    spe - Hframe_stack2: fns v2'.
    rwl - Hv1' Hv2' in *.
    spe_rfl - Hframe_stack1 Hframe_stack2.
    spc - Hframe_stack1: Hv1_wfm.
    spc - Hframe_stack2: Hv2_wfm.
    (* +6 Destruct?: destruct/rewrite?/unfold? *)
    des - Hframe_stack1 as [kv1 [Hv1_res Hv1_step]].
    des - Hframe_stack2 as [kv2 [Hv2_res Hv2_step]].
    rwr - bexp_to_fexp_add_vars in Hv2_step.
    rwl - Hv1' in Hv2_step.
    ufl - bexp_to_fexp_subst measure_env_exp in *.
    (* +7 Scope: exists/split/tactic *)
    eex; spl.
    1: asm.
    (* +12 Step: clear/do_step/constructor?/trans?/exact? *)
    clr - Hv1_res Hv2_res.
    do_step_trans - Hv1_step. clr - kv1.
    do_step.
    1: cwr - Hv1' Hlength; bse - bvs_to_fvs_length.
    exa - Hv2_step.
  }
  16: { (* Try *)
  (* +1 Inversion: clear?/rename?/inversion/simple *)
    clr - Hbig_step1 Hbig_step2.
    ren - Hframe_stack1 Hframe_stack2 Hv2_wfm Hlength:
      IHHbig_step1 IHHbig_step2 Hwfm H.
    ivc - Hresult.
    sbn.
    (* +2 Measure Reduction?: rewrite *)
    replace
      (subst_env (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env env) env e1)
      with
      (subst_env (measure_exp e1 + measure_env env) env e1)
      by admit.
    replace
      (subst_env (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env env) env e2)
      with
      (subst_env (measure_exp e2 + measure_env env) env e2)
      by admit.
    replace
      (subst_env (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env env) env e3)
      with
      (subst_env (measure_exp e3 + measure_env env) env e3)
      by admit.
    (* +3 Well Formed Map?: simpl?/apply/destruct *)
    assert (well_formed_map_fs_result (bvs_to_fvs fns vals)) as Hv1_wfm
      by admit.
    (* +4 Remember?: remember/rewrite? *)
    rem - v1' v2' as Hv1' Hv2':
      (bvs_to_fvs fns vals)
      (bres_to_fres fns res).
    (* +5 Specialize?: specialize/rewrite? *)
    spe - Hframe_stack1: fns v1'.
    spe - Hframe_stack2: fns v2'.
    ufl - bres_to_fres in Hframe_stack1.
    rwl - Hv1' Hv2' in *.
    spe_rfl - Hframe_stack1 Hframe_stack2.
    spc - Hframe_stack1: Hv1_wfm.
    spc - Hframe_stack2: Hv2_wfm.
    (* +6 Destruct?: destruct/rewrite?/unfold? *)
    des - Hframe_stack1 as [kv1 [Hv1_res Hv1_step]].
    des - Hframe_stack2 as [kv2 [Hv2_res Hv2_step]].
(*     rwr - bexp_to_fexp_add_vars in Hv2_step. *)
(*     rwl - Hv1' in Hv2_step. *)
    (* replace
      (bexp_to_fexp_subst (add_vars vl1 fns) (rem_vars vl1 env) e2)
      with
      (bexp_to_fexp_subst (add_vars vl1 fns) env e2)
      in Hv2_step
      by admit.
    ufl - bexp_to_fexp_subst measure_env_exp in *. *)
    (* +7 Scope: exists/split/tactic *)
    eex; spl.
    1: asm.
    (* +12 Step: clear/do_step/constructor?/trans?/exact? *)
    clr - Hv1_res Hv2_res.
    do_step_trans - Hv1_step. clr - kv1.
    do_step.
    1: cwr - Hv1' Hlength; bse - bvs_to_fvs_length.
    rwr - bexp_to_fexp_add_vars in Hv2_step.
    ufl - bexp_to_fexp_subst measure_env_exp in *.
(*     exa - Hv2_step. *)
admit.
  }
  (* #4 Lists: [(e::el)] (Tuple & Values) {SIMILIAR}*)
  5: { (* Tuple *)
    ren - Hlen_vals Hlen_eff Hlen_ids Hbs Hfs Heff Hid:
      H H0 H1 H2 H3 H4 H5.
    ivc - Hresult.
    des - exps as [|e el].
    * clr - Hlen_eff Hlen_ids Hbs Hfs Hwfm.
      smp - Hlen_vals.
      pse - length_zero_empty as Hempty: Value vals Hlen_vals.
      ivc - Hempty.
      smp; eex; spl.
      - scope_solver_triv.
      - do_step; do_step1; cns.
    * destruct vals.
      1: smp *; con.
      ren - vl: vals.
      ufl - bexp_to_fexp_subst measure_env_exp.
      smp.
      (* Measure reduction*)
      rwr - mred_eel_e.
      rwr - mred_eel_el.
      (*remember*)
      rem - v' vl' as Hv' Hvl':
        (bval_to_fval fns v)
        (map (bval_to_fval fns) vl).
      (* Pose *)
      pse - create_result_tuple as Hcreate: v' vl'.
      pose proof framestack_ident
        ITuple
        (map (bexp_to_fexp fns)
          (map (subst_env (measure_list measure_exp el + measure_env env) env)
            el))
        []
        vl'
        (RValSeq [Syntax.VTuple (v' :: vl')])
        v'
        []
        []
        Hcreate
        as Hident
        .
      (*Assert*)
      assert
        (list_biforall (λ (e : Exp) (v : Val), ⟨ [], e ⟩ -->* RValSeq [v])
           (map (bexp_to_fexp fns)
              (map (subst_env
                (measure_list measure_exp el + measure_env env) env) el)) vl')
        as Hlist.
      {
        clr + Hfs Hv' Hvl' Hlen_vals Hwfm.
        ren - v0 v0' Hv0': v v' Hv'.
        generalize dependent el.
        generalize dependent vl.
        induction vl as [| v vl IH].
        - (* Base case: vl is empty *)
          intros Hwfm Hvl' el Hel_length Hfs.
          destruct el as [| e' el'].
          + (* Both lists are empty *)
            ivc -Hvl'.
            simpl. constructor.
          + (* el is non-empty, contradiction *)
            simpl in Hel_length. discriminate.
        - (* Inductive step: vl is v' :: vl' *)
          intros Hwfm Hvl' el Hel_length Hfs.
          destruct el as [| e' el'].
          + (* el is empty, contradiction *)
            simpl in Hel_length. discriminate.
          + (* Both lists are non-empty *)
            simpl in Hel_length. inversion Hel_length.
            simpl.
            ivc - Hv0'.
            smp.
            constructor.
            ** epose proof Hfs 1 ltac: (slia) fns
                (RValSeq [(bval_to_fval fns v)])
                eq_refl _ as Hv.
               smp - Hv.
               rwr - mred_eel_e.
               ufl - bexp_to_fexp_subst in Hv.
               asm.
            ** rwr - mred_eel_el.
               ass as Hwfm1 by admit: (* with later Hwfm *)
                (well_formed_map_fs_result
                  (bres_to_fres fns (inl [VTuple (v0 :: vl)]))).
               (* bad direction *)
               admit.
      }
      spc - Hident: Hlist.
      epose proof Hfs 0 ltac: (slia) fns
        (RValSeq [(bval_to_fval fns v)])
        eq_refl _ as Hv.
      (**)
      (*destruct*)
      smp - Hv.
      des - Hv as [kv [Hv_res Hv_step]].
      des - Hident as [kvl Hvl_step].
      (*Scope*)
      eex; spl.
      1: admit.
      (* Step *)
      do_step.
      do_step_trans - Hv_step. clr - kv.
      rwl - Hv' in *. 
      exa - Hvl_step.
  }
Admitted.



Theorem equivalence_bigstep_framestack2 :
  forall e env modules own_module id id' eff eff' e',
    (eval_expr env modules own_module id e eff id' e' eff')
->  forall f r,
      bres_to_fres f e' = r
  ->  well_formed_map_fs_result r
  ->  ⟨ [], (bexp_to_fexp_subst f env e) ⟩ -->* r.
Proof.
  (* #1 Intro: intro/induction *)
  itr - e.
  ind + ind_exp - e;
    itr - env modules own_module id id' e' eff eff' Hbigstep fns r Hresult Hwfm.
  (* #2 Atoms #1: (Nil & Lit) {SAME} *)
  2: { (* Nil *)
    ivc - Hbigstep.
    eex; spl.
    1: scope_solver_triv.
    do_step; cns.
  }
  2: { (* Lit *)
    ivc - Hbigstep.
    eex; spl.
    1: scope_solver_triv.
    do_step; cns.
  }
  (* #4 Doubles #1: [e1;e2] (Cons, Seq) {SIMILIAR}*)
  5: { (* Cons *)
    (* +1 Inversion: clear?/rename?/inversion/simple *)
    ren - Hfs1 Hfs2: IHe1 IHe2.
    ivc - Hbigstep.
    *
    ren - v1 v2 Hbs1 Hbs2: hdv tlv H10 H5.
    sbn.
    (* +2 Measure Reduction?: rewrite *)
    rwr - mred_e1e2_e1.
    rwr - mred_e1e2_e2.
    (* +3 Well Formed Map?: simpl?/apply/destruct *)
    des - Hwfm as [[Hv1_wfm Hv2_wfm] _].
    app - well_formed_map_fs_to_result in Hv1_wfm.
    app - well_formed_map_fs_to_result in Hv2_wfm.
    (* +4 Remember?: remember/rewrite? *)
    rem - v1' v2' as Hv1' Hv2':
      (bval_to_fval fns v1)
      (bval_to_fval fns v2).
    (* +5 Specialize?: specialize/rewrite? *)
    spc - Hfs1: env modules own_module id'0 id' eff2 eff
      (inl [v1] : ValueSequence + Exception) Hbs1 fns.
    spe - Hfs1: (RValSeq [v1']).
    spc - Hfs2: env modules own_module id id'0 e' eff2
      (inl [v2] : ValueSequence + Exception) Hbs2 fns.
    spe - Hfs2: (RValSeq [v2']).
    ufl -bres_to_fres bvs_to_fvs in Hfs1 Hfs2.
    pse - bval_to_fval_list2 as Hvs1': fns v1 v1' Hv1'.
    pse - bval_to_fval_list2 as Hvs2': fns v2 v2' Hv2'.
    cwr - Hvs1' Hvs2' in *.
    spe_rfl - Hfs1 Hfs2.
    spc - Hfs1: Hv1_wfm.
    spc - Hfs2: Hv2_wfm.
    (* +6 Destruct?: destruct *)
    des - Hfs1 as [kv1 [Hv1_res Hv1_step]].
    des - Hfs2 as [kv2 [Hv2_res Hv2_step]].
    (* +7 Scope: exists/split/tactic *)
    eex; spl.
    1: scope_solver_cons - v1' v2' Hv1_res Hv2_res.
    (* +12 Step: clear/do_step/constructor?/trans?/exact? *)
    clr - Hv1_res Hv2_res.
    do_step_trans - Hv2_step; clr - kv2 Hv2' v2.
    do_step_trans - Hv1_step; clr - kv1 Hv1' v1.
    do_step; cns.
   *
    ren - Hbs2 Hex_wfm: H9 Hwfm.
    sbn.
    (* +2 Measure Reduction?: rewrite *)
    rwr - mred_e1e2_e1.
    rwr - mred_e1e2_e2.
    (* +3 Well Formed Map?: simpl?/apply/destruct *)
    (* des - Hwfm as [[Hv1_wfm Hv2_wfm] _].
    app - well_formed_map_fs_to_result in Hv1_wfm.
    app - well_formed_map_fs_to_result in Hv2_wfm. *)
    ufl - bres_to_fres in Hex_wfm.
    (* +4 Remember?: remember/rewrite? *)
    (* rem - v1' v2' as Hv1' Hv2':
      (bval_to_fval fns v1)
      (bval_to_fval fns v2). *)
    rem - ex' as Hex':
      (bexc_to_fexc fns ex).
    (* +5 Specialize?: specialize/rewrite? *)
    spc - Hfs2: env modules own_module id id' e' eff
      (inr ex : ValueSequence + Exception) Hbs2 fns.
    spe - Hfs2: (RExc ex').
    clr - Hfs1.
    ufl -bres_to_fres bvs_to_fvs in Hfs2.
    rwl - Hex' in Hfs2.
    spe_rfl - Hfs2.
    spc - Hfs2: Hex_wfm.
    (* +6 Destruct?: destruct *)
    des - Hfs2 as [kv2 [Hv2_res Hv2_step]].
    (* +7 Scope: exists/split/tactic *)
    eex; spl.
    1: asm.
    (* +12 Step: clear/do_step/constructor?/trans?/exact? *)
    clr - Hv2_res.
    do_step_trans - Hv2_step. clr - kv2.
    do_step. cns.
   * admit.
  }
  5: { (* Tuple *)
    ren - HForall: H.
    ivc - Hbigstep.
    * des - l.
      + smp - H0. pse - length_zero_empty as Hempty: Value vals H0. ivc - Hempty.
        smp; eex; spl.
        - scope_solver_triv.
        - do_step; do_step1; cns.
      + ivc - HForall. ren - He HForall: H5 H6.
        (* this doesnt work*)
        admit.
    * admit.
  }
Admitted.






(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: OLD  /////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

(*
Section Equivalence.


(*TODO needs well_formed_map predicate*)

  (*Todo: restriction to f?*)
  (*Todo restriction to closed *)
  Theorem equivalence_bigstep_framestack : 

    forall env modules own_module id id' e e' eff eff' f r,

      (eval_expr env modules own_module id e eff id' e' eff')

      ->

  	  r = bres_to_fres f e'

(* wellformed_map r (valseq,exc) later on top level *)

  	  ->

  	  ⟨ [], (bexp_to_fexp_subst f env e) ⟩
      	-->*
  	  r.

  Proof.
    intros. revert f r H0. induction H; intros.
    (* Values *)
    * admit.
    * admit.
    (* Nil *)
    * eexists. split; inv H0.
      - constructor. 
        scope_solver.
      - do 1 do_step.
        constructor.
    (* Lit *)
    * eexists. split; inv H0.
      - constructor.
        scope_solver.
      - do 1 do_step.
        constructor.
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
    * admit.
    (* Fun *)
    * admit.
    (* Tuple*)
    * admit.
    (* Cons *)
    * specialize (IHeval_expr2 f).
      specialize (IHeval_expr1 f).
      (*
      unfold bs_to_fs_res in H1.
      case_match.
      2: { congruence. }
      inv H1.
      unfold bs_to_fs_valseq in H2.
      simpl in H2.
      *)
      unfold bs_to_fs_res in H1.
      case_match.
      2: { congruence. }
      inv H1.
      unfold bs_to_fs_valseq in H2.
      simpl in H2.
      unfold bs_to_fs_val in H2.
      remember (subst_env (measure_val (VCons hdv tlv))) as _fsubst.
      unfold val_to_exp in H2.
      fold val_to_exp in H2.
      unfold bs_to_fs_exp in H2.
      unfold eraseNames in H2.
      fold eraseNames in H2.
      unfold exp_to_val_fs in H2.
      fold exp_to_val_fs in H2.
      case_match.
      2: { inv H2. }
      case_match.
      2: { inv H2. }
      inv H2.
      rewrite measure_reduction with (n2 := measure_val hdv) in H1.
      2-3: slia.
      rewrite measure_reduction with (n2 := measure_val tlv) in H3.
      2-3: slia.
      cbn.
      rewrite measure_reduction_subst_env with (e := hd).
      2: { unfold measure_subst_env. lia. }
      rewrite measure_reduction_subst_env with (e := tl).
      2: { unfold measure_subst_env. lia. }
      unfold bs_to_fs_res in *.
      simpl in *.
      unfold bs_to_fs_val in *.
      unfold bs_to_fs_exp in *.
      rewrite H1 in *.
      rewrite H3 in *.
      simpl in *.
      specialize (IHeval_expr1 _ eq_refl).
      specialize (IHeval_expr2 _ eq_refl).
      unfold bs_to_fs_valseq in *.
      inv IHeval_expr1.
      inv IHeval_expr2.
      destruct H2.
      destruct H4.
      eexists. split.
      { admit. }
      eapply transitive_eval.
      - do_step.
        eapply frame_indep_core in H5.
        exact H5.
      - cbn.
        do_step.
        eapply transitive_eval.
        {
          eapply frame_indep_core in H6.
          exact H6.
        }
        do_step.
        apply step_refl.
    (* Case *)
    * destruct (bs_to_fs_res f subst_env res).
      - admit.
      - congruence.
    (* Call *)    
    * admit.
    * admit.
    (* Primop *)
    * admit.
    (* App *)
    * admit.
    (* Let *)
    * 
      specialize (IHeval_expr2 f r H2).
      specialize (IHeval_expr1 f).
      destruct (bs_to_fs_res f subst_env (inl vals)) eqn:Hvals.
      2: { admit. }
      specialize (IHeval_expr1 r0 eq_refl).
      inv IHeval_expr1.
      destruct H3.
      inv IHeval_expr2.
      destruct H5.
      cbn in Hvals.
      case_match; inv Hvals.
      eexists. split.
      { admit. }
      eapply transitive_eval.
      - cbn. do_step.
        rewrite measure_reduction_subst_env with (e := e2).
        2: { unfold measure_subst_env. admit. }
        rewrite measure_reduction_subst_env with (e := e1).
        2: { unfold measure_subst_env. lia. }
        eapply frame_indep_core in H4.
        unfold bs_to_fs_exp_env in H4.
        unfold bs_to_fs_exp in H4.
        exact H4.
      - Search "rem" "env".
        do_step.
        1: { admit. } (*H7 and H0*)
        unfold bs_to_fs_exp_env, bs_to_fs_exp in H6.
        (* theorem *) (*e ind*)
        (*H7 -> (bs_to_fs_valseq f subst_env vals = Some v)
          eraseNames f (subst_env measure (append_vars l vals env)) e  = 
          (eraseNames (addVars l f) (subst_env measure env) e).[list_subst v idsubst]
        *)
        cbn.
        unfold bs_to_fs_exp_env in H6.
        unfold bs_to_fs_exp in H6.
        remember (fold_left
                 (λ (env' : list ((Var + FunctionIdentifier) * Value)) 
                    (key : Var + FunctionIdentifier),
                    filter (λ '(k, _), negb (var_funid_eqb k key)) env') 
                 (map inl l) env) as env'.
        do_step.
        1: { admit. }
        cbn in H6. (* generalize in H6?*)
        admit.
    (* Seq *)
    * specialize (IHeval_expr2 f r H1).
      specialize (IHeval_expr1 f).
      destruct (bs_to_fs_res f subst_env (inl [v1])) eqn:Hv1.
      2: { admit. }
      specialize (IHeval_expr1 r0 eq_refl).
      inv IHeval_expr1.
      destruct H2.
      inv IHeval_expr2.
      destruct H4.
      unfold bs_to_fs_exp_env in H5.
      unfold bs_to_fs_exp in H5.
      remember (eraseNames f (subst_env (measure_subst_env env e2) env e2)) as e.
      (* pose proof framestack_fseq e r r0 x0 H5.
      inv H6. *)
      inv Hv1.
      case_match. 2: congruence.
      inv H7.
      destruct (bs_to_fs_val f subst_env v1). 2: inv H6.
      inv H6.
      eexists. split.
      { admit. }
      eapply transitive_eval.
      - cbn. do_step.
        rewrite measure_reduction_subst_env with (e := e2).
        2: { unfold measure_subst_env. lia. }
        rewrite measure_reduction_subst_env with (e := e1).
        2: { unfold measure_subst_env. lia. }
        eapply frame_indep_core in H3.
        unfold bs_to_fs_exp_env in H3.
        unfold bs_to_fs_exp in H3.
        exact H3.
      - cbn.
        do_step.
        exact H5.
    (* LetRec *)
    * admit.
    (* Map *)
    * admit.
    (* Cons *)
    * admit.
    * admit.
    (* Tuple *)
    * admit.
    (* Try *)
    * admit.
    * admit.
    (* Case *)
    * admit.
    * admit.
    (* Call *)
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    (* Primop *)
    * admit.
    (* App *)
    * admit.
    * admit.
    * admit.
    * admit.
    (* Let *)
    * admit.
    (* Seq *)
    * admit.
    (* Map *)
    * admit.
  Admitted.


End Equivalence.
*)