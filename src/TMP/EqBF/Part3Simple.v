From CoreErlang.TMP.EqBF Require Export Part2Simple.

Import BigStep.













(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: EQUIVALENCEREDUCTION /////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* Main
  - bs_to_fs_equivalence_reduction
*)






(* Section: EquivalenceReduction_Tactics. *)

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
  | constructor ].

Tactic Notation "rem_sbt"
  "-"   ident(name)                   (* remember as *)
  "as"  ident(Hname)                  (* remember eqn *)
  ":"   constr(v)                     (* : Value *)
  :=
  remember
    (subst_env (measure_val v))
    as sbt
    eqn:Hsbt.

Tactic Notation "rem_sbt"
  ":"   constr(v)                     (* : Value *)
  :=
  remember
    (subst_env (measure_val v))
    as sbt
    eqn:Hsbt.

Tactic Notation "rem_sbt_smp_ivc"
  ":" constr(v)                       (* : Value *)
  :=
  remember
    (subst_env (measure_val v))
    as sbt
    eqn:Hsbt;
  simpl;
  inversion Hsbt;
  subst;
  clear_refl.

Tactic Notation "rem_sbt_smp_ivc_stp"
  ":" constr(v)                       (* : Value *)
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



Tactic Notation "do_step_trans"
  "-" ident(Hstep) ident(k) ident(Hv) ident(v)
  :=
  do_step;
  eapply transitive_eval;
  [ eapply frame_indep_core in Hstep;
    exact Hstep
  | clear Hstep k Hv v;
    simpl ].


(* End: EquivalenceReduction_Tactics. *)





Section EquivalenceReduction.



  Theorem bs_to_fs_equivalence_reduction :
    forall v f v',
      Forall well_formed_map_fs [v'] ->
      bval_to_fval f v = v'
      -> ⟨ [], bexp_to_fexp f
          (bval_to_bexp (subst_env (measure_val v))
          v) ⟩
         -->* RValSeq [v'].
  Proof.
    (* #1 Intro: intros/induction v using ind_val *)
    itr - v f.
    ind + ind_val - v; itr - v' Hwfm Heq.
    (* #2 Atom: (Nil & Lit) {SAME} *)
    1: {
      (* +1 Inversion: clear/rename/inversion *)
      clr - Hwfm.
      ivc - Heq.
      (* +2 Simplify: refold *)
      rfl - bval_to_bexp bexp_to_fexp bval_to_fval.
      (* +8 FrameStack Proof: eexists/split *)
      exs - 1; spl.
      (* +9 Scope: pose proof *)
      1: cns; scope_solver.
      (* +10 Step: clear/do_step/constructor *)
      do_step.
      cns.
    }
    1: {
      (* +1 Inversion: clear/rename/inversion *)
      clr - Hwfm.
      ivc - Heq.
      (* +2 Simplify: refold *)
      rfl - bval_to_bexp bexp_to_fexp bval_to_fval.
      (* +8 FrameStack Proof: eexists/split *)
      exs - 1; spl.
      (* +9 Scope: pose proof *)
      1: cns; scope_solver.
      (* +10 Step: clear/do_step/constructor *)
      do_step.
      cns.
    }
    (* #3 Double: [e1;e2] (Cons) *)
    1: {
      (* +1 Inversion: clear/rename/inversion *)
      ren - Hv1 Hv2: IHv1 IHv2.
      ivc - Heq.
      (* +2 Simplify: refold *)
      rfl - bval_to_bexp bexp_to_fexp bval_to_fval.
      rfl - bval_to_fval in Hwfm.
      (* +3 Measure Reduction: rewrite *)
      rwr - mred_vcons_v1.
      rwr - mred_vcons_v2.
      (* +4 Well Formed Map: apply/destruct *)
      app - well_formed_map_fs_cons in Hwfm.
      des - Hwfm as [Hwfm_v1 Hwfm_v2].
      (* +5 Remember: remember *)
      rem - v1' v2' as Hv1' Hv2':
        (bval_to_fval f v1)
        (bval_to_fval f v2).
      (* +6 Specialize: specialize *)
      spc - Hv1: v1' Hwfm_v1.
      spc - Hv2: v2' Hwfm_v2.
      spe_rfl - Hv1 Hv2.
      (* +7 Destruct: destruct *)
      des - Hv1 as [kv1 [Hv1_res Hv1_step]].
      des - Hv2 as [kv2 [Hv2_res Hv2_step]].
      (* +8 FrameStack Proof: eexists/split *)
      eex; spl.
      (* +9 Scope: pose proof *)
      1: bse - scope_cons: v1' v2' Hv1_res Hv2_res.
      (* +10 Step: clear/do_step/constructor *)
      clr - Hv1_res Hv2_res.
      do_step_trans - Hv2_step kv2 Hv2' v2.
      do_step_trans - Hv1_step kv1 Hv1' v1.
      do_step.
      cns.
    }
    2: {
      (* +1 Inversion: clear/rename/inversion *)
      ren - HForall: H.
      ivc - Heq.
      (* Induction *)
      ind - l as [| v vl].
      {
        simpl. eexists. split.
        * constructor; scope_solver.
        * do_step.
          econstructor.
          {
            econstructor.
            {
              congruence.
            }
            constructor.
          }
          constructor.
          
          eapply step_trans.
          {
            econstructor.
            {
              congruence.
            }
            constructor.
          }
          apply step_refl.
      }
    }
  Admitted.


(* OLD: *)


  Theorem bs_to_fs_equivalence_reduction :
    forall v f v',
      Forall well_formed_map_fs [v'] ->
      bval_to_fval f v = v'
      -> ⟨ [], bexp_to_fexp f
          (bval_to_bexp (subst_env (measure_val v))
          v) ⟩
         -->* RValSeq [v'].
  Proof.
    intros v f.
    induction v using ind_val.
    * (* #1 VNil *)
      (* +1 Intro *)
      simpl.
      intros vs Hmap H.
      inv H.
      (* +2 FrameStack Proof *)
      exists 1; split.
      - (* #1.1 Scope *)
        constructor.
        scope_solver.
      - (* #1.2 Step *)
        eapply step_trans.
        {
          constructor.
          scope_solver.
        }
        apply step_refl.
    * (* #2 VLit *)
      (* +1 Intro *)
      simpl.
      intros vs Hmap H.
      inv H.
      (* +2 FrameStack Proof *)
      exists 1; split.
      - (* #2.1 Scope *)
        constructor.
        scope_solver.
      - (* #2.2 Step *)
        eapply step_trans.
        {
          constructor.
          scope_solver.
        }
        apply step_refl.
    * (* #3 VCons *)
      (* +1 Intro *)
      intros vs Hmap H.
      (* rename [vs] *)
      rename H into Hvs.

      
      (* +2 Eliminate Cases *)
      (* case match [v1,v2] *)
(*       unfold bval_to_fval in *. *)
      remember 
        (subst_env (measure_val (VCons v1 v2))) 
        as _f_st.
      cbn.
      cbn in Hvs.
      ivs - Hvs.
      
      
      (*v1*)
      case_match. 2:
      {
        cbn in Hvs.
        congruence.
      }
      (*v2*)
      case_match. 2:
      {
        cbn in Hvs.
        congruence.
      }
      (*inversion*)
      cbn in Hvs.
      inv Hvs.
      (* rename [v1',v2'] *)
      (*v1'*)
      rename v into v1'.
      rename H into Hv1'.
      (*v2'*)
      rename v0 into v2'.
      rename H0 into Hv2'.
      (* +3 Formalize Hypotheses *)
      (* measure reduction [v1,v2] *)
      (*v1*)
      rewrite measure_val_reduction 
        with (n2 := measure_val v1) 
        in Hv1'.
      2-3: slia.
      (*v2*)
      rewrite measure_val_reduction 
        with (n2 := measure_val v2) 
        in Hv2'.
      2-3: slia.
      (* +3 Specialize Hypotheses *)
      (* specialize [v1,v2] *)
      (*v1*)
      specialize (IHv1 [v1']).
      unfold bexp_to_fexp in IHv1.
      rewrite Hv1' in IHv1.
      clear Hv1'.
      inv Hmap. (*NEW*)
      destruct H1.
      specialize (IHv1 (ltac: (by constructor)) eq_refl).
      (*v2*)
      specialize (IHv2 [v2']).
      unfold bexp_to_fexp in IHv2.
      rewrite Hv2' in IHv2.
      clear Hv2'.
      specialize (IHv2 (ltac: (by constructor)) eq_refl).
      (* destruct hypothesis [v1,v2] *)
      destruct IHv1 as [kv1 [Hv1_res Hv1_step]].
      destruct IHv2 as [kv2 [Hv2_res Hv2_step]].
      (* measure reduction [v1,v2] *)
      (*v1*)
      rewrite measure_val_reduction 
        with (n2 := measure_val v1).
      2-3: slia.
      (*v2*)
      rewrite measure_val_reduction 
        with (n2 := measure_val v2)
             (v := v2).
      2-3: slia.
      (* +3 FrameStack Proof *)
      eexists; split. 
      + (* #3.1 Scope *)
        clear - Hv1_res Hv2_res.
        constructor.
        inv Hv1_res.
        inv Hv2_res.
        destruct_foralls.
        scope_solver.
      + (* #3.2 Step *)
        clear Hv1_res Hv2_res.
        (*v2*)
        do 1 do_step.
        eapply transitive_eval.
        {
          eapply frame_indep_core in Hv2_step.
          exact Hv2_step.
        }
        simpl.
        clear Hv2_step kv2 v2.
        (*v1*)
        do 1 do_step.
        eapply transitive_eval.
        {
          eapply frame_indep_core in Hv1_step.
          exact Hv1_step.
        }
        simpl.
        clear Hv1_step kv1 v1.
        (*end*)
        clear f.
        do 1 do_step.
        apply step_refl.
    * (* #4 VClos *)
      (* +1 Intro *)
      clear H.
      intros vs Hmap Hvs.
      (* +2 Destruct Cases *)
      unfold bval_to_fval in *.
      remember
        (subst_env (measure_val (VClos ref ext id params body funid)))
        as _f_st.
      simpl in Hvs.
      remember
        (fold_left
          (λ (env' : list ((Var + FunctionIdentifier) * Value)) 
             (key : Var + FunctionIdentifier),
             filter (λ '(k, _), negb (var_funid_eqb k key)) env') 
          (map inl params) ref)
        as env'.
      (*ext*)
      destruct ext.
      - (* #4.1 [] *)
        cbn.
        inv Hvs.
        remember
          (fold_left
            (λ (env' : list ((Var + FunctionIdentifier) * Value)) 
               (key : Var + FunctionIdentifier),
               filter (λ '(k, _), negb (var_funid_eqb k key)) env') 
            (map inl params) ref)
          as env'.
        unfold bexp_to_fexp.
        eexists; split.
        + (* #4.1.1 Scope *)
          constructor.
          destruct_foralls.
          constructor. 2: 
          {
            scope_solver.
          }
          constructor. 1:
          {
            cbn.
            intros.
            inv H.
          }
          admit.
        + (* #4.1.2 Step *)
          do_step.
          apply step_refl.
      - (* #4.2 _ :: _ *)
        (*funid*)
        destruct funid.
        + (* #4.2.1 Some *)
          cbn in Hvs.
          cbn.
          congruence.
          (*TODO: this is not a congruence, bval_to_fval definition is incorrect *)
        + (* #4.2.2 None *)
          cbn.
          inv Hvs.
          remember
            (fold_left
              (λ (env' : list ((Var + FunctionIdentifier) * Value)) 
                 (key : Var + FunctionIdentifier),
                 filter (λ '(k, _), negb (var_funid_eqb k key)) env') 
              (map inl params) ref)
            as env'.
          unfold bexp_to_fexp.
          eexists; split.
          ** (* #4.2.2.1 Scope *)
             constructor.
             destruct_foralls.
             constructor. 2: 
             {
               scope_solver.
             }
             constructor. 1:
             {
               cbn.
               intros.
               inv H.
             }
             admit.
          ** (* #4.2.2.2 Scope *)
             do_step.
             apply step_refl.
    * (* #5 VTuple *)
      induction H.
      - (* #5.1 Base Step*)
        (* +1 Intro *)
        intros vs Hmap H.
        cbn in *.
        clear f.
        inv H.
        (* +2 FrameStack Proof *)
        exists 2. split. 
        + (* #5.1.1 Scope *)
          constructor.
          scope_solver.
        + (* #5.1.2 Step *)
          do 1 do_step.
          eapply step_trans.
          {
            econstructor.
            {
              congruence.
            }
            constructor.
          }
          apply step_refl.
      - (* #5.2 Inductive Step *)
        (* +1 Intro *)
        clear H0.
        intros vs Hmap H1.
        (* rename [v,vintros.l,vs] *)
        (*v*)
        rename x into v.
        rename H into Hv.
        (*vl*)
        rename l into vl.
        rename IHForall into Hvl.
        (*vs*)
        rename H1 into Hvs.
        (* +2 Eliminate Cases *)
        (* case match [v] *)
        unfold bval_to_fval in *.
        remember 
          (subst_env (measure_val (VTuple (v :: vl))))
          as _f_st.
        simpl in Hvs.
        (*v*)
        case_match.
        2: {
          cbn in Hvs.
          congruence.
        }
        (*inversion*)
        cbn in Hvs.
        inv Hvs.
        (* rename [vl'] *)
        (*vl*)
        rename l into vl'.
        rename H into Hvl'.
        (* +3 Formalize Hypotheses *)
        (* measure reduction [v,vl] *)
        (*v*)
        rewrite measure_val_reduction 
          with (n2 := measure_val v) 
          in Hvl'.
        2-3: cbn; lia.
        (*vl*)
        rewrite measure_val_reduction_list
          with (v2 := VTuple vl) 
          in Hvl'.
        Print measure_list.
        2-3: refold measure_val; unfold measure_list; slia.
        (* destruct expression [v,vl] *)
        (*v*)
        remember
          (fexp_to_fval (bexp_to_fexp f
            (bval_to_bexp (subst_env (measure_val v))
              v)))
          as _v_to_fs.
        destruct _v_to_fs as [v' |]. 2:
        {
          inversion Hvl'.
        }
        clear Heq_v_to_fs.
        (*vl*)
        remember 
          (mapM fexp_to_fval
               (map (λ x : Expression, bexp_to_fexp f x)
                  (map (bval_to_bexp (subst_env (measure_val (VTuple vl)))) vl)))
          as _vl_to_el.
        simpl in Hvl'.
        destruct _vl_to_el as [vl'0 |]. 2:
        {
          inversion Hvl'.
        }
        (* inversion [vl'] *)
        simpl in Hvl'.
        inv Hvl'.
        (* rename [vl'] *)
        rename vl'0 into vl'.
        (* +4 Specialize Hypotheses *)
        pose proof well_formed_map_fs_tuple v' vl' Hmap as Hmap_tuple.
        destruct Hmap_tuple as [Hmap_v Hmap_vl].
        clear Hmap.
        (* specialize [v,vl] *)
        (*v*)
        specialize (Hv [v'] Hmap_v).
        specialize (Hv eq_refl).
        clear Hmap_v.
        (*vl*)
        specialize (Hvl [Syntax.VTuple vl'] Hmap_vl).
        remember 
          (subst_env (measure_val (VTuple vl)))
          as _f_st.
        simpl in Hvl.
        inv Heq_f_st.
        clear H.
        case_match. 2:
        {
          congruence.
        }
        clear H.
        symmetry in Heq_vl_to_el.
        inv Heq_vl_to_el.
        specialize (Hvl eq_refl).
        clear Hmap_vl.
        (* destruct hypothesis [v,vl] *)
        destruct Hv as [kv [Hv_res Hv_step]].
        destruct Hvl as [kvl [Hvl_res Hvl_step]].
        (* +5 Assert Theorem *)
        (* pose proof *)
        pose proof framestack_ident as Hident.
        remember
          (map (erase_names_exp f)
            (map (bval_to_bexp (subst_env (measure_val (VTuple vl))))
              vl))
          as _el.
        remember
          (RValSeq [Syntax.VTuple (v' :: vl')])
          as _r.
        specialize (Hident ITuple _el [] vl' _r v' [] []).
        (* assert *)
        assert 
          (create_result ITuple ([] ++ v' :: vl') [] = 
          Some (_r, []))
          as Hr.
        {
          simpl.
          inv Heq_r.
          reflexivity.
        }
        (* apply *)
        inv Heq_r.
        clear H.
        apply Hident in Hr as Hvl. 2:
        {
          clear - Hvl_step.
          inv Hvl_step.
          remember 
            (subst_env (measure_val (VTuple vl)))
            as _f_st.
          inv H.
          inv H0.
          remember 
            (subst_env (measure_val (VTuple vl)))
            as _f_st.
          inv H. 2:
          {
            cbn. inv H8.
            inv H1.
            {
              apply biforall_nil.
            }
            inv H.
          }
          pose proof framestack_ident_rev _ _ _ _ _ _ H1.
          destruct H.
          destruct H.
          destruct H.
          destruct H.
          simpl in H.
          by inv H.
        }
        clear Hr Hident Hvl_step kvl.
        (* destruct hypothesis [vl] *)
        destruct Hvl as [kvl Hvl_step].
        (* +6 frame stack proof *)
        eexists. split.
        + (* #5.2.1 Scope *)
          clear Hvl_step kvl vl Hv_step kv v f.
          (* destruct_foralls *)
          inv Hv_res.
          inv Hvl_res.
          destruct_foralls.
          (* rename *)
          rename H2 into Hv.
          rename H3 into Hvl.
          rename v' into v.
          rename vl' into vl.
          (* constructor *)
          constructor.
          constructor. 2:
          {
            scope_solver.
          }
          constructor; cbn.
          (*v*)
          destruct i.
          {
            intro.
            exact Hv.
          }
          (*vl*)
          clear Hv v.
          inv Hvl.
          rename H1 into Hvl.
          pose proof scope_vl_succ_id i vl Hvl.
          assumption.
        + (* #5.2.2 Step *)
          clear Hvl_res Hv_res.
          do 2 rmb_sbt_mval_spl_step (VTuple (v :: vl)).
          (*measure reduction [v,vl]*)
          (*v*)
          rewrite measure_val_reduction 
            with (n2 := measure_val v).
          2-3: refold measure_val; unfold measure_list; slia.
          (*vl*)
          rewrite measure_val_reduction_list
            with (v2 := VTuple vl).
          2-3: refold measure_val; unfold measure_list; slia.
          (* step [v,vl] *)
          (*v*)
          eapply transitive_eval.
          {
            eapply frame_indep_core in Hv_step.
            exact Hv_step.
          }
          clear Hv_step kv v.
          rmb_sbt_mval_spl (VTuple vl).
          (*vl*)
          exact Hvl_step.
    * (* #6 VMap *)
      induction H.
      - (* #6.1 Base step *)
        (* +1 Intro *)
        intros vs Hmap H.
        cbn in *.
        clear f.
        inv H.
        (* +2 FrameStack Proof *)
        exists 1; split. 
        + (* #6.1.1 Scope *)
          constructor.
          scope_solver.
        + (* #6.1.2 Frame *)
          do 1 do_step.
          apply step_refl.
      - (* #6.2 Induction step *)
        (* +1 Intro *)
        clear H0.
        intros vs Hmap H1.
        (* destruct value [x] *)
        destruct x.
        simpl in H.
        (* destruct hypothesis [H] *)
        destruct H as [Hv1 Hv2].
        (* rename value [v1,v2,vl]*)
        rename v into v1.
        rename v0 into v2.
        rename l into vl.
        (* rename hypothesis [vl,vs]*)
        rename IHForall into Hvl.
        rename H1 into Hvs.
        (* +2 Eliminate Cases *)
        (* case match [v1,v2,vl] *)
        unfold bval_to_fval in *.
        remember
          (subst_env (measure_val (VMap ((v1, v2) :: vl)))) 
          as _f_st.
        simpl in Hvs.
        (*vl*)
        case_match. 2: {
          cbn in Hvs.
          congruence.
        }
        (* inversion *)
        cbn in Hvs.
        inv Hvs.
        (*v1*)
        case_match. 2:
        {
          inv H.
        }
        (*v2*)
        case_match. 2:
        {
          inv H.
        }
        (* rename [vl']*)
        rename l into vl'.
        rename H into Hvl'.
        (* rename [v1,v2]*)
        (*v1*)
        rename v into v1'.
        rename H0 into Hv1'.
        (*v2*)
        rename v0 into v2'.
        rename H1 into Hv2'.
        (* +3 Formalize Hypotheses *)
        (* - measure reduction [v1,v2,vl] *)
        (*v1*)
        rewrite measure_val_reduction with (n2 := measure_val v1) in Hv1'.
        2-3: refold measure_val; unfold measure_map; slia.
        (*v2*)
        rewrite measure_val_reduction with (n2 := measure_val v2) in Hv2'.
        2-3: refold measure_val; unfold measure_map; slia.
        (*vl*)
        rewrite measure_val_reduction_map with (v2 := VMap vl) in Hvl'.
        2-3: refold measure_val; unfold measure_map; slia.
        (* - clear cases with inversion [v1,v2,vl] *)
        (*v1*)
        remember 
          (fexp_to_fval (bexp_to_fexp f 
            (bval_to_bexp (subst_env (measure_val v1)) 
              v1))) 
          as _v1_to_fs.
        destruct _v1_to_fs as [v1'0 |]. 2:
        {
          inversion Hv1'.
        }
        inv Hv1'.
        clear Heq_v1_to_fs.
        (*v2*)
        remember 
          (fexp_to_fval (bexp_to_fexp f 
            (bval_to_bexp (subst_env (measure_val v2)) 
              v2))) 
          as _v2_to_fs.
        destruct _v2_to_fs as [v2'0 |]. 2:
        {
          inversion Hv2'.
        }
        inv Hv2'.
        clear Heq_v2_to_fs.
        (*vl*)
        remember (map (λ '(x, y0), (bexp_to_fexp f x, bexp_to_fexp f y0))
          (map
             (prod_map (bval_to_bexp (subst_env (measure_val (VMap vl))))
                (bval_to_bexp (subst_env (measure_val (VMap vl))))) vl)) 
          as _vl_to_fs.
        simpl in Hvl'.
        remember 
          (mapM
            (λ '(x, y),
              match fexp_to_fval x with
                | Some x' => match fexp_to_fval y with
                             | Some y' => Some (x', y')
                             | None => None
                             end
                | None => None
                end) _vl_to_fs)
          as _vl_to_el.
        destruct _vl_to_el as [vl'0 |]. 2:
        {
          inversion Hvl'.
        }
        simpl in Hvl'.
        inv Hvl'.
        (* rename [vl']*)
        rename vl'0 into vl'.
        (* +4 Specialize Hypotheses *)
        pose proof well_formed_map_fs_map v1' v2' vl' Hmap as Hmap_map.
        destruct Hmap_map as [Hmap_v1 [Hmap_v2 Hmap_vl]].
        (* - specialize [v0,v1] *)
        (*v1*)
        specialize (Hv1 [v1'] Hmap_v1).
        specialize (Hv1 eq_refl).
        (*v2*)
        specialize (Hv2 [v2'] Hmap_v2).
        specialize (Hv2 eq_refl).
        (*vl*)
        specialize (Hvl [Syntax.VMap vl'] Hmap_vl).
        remember
          (subst_env (measure_val (VMap vl))) 
          as _f_st.
        simpl in Hvl.
        case_match. 2:
        {
          congruence.
        }
        symmetry in Heq_vl_to_el.
        inv Heq_vl_to_el.
        specialize (Hvl eq_refl).
        clear H.
        (* - destruct hypothesis [v1,v2,vl] *)
        destruct Hv1 as [kv1 [Hv1_res Hv1_step]].
        destruct Hv2 as [kv2 [Hv2_res Hv2_step]].
        destruct Hvl as [kvl [Hvl_res Hvl_step]].
        (* +5 Assert Theorem *)
        (* pose proof *)
        pose proof framestack_ident as Hident.
        remember 
          ((map (λ '(x, y), (erase_names_exp f x, erase_names_exp f y))
            (map
               (prod_map
                  (bval_to_bexp (subst_env (measure_val (VMap vl))))
                  (bval_to_bexp (subst_env (measure_val (VMap vl)))))
               vl)))
          as _el.
        Print create_result.
        remember 
          (RValSeq [Syntax.VMap (make_val_map ((v1', v2') :: vl'))]) 
          as _r.
        remember 
          (flatten_list _el)
          as _fel.
        remember 
          (flatten_list vl')
          as _fvl'.
        specialize (Hident IMap _fel [v1'] _fvl' _r v2' [] []).
        (* assert *)
        assert (create_result IMap ([v1'] ++ v2' :: _fvl') [] = Some (_r, [])) as Hr.
        {
          simpl.
          inv Heq_r.
          clear H.
          by rewrite flatten_deflatten.
        }
        (* apply *)
        inv Heq_r.
        clear H.
        apply Hident in Hr as Hvl. 2:
        {
          Check framestack_ident.
          (*clear - Hvl_step. *)
          inv Hvl_step.
          remember 
            (subst_env (measure_val (VMap vl)))
            as _f_st.
          inv H.
          {
            inv H0.
            {
              cbn.
              apply biforall_nil.
            }
            inv H.
          }
          remember 
            (subst_env (measure_val (VMap vl)))
            as _f_st.
          Check framestack_ident_rev.
          pose proof framestack_ident_rev _ _ _ _ _ _ H0.
            destruct H.
            destruct H.
            destruct H.
            destruct H.
            inv H1.
            inv H8.
            cbn in H.
            inv H.
            Search flatten_list list_biforall.
            admit.
        }
        clear Hr Hident Hvl_step kvl Hmap_v1 Hmap_v2 Hmap_vl.
        (* destruct hypothesis [vl] *)
        destruct Hvl as [kvl Hvl_step].
        (* +6 FrameStack Proof *)
        eexists; split.
        + (* #6.2.1 Scope *)
          clear v1 kv1 Hv1_step v2 kv2 Hv2_step vl kvl Hvl_step f Hmap.
          (* destruct_foralls *)
          inv Hv1_res.
          inv Hv2_res.
          inv Hvl_res.
          destruct_foralls.
          (* rename *)
          rename H2 into Hv1.
          rename H3 into Hv2.
          rename H4 into Hvl.
          rename v1' into v1.
          rename v2' into v2.
          rename vl' into vl.
          (* constructor *)
          constructor.
          constructor. 2:
          {
            scope_solver.
          }
          constructor; cbn.
          (*fst*)
          {
            clear Hv2 v2.
            destruct i.
            (*v1*)
            {
              intro.
              exact Hv1.
            }
            clear Hv1 v1.
            (*vl*)
            inv Hvl.
            rename H0 into Hvl.
            clear H2.
            pose proof scope_vl_succ (Val * Val) i vl fst Hvl.
            assumption.
          }
          (*snd*)
          {
            clear Hv1 v1.
            destruct i.
            (*v1*)
            {
              intro.
              exact Hv2.
            }
            clear Hv2 v2.
            (*vl*)
            inv Hvl.
            rename H2 into Hvl.
            clear H0.
            pose proof scope_vl_succ (Val * Val) i vl snd Hvl.
            assumption.
          }
        + (* #6.2.2 Frame *)
          clear Hv1_res Hv2_res Hvl_res.
          rmb_sbt_mval_spl_step (VMap ((v1 ,v2) :: vl)).
          (*measure reduction [v1,v2,vl]*)
          (*v1*)
          rewrite measure_val_reduction 
            with (n2 := measure_val v1)
                 (v := v1).
          2-3: refold measure_val; unfold measure_map; slia.
          (*v2*)
          rewrite measure_val_reduction 
            with (n2 := measure_val v2)
                 (v := v2).
          2-3: refold measure_val; unfold measure_map; slia.
          (*vl*)
          rewrite measure_val_reduction_map
            with (v2 := VMap vl).
          2-3: refold measure_val; unfold measure_map; slia.
          (* step [v1,v2,vl] *)
          (*v1*)
          eapply transitive_eval.
          {
            eapply frame_indep_core in Hv1_step.
            exact Hv1_step.
          }
          clear Hv1_step kv1 v1.
          rmb_sbt_mval_spl_step (VMap vl).
          (*v2*)
          eapply transitive_eval.
          {
            eapply frame_indep_core in Hv2_step.
            exact Hv2_step.
          }
          clear Hv2_step kv2 v2.
          rmb_sbt_mval_spl (VMap vl).
          (*vl*)
          inv Hmap.
          unfold well_formed_map_fs in H1.
          clear H2.
          destruct H1.
          clear H0.
          rewrite <- H in Hvl_step.
          exact Hvl_step.
  Admitted.


End EquivalenceReduction.