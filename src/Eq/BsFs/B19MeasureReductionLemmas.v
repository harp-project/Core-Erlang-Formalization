From CoreErlang.Eq.BsFs Require Export B18MeasureReductionTactics.

Import BigStep.

(* STRUCTURE:
* Help
  - measure_exp_notzero
  - measure_case_eq
  - measure_ext_eq
  - measure_env_eq
* Environment
  - measure_env_rem_keys_le
  - measure_env_rem_vars_le
  - measure_env_rem_fids_le
  - measure_env_rem_exp_ext_fids_le
  - measure_env_rem_val_ext_fids_le
  - measure_env_rem_exp_ext_both_le
  - measure_env_rem_val_ext_both_le
* Value
  - mred_vcons
  - mred_vtuple
  - mred_vmap
  - mred_vclos
  - mred_val
* Expression
  - mred_exp
* Seperate
  - mred_exp_seperate
  - mred_exp_onlyexp
  - mred_exp_onlyenv
* Mappers
  - mred_val_list
  - mred_val_map
  - mred_exp_list
  - mred_exp_map
* Minimum
  - mred_val_min
  - mred_val_list_min
  - mred_val_map_min
  - mred_exp_min
  - mred_exp_onlyexp_min
  - mred_exp_onlyenv_min
  - mred_exp_list_min
  - mred_exp_map_min
  - mred_exp_ext_min
  - mred_exp_list_split_min
  - mred_exp_map_split_min
* Inductive Value
  - mred_vcons_v1
  - mred_vcons_v2
  - mred_v1v2_v1 ?
  - mred_v1v2_v2 ?
  - mred_vtuple_v
  - mred_vtuple_vl
  - mred_vvl_v
  - mred_vvl_vl
  - mred_vmap_v1
  - mred_vmap_v2
  - mred_vmap_vll
  - mred_v1v2vll_v1
  - mred_v1v2vll_v2
  - mred_v1v2vll_vll
* Inductive Expression
  - mred_e_rem_vars
  - mred_eext_e_rem_vars
  - mred_e1e2_e1
  - mred_e1e2_e2
  - mred_e1e2_e2_rem_vars
  - mred_e1e2e3_e1
  - mred_e1e2e3_e2_rem_vars
  - mred_e1e2e3_e3_rem_vars
  - mred_eel_e
  - mred_eel_el
  - mred_e1e2ell_e1
  - mred_e1e2ell_e2
  - mred_e1e2ell_ell
  - mred_expel_exp
  - mred_expel_el
  - mred_eext_ext_rem_both
*)












Section Help.



  Lemma measure_exp_notzero :
    forall e,
      measure_exp e <> 0.
  Proof.
    (* #1 Induction: intro/induction + simpl/congruence *)
    itr.
    ind - e; smp; con.
  Qed.



  Lemma measure_case_eq :
    forall case,
      measure_case case = measure_exp_case measure_exp case.
  Proof.
    (* #1 Trivial: intro/unfold/trival *)
    itr.
    ufl - measure_case measure_exp_case.
    trv.
  Qed.



  Lemma measure_ext_eq :
    forall ext,
      measure_ext ext = measure_exp_ext measure_exp ext.
  Proof.
    (* #1 Trivial: intro/unfold/trival *)
    itr.
    ufl - measure_ext.
    unfold  measure_exp_ext.
    trv.
  Qed.



  Lemma measure_env_eq :
    forall env,
      measure_env env = measure_val_env measure_val env.
  Proof.
    (* #1 Trivial: intro/unfold/trival *)
    itr.
    ufl - measure_env measure_val_env.
    trv.
  Qed.



End Help.












Section Environment.



  Lemma measure_env_rem_keys_le :
    forall env keys,
    measure_env (rem_keys keys env) <= measure_env env.
  Proof.
    (* #1 Induction on Environment: intro/induction + simpl *)
    itr.
    ind - env as [| [k v] env Hle_e1k_e1]: smp.
    (* #2 Pose Cons: remember/pose/subst *)
    rem - env' as Heq_env:
      (rem_keys keys ((k, v) :: env)).
    pse - rem_keys_cons_env as Hcons: keys k v env env' Heq_env.
    sbt.
    (* #3 Destruct Cons: destuct + rewrite *)
    des - Hcons; cwr - H in *.
    * (* #4.1 Assert Le: assert/lia + trv_le_solver *)
      ass - as Hle_e1_e2: trv_le_solver >
        (measure_env env <= measure_env ((k, v) :: env)).
      lia.
    * (* #4.2 Solve by Lia: unfold/simpl/lia *)
      ufl + measure_env in Hle_e1k_e1.
      sli.
  Qed.



  Lemma measure_env_rem_vars_le :
    forall env vars,
    measure_env (rem_vars vars env) <= measure_env env.
  Proof.
    (* #1 Prove by Previus Theorem: intro/unfold/pose *)
    itr.
    ufl - rem_vars.
    bse - measure_env_rem_keys_le.
  Qed.



  Lemma measure_env_rem_fids_le :
    forall env fids,
    measure_env (rem_fids fids env) <= measure_env env.
  Proof.
    (* #1 Prove by Previus Theorem: intro/unfold/pose *)
    itr.
    ufl - rem_fids.
    bse - measure_env_rem_keys_le.
  Qed.



  Lemma measure_env_rem_exp_ext_fids_le :
    forall env ext,
    measure_env (rem_exp_ext_fids ext env) <= measure_env env.
  Proof.
    (* #1 Prove by Previus Theorem: intro/unfold/pose *)
    itr.
    ufl - rem_exp_ext_fids.
    bse - measure_env_rem_fids_le.
  Qed.



  Lemma measure_env_rem_val_ext_fids_le :
    forall env ext,
    measure_env (rem_val_ext_fids ext env) <= measure_env env.
  Proof.
    (* #1 Prove by Previus Theorem: intro/unfold/pose *)
    itr.
    ufl - rem_val_ext_fids.
    bse - measure_env_rem_fids_le.
  Qed.



  Lemma measure_env_rem_exp_ext_both_le :
    forall env vars ext,
    measure_env (rem_exp_ext_both vars ext env) <= measure_env env.
  Proof.
    (* #1 Prove by Previus Theorems: intro/unfold/pose/lia *)
    itr.
    ufl - rem_exp_ext_both.
    pse - measure_env_rem_vars_le as Hvars: env vars.
    pse - measure_env_rem_exp_ext_fids_le as Hext: (rem_vars vars env) ext.
    lia.
  Qed.



  Lemma measure_env_rem_val_ext_both_le :
    forall env vars ext,
    measure_env (rem_val_ext_both vars ext env) <= measure_env env.
  Proof.
    (* #1 Prove by Previus Theorems: intro/unfold/pose/lia *)
    itr.
    ufl - rem_val_ext_both.
    pse - measure_env_rem_vars_le as Hvars: env vars.
    pse - measure_env_rem_val_ext_fids_le as Hext: (rem_vars vars env) ext.
    lia.
  Qed.



End Environment.












Section Value.



  Theorem mred_vcons :
      forall v1 v2 n1 n2,
          measure_val (VCons v1 v2) <= n1
      ->  measure_val (VCons v1 v2) <= n2
      ->  ( measure_val v1 <= n1
        ->  measure_val v1 <= n2
        ->  bval_to_bexp (subst_env n1) v1
          = bval_to_bexp (subst_env n2) v1)
      ->  ( measure_val v2 <= n1
        ->  measure_val v2 <= n2
        ->  bval_to_bexp (subst_env n1) v2
          = bval_to_bexp (subst_env n2) v2)
      ->  bval_to_bexp (subst_env n1) (VCons v1 v2)
        = bval_to_bexp (subst_env n2) (VCons v1 v2).
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - v1 v2 n1 n2 Hle_v1v2_n1 Hle_v1v2_n2 Heq_v1 Heq_v2.
    (* #2 Remember: destruct/simpl/remember *)
    rem - mv1 mv2 mv1v2 as Hmv1 Hmv2 Hmv1v2:
      (measure_val v1)
      (measure_val v2)
      (measure_val (VCons v1 v2)).
    (* #3 Assert: assert *)
    ass_le > (mv1 <= mv1v2) as Hle_v1_v1v2: Hmv1 Hmv1v2.
    ass_le > (mv2 <= mv1v2) as Hle_v2_v1v2: Hmv2 Hmv1v2.
    ass_le_trn > (mv1 <= n1) as Hle_v1_n1: Hle_v1_v1v2 Hle_v1v2_n1.
    ass_le_trn > (mv1 <= n2) as Hle_v1_n2: Hle_v1_v1v2 Hle_v1v2_n2.
    ass_le_trn > (mv2 <= n1) as Hle_v2_n1: Hle_v2_v1v2 Hle_v1v2_n1.
    ass_le_trn > (mv2 <= n2) as Hle_v2_n2: Hle_v2_v1v2 Hle_v1v2_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmv1 Hmv2 Hmv1v2 in *.
    clr + Heq_v1 Heq_v2 Hle_v1_n1 Hle_v1_n2 Hle_v2_n1 Hle_v2_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_v1: Hle_v1_n1 Hle_v1_n2.
    spc - Heq_v2: Hle_v2_n1 Hle_v2_n2.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_v1 Heq_v2.
  Qed.






  Theorem mred_vtuple :
    forall vl n1 n2,
        measure_val (VTuple vl) <= n1
    ->  measure_val (VTuple vl) <= n2
    ->  Forall (fun v =>
            measure_val v <= n1
        ->  measure_val v <= n2
        ->  bval_to_bexp (subst_env n1) v
          = bval_to_bexp (subst_env n2) v)
          vl
    ->  bval_to_bexp (subst_env n1) (VTuple vl)
      = bval_to_bexp (subst_env n2) (VTuple vl).
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - vl n1 n2 Hle_vvl_n1 Hle_vvl_n2 HForall.
    ind - vl as [| v vl Heq_vl]: bmp.
    ivc - HForall as Heq_v HForall: H1 H2.
    (* #2 Remember: destruct/simpl/remember *)
    rem - mv mvl mvvl as Hmv Hmvl Hmvvl:
      (measure_val v)
      (measure_val (VTuple vl))
      (measure_val (VTuple (v :: vl))).
    (* #3 Assert: assert *)
    ass_le > (mv <= mvvl) as Hle_v_vvl: Hmv Hmvvl.
    ass_le > (mvl <= mvvl) as Hle_vl_vvl: Hmvl Hmvvl.
    ass_le_trn > (mv <= n1) as Hle_v_n1: Hle_v_vvl Hle_vvl_n1.
    ass_le_trn > (mv <= n2) as Hle_v_n2: Hle_v_vvl Hle_vvl_n2.
    ass_le_trn > (mvl <= n1) as Hle_vl_n1: Hle_vl_vvl Hle_vvl_n1.
    ass_le_trn > (mvl <= n2) as Hle_vl_n2: Hle_vl_vvl Hle_vvl_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmv Hmvl Hmvvl in *.
    clr + Heq_v Heq_vl HForall Hle_v_n1 Hle_v_n2 Hle_vl_n1 Hle_vl_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_v: Hle_v_n1 Hle_v_n2.
    spc - Heq_vl: Hle_vl_n1 Hle_vl_n2 HForall.
    inj - Heq_vl as Heq_vl.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_v Heq_vl.
  Qed.






  Theorem mred_vmap :
    forall vll n1 n2,
        measure_val (VMap vll) <= n1
    ->  measure_val (VMap vll) <= n2
    ->  Forall (fun v =>
           (measure_val v.1 <= n1
        ->  measure_val v.1 <= n2
        ->  bval_to_bexp (subst_env n1) v.1
          = bval_to_bexp (subst_env n2) v.1)
        /\ (measure_val v.2 <= n1
        ->  measure_val v.2 <= n2
        ->  bval_to_bexp (subst_env n1) v.2
          = bval_to_bexp (subst_env n2) v.2))
          vll
    ->  bval_to_bexp (subst_env n1) (VMap vll)
      = bval_to_bexp (subst_env n2) (VMap vll).
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - vll n1 n2 Hle_vvll_n1 Hle_vvll_n2 HForall.
    ind - vll as [| v vll Heq_vll]: bmp.
    ivc - HForall as Heq_v HForall: H1 H2.
    (* #2 Remember: destruct/simpl/remember *)
    des - v as [v1 v2].
    des - Heq_v as [Heq_v1 Heq_v2].
    smp - Heq_v1 Heq_v2.
    rem - mv1 mv2 mv mvll mvvll as Hmv1 Hmv2 Hmv Hmvll Hmvvll:
      (measure_val v1)
      (measure_val v2)
      (measure_val v1 + measure_val v2)
      (measure_val (VMap vll))
      (measure_val (VMap ((v1, v2) :: vll))).
    (* #3 Assert: assert *)
    ass_le > (mv1 <= mv) as Hle_v1_v: Hmv1 Hmv.
    ass_le > (mv2 <= mv) as Hle_v2_v: Hmv2 Hmv.
    ass_le > (mv <= mvvll) as Hle_v_vvll: Hmv Hmvvll.
    ass_le > (mvll <= mvvll) as Hle_vll_vvll: Hmvll Hmvvll.
    ass_le_trn > (mv1 <= n1) as Hle_v1_n1: Hle_v1_v Hle_v_vvll Hle_vvll_n1.
    ass_le_trn > (mv1 <= n2) as Hle_v1_n2: Hle_v1_v Hle_v_vvll Hle_vvll_n2.
    ass_le_trn > (mv2 <= n1) as Hle_v2_n1: Hle_v2_v Hle_v_vvll Hle_vvll_n1.
    ass_le_trn > (mv2 <= n2) as Hle_v2_n2: Hle_v2_v Hle_v_vvll Hle_vvll_n2.
    ass_le_trn > (mvll <= n1) as Hle_vll_n1: Hle_vll_vvll Hle_vvll_n1.
    ass_le_trn > (mvll <= n2) as Hle_vll_n2: Hle_vll_vvll Hle_vvll_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmv1 Hmv2 Hmv Hmvll Hmvvll in *.
    clr + Heq_v1 Heq_v2 Heq_vll HForall
      Hle_v1_n1 Hle_v1_n2 Hle_v2_n1 Hle_v2_n2 Hle_vll_n1 Hle_vll_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_v1: Hle_v1_n1 Hle_v1_n2.
    spc - Heq_v2: Hle_v2_n1 Hle_v2_n2.
    spc - Heq_vll: Hle_vll_n1 Hle_vll_n2 HForall.
    inj - Heq_vll as Heq_vll.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_v1 Heq_v2 Heq_vll.
  Qed.






  Theorem mred_vclos :
    forall env ext id vars e fid n1 n2,
        measure_val (VClos env ext id vars e fid) <= n1
    ->  measure_val (VClos env ext id vars e fid) <= n2
    ->  Forall (fun x =>
            measure_val x.2 <= n1
        ->  measure_val x.2 <= n2
        ->  bval_to_bexp (subst_env n1) x.2
          = bval_to_bexp (subst_env n2) x.2)
          env
    ->  bval_to_bexp (subst_env n1) (VClos env ext id vars e fid)
      = bval_to_bexp (subst_env n2) (VClos env ext id vars e fid).
  Proof.
    itr - env ext id vars e fid n1 n2 Hle_env_n1 Hle_env_n2 HForall.
    (* Problem: HForall only talks about env, but not of e & ext *)
    admit.
    (* Not Provable / Not True *)
  Admitted.






  Theorem mred_val :
    forall v n1 n2,
        measure_val v <= n1
    ->  measure_val v <= n2
    ->  bval_to_bexp (subst_env n1) v
      = bval_to_bexp (subst_env n2) v.
  Proof.
    (* #1 Value Induction: intro/induction + cbn *)
    itr - v n1 n2 Hn1 Hn2.
    ind ~ ind_val - v :- sbn.
    (* #2 Cons: pose *)
    1: bse - mred_vcons:  v1 v2 n1 n2
                          Hn1 Hn2 IHv1 IHv2.
    (* #3 Tuple: pose *)
    2: bse - mred_vtuple: l n1 n2
                          Hn1 Hn2 H.
    (* #4 Map: pose *)
    2: bse - mred_vmap:   l n1 n2
                          Hn1 Hn2 H.
    (* #5 Closure: pose *)
    bse - mred_vclos:     ref ext id params body funid n1 n2
                          Hn1 Hn2 H.
  Qed.



End Value.












Section Expression.



  Theorem mred_exp :
    forall env e n1 n2,
        measure_env_exp env e <= n1
    ->  measure_env_exp env e <= n2
    ->  subst_env n1 env e
      = subst_env n2 env e.
  Proof.
    (* Not Provable / Not True *)
  Admitted.



End Expression.












Section Separate.



  Theorem mred_exp_separate :
    forall env e ne1 ne2 nenv1 nenv2,
        measure_exp e <= ne1
    ->  measure_exp e <= ne2
    ->  measure_env env <= nenv1
    ->  measure_env env <= nenv2
    ->  subst_env (ne1 + nenv1) env e
      = subst_env (ne2 + nenv2) env e.
  Proof.
    (* #1 Pose Larger or Equal Mono: intro/pose + clear *)
    itr - env e ne1 ne2 nenv1 nenv2 Hle_e1 Hle_e2 Hle_env1 Hle_env2.
    psc - Nat.add_le_mono as Hle1:
      (measure_exp e) ne1
      (measure_env env) nenv1
      Hle_e1 Hle_env1.
    psc - Nat.add_le_mono as Hle2:
      (measure_exp e) ne2
      (measure_env env) nenv2
      Hle_e2 Hle_env2.
    (* #2 Prove by Previus Theorem: pose/unfold/specialize *)
    pse - mred_exp as Heq: env e (ne1 + nenv1) (ne2 + nenv2).
    ufl - measure_env_exp in Heq.
    bpe - Heq: Hle1 Hle2.
  Qed.



  Theorem mred_exp_only_exp :
    forall env e n1 n2,
        measure_exp e <= n1
    ->  measure_exp e <= n2
    ->  subst_env (n1 + measure_env env) env e
      = subst_env (n2 + measure_env env) env e.
  Proof.
    (* #1 Prove by Previus Theorem: intro/assert/pose *)
    itr - env e n1 n2 Hle1 Hle2.
    ass > (measure_env env <= measure_env env) as Hle_env: lia.
    bse - mred_exp_separate:  env e n1 n2 (measure_env env) (measure_env env)
                              Hle1 Hle2 Hle_env Hle_env.
  Qed.



  Theorem mred_exp_only_env :
    forall env e n1 n2,
        measure_env env <= n1
    ->  measure_env env <= n2
    ->  subst_env (measure_exp e + n1) env e
      = subst_env (measure_exp e + n2) env e.
  Proof.
    (* #1 Prove by Previus Theorem: intro/assert/pose *)
    itr - env e n1 n2 Hle1 Hle2.
    ass > (measure_exp e <= measure_exp e) as Hle_e: lia.
    bse - mred_exp_separate:  env e (measure_exp e) (measure_exp e) n1 n2 
                              Hle_e Hle_e Hle1 Hle2.
  Qed.



End Separate.












Section Mappers.



  Theorem mred_val_list :
    forall vl n1 n2,
        list_sum (map measure_val vl) <= n1
    ->  list_sum (map measure_val vl) <= n2
    ->  map (bval_to_bexp (subst_env n1)) vl
      = map (bval_to_bexp (subst_env n2)) vl.
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - vl n1 n2 Hle_vvl_n1 Hle_vvl_n2.
    ind - vl as [| v vl Heq_vl]: bmp.
    (* #2 Remember: destruct/simpl/remember *)
    rem - mv mvl mvvl as Hmv Hmvl Hmvvl:
      (measure_val v)
      (list_sum (map measure_val vl))
      (list_sum (map measure_val (v :: vl))).
    (* #3 Assert: assert *)
    ass_le > (mv <= mvvl) as Hle_v_vvl: Hmv Hmvvl.
    ass_le > (mvl <= mvvl) as Hle_vl_vvl: Hmvl Hmvvl.
    ass_le_trn > (mv <= n1) as Hle_v_n1: Hle_v_vvl Hle_vvl_n1.
    ass_le_trn > (mv <= n2) as Hle_v_n2: Hle_v_vvl Hle_vvl_n2.
    ass_le_trn > (mvl <= n1) as Hle_vl_n1: Hle_vl_vvl Hle_vvl_n1.
    ass_le_trn > (mvl <= n2) as Hle_vl_n2: Hle_vl_vvl Hle_vvl_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmv Hmvl Hmvvl in *.
    clr + Heq_vl Hle_v_n1 Hle_v_n2 Hle_vl_n1 Hle_vl_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_vl: Hle_vl_n1 Hle_vl_n2.
    psc - mred_val as Heq_v: v n1 n2 Hle_v_n1 Hle_v_n2.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_v Heq_vl.
  Qed.






  Theorem mred_val_map :
    forall vll n1 n2,
        list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vll)
          <= n1
    ->  list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vll)
          <= n2
    ->  map
          (prod_map
            (bval_to_bexp (subst_env n1))
            (bval_to_bexp (subst_env n1)))
          vll
      = map
          (prod_map
            (bval_to_bexp (subst_env n2))
            (bval_to_bexp (subst_env n2)))
          vll.
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - vll n1 n2 Hle_vvll_n1 Hle_vvll_n2.
    ind - vll as [| v vll Heq_vll]: bmp.
    (* #2 Remember: destruct/simpl/remember *)
    des - v as [v1 v2].
    rem - mv1 mv2 mv mvll mvvll as Hmv1 Hmv2 Hmv Hmvll Hmvvll:
      (measure_val v1)
      (measure_val v2)
      (measure_val v1 + measure_val v2)
      (list_sum (map (fun '(x, y) => measure_val x + measure_val y) vll))
      (list_sum (map (fun '(x, y) => measure_val x + measure_val y)
        ((v1, v2) :: vll))).
    (* #3 Assert: assert *)
    ass_le > (mv1 <= mv) as Hle_v1_v: Hmv1 Hmv.
    ass_le > (mv2 <= mv) as Hle_v2_v: Hmv2 Hmv.
    ass_le > (mv <= mvvll) as Hle_v_vvll: Hmv Hmvvll.
    ass_le > (mvll <= mvvll) as Hle_vll_vvll: Hmvll Hmvvll.
    ass_le_trn > (mv1 <= n1) as Hle_v1_n1: Hle_v1_v Hle_v_vvll Hle_vvll_n1.
    ass_le_trn > (mv1 <= n2) as Hle_v1_n2: Hle_v1_v Hle_v_vvll Hle_vvll_n2.
    ass_le_trn > (mv2 <= n1) as Hle_v2_n1: Hle_v2_v Hle_v_vvll Hle_vvll_n1.
    ass_le_trn > (mv2 <= n2) as Hle_v2_n2: Hle_v2_v Hle_v_vvll Hle_vvll_n2.
    ass_le_trn > (mvll <= n1) as Hle_vll_n1: Hle_vll_vvll Hle_vvll_n1.
    ass_le_trn > (mvll <= n2) as Hle_vll_n2: Hle_vll_vvll Hle_vvll_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmv1 Hmv2 Hmv Hmvll Hmvvll in *.
    clr + Heq_vll Hle_v1_n1 Hle_v1_n2 Hle_v2_n1 Hle_v2_n2 Hle_vll_n1 Hle_vll_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_vll: Hle_vll_n1 Hle_vll_n2.
    psc - mred_val as Heq_v1: v1 n1 n2 Hle_v1_n1 Hle_v1_n2.
    psc - mred_val as Heq_v2: v2 n1 n2 Hle_v2_n1 Hle_v2_n2.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_v1 Heq_v2 Heq_vll.
  Qed.






  Theorem mred_exp_list :
    forall env el n1 n2,
        list_sum (map measure_exp el) + measure_env env <= n1
    ->  list_sum (map measure_exp el) + measure_env env <= n2
    ->  map (subst_env n1 env) el
      = map (subst_env n2 env) el.
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - env el n1 n2 Hle_eel_n1 Hle_eel_n2.
    ind - el as [| e el Heq_el]: bmp.
    (* #2 Remember: destruct/simpl/remember *)
    rem - menv me mel meel as Hmenv Hme Hmel Hmeel:
      (measure_env env)
      (measure_exp e)
      (list_sum (map measure_exp el))
      (list_sum (map measure_exp (e :: el))).
    (* #3 Assert: assert *)
    ass_le > (me + menv <= meel + menv) as Hle_e_eel: Hme Hmeel Hmenv.
    ass_le > (mel + menv <= meel + menv) as Hle_el_eel: Hmel Hmeel Hmenv.
    ass_le_trn > (me + menv <= n1) as Hle_e_n1: Hle_e_eel Hle_eel_n1.
    ass_le_trn > (me + menv <= n2) as Hle_e_n2: Hle_e_eel Hle_eel_n2.
    ass_le_trn > (mel + menv <= n1) as Hle_el_n1: Hle_el_eel Hle_eel_n1.
    ass_le_trn > (mel + menv <= n2) as Hle_el_n2: Hle_el_eel Hle_eel_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmenv Hme Hmel Hmeel in *.
    clr + Heq_el Hle_e_n1 Hle_e_n2 Hle_el_n1 Hle_el_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_el: Hle_el_n1 Hle_el_n2.
    psc - mred_exp as Heq_e: env e n1 n2 Hle_e_n1 Hle_e_n2.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_e Heq_el.
  Qed.






  Theorem mred_exp_map :
    forall env ell n1 n2,
        list_sum (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) ell)
           + measure_env env <= n1
    ->  list_sum (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) ell)
          + measure_env env <= n2
    ->  map
          (prod_map
            (subst_env n1 env)
            (subst_env n1 env))
          ell
      = map
          (prod_map
            (subst_env n2 env)
            (subst_env n2 env))
          ell.
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - env ell n1 n2 Hle_eell_n1 Hle_eell_n2.
    ind - ell as [| e ell Heq_ell]: bmp.
    (* #2 Remember: destruct/simpl/remember *)
    des - e as [e1 e2].
    rem - menv me1 me2 me mell meell as Hmenv Hme1 Hme2 Hme Hmell Hmeell:
      (measure_env env)
      (measure_exp e1)
      (measure_exp e2)
      (measure_exp e1 + measure_exp e2)
      (list_sum (map (fun '(x, y) => measure_exp x + measure_exp y) ell))
      (list_sum (map (fun '(x, y) => measure_exp x + measure_exp y)
        ((e1, e2) :: ell))).
    (* #3 Assert: assert *)
    ass_le > (me1 + menv <= me + menv) as Hle_e1_e: Hme1 Hme Hmenv.
    ass_le > (me2 + menv <= me + menv) as Hle_e2_e: Hme2 Hme Hmenv.
    ass_le > (me + menv <= meell + menv) as Hle_e_eell: Hme Hmeell Hmenv.
    ass_le > (mell + menv <= meell + menv) as Hle_ell_eell: Hmell Hmeell Hmenv.
    ass_le_trn > (me1 + menv <= n1) as Hle_e1_n1: Hle_e1_e Hle_e_eell Hle_eell_n1.
    ass_le_trn > (me1 + menv <= n2) as Hle_e1_n2: Hle_e1_e Hle_e_eell Hle_eell_n2.
    ass_le_trn > (me2 + menv <= n1) as Hle_e2_n1: Hle_e2_e Hle_e_eell Hle_eell_n1.
    ass_le_trn > (me2 + menv <= n2) as Hle_e2_n2: Hle_e2_e Hle_e_eell Hle_eell_n2.
    ass_le_trn > (mell + menv <= n1) as Hle_ell_n1: Hle_ell_eell Hle_eell_n1.
    ass_le_trn > (mell + menv <= n2) as Hle_ell_n2: Hle_ell_eell Hle_eell_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmenv Hme1 Hme2 Hme Hmell Hmeell in *.
    clr + Heq_ell Hle_e1_n1 Hle_e1_n2 Hle_e2_n1 Hle_e2_n2 Hle_ell_n1 Hle_ell_n2.
    (* #5 Specialize: specialize/pose *)
    spc - Heq_ell: Hle_ell_n1 Hle_ell_n2.
    psc - mred_exp as Heq_e1: env e1 n1 n2 Hle_e1_n1 Hle_e1_n2.
    psc - mred_exp as Heq_e2: env e2 n1 n2 Hle_e2_n1 Hle_e2_n2.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_e1 Heq_e2 Heq_ell.
  Qed.



  (* NOT USED *)
  Theorem mred_exp_ext :
    forall env (ext : list (FunctionIdentifier * (list Var * Expression)))
      n1 n2,
        measure_ext ext + measure_env env <= n1
    ->  measure_ext ext + measure_env env <= n2
    ->  map
          (fun '(fid, (vars, body)) => (fid, (vars, subst_env n1 env body)))
          ext
      = map
          (fun '(fid, (vars, body)) => (fid, (vars, subst_env n2 env body)))
          ext.
  Proof.
    (* #1 Intro: intro/induction + smp *)
    itr - env ext n1 n2 Hle_eext_n1 Hle_eext_n2.
    ind - ext as [| [f [v e]] ext Heq_ext]: smp.
    (* #2 Simplify: unfold/simpl/rewrite *)
    unfold measure_ext in *.
    smp ~ map - Hle_eext_n1.
    smp ~ map - Hle_eext_n2.
    rwr - cons_app in *.
    rwr - list_sum_app in *.
    smp - Hle_eext_n1 Hle_eext_n2.
    rwl - Nat.add_assoc in *.
    rwr - Nat.add_0_r in *.
    rwr - Nat.add_assoc in *.
    smp ~ map.
    (* #3 Remember: remember *)
    rem - menv me mext as Hmenv Hme Hmext:
      (measure_env env)
      (measure_exp e)
      (list_sum (map (measure_exp ∘ snd ∘ snd) ext)).
    (* #4 Assert: assert/ass_le_trn + rewrite/lia *)
    ass - as Hle_e_eext: rwr - Hmenv Hme Hmext; lia >
      (me + menv <= me + mext + menv).
    ass - as Hle_ext_eext: rwr - Hmenv Hme Hmext; lia >
      (mext + menv <= me + mext + menv).
    ass_le_trn > (me + menv <= n1) as Hle_e_n1: Hle_e_eext Hle_eext_n1.
    ass_le_trn > (me + menv <= n2) as Hle_e_n2: Hle_e_eext Hle_eext_n2.
    ass_le_trn > (mext + menv <= n1) as Hle_ext_n1: Hle_ext_eext Hle_eext_n1.
    ass_le_trn > (mext + menv <= n2) as Hle_ext_n2: Hle_ext_eext Hle_eext_n2.
    (* #5 Clear: rewrite/clear *)
    cwr - Hmenv Hme Hmext in *.
    clr + Heq_ext Hle_e_n1 Hle_e_n2 Hle_ext_n1 Hle_ext_n2.
    (* #6 Specialize: pose/specialize*)
    psc - mred_exp as Heq_e: env e n1 n2 Hle_e_n1 Hle_e_n2.
    spc - Heq_ext: Hle_ext_n1 Hle_ext_n2.
    (* #7 Rewrite: rewrite + reflexivity *)
    bwr - Heq_e Heq_ext.
  Qed.



End Mappers.












Section Minimum.



  Theorem mred_val_min :
    forall v n,
        measure_val v <= n
    ->  bval_to_bexp (subst_env n) v
    =   bval_to_bexp (subst_env (measure_val v)) v.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr - v n Hle1.
    mred_solver - v n Hle1 Hle2:
      mred_val
      (measure_val v)
      (measure_val v).
  Qed.






  Theorem mred_val_list_min :
    forall vl n,
        list_sum (map measure_val vl) <= n
    ->  map (bval_to_bexp (subst_env n)) vl
      = map (bval_to_bexp (subst_env (list_sum (map measure_val vl)))) vl.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr - vl n Hle1.
    mred_solver - vl n Hle1 Hle2:
      mred_val_list
      (list_sum (map measure_val vl)).
  Qed.






  Theorem mred_val_map_min :
    forall vll n,
        list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vll)
          <= n
    ->  map
          (prod_map
            (bval_to_bexp (subst_env n))
            (bval_to_bexp (subst_env n)))
          vll
      = map
          (prod_map
            (bval_to_bexp
              (subst_env
                (list_sum
                  (map
                    (fun '(x, y) => (measure_val x) + (measure_val y))
                    vll))))
            (bval_to_bexp
              (subst_env
                (list_sum
                  (map
                    (fun '(x, y) => (measure_val x) + (measure_val y))
                    vll)))))
          vll.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr - vll n Hle1.
    mred_solver - vll n Hle1 Hle2:
      mred_val_map
      (list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vll)).
  Qed.






  Theorem mred_exp_min :
    forall env e n,
        measure_env_exp env e <= n
    ->  subst_env n env e
    =   subst_env (measure_env_exp env e) env e.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr -  env e n Hle1.
    mred_solver - env e n Hle1 Hle2:
      mred_exp
      (measure_env_exp env e).
  Qed.






  Theorem mred_exp_only_exp_min :
    forall env e n m,
        measure_exp e <= n
    ->  measure_env env <= m
    ->  subst_env (n + m) env e
    =   subst_env (measure_exp e + m) env e.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr -  env e n m Hle_e Hle_env.
    app - mred_exp_separate; lia.
  Qed.






  Theorem mred_exp_only_env_min :
    forall env e n m,
        measure_exp e <= n
    ->  measure_env env <= m
    ->  subst_env (n + m) env e
    =   subst_env (n + measure_env env) env e.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr -  env e n m Hle_e Hle_env.
    app - mred_exp_separate; lia.
  Qed.





  Theorem mred_exp_list_min :
    forall env el n,
        list_sum (map measure_exp el) + measure_env env <= n
    ->  map (subst_env n env) el
      = map (subst_env (list_sum (map measure_exp el) + measure_env env) env)
         el.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr -  env el n Hle1.
    mred_solver - env el n Hle1 Hle2:
      mred_exp_list
      (list_sum (map measure_exp el) + measure_env env).
  Qed.






  Theorem mred_exp_map_min :
    forall env ell n,
        list_sum (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) ell)
           + measure_env env <= n
    ->  map
          (prod_map
            (subst_env n env)
            (subst_env n env))
          ell
      = map
          (prod_map
            (subst_env
              (list_sum
                (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) ell)
                + measure_env env)
              env)
            (subst_env
              (list_sum
                (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) ell)
                + measure_env env)
              env))
          ell.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr -  env ell n Hle1.
    mred_solver - env ell n Hle1 Hle2:
      mred_exp_map
      (list_sum (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) ell)
        + measure_env env).
  Qed.






  (* NOT USED *)
  Theorem mred_exp_ext_min :
    forall env (ext : list (FunctionIdentifier * (list Var * Expression))) n,
        measure_ext ext + measure_env env <= n
    ->  map
          (fun '(fid, (vars, body)) => (fid, (vars, subst_env n env body)))
          ext
      = map
          (fun '(fid, (vars, body)) =>
            (fid, (vars, subst_env (measure_ext ext + measure_env env) env body)))
          ext.
  Proof.
    (* #1 Measure Reduction Solver: intro/apply + lia *)
    itr -  env ext n Hle.
    app - mred_exp_ext; lia.
  Qed.






  Theorem mred_exp_list_split_min :
    forall fns env el1 el2,
      map
        (bexp_to_fexp fns)
        (map
          (subst_env
            (measure_list measure_exp (el1 ++ el2) + measure_env env)
            env)
          (el1 ++ el2))
    = map
        (bexp_to_fexp fns)
        (map
          (subst_env
            (measure_list measure_exp el1 + measure_env env)
            env)
          el1)
      ++
      map
        (bexp_to_fexp fns)
        (map
          (subst_env
            (measure_list measure_exp el2 + measure_env env)
            env)
          el2).
  Proof.
    (* #1 Intro: intro *)
    itr.
    (* #2 Rewrite Applicative: rewrite *)
    do 2 rwr - map_app.
    (* #3 Measure Reduction: rewrite *)
    rewrite mred_exp_list_min with (el := el1).
    rewrite mred_exp_list_min with (el := el2).
    (* #4 Trivial: trv_le_solver/trivial*)
    2-3: trv_le_solver.
    trv.
  Qed.






  Theorem mred_exp_map_split_min :
    forall fns env ell1 ell2,
      map
        (prod_map
          (bexp_to_fexp fns)
          (bexp_to_fexp fns))
        (map
          (prod_map
            (subst_env
              (measure_map measure_exp (ell1 ++ ell2) + measure_env env)
              env)
            (subst_env
              (measure_map measure_exp (ell1 ++ ell2) + measure_env env)
              env))
          (ell1 ++ ell2))
    = map
        (prod_map
          (bexp_to_fexp fns)
          (bexp_to_fexp fns))
        (map
          (prod_map
            (subst_env
              (measure_map measure_exp ell1 + measure_env env)
              env)
            (subst_env
              (measure_map measure_exp ell1 + measure_env env)
              env))
          ell1)
      ++
      map
        (prod_map
          (bexp_to_fexp fns)
          (bexp_to_fexp fns))
        (map
          (prod_map
            (subst_env
              (measure_map measure_exp ell2 + measure_env env)
              env)
            (subst_env
              (measure_map measure_exp ell2 + measure_env env)
              env))
          ell2).
  Proof.
    (* #1 Intro: intro *)
    itr.
    (* #2 Rewrite Applicative: rewrite *)
    do 2 rwr - map_app.
    (* #3 Measure Reduction: rewrite *)
    rewrite mred_exp_map_min with (ell := ell1).
    rewrite mred_exp_map_min with (ell := ell2).
    (* #4 Trivial: trv_le_solver/trivial*)
    2-3: trv_le_solver.
    trv.
  Qed.



End Minimum.











Section Inductive_Value.



  Theorem mred_vcons_v1 :
    forall v1 v2,
      bval_to_bexp (subst_env (measure_val (VCons v1 v2))) v1
    = bval_to_bexp (subst_env (measure_val v1)) v1.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - v1 Hle:
      mred_val_min
      (measure_val v1)
      (measure_val (VCons v1 v2)).
  Qed.



  Theorem mred_vcons_v2 :
    forall v1 v2,
      bval_to_bexp (subst_env (measure_val (VCons v1 v2))) v2
    = bval_to_bexp (subst_env (measure_val v2)) v2.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - v2 Hle:
      mred_val_min
      (measure_val v2)
      (measure_val (VCons v1 v2)).
  Qed.






  Theorem mred_v1v2_v1 :
    forall v1 v2,
      bval_to_bexp (subst_env (measure_val v1 + measure_val v2)) v1
    = bval_to_bexp (subst_env (measure_val v1)) v1.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - v1 Hle:
      mred_val_min
      (measure_val v1)
      (measure_val v1 + measure_val v2).
  Qed.



  Theorem mred_v1v2_v2 :
    forall v1 v2,
      bval_to_bexp (subst_env (measure_val v1 + measure_val v2)) v2
    = bval_to_bexp (subst_env (measure_val v2)) v2.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - v2 Hle:
      mred_val_min
      (measure_val v2)
      (measure_val v1 + measure_val v2).
  Qed.









  Theorem mred_vtuple_v :
    forall v vl,
      bval_to_bexp (subst_env (measure_val (VTuple (v :: vl)))) v
    = bval_to_bexp (subst_env (measure_val v)) v.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - v Hle:
      mred_val_min
      (measure_val v)
      (measure_val (VTuple (v :: vl))).
  Qed.



  Theorem mred_vtuple_vl :
    forall v vl,
      map (bval_to_bexp (subst_env (measure_val (VTuple (v :: vl))))) vl
    = map (bval_to_bexp (subst_env (measure_val (VTuple vl)))) vl.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - vl Hle1 Hle2:
      mred_val_list
      (list_sum (map measure_val vl))
      (measure_val (VTuple vl))
      (measure_val (VTuple (v :: vl))).
  Qed.






  Theorem mred_vvl_v :
    forall v vl,
      bval_to_bexp (subst_env (measure_val v + measure_list measure_val vl)) v
    = bval_to_bexp (subst_env (measure_val v)) v.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - v Hle:
      mred_val_min
      (measure_val v)
      (measure_val v + measure_list measure_val vl).
  Qed.



  Theorem mred_vvl_vl :
    forall v vl,
      map
        (bval_to_bexp
          (subst_env (measure_val v + measure_list measure_val vl))) vl
    = map (bval_to_bexp (subst_env (measure_list measure_val vl))) vl.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - vl Hle:
      mred_val_list_min
      (measure_list measure_val vl)
      (measure_val v + measure_list measure_val vl).
  Qed.









  Theorem mred_vmap_v1 :
    forall v1 v2 vll,
      bval_to_bexp (subst_env (measure_val (VMap ((v1, v2) :: vll)))) v1
    = bval_to_bexp (subst_env (measure_val v1)) v1.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - v1 Hle:
      mred_val_min
      (measure_val v1)
      (measure_val (VMap ((v1, v2) :: vll))).
  Qed.



  Theorem mred_vmap_v2 :
    forall v1 v2 vll,
      bval_to_bexp (subst_env (measure_val (VMap ((v1, v2) :: vll)))) v2
    = bval_to_bexp (subst_env (measure_val v2)) v2.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - v2 Hle:
      mred_val_min
      (measure_val v2)
      (measure_val (VMap ((v1, v2) :: vll))).
  Qed.



  Theorem mred_vmap_vll :
    forall v1 v2 vll,
      map
        (prod_map
          (bval_to_bexp (subst_env (measure_val (VMap ((v1, v2) :: vll)))))
          (bval_to_bexp (subst_env (measure_val (VMap ((v1, v2) :: vll))))))
        vll
    =
      map
        (prod_map
          (bval_to_bexp (subst_env (measure_val (VMap vll))))
          (bval_to_bexp (subst_env (measure_val (VMap vll)))))
        vll.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - vll Hle1 Hle2:
      mred_val_map
      (list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vll))
      (measure_val (VMap vll))
      (measure_val (VMap ((v1, v2) :: vll))).
  Qed.






  Theorem mred_v1v2vll_v1 :
    forall v1 v2 vll,
      bval_to_bexp
        (subst_env
          (measure_val v1 + measure_val v2 + measure_map measure_val vll)) v1
    = bval_to_bexp (subst_env (measure_val v1)) v1.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - v1 Hle:
      mred_val_min
      (measure_val v1)
      (measure_val v1 + measure_val v2 + measure_map measure_val vll).
  Qed.



  Theorem mred_v1v2vll_v2 :
    forall v1 v2 vll,
      bval_to_bexp
        (subst_env
          (measure_val v1 + measure_val v2 + measure_map measure_val vll)) v2
    = bval_to_bexp (subst_env (measure_val v2)) v2.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - v2 Hle:
      mred_val_min
      (measure_val v2)
      (measure_val v1 + measure_val v2 + measure_map measure_val vll).
  Qed.



  Theorem mred_v1v2vll_vll :
    forall v1 v2 vll,
      map
        (prod_map
          (bval_to_bexp
            (subst_env
              (measure_val v1 + measure_val v2 + measure_map measure_val vll)))
          (bval_to_bexp
            (subst_env
              (measure_val v1 + measure_val v2 + measure_map measure_val vll))))
        vll
    =
      map
        (prod_map
          (bval_to_bexp (subst_env (measure_map measure_val vll)))
          (bval_to_bexp (subst_env (measure_map measure_val vll))))
        vll.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - vll Hle:
      mred_val_map_min
      (measure_map measure_val vll)
      (measure_val v1 + measure_val v2 + measure_map measure_val vll).
  Qed.



End Inductive_Value.












Section Inductive_Expression.



  Theorem mred_e_rem_vars :
    forall vars env e,
      subst_env (measure_exp e + measure_env env)
        (rem_vars vars env) e
    = subst_env (measure_env_exp (rem_vars vars env) e)
        (rem_vars vars env) e.
  Proof.
    (* #1 Measure Reduction Environment: intro/assert/pose/rewrite
      + lia/clear/trivial *)
    itr.
    ass > (measure_exp e <= measure_exp e) as Hle_e: lia.
    pse - measure_env_rem_vars_le as Hle_env: env vars.
    psc - mred_exp_only_env_min as Heq_env: (rem_vars vars env) e
      (measure_exp e) (measure_env env)
      Hle_e Hle_env.
    bwr - Heq_env.
  Qed.



  Theorem mred_eext_e_rem_vars :
    forall vars env e
      (ext : list (nat * FunctionIdentifier * FunctionExpression)),
      subst_env
        (measure_exp e + measure_exp_ext measure_exp ext + measure_env env)
        (rem_vars vars env) e
    = subst_env (measure_env_exp (rem_vars vars env) e)
        (rem_vars vars env) e.
  Proof.
    (* #1 Measure Reduction Separate: intro/pose/apply + lia/assumption *)
    itr.
    pse - measure_env_rem_vars_le as Hle_env: env vars.
    app - mred_exp_separate; lia + asm.
  Qed.



  Theorem mred_eext_e_rem_exp_ext_fids :
    forall ext env e,
      subst_env
        (measure_exp e + measure_exp_ext measure_exp ext + measure_env env)
        (rem_exp_ext_fids ext env) e
    = subst_env (measure_env_exp (rem_exp_ext_fids ext env) e)
        (rem_exp_ext_fids ext env) e.
  Proof.
    (* #1 Measure Reduction Separate: intro/pose/apply + lia/assumption *)
    itr.
    app - mred_exp_separate; try lia.
    app - measure_env_rem_exp_ext_fids_le.
  Qed.









  Theorem mred_e1e2_e1 :
    forall env e1 e2,
      subst_env (measure_exp e1 + measure_exp e2 + measure_env env) env e1
    = subst_env (measure_env_exp env e1) env e1.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - env e1 Hle:
      mred_exp_min
      (measure_env_exp env e1)
      (measure_exp e1 + measure_exp e2 + measure_env env).
  Qed.



  Theorem mred_e1e2_e2 :
    forall env e1 e2,
      subst_env (measure_exp e1 + measure_exp e2 + measure_env env) env e2
    = subst_env (measure_env_exp env e2) env e2.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - env e2 Hle:
      mred_exp_min
      (measure_env_exp env e2)
      (measure_exp e1 + measure_exp e2 + measure_env env).
  Qed.



  Theorem mred_e1e2_e2_rem_vars :
    forall vars env e1 e2,
      subst_env (measure_exp e1 + measure_exp e2 + measure_env env)
        (rem_vars vars env) e2
    = subst_env (measure_env_exp (rem_vars vars env) e2)
        (rem_vars vars env) e2.
  Proof.
    (* #1 Measure Reduction Environment: intro/assert/pose/rewrite
      + lia/clear *)
    itr.
    ass > (measure_exp e2 <= measure_exp e1 + measure_exp e2) as Hle_e2: lia.
    pse - measure_env_rem_vars_le as Hle_env: env vars.
    psc - mred_exp_only_env_min as Heq_env: (rem_vars vars env) e2
      (measure_exp e1 + measure_exp e2) (measure_env env)
      Hle_e2 Hle_env.
    cwr - Heq_env.
    (* #2 Measure Reduction Solver: mred_solver *)
    mred_solver > (rem_vars vars env) e2 Hle:
      mred_exp_min
      (measure_env_exp (rem_vars vars env) e2)
      (measure_exp e1 + measure_exp e2 + measure_env (rem_vars vars env)).
  Qed.









  Theorem mred_e1e2e3_e1 :
    forall env e1 e2 e3,
      subst_env (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env env) env e1
    = subst_env (measure_env_exp env e1) env e1.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - env e1 Hle:
      mred_exp_min
      (measure_env_exp env e1)
      (measure_exp e1 + measure_exp e2 + measure_exp e3 + measure_env env).
  Qed.



  Theorem mred_e1e2e3_e2_rem_vars :
    forall vars env e1 e2 e3,
      subst_env (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env env) (rem_vars vars env) e2
    = subst_env (measure_env_exp (rem_vars vars env) e2)
        (rem_vars vars env) e2.
  Proof.
    (* #1 Measure Reduction Environment: intro/assert/pose/rewrite
      + lia/clear *)
    itr.
    ass > (measure_exp e2 ≤ measure_exp e1 + measure_exp e2 + measure_exp e3)
      as Hle_e2: lia.
    pse - measure_env_rem_vars_le as Hle_env: env vars.
    psc - mred_exp_only_env_min as Heq_env: (rem_vars vars env) e2
      (measure_exp e1 + measure_exp e2 + measure_exp e3) (measure_env env)
      Hle_e2 Hle_env.
    cwr - Heq_env.
    (* #2 Measure Reduction Solver: mred_solver *)
    mred_solver > (rem_vars vars env) e2 Hle:
      mred_exp_min
      (measure_env_exp (rem_vars vars env) e2)
      (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env (rem_vars vars env)).
  Qed.



  Theorem mred_e1e2e3_e3_rem_vars :
    forall vars env e1 e2 e3,
      subst_env (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env env) (rem_vars vars env) e3
    = subst_env (measure_env_exp (rem_vars vars env) e3)
        (rem_vars vars env) e3.
  Proof.
    (* #1 Measure Reduction Environment: intro/assert/pose/rewrite
      + lia/clear *)
    itr.
    ass > (measure_exp e3 ≤ measure_exp e1 + measure_exp e2 + measure_exp e3)
      as Hle_e3: lia.
    pse - measure_env_rem_vars_le as Hle_env: env vars.
    psc - mred_exp_only_env_min as Heq_env: (rem_vars vars env) e3
      (measure_exp e1 + measure_exp e2 + measure_exp e3) (measure_env env)
      Hle_e3 Hle_env.
    (* #2 Measure Reduction Solver: mred_solver *)
    cwr - Heq_env.
    mred_solver > (rem_vars vars env) e3 Hle:
      mred_exp_min
      (measure_env_exp (rem_vars vars env) e3)
      (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env (rem_vars vars env)).
  Qed.









  Theorem mred_eel_e :
    forall env e el,
      subst_env (measure_list measure_exp (e :: el) + measure_env env) env e
    = subst_env (measure_env_exp env e) env e.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - env e Hle:
      mred_exp_min
      (measure_env_exp env e)
      (measure_list measure_exp (e :: el) + measure_env env).
  Qed.



  Theorem mred_eel_el :
    forall env e el,
      map
        (subst_env (measure_list measure_exp (e :: el) + measure_env env) env)
        el
    = map (subst_env (measure_list measure_exp el + measure_env env) env) el.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - env el Hle:
      mred_exp_list_min
      (measure_list measure_exp el + measure_env env)
      (measure_list measure_exp (e :: el) + measure_env env).
  Qed.









  Theorem mred_e1e2ell_e1 :
    forall env e1 e2 ell,
      subst_env
        (measure_map measure_exp ((e1, e2) :: ell) + measure_env env) env e1
    = subst_env (measure_env_exp env e1) env e1.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - env e1 Hle:
      mred_exp_min
      (measure_env_exp env e1)
      (measure_map measure_exp ((e1, e2) :: ell) + measure_env env).
  Qed.



  Theorem mred_e1e2ell_e2 :
    forall env e1 e2 ell,
      subst_env
        (measure_map measure_exp ((e1, e2) :: ell) + measure_env env) env e2
    = subst_env (measure_env_exp env e2) env e2.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - env e2 Hle:
      mred_exp_min
      (measure_env_exp env e2)
      (measure_map measure_exp ((e1, e2) :: ell) + measure_env env).
  Qed.



  Theorem mred_e1e2ell_ell :
    forall env e1 e2 ell,
      map
        (prod_map
          (subst_env
            (measure_map measure_exp ((e1, e2) :: ell) + measure_env env) env)
          (subst_env
            (measure_map measure_exp ((e1, e2) :: ell) + measure_env env) env))
        ell
    = map
        (prod_map
          (subst_env (measure_map measure_exp ell + measure_env env) env)
          (subst_env (measure_map measure_exp ell + measure_env env) env))
        ell.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - env ell Hle:
      mred_exp_map_min
      (measure_map measure_exp ell + measure_env env)
      (measure_map measure_exp ((e1, e2) :: ell) + measure_env env).
  Qed.









  Theorem mred_expel_exp :
    forall env exp el,
      subst_env
        (measure_exp exp + measure_list measure_exp el + measure_env env)
        env
        exp
    = subst_env (measure_env_exp env exp) env exp.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - env exp Hle:
      mred_exp_min
      (measure_env_exp env exp)
      (measure_exp exp + measure_list measure_exp el + measure_env env).
  Qed.



  Theorem mred_expel_el :
    forall env exp el,
      map
        (subst_env
          (measure_exp exp + measure_list measure_exp el + measure_env env)
          env)
        el
    = map (subst_env (measure_list measure_exp el + measure_env env) env) el.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr.
    mred_solver - env el Hle:
      mred_exp_list_min
      (measure_list measure_exp el + measure_env env)
      (measure_exp exp + measure_list measure_exp el + measure_env env).
  Qed.






  Theorem mred_eext_ext_rem_both :
    forall env e ext,
      (map
        (fun '(fid, (vars, body)) =>
          (fid,
          (vars,
          subst_env
            (measure_exp e + measure_exp_ext measure_exp ext + measure_env env)
            (rem_exp_ext_both vars ext env) body))) ext)
    = (map
        (fun '(fid, (vars, body)) =>
          (fid,
          (vars,
          subst_env
            (measure_env_exp (rem_exp_ext_both vars ext env) body)
            (rem_exp_ext_both vars ext env) body))) ext).
  Proof.
    (* #1 Apply Extension: intro/apply/f_equal *)
    itr.
    apply map_ext_in_iff.
    itr - a HIn.
    des - a as [fid [vars body]].
    do 2 feq.
    (* #2 Split Extension: apply/destruct/rewrite + rename*)
    app - In_split in HIn.
    des - HIn; ren - ext1 HIn: x H.
    des - HIn; ren - ext2 HIn: x H.
    cwr - HIn.
    (* #3 Measure reduction: apply *)
    app - mred_exp_min.
    (* #4 Unfold: unfold*)
    ufl - measure_env_exp.
    unfold measure_exp_ext.
    (* #5 Rewrite Append Lemmas: rewrite *)
    rwr - cons_app.
    do 2 rwr - map_app
               list_sum_app.
    (* #6 Simplify: simpl/rewrite *)
    smp.
    rwr - Nat.add_0_r.
    (* #7 Reorder (Comm & Assoc): rewrite *)
    rwr - Nat.add_comm.
    rwr - Nat.add_assoc.
    rewrite Nat.add_comm with (n := measure_exp body).
    do 3 rwl - Nat.add_assoc.
    rewrite Nat.add_comm with (n := measure_exp body).
    do 3 rwr - Nat.add_assoc.
    (* #8 Lesser or Equal Reduction: rewrite *)
    rwl - NPeano.Nat.add_le_mono_r.
    (* #9 Add Zero: pose/symmetry/rewrite + clear *)
    pse - Nat.add_0_l as Hlzero:
          (measure_env
            (rem_exp_ext_both vars (ext1 ++ (fid, (vars, body)) :: ext2) env)).
    sym - Hlzero.
    setoid_rewrite Hlzero; clr - Hlzero.
    (* #10 Apply Mono: *)
    app - Nat.add_le_mono: lia.
    (* #11 Environment Reduction: pose *)
    app - measure_env_rem_exp_ext_both_le.
  Qed.



  Theorem mred_eext_ext_rem_both_from_val :
    forall env e ext,
      (map
        (fun '(fid, (vars, body)) =>
          (fid,
          (vars,
          subst_env
            (measure_exp e + measure_exp_ext measure_exp ext + measure_env env)
            (rem_exp_ext_both vars (bval_to_bexp_ext ext) env) body)))
            (bval_to_bexp_ext ext))
    = (map
        (fun '(fid, (vars, body)) =>
          (fid,
          (vars,
          subst_env
            (measure_env_exp (rem_exp_ext_both vars (bval_to_bexp_ext ext) env) body)
            (rem_exp_ext_both vars (bval_to_bexp_ext ext) env) body)))
            (bval_to_bexp_ext ext)).
  Proof.
    (* #1 Apply Extension: intro/apply/f_equal *)
    itr.
    apply map_ext_in_iff.
    itr - a HIn.
    des - a as [fid [vars body]].
    do 2 feq.
    (* #2 Split Extension: apply/destruct/rewrite + rename*)
    app - In_split in HIn.
    des - HIn; ren - ext1 HIn: x H.
    des - HIn; ren - ext2 HIn: x H.
    rwr - HIn.
    (* #TMP Assert and destruct *)
    ass > (exists ext1' ext2' n,
      ext = ext1' ++ [(n, fid, (vars, body))] ++ ext2' /\
      bval_to_bexp_ext ext1' = ext1 /\
      bval_to_bexp_ext [(n, fid, (vars, body))] = [(fid, (vars, body))] /\
      bval_to_bexp_ext ext2' = ext2).
    {
      admit.
    }
    do 4 des - H. 
    des - H0.
    des - H1.
    ren - ext1' ext2' n Heq Hext1 Hbody Hext2: x x0 x1 H H0 H1 H2.
    cwr - Heq.
    (* #3 Measure reduction: apply *)
    app - mred_exp_min.
    (* #4 Unfold: unfold*)
    ufl - measure_env_exp.
    unfold measure_exp_ext.
    (* #5 Rewrite Append Lemmas: rewrite *)
    rwr - cons_app.
    do 2 rwr - map_app
               list_sum_app.
    (* #6 Simplify: simpl/rewrite *)
    smp.
    rwr - Nat.add_0_r.
    (* #7 Reorder (Comm & Assoc): rewrite *)
    rwr - Nat.add_comm.
    rwr - Nat.add_assoc.
    rewrite Nat.add_comm with (n := measure_exp body).
    do 3 rwl - Nat.add_assoc.
    rewrite Nat.add_comm with (n := measure_exp body).
    do 3 rwr - Nat.add_assoc.
    (* #8 Lesser or Equal Reduction: rewrite *)
    rwl - NPeano.Nat.add_le_mono_r.
    (* #9 Add Zero: pose/symmetry/rewrite + clear *)
    pse - Nat.add_0_l as Hlzero:
          (measure_env
            (rem_exp_ext_both vars (ext1 ++ (fid, (vars, body)) :: ext2) env)).
    sym - Hlzero.
    setoid_rewrite Hlzero; clr - Hlzero.
    (* #10 Apply Mono: *)
    app - Nat.add_le_mono: lia.
    (* #11 Environment Reduction: pose *)
    app - measure_env_rem_exp_ext_both_le.
  Admitted.



End Inductive_Expression.