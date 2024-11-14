From CoreErlang.TMP.EqBF Require Export Part3Simple.

Import BigStep.

(*
| [], modules, own_module, id', bval_to_bexp (subst_env (measure_val v)) v, eff' | -e> | id',
inl [v], eff' |
*)
  Theorem eq_bs_var_reduction :
    forall modules own_module id v eff,
      (eval_expr [] modules own_module id
        (bval_to_bexp (subst_env (measure_val v)) v) eff id (inl [v]) eff).
  Proof.
    itr.
    ind + ind_val - v.
    * smp; cns.
    * smp; cns.
    * rfl - bval_to_bexp.
      rwr - mred_vcons_v1
            mred_vcons_v2.
      ens.
      exa - IHv2.
      exa - IHv1.
    * adm.
    * ren - vl HForall: l H.
      rfl - bval_to_bexp.
      ens.
      - ind - vl as [| v vl IHvl].
        + bmp.
        + ivc - HForall as Hbs_v HForall: H1 H2.
          spc - IHvl as Hlength_vl: HForall.
          rem_sbt_smp: (VTuple (v :: vl)).
          rwr - mred_vtuple_vl.
          bwr - Hlength_vl.
      - ass - as Hlength: rwr - repeat_length >
          (Datatypes.length
            (map (bval_to_bexp (subst_env (measure_val (VTuple vl)))) vl) = 
          Datatypes.length
            (repeat eff
          (Datatypes.length
            (map (bval_to_bexp (subst_env (measure_val (VTuple vl)))) vl)))).
        exa - Hlength.
      - ass - as Hlength: rwr - repeat_length >
          (Datatypes.length
            (map (bval_to_bexp (subst_env (measure_val (VTuple vl)))) vl) = 
          Datatypes.length
            (repeat id
          (Datatypes.length
            (map (bval_to_bexp (subst_env (measure_val (VTuple vl)))) vl)))).
        exa - Hlength.
      - adm.
      - adm.
      - adm.
    * adm.
  Admitted.



  Theorem eq_bs_subst_env :
    forall env modules own_module id id' e e' eff eff',
        (eval_expr env modules own_module id e eff id' e' eff')
    ->  (eval_expr [] modules own_module id
          (subst_env (measure_env_exp env e) env e) eff id' e' eff').
  Proof.
    itr - env modules own_module id id' e e' eff eff' Hbs;
    gen - env modules own_module id id'.
    rev - e' eff eff'.
    ind + ind_exp - e; itr.
    2: { (*ENil*)
      ivs - Hbs.
      smp.
      cns.
    }
    2: { (*ELit*)
      ivs - Hbs.
      smp.
      cns.
    }
    2: { (*EVar*)
      ivs - Hbs as var vs Hget: v res H4.
      smp.
      rwr - Hget.
      (* #3 Destruct Match: destruct/simple + apply/simpl/congruence *)
      des - vs as [|v vs]:
        app - get_value_singelton_length in Hget; smp - Hget; con.
      des - vs as [|v0 vs]:
        app - get_value_singelton_length in Hget; smp - Hget; con.
      (* #4 Measure Reduction: apply/destruct/assert/pose/rewrite + clear/triv *)
      app - get_value_in in Hget as HIn.
      app - In_split in HIn as Heq_env.
      des - Heq_env as [env1]; ren - Heq_env: H.
      des - Heq_env as [env2]; ren - Heq_env: H.
      cwr - Heq_env.
      ass - as Hnle: triv_nle_solver >
        (measure_val v <= measure_env (env1 ++ (inl var, v) :: env2)).
      psc - mred_val_min as Hmred_v: v
        (measure_env (env1 ++ (inl var, v) :: env2)) Hnle.
      cwr - Hmred_v; clr - env1 env2.
      bse - eq_bs_var_reduction: modules own_module id' v eff'.
    }
    2: { (*EFunId*)
      ivs - Hbs.
      - ren - funid vs Hget: f res H4.
        smp.
        rwr - Hget.
        (* #3 Destruct Match: destruct/simple + apply/simpl/congruence *)
        des - vs as [|v vs]:
          app - get_value_singelton_length in Hget; smp - Hget; con.
        des - vs as [|v0 vs]:
          app - get_value_singelton_length in Hget; smp - Hget; con.
        (* #4 Measure Reduction: apply/destruct/assert/pose/rewrite + clear/triv *)
        app - get_value_in in Hget as HIn.
        app - In_split in HIn as Heq_env.
        des - Heq_env as [env1]; ren - Heq_env: H.
        des - Heq_env as [env2]; ren - Heq_env: H.
        cwr - Heq_env.
        ass - as Hnle: triv_nle_solver >
          (measure_val v <= measure_env (env1 ++ (inr funid, v) :: env2)).
        psc - mred_val_min as Hmred_v: v
          (measure_env (env1 ++ (inr funid, v) :: env2)) Hnle.
        cwr - Hmred_v; clr - env1 env2.
        bse - eq_bs_var_reduction: modules own_module id' v eff'.
      - ren - funid Hget Hmod: f H0 H1.
        smp.
        rwr - Hget.
        cns.
        smp.
        ufl - get_own_modfunc in Hmod.
        des > (get_module own_module (modules ++ stdlib)); smp - Hmod.
        + adm.
        + con.
    }
    2: { (* EFun*)
      ivs - Hbs.
      smp.
      adm.
    }
    10: { (*ELetRec*)
      adm.
    }
    2: {
      ivs - Hbs.
      * ren - v2 Hv2 v1 Hv1: tlv H5 hdv H10.
        specialize (IHe1 eff' eff2 (inl [v1])
          id' id'0 own_module modules env Hv1).
        specialize (IHe2 eff2 eff (inl [v2])
          id'0 id own_module modules env Hv2).
        smp.
        rwr - mred_e1e2_e2
              mred_e1e2_e1.
        ens.
        - exa - IHe2.
        - exa - IHe1.
      * ren - exc Hexc: ex H9.
        specialize (IHe2 eff' eff (inr exc) id' id own_module modules env Hexc).
        smp.
        rwr - mred_e1e2_e2
              mred_e1e2_e1.
        ens.
        exa - IHe2.
    }
    1: {
      ivc - Hbs.
      - smp.
        ens.
        + ivs - H1.
          bwr - map_length.
        + ass - as Hlength: rwr - repeat_length >
            (Datatypes.length
              (map (subst_env
                (measure_list measure_exp el + measure_env env) env) el) = 
            Datatypes.length
              (repeat eff
            (Datatypes.length
              (map (subst_env
                (measure_list measure_exp el + measure_env env) env) el)))).
          exa - Hlength.
       + ass - as Hlength: rwr - repeat_length >
            (Datatypes.length
              (map (subst_env
                (measure_list measure_exp el + measure_env env) env) el) = 
            Datatypes.length
              (repeat id
            (Datatypes.length
              (map (subst_env
                (measure_list measure_exp el + measure_env env) env) el)))).
          exa - Hlength.
       + rwr - map_length.
          Print nth_def.
          itr.
          ass - as Heff: adm >
            ((nth_def (repeat eff (Datatypes.length el))  eff [] i) = eff).
          ass - as Hid: adm >
            ((nth_def (repeat id (Datatypes.length el)) id 0 i) = id).
          ass - as Heff': adm >
            ((nth_def (repeat eff (Datatypes.length el))  eff [] (S i)) = eff).
          ass - as Hid': adm >
            ((nth_def (repeat id (Datatypes.length el)) id 0 (S i)) = id).
          setoid_rewrite Hid.
          setoid_rewrite Heff.
          setoid_rewrite Hid'.
          setoid_rewrite Heff'.
          spe - H4: i H0.
          adm.
       + adm.
       + adm.
     - adm.
    }
  Admitted.


From CoreErlang Require Export FunctionalBigStep.

Import ListNotations.

Open Scope string_scope.
(*
| [], modules, own_module, id,
EFun vl (subst_env (measure_env_exp (rem_vars vl env) e) (rem_vars vl env) e), eff | -e> | 
S id, inl [VClos env [] id vl e None], eff |
*)

Example eval_letrec1_fbs : 
  fbs_expr 1000 [] [] "" 0 (ELetRec [(("x", 1), (["X"], EApp (EFunId ("x", 1)) [EVar "X"])) ]
            (EApp (EFunId ("x", 1)) [ETuple []])) []
=
  Timeout.
Proof.
  auto.
Qed.

Lemma test0 :
  (EFun ["x"; "y"] (EValues [(EVar "x"); (EVar "y"); ENil])) = ENil.
Proof.
Admitted.

Check fbs_expr.

Example test1 : 
  fbs_expr 1000 [] [] "" 0 (EFun ["x"; "y"] (EValues [(EVar "x"); (EVar "y"); (EVar "z")])) []
=
  Timeout.
Proof.
  smp.
Admitted.

Check Environment.
Print Environment.

Example test2 : 
  fbs_expr 1000 [(inl "z" , VLit (Integer 1))]  [] "" 0 (EFun ["x"; "y"] (EValues [(EVar "x"); (EVar "y"); (EVar "z")])) []
=
  Timeout.
Proof.
  smp.
Admitted.


Example test3 : 
  fbs_expr 1000 [(inl "z" , VLit (Integer 1)); (inl "x" , VLit (Integer 2))]  [] "" 0 (EFun ["x"; "y"] (EValues [(EVar "x"); (EVar "y"); (EVar "z")])) []
=
  Timeout.
Proof.
  smp.
Admitted.

Example test4 : 
  fbs_expr 1000 [(inl "x" , VLit (Integer 2))]  [] "" 0 (EVar "x") []
=
  Timeout.
Proof.
  smp.
Admitted.

Print get_env.
Print get_env_base.


  Theorem eq_bs_subst_env1 :
    forall env modules own_module id id' e e' eff eff',
        (eval_expr env modules own_module id e eff id' e' eff')
    ->  (eval_expr [] modules own_module id
          (subst_env (measure_env_exp env e) env e) eff id' e' eff').
  Proof.
    itr - env modules own_module id id' e e' eff eff' Hbs.
    ind - Hbs.
    8: {
      smp.
      rwr - mred_e_vars.
      (* ? Refactor Bigstep: EFun (rem_vars env)*)
      (**)
      replace (rem_vars vl env) with env.
      2: adm. (* not true *)
      
    }
  Admitted.