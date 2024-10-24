From CoreErlang.TMP.EqBF Require Export Part1Simple.

Import BigStep.













(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: MeasureLemmas ////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* Environment
  - measure_env_rem_le
* Tactics
  - ass_le_trans
  - ass_le_trans2
* Value
  - mred_val_cons
  - mred_val_tuple
  - mred_val_map
  - mred_val_clos
  - mred_val
* Expression
  - mred_exp
* Separate
  - mred_exp_separate
  - mred_exp_only_exp
  - mred_exp_only_env
* Mapper
  - mred_val_list
  - mred_val_list_map
* Minimum
  - mred_val_min
  - mred_val_list_min
  - mred_val_list_map_min
  - measure_exp_reduction_min
* Specials
  - mred_vcons_v1
  - mred_vcons_v2
  - mred_vtuple_v
  - mred_vtuple_vl
  - mred_vmap_v1
  - mred_vmap_v2
  - mred_vmap_vl
*)






Section MeasureLemmas_Environment.



  Lemma measure_env_rem_keys_le :
    forall env keys,
    measure_env (rem_keys keys env) <= measure_env env.
  Proof.
    itr.
    ufl - measure_env rem_keys.
  Admitted.



  Lemma measure_env_rem_vars_le :
    forall env vars,
    measure_env (rem_vars vars env) <= measure_env env.
  Proof.
    (* #1 Prove by Previus Theorem: intro/unfold/pose *)
    itr.
    ufl - rem_vars.
    by pose proof measure_env_rem_keys_le env (map inl vars).
  Qed.



  Lemma measure_env_rem_fids_le :
    forall env fids,
    measure_env (rem_fids fids env) <= measure_env env.
  Proof.
    (* #1 Prove by Previus Theorem: intro/unfold/pose *)
    itr.
    ufl - rem_fids.
    by pose proof measure_env_rem_keys_le env (map inr (map fst fids)).
  Qed.



  Lemma measure_env_rem_both_le :
    forall env vars fids,
    measure_env (rem_both fids vars env) <= measure_env env.
  Proof.
    (* #1 Pose Previus Theorems: intro/unfold/pose *)
    itr.
    ufl - rem_both.
    pse - measure_env_rem_fids_le as Hle_fids: (rem_vars vars env) fids.
    pse - measure_env_rem_vars_le as Hle_vars: env vars.
    (* #2 Apply Transitive: apply/exact *)
    epp - Nat.le_trans: exa - Hle_fids | exa - Hle_vars.
  Qed.



  Lemma measure_env_rem_nfifes_le :
    forall env nfifes,
    measure_env (rem_nfifes nfifes env) <= measure_env env.
  Proof.
    (* #1 Prove by Previus Theorem: intro/unfold/pose *)
    itr.
    ufl - rem_nfifes.
    by pose proof measure_env_rem_keys_le env
          (map inr (map snd (map fst nfifes))).
  Qed.



End MeasureLemmas_Environment.






(* Section MeasureLemmas_Tactics *)



Ltac triv_nle_solver := 
  smp;
  try unfold measure_env_exp;
  try unfold measure_env;
  try unfold measure_list;
  try unfold measure_map;
  try rewrite map_app, list_sum_app;
  sli.



Tactic Notation "ass_nle"
  "as"  ident(Ile)
  ":"   constr(Cle)
  :=
  assert Cle as Ile by triv_nle_solver.

Tactic Notation "ass_nle"
        constr(Cle)
  "as"  ident(Ile)
  ":"   hyp(Hm1) hyp(Hm2)
  :=
  assert Cle as Ile by
    (rewrite Hm1, Hm2;
    triv_nle_solver).

Tactic Notation "ass_nle"
        constr(Cle)
  "as"  ident(Ile)
  ":"   hyp(Hm1) hyp(Hm2) hyp(Hm3)
  :=
  assert Cle as Ile by
    (rewrite Hm1, Hm2, Hm3;
    triv_nle_solver).


Tactic Notation "ass_nle_trn"
        constr(Cle_n1_n3)
  "as"  ident(Ile_n1_n3)
  ":"   hyp(Hle_n1_n2) hyp(Hle_n2_n3)
  :=
  assert Cle_n1_n3 as Ile_n1_n3 by
    (eapply Nat.le_trans;
      [exact Hle_n1_n2 | exact Hle_n2_n3]).

Tactic Notation "ass_nle_trn"
        constr(Cle_n1_n4)
  "as"  ident(Ile_n1_n4)
  ":"   hyp(Hle_n1_n2) hyp(Hle_n2_n3) hyp(Hle_n3_n4)
  :=
  assert Cle_n1_n4 as Ile_n1_n4 by
    (eapply Nat.le_trans;
      [eapply Nat.le_trans;
        [exact Hle_n1_n2 | exact Hle_n2_n3]
      | exact Hle_n3_n4]).



Tactic Notation "mred_solver"
  "-" ident(v) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(mv) constr(n1) constr(n2)
  :=
  ass_nle as Hle1: (mv <= n1);
  ass_nle as Hle2: (mv <= n2);
  ase - theorem: v n1 n2 Hle1 Hle2.

Tactic Notation "mred_solver"
  "-" ident(v) ident(n1) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(mv) constr(n2)
  :=
  ass_nle as Hle2: (mv <= n2);
  ase - theorem: v n1 n2 Hle1 Hle2.

Tactic Notation "mred_solver"
  "-" ident(v) ident(n1) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(n2)
  :=
  ass_nle as Hle2: (n2 <= n2);
  ase - theorem: v n1 n2 Hle1 Hle2.

Tactic Notation "mred_solver"
  "-" ident(v) ident(Hle)
  ":" constr(theorem) constr(mv) constr(n)
  :=
  ass_nle as Hle: (mv <= n);
  bse - theorem: v n Hle.

Tactic Notation "mred_solver"
  "-" ident(env) ident(e) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(me) constr(n1) constr(n2)
  :=
  ass_nle as Hle1: (me <= n1);
  ass_nle as Hle2: (me <= n2);
  ase - theorem: env e n1 n2 Hle1 Hle2.

Tactic Notation "mred_solver"
  "-" ident(env) ident(e) ident(n1) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(me) constr(n2)
  :=
  ass_nle as Hle2: (me <= n2);
  ase - theorem: env e n1 n2 Hle1 Hle2.

Tactic Notation "mred_solver"
  "-" ident(env) ident(e) ident(n1) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(n2)
  :=
  ass_nle as Hle2: (n2 <= n2);
  ase - theorem: env e n1 n2 Hle1 Hle2.

Tactic Notation "mred_solver"
  "-" ident(env) ident(e) ident(Hle)
  ":" constr(theorem) constr(me) constr(n)
  :=
  ass_nle as Hle: (me <= n);
  ase - theorem: env e n Hle.

Tactic Notation "mred_solver"
  ">" constr(env) ident(e) ident(Hle)
  ":" constr(theorem) constr(me) constr(n)
  :=
  ass_nle as Hle: (me <= n);
  ase - theorem: env e n Hle.

(* End MeasureLemmas_Tactics *)






Section MeasureLemmas_Value.



  Theorem mred_val_cons :
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
    ass_nle (mv1 <= mv1v2) as Hle_v1_v1v2: Hmv1 Hmv1v2.
    ass_nle (mv2 <= mv1v2) as Hle_v2_v1v2: Hmv2 Hmv1v2.
    ass_nle_trn (mv1 <= n1) as Hle_v1_n1: Hle_v1_v1v2 Hle_v1v2_n1.
    ass_nle_trn (mv1 <= n2) as Hle_v1_n2: Hle_v1_v1v2 Hle_v1v2_n2.
    ass_nle_trn (mv2 <= n1) as Hle_v2_n1: Hle_v2_v1v2 Hle_v1v2_n1.
    ass_nle_trn (mv2 <= n2) as Hle_v2_n2: Hle_v2_v1v2 Hle_v1v2_n2.
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



  Theorem mred_val_tuple :
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
    ass_nle (mv <= mvvl) as Hle_v_vvl: Hmv Hmvvl.
    ass_nle (mvl <= mvvl) as Hle_vl_vvl: Hmvl Hmvvl.
    ass_nle_trn (mv <= n1) as Hle_v_n1: Hle_v_vvl Hle_vvl_n1.
    ass_nle_trn (mv <= n2) as Hle_v_n2: Hle_v_vvl Hle_vvl_n2.
    ass_nle_trn (mvl <= n1) as Hle_vl_n1: Hle_vl_vvl Hle_vvl_n1.
    ass_nle_trn (mvl <= n2) as Hle_vl_n2: Hle_vl_vvl Hle_vvl_n2.
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



  Theorem mred_val_map :
    forall vl n1 n2,
        measure_val (VMap vl) <= n1
    ->  measure_val (VMap vl) <= n2
    ->  Forall (fun v =>
           (measure_val v.1 <= n1
        ->  measure_val v.1 <= n2
        ->  bval_to_bexp (subst_env n1) v.1
          = bval_to_bexp (subst_env n2) v.1)
        /\ (measure_val v.2 <= n1
        ->  measure_val v.2 <= n2
        ->  bval_to_bexp (subst_env n1) v.2
          = bval_to_bexp (subst_env n2) v.2))
          vl
    ->  bval_to_bexp (subst_env n1) (VMap vl)
      = bval_to_bexp (subst_env n2) (VMap vl).
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - vl n1 n2 Hle_vvl_n1 Hle_vvl_n2 HForall.
    ind - vl as [| v vl Heq_vl]: bmp.
    ivc - HForall as Heq_v HForall: H1 H2.
    (* #2 Remember: destruct/simpl/remember *)
    des - v as [v1 v2].
    des - Heq_v as [Heq_v1 Heq_v2].
    smp - Heq_v1 Heq_v2.
    rem - mv1 mv2 mv mvl mvvl as Hmv1 Hmv2 Hmv Hmvl Hmvvl:
      (measure_val v1)
      (measure_val v2)
      (measure_val v1 + measure_val v2)
      (measure_val (VMap vl))
      (measure_val (VMap ((v1, v2) :: vl))).
    (* #3 Assert: assert *)
    ass_nle (mv1 <= mv) as Hle_v1_v: Hmv1 Hmv.
    ass_nle (mv2 <= mv) as Hle_v2_v: Hmv2 Hmv.
    ass_nle (mv <= mvvl) as Hle_v_vvl: Hmv Hmvvl.
    ass_nle (mvl <= mvvl) as Hle_vl_vvl: Hmvl Hmvvl.
    ass_nle_trn (mv1 <= n1) as Hle_v1_n1: Hle_v1_v Hle_v_vvl Hle_vvl_n1.
    ass_nle_trn (mv1 <= n2) as Hle_v1_n2: Hle_v1_v Hle_v_vvl Hle_vvl_n2.
    ass_nle_trn (mv2 <= n1) as Hle_v2_n1: Hle_v2_v Hle_v_vvl Hle_vvl_n1.
    ass_nle_trn (mv2 <= n2) as Hle_v2_n2: Hle_v2_v Hle_v_vvl Hle_vvl_n2.
    ass_nle_trn (mvl <= n1) as Hle_vl_n1: Hle_vl_vvl Hle_vvl_n1.
    ass_nle_trn (mvl <= n2) as Hle_vl_n2: Hle_vl_vvl Hle_vvl_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmv1 Hmv2 Hmv Hmvl Hmvvl in *.
    clr + Heq_v1 Heq_v2 Heq_vl HForall
      Hle_v1_n1 Hle_v1_n2 Hle_v2_n1 Hle_v2_n2 Hle_vl_n1 Hle_vl_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_v1: Hle_v1_n1 Hle_v1_n2.
    spc - Heq_v2: Hle_v2_n1 Hle_v2_n2.
    spc - Heq_vl: Hle_vl_n1 Hle_vl_n2 HForall.
    inj - Heq_vl as Heq_vl.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_v1 Heq_v2 Heq_vl.
  Qed.



  Theorem mred_val_clos :
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
  Admitted.



(** NOTES
* FULL NAME:
  - Measure Reduction at Value
* OLD NAME:
  - measure_reduction
  - measure_val_reduction
* FUNCTION:
  - When converting Value to Expression in Bigstep,
    the subst_env's fuel can be rewriten,
    if both the previus and the new fuel is bigger or equal,
    than the Value being converted
* USING:
  -
* USED AT:
  -
* History:
  - Relatively was easy to prove, except VClos
    (Might need a dual Proof with measure_exp_reduction)
  - !maybe measure_val and measure_exp needs to be dual defined because of Clos
*)
  Theorem mred_val :
    forall v n1 n2,
        measure_val v <= n1
    ->  measure_val v <= n2
    ->  bval_to_bexp (subst_env n1) v
      = bval_to_bexp (subst_env n2) v.
  Proof.
    (* #1 Value Induction: intro/induction + cbn *)
    itr - v n1 n2 Hn1 Hn2.
    ind + ind_val - v :- sbn.
    (* #2 Cons: pose *)
    1: bse - mred_val_cons:   v1 v2 n1 n2
                              Hn1 Hn2 IHv1 IHv2.
    (* #3 Tuple: pose *)
    2: bse - mred_val_tuple:  l n1 n2
                              Hn1 Hn2 H.
    (* #4 Map: pose *)
    2: bse - mred_val_map:    l n1 n2
                              Hn1 Hn2 H.
    (* #4 Closure: pose *)
    bse - mred_val_clos:      ref ext id params body funid n1 n2
                              Hn1 Hn2 H.
  Qed.



End MeasureLemmas_Value.






Section MeasureLemmas_Expression.



  (**
  * OLD NAMES:
    - measure_env_exp_reduction
  *)
  Theorem mred_exp :
    forall env e n1 n2,
        measure_env_exp env e <= n1
    ->  measure_env_exp env e <= n2
    ->  subst_env n1 env e
      = subst_env n2 env e.
  Proof.
  Admitted.



End MeasureLemmas_Expression.






Section MeasureLemmas_Separate.



  Theorem mred_exp_separate :
    forall env e ne1 ne2 nenv1 nenv2,
        measure_exp e <= ne1
    ->  measure_exp e <= ne2
    ->  measure_env env <= nenv1
    ->  measure_env env <= nenv2
    ->  subst_env (ne1 + nenv1) env e
      = subst_env (ne2 + nenv2) env e.
  Proof.
    (* #1 Pose Larger or Equal Mono: intro/pose *)
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



End MeasureLemmas_Separate.






Section MeasureLemmas_Mappers.



(**
* OLD NAMES:
  - measure_val_reduction_list
*)
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
    ass_nle (mv <= mvvl) as Hle_v_vvl: Hmv Hmvvl.
    ass_nle (mvl <= mvvl) as Hle_vl_vvl: Hmvl Hmvvl.
    ass_nle_trn (mv <= n1) as Hle_v_n1: Hle_v_vvl Hle_vvl_n1.
    ass_nle_trn (mv <= n2) as Hle_v_n2: Hle_v_vvl Hle_vvl_n2.
    ass_nle_trn (mvl <= n1) as Hle_vl_n1: Hle_vl_vvl Hle_vvl_n1.
    ass_nle_trn (mvl <= n2) as Hle_vl_n2: Hle_vl_vvl Hle_vvl_n2.
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



(**
* OLD NAMES:
  - measure_val_reduction_map
*)
  Theorem mred_val_list_map :
    forall vl n1 n2,
        list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl)
          <= n1
    ->  list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl)
          <= n2
    ->  map
          (prod_map
            (bval_to_bexp (subst_env n1))
            (bval_to_bexp (subst_env n1)))
          vl
      = map
          (prod_map
            (bval_to_bexp (subst_env n2))
            (bval_to_bexp (subst_env n2)))
          vl.
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - vl n1 n2 Hle_vvl_n1 Hle_vvl_n2.
    ind - vl as [| v vl Heq_vl]: bmp.
    (* #2 Remember: destruct/simpl/remember *)
    des - v as [v1 v2].
    rem - mv1 mv2 mv mvl mvvl as Hmv1 Hmv2 Hmv Hmvl Hmvvl:
      (measure_val v1)
      (measure_val v2)
      (measure_val v1 + measure_val v2)
      (list_sum (map (fun '(x, y) => measure_val x + measure_val y) vl))
      (list_sum (map (fun '(x, y) => measure_val x + measure_val y)
        ((v1, v2) :: vl))).
    (* #3 Assert: assert *)
    ass_nle (mv1 <= mv) as Hle_v1_v: Hmv1 Hmv.
    ass_nle (mv2 <= mv) as Hle_v2_v: Hmv2 Hmv.
    ass_nle (mv <= mvvl) as Hle_v_vvl: Hmv Hmvvl.
    ass_nle (mvl <= mvvl) as Hle_vl_vvl: Hmvl Hmvvl.
    ass_nle_trn (mv1 <= n1) as Hle_v1_n1: Hle_v1_v Hle_v_vvl Hle_vvl_n1.
    ass_nle_trn (mv1 <= n2) as Hle_v1_n2: Hle_v1_v Hle_v_vvl Hle_vvl_n2.
    ass_nle_trn (mv2 <= n1) as Hle_v2_n1: Hle_v2_v Hle_v_vvl Hle_vvl_n1.
    ass_nle_trn (mv2 <= n2) as Hle_v2_n2: Hle_v2_v Hle_v_vvl Hle_vvl_n2.
    ass_nle_trn (mvl <= n1) as Hle_vl_n1: Hle_vl_vvl Hle_vvl_n1.
    ass_nle_trn (mvl <= n2) as Hle_vl_n2: Hle_vl_vvl Hle_vvl_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmv1 Hmv2 Hmv Hmvl Hmvvl in *.
    clr + Heq_vl Hle_v1_n1 Hle_v1_n2 Hle_v2_n1 Hle_v2_n2 Hle_vl_n1 Hle_vl_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_vl: Hle_vl_n1 Hle_vl_n2.
    psc - mred_val as Heq_v1: v1 n1 n2 Hle_v1_n1 Hle_v1_n2.
    psc - mred_val as Heq_v2: v2 n1 n2 Hle_v2_n1 Hle_v2_n2.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_v1 Heq_v2 Heq_vl.
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
    ass_nle (me + menv <= meel + menv) as Hle_e_eel: Hme Hmeel Hmenv.
    ass_nle (mel + menv <= meel + menv) as Hle_el_eel: Hmel Hmeel Hmenv.
    ass_nle_trn (me + menv <= n1) as Hle_e_n1: Hle_e_eel Hle_eel_n1.
    ass_nle_trn (me + menv <= n2) as Hle_e_n2: Hle_e_eel Hle_eel_n2.
    ass_nle_trn (mel + menv <= n1) as Hle_el_n1: Hle_el_eel Hle_eel_n1.
    ass_nle_trn (mel + menv <= n2) as Hle_el_n2: Hle_el_eel Hle_eel_n2.
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



  Theorem mred_exp_list_map :
    forall env el n1 n2,
        list_sum (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) el)
           + measure_env env <= n1
    ->  list_sum (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) el)
          + measure_env env <= n2
    ->  map
          (prod_map
            (subst_env n1 env)
            (subst_env n1 env))
          el
      = map
          (prod_map
            (subst_env n2 env)
            (subst_env n2 env))
          el.
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - env el n1 n2 Hle_eel_n1 Hle_eel_n2.
    ind - el as [| e el Heq_el]: bmp.
    (* #2 Remember: destruct/simpl/remember *)
    des - e as [e1 e2].
    rem - menv me1 me2 me mel meel as Hmenv Hme1 Hme2 Hme Hmel Hmeel:
      (measure_env env)
      (measure_exp e1)
      (measure_exp e2)
      (measure_exp e1 + measure_exp e2)
      (list_sum (map (fun '(x, y) => measure_exp x + measure_exp y) el))
      (list_sum (map (fun '(x, y) => measure_exp x + measure_exp y)
        ((e1, e2) :: el))).
    (* #3 Assert: assert *)
    ass_nle (me1 + menv <= me + menv) as Hle_e1_e: Hme1 Hme Hmenv.
    ass_nle (me2 + menv <= me + menv) as Hle_e2_e: Hme2 Hme Hmenv.
    ass_nle (me + menv <= meel + menv) as Hle_e_eel: Hme Hmeel Hmenv.
    ass_nle (mel + menv <= meel + menv) as Hle_el_eel: Hmel Hmeel Hmenv.
    ass_nle_trn (me1 + menv <= n1) as Hle_e1_n1: Hle_e1_e Hle_e_eel Hle_eel_n1.
    ass_nle_trn (me1 + menv <= n2) as Hle_e1_n2: Hle_e1_e Hle_e_eel Hle_eel_n2.
    ass_nle_trn (me2 + menv <= n1) as Hle_e2_n1: Hle_e2_e Hle_e_eel Hle_eel_n1.
    ass_nle_trn (me2 + menv <= n2) as Hle_e2_n2: Hle_e2_e Hle_e_eel Hle_eel_n2.
    ass_nle_trn (mel + menv <= n1) as Hle_el_n1: Hle_el_eel Hle_eel_n1.
    ass_nle_trn (mel + menv <= n2) as Hle_el_n2: Hle_el_eel Hle_eel_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmenv Hme1 Hme2 Hme Hmel Hmeel in *.
    clr + Heq_el Hle_e1_n1 Hle_e1_n2 Hle_e2_n1 Hle_e2_n2 Hle_el_n1 Hle_el_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_el: Hle_el_n1 Hle_el_n2.
    psc - mred_exp as Heq_e1: env e1 n1 n2 Hle_e1_n1 Hle_e1_n2.
    psc - mred_exp as Heq_e2: env e2 n1 n2 Hle_e2_n1 Hle_e2_n2.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_e1 Heq_e2 Heq_el.
  Qed.



End MeasureLemmas_Mappers.






Section MeasureLemmas_Min.



  Theorem mred_val_min :
    forall v n,
        measure_val v <= n
    ->  bval_to_bexp (subst_env n) v
    =   bval_to_bexp (subst_env (measure_val v)) v.
  Proof.
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
    itr - vl n Hle1.
    mred_solver - vl n Hle1 Hle2:
      mred_val_list
      (list_sum (map measure_val vl)).
  Qed.



  Theorem mred_val_list_map_min :
    forall vl n,
        list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl)
          <= n
    ->  map
          (prod_map
            (bval_to_bexp (subst_env n))
            (bval_to_bexp (subst_env n)))
          vl
      = map
          (prod_map
            (bval_to_bexp
              (subst_env
                (list_sum
                  (map
                    (fun '(x, y) => (measure_val x) + (measure_val y))
                    vl))))
            (bval_to_bexp
              (subst_env
                (list_sum
                  (map
                    (fun '(x, y) => (measure_val x) + (measure_val y))
                    vl)))))
          vl.
  Proof.
    itr - vl n Hle1.
    mred_solver - vl n Hle1 Hle2:
      mred_val_list_map
      (list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl)).
  Qed.



  Theorem mred_exp_min :
    forall env e n,
        measure_env_exp env e <= n
    ->  subst_env n env e
    =   subst_env (measure_env_exp env e) env e.
  Proof.
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
    itr -  env el n Hle1.
    mred_solver - env el n Hle1 Hle2:
      mred_exp_list
      (list_sum (map measure_exp el) + measure_env env).
  Qed.



  Theorem mred_exp_list_map_min :
    forall env el n,
        list_sum (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) el)
           + measure_env env <= n
    ->  map
          (prod_map
            (subst_env n env)
            (subst_env n env))
          el
      = map
          (prod_map
            (subst_env
              (list_sum
                (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) el)
                + measure_env env)
              env)
            (subst_env
              (list_sum
                (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) el)
                + measure_env env)
              env))
          el.
  Proof.
    itr -  env el n Hle1.
    mred_solver - env el n Hle1 Hle2:
      mred_exp_list_map
      (list_sum (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) el)
        + measure_env env).
  Qed.



End MeasureLemmas_Min.





Section MeasureLemmas_Specials.



  Theorem mred_vcons_v1 :
    forall v1 v2,
      bval_to_bexp (subst_env (measure_val (VCons v1 v2))) v1
    = bval_to_bexp (subst_env (measure_val v1)) v1.
  Proof.
    itr.
    mred_solver - v1 Hle:
      mred_val_min
      (measure_val v1)
      (measure_val (VCons v1 v2)).
  Qed.



  Theorem mred_v1v2_v1 :
    forall v1 v2,
      bval_to_bexp (subst_env (measure_val v1 + measure_val v2)) v1
    = bval_to_bexp (subst_env (measure_val v1)) v1.
  Proof.
    itr.
    mred_solver - v1 Hle:
      mred_val_min
      (measure_val v1)
      (measure_val v1 + measure_val v2).
  Qed.



  Theorem mred_vcons_v2 :
    forall v1 v2,
      bval_to_bexp (subst_env (measure_val (VCons v1 v2))) v2
    = bval_to_bexp (subst_env (measure_val v2)) v2.
  Proof.
    itr.
    mred_solver - v2 Hle:
      mred_val_min
      (measure_val v2)
      (measure_val (VCons v1 v2)).
  Qed.



  Theorem mred_v1v2_v2 :
    forall v1 v2,
      bval_to_bexp (subst_env (measure_val v1 + measure_val v2)) v2
    = bval_to_bexp (subst_env (measure_val v2)) v2.
  Proof.
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
    itr.
    mred_solver - v Hle:
      mred_val_min
      (measure_val v)
      (measure_val (VTuple (v :: vl))).
  Qed.



  Theorem mred_vvl_v :
    forall v vl,
      bval_to_bexp (subst_env (measure_val v + measure_list measure_val vl)) v
    = bval_to_bexp (subst_env (measure_val v)) v.
  Proof.
    itr.
    mred_solver - v Hle:
      mred_val_min
      (measure_val v)
      (measure_val v + measure_list measure_val vl).
  Qed.



  Theorem mred_vtuple_vl :
    forall v vl,
      map (bval_to_bexp (subst_env (measure_val (VTuple (v :: vl))))) vl
    = map (bval_to_bexp (subst_env (measure_val (VTuple vl)))) vl.
  Proof.
    itr.
    mred_solver - vl Hle1 Hle2:
      mred_val_list
      (list_sum (map measure_val vl))
      (measure_val (VTuple vl))
      (measure_val (VTuple (v :: vl))).
  Qed.



  Theorem mred_vvl_vl :
    forall v vl,
      map
        (bval_to_bexp
          (subst_env (measure_val v + measure_list measure_val vl))) vl
    = map (bval_to_bexp (subst_env (measure_list measure_val vl))) vl.
  Proof.
    itr.
    mred_solver - vl Hle:
      mred_val_list_min
      (measure_list measure_val vl)
      (measure_val v + measure_list measure_val vl).
  Qed.



  Theorem mred_vmap_v1 :
    forall v1 v2 vl,
      bval_to_bexp (subst_env (measure_val (VMap ((v1, v2) :: vl)))) v1
    = bval_to_bexp (subst_env (measure_val v1)) v1.
  Proof.
    itr.
    mred_solver - v1 Hle:
      mred_val_min
      (measure_val v1)
      (measure_val (VMap ((v1, v2) :: vl))).
  Qed.



  Theorem mred_v1v2vl_v1 :
    forall v1 v2 vl,
      bval_to_bexp
        (subst_env
          (measure_val v1 + measure_val v2 + measure_map measure_val vl)) v1
    = bval_to_bexp (subst_env (measure_val v1)) v1.
  Proof.
    itr.
    mred_solver - v1 Hle:
      mred_val_min
      (measure_val v1)
      (measure_val v1 + measure_val v2 + measure_map measure_val vl).
  Qed.



  Theorem mred_vmap_v2 :
    forall v1 v2 vl,
      bval_to_bexp (subst_env (measure_val (VMap ((v1, v2) :: vl)))) v2
    = bval_to_bexp (subst_env (measure_val v2)) v2.
  Proof.
    itr.
    mred_solver - v2 Hle:
      mred_val_min
      (measure_val v2)
      (measure_val (VMap ((v1, v2) :: vl))).
  Qed.



  Theorem mred_v1v2vl_v2 :
    forall v1 v2 vl,
      bval_to_bexp
        (subst_env
          (measure_val v1 + measure_val v2 + measure_map measure_val vl)) v2
    = bval_to_bexp (subst_env (measure_val v2)) v2.
  Proof.
    itr.
    mred_solver - v2 Hle:
      mred_val_min
      (measure_val v2)
      (measure_val v1 + measure_val v2 + measure_map measure_val vl).
  Qed.



  Theorem mred_vmap_vl :
    forall v1 v2 vl,
      map
        (prod_map
          (bval_to_bexp (subst_env (measure_val (VMap ((v1, v2) :: vl)))))
          (bval_to_bexp (subst_env (measure_val (VMap ((v1, v2) :: vl))))))
        vl
    =
      map
        (prod_map
          (bval_to_bexp (subst_env (measure_val (VMap vl))))
          (bval_to_bexp (subst_env (measure_val (VMap vl)))))
        vl.
  Proof.
    itr.
    mred_solver - vl Hle1 Hle2:
      mred_val_list_map
      (list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl))
      (measure_val (VMap vl))
      (measure_val (VMap ((v1, v2) :: vl))).
  Qed.



  Theorem mred_v1v2vl_vl :
    forall v1 v2 vl,
      map
        (prod_map
          (bval_to_bexp
            (subst_env
              (measure_val v1 + measure_val v2 + measure_map measure_val vl)))
          (bval_to_bexp
            (subst_env
              (measure_val v1 + measure_val v2 + measure_map measure_val vl))))
        vl
    =
      map
        (prod_map
          (bval_to_bexp (subst_env (measure_map measure_val vl)))
          (bval_to_bexp (subst_env (measure_map measure_val vl))))
        vl.
  Proof.
    itr.
    mred_solver - vl Hle:
      mred_val_list_map_min
      (measure_map measure_val vl)
      (measure_val v1 + measure_val v2 + measure_map measure_val vl).
  Qed.



  Theorem mred_e1e2_e1 :
    forall env e1 e2,
      subst_env (measure_exp e1 + measure_exp e2 + measure_env env) env e1
    = subst_env (measure_env_exp env e1) env e1.
  Proof.
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
    itr.
    mred_solver - env e2 Hle:
      mred_exp_min
      (measure_env_exp env e2)
      (measure_exp e1 + measure_exp e2 + measure_env env).
  Qed.



  Theorem mred_e1e2e3_e1 :
    forall env e1 e2 e3,
      subst_env (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env env) env e1
    = subst_env (measure_env_exp env e1) env e1.
  Proof.
    itr.
    mred_solver - env e1 Hle:
      mred_exp_min
      (measure_env_exp env e1)
      (measure_exp e1 + measure_exp e2 + measure_exp e3 + measure_env env).
  Qed.



  Theorem mred_e1e2e3_e2 :
    forall env e1 e2 e3,
      subst_env (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env env) env e2
    = subst_env (measure_env_exp env e2) env e2.
  Proof.
    itr.
    mred_solver - env e2 Hle:
      mred_exp_min
      (measure_env_exp env e2)
      (measure_exp e1 + measure_exp e2 + measure_exp e3 + measure_env env).
  Qed.



  Theorem mred_e1e2e3_e3 :
    forall env e1 e2 e3,
      subst_env (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env env) env e3
    = subst_env (measure_env_exp env e3) env e3.
  Proof.
    itr.
    mred_solver - env e3 Hle:
      mred_exp_min
      (measure_env_exp env e3)
      (measure_exp e1 + measure_exp e2 + measure_exp e3 + measure_env env).
  Qed.



  Theorem mred_eel_e :
    forall env e el,
      subst_env (measure_list measure_exp (e :: el) + measure_env env) env e
    = subst_env (measure_env_exp env e) env e.
  Proof.
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
    itr.
    mred_solver - env el Hle:
      mred_exp_list_min
      (measure_list measure_exp el + measure_env env)
      (measure_list measure_exp (e :: el) + measure_env env).
  Qed.



  Theorem mred_e1e2_e2_vars :
    forall vars env e1 e2,
      subst_env (measure_exp e1 + measure_exp e2 + measure_env env)
        (rem_vars vars env) e2
    = subst_env (measure_env_exp (rem_vars vars env) e2)
        (rem_vars vars env) e2.
  Proof.
    itr.
    ass > (measure_exp e2 ≤ measure_exp e1 + measure_exp e2) as Hle_e2: lia.
    pse - measure_env_rem_vars_le as Hle_env: env vars.
    psc - mred_exp_only_env_min as Heq_env: (rem_vars vars env) e2
      (measure_exp e1 + measure_exp e2) (measure_env env)
      Hle_e2 Hle_env.
    cwr - Heq_env.
    mred_solver > (rem_vars vars env) e2 Hle:
      mred_exp_min
      (measure_env_exp (rem_vars vars env) e2)
      (measure_exp e1 + measure_exp e2 + measure_env (rem_vars vars env)).
  Qed.



  Theorem mred_e1e2e3_e2_vars :
    forall vars env e1 e2 e3,
      subst_env (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env env) (rem_vars vars env) e2
    = subst_env (measure_env_exp (rem_vars vars env) e2)
        (rem_vars vars env) e2.
  Proof.
    itr.
    ass > (measure_exp e2 ≤ measure_exp e1 + measure_exp e2 + measure_exp e3)
      as Hle_e2: lia.
    pse - measure_env_rem_vars_le as Hle_env: env vars.
    psc - mred_exp_only_env_min as Heq_env: (rem_vars vars env) e2
      (measure_exp e1 + measure_exp e2 + measure_exp e3) (measure_env env)
      Hle_e2 Hle_env.
    cwr - Heq_env.
    mred_solver > (rem_vars vars env) e2 Hle:
      mred_exp_min
      (measure_env_exp (rem_vars vars env) e2)
      (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env (rem_vars vars env)).
  Qed.



  Theorem mred_e1e2e3_e3_vars :
    forall vars env e1 e2 e3,
      subst_env (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env env) (rem_vars vars env) e3
    = subst_env (measure_env_exp (rem_vars vars env) e3)
        (rem_vars vars env) e3.
  Proof.
    itr.
    ass > (measure_exp e3 ≤ measure_exp e1 + measure_exp e2 + measure_exp e3)
      as Hle_e3: lia.
    pse - measure_env_rem_vars_le as Hle_env: env vars.
    psc - mred_exp_only_env_min as Heq_env: (rem_vars vars env) e3
      (measure_exp e1 + measure_exp e2 + measure_exp e3) (measure_env env)
      Hle_e3 Hle_env.
    cwr - Heq_env.
    mred_solver > (rem_vars vars env) e3 Hle:
      mred_exp_min
      (measure_env_exp (rem_vars vars env) e3)
      (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env (rem_vars vars env)).
  Qed.



End MeasureLemmas_Specials.













(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: CONVERTERLEMMAS //////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

(** STRUCTURE:
* Basics Injective
  - cons_inj
  - fcons_inj
  - ftuple_inj
  - fmap_inj
* Value Helpers
  - bval_to_fval_tuple
  - bval_to_fval_map
* Value Main
* Expression
*)



(** NOTES
* HISTORY:
  - bexp_to_fexp_add_vars: EFun need new theorem ->
    + bvs_to_fvs_add_vars: but this is list Val, and need a Val version ->
      ** bval_to_fval_add_vars: each path needed special injection lemmas ->
        -- See in -> Basics Injective & Value Helpers
*)









Section ConverterLemmas_Basics_Injective.



  Lemma cons_inj :
    forall
      (A : Type)
      (x y : A)
      (xs ys : list A),
        x :: xs = y :: ys
    ->  x = y /\ xs = ys.
  Proof.
    itr.
    ivc - H.
    ato.
  Qed.



  Lemma fcons_inj :
    forall x1 x2 y,
        Syntax.VCons x1 x2 = y
    ->  exists z1 z2,
            x1 = z1
        /\  x2 = z2
        /\  y = Syntax.VCons z1 z2.
  Proof.
    itr.
    exi - x1 x2.
    ato.
  Qed.



  Lemma ftuple_inj :
    forall
      (A : Type)
      (f : A -> Val)
      (x : A)
      (xl : list A)
      (y : Val),
        Syntax.VTuple ((f x) :: (map f xl)) = y
    ->  exists z zl,
            (f x) = z
        /\  (map f xl) = zl
        /\  y = Syntax.VTuple (z :: zl).
  Proof.
    itr.
    exi - (f x) (map f xl).
    ato.
  Qed.



  Lemma fmap_inj :
    forall
      (A : Type)
      (f : A -> Val)
      (x1 x2 : A)
      (xl : list (A * A))
      (y : Val),
        Syntax.VMap (((f x1), (f x2)) :: (map (fun '(k, v) => (f k, f v)) xl)) = y
    ->  exists z1 z2 zl,
            (f x1) = z1
        /\  (f x2) = z2
        /\  (map (fun '(k, v) => (f k, f v)) xl) = zl
        /\  y = Syntax.VMap ((z1, z2) :: zl).
  Proof.
    itr.
    exi - (f x1) (f x2) (map (fun '(k, v) => (f k, f v)) xl).
    ato.
  Qed.



End ConverterLemmas_Basics_Injective.






Section ConverterLemmas_Value_Help.



  Lemma bval_to_fval_tuple :
    forall f bvl fvl,
        map (bval_to_fval f) bvl = fvl
    <-> bval_to_fval f (VTuple bvl) = Syntax.VTuple fvl.
  Proof.
    itr.
    spl; itr.
    * smp; f_equal; exact H.
    * smp - H; inj - H as H; exact H.
  Qed.



  Lemma bval_to_fval_map :
    forall f bvl fvl,
        map (fun '(x, y) => ((bval_to_fval f x), (bval_to_fval f y))) bvl = fvl
    <-> bval_to_fval f (VMap bvl) = Syntax.VMap fvl.
  Proof.
    itr.
    spl; itr.
    * smp; f_equal; exact H.
    * smp - H; inj - H as H; exact H.
  Qed.



End ConverterLemmas_Value_Help.






Section ConverterLemmas_Value_Main.



  Theorem bval_to_fval_add_vars_cons :
    forall bv1 bv2 vars f,
        (forall fv,
            bval_to_fval f bv1 = fv
        ->  bval_to_fval (add_vars vars f) bv1 = fv)
    ->  (forall fv,
            bval_to_fval f bv2 = fv
        ->  bval_to_fval (add_vars vars f) bv2 = fv)
    ->  (forall fv,
            bval_to_fval f (VCons bv1 bv2) = fv
        ->  bval_to_fval (add_vars vars f) (VCons bv1 bv2) = fv).
  Proof.
    (* #1 Intro: intro/induction/destruct/inversion/simpl *)
    itr - bv1 bv2 vars f Heq_v1 Heq_v2 fv Heq.
    smp + Heq.
    (* #2 Apply: apply/inversion/destruct/rewrite *)
    app - fcons_inj in Heq.
    ivc - Heq as fv1 Heq: x H.
    ivc - Heq as fv2 Heq: x H.
    des - Heq as [Hv1 [Hv2 Heq]].
    cwr - Heq.
    (* #3 Specialize: specialize/apply *)
    spc - Heq_v1: fv1 Hv1.
    spc - Heq_v2: fv2 Hv2.
    (* #4 Rewrite: f_equal/rewrite/assumption *)
    f_equal; asm.
  Qed.



  Theorem bval_to_fval_add_vars_tuple :
    forall bvl vars f,
        Forall (fun bv =>
            (forall fv,
                  bval_to_fval f bv = fv
              ->  bval_to_fval (add_vars vars f) bv = fv))
          bvl
    ->  (forall fv,
            bval_to_fval f (VTuple bvl) = fv
        ->  bval_to_fval (add_vars vars f) (VTuple bvl) = fv).
  Proof.
    (* #1 Intro: intro/induction/destruct/inversion/simpl *)
    itr - bvl vars f HForall.
    ind - bvl as [| bv bvl Heq_vl]: itr; bmp |> smp.
    itr - fv' Heq.
    ivr - HForall; clr - HForall H H0 x l; ren - Heq_v HForall: H1 H2.
    smp + Heq.
    (* #2 Apply: apply/inversion/destruct/rewrite *)
    app - ftuple_inj in Heq.
    ivc - Heq as fv Heq: x H.
    ivc - Heq as fvl Heq: x H.
    des - Heq as [Hv [Hvl Heq]].
    cwr - Heq in *.
    (* #3 Specialize: specialize/apply *)
    app - bval_to_fval_tuple in Hvl.
    spc - Heq_v: fv Hv.
    spc - Heq_vl: HForall (Syntax.VTuple fvl) Hvl.
    app - bval_to_fval_tuple in Heq_vl.
    (* #4 Rewrite: f_equal/rewrite/assumption *)
    f_equal.
    bwr - Heq_v Heq_vl.
  Qed.



  Theorem bval_to_fval_add_vars_map :
    forall bvl vars f,
        Forall (fun bv =>
            (forall fv,
                bval_to_fval f bv.1 = fv
            ->  bval_to_fval (add_vars vars f) bv.1 = fv)
        /\  (forall fv,
                bval_to_fval f bv.2 = fv
            ->  bval_to_fval (add_vars vars f) bv.2 = fv))
          bvl
    ->  (forall fv,
            bval_to_fval f (VMap bvl) = fv
        ->  bval_to_fval (add_vars vars f) (VMap bvl) = fv).
  Proof.
    (* #1 Intro: intro/induction/destruct/inversion/simpl *)
    itr - bvl vars f HForall.
    ind - bvl as [| bv bvl Heq_vl]: itr; bmp |> smp.
    des - bv as [bv1 bv2].
    itr - fv' Heq.
    ivr - HForall; clr - HForall H H0 x l; ren - Heq_v HForall: H1 H2.
    des - Heq_v as [Heq_v1 Heq_v2].
    smp + Heq Heq_v1 Heq_v2.
    (* #2 Apply: apply/inversion/destruct/rewrite *)
    app - fmap_inj in Heq.
    ivc - Heq as fv1 Heq: x H.
    ivc - Heq as fv2 Heq: x H.
    ivc - Heq as fvl Heq: x H.
    des - Heq as [Hv1 [Hv2 [Hvl Heq]]].
    cwr - Heq in *.
    (* #3 Specialize: specialize/apply *)
    app - bval_to_fval_map in Hvl.
    spc - Heq_v1: fv1 Hv1.
    spc - Heq_v2: fv2 Hv2.
    spc - Heq_vl: HForall (Syntax.VMap fvl) Hvl.
    app - bval_to_fval_map in Heq_vl.
    (* #4 Rewrite: f_equal/rewrite/assumption *)
    f_equal.
    bwr - Heq_v1 Heq_v2 Heq_vl.
  Qed.



  Theorem bval_to_fval_add_vars :
    forall bv vars f fv,
        bval_to_fval f bv = fv
    ->  bval_to_fval (add_vars vars f) bv = fv.
  Proof.
    (* #1 Intro: intro/induction using ind_val *)
    itr - bv vars f.
    ind + ind_val - bv.
    (* #2 Nil & Lit: *)
    1-2: itr - fv Heq; ivr - Heq; bbn.
    (* #3 Cons: *)
    1: bse - bval_to_fval_add_vars_cons: bv1 bv2 vars f IHbv1 IHbv2.
    (* #4 Tuple: *)
    2: bse - bval_to_fval_add_vars_tuple: l vars f H.
    (* #5 Map: *)
    2: bse - bval_to_fval_add_vars_map: l vars f H.
    (* #6 Clos: *)
    admit.
  Admitted.



  Theorem bvs_to_fvs_add_vars :
    forall bvs fvs vars f,
        bvs_to_fvs f bvs = fvs
    ->  bvs_to_fvs (add_vars vars f) bvs = fvs.
  Proof.
    (* #1 Intro: intro/induction/destruct/inversion/simpl *)
    itr - bvs.
    ind - bvs as [| bv bvs IHbvs]: itr; bvs - H.
    itr - fvs vars f Heq.
    des - fvs as [| fv fvs]: ivs - Heq.
    smp + Heq.
    (* #2 Apply: apply/inversion/destruct/rewrite *)
    app - cons_inj in Heq.
    des - Heq as [Hv Hvs].
    (* #3 Specialize: specialize/apply *)
    psc - bval_to_fval_add_vars as Heq_v: bv vars f fv Hv.
    spc - IHbvs as Heq_vs: fvs vars f Hvs.
    (* #4 Rewrite: f_equal/rewrite/assumption *)
    bwr - Heq_v Heq_vs.
  Qed.



  Lemma bvs_to_fvs_length :
    forall fns vs,
      Datatypes.length (bvs_to_fvs fns vs)
    = Datatypes.length vs.
  Proof.
    itr.
    ind - vs as [| v vs Hvs]: bmp |> smp.
    bwr - Hvs.
  Qed.



End ConverterLemmas_Value_Main.






Section ConverterLemmas_Expression.



  Theorem bexp_to_fexp_add_vars_comm :
    forall env e vars1 vars2 f,
      bexp_to_fexp
        (add_vars vars1 (add_vars vars2 f))
        (subst_env (measure_exp e + measure_env env) env e)
    = bexp_to_fexp
        (add_vars vars2 (add_vars vars1 f))
        (subst_env (measure_exp e + measure_env env) env e).
  Proof.
    (* #1 Intro: *)
    itr.
    ind + ind_exp - e.
    (* #2 Nil & Lit: *)
    2-3: bmp.
    admit.
  Admitted.



  Theorem bexp_to_fexp_add_vars :
    forall e fns vars vs env,
        bexp_to_fexp_subst fns (append_vars_to_env vars vs env) e
      = (bexp_to_fexp_subst (add_vars vars fns) (rem_vars vars env) e)
        .[list_subst (bvs_to_fvs fns vs) idsubst].
  Proof.
    (* #1 Intro: *)
    itr - e.
    ind + ind_exp - e; itr; ufl - bexp_to_fexp_subst measure_env_exp; smp.
    8,10: ren - el: l.
    (* #2 Atom: (Nil & Lit) {SAME} *)
    2-3: bbn.
    (* #3 Double: [e1;e2] (Cons & Seq) {SAME} *)
    5: {
      (* +1 Simplify: rename/induction/inversion *)
      ren - Heq_e1 Heq_e2: IHe1 IHe2.
      (* +2 Measure Reduction: rewrite *)
      do 2 rwr - mred_e1e2_e1.
      do 2 rwr - mred_e1e2_e2.
      (* +3 Specialize: specialize/injection *)
      spe - Heq_e1: fns vars vs env.
      spc - Heq_e2: fns vars vs env.
      (* +4 Rewrite: unfold/rewrite *)
      ufl - bexp_to_fexp_subst measure_env_exp in *.
      bwr - Heq_e1 Heq_e2.
    }
    11: {
      (* +1 Simplify: rename/induction/inversion *)
      ren - Heq_e1 Heq_e2: IHe1 IHe2.
      (* +2 Measure Reduction: rewrite *)
      do 2 rwr - mred_e1e2_e1.
      do 2 rwr - mred_e1e2_e2.
      (* +3 Specialize: specialize/injection *)
      spe - Heq_e1: fns vars vs env.
      spc - Heq_e2: fns vars vs env.
      (* +4 Rewrite: unfold/rewrite *)
      ufl - bexp_to_fexp_subst measure_env_exp in *.
      bwr - Heq_e1 Heq_e2.
    }
    (* #4 List: [(e::el)] (Tuple, Values & PrimOp) {SAME} *)
    5: {
      (* +1 Simplify: rename/induction/inversion *)
      ren - HForall: H.
      ind - el as [| e el Heq_el]: bbn |> smp.
      ivr - HForall; clr - HForall H H0 x l; ren - Heq_e HForall: H1 H2.
      (* +2 Measure Reduction: rewrite *)
      do 2 rwr - mred_eel_e.
      do 2 rwr - mred_eel_el.
      (* +3 Specialize: specialize/injection *)
      spc - Heq_e: fns vars vs env.
      spc - Heq_el: HForall.
      inj - Heq_el as Heq_el.
      (* +4 Rewrite: unfold/rewrite *)
      ufl - bexp_to_fexp_subst measure_env_exp in *.
      bwr - Heq_e Heq_el.
    }
    1: {
      (* +1 Simplify: rename/induction/inversion *)
      ren - HForall: H.
      ind - el as [| e el Heq_el]: bbn |> smp.
      ivr - HForall; clr - HForall H H0 x l; ren - Heq_e HForall: H1 H2.
      (* +2 Measure Reduction: rewrite *)
      do 2 rwr - mred_eel_e.
      do 2 rwr - mred_eel_el.
      (* +3 Specialize: specialize/injection *)
      spc - Heq_e: fns vars vs env.
      spc - Heq_el: HForall.
      inj - Heq_el as Heq_el.
      (* +4 Rewrite: unfold/rewrite *)
      ufl - bexp_to_fexp_subst measure_env_exp in *.
      bwr - Heq_e Heq_el.
    }
    4:
    {
      (* +1 Simplify: rename/induction/inversion *)
      ren - HForall: H.
      ind - el as [| e el Heq_el]: bbn |> smp.
      ivr - HForall; clr - HForall H H0 x l; ren - Heq_e HForall: H1 H2.
      (* +2 Measure Reduction: rewrite *)
      do 2 rwr - mred_eel_e.
      do 2 rwr - mred_eel_el.
      (* +3 Specialize: specialize/injection *)
      spc - Heq_e: fns vars vs env.
      spc - Heq_el: HForall.
      inj - Heq_el as Heq_el.
      (* +4 Rewrite: unfold/rewrite *)
      ufl - bexp_to_fexp_subst measure_env_exp in *.
      bwr - Heq_e Heq_el.
    }
    (* Fun *)
    3: {
      (* +1 Simplify: rename/induction/inversion *)
      ren - Heq_e: IHe.
      (* +3 Specialize: specialize/injection *)
      spc - Heq_e: (add_vars vl fns) vars vs env.
      (* +4 Rewrite: unfold/rewrite *)
      ufl - bexp_to_fexp_subst measure_env_exp in *.
      rwr - bexp_to_fexp_add_vars_comm in Heq_e.
      rwr - bexp_to_fexp_add_vars_comm in Heq_e.
      rwr - Heq_e.
      (* bwr - Heq_e. *)
      (*
      list_subst (bvs_to_fvs (add_vars vl fns) vs) idsubst
      =
      upn (Datatypes.length vl) (list_subst (bvs_to_fvs fns vs) idsubst)
      *)
      admit.
    }
    1-9: admit.
  Admitted.



End ConverterLemmas_Expression.