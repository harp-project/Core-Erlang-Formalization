From CoreErlang.TMP.EqBF Require Export Part1Simple.

Import BigStep.













(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: MeasureLemmas ////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* Tactics
  - ass_le_trans
  - ass_le_trans2
* Value
  - mred_val
* Expression
  - measure_exp_reduction
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






(* Section MeasureLemmas_Tactics *)



Ltac triv_nle_solver := 
  smp;
  try unfold measure_env_exp;
  try unfold measure_list;
  try unfold measure_map;
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
  "-" ident(v) ident(n) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(m1) constr(m2)
  :=
  ass_nle as Hle2: (m1 <= m2);
  bse - theorem: v n m2 Hle1 Hle2.



Tactic Notation "mred_solver"
  "-" ident(v) ident(Hle)
  ":" constr(theorem) constr(m1) constr(m2)
  :=
  ass_nle as Hle: (m1 <= m2);
  bse - theorem: v m2 Hle.



Tactic Notation "mred_solver"
  "-" ident(env) ident(e) ident(n) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(m1) constr(m2)
  :=
  ass_nle as Hle2: (m1 <= m2);
  bse - theorem: env e n m2 Hle1 Hle2.



Tactic Notation "mred_solver"
  "-" ident(env) ident(e) ident(Hle)
  ":" constr(theorem) constr(m1) constr(m2)
  :=
  ass_nle as Hle: (m1 <= m2);
  bse - theorem: env e m2 Hle.



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
*)
  Theorem mred_val :
    forall v n1 n2,
        measure_val v <= n1
    ->  measure_val v <= n2
    ->  bval_to_bexp (subst_env n1) v
      = bval_to_bexp (subst_env n2) v.
  Proof.
    (* #1 Intro: intro/induction *)
    itr - v n1 n2 Hn1 Hn2.
    ind + ind_val - v.
    (* #2 Nil/Lit: cbn *)
    1-2: bbn.
    (* #3 Cons: pose proof *)
    * bse - mred_val_cons: v1 v2 n1 n2 Hn1 Hn2 IHv1 IHv2.
    (* #4 Clos *)
    * admit.
    (* #5 Tuple: pose proof *)
    * bse - mred_val_tuple: l n1 n2 Hn1 Hn2 H.
    (* #6 Map: pose proof *)
    * bse - mred_val_map: l n1 n2 Hn1 Hn2 H.
  Admitted.





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
    cwr - Hmenv in *.
    cwr - Hme1 Hme2 Hme Hmel Hmeel in *.
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
      = map (bval_to_bexp (subst_env (measure_val (VTuple vl)))) vl.
  Proof.
    itr - vl n Hle1.
    mred_solver - vl n Hle1 Hle2:
      mred_val_list
      (list_sum (map measure_val vl))
      (measure_val (VTuple vl)).
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
            (bval_to_bexp (subst_env (measure_val (VMap vl))))
            (bval_to_bexp (subst_env (measure_val (VMap vl)))))
          vl.
  Proof.
    itr - vl n Hle1.
    mred_solver - vl n Hle1 Hle2:
      mred_val_list_map
      (list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl))
      (measure_val (VMap vl)).
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
      (measure_env_exp env e)
      (measure_env_exp env e).
  Qed.


(*
  Theorem mred_exp_list :
    forall env el n,
        list_sum (map measure_exp el) + measure_env env <= n
    ->  map (subst_env n env) el
      = map (subst_env (list_sum (map measure_exp el) + measure_env env) env)
         el.
  Proof.
    itr -  env el n Hle1.
    mred_solver - env el n Hle1 Hle2:
      mred_exp
      (list_sum (map measure_exp el) + measure_env env)
      (list_sum (map measure_exp el) + measure_env env).
  Qed.
*)

End MeasureLemmas_Min.





Section MeasureLemmas_Specials.

  Lemma lered :
    forall a b c,
        (a + c <= b + c)
    <-> (a <= b).
  Proof.
    itr; lia.
  Qed.

Ltac mexp_le :=
  ufl - measure_env_exp;
  smp;
  try unfold measure_list;
  smp;
  lia.

Ltac ass_mexp_le env e1 e2 Hle :=
  assert (measure_env_exp env e1 <= measure_env_exp env e2) as Hle by mexp_le.

Ltac psp_mexp_le env e1 e2 Hle :=
  pose proof mred_exp_min env e1 (measure_env_exp env e2) Hle.

Ltac solve_mred_exp env e1 e2 Hle :=
  ass_mexp_le env e1 e2 Hle;
  psp_mexp_le env e1 e2 Hle;
  assumption.


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



  Theorem mred_vtuple_vl :
    forall v vl,
      map (bval_to_bexp (subst_env (measure_val (VTuple (v :: vl))))) vl
    = map (bval_to_bexp (subst_env (measure_val (VTuple vl)))) vl.
  Proof.
    itr.
    mred_solver - vl Hle:
      mred_val_list_min
      (list_sum (map measure_val vl))
      (measure_val (VTuple (v :: vl))).
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
    mred_solver - vl Hle:
      mred_val_list_map_min
      (list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl))
      (measure_val (VMap ((v1, v2) :: vl))).
  Qed.



  Theorem mred_econs_e1 :
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



  Theorem mred_econs_e2 :
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


(*
  Theorem mred_etuple_e :
    forall env e el,
      subst_env (measure_list measure_exp el + measure_env env) env e
    = subst_env (measure_env_exp env e) env e.
  Proof.
    itr.
    mred_solver - env e Hle:
      mred_exp_list_min
      (measure_env_exp env e)
      (measure_list measure_exp el + measure_env env).
  Qed.
*)

(*
Syntax.ETuple
    (bexp_to_fexp f
       (subst_env
          (measure_list measure_exp (e :: el) + measure_env (append_vars_to_env vars bvs env))
          (append_vars_to_env vars bvs env) e)
     :: map (bexp_to_fexp f)
          (map
             (subst_env
                (measure_list measure_exp (e :: el) +
                 measure_env (append_vars_to_env vars bvs env))
                (append_vars_to_env vars bvs env)) el))

*)



(*
  Theorem mred_etuple_e :
    forall env e el,
        subst_env (measure_exp (ETuple (e :: el)) + measure_env env) env e
    =   subst_env (measure_exp e + measure_env env) env e.
  Proof.
    itr; solve_mred_exp env e (ETuple (e :: el)) Hle.
  Qed.


  Theorem mred_etuple_el :
    forall env e el,
      subst_env (measure_env_exp env (ETuple (e :: el))) env (ETuple el)
    = subst_env (measure_env_exp env (ETuple el)) env (ETuple el).
  Proof.
    itr; solve_mred_exp env (ETuple el) (ETuple (e :: el)) Hle.
  Qed.
*)

End MeasureLemmas_Specials.













(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: CONVERTERSLEMMAS /////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)




Theorem bexp_to_fexp_add_vars :
  forall e f bvs fvs vars env,
      bvs_to_fvs f bvs = fvs
  ->  bexp_to_fexp
        f
        (subst_env
          (measure_env_exp (append_vars_to_env vars bvs env) e)
          (append_vars_to_env vars bvs env)
          e)
  =   (bexp_to_fexp
        (add_vars vars f)
        (subst_env
          (measure_env_exp env e)
          env
          e))
      .[list_subst fvs idsubst].
Proof.
  (* #1 Intro: *)
  intros e.
  induction e using ind_exp; intros.
  (* #2 Nil & Lit: *)
  2-3: bbn.
  (* #3 Values: *)
  * admit.
  (* #4 Var: *)
  * cbn.
    pose proof get_value_singelton as Hsgl.
    destruct (get_value (append_vars_to_env vars bvs env) (inl v)) eqn:Hd1.
    (* case_match. 1: apply Hsgl in Hd1; inv Hd1; inv H0. *)
    (*
    case_match. 2: apply Hsgl in Hd1; inv Hd1; inv H1.
    destruct (get_value env (inl v)) eqn:Hd2.
    case_match; subst; cbn in *.
    1: apply Hsgl in Hd2; inv Hd2; inv H.
    subst.
    1-3: admit.
    *)
(*     1-4: admit. *)
    admit.
    admit.
  (* #5 FunId: *)
  * admit.
  (* #6 Fun: *)
  * (* temporaly admit *)
    cbn.
    do 2 f_equal.
    unfold measure_env_exp in IHe.
    erewrite IHe.
    Print up_subst.
    Print list_subst.
    Print scons.
    Search upn list_subst.
    Search upn ">>".
(*     specialize (IHe (add_vars vl f) bvs fvs vars env). *)
    admit.
    admit.
  (* #7 Cons: *)
  * smp.
    do 2 rewrite mred_econs_e1.
    do 2 rewrite mred_econs_e2.
    specialize (IHe1 f bvs fvs vars env H).
    specialize (IHe2 f bvs fvs vars env H).
    by rewrite IHe1, IHe2.
  (* #7 Tuple: *)
  * cbn.
    induction l as [| e el].
    - bbn.
    - smp. ivc - H as He Hel: H3 H4.
      specialize (IHel Hel).
      admit.
Admitted.