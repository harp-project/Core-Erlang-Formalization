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
  - measure_val_reduction
* Expression
  - measure_exp_reduction
* Mapper
  - measure_val_reduction_list
  - measure_val_reduction_map
* Minimum
  - measure_val_reduction_min
  - measure_val_reduction_list_min
  - measure_val_reduction_map_min
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



Tactic Notation "ass_le_trans"
  constr(H1le3) ident(n2) ident(H1le2) ident(H2le3)
  "as" ident(H)
  :=
  assert H1le3 as H
    by (apply Nat.le_trans with (m := n2);
      [exact H1le2 | exact H2le3]).



Tactic Notation "ass_le_trans2"
  constr(H1le4) ident(n2) ident(n3) ident(H1le2) ident(H2le3) ident(H3le4)
  "as" ident(H)
  :=
  assert H1le4 as H
    by (apply Nat.le_trans with (m := n3);
      [apply Nat.le_trans with (m := n2);
        [exact H1le2 | exact H2le3]
      | exact H3le4]).



(* End MeasureLemmas_Tactics *)






Section MeasureLemmas_Value.



(** NOTES
* FULL NAME:
  - Measure Reduction at Value
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
  Theorem measure_val_reduction :
    forall v n1 n2,
      measure_val v <= n1
    ->
      measure_val v <= n2
    ->
      bval_to_bexp (subst_env n1) v
    =
      bval_to_bexp (subst_env n2) v.
  Proof.
    intros v n1 n2 Hn1 Hn2.
    induction v using derived_Value_ind.
    * by cbn.
    * by cbn.
    * (* Cons *)
      remember
        (BigStep.Syntax.VCons v1 v2)
        as vcons
        eqn:Heq_vcons.
      assert (measure_val v1 ≤ measure_val vcons) as Hv1.
      rewrite Heq_vcons; slia.
      assert (measure_val v2 ≤ measure_val vcons) as Hv2.
      rewrite Heq_vcons; slia.
      assert (measure_val v1 ≤ n1) as Hv1n1.
      {
        apply Nat.le_trans with (m := measure_val vcons).
        - exact Hv1.
        - exact Hn1.
      }
      assert (measure_val v1 ≤ n2) as Hv1n2.
      {
        apply Nat.le_trans with (m := measure_val vcons).
        - exact Hv1.
        - exact Hn2.
      }
      assert (measure_val v2 ≤ n1) as Hv2n1.
      {
        apply Nat.le_trans with (m := measure_val vcons).
        - exact Hv2.
        - exact Hn1.
      }
      assert (measure_val v2 ≤ n2) as Hv2n2.
      {
        apply Nat.le_trans with (m := measure_val vcons).
        - exact Hv2.
        - exact Hn2.
      }
      clear Hv1 Hv2 Hn1 Hn2.
      specialize (IHv1 Hv1n1 Hv1n2).
      specialize (IHv2 Hv2n1 Hv2n2).
      inv Heq_vcons.
      clear H Hv1n1 Hv1n2 Hv2n1 Hv2n2.
      cbn.
      rewrite IHv1.
      rewrite IHv2.
      reflexivity.
    * (* Clos *)
      (*
      simpl in *.
      destruct ext.
      - f_equal.
      *)
      rename H into HForall.
      induction ref as [| x env IHenv].
      - cbn.
        destruct ext; destruct funid.
        1-2, 4: rewrite rem_vars_empty; by do 2 rewrite subst_env_empty.
        rewrite rem_nfifes_empty.
        f_equal.
        unfold bval_to_bexp_ext.
        apply map_ext.
        intros [fid [vl e]].
        rewrite rem_vars_empty.
        do 2 rewrite subst_env_empty.
        reflexivity.
      - invc HForall.
        rename H1 into Hx.
        rename H2 into HForall.
        specialize (IHenv HForall).
        clear HForall.
        remember
          (VClos env ext id params body funid)
          as v_env
          eqn:Heq_v_env.
        remember
          (VClos (x :: env) ext id params body funid)
          as v_xenv
          eqn:Heq_v_xenv.
        assert (measure_val v_env ≤ measure_val v_xenv) as Henv.
        {
          rewrite Heq_v_env.
          rewrite Heq_v_xenv.
          simpl.
          unfold measure_env'.
          slia.
        }
        assert (measure_val x.2 ≤ n1) as Hxn1.
        {
          apply Nat.le_trans with (m := measure_val v_xenv).
          - rewrite Heq_v_xenv. destruct x. simpl. unfold measure_env'. slia.
          - exact Hn1.
        }
        assert (measure_val v_env ≤ n1) as Henvn1.
        {
          apply Nat.le_trans with (m := measure_val v_xenv).
          - exact Henv.
          - exact Hn1.
        }
        assert (measure_val x.2 ≤ n2) as Hxn2.
        {
          apply Nat.le_trans with (m := measure_val v_xenv).
          - rewrite Heq_v_xenv. destruct x. simpl. unfold measure_env'. slia.
          - exact Hn2.
        }
        assert (measure_val v_env ≤ n2) as Henvn2.
        {
          apply Nat.le_trans with (m := measure_val v_xenv).
          - exact Henv.
          - exact Hn2.
        }
        specialize (Hx Hxn1 Hxn2).
        specialize (IHenv Henvn1 Henvn2).
        clear Hxn1 Hxn2 Henvn1 Henvn2 Henv.
        inv Heq_v_env.
        clear H Hn2 Hn1.
        simpl in *.
        destruct ext; destruct funid.
        + f_equal.
          inv IHenv.
          rename H0 into Henv.
          destruct x.
          simpl in *.
          admit.
        + admit.
        + admit.
        + admit.
    * (* Tuple *)
      induction l as [| v vl IHvl].
      - by cbn.
      - inv H.
        rename H2 into Hv.
        rename H3 into HForall.
        remember
          (BigStep.Syntax.VTuple vl)
          as vtuple_vl
          eqn:Heq_vtuple_vl.
        remember
          (BigStep.Syntax.VTuple (v :: vl))
          as vtuple_vvl
          eqn:Heq_vtuple_vvl.
        assert (measure_val vtuple_vl ≤ measure_val vtuple_vvl) as Hvl.
        {
          rewrite Heq_vtuple_vl.
          rewrite Heq_vtuple_vvl.
          simpl.
          unfold measure_list.
          simpl.
          slia.
        }
        assert (measure_val v ≤ n1) as Hvn1.
        {
          apply Nat.le_trans with (m := measure_val vtuple_vvl).
          - inv Heq_vtuple_vvl. cbn. lia.
          - exact Hn1.
        }
        assert (measure_val vtuple_vl ≤ n1) as Hvln1.
        {
          apply Nat.le_trans with (m := measure_val vtuple_vvl).
          - exact Hvl.
          - exact Hn1.
        }
        assert (measure_val v ≤ n2) as Hvn2.
        {
          apply Nat.le_trans with (m := measure_val vtuple_vvl).
          - inv Heq_vtuple_vvl. cbn. lia.
          - exact Hn2.
        }
        assert (measure_val vtuple_vl ≤ n2) as Hvln2.
        {
          apply Nat.le_trans with (m := measure_val vtuple_vvl).
          - exact Hvl.
          - exact Hn2.
        }
        clear Hn1 Hn2.
        specialize (Hv Hvn1 Hvn2).
        specialize (IHvl HForall Hvln1 Hvln2).
        invc Heq_vtuple_vl.
        clear H Hvn1 Hvln1 Hvn2 Hvln2 Hvl HForall.
        simpl in *.
        injection IHvl as Hmap_vl.
        rewrite Hmap_vl.
        rewrite Hv.
        reflexivity.
    * (* Map *)
      induction l as [| (v1, v2) vl IHvl].
      - by cbn.
      - inv H.
        rename H2 into Hv.
        rename H3 into HForall.
        simpl in Hv.
        destruct Hv as [Hv1 Hv2].
        remember
          (BigStep.Syntax.VMap vl)
          as vmap_vl
          eqn:Heq_vmap_vl.
        remember
          (BigStep.Syntax.VMap ((v1, v2) :: vl))
          as vmap_vvl
          eqn:Heq_vmap_vvl.
        assert (measure_val vmap_vl ≤ measure_val vmap_vvl) as Hvl.
        {
          rewrite Heq_vmap_vl.
          rewrite Heq_vmap_vvl.
          simpl.
          unfold measure_list.
          unfold measure_map.
          slia.
        }
        assert (measure_val v1 ≤ n1) as Hv1n1.
        {
          apply Nat.le_trans with (m := measure_val vmap_vvl).
          - inv Heq_vmap_vvl. cbn. lia.
          - exact Hn1.
        }
        assert (measure_val v2 ≤ n1) as Hv2n1.
        {
          apply Nat.le_trans with (m := measure_val vmap_vvl).
          - inv Heq_vmap_vvl. cbn. lia.
          - exact Hn1.
        }
        assert (measure_val vmap_vl ≤ n1) as Hvln1.
        {
          apply Nat.le_trans with (m := measure_val vmap_vvl).
          - exact Hvl.
          - exact Hn1.
        }
        assert (measure_val v1 ≤ n2) as Hv1n2.
        {
          apply Nat.le_trans with (m := measure_val vmap_vvl).
          - inv Heq_vmap_vvl. cbn. lia.
          - exact Hn2.
        }
        assert (measure_val v2 ≤ n2) as Hv2n2.
        {
          apply Nat.le_trans with (m := measure_val vmap_vvl).
          - inv Heq_vmap_vvl. cbn. lia.
          - exact Hn2.
        }
        assert (measure_val vmap_vl ≤ n2) as Hvln2.
        {
          apply Nat.le_trans with (m := measure_val vmap_vvl).
          - exact Hvl.
          - exact Hn2.
        }
        clear Hn1 Hn2.
        specialize (Hv1 Hv1n1 Hv1n2).
        specialize (Hv2 Hv2n1 Hv2n2).
        specialize (IHvl HForall Hvln1 Hvln2).
        invc Heq_vmap_vl.
        clear H Hv1n1 Hv2n1 Hvln1 Hv1n2 Hv2n2 Hvln2 Hvl HForall.
        simpl in *.
        injection IHvl as Hvl.
        rewrite Hv1.
        rewrite Hv2.
        rewrite Hvl.
        reflexivity.
  Admitted.



End MeasureLemmas_Value.






Section MeasureLemmas_Expression.



Theorem measure_env_exp_reduction :
    forall env e n1 n2,
        measure_env_exp env e <= n1
    ->  measure_env_exp env e <= n2
    ->  subst_env n1 env e
    =   subst_env n2 env e.
  Proof.
  Admitted.



End MeasureLemmas_Expression.






Section MeasureLemmas_Mappers.



  Theorem measure_val_reduction_list :
    forall vl n1 n2,
      list_sum (map measure_val vl) <= n1
    ->
      list_sum (map measure_val vl) <= n2
    ->
      map (bval_to_bexp (subst_env n1)) vl
    =
      map (bval_to_bexp (subst_env n2)) vl.
  Proof.
    int vl n1 n2 Hvvl_n1 Hvvl_n2.
    (* + induction (base solved) *)
    ind vl. 1: bcbn.
    (* + rename/remember *)
    ren v <- a.
    rem mv mvl mvvl <-
      (measure_val v)
      (list_sum (map measure_val vl))
      (list_sum (map measure_val (v :: vl)))
      as Hmv Hmvl Hmvvl.
    (* + assert triv *)
    ass (mv <= mvvl) as Hv_vvl by (rwr Hmv Hmvvl; slia).
    ass (mvl <= mvvl) as Hvl_vvl by (rwr Hmvl Hmvvl; slia).
    (* + assert trans *)
    ass_le_trans (mv <= n1) mvvl Hv_vvl Hvvl_n1 as Hv_n1.
    ass_le_trans (mv <= n2) mvvl Hv_vvl Hvvl_n2 as Hv_n2.
    ass_le_trans (mvl <= n1) mvvl Hvl_vvl Hvvl_n1 as Hvl_n1.
    ass_le_trans (mvl <= n2) mvvl Hvl_vvl Hvvl_n2 as Hvl_n2.
    (* + clear/rewrite *)
    rwrc Hmv Hmvl Hmvvl in *.
    clr - IHvl Hv_n1 Hv_n2 Hvl_n1 Hvl_n2.
    (* + specialize/pose proof *)
    pspc measure_val_reduction: v n1 n2 Hv_n1 Hv_n2 as Hv.
    spcc IHvl: Hvl_n1 Hvl_n2 as Hvl.
    (* rewrite *)
    cbn.
    by rwr Hv Hvl.
  Qed.



  Theorem measure_val_reduction_map :
    forall vl n1 n2,
      list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl) <= n1
    ->
      list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl) <= n2
    ->
      map
        (prod_map
          (bval_to_bexp (subst_env n1))
          (bval_to_bexp (subst_env n1)))
        vl
    =
      map
        (prod_map
          (bval_to_bexp (subst_env n2))
          (bval_to_bexp (subst_env n2)))
        vl.
  Proof.
    int vl n1 n2 Hvvl_n1 Hvvl_n2.
    (* + induction (base solved) *)
    ind vl. 1: bcbn.
    (* + rename/remember *)
    ren v <- a.
    rem mv1 mv2 mv mvl mvvl <-
      (measure_val v.1)
      (measure_val v.2)
      (measure_val v.1 + measure_val v.2)
      (list_sum (map (λ '(x, y), measure_val x + measure_val y) vl))
      (list_sum (map (λ '(x, y), measure_val x + measure_val y) (v :: vl)))
      as Hmv1 Hmv2 Hmv Hmvl Hmvvl.
    (* + assert triv *)
    ass (mv1 <= mv) as Hv1_v by slia.
    ass (mv2 <= mv) as Hv2_v by slia.
    ass (mv <= mvvl) as Hv_vvl by (rwr Hmv Hmvvl; des v; slia).
    ass (mvl <= mvvl) as Hvl_vvl by (rwr Hmvl Hmvvl; des v; slia).
    (* + assert trans *)
    ass_le_trans2 (mv1 <= n1) mv mvvl Hv1_v Hv_vvl Hvvl_n1 as Hv1_n1.
    ass_le_trans2 (mv2 <= n1) mv mvvl Hv2_v Hv_vvl Hvvl_n1 as Hv2_n1.
    ass_le_trans2 (mv1 <= n2) mv mvvl Hv1_v Hv_vvl Hvvl_n2 as Hv1_n2.
    ass_le_trans2 (mv2 <= n2) mv mvvl Hv2_v Hv_vvl Hvvl_n2 as Hv2_n2.
    ass_le_trans (mvl <= n1) mvvl Hvl_vvl Hvvl_n1 as Hvl_n1.
    ass_le_trans (mvl <= n2) mvvl Hvl_vvl Hvvl_n2 as Hvl_n2.
    (* + clear/rewrite *)
    rwrc Hmv1 Hmv2 Hmv Hmvl Hmvvl in *.
    clr - IHvl Hv1_n1 Hv1_n2 Hv2_n1 Hv2_n2 Hvl_n1 Hvl_n2.
    (* + specialize/pose proof *)
    pspc measure_val_reduction: v.1 n1 n2 Hv1_n1 Hv1_n2 as Hv1.
    pspc measure_val_reduction: v.2 n1 n2 Hv2_n1 Hv2_n2 as Hv2.
    spcc IHvl: Hvl_n1 Hvl_n2 as Hvl.
    (* rewrite *)
    des v as [v1 v2].
    cbn in *.
    by rwr Hv1 Hv2 Hvl.
  Qed.



End MeasureLemmas_Mappers.






Section MeasureLemmas_Min.



  Theorem measure_val_reduction_min :
    forall v n,
        measure_val v <= n
    ->  bval_to_bexp (subst_env n) v
    =   bval_to_bexp (subst_env (measure_val v)) v.
  Proof.
    intros v n Hle1.
    assert (measure_val v <= measure_val v) as Hle2 by lia.
    by psp measure_val_reduction: v n (measure_val v) Hle1 Hle2.
  Qed.



  Theorem measure_val_reduction_list_min :
  forall vl n,
    list_sum (map measure_val vl) <= n
  ->
    map (bval_to_bexp (subst_env n)) vl
  =
    map (bval_to_bexp (subst_env (measure_val (VTuple vl)))) vl.
  Proof.
    int vl n Hle1.
    assert (list_sum (map measure_val vl) <= measure_val (VTuple vl)) as Hle2
      by (smp; unfold measure_list; slia).
    by psp measure_val_reduction_list:
      vl n (measure_val (VTuple vl)) Hle1 Hle2.
  Qed.



  Theorem measure_val_reduction_map_min :
    forall vl n,
      list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl) <= n
    ->
      map
        (prod_map
          (bval_to_bexp (subst_env n))
          (bval_to_bexp (subst_env n)))
        vl
    =
      map
        (prod_map
          (bval_to_bexp (subst_env (measure_val (VMap vl))))
          (bval_to_bexp (subst_env (measure_val (VMap vl)))))
        vl.
  Proof.
      intros vl n Hle1.
      ass (list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl)
          <= measure_val (VMap vl))
        as Hle2
        by (smp; unfold measure_map; slia).
      by psp measure_val_reduction_map: vl n (measure_val (VMap vl)) Hle1 Hle2.
    Qed.



  Theorem measure_env_exp_reduction_min :
    forall env e n,
        measure_env_exp env e <= n
    ->  subst_env n env e
    =   subst_env (measure_env_exp env e) env e.
  Proof.
    int env e n Hle1.
    ass (measure_env_exp env e <= measure_env_exp env e) as Hle2 by lia.
    by psp measure_env_exp_reduction: env e n (measure_env_exp env e) Hle1 Hle2.
  Qed.



End MeasureLemmas_Min.





Section MeasureLemmas_Specials.



  Lemma lered :
    forall a b c,
        (a + c <= b + c)
    <-> (a <= b).
  Proof.
    int; lia.
  Qed.

Ltac mexp_le :=
  unfold measure_env_exp;
  smp;
  try unfold measure_list;
  smp;
  lia.

Ltac ass_mexp_le env e1 e2 Hle :=
  assert (measure_env_exp env e1 <= measure_env_exp env e2) as Hle by mexp_le.

Ltac psp_mexp_le env e1 e2 Hle :=
  pose proof measure_env_exp_reduction_min env e1 (measure_env_exp env e2) Hle.

Ltac solve_mred_exp env e1 e2 Hle :=
  ass_mexp_le env e1 e2 Hle;
  psp_mexp_le env e1 e2 Hle;
  assumption.



  Theorem mred_vcons_v1 :
    forall v1 v2,
        bval_to_bexp (subst_env (measure_val (VCons v1 v2))) v1
    =   bval_to_bexp (subst_env (measure_val v1)) v1.
  Proof.
    int.
    ass (measure_val v1 <= measure_val (VCons v1 v2)) as Hle by slia.
    by psp measure_val_reduction_min: v1 (measure_val (VCons v1 v2)) Hle.
  Qed.



  Theorem mred_vcons_v2 :
    forall v1 v2,
        bval_to_bexp (subst_env (measure_val (VCons v1 v2))) v2
    =   bval_to_bexp (subst_env (measure_val v2)) v2.
  Proof.
    int.
    ass (measure_val v2 <= measure_val (VCons v1 v2)) as Hle by slia.
    by psp measure_val_reduction_min: v2 (measure_val (VCons v1 v2)) Hle.
  Qed.



  Theorem mred_vtuple_v :
    forall v vl,
        bval_to_bexp (subst_env (measure_val (VTuple (v :: vl)))) v
    =   bval_to_bexp (subst_env (measure_val v)) v.
  Proof.
    int.
    ass (measure_val v <= measure_val (VTuple (v :: vl))) as Hle by clia.
    by psp measure_val_reduction_min: v (measure_val (VTuple (v :: vl))) Hle.
  Qed.



  Theorem mred_vtuple_vl :
    forall v vl,
      map (bval_to_bexp (subst_env (measure_val (VTuple (v :: vl))))) vl
    =
      map (bval_to_bexp (subst_env (measure_val (VTuple vl)))) vl.
  Proof.
    int.
    ass (list_sum (map measure_val vl) <= measure_val (VTuple (v :: vl))) as Hle
      by (smp; unfold measure_list; slia).
    by psp measure_val_reduction_list_min:
      vl (measure_val (VTuple (v :: vl))) Hle.
  Qed.



  Theorem mred_vmap_v1 :
    forall v1 v2 vl,
        bval_to_bexp (subst_env (measure_val (VMap ((v1, v2) :: vl)))) v1
    =   bval_to_bexp (subst_env (measure_val v1)) v1.
  Proof.
    int.
    ass (measure_val v1 <= measure_val (VMap ((v1, v2) :: vl))) as Hle by clia.
    by psp measure_val_reduction_min:
      v1 (measure_val (VMap ((v1, v2) :: vl))) Hle.
  Qed.



  Theorem mred_vmap_v2 :
    forall v1 v2 vl,
        bval_to_bexp (subst_env (measure_val (VMap ((v1, v2) :: vl)))) v2
    =   bval_to_bexp (subst_env (measure_val v2)) v2.
  Proof.
    int.
    ass (measure_val v2 <= measure_val (VMap ((v1, v2) :: vl))) as Hle by clia.
    by psp measure_val_reduction_min:
      v2 (measure_val (VMap ((v1, v2) :: vl))) Hle.
  Qed.



  Theorem mred_vmap :
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
    int.
    ass (list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl)
        <= (measure_val (VMap ((v1, v2) :: vl))))
      as Hle
      by (smp; unfold measure_map; slia).
    by psp measure_val_reduction_map_min:
      vl (measure_val (VMap ((v1, v2) :: vl))) Hle.
  Qed.



  Theorem mred_econs_e1 :
    forall env e1 e2,
        subst_env (measure_env_exp env (ECons e1 e2)) env e1
    =   subst_env (measure_env_exp env e1) env e1.
  Proof.
    int; solve_mred_exp env e1 (ECons e1 e2) Hle.
  Qed.


  Theorem mred_econs_e2 :
    forall env e1 e2,
        subst_env (measure_env_exp env (ECons e1 e2)) env e2
    =   subst_env (measure_env_exp env e2) env e2.
  Proof.
    int; solve_mred_exp env e2 (ECons e1 e2) Hle.
  Qed.


  Theorem mred_etuple_e :
    forall env e el,
        subst_env (measure_exp (ETuple (e :: el)) + measure_env env) env e
    =   subst_env (measure_exp e + measure_env env) env e.
  Proof.
    int; solve_mred_exp env e (ETuple (e :: el)) Hle.
  Qed.







  Theorem mred_etuple_el :
    forall env e el,
      subst_env (measure_env_exp env (ETuple (e :: el))) env (ETuple el)
    = subst_env (measure_env_exp env (ETuple el)) env (ETuple el).
  Proof.
    int; solve_mred_exp env (ETuple el) (ETuple (e :: el)) Hle.
  Qed.

End MeasureLemmas_Specials.













(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: ERASENAMESLEMMAS /////////////////////////////////////////////////
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
  intros e.
  induction e using exp_ind; intros.
  * admit.
  * bcbn.
  * bcbn.
  * cbn.
    pose proof get_value_singelton as Hsgl.
    destruct (get_value (append_vars_to_env vars bvs env) (inl v)) eqn:Hd1.
    case_match. 1: apply Hsgl in Hd1; inv Hd1; inv H0.
    (*
    case_match. 2: apply Hsgl in Hd1; inv Hd1; inv H1.
    destruct (get_value env (inl v)) eqn:Hd2.
    case_match; subst; cbn in *.
    1: apply Hsgl in Hd2; inv Hd2; inv H.
    subst.
    1-3: admit.
    *)
    1-3: admit.
  * admit.
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
    specialize (IHe (add_vars vl f) bvs fvs vars env).
    admit.
    admit.
  * cbn.
    rewrite measure_env_exp_reduction_min.
    2: unfold measure_env_exp; lia.
    rewrite measure_env_exp_reduction_min with (e := e2).
    2: unfold measure_env_exp; lia.
    rewrite measure_env_exp_reduction_min with (env := env).
    2: unfold measure_env_exp; lia.
    rewrite measure_env_exp_reduction_min with (env := env) (e := e2).
    2: unfold measure_env_exp; lia.
    specialize (IHe1 f bvs fvs vars env).
    specialize (IHe2 f bvs fvs vars env).
    by rewrite IHe1, IHe2.
  * cbn.
    induction l as [| e el].
    - bcbn.
    - invc H: He Hel <- H3 H4.
      specialize (IHel Hel).
      admit.
Admitted.