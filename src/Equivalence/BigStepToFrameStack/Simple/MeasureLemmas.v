From CoreErlang.Equivalence.BigStepToFrameStack.Simple Require Export SubstituteLemmas.
From CoreErlang.Equivalence.BigStepToFrameStack Require Export Measure.

From CoreErlang.Equivalence.BigStepToFrameStack Require Import Induction.

Import BigStep.

(**
* Value
  - measure_val_reduction
  - measure_val_reduction_list
  - measure_val_reduction_map
  - measure_val_reduction_min
* EnvExpression
  - measure_env_exp_reduction
  - measure_env_exp_reduction_min
*)



Section Value.



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
      - inv HForall.
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
          unfold measure_env.
          slia.
        }
        assert (measure_val x.2 ≤ n1) as Hxn1.
        {
          apply Nat.le_trans with (m := measure_val v_xenv).
          - rewrite Heq_v_xenv. destruct x. simpl. unfold measure_env. slia.
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
          - rewrite Heq_v_xenv. destruct x. simpl. unfold measure_env. slia.
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
        inv Heq_vtuple_vl.
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
        inv Heq_vmap_vl.
        clear H Hv1n1 Hv2n1 Hvln1 Hv1n2 Hv2n2 Hvln2 Hvl HForall.
        simpl in *.
        injection IHvl as Hvl.
        rewrite Hv1.
        rewrite Hv2.
        rewrite Hvl.
        reflexivity.
  Admitted.



  Theorem measure_val_reduction_list :
    forall vl v1 v2,
      list_sum (map measure_val vl) <= measure_val v1
    ->
      list_sum (map measure_val vl) <= measure_val v2
    ->
      map (bval_to_bexp (subst_env (measure_val v1))) vl
    =
      map (bval_to_bexp (subst_env (measure_val v2))) vl.
  Proof.
    intros vl v1 v2 Hv1 Hv2.
    induction vl.
    * by cbn.
    * rename a into v.
      assert (measure_val v
        <= list_sum (map measure_val (v :: vl))) as Hv.
      slia.
      assert (list_sum (map measure_val vl)
        <= list_sum (map measure_val (v :: vl))) as Hvl.
      slia.
      assert (measure_val v <= measure_val v1) as Hvv1.
      {
        apply Nat.le_trans with (m := list_sum (map measure_val (v :: vl))).
          - exact Hv.
          - exact Hv1.
      }
      assert (list_sum (map measure_val vl) <= measure_val v1) as Hvlv1.
      {
        apply Nat.le_trans with (m := list_sum (map measure_val (v :: vl))).
          - exact Hvl.
          - exact Hv1.
      }
      assert (measure_val v <= measure_val v2) as Hvv2.
      {
        apply Nat.le_trans with (m := list_sum (map measure_val (v :: vl))).
          - exact Hv.
          - exact Hv2.
      }
      assert (list_sum (map measure_val vl) <= measure_val v2) as Hvlv2.
      {
        apply Nat.le_trans with (m := list_sum (map measure_val (v :: vl))).
          - exact Hvl.
          - exact Hv2.
      }
      clear Hv Hvl Hv1 Hv2.
      specialize (IHvl Hvlv1 Hvlv2).
      pose proof measure_val_reduction
        v (measure_val v1) (measure_val v2) Hvv1 Hvv2 as Hv.
      clear Hvv1 Hvlv1 Hvv2 Hvlv2.
      cbn.
      rewrite IHvl.
      rewrite Hv.
      reflexivity.
  Qed.



  Theorem measure_val_reduction_map :
    forall vl v1 v2,
      list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl)
        <= measure_val v1
    ->
      list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl)
        <= measure_val v2
    ->
      map
        (prod_map
          (bval_to_bexp (subst_env (measure_val v1)))
          (bval_to_bexp (subst_env (measure_val v1))))
        vl
    =
      map
        (prod_map
          (bval_to_bexp (subst_env (measure_val v2)))
          (bval_to_bexp (subst_env (measure_val v2))))
        vl.
  Proof.
    intros vl v1 v2 Hvvl_v1 Hvvl_v2.
    induction vl.
    * by cbn.
    * (* + rename/remember *)
      rename a into v.
      remember
        (measure_val v1)
        as measure_v1
        eqn: Heq_v1.
      remember
        (measure_val v2)
        as measure_v2
        eqn: Heq_v2.
      remember
        (measure_val v.1)
        as measure_vx
        eqn: Heq_vx.
      remember
        (measure_val v.2)
        as measure_vy
        eqn: Heq_vy.
      remember
        (measure_val v.1 + measure_val v.2)
        as measure_v
        eqn: Heq_v.
      remember
        (list_sum (map (λ '(x, y), measure_val x + measure_val y) vl))
        as measure_vl
        eqn: Heq_vl.
      remember
        (list_sum (map (λ '(x, y), measure_val x + measure_val y) (v :: vl)))
        as measure_vvl
        eqn: Heq_vvl.
      (* + assert triv *)
      assert (measure_vx <= measure_v) as Hvx_v.
      slia.
      assert (measure_vy <= measure_v) as Hvy_v.
      slia.
      assert (measure_v <= measure_vvl) as Hv_vvl.
      rewrite Heq_v; rewrite Heq_vvl; destruct v; slia.
      assert (measure_vl <= measure_vvl) as Hvl_vvl.
      rewrite Heq_vl; rewrite Heq_vvl; slia.
      (* + assert trans *)
      assert (measure_vx <= measure_v1) as Hvx_v1.
      {
        apply Nat.le_trans with (m := measure_vvl).
        - apply Nat.le_trans with (m := measure_v).
          + exact Hvx_v.
          + exact Hv_vvl.
        - exact Hvvl_v1.
      }
      assert (measure_vy <= measure_v1) as Hvy_v1.
      {
        apply Nat.le_trans with (m := measure_vvl).
        - apply Nat.le_trans with (m := measure_v).
          + exact Hvy_v.
          + exact Hv_vvl.
        - exact Hvvl_v1.
      }
      assert (measure_vl <= measure_v1) as Hvl_v1.
      {
        apply Nat.le_trans with (m := measure_vvl).
        - exact Hvl_vvl.
        - exact Hvvl_v1.
      }
      assert (measure_vx <= measure_v2) as Hvx_v2.
      {
        apply Nat.le_trans with (m := measure_vvl).
        - apply Nat.le_trans with (m := measure_v).
          + exact Hvx_v.
          + exact Hv_vvl.
        - exact Hvvl_v2.
      }
      assert (measure_vy <= measure_v2) as Hvy_v2.
      {
        apply Nat.le_trans with (m := measure_vvl).
        - apply Nat.le_trans with (m := measure_v).
          + exact Hvy_v.
          + exact Hv_vvl.
        - exact Hvvl_v2.
      }
      assert (measure_vl <= measure_v2) as Hvl_v2.
      {
        apply Nat.le_trans with (m := measure_vvl).
        - exact Hvl_vvl.
        - exact Hvvl_v2.
      }
      rewrite Heq_vx in *.
      rewrite Heq_vy in *.
      clear Heq_vx Heq_vy Hvx_v Hvy_v Hv_vvl Hvl_vvl Hvvl_v1 Hvvl_v2.
      (* + specialize/pose proof *)
      pose proof measure_val_reduction
        v.1 measure_v1 measure_v2 Hvx_v1 Hvx_v2 as Hvx.
      pose proof measure_val_reduction
        v.2 measure_v1 measure_v2 Hvy_v1 Hvy_v2 as Hvy.
        specialize (IHvl Hvl_v1 Hvl_v2) as Hvl.
      clear - Hvx Hvy Hvl.
      (* rewrite *)
      destruct v as [x y].
      cbn in *.
      rewrite Hvx.
      rewrite Hvy.
      rewrite Hvl.
      reflexivity.
  Qed.



  Theorem measure_val_reduction_min :
    forall v n,
        measure_val v <= n
    ->  bval_to_bexp (subst_env n) v
    =   bval_to_bexp (subst_env (measure_val v)) v.
  Proof.
    intros v n Hn.
    assert (measure_val v <= measure_val v) as Hv.
    lia.
    by pose proof measure_val_reduction
      v n (measure_val v) Hn Hv.
  Qed.



End Value.






Section EnvExpression.



  Theorem measure_env_exp_reduction :
    forall env e n1 n2,
        measure_env_exp env e <= n1
    ->  measure_env_exp env e <= n2
    ->  subst_env n1 env e
    =   subst_env n2 env e.
  Proof.
  Admitted.



  Theorem measure_env_exp_reduction_min :
    forall env e n,
        measure_env_exp env e <= n
    ->  subst_env n env e
    =   subst_env (measure_env_exp env e) env e.
  Proof.
    intros env e n Hn.
    assert (measure_env_exp env e <= measure_env_exp env e) as Hv.
    lia.
    by pose proof measure_env_exp_reduction
      env e n (measure_env_exp env e) Hn Hv.
  Qed.



End EnvExpression.