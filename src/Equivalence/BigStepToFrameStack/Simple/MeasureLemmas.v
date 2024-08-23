From CoreErlang.Equivalence.BigStepToFrameStack.Simple Require Export Substitute.
From CoreErlang.Equivalence.BigStepToFrameStack Require Export Measure.

From CoreErlang Require Import Basics.
Require Import stdpp.list.

Import BigStep.

(**
* meausre_reduction [Admitted]
* meausre_reduction_list [Admitted]
* meausre_reduction_map [Admitted]
*)




(*
Theorem subst_env_empty :
  forall n e,
    subst_env n [] e = e.
Proof.
  intros.
  destruct n.
  { by cbn. }
  induction e using derived_Expression_ind.
  * 
Admitted.
*)

Theorem measure_reduction_val :
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
    induction ref as [| x env IHenv].
    - cbn.
      admit.
    - admit.
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






Theorem measure_reduction_val_list :
  forall vl v1 v2,
    list_sum (map measure_val vl) <= measure_val v1
  ->
    list_sum (map measure_val vl) <= measure_val v2
  ->
    map (bval_to_bexp (subst_env (measure_val v1))) vl
  =
    map (bval_to_bexp (subst_env (measure_val v2))) vl.
Proof.
Admitted.






Theorem measure_reduction_val_map :
  forall ml v1 v2,
    list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) ml)
      <= measure_val v1
  ->
    list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) ml)
      <= measure_val v2
  ->
    map
      (prod_map
        (bval_to_bexp (subst_env (measure_val v1)))
        (bval_to_bexp (subst_env (measure_val v1))))
      ml
  =
    map
      (prod_map
        (bval_to_bexp (subst_env (measure_val v2)))
        (bval_to_bexp (subst_env (measure_val v2))))
      ml.
Proof.
Admitted.






Theorem measure_reduction_subst_env :
  forall env e n,
    measure_env_exp env e <= n
    -> subst_env n env e = subst_env (measure_env_exp env e) env e.
Proof.
Admitted.