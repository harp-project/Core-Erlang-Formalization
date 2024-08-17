From CoreErlang.Equivalence.BigStepToFrameStack.Simple Require Export Substitute.
From CoreErlang.Equivalence.BigStepToFrameStack Require Export Measure.

Require Import stdpp.list.

(**
* meausre_reduction [Admitted]
* meausre_reduction_list [Admitted]
* meausre_reduction_map [Admitted]
*)



Theorem measure_reduction :
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
  induction v.
  * by cbn.
  * by cbn.
  * admit.
  * cbn.
    assert
      (measure_val v1 ≤
        measure_val (BigStep.Syntax.VCons v1 v2))
      as Hv1.
    {
      cbn.
      lia.
    }
    assert
      (measure_val v2 ≤
        measure_val (BigStep.Syntax.VCons v1 v2))
      as Hv2.
    {
      cbn.
      lia.
    }
    assert (measure_val v1 ≤ n1) as Hv1n1.
    {
      apply Nat.le_trans
        with (m := measure_val (BigStep.Syntax.VCons v1 v2)).
      - exact Hv1.
      - exact Hn1.
    }
    assert (measure_val v1 ≤ n2) as Hv1n2.
    {
      apply Nat.le_trans
        with (m := measure_val (BigStep.Syntax.VCons v1 v2)).
      - exact Hv1.
      - exact Hn2.
    }
    assert (measure_val v2 ≤ n1) as Hv2n1.
    {
      apply Nat.le_trans
        with (m := measure_val (BigStep.Syntax.VCons v1 v2)).
      - exact Hv2.
      - exact Hn1.
    }
    assert (measure_val v2 ≤ n2) as Hv2n2.
    {
      apply Nat.le_trans
        with (m := measure_val (BigStep.Syntax.VCons v1 v2)).
      - exact Hv2.
      - exact Hn2.
    }
    specialize (IHv1 Hv1n1 Hv1n2).
    specialize (IHv2 Hv2n1 Hv2n2).
    rewrite IHv1.
    rewrite IHv2.
    reflexivity.
  * admit.
  * admit.
Admitted.






Theorem measure_reduction_list :
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






Theorem measure_reduction_map :
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