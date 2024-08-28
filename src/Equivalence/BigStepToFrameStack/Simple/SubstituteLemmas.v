From CoreErlang.Equivalence.BigStepToFrameStack.Simple Require Export Substitute.

Import BigStep.



Theorem subst_env_empty :
  forall n e,
    subst_env n [] e = e.
Proof.
  intros.
  generalize dependent n.
  induction e using derived_Expression_ind.
  * (* Values *)
    rename H into HForall.
    induction el as [| e el IHel]; intros; destruct n; cbn.
    1-3: reflexivity.
    inv HForall.
    rename H1 into He.
    rename H2 into HForall.
    specialize (IHel HForall (S n)).
    clear HForall.
    cbn.
    f_equal.
    rewrite He.
    clear He.
    cbn in IHel.
    injection IHel; intros Hel.
    clear IHel.
    rewrite Hel.
    reflexivity.
  * destruct n; by cbn.
  * destruct n; by cbn.
  * destruct n; by cbn.
  * destruct n; by cbn.
  * (* Fun *)
    destruct n; cbn.
    - reflexivity.
    - specialize (IHe n).
      rewrite IHe.
      reflexivity.
  * (* Cons *)
    destruct n; cbn.
    - reflexivity.
    - specialize (IHe1 n).
      specialize (IHe2 n).
      rewrite IHe1.
      rewrite IHe2.
      reflexivity.
  * (* Tuple *)
    rename H into HForall.
    induction l as [| e el IHel]; intros; destruct n; cbn.
    1-3: reflexivity.
    inv HForall.
    rename H1 into He.
    rename H2 into HForall.
    specialize (IHel HForall (S n)).
    clear HForall.
    cbn.
    f_equal.
    rewrite He.
    clear He.
    cbn in IHel.
    injection IHel; intros Hel.
    clear IHel.
    rewrite Hel.
    reflexivity.
  * (* Call *)
    rename H into HForall.
    induction l as [| e el IHel]; intros; destruct n; cbn.
    2: rewrite IHe1; by rewrite IHe2.
    1-2: reflexivity.
    rewrite IHe1.
    rewrite IHe2.
    inv HForall.
    rename H1 into He.
    rename H2 into HForall.
    specialize (IHel HForall (S n)).
    clear HForall.
    cbn.
    f_equal.
    rewrite He.
    clear He.
    cbn in IHel.
    injection IHel; intros Hel.
    clear IHel.
    rewrite Hel.
    reflexivity.
  * (* PrimOp *)
    rename H into HForall.
    induction l as [| e el IHel]; intros; destruct n; cbn.
    1-3: reflexivity.
    inv HForall.
    rename H1 into He.
    rename H2 into HForall.
    specialize (IHel HForall (S n)).
    clear HForall.
    cbn.
    f_equal.
    rewrite He.
    clear He.
    cbn in IHel.
    injection IHel; intros Hel.
    clear IHel.
    rewrite Hel.
    reflexivity.
  * (* App *)
    rename e into e'.
    rename H into HForall.
    induction l as [| e el IHel]; intros; destruct n; cbn.
    2: by rewrite IHe.
    1-2: reflexivity.
    inv HForall.
    rename H1 into He.
    rename H2 into HForall.
    specialize (IHel HForall (S n)).
    clear HForall.
    cbn in IHel.
    inv IHel.
    clear H0.
    rename H1 into Hel.
    rewrite IHe.
    rewrite IHe.
    rewrite He.
    rewrite Hel.
    rewrite Hel.
    reflexivity.
  * (* Case *)
    rename e into e'.
    rename H into HForall.
    induction l as [| e el IHel]; intros; destruct n; cbn.
    2: by rewrite IHe.
    1-2: reflexivity.
    inv HForall.
    destruct e as [e e2].
    destruct e as [p e1].
    destruct H1.
    cbn in *.
    rename H into He1.
    rename H0 into He2.
    rename H2 into HForall.
    specialize (IHel HForall (S n)).
    clear HForall IHe.
    cbn in IHel.
    injection IHel; intros Hel He.
    clear IHel.
    rewrite He.
    rewrite Hel.
    rewrite He1.
    rewrite He2.
    reflexivity.
  * (* Let *)
    destruct n; cbn.
    - reflexivity.
    - rewrite rem_vars_empty.
      rewrite IHe1.
      rewrite IHe2.
      reflexivity.
  * (* Seq *)
    destruct n; cbn.
    - reflexivity.
    - rewrite IHe1.
      rewrite IHe2.
      reflexivity.
  * (* LetRec *)
    rename e into e'.
    rename H into HForall.
    induction l as [| e el IHel]; intros; destruct n.
    2: cbn; by rewrite IHe.
    1-2: reflexivity.
    inv HForall.
    destruct e as [f e].
    destruct e as [l e].
    cbn in H1.
    rename H1 into He.
    rename H2 into HForall.
    specialize (IHel HForall (S n)).
    clear HForall.
    cbn in IHel.
    injection IHel; intros Hefid Hel.
    clear IHel.
    simpl.
    rewrite rem_fids_empty.
    rewrite IHe.
    rewrite rem_both_empty.
    rewrite He.
    cbn.
    (*rewrite env_rem_fids_vars_empty_map in Hel. *)
    f_equal.
    f_equal.
    rewrite <- Hel at 2.
    apply map_ext.
    intros [fid [vl b]].
    rewrite rem_vars_empty.
    cbn.
    f_equal.
    f_equal.
    f_equal.
    unfold rem_both.
    unfold rem_fids.
    unfold rem_keys.
    f_equal.
    rewrite rem_vars_empty.
    reflexivity.
  * (* Map *)
    rename H into HForall.
    induction l as [| e el IHel]; intros; destruct n; cbn.
    1-3: reflexivity.
    inv HForall.
    destruct e as [e1 e2].
    destruct H1.
    rename H into He1.
    rename H0 into He2.
    rename H2 into HForall.
    specialize (IHel HForall (S n)).
    clear HForall.
    cbn.
    f_equal.
    rewrite He1.
    rewrite He2.
    clear He1 He2.
    cbn in *.
    injection IHel; intros Hel.
    clear IHel.
    rewrite Hel.
    reflexivity.
  * (* Try *)
    destruct n; cbn.
    - reflexivity.
    - rewrite IHe1.
      rewrite IHe2.
      rewrite IHe3.
      reflexivity.
Qed.