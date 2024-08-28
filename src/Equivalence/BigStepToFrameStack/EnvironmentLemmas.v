From CoreErlang.Equivalence.BigStepToFrameStack Require Export EnvironmentDefinitions.
From CoreErlang.Equivalence Require Export Basics.

(**
* Help
  - Get
    + get_value_cons
  - Remove
    + rem_keys_empty
* Main
  - Get
    + can_get_value_than_in
    + get_value_singelton
    + get_value_singelton_length
  - Remove
    + rem_vars_empty
    + rem_fids_empty
    + rem_both_empty
    + rem_nfifes_empty
    + rem_both_empty_map [NotUsing]
*)

(**
NOTES:  Maybe place this in BigStep/Environment
*)



Section Help.



  Section Get.

    Lemma get_value_cons :
      forall env key k var v,
          get_value ((k, v) :: env) key = Some [var]
      ->  get_value [(k, v)] key = Some [var] 
      \/  get_value env key = Some [var].
    Proof.
      intros env key k var v Hcons.
      unfold get_value in Hcons.
      remember
        (var_funid_eqb key k)
        as _key_eqb.
      symmetry in Heq_key_eqb.
      destruct _key_eqb.
      * left.
        clear env.
        inv Hcons.
        unfold var_funid_eqb in Heq_key_eqb.
        destruct key.
        - destruct k.
          + cbn.
            rewrite Heq_key_eqb.
            reflexivity.
          + congruence.
        - destruct k.
          + congruence.
          + cbn.
            rewrite Heq_key_eqb.
            reflexivity.
      * right.
        exact Hcons.
    Qed.

  End Get.



  Section Remove.

    Lemma rem_keys_empty :
      forall keys,
        rem_keys keys [] = [].
    Proof.
      intros.
      unfold rem_keys.
      induction keys.
      * by cbn.
      * cbn.
        by rewrite IHkeys.
    Qed.

  End Remove.



End Help.






Section Main.



  Section Get.

    Theorem get_value_in :
      forall env key var,
          get_value env key = Some [var]
      ->  In (key , var) env.
    Proof.
      intros env.
      induction env; intros key var Hget_value.
      * inv Hget_value.
      * destruct a as [k v].
        apply get_value_cons in Hget_value.
        destruct Hget_value.
        - clear IHenv.
          rename H into Hget_value.
          unfold get_value in Hget_value.
          remember
            (var_funid_eqb key k)
            as key_eqb
            eqn:Heq_key_eqb.
          symmetry in Heq_key_eqb.
          destruct key_eqb.
          + inv Hget_value.
            apply var_funid_eqb_eq in Heq_key_eqb.
            rewrite <- Heq_key_eqb.
            clear Heq_key_eqb k.
            constructor.
            clear env.
            reflexivity.
          + clear Heq_key_eqb.
            congruence.
        - rename H into Hget_value.
          specialize (IHenv key var Hget_value).
          pose proof in_cons (k, v) (key, var) env IHenv.
          clear IHenv Hget_value.
          assumption.
    Qed.

    Lemma get_value_singelton :
      forall env key vs,
          get_value env key = Some vs
      ->  exists value, vs = [value].
    Proof.
       intros env key vs.
       induction env as [| [k v] env IHenv]; intros Hget; cbn in Hget.
       * congruence.
       * destruct (var_funid_eqb key k) eqn:Heqb.
         - exists v.
           by inv Hget.
         - by apply IHenv.
    Qed.

    Lemma get_value_singelton_length :
      forall env key l,
          get_value env key = Some l
      ->  length l = 1.
    Proof.
       intros env key vs Hget.
       pose proof get_value_singelton env key vs Hget as Hsingelton.
       by inv Hsingelton.
    Qed.

  End Get.



  Section Remove.

    Lemma rem_vars_empty :
      forall vars,
        rem_vars vars [] = [].
    Proof.
      intros.
      unfold rem_vars.
      by rewrite rem_keys_empty.
    Qed.

    Lemma rem_fids_empty :
      forall fids,
        rem_fids fids [] = [].
    Proof.
      intros.
      unfold rem_fids.
      by rewrite rem_keys_empty.
    Qed.

    Lemma rem_both_empty :
      forall fids vars,
        rem_both fids vars [] = [].
    Proof.
      intros.
      unfold rem_both.
      rewrite rem_vars_empty.
      rewrite rem_fids_empty.
      reflexivity.
    Qed.

    Lemma rem_nfifes_empty :
      forall ext,
        rem_nfifes ext [] = [].
    Proof.
      intros.
      unfold rem_nfifes.
      by rewrite rem_keys_empty.
    Qed.

    Lemma rem_both_empty_map :
      forall (f : Environment -> Expression -> Expression) el,
        map
          (fun  '(fid, (vl, b)) =>
            (fid, (vl, f (rem_both el vl []) b)))
          el
      = map
          (fun '(fid, (vl, b)) =>
            (fid, (vl, f [] b)))
          el.
    Proof.
      intros.
      apply map_ext.
      intros [fid [vl b]].
      by rewrite rem_both_empty.
    Qed.

  End Remove.



End Main.