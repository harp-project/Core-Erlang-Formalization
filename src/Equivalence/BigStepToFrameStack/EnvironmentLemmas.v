From CoreErlang.BigStep Require Export Environment.

From CoreErlang Require Import Basics.
Require Import stdpp.list.

(**
* Help
  - Remove
    + env_rem
  - Get
    + get_value_cons
* Main
  - Remove
    + env_rem_vars
    + env_rem_fids
    + env_rem_fids_vars
    + env_rem_ext
  - Get
    + can_get_value_than_in
*)

(**
NOTES:  Maybe place this in BigStep/Environment
*)



Section Help.



  Section Remove.

    Definition env_rem
      (keys : list (Var + FunctionIdentifier))
      (env : Environment)
      : Environment
      :=
    fold_left
      (fun env' key =>
        filter (fun '(k, v) =>
          negb (var_funid_eqb k key))
          env')
      keys
      env.

  End Remove.



  Section Get.

    Theorem get_value_cons :
      forall env key k var v,
          get_value ((k, v) :: env) key = Some [var]
      ->  get_value [(k, v)] key = Some [var] 
      \/
          get_value env key = Some [var].
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



End Help.






Section Main.



  Section Remove.

    Definition env_rem_vars
      (vars : list Var)
      (env : Environment)
      : Environment
      :=
    env_rem (map inl vars) env.



    Definition env_rem_fids
      (fids : list (FunctionIdentifier * FunctionExpression))
      (env : Environment)
      : Environment
      :=
    env_rem (map inr (map fst fids)) env.



    Definition env_rem_fids_vars
      (fids : list (FunctionIdentifier * FunctionExpression))
      (vars : list Var)
      (env : Environment)
      : Environment
      :=
    env_rem_fids fids (env_rem_vars vars env).



    Definition env_rem_ext
      (ext : list (nat * FunctionIdentifier * FunctionExpression))
      (env : Environment)
      : Environment
      :=
    env_rem (map inr (map snd (map fst ext))) env.

  End Remove.



  Section Get.

    Theorem can_get_value_than_in :
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
            as _key_eqb.
          symmetry in Heq_key_eqb.
          destruct _key_eqb.
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

  End Get.



End Main.