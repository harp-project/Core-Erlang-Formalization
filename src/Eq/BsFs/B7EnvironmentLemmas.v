From CoreErlang.Eq.BsFs Require Export B6EnvironmentDefinitions.

Import BigStep.

(* STRUCTURE:
* Remove
  - rem_keys_cons_env
* GetValue
  - get_value_singleton
  - get_value_singleton_length
  - get_value_cons
  - get_value_in
*)












Section Remove.



  Lemma rem_keys_cons_env :
    forall keys k v env env',
        env' = rem_keys keys ((k, v) :: env)
    ->  env' = rem_keys keys env
    \/  env' = (k, v) :: rem_keys keys env.
  Proof.
    (* #1 Simplify: intro/simple *)
    itr - keys k v env env' Hcons.
    smp *.
    (* #2 Destruct Exists: destruct/right/left *)
    des >
      (negb
        (existsb (λ x : Var + FunctionIdentifier, var_funid_eqb x k) keys)).
    * by rgt.
    * by lft.
  Qed.



End Remove.









Section GetValue.



  Theorem get_value_singleton :
    forall env key vs,
        get_value env key = Some vs
    ->  exists value, vs = [value].
  Proof.
    (* #1 Induction on Environment: intro/induction + intro/simpl/congruence*)
    itr - env key vs.
    ind - env as [| [k v] env IHenv] :> itr - Hget; smp - Hget :- con.
    (* #2 Destruct Key Equality: destruct + apply *)
    des > (var_funid_eqb key k) as Hkey :- app - IHenv.
    (* #3 Exists Value: exists/inversion *)
    exi - v.
    bvs - Hget.
  Qed.



  Theorem get_value_singleton_length :
    forall env key l,
        get_value env key = Some l
    ->  length l = 1.
  Proof.
    (* #1 Pose by Previous: intro/pose/inversion *)
    itr - env key vs Hget.
    pse - get_value_singleton as Hsingl: env key vs Hget.
    bvs - Hsingl.
  Qed.



  Theorem get_value_cons :
    forall env key k var v,
        get_value ((k, v) :: env) key = Some [var]
    ->  get_value [(k, v)] key = Some [var] 
    \/  get_value env key = Some [var].
  Proof.
    (* #1 Destruct Key Equality: intro/simpl/destruct/auto *)
    itr - env key k var v Hcons.
    smp *.
    des > (var_funid_eqb key k) as Heqb_key; ato.
  Qed.



  Theorem get_value_in :
    forall env key var,
        get_value env key = Some [var]
    ->  In (key , var) env.
  Proof.
    (* #1 Induction on Environment: intro/induction + intro/inversion *)
    itr - env.
    ind - env as [| [k v] env IHenv] :> itr - key var Hget :- ivc - Hget.
    (* #2 Destruct Get_Value: apply/destruct *)
    app - get_value_cons in Hget.
    des - Hget as [Hget | Hget].
    * (* #3.1 Destruct Key Equality: clear/simpl/destruct + congruence *)
      clr - IHenv.
      smp *.
      des > (var_funid_eqb key k) as Hkey :- con.
      (* #4.1 Rewrite Var & FunId: left/inversion/apply/rewrite *)
      lft.
      ivc - Hget.
      app - var_funid_eqb_eq in Hkey.
      bwr - Hkey.
    * (* #3.2 Pose In_Cons: specialize/pose *)
      spc - IHenv: key var Hget.
      by pose proof in_cons (k, v) (key, var) env IHenv.
  Qed.



End GetValue.