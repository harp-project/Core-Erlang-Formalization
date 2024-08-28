From CoreErlang.BigStep Require Export Environment.

(**
* Help
  - rem_keys
* Main
  - rem_vars
  - rem_fids
  - rem_both
  - rem_nfifes
*)

(**
NOTES:  Maybe place this in BigStep/Environment
*)



Section Help.



  Definition rem_keys
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



End Help.






Section Main.



  Definition rem_vars
    (vars : list Var)
    (env : Environment)
    : Environment
    :=
  rem_keys (map inl vars) env.



  Definition rem_fids
    (fids : list (FunctionIdentifier * FunctionExpression))
    (env : Environment)
    : Environment
    :=
  rem_keys (map inr (map fst fids)) env.



  Definition rem_both
    (fids : list (FunctionIdentifier * FunctionExpression))
    (vars : list Var)
    (env : Environment)
    : Environment
    :=
  rem_fids fids (rem_vars vars env).



  Definition rem_nfifes
    (nfifes : list (nat * FunctionIdentifier * FunctionExpression))
    (env : Environment)
    : Environment
    :=
  rem_keys (map inr (map snd (map fst nfifes))) env.



End Main.