From CoreErlang.BigStep Require Export Environment.

(**
* Help
  - env_rem
* Main
  - env_rem_vars
  - env_rem_fids
  - env_rem_fids_vars
  - env_rem_ext
*)

(**
NOTES:  Maybe place this in BigStep/Environment
*)



Section Help.



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



End Help.






Section Main.



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



End Main.