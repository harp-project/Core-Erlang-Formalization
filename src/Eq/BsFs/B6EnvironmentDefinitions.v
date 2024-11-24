From CoreErlang.Eq.BsFs Require Export B5WellFormedMapLemmas.

Import BigStep.

(* STRUCTURE:
* Remove
  - rem_keys
  - rem_vars
  - rem_fids
  - rem_exp_ext_fids
  - rem_val_ext_fids
  - rem_exp_ext_both
  - rem_val_ext_both
*)












Section Remove.



  Definition rem_keys
    (keys : list (Var + FunctionIdentifier))
    (env : Environment)
    : Environment
    :=
    filter
      (fun '(k, v) =>
        negb (existsb
          (fun x => (var_funid_eqb x k))
          keys))
      env.



  Definition rem_vars
    (vars : list Var)
    (env : Environment)
    : Environment
    :=
  rem_keys (map inl vars) env.



  Definition rem_fids
    (fids : list FunctionIdentifier)
    (env : Environment)
    : Environment
    :=
  rem_keys (map inr fids) env.



  Definition rem_exp_ext_fids
    (ext : list (FunctionIdentifier * FunctionExpression))
    (env : Environment)
    : Environment
    :=
  rem_fids (map fst ext) env.



  Definition rem_val_ext_fids
    (ext : list (nat * FunctionIdentifier * FunctionExpression))
    (env : Environment)
    : Environment
    :=
  rem_fids (map (snd ∘ fst) ext) env.



  Definition rem_exp_ext_both
    (vars : list Var)
    (ext : list (FunctionIdentifier * FunctionExpression))
    (env : Environment)
    : Environment
    :=
  rem_exp_ext_fids ext (rem_vars vars env).



  Definition rem_val_ext_both
    (vars : list Var)
    (ext : list (nat * FunctionIdentifier * FunctionExpression))
    (env : Environment)
    : Environment
    :=
  rem_val_ext_fids ext (rem_vars vars env).



End Remove.