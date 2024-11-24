From CoreErlang.Eq.BsFs Require Export B16EraseNamesDefinitions.

Import BigStep.

(* STRUCTURE:
* Convert
  - bexp_to_fexp_subst
  - bvs_to_fvs
  - bec_to_fec
  - bexc_to_fexc
  - bresult_to_fresult
*)












Section Convert.



  Definition bexp_to_fexp_subst
    fns
    (env : Environment)
    (e : Expression)
    : Exp
    :=
  bexp_to_fexp
    fns
    (subst_env
      (measure_env_exp env e)
      env
      e).



  Definition bvs_to_fvs
    fns
    (vs : ValueSequence)
    : ValSeq
    :=
  map
    (bval_to_fval fns)
    vs.



  Definition bec_to_fec
    (ec : ExceptionClass)
    : ExcClass
    :=
  match ec with
  | Error =>  CoreErlang.Syntax.Error
  | Throw =>  CoreErlang.Syntax.Throw
  | Exit =>   CoreErlang.Syntax.Exit
  end.



  Definition bexc_to_fexc
    fns
    (exc : Exception)
    : CoreErlang.Syntax.Exception
    :=
  match exc with
  | (ec, v1, v2) =>
      (bec_to_fec ec,
      bval_to_fval fns v1,
      bval_to_fval fns v2)
  end.



  Definition bresult_to_fresult
    fns
    (result : (ValueSequence + Exception))
    : Redex
    :=
  match result with
  | inl vs =>   RValSeq (bvs_to_fvs fns vs)
  | inr exc =>  RExc (bexc_to_fexc fns exc)
  end.



End Convert.