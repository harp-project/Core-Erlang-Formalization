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







(*TEST*)
Open Scope string_scope.


Lemma erase_names_test_X1 :
  step_any
    []
    (bexp_to_fexp_subst
      (fun _ => 0)
      []
      ((ELetRec [(("fun1",0), ([], EApp (EFunId ("fun3", 0)) []));
                  (("fun2",0), ([], ELit (Integer 42))); 
                  (("fun3",0), ([], EApp (EFunId ("fun2", 0)) []))]
                (EApp (EFunId ("fun1",0)) []))))
    (bresult_to_fresult
      (fun _ => 0)
      ((inl [VLit (Integer 42)]))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 15 do_framestack_step.
Qed.



Lemma erase_names_test_X2 :
  step_any
    []
    (bexp_to_fexp_subst
      (fun _ => 0)
      []
      (ELetRec
        [(("f", 1), (["X"],
          ECase (EVar "X")
            [([PLit (Integer 0)], ELit (Atom "true"), ELit (Integer 5));
            ([PLit (Integer 1)], ELit (Atom "true"), EApp (EFunId ("f", 1)) [ELit (Integer 0)]);
            ([PVar "A"], ELit (Atom "true"), EApp (EFunId ("f", 1)) [ELit (Integer 1)])]
        ))]
        (ELet ["X"] (EFun ["F"]
             (ELetRec [(("f", 1), (["X"], ELit (Integer 0)))] 
                (EApp (EVar "F") [ELit (Integer 2)])
             ))
          (EApp (EVar "X") [EFunId ("f", 1)])
         )))
    (bresult_to_fresult
      (fun _ => 0)
      (inl [VLit (Integer 5)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 50 do_framestack_step.
Qed.