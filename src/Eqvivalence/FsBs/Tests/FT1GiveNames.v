From CoreErlang.Eqvivalence.FsBs Require Export F1GiveNames.
From CoreErlang.Eqvivalence Require Export B1EraseNames.

Import BigStep.

Open Scope string_scope.




Import SubstSemantics.

Compute give_exp 0
  (˝VTuple [VVar 0; VVar 1; VVar 2]).
Compute give_exp 0
  (°EFun 2
    (˝VTuple [VVar 0; VVar 1; VVar 2])).
Compute give_exp 0
  (°EFun 2
    (°EFun 2
      (˝VTuple [VVar 0; VVar 1; VVar 2; VVar 3; VVar 4]))).
Compute give_exp 0
  (°ELet 2
    (˝VNil)
    (˝VTuple [VVar 0; VVar 1; VVar 2])).
Compute give_exp 0
  (°ELet 2
    (˝VNil)
    (°ELet 2
      (˝VNil)
      (˝VTuple [VVar 0; VVar 1; VVar 2; VVar 3; VVar 4]))).
Compute give_exp 0
  (°ELet 2
    (˝VNil)
    (°ELet 2
      (˝VTuple [VVar 0; VVar 1; VVar 2])
      (˝VTuple [VVar 0; VVar 1; VVar 2; VVar 3; VVar 4]))).
Compute give_exp 0
  (°ELet 2
    (˝VTuple [VVar 0; VVar 1; VVar 2])
    (°ELet 2
      (˝VTuple [VVar 0; VVar 1; VVar 2])
      (˝VTuple [VVar 0; VVar 1; VVar 2; VVar 3; VVar 4]))).

Import BigStep.









Section FullCircle.



Definition full_names
    (Γ : Environment)
    (e : Expression)
    : Expression
    :=
  give_names (erase_names Γ e).



Definition full_result
    (r : (ValueSequence + Exception))
    : (ValueSequence + Exception)
    :=
  give_redex (erase_result r).



End FullCircle.










From CoreErlang Require Export FunctionalBigStep.


Section TestSuccess.



  Lemma erase_names_test_X1A :
    eval_expr
      []
      []
      ""
      0
      (full_names
        []
        ((ELetRec [(("fun1",0), ([], EApp (EFunId ("fun3", 0)) []));
                    (("fun2",0), ([], ELit (Integer 42))); 
                    (("fun3",0), ([], EApp (EFunId ("fun2", 0)) []))]
                  (EApp (EFunId ("fun1",0)) []))))
      []
      3
      (full_result
        ((inl [VLit (Integer 42)])))
      [].
  Proof.
    cbn.
  Admitted.



  Lemma full_names_test_X1A :
    fbs_expr 1000
      []
      []
      ""
      0
      (full_names
        []
        ((ELetRec [(("fun1",0), ([], EApp (EFunId ("fun3", 0)) []));
                    (("fun2",0), ([], ELit (Integer 42))); 
                    (("fun3",0), ([], EApp (EFunId ("fun2", 0)) []))]
                  (EApp (EFunId ("fun1",0)) []))))
      []
    =
    Result
      3
      (full_result
        ((inl [VLit (Integer 42)])))
      [].
  Proof.
    cbn.
  Admitted.



  Lemma full_names_test_X6A :
    eval_expr
      []
      []
      ""
      0
      (full_names
        [(inl "X", VLit (Integer 42))]
        (ELet ["Y"] (EValues [EFun [] (EVar "X")])
          (EApp (EVar "Y") [])))
      []
      1
      (full_result
        ((inl [VLit (Integer 42)])))
      [].
  Proof.
    cbn.
  Admitted.



  Lemma full_names_test_X6B :
    fbs_expr 1000
      []
      []
      ""
      0
      (full_names
        [(inl "X", VLit (Integer 42))]
        (ELet ["Y"] (EValues [EFun [] (EVar "X")])
          (EApp (EVar "Y") [])))
      []
    =
    Result
      1
      (full_result
        ((inl [VLit (Integer 42)])))
      [].
  Proof.
    cbn.
  Admitted.



  Lemma full_names_test_X7A :
    eval_expr
      []
      []
      ""
      0
      (full_names
        []
        (ELet ["X"] (ELit (Integer 1)) 
              (ELet ["X"] (ELit (Integer 2)) 
                 (EVar "X"))))
      []
      0
      (full_result
        ((inl [VLit (Integer 2)])))
      [].
  Proof.
    cbn.
  Admitted.



  Lemma full_names_test_X7B :
    fbs_expr 1000
      []
      []
      ""
      0
      (full_names
        []
        (ELet ["X"] (ELit (Integer 1)) 
              (ELet ["X"] (ELit (Integer 2)) 
                 (EVar "X"))))
      []
    =
    Result
      0
      (full_result
        ((inl [VLit (Integer 2)])))
      [].
  Proof.
    cbn.
    auto.
  Qed.



End TestSuccess.