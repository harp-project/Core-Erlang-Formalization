From CoreErlang.FrameStack Require SubstSemantics.


Open Scope string_scope.


Module FrameStack.


Import FrameStack.SubstSemantics.


Import ListNotations.


(*
  Let "e" be a parameter expression.


  letrec 'fact'/1 =
    fun(X) ->
      case <X> of
        <0> -> 1
        <Z> -> let <Y> = <apply 'fact'/1(call 'erlang':'-'(Z, 1))>
                 in call 'erlang':'*'(Z,Y)
    in
      apply 'fact'/1(e)


  Define the above expression!
 *)


Definition fact_frameStack (e : Exp) : Exp :=
  ELetRec
    [
      (1, °ECase (˝VVar 1)
        [
          ([PLit 0%Z], ˝VLit "true", 
            ˝VLit 1%Z);
          ([PVar], ˝VLit "true", 
            (°ELet 1 (EApp (˝VFunId (1, 1)) [(°ECall (˝VLit "erlang") (˝VLit "-")  [˝VVar 0; ˝VLit 1%Z])])
              (°ECall (˝VLit "erlang") (˝VLit "*")  [˝VVar 1; ˝VVar 0])))
        ])
    ]
  (EApp (˝VFunId (0, 1)) [e])
.


End FrameStack.