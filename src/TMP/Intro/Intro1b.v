From CoreErlang.FrameStack Require SubstSemantics.


Open Scope string_scope.


Module FrameStack.


Import FrameStack.SubstSemantics.


Import ListNotations.


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


(* Hint: to solve statements about scopes (e.g., VALCLOSED), use "scope_solver"!
   Also using "(e)constructor" could help you determine which rule of the semantics
   can be used. Beware, not all semantic rules are syntax-driven, there are rules
   about ECase expressions that can applied to the same configuration.


   Since you prove the evaluation of a factorial function, thus expect repetition
   of proof steps in the script you write. This proof should not be short (>120 LOC),
   if you write out each step.


   Tactics you should use: apply, (e)constructor, simpl, relfexivity, auto, congruence
 *)


(*

⟨ [FApp1 [˝ VLit 3%Z]], [VClos [(0, 1, ° ECase (˝ VVar 1) [([PLit 0%Z], ˝ VLit "true", ˝ VLit 1%Z); ([PVar], ˝ VLit "true", ° ELet 1 (° EApp (˝ VFunId (1, 1)) [° ECall (˝ VLit "erlang") (˝ VLit "-") [˝ VVar 0; ˝ VLit 1%Z]]) (° ECall (˝ VLit "erlang") (˝ VLit "*") [˝ VVar 1; ˝ VVar 0]))])] 0 1 (° ECase (˝ VVar 1) [([PLit 0%Z], ˝ VLit "true", ˝ VLit 1%Z); ([PVar], ˝ VLit "true", ° ELet 1 (° EApp (˝ VFunId (1, 1)) [° ECall (˝ VLit "erlang") (˝ VLit "-") [˝ VVar 0; ˝ VLit 1%Z]]) (° ECall (˝ VLit "erlang") (˝ VLit "*") [˝ VVar 1; ˝ VVar 0]))])] ⟩

*)


(* Prove the following theorem *)
Theorem fact_eval_3 :
  ⟨[], fact_frameStack (˝VLit 3%Z)⟩ -->* RValSeq [VLit 6%Z].
Proof.
  eexists.
  split.
  (* VALCLOSED *)
  {
    constructor.
    constructor.
    {
      scope_solver.
    }
    constructor.
  }
  (* ELetRec *)
  simpl. econstructor.
  {
    simpl. constructor.
    simpl. constructor.
  }
  (* EApp *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FApp1 *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* <> *)
  simpl. econstructor.
  {
    simpl. constructor.
    congruence.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FParams *)
  simpl. econstructor.
  {
    simpl. econstructor.
    simpl. constructor.
  }
  (* ------------------------ #1 Recurzion ------------------------ *)
  (* ECase *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver. 
  }
  (* FCase1 *)
  simpl. econstructor.
  {
    apply eval_step_case_not_match.
    simpl. reflexivity.
  }
  (* FCase1 *)
  simpl. econstructor.
  {
    apply eval_step_case_match.
    simpl. reflexivity.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FCase2 *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* FLet *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* FLet *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FApp1 *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* <> *)
  simpl. econstructor.
  {
    simpl. constructor.
    congruence.
  }
  (* FParams *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FCallMod *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FCallFun *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* <> *)
  simpl. econstructor.
  {
    simpl. constructor.
    congruence.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FParams *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FParams *)
  simpl. econstructor.
  {
    simpl. econstructor.
    simpl. constructor.
  }
  (* FParams *)
  simpl. econstructor.
  {
    simpl. econstructor.
    simpl. constructor.
  }
  (* FLet *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* ------------------------ #2 Recurzion ------------------------ *)
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FCase1 *)
  simpl. econstructor.
  {
    apply eval_step_case_not_match.
    simpl. reflexivity.
  }
  (* FCase1 *)
  simpl. econstructor.
  {
    apply eval_step_case_match.
    simpl. reflexivity.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FCase2 *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* FLet *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* FLet *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FApp1 *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* <> *)
  simpl. econstructor.
  {
    simpl. constructor.
    congruence.
  }
  (* FParams *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FCallMod *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FCallFun *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* <> *)
  simpl. econstructor.
  {
    simpl. constructor.
    congruence.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FParams *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FParams *)
  simpl. econstructor.
  {
    simpl. econstructor.
    simpl. constructor.
  }
  (* FParams *)
  simpl. econstructor.
  {
    simpl. econstructor.
    simpl. constructor.
  }
  (* FLet *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* ------------------------ #3 Recurzion ------------------------ *)
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FCase1 *)
  simpl. econstructor.
  {
    apply eval_step_case_not_match.
    simpl. reflexivity.
  }
  (* FCase1 *)
  simpl. econstructor.
  {
    apply eval_step_case_match.
    simpl. reflexivity.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FCase2 *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* FLet *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* FLet *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FApp1 *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* <> *)
  simpl. econstructor.
  {
    simpl. constructor.
    congruence.
  }
  (* FParams *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FCallMod *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FCallFun *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* <> *)
  simpl. econstructor.
  {
    simpl. constructor.
    congruence.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FParams *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FParams *)
  simpl. econstructor.
  {
    simpl. econstructor.
    simpl. constructor.
  }
  (* FParams *)
  simpl. econstructor.
  {
    simpl. econstructor.
    simpl. constructor.
  }
  (* FLet *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* ------------------------ #4 Recurzion ------------------------ *)
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FCase1 *)
  simpl. econstructor.
  {
    apply eval_step_case_match.
    simpl. reflexivity.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FCase2 *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FLet *)
  simpl. econstructor.
  {
    simpl. constructor.
    simpl. reflexivity.
  }
  (* FLet *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FCallMod *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FCallFun *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* <> *)
  simpl. econstructor.
  {
    simpl. constructor.
    congruence.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FParams *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FParams *)
  simpl. econstructor.
  {
    simpl. econstructor.
    simpl. constructor.
  }
  (* FParams *)
  simpl. econstructor.
  {
    simpl. constructor.
    simpl. reflexivity.
  }
  (* FLet *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FCallMod *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FCallFun *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* <> *)
  simpl. econstructor.
  {
    simpl. constructor.
    congruence.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FParams *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FParams *)
  simpl. econstructor.
  {
    simpl. econstructor.
    simpl. reflexivity.
  }
  (* FParams *)
  simpl. econstructor.
  {
    simpl. econstructor.
    simpl. reflexivity.
  }
  (* FLet *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FCallMod *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FCallFun *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* <> *)
  simpl. econstructor.
  {
    simpl. constructor.
    congruence.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FParams *)
  simpl. econstructor.
  {
    simpl. constructor.
  }
  (* VALCLOSED *)
  simpl. econstructor.
  {
    simpl. constructor.
    scope_solver.
  }
  (* FParams *)
  simpl. econstructor.
  {
    simpl. econstructor.
    simpl. reflexivity.
  }
  simpl. constructor.
Qed.


End FrameStack.