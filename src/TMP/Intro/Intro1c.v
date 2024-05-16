From CoreErlang.FrameStack Require SubstSemantics.
From CoreErlang.FrameStack Require Export CTX.


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


(*
  Hard task:
    Prove the following theorem about the correctness of fact!


  Use induction over n! Follow the scheme described in fact_eval_3. Check what
  theorems are available about transitive evaluation.
*)


Lemma succ_nat_minus_1_equals_nat : forall n,
  eval_arith "erlang" "-" [VLit (Z.pos (Pos.of_succ_nat n)); VLit 1%Z] = RValSeq [VLit (Z.of_nat n)]. 
Proof.
    Print eval_arith.
    intros n.
    induction n.
    * cbn. reflexivity.
    * rewrite -> SuccNat2Pos.inj_succ.
      rewrite -> Pos2Z.inj_succ.
      rewrite <- Z.add_1_l.
      admit.
Admitted.



Theorem fact_eval : forall n,
  ⟨[], fact_frameStack (˝VLit (Z.of_nat n))⟩ -->* RValSeq [VLit (Z.of_nat (Factorial.fact n))].
Proof.
    intros n.
    induction n.
    *   simpl. econstructor.
        {
            split.
            {
                constructor.
                constructor.
                scope_solver.
                constructor.
            }
            simpl. econstructor.
            {
                simpl. constructor.
                simpl. reflexivity.
            }
            simpl. econstructor.
            {
                simpl. constructor.
            }
            simpl. econstructor.
            {
                simpl. constructor.
                scope_solver.
            }
            simpl. econstructor.
            {
                simpl. constructor.
            }
            simpl. econstructor.
            {
                simpl. constructor.
                congruence.
            }
            simpl. econstructor.
            {
                simpl. constructor.
                scope_solver.
            }
            simpl. econstructor.
            {
                simpl. econstructor.
                simpl. constructor.
            }
            simpl. econstructor.
            {
                simpl. constructor.
            }
            simpl. econstructor.
            {
                simpl. constructor.
                scope_solver.
            }
            simpl. econstructor.
            {
                apply eval_step_case_match.
                simpl. constructor.
            }
            simpl. econstructor.
            {
                simpl. constructor.
                scope_solver.
            }
            simpl. econstructor.
            {
                simpl. constructor.
            }
            simpl. econstructor.
            {
                simpl. constructor.
                scope_solver.
            }
            simpl. constructor.
        }
    *   inversion IHn. inversion H.
        unfold fact_frameStack.
        unfold fact_frameStack in H1.
        simpl. econstructor.
        {
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
            rewrite -> succ_nat_minus_1_equals_nat.
            inv H1.
            inv H2.
            simpl in H3.
            inv H3.
            inv H1.
            simpl in H2.
            inv H2.
            inv H1.
            simpl in H3.
            inv H3.
            inv H1.
            simpl in H2.
            inv H2.
            inv H1.
            simpl in H3.
            inv H3.
            inv H1.
            simpl in H2.
            eapply frame_indep_core in H2.
            {
                eapply transitive_eval.
                {
                    (* apply H2. *)
                    admit.
                }
                admit.
                (*
                {
                    simpl. econstructor.
                    {
                        simpl. constructor.
                    }
                }
                *)
            }
        }
Admitted.

(*

⟨ [FParams (IApp (VClos [(0, 1, ° ECase (˝ VVar 1) [([PLit 0%Z], ˝ VLit "true", ˝ VLit 1%Z); ([PVar], ˝ VLit "true", ° ELet 1 (° EApp (˝ VFunId (1, 1)) [° ECall (˝ VLit "erlang") (˝ VLit "-") [˝ VVar 0; ˝ VLit 1%Z]]) (° ECall (˝ VLit "erlang") (˝ VLit "*") [˝ VVar 1; ˝ VVar 0]))])] 0 1 (° ECase (˝ VVar 1) [([PLit 0%Z], ˝ VLit "true", ˝ VLit 1%Z); ([PVar], ˝ VLit "true", ° ELet 1 (° EApp (˝ VFunId (1, 1)) [° ECall (˝ VLit "erlang") (˝ VLit "-") [˝ VVar 0; ˝ VLit 1%Z]]) (° ECall (˝ VLit "erlang") (˝ VLit "*") [˝ VVar 1; ˝ VVar 0]))]))) [] []], [VLit (Z.of_nat n)] ⟩ 
    -[ k0 ]-> 
⟨ [], [VLit (Z.of_nat (Factorial.fact n))] ⟩


⟨ [FParams (IApp (VClos [(0, 1, ° ECase (˝ VVar 1) [([PLit 0%Z], ˝ VLit "true", ˝ VLit 1%Z); ([PVar], ˝ VLit "true", ° ELet 1 (° EApp (˝ VFunId (1, 1)) [° ECall (˝ VLit "erlang") (˝ VLit "-") [˝ VVar 0; ˝ VLit 1%Z]]) (° ECall (˝ VLit "erlang") (˝ VLit "*") [˝ VVar 1; ˝ VVar 0]))])] 0 1 (° ECase (˝ VVar 1) [([PLit 0%Z], ˝ VLit "true", ˝ VLit 1%Z); ([PVar], ˝ VLit "true", ° ELet 1 (° EApp (˝ VFunId (1, 1)) [° ECall (˝ VLit "erlang") (˝ VLit "-") [˝ VVar 0; ˝ VLit 1%Z]]) (° ECall (˝ VLit "erlang") (˝ VLit "*") [˝ VVar 1; ˝ VVar 0]))]))) [] []; FLet 1 (° ECall (˝ VLit "erlang") (˝ VLit "*") [˝ VLit (Z.pos (Pos.of_succ_nat n)); ˝ VVar 0])], eval_arith "erlang" "-" [VLit (Z.pos (Pos.of_succ_nat n)); VLit 1%Z] ⟩ 
    -[ ?k ]-> 
⟨ [], [VLit (Z.of_nat (Factorial.fact n + n * Factorial.fact n))] ⟩

*)

End FrameStack.