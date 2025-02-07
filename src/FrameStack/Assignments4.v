(* From CoreErlang.BigStep Require Import FunctionalBigStep. *)
From CoreErlang.FrameStack Require SubstSemantics SubstSemanticsLemmas.

Open Scope string_scope.

Module FrameStack.

Import FrameStack.SubstSemantics.

Import ListNotations.
(*
  Let "e" be a parameter expression.

  letrec 'fact'/1 =
    fun(X) ->
      case X of
        <0> -> 1
        <Z> -> let <Y> = apply 'fact'/1(call 'erlang':'-'(Z, 1))
                 in call 'erlang':'*'(Z,Y);
    in
      apply 'fact'/1(e)

  Define the above expression!
 *)

Definition fact_frameStack (e : Exp) : Exp :=
  ELetRec
    [(1, °ECase (˝VVar 1) [
      ([PLit 0%Z], ˝ttrue, (˝VLit 1%Z));
      ([PVar], ˝ttrue,
        °ELet 1 (EApp (˝VFunId (1, 1))
          [°ECall (˝VLit "erlang") (˝VLit "-") [˝VVar 0; ˝VLit 1%Z]])
          (°ECall (˝VLit "erlang") (˝VLit "*") [˝VVar 1; ˝VVar 0])
      )
    ])]
    (EApp (˝VFunId (0, 1)) [e])
   (* Write the definition here *)
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
(* Prove the following theorem *)
Theorem fact_eval_3 :
  ⟨[], fact_frameStack (˝VLit 3%Z)⟩ -->* RValSeq [VLit 6%Z].
Proof.
  unfold step_any. eexists. split.
  apply valseq_is_result. apply Forall_cons.
  scope_solver.
  apply Forall_nil.

  econstructor. apply eval_heat_letrec. auto. simpl.
  econstructor. apply eval_heat_app.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_heat_app2.
  econstructor. apply eval_step_params_0. discriminate.
  econstructor. apply cool_value. scope_solver.
  econstructor. eapply eval_cool_params. reflexivity. simpl.
  econstructor. apply eval_heat_case.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_step_case_not_match. reflexivity.
  econstructor. apply eval_step_case_match. reflexivity. simpl. (* Ask about it *)
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_step_case_true. 
  econstructor. apply eval_heat_let.
  econstructor. apply eval_heat_app.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_heat_app2.
  econstructor. apply eval_step_params_0. discriminate.
  econstructor. apply eval_heat_call_mod.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_heat_call_fun.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_heat_call_params.
  econstructor. apply eval_step_params_0. discriminate.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_step_params. simpl.
  econstructor. apply cool_value. scope_solver.
  econstructor. eapply eval_cool_params. reflexivity. simpl.
  econstructor. eapply eval_cool_params. reflexivity. simpl.
  
  econstructor. apply eval_heat_case.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_step_case_not_match. reflexivity.
  econstructor. apply eval_step_case_match. reflexivity. simpl. (* Ask about it *)
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_step_case_true. 
  econstructor. apply eval_heat_let.
  econstructor. apply eval_heat_app.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_heat_app2.
  econstructor. apply eval_step_params_0. discriminate.
  econstructor. apply eval_heat_call_mod.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_heat_call_fun.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_heat_call_params.
  econstructor. apply eval_step_params_0. discriminate.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_step_params. simpl.
  econstructor. apply cool_value. scope_solver.
  econstructor. eapply eval_cool_params. reflexivity. simpl.
  econstructor. eapply eval_cool_params. reflexivity. simpl.

  econstructor. apply eval_heat_case.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_step_case_not_match. reflexivity.
  econstructor. apply eval_step_case_match. cbv. reflexivity. simpl. (* Ask about it *)
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_step_case_true. 
  econstructor. apply eval_heat_let.
  econstructor. apply eval_heat_app.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_heat_app2.
  econstructor. apply eval_step_params_0. discriminate.
  econstructor. apply eval_heat_call_mod.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_heat_call_fun.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_heat_call_params.
  econstructor. apply eval_step_params_0. discriminate.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_step_params. simpl.
  econstructor. apply cool_value. scope_solver.
  econstructor. eapply eval_cool_params. reflexivity. simpl.
  econstructor. eapply eval_cool_params. reflexivity. simpl.

  econstructor. apply eval_heat_case.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_step_case_match. reflexivity. simpl.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_step_case_true.
  econstructor. apply cool_value. scope_solver.

  econstructor. apply eval_cool_let. auto. simpl. (* Ask about it *)
  econstructor. apply eval_heat_call_mod. simpl.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_heat_call_fun.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_heat_call_params.
  econstructor. apply eval_step_params_0. discriminate.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_step_params. simpl.
  econstructor. apply cool_value. scope_solver.
  econstructor. eapply eval_cool_params. reflexivity. simpl.

  econstructor. apply eval_cool_let. auto. simpl.
  econstructor. apply eval_heat_call_mod. simpl.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_heat_call_fun.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_heat_call_params.
  econstructor. apply eval_step_params_0. discriminate.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_step_params. simpl.
  econstructor. apply cool_value. scope_solver.
  econstructor. eapply eval_cool_params. reflexivity. simpl.

  econstructor. apply eval_cool_let. auto. simpl.
  econstructor. apply eval_heat_call_mod. simpl.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_heat_call_fun.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_heat_call_params.
  econstructor. apply eval_step_params_0. discriminate.
  econstructor. apply cool_value. scope_solver.
  econstructor. apply eval_step_params. simpl.
  econstructor. apply cool_value. scope_solver.
  econstructor. eapply eval_cool_params. reflexivity. simpl.
  econstructor. (* Ask about it *)
Qed.

(* Define the following function in Core Erlang! To compile a Core Erlang file
   use the "from_core" option of the standard compiler/interpreter.
   For examples, we refer to the language specification:
   https://www.it.uu.se/research/group/hipe/cerl/doc/core_erlang-1.0.3.pdf
   You can also check example codes in the Erl_codes folder.
   Instead of the letrec expression, define it as a top level function *)
Definition collatz (e : Exp) : Exp :=
  ELetRec [
    (1, °ECase (˝VVar 1)
     [
       ([PLit 1%Z], ˝ttrue, ˝VNil);
       ([PVar], 
          °ECall (˝erlang) (˝VLit "and") [
            °ECall (˝erlang) (˝VLit "<") [˝VLit 0%Z; ˝VVar 0];
            °ECall (˝erlang) (˝VLit "=") [
              ˝VLit 0%Z; 
              °ECall (˝erlang) (˝VLit "rem") [˝VVar 0; ˝VLit 2%Z]
            ]
          ],
         °ECons (˝VVar 0) (EApp (˝VFunId (1,1)) [
           °ECall (˝erlang) (˝VLit "div") [˝VVar 0; ˝VLit 2%Z]
         ])
       );
       ([PVar], °ECall (˝erlang) (˝VLit "<") [˝VLit 0%Z; ˝VVar 0],
         °ECons (˝VVar 0) (EApp (˝VFunId (1,1)) [
           °ECall (˝erlang) (˝VLit "+")
             [°ECall (˝erlang) (˝VLit "*") [˝VLit 3%Z; ˝VVar 0];
              ˝VLit 1%Z]
         ])
       )
     ])
  ]
  (EApp (˝VFunId (0, 1)) [e]).

(*
  module 'exercise' ['fun_func'/1,
                    'module_info'/0,
                    'module_info'/1]
    attributes []
  'collatz'/1 =
    (fun (_0) ->
      (case <_0> of
        <1> when 'true' -> []
        <X> when
          call 'erlang':'and'(
            call 'erlang':'<'(0, _0),
            call 'erlang':'=='(0, call 'erlang':'rem'(_0, 2))
          ) ->
          [X|apply 'collatz'/1(call 'erlang':'div'(X,2))]
		    <X> when
	      	call 'erlang':'<'(0, _0) ->
          [X|apply 'collatz'/1(call 'erlang':'+'
			      (call 'erlang':'*'(3, X), 1))]
        end
        -| [{'function',{'fun_func',1}}] )
      -| [{'function',{'fun_func',1}}] )

%% Needed by erlc

  'module_info'/0 =
    ( fun () ->
      call 'erlang':'get_module_info'
        ('exercise')
      -| [{'function',{'module_info',0}}] )
  'module_info'/1 =
    ( fun (_0) ->
      call 'erlang':'get_module_info'
        ('exercise', ( _0
          -| [{'function',{'module_info',1}}] ))
      -| [{'function',{'module_info',1}}] )
end
*)

(* Erlang def

  collatz(1) -> [];
  collatz(X) when ((0 == (X rem 2)) band (0 < X)) ->
    [X | collatz(X div 2)];
  collatz(X) when 0 < X ->
    [X | collatz(3 * X + 1)].

*)


(*
  Hard task:
    Prove the following theorem about the correctness of fact!

  Use induction over n! Follow the scheme described in fact_eval_3. Check what
  theorems are available about transitive evaluation.
*)

Ltac do_step := econstructor; [constructor;auto|simpl].

Theorem fact_eval : forall n,
  ⟨[], fact_frameStack (˝VLit (Z.of_nat n))⟩ -->* RValSeq [VLit (Z.of_nat (Factorial.fact n))].
Proof.
  induction n; intros.
  - unfold step_any. eexists. split.
    + apply valseq_is_result. apply Forall_cons.
      scope_solver.
      apply Forall_nil.
    + do 3 do_step. scope_solver.
      do 2 do_step. discriminate.
      do 1 do_step. scope_solver.
      econstructor. eapply eval_cool_params. reflexivity. simpl.
      do 2 do_step. scope_solver.
      econstructor. apply eval_step_case_match. reflexivity. simpl.
      econstructor. apply cool_value. scope_solver.
      econstructor. apply eval_step_case_true.
      econstructor. apply cool_value. scope_solver.
      econstructor.

  - unfold step_any. 
      inv IHn. inv H. unfold fact_frameStack in H1.
      inv H1. inv H. simpl in H2. inv H2. inv H. inv H1. inv H.
      inv H2. inv H. inv H1. inv H. clear H10 H4 H0. inv H2. inv H.
      inv H0. inv H. simpl in H8. inv H8. cbn in H1.

      eexists. split.

    + apply valseq_is_result. apply Forall_cons.
      scope_solver.
      apply Forall_nil.
    + do 3 do_step. scope_solver.
      do 2 do_step. discriminate.
      econstructor. apply cool_value. scope_solver.
      econstructor. eapply eval_cool_params. reflexivity. simpl.

      do 2 do_step. scope_solver.
      econstructor. apply eval_step_case_not_match. reflexivity.
      econstructor. apply eval_step_case_match. reflexivity. simpl. (* Ask about it *)
      econstructor. apply cool_value. scope_solver.
      do 4 do_step. scope_solver.
      do 2 do_step. discriminate.
      do 2 do_step. scope_solver.
      do 2 do_step. scope_solver.
      do 2 do_step. discriminate.
      econstructor. apply cool_value. scope_solver.
      do 2 do_step. scope_solver.
      econstructor. eapply eval_cool_params. reflexivity.
      Search Pos.of_succ_nat Z.of_nat. rewrite Znat.Zpos_P_of_succ_nat. simpl.
      econstructor. eapply eval_cool_params. reflexivity. simpl.

      replace (Z.succ (Z.of_nat n) - 1)%Z with (Z.of_nat n)%Z by lia.
      eapply FrameStack.SubstSemanticsLemmas.transitive_eval.

      ++ eapply (FrameStack.SubstSemanticsLemmas.frame_indep_nil _ _ _ _ H1).

      ++ clear H1 H3. do 7 do_step. congruence.
         do 3 do_step. econstructor. econstructor. econstructor. simpl.
         unfold eval_arith. simpl.
         rewrite Znat.Nat2Z.inj_add. rewrite Z.add_comm.
         rewrite <- Znat.Nat2Z.inj_succ.
         rewrite Znat.Nat2Z.inj_mul.
         replace ((Z.of_nat n) * (Z.of_nat (Factorial.fact n)))%Z with ((Z.of_nat (Factorial.fact n)) * Z.of_nat n)%Z by lia.
         Search Zmult. rewrite Zmult_succ_r_reverse. rewrite Z.mul_comm. rewrite <- Znat.Nat2Z.inj_succ. econstructor.
Qed.


End FrameStack.

Module BigStep.



End BigStep.
