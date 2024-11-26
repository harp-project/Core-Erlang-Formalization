(**
  This file contains assignments about the semantics of Core Erlang, which can
  help the readers get familiar with it.
*)
(* From CoreErlang.BigStep Require Import FunctionalBigStep. *)
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
  ˝ttrue (* Write the definition here *)
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

Admitted.

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
  Hard task:
    Prove the following theorem about the correctness of fact!

  Use induction over n! Follow the scheme described in fact_eval_3. Check what
  theorems are available about transitive evaluation.
*)
Theorem fact_eval : forall n,
  ⟨[], fact_frameStack (˝VLit (Z.of_nat n))⟩ -->* RValSeq [VLit (Z.of_nat (Factorial.fact n))].
Proof.

Admitted.


End FrameStack.

Module BigStep.



End BigStep.
