(**
  This file contains assignments about the semantics of Core Erlang, which can
  help the readers get familiar with it.
*)
(* From CoreErlang.BigStep Require Import FunctionalBigStep. *)
From CoreErlang.FrameStack Require SubstSemantics
                                   CIU.

Open Scope string_scope.

Module FrameStack.

Import FrameStack.SubstSemantics FrameStack.CIU.
Import ListNotations.
(*
  Let "e" be a parameter expression.

  letrec 'fact'/1 =
    fun(X) ->
      case <X> of
        <0> when 'true' -> 1
        <Z>  when 'true'->
          let <Y> = <apply 'fact'/1(call 'erlang':'-'(Z, 1))>
            in call 'erlang':'*'(Z,Y)
    in
      apply 'fact'/1(e)

  Define the above expression!
 *)

Definition fact (e : Exp) : Exp :=
  ˝ttrue (* Write the definition here *)
.

(* Prove the following property *)
(* Hint: to solve statements about scopes (e.g., VALCLOSED), use "scope_solver"!
   Also using "(e)constructor" could help you determine which rule of the semantics
   can be used. Beware, not all semantic rules are syntax-driven, there are rules
   about ECase expressions that can applied to the same configuration.

   Since you prove the evaluation of a factorial function, thus expect repetition
   of proof steps in the script you write. This proof should not be short (>120 LOC),
   if you write out each step.

   Tactics that can aid in this proof: apply, (e)constructor, simpl, cbn, cbv,
     relfexivity, auto, congruence, lia, scope_solver
 *)
Goal
  ⟨[], fact (˝VLit 3%Z)⟩ -->* RValSeq [VLit 6%Z].
Proof.

Admitted.

(* Define the following function in Core Erlang! To compile a Core Erlang file
   use the "from_core" option of the standard compiler/interpreter.
   For examples, we refer to the language specification:
   https://www.diva-portal.org/smash/record.jsf?dswid=-4140&pid=diva2%3A1695554
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
            °ECall (˝erlang) (˝VLit "==") [
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

  Use induction over n! Follow the scheme described in the previous evaluation.
  Check what theorems are available about transitive evaluation.
*)
Theorem fact_eval : forall n,
  ⟨[], fact (˝VLit (Z.of_nat n))⟩ -->* RValSeq [VLit (Z.of_nat (Factorial.fact n))].
Proof.

Admitted.



(*
  Let "e" and "d" be parameter expressions.

  letrec 'fact'/2 =
    fun(X, A) ->
      case <X> of
        <0> when 'true' -> A
        <Z> when 'true' -> apply 'fact'/2(call 'erlang':'-'(Z, 1), call 'erlang':'*'(Z, A))
    in
      apply 'fact'/2(e, d)

  Define the above expression!
 *)
Definition tailrec_fact (e d : Exp) : Exp :=
  ˝ttrue (* Write the definition here *)
.

(* Prove the following property *)
(* Hint: to solve statements about scopes (e.g., VALCLOSED), use "scope_solver"!
   Also using "(e)constructor" could help you determine which rule of the semantics
   can be used. Beware, not all semantic rules are syntax-driven, there are rules
   about ECase expressions that can applied to the same configuration.

   Since you prove the evaluation of a factorial function, thus expect repetition
   of proof steps in the script you write. This proof should not be short,
   if you write out each step.

   Tactics that can aid in this proof: apply, (e)constructor, simpl, cbn, cbv,
     relfexivity, auto, congruence, lia, scope_solver
 *)
Goal
  ⟨[], tailrec_fact (˝VLit 3%Z) (˝VLit 1%Z)⟩ -->* RValSeq [VLit 6%Z].
Proof.

Admitted.

(*
  Hard task:
    Prove the following theorem about the correctness of 
    tailrec_fact!

  Use induction over "n"! Follow the scheme described in the previous
  evaluation. Check what theorems are available about transitive evaluation.

  Remember that this is the tail recursive version of factorial; therefore,
  you should NOT introduce "m" before starting induction (since "m"---the second
  parameter---increases in the recursive applications.
  ).
*)
Theorem tailrec_fact_eval : forall n m,
  ⟨[], tailrec_fact (˝VLit (Z.of_nat n)) (˝VLit (Z.of_nat m))⟩ -->* RValSeq [VLit (Z.of_nat (Factorial.fact n * m))].
Proof.

Admitted.


(* Prove the following program equivalence theorem. *)
(* Hint: search the repository for theorems about evaluation and CIU equivalence!
   Rather than using manual evaluation steps, try to rely on the previous theorems!
 *)
Theorem fact_equiv n :
  CIU (fact (˝VLit (Z.of_nat n))) (tailrec_fact (˝VLit (Z.of_nat n)) (˝VLit 1%Z)).
Proof.

Admitted.


End FrameStack.

Module Concurrent.

Import FrameStack.SubstSemantics.
Import ListNotations.



End Concurrent.
