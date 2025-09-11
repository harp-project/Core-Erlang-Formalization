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
  
Admitted.

From CoreErlang.Interpreter Require Import StepFunctions Equivalences.

Fixpoint sequentialStepMaxK (fs : FrameStack) (r : Redex) (k : nat) : option (FrameStack * Redex) :=
  match k with
  | 0 => Some (fs, r)
  | S k' => match sequentialStepFunc fs r with
            | Some (fs', r') => sequentialStepMaxK fs' r' k'
            | None => match fs, r with
                      | [], RValSeq _ => Some (fs, r)
                      | _, _ => None
                      end
            end
  end.

Arguments sequentialStepFunc !_ !_ /.
Arguments sequentialStepMaxK !_ !_ !_ /.

Fixpoint sequentialStepMaxK' (fs : FrameStack) (r : Redex) (p : positive) : option (FrameStack * Redex) :=
  match p with
  | xH => 
    match sequentialStepFunc fs r with
    | Some (fs', r') => Some (fs', r')
    | None =>
      match fs, r with
      | [], RValSeq _ => Some (fs, r)
      | _, _ => None
      end
    end
  | xO p' => 
    let res := sequentialStepMaxK' fs r p' in
    match res with
    | Some (fs', r') => sequentialStepMaxK' fs' r' p'
    | None => None
    end
  | xI p' => 
    let res := sequentialStepMaxK' fs r p' in
    match res with
    | Some (fs', r') =>
      let res' := sequentialStepMaxK' fs' r' p' in
      match res' with
      | Some (fs'', r'') =>
        match sequentialStepFunc fs'' r'' with
        | Some (fs''', r''') => Some (fs''', r''')
        | None =>
          match fs'', r'' with
          | [], RValSeq _ => Some (fs'', r'')
          | _, _ => None
          end
        end
      | None => None
      end
    | None => None
    end
  end.

Fixpoint sequentialStepMaxK'' (fs : FrameStack) (r : Redex) (p : positive) : option (FrameStack * Redex) :=
  match fs, r with
  | [], RValSeq _ => Some (fs, r)
  | _, _ =>
    match p with
    | xH => sequentialStepFunc fs r
    | xO p' =>
      match sequentialStepMaxK'' fs r p' with
      | Some (fs', r') => sequentialStepMaxK'' fs' r' p'
      | None => None
      end
    | xI p' =>
      match sequentialStepFunc fs r with
      | Some (fs', r') =>
        match sequentialStepMaxK'' fs' r' p' with
        | Some (fs'', r'') => sequentialStepMaxK'' fs'' r'' p'
        | None => None
        end
      | None => None
      end
    end
  end.

Arguments sequentialStepMaxK' !_ !_ !_ /.
Arguments sequentialStepMaxK'' !_ !_ !_ /.

(*
Theorem kSeqStepEquiv: forall fs fs' e e' k, FSCLOSED fs -> REDCLOSED e ->
  ⟨ fs, e ⟩ -[ k ]-> ⟨ fs', e' ⟩ <-> sequentialStepMaxK fs e k = Some (fs', e').
Proof.
  intros. split; intro.
  * induction H1.
    + simpl. reflexivity.
    + simpl. destruct (sequentialStepFunc fs e) eqn:Hssf.
      - destruct p. apply sequentialStepEquiv in Hssf;[|auto].
        pose proof (@step_determinism e e' fs fs' H1 f r Hssf).
        destruct H3. subst. clear H1.
        destruct (step_closedness fs e fs' e' Hssf H H0).
        apply (IHstep_rt H1 H3).
      - apply (sequentialStepEquiv fs fs' e e' H0) in H1. congruence.
  * revert H1 H H0. revert fs fs' e e'. induction k; intros.
    + simpl in H1. inv H1. constructor.
    + simpl in H1. destruct (sequentialStepFunc fs e) eqn:Hssf.
      - destruct p.
        apply sequentialStepEquiv in Hssf;[|auto].
        destruct (step_closedness fs e f r Hssf H H0).
        specialize (IHk f fs' r e' H1 H2 H3).
        apply step_trans with (fs' := f) (e' := r); auto.
      - discriminate.
Qed.*)

Ltac case_innermost_term t :=
  lazymatch t with
  | context[match ?x with _ => _ end] =>
      first [ case_innermost_term x
            | destruct x eqn:?H ]
  | _ => fail "No match subterm found"
  end.

Ltac case_innermost :=
  match goal with
  | |- ?g => case_innermost_term g
  end.

(*Ltac case_innermost' :=
  match goal with
  | [ H: context[match ?x with _ => _ end] |- _ ] =>
      destruct x eqn:?Hx in H; inv Hx; try case_innermost
  | [ |- context[match ?x with _ => _ end] ] =>
      destruct x eqn:?Hx; inv Hx; try case_innermost
  | _ => idtac
  end.*)

Ltac match_unwind t :=
  lazymatch t with
  | context[match ?x with _ => _ end] => match_unwind x; idtac "hello"; simpl
  | _ => simpl
  end.

Ltac unwind :=
  match goal with
  | |- ?g => match_unwind g
  end.

(* Ltac hypothesize_matchstack_term t :=
  lazymatch t with
  | context[match ?x with _ => _ end] => destruct x eqn:?Hx;hypothesize_matchstack_term Hx
  | _ => idtac
  end.

Ltac hypothesize_matchstack :=
  match goal with
  | |- ?g => hypothesize_matchstack_term g
  end. *)

Theorem fact_eval_example':
  forall (z : Z), (0 <= z < 5)%Z -> exists (y : Z), sequentialStepMaxK [] (fact_frameStack (˝VLit z)) 1000 = Some ([], RValSeq [VLit y]) /\ (z <= y)%Z.
Proof.
  intros. unfold fact_frameStack.
  all:simpl. all:try lia.
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
Qed.


Theorem fact_eval_example'':
  forall (z : Z), (0 <= z < 5)%Z -> exists (y : Z), sequentialStepMaxK' [] (fact_frameStack (˝VLit z)) 100000 = Some ([], RValSeq [VLit y]) /\ (z <= y)%Z.
Proof.
  intros. unfold fact_frameStack.
  all:simpl. all:try lia.
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
Qed.


Fixpoint sequentialStepMaxK''' (fs : FrameStack) (r : Redex) (p : positive) : option (FrameStack * Redex) :=
  match sequentialStepFunc fs r with
  | None => 
    match fs, r with
    | [], RValSeq _ => Some (fs, r)
    | _, _ => None
    end
  | Some (fs', r') =>
    match p with
    | xH => Some (fs', r')
    | xO p' =>
      match sequentialStepMaxK''' fs r p' with
      | Some (fs'', r'') => sequentialStepMaxK''' fs'' r'' p'
      | None => None
      end
    | xI p' =>
      match sequentialStepMaxK''' fs' r' p' with
      | Some (fs'', r'') => sequentialStepMaxK''' fs'' r'' p'
      | None => None
      end
    end
  end.

Arguments sequentialStepMaxK''' !_ !_ !_ /.

Theorem fact_eval_example''':
  forall (z : Z), (0 <= z < 5)%Z -> exists (y : Z), sequentialStepMaxK''' [] (fact_frameStack (˝VLit z)) 100000 = Some ([], RValSeq [VLit y]) /\ (z <= y)%Z.
Proof.
  intros. unfold fact_frameStack.
  all:simpl. all:try lia.
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
Qed.


(* symbolic execution plans TODO:
    These plans come "outside in", starting with the big picture.
    Although the actual implementation is likely to be "inside out".
    
    - Start out with an Erlang module file
    - Add comments to it in a standard format, containing preconditions and postconditions about a function
      - Preconditions should be about the input of the function (be mindful about arity)
      - Postconditions should be about the output of the function (termination in RValSeq)
      - Search depth: the "k" steps required for the execution. This should also be a parameter, since
        Coq can not handle divergence.
    - Utilize and change the pretty-printer, so it prints a theorem, where the function to be
      tested is given the arguments specified in the precondition comments. The postcondition is given by the
      value the program leads to and the condition after. The standard format should look like 
      fact_eval_example' above.
      - with this approach, we don't need to develop as much metatheory.
      - however, "k" steps is still an issue. even with the arguments + bang pattern thingy. It gets slower
        as k increases. "simpl" still causes stack overflow for big enough values.
    - Make a custom tactic that tries to solve the goal. Utilize smt solvers (this is when the lack of
      metatheory is a big advantage).
      - Possibly more than 1 SMT solvers should be utilized, with a heuristic?
      - SMT solvers are utilized in 2 cases. Either finding out if the termination satisfies the goal
        (end of config execution), or finding out that a configuration is impossible (moving along with
        config execution).
        - if termination does not satisfy a goal: FAIL: the message should provide the configuration of the
          symbolic variables under which the fail (list of hypotheses). INVESTIGATE: can 'a' (or 'the')
          concrete value be given for symbolic variables under the hypotheses?
        - if termination satisfies the goal, but SMT solvers can not solve the goal: POTENTIAL FAIL: the
          message should provide the hypotheses. Maybe the goal is actually solvable, just not by the SMT
          solver. Unfortunately, because of the laws of the universe as we know it in 2025, not all goals
          are trivially solvable by SMT solvers. It's probably impossible to tell this point and the
          previous one apart (at least I think).
        - if moving along with a configuration can not happen, and the SMT solver find that it can not happen:
          HAPPINESS: goal should be solved automatically.
        - if moving along with a configuration can not happen, and the SMT solver does not find out:
          UNHAPPINESS, TRY MOVING ALONG: this stinks, but as I've stated not all goals are solvable by SMT
          solvers. Maybe we get to configurations that can be solvable? Unfortunately I don't
          think we can do induction automatically (if we can, I think it's a big big hassle).
        - if moving along with the configuration can happen: HAPPINESS, TRY MOVING ALONG: this is a standard
          case. Again, I do not think that we can differentiate between this point and the previous one.
      - The output of the tactic should be a list of goals that could not be solved automatically.
    - Have a way to try to prove everything without even opening the Coq file. So generate the file with the
      new pretty printer from the Erlang source code, and have a 'running' file that tries compiling the
      coq file. If the custom tactic can solve everything, inform the user. If it can not solve everything,
      display the unsolved goals. The user should only have to open Coq for unsolved goals if absolutely
      necessary.
    
    PROS for this approach:
      - The tool should easily integrate with the Erlang code
      - Writing preconditions and postconditions in a standardized way should make goal generation standard
      - If goal generation is standard, metatheory in Coq should not be needed to be developed
      - If metatheory is not needed, integrating SMT solvers should be more straightforward
    CONS (or more precisely, THINGS TO SOLVE):
      - developing the standard way of writing pre- and postconditions in the Erlang file is not
        as easy as it first seems. Preconditions are the trickier part: Arity and symbolic variable order
        might need to be defined by hand (since the precond is just a conjunction of conditions).
        Postconditions need a special symbol for the value produced. This might also need to be hand defined.
      - SMT solvers can not solve everything. We just have to live with this fact.
      - The "k" step problem. A step count needs to be defined, or else the multi-step function is not
        descending. Defining "k" with "nat"-s causes stack overflow, even with the tactics having
        bang pattern arguments. "k" can not be existential, because that would mean that we need to be able
        to calculate it beforehand (impossible). A good solution needs to be devised. I suspect choosing
        "nat"-s for a step count also causes the proofs to be slow.
      - running out of "k" steps should be explicitly stated somehow, somewhere.
      - what about concurrency? I suspect that, since steps are not deterministic, a new way of doing
        multiple steps in a row is required. Like with the pmap example, have a list of actions taken
        along the way (at least I think that's how that works?). This would be very complicated, and honestly,
        it might go beyond the scope of the thesis. Somebody in the future will have the unfortunate task
        of figuring all that out.
      - installing SMT solvers might be a bit complex since the change from Coq to Rocq
      - what about other data types? Integers are one thing, lists, strings and maps are a whole problem
        in their own right. Especially because of bounds (if they are needed).
      - Bounds: I don't think there is a general way to have unbounded expressions. Limiting the step count
        to "k" should solve this issue somewhat. Programs without recursion should be fine, and for recursive
        programs the step limit should suffice.
    
    PLANS for the thesis:
    [x] investigate solutions for the "k" problem           <
    [ ] install SMT solvers (not trivial unfortunately).    | do most of this before the trip to
        Actually, just "lia" can be used until it's done.   | Singapore, and before lab work
    [ ] Have a few nice example programs                    | kicks into high gear
    [ ] implement the solver tactic                         |
    [ ] figure out the pretty printer part                  <
    [ ] equivalence proofs
    [ ] if I have time (hopefully): look into concurrency
    [ ] write the text of the thesis
 *)

Theorem fact_eval_example:
  forall (x y : Z), (x >= 0)%Z /\ (x < 3)%Z -> ⟨[], fact_frameStack (˝VLit x)⟩ -->* RValSeq [VLit y] -> (x <= y)%Z.
Proof.
  intros. unfold step_any in H0. destruct H0. destruct H0. unfold fact_frameStack in H1.
  inv H1; apply sequentialStepEquiv in H2;[|scope_solver]; simpl in H2; inv H2.
  inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
  inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
  inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
  inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
  inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
  inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
  inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
  inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
  inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
  destruct x eqn:Hx; inv H4.
  * inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3. Search "<="%Z 0. apply Z2Nat.neq_0_nonneg. auto. inv H1.
  * inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    destruct (if (Z.pos p - 1 =? 0)%Z then Some [] else None) eqn:Hp.
    + inv H4. inv H2. inv H1. inv H3. inv H1. inv H2. inv H1. inv H3. inv H1.
      inv H2. inv H1. inv H3. inv H1. inv H2. inv H1. inv H3. inv H1. inv H2.
      inv H1. inv H3. inv H1. inv H2. inv H1. inv H3. inv H1. inv H2. inv H1.
      inv H3. inv H1. inv H17. inv H2.
      - Search "*"%Z. rewrite Z.mul_1_r. apply Z.le_refl.
      - inv H1.
    + inv H4. inv H2. inv H1. inv H3. inv H1. inv H2. inv H1. inv H3. inv H1.
      inv H2. inv H1. inv H3. inv H1. inv H2. inv H1. inv H3. inv H1. inv H2.
      inv H1. inv H3. inv H1. inv H2. inv H1. inv H3. inv H1. inv H2. inv H1.
      inv H3. inv H1. inv H2. inv H1. inv H3. inv H1. inv H2. inv H1. inv H3.
      inv H1. inv H2. admit.
  * lia. (* H is impossible *)
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
  (*
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
         *)
Admitted.


End FrameStack.

Module BigStep.



End BigStep.


	
