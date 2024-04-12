(* From CoreErlang.BigStep Require Import FunctionalBigStep. *)
From CoreErlang.FrameStack Require SubstSemantics.


Open Scope string_scope.


Module FrameStack.


Import FrameStack.SubstSemantics.


Import ListNotations.



(* ------------LIT/0------------ *)

(*
  NOTE:
    ˝VLit (Integer 42) = ˝VLit 42%Z
*)

(* 
  'fun1'/0 = fun() -> 42 
*)

Definition fun1_0 : Exp :=
  ˝VLit 42%Z
.

Theorem fun1_test :
  ⟨[], fun1_0⟩ -->* RValSeq [VLit 42%Z].
Proof.
  unfold fun1_0.
  scope_solver.
  eexists.
  split.
  * Print is_result.
    constructor.
    Print Forall.
    constructor.
    + scope_solver.
    + constructor.
  * econstructor.
    + apply cool_value.
      scope_solver.
    + apply step_refl.
Qed.



(* 
  'fun2'/0 = fun() -> "Hello World!" 
*)

Definition fun2_0 : Exp :=
  ˝VLit (Atom "Hello World!")
.



(* 
  'fun3'/0 = fun() -> true
*)

Definition fun3_0 : Exp :=
  ˝ttrue
.



(* 
  'fun4'/0 = fun() -> apply 'fun1'/0()
*)

Definition fun4_0 : Exp :=
  EApp fun1_0 []
.






(* ------------SIMPLE FUNCTION------------ *)



(* 
  'fun5'/1 = fun(X) -> X
*)

Definition fun5_1 (e : Exp) : Exp :=
  e
.



(* 
  'fun6'/1 = fun(X) -> apply X()
*)

Definition fun6_1 (e : Exp) : Exp :=
  EApp e []
.



(* 
  'fun7'/2 = fun(X,Y) -> apply X(Y)
*)

Definition fun7_1 (x y : Exp) : Exp :=
  EApp x [y]
.



(* 
  'fun8'/3 = fun(X,Y) -> apply X(Y)
*)

Definition fun8_3 (x y z : Exp) : Exp :=
  EApp x [y;z]
.






(* ------------ARITMETIC FUNCTION------------ *)



(* 
  'plus1'/1 = fun(X) -> X + 1
*)

Definition plus1_1 (x : Exp) : Exp :=
  °ECall (˝VLit "erlang") (˝VLit "+")  [x; ˝VLit 1%Z]
.



(* 
  'plus'/2 = fun(X,Y) -> X + Y
*)

Definition plus_2 (x y : Exp) : Exp :=
  °ECall (˝VLit "erlang") (˝VLit "+")  [x; y]
.



(* 
  'sub'/2 = fun(X,Y) -> X + Y
*)

Definition sub_2 (x y : Exp) : Exp :=
  °ECall (˝VLit "erlang") (˝VLit "-")  [x; y]
.



(* 
  'multi'/2 = fun(X,Y) -> X * Y
*)

Definition multi_2 (x y : Exp) : Exp :=
  °ECall (˝VLit "erlang") (˝VLit "*")  [x; y]
.



(* 
  'neg'/1 = fun(X) ->
              case <X> of
              <true>  -> false
              <false> -> true
*)

Definition neg_1 (x : Exp) : Exp :=
  ECase x 
        [
          ([PLit (Atom "true")], ˝VLit "true", ˝ffalse);
          ([PLit (Atom "false")], ˝VLit "true", ˝ttrue)
        ]
.


Theorem neg_1_test :
  ⟨[], neg_1 (˝ttrue)⟩ -->* RValSeq [ffalse].
Proof.
  unfold neg_1.
  scope_solver.
  eexists.
  split.
  * Print is_result.
    constructor.
    Print Forall.
    constructor.
    + scope_solver.
    + constructor.
  * econstructor.
    + constructor.
    + econstructor.
      - constructor.
        scope_solver.
      - econstructor.
        ** constructor.
           Print match_pattern_list.
           simpl.
            reflexivity.
        ** econstructor.
           ++ constructor.
              scope_solver.
           ++ simpl. econstructor.
              -- constructor.
              -- econstructor.
                 *** constructor.
                     scope_solver.
                 *** constructor. 
Qed.


(* 
  'minus1pos'/1 = fun(X) ->
                    case <X> of
                      <0> -> 0
                      <Y> -> Y - 1
*)

Definition minus1pos_1 (x : Exp) : Exp :=
  ECase x 
        [
          ([PLit 0%Z], ˝VLit "true", ˝VLit 0%Z);
          ([PVar], ˝VLit "true", (°ECall (˝VLit "erlang") (˝VLit "-")  [˝VVar 0; ˝VLit 1%Z]))
        ]
.



(* 
  'multiple3'/1 = fun(X) ->
                    case <X> of 
                      <0> -> 0
                      <Z> -> let <Y> = Z + Z
                              in Z + Y
*)

Definition multiple3_1 (x : Exp) : Exp :=
  ECase x
    [
      ([PLit 0%Z], ˝VLit "true", 
        ˝VLit 0%Z);
      ([PVar], ˝VLit "true", 
        (°ELet 1 (°ECall (˝VLit "erlang") (˝VLit "+") [˝VVar 0; ˝VVar 0])
          (°ECall (˝VLit "erlang") (˝VLit "+") [˝VVar 1; ˝VVar 0])))
    ]
.





(* ------------RECURZIVE FUNCTION------------ *)




(*
  letrec 'tozero'/1 =
    fun(X) -> 
      case <X> of 
        <0> -> 0
        <Z> -> let <Y> = <apply 'tozero'/1(Z)>
                in Y
 

*)

Definition tozero_1 (x : Exp) : Exp :=
  ELetRec
    [
      (1, °ECase (˝VVar 1)
        [
          ([PLit 0%Z], ˝VLit "true", 
            ˝VLit 0%Z);
          ([PVar], ˝VLit "true", 
            (°ELet 1 (EApp (˝VFunId (1, 1)) [˝VVar 0])
              (˝VVar 0)))
        ])
    ]
  (EApp (˝VFunId (0, 1)) [x])
.








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
