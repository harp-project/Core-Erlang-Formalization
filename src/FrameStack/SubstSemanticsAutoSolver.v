(**
  This file contains assignments about the semantics of Core Erlang, which can
  help the readers get familiar with it.
*)
From CoreErlang.FrameStack Require SubstSemantics
                                   CIU.
From CoreErlang.FrameStack Require Import Examples.

Open Scope string_scope.

Import FrameStack.SubstSemantics FrameStack.CIU.
Import ListNotations.

 Ltac match_list_solver :=
  match goal with
  (*TODO: is the first pattern neccessary?*)
  | [ |- Some _ = None] => fail
  | [ |- Some _ = Some _] => auto
  | [ |- None = None] => auto
  | _ => fail "Unexpected goal in match_list_solver"
  end.

 Ltac one_step_full_solver :=
  match goal with
  | [ |- ⟨ FParams _ _ (_ :: _) :: _ , RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => apply eval_step_params
  | [ |- ⟨ FParams _ _ (_ :: _) :: _ , RBox ⟩ --> ⟨ _ , _ ⟩] => apply eval_step_params_0; discriminate
  | [ |- ⟨ FParams _ _ [] :: _ , RBox ⟩ --> ⟨ _ , _ ⟩] => eapply eval_cool_params_0; discriminate; auto
  | [ |- ⟨ FParams _ _ [] :: _ , RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => eapply eval_cool_params; auto

  (*needs testing*)
  | [ |- ⟨ _ , RExp (° EValues _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_values
  (*needs testing*)
  | [ |- ⟨ _ , RExp (° ETuple _)⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_tuple
  (*needs testing*)
  | [ |- ⟨ _ , RExp (° EMap [])⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_map_0
  | [ |- ⟨ _ , RExp (° EMap ((_, _) :: _)) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_map

  | [ |- ⟨ _ , RExp (° ECall _ _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_call_mod
  | [ |- ⟨ FCallMod _ _ :: _, RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_call_fun
  | [ |- ⟨ FCallFun _ _ :: _, RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_call_params

  | [ |- ⟨ _ , RExp (° EPrimOp _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_primop

  | [ |- ⟨ FApp1 _ :: _  , RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_app2
  | [ |- ⟨ _ , RExp (° EApp _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_app

  (*needs testing*)
  | [ |- ⟨ FCons1 _ :: _ , RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_cons_1
  | [ |- ⟨ FCons2 _ :: _ , RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_cons_2
  | [ |- ⟨ _ , RExp (° ECons _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_cons

  | [ |- ⟨ FLet _ _ :: _, RValSeq _ ⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_let; reflexivity
  | [ |- ⟨ _, RExp (° ELet _ _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_let
  (*needs testing*)
  | [ |- ⟨ FSeq _ :: _, RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_seq
  (*needs testing*)
  | [ |- ⟨ _, RExp (° ESeq _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_seq
  (*needs testing*)
  | [ |- ⟨ _, RExp (° EFun _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_fun
 
  

  | [ |- ⟨ _ , RExp (° ECase _ _)⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_case
  (***)
  | [ |- ⟨ FCase1 (_ :: _) :: _ , RValSeq _⟩ --> ⟨ _ , _ ⟩] => apply eval_step_case_not_match; cbv; match_list_solver
  | [ |- ⟨ FCase1 (_ :: _) :: _ , RValSeq _⟩ --> ⟨ _ , _ ⟩] => apply eval_step_case_match; cbv; match_list_solver

  | [ |- ⟨ FCase2 _ _ _ :: _ , RValSeq [ VLit (Atom "true") ]⟩ --> ⟨ _ , _ ⟩] => apply eval_step_case_true
  | [ |- ⟨ FCase2 _ _ _ :: _ , RValSeq [ VLit (Atom "false") ]⟩ --> ⟨ _ , _ ⟩] => apply eval_step_case_false
  (***)
  (*needs testing*)
  | [ |- ⟨ FCase1 [] :: _ , RValSeq _⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_case_empty

  | [ |- ⟨ _ , RExp (° ELetRec _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_letrec; auto
  (*needs testing*)
  | [ |- ⟨ FTry _ _ _ _ :: _ , RValSeq _⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_try_ok; auto
  | [ |- ⟨ FTry _ _ 3 _ :: _ , RExc (_ , _ , _)⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_try_err
  | [ |- ⟨ _ , RExp (° ETry _ _ _ _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_try

  | [ |- ⟨ _ :: _ , RExc _⟩ --> ⟨ _ , _ ⟩] => apply eval_prop_exc; auto
  
  
  (*No other pattern matches, needs cooling*)
  | [ |- ⟨ _ , _ ⟩ --> ⟨ _ , _ ⟩] => apply SubstSemantics.cool_value
  
  end.

Ltac make_first_step :=
  match goal with
  | [ |- ⟨ _ , _ ⟩ -[ ?k ]-> ⟨ _ , _ ⟩] =>
       apply step_refl +
       (eapply step_trans; [one_step_full_solver | idtac]; cbv)
  end.

Ltac many_step_solver := repeat make_first_step.

Ltac star_step_solver := 
    eexists;
    split; [ 
      constructor
    | cbv; many_step_solver
    ].
