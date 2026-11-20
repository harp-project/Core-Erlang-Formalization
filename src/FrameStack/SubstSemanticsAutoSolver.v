(**
  This file contains tactics that automatically prove evaluation goals of the
  (unlabeled) frame stack semantics, by applying the reduction rules step by
  step. The tests of these tactics are in
  `FrameStack/Tests/SubstSemanticsAutoSolverTests.v`.
*)
From CoreErlang.FrameStack Require Export SubstSemantics.

(** `match_solver` closes the (computed) result of pattern matching, if it is
    a successful or a failed match. *)
Ltac match_solver :=
  match goal with
  | [ |- Matches _ = Matches _] => reflexivity
  | [ |- NotMatches = NotMatches] => reflexivity
  | _ => fail "Unexpected goal in match_solver"
  end.

(** `match_list_solver` computes and closes the result of pattern list
    matching. *)
Ltac match_list_solver :=
  match goal with
  | [ |- match_pattern_list _ _ = _] => simpl match_pattern_list; match_solver
  end.

(** `one_step_full_solver` proves a single reduction step, by selecting the
    reduction rule based on the shape of the configuration. *)
Ltac one_step_full_solver :=
  match goal with
  (* Parameter list frames *)
  | [ |- ⟨ FParams _ _ (_ :: _) :: _ , RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => apply eval_step_params
  | [ |- ⟨ FParams _ _ (_ :: _) :: _ , RBox ⟩ --> ⟨ _ , _ ⟩] => apply eval_step_params_0; discriminate
  | [ |- ⟨ FParams _ _ [] :: _ , RBox ⟩ --> ⟨ _ , _ ⟩] => eapply eval_cool_params_0; [discriminate | auto]
  | [ |- ⟨ FParams _ _ [] :: _ , RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => eapply eval_cool_params; auto

  (* Constructs with lists of subexpressions *)
  | [ |- ⟨ _ , RExp (° EValues _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_values
  | [ |- ⟨ _ , RExp (° ETuple _)⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_tuple
  | [ |- ⟨ _ , RExp (° EBin _)⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_bin
  | [ |- ⟨ _ , RExp (° EMap [])⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_map_0
  | [ |- ⟨ _ , RExp (° EMap ((_, _) :: _)) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_map

  (* Calls, primops and applications *)
  | [ |- ⟨ _ , RExp (° ECall _ _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_call_mod
  | [ |- ⟨ FCallMod _ _ :: _, RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_call_fun
  | [ |- ⟨ FCallFun _ _ :: _, RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_call_params
  | [ |- ⟨ _ , RExp (° EPrimOp _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_primop
  | [ |- ⟨ FApp1 _ :: _  , RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_app2
  | [ |- ⟨ _ , RExp (° EApp _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_app

  (* Lists *)
  | [ |- ⟨ FCons1 _ :: _ , RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_cons_1
  | [ |- ⟨ FCons2 _ :: _ , RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_cons_2
  | [ |- ⟨ _ , RExp (° ECons _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_cons

  (* Let, sequencing *)
  | [ |- ⟨ FLet _ _ :: _, RValSeq _ ⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_let; reflexivity
  | [ |- ⟨ _, RExp (° ELet _ _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_let
  | [ |- ⟨ FSeq _ :: _, RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_seq
  | [ |- ⟨ _, RExp (° ESeq _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_seq

  (* Binary segments *)
  | [ |- ⟨ _, RExp (° ESeg _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_seg
  | [ |- ⟨ FSeg1 _ _ _ _ _ :: _, _ ⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_seg_val
  | [ |- ⟨ FSeg2 _ _ _ _ _ :: _, _ ⟩ --> ⟨ _ , _ ⟩] => eapply eval_cool_seg_size; reflexivity

  (* Functions *)
  | [ |- ⟨ _, RExp (° EFun _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_fun

  (* Case *)
  | [ |- ⟨ _ , RExp (° ECase _ _)⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_case
  | [ |- ⟨ FCase1 (_ :: _) :: _ , RValSeq _⟩ --> ⟨ _ , _ ⟩] => apply eval_step_case_not_match; match_list_solver
  | [ |- ⟨ FCase1 (_ :: _) :: _ , RValSeq _⟩ --> ⟨ _ , _ ⟩] => apply eval_step_case_match; match_list_solver
  | [ |- ⟨ FCase2 _ _ _ :: _ , RValSeq [ VLit (Atom "true") ]⟩ --> ⟨ _ , _ ⟩] => apply eval_step_case_true
  (* any other guard value fails *)
  | [ |- ⟨ FCase2 _ _ _ :: _ , RValSeq [ _ ]⟩ --> ⟨ _ , _ ⟩] => apply eval_step_case_false; congruence
  | [ |- ⟨ FCase1 [] :: _ , RValSeq _⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_case_empty

  (* Letrec *)
  | [ |- ⟨ _ , RExp (° ELetRec _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_letrec; auto

  (* Try *)
  | [ |- ⟨ FTry _ _ _ _ :: _ , RValSeq _⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_try_ok; auto
  | [ |- ⟨ FTry _ _ 3 _ :: _ , RExc (_ , _ , _)⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_try_err
  | [ |- ⟨ _ , RExp (° ETry _ _ _ _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_try

  (* Exception propagation *)
  | [ |- ⟨ _ :: _ , RExc _⟩ --> ⟨ _ , _ ⟩] => apply eval_prop_exc; auto

  (* No other pattern matches, needs cooling *)
  | [ |- ⟨ _ , _ ⟩ --> ⟨ _ , _ ⟩] => apply SubstSemantics.cool_value
  end.

(** `make_first_step` proves a `k`-step evaluation goal with 0 steps, or by
    making one step with `one_step_full_solver` (and simplifying the rest). *)
Ltac make_first_step :=
  match goal with
  | [ |- ⟨ _ , _ ⟩ -[ ?k ]-> ⟨ _ , _ ⟩] =>
       apply step_refl +
       (eapply step_trans; [one_step_full_solver | idtac]; cbv)
  end.

(** `many_step_solver` makes steps until the evaluation is finished. *)
Ltac many_step_solver := repeat make_first_step.

(** `star_step_solver` proves goals of the form `⟨ fs, e ⟩ -->* r`. *)
Ltac star_step_solver :=
    eexists;
    split; [
      constructor
    | cbv; many_step_solver
    ].
