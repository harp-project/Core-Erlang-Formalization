From CoreErlang.FrameStack Require Export Frames SubstSemantics.
From CoreErlang.Concurrent Require Export ProcessSemantics.
From CoreErlang.Interpreter Require Export EqualityFunctions.
From CoreErlang.Interpreter Require Import StepFunctions.

(*-----------------------------------------------*)
(* Process semantics tests *)

Definition ex_Clos_1: Val :=
 VClos
  [(0, 1,
    ° ELet 1 (˝ VCons (VLit 97%Z) (VCons (VVar 1) VNil))
    (° ESeq (° ECall (˝ VLit "erlang"%string) (˝ VLit "list_to_atom"%string) [˝ VVar 0])
      (° ELet 1 (° ECall (˝ VLit "erlang"%string) (˝ VLit "+"%string) [˝ VVar 2; ˝ VLit 1%Z])
      (° EApp (˝ VFunId (2, 1)) [˝ VVar 0]))))] 0 1
  (° ELet 1 (˝ VCons (VLit 97%Z) (VCons (VVar 1) VNil))
    (° ESeq (° ECall (˝ VLit "erlang"%string) (˝ VLit "list_to_atom"%string) [˝ VVar 0])
      (° ELet 1 (° ECall (˝ VLit "erlang"%string) (˝ VLit "+"%string) [˝ VVar 2; ˝ VLit 1%Z])
      (° EApp (˝ VFunId (2, 1)) [˝ VVar 0])))).

Definition ex_Clos_2: Val :=
 VClos
  [(0, 1,
    ° ELet 1 (˝ VCons (VLit 97%Z) (VCons (VVar 1) VNil))
    (° ESeq (° ECall (˝ VLit "erlang"%string) (˝ VLit "list_to_atom"%string) [˝ VVar 0])
      (° ELet 1 (° ECall (˝ VLit "erlang"%string) (˝ VLit "-"%string) [˝ VVar 2; ˝ VLit 1%Z])
      (° EApp (˝ VFunId (2, 1)) [˝ VVar 0]))))] 0 1
  (° ELet 1 (˝ VCons (VLit 97%Z) (VCons (VVar 1) VNil))
    (° ESeq (° ECall (˝ VLit "erlang"%string) (˝ VLit "list_to_atom"%string) [˝ VVar 0])
      (° ELet 1 (° ECall (˝ VLit "erlang"%string) (˝ VLit "+"%string) [˝ VVar 2; ˝ VLit 1%Z])
      (° EApp (˝ VFunId (2, 1)) [˝ VVar 0])))).

(** SIGNAL ARRIVAL *)

(* p_arrive *)

(* p_arrive simple case *)
Definition test_process_1 : Process := (inl ([], RBox, emptyBox, ∅, true)).
Definition test_action_1  : Action  := (AArrive 1 2 (SMessage (VLit 0%Z))).
Definition test_result_1  : option Process := Some (inl ([], RBox, ([], [VLit 0%Z]), ∅, true)).
Goal processLocalStepFunc test_process_1 test_action_1 = test_result_1.
Proof. reflexivity. Qed.

(* p_arrive correct with sending PIDs *)
Definition test_process_2 : Process := (inl ([], RBox, emptyBox, ∅, true)).
Definition test_action_2  : Action  := (AArrive 1 2 (SMessage (VPid 0))).
Definition test_result_2  : option Process := Some (inl ([], RBox, ([], [VPid 0]), ∅, true)).
Goal processLocalStepFunc test_process_2 test_action_2 = test_result_2.
Proof. reflexivity. Qed.

Definition test_process_3 : Process := (inl ([], RBox, emptyBox, ∅, true)).
Definition test_action_3  : Action  := (AArrive 1 2 (SMessage (VPid 0))).
Definition test_result_3  : option Process := Some (inl ([], RBox, ([], [VPid 1]), ∅, true)).
Goal processLocalStepFunc test_process_3 test_action_3 <> test_result_3.
Proof. discriminate. Qed.

(* p_arrive correct with sending closures *)
Definition test_process_4 : Process := (inl ([], RBox, emptyBox, ∅, true)).
Definition test_action_4  : Action  := (AArrive 1 2 (SMessage ex_Clos_1)).
Definition test_result_4  : option Process := Some (inl ([], RBox, ([], [ex_Clos_1]), ∅, true)).
Goal processLocalStepFunc test_process_4 test_action_4 = test_result_4.
Proof. reflexivity. Qed.

Definition test_process_5 : Process := (inl ([], RBox, emptyBox, ∅, true)).
Definition test_action_5  : Action  := (AArrive 1 2 (SMessage ex_Clos_1)).
Definition test_result_5  : option Process := Some (inl ([], RBox, ([], [ex_Clos_2]), ∅, true)).
Goal processLocalStepFunc test_process_5 test_action_5 <> test_result_5.
Proof. discriminate. Qed.

(* p_arrive preserves things *)
Goal forall fs e links flag, processLocalStepFunc (inl (fs, e, emptyBox, links, flag)) (AArrive 1 2 (SMessage ex_Clos_1))
     = Some (inl (fs, e, ([], [ex_Clos_1]), links, flag)).
Proof. reflexivity. Qed.

(* p_exit_drop *)
(* reason = normal /\ dest <> source /\ flag = false *)
Definition test_process_6 : Process := (inl ([], RBox, emptyBox, ∅, false)).
Definition test_action_6  : Action  := (AArrive 42 2 (SExit normal true)).
Definition test_result_6  : option Process := Some (inl ([], RBox, emptyBox, ∅, false)).
Goal processLocalStepFunc test_process_6 test_action_6 = test_result_6.
Proof. reflexivity. Qed.

(* source ∉ links /\ b = true /\ dest <> source *)
Definition test_process_7 : Process := (inl ([], RBox, emptyBox, ∅, true)).
Definition test_action_7  : Action  := (AArrive 42 2 (SExit normal true)).
Definition test_result_7  : option Process := Some (inl ([], RBox, emptyBox, ∅, true)).
Goal processLocalStepFunc test_process_7 test_action_7 = test_result_7.
Proof. reflexivity. Qed.

(* p_exit_terminate *)
(* (reason = kill /\ b = false /\ reason' = killed) *)
Definition test_process_8 : Process := (inl ([], RBox, emptyBox, {[1;2;3]}, true)).
Definition test_action_8  : Action  := (AArrive 42 2 (SExit kill false)).
Definition test_result_8  : option Process := Some (inr {[ 1 := killed; 2 := killed; 3 := killed]}).
Goal processLocalStepFunc test_process_8 test_action_8 = test_result_8.
Proof. reflexivity. Qed.

(* others do not get notified *)
Definition test_process_9 : Process := (inl ([], RBox, emptyBox, {[1;2;3]}, true)).
Definition test_action_9  : Action  := (AArrive 42 2 (SExit kill false)).
Definition test_result_9  : option Process := Some (inr {[ 1 := killed; 2 := killed; 3 := killed; 4 := killed]}).
Goal processLocalStepFunc test_process_9 test_action_9 <> test_result_9.
Proof. discriminate. Qed.

(* everyone gets notified *)
Definition test_process_10 : Process := (inl ([], RBox, emptyBox, {[1;2;3]}, true)).
Definition test_action_10  : Action  := (AArrive 42 2 (SExit kill false)).
Definition test_result_10  : option Process := Some (inr ∅).
Goal processLocalStepFunc test_process_10 test_action_10 <> test_result_10.
Proof. discriminate. Qed.

(* (flag = false /\ reason <> normal /\ reason' = reason /\ b = true /\ source ∈ links *)
Definition test_process_11 : Process := (inl ([], RBox, emptyBox, {[1;2;3]}, false)).
Definition test_action_11  : Action  := (AArrive 1 2 (SExit kill true)).
Definition test_result_11  : option Process := Some (inr {[ 1 := kill; 2 := kill; 3 := kill]}).
Goal processLocalStepFunc test_process_11 test_action_11 = test_result_11.
Proof. reflexivity. Qed.

(* (flag = false /\ reason <> normal /\ reason' = reason /\ b = false /\ reason <> kill) *)
Definition test_process_12 : Process := (inl ([], RBox, emptyBox, {[1;2;3]}, false)).
Definition test_action_12  : Action  := (AArrive 42 2 (SExit killed false)).
Definition test_result_12  : option Process := Some (inr {[ 1 := killed; 2 := killed; 3 := killed]}).
Goal processLocalStepFunc test_process_12 test_action_12 = test_result_12.
Proof. reflexivity. Qed.

(* (flag = false /\ reason <> normal /\ reason' = reason /\ source ∈ links /\ reason <> kill) *)
Goal forall b, processLocalStepFunc (inl ([], RBox, emptyBox, {[1;2;3]}, false)) (AArrive 1 2 (SExit killed b))
     = Some (inr {[ 1 := killed; 2 := killed; 3 := killed]}).
Proof. intros. destruct b; reflexivity. Qed.

(* p_exit_convert *)
(* (b = false /\ reason <> kill) *)
Definition test_process_13 : Process := (inl ([], RBox, emptyBox, ∅, true)).
Definition test_action_13  : Action  := (AArrive 42 2 (SExit normal false)).
Definition test_result_13  : option Process := Some (inl ([], RBox, ([], [VTuple [EXIT; VPid 42; normal]]), ∅, true)).
Goal processLocalStepFunc test_process_13 test_action_13  = test_result_13.
Proof. reflexivity. Qed.

(* (b = true /\ source ∈ links) *)
Definition test_process_14 : Process := (inl ([], RBox, emptyBox, {[42]}, true)).
Definition test_action_14  : Action  := (AArrive 42 2 (SExit normal true)).
Definition test_result_14  : option Process := Some (inl ([], RBox, ([], [VTuple [EXIT; VPid 42; normal]]), {[42]}, true)).
Goal processLocalStepFunc test_process_14 test_action_14 = test_result_14.
Proof. reflexivity. Qed.

(* p_link_arrived *)
(* p_link_arrived simple case *)
Definition test_process_15 : Process := (inl ([], RBox, emptyBox, ∅, true)).
Definition test_action_15  : Action  := (AArrive 42 2 SLink).
Definition test_result_15  : option Process := Some (inl ([], RBox, emptyBox, {[42]}, true)).
Goal processLocalStepFunc test_process_15 test_action_15 = test_result_15.
Proof. reflexivity. Qed.

(* p_link_arrived same link arrives *)
Definition test_process_16 : Process := (inl ([], RBox, emptyBox, {[42]}, true)).
Definition test_action_16  : Action  := (AArrive 42 2 SLink).
Definition test_result_16  : option Process := Some (inl ([], RBox, emptyBox, {[42]}, true)).
Goal processLocalStepFunc test_process_16 test_action_16 = test_result_16.
Proof. reflexivity. Qed.

(* p_link_arrived preserves things *)
Goal forall fs e mb flag, processLocalStepFunc (inl (fs, e, mb, ∅, flag)) (AArrive 42 2 SLink)
     = Some (inl (fs, e, mb, {[42]}, flag)).
Proof. reflexivity. Qed.

(* p_unlink_arrived *)
(* p_unlink_arrived simple case *)
Definition test_process_17 : Process := (inl ([], RBox, emptyBox, {[42]}, true)).
Definition test_action_17  : Action  := (AArrive 42 2 SUnlink).
Definition test_result_17  : option Process := Some (inl ([], RBox, emptyBox, ∅, true)).
Goal processLocalStepFunc test_process_17 test_action_17 = test_result_17.
Proof. reflexivity. Qed.

(* p_unlink_arrived simple case *)
Definition test_process_18 : Process := (inl ([], RBox, emptyBox, {[42]}, true)).
Definition test_action_18  : Action  := (AArrive 42 2 SUnlink).
Definition test_result_18  : option Process := Some (inl ([], RBox, emptyBox, ∅, true)).
Goal processLocalStepFunc test_process_18 test_action_18 = test_result_18.
Proof. reflexivity. Qed.

(* p_unlink_arrived nonexistant link *)
Definition test_process_19 : Process := (inl ([], RBox, emptyBox, {[42]}, true)).
Definition test_action_19  : Action  := (AArrive 1 2 SUnlink).
Definition test_result_19  : option Process := Some (inl ([], RBox, emptyBox, {[42]}, true)).
Goal processLocalStepFunc test_process_19 test_action_19 = test_result_19.
Proof. reflexivity. Qed.

(* p_unlink_arrived preserves things *)
Goal forall fs e mb flag, processLocalStepFunc (inl (fs, e, mb, ∅, flag)) (AArrive 42 2 SUnlink)
     = Some (inl (fs, e, mb, ∅, flag)).
Proof. reflexivity. Qed.

(** SIGNAL SENDING *)

(* p_send simple case *)
Definition test_process_20 : Process := (inl ([FParams (ICall erlang send) [VPid 2] []], RValSeq [VNil], emptyBox, ∅, true)).
Definition test_action_20  : Action  := (ASend 1 2 (SMessage VNil)).
Definition test_result_20  : option Process := Some (inl ([], RValSeq [VNil], emptyBox, ∅, true)).
Goal processLocalStepFunc test_process_20 test_action_20 = test_result_20.
Proof. reflexivity. Qed.

(* p_send can't send wrong reason *)
Definition test_process_21 : Process := (inl ([FParams (ICall erlang send) [VPid 2] []], RValSeq [VNil], emptyBox, ∅, true)).
Definition test_action_21  : Action  := (ASend 1 2 (SMessage (VLit 0%Z))).
Definition test_result_21  : option Process := None.
Goal processLocalStepFunc test_process_21 test_action_21 = test_result_21.
Proof. reflexivity. Qed.

(* p_send correct with sending PIDs *)
Definition test_process_22 : Process := (inl ([FParams (ICall erlang send) [VPid 2] []], RValSeq [VPid 420], emptyBox, ∅, true)).
Definition test_action_22  : Action  := (ASend 1 2 (SMessage (VPid 420))).
Definition test_result_22  : option Process := Some (inl ([], RValSeq [VPid 420], emptyBox, ∅, true)).
Goal processLocalStepFunc test_process_22 test_action_22 = test_result_22.
Proof. reflexivity. Qed.

Definition test_process_23 : Process := (inl ([FParams (ICall erlang send) [VPid 2] []], RValSeq [VPid 420], emptyBox, ∅, true)).
Definition test_action_23  : Action  := (ASend 1 2 (SMessage (VPid 420))).
Definition test_result_23  : option Process := Some (inl ([], RValSeq [VPid 42], emptyBox, ∅, true)).
Goal processLocalStepFunc test_process_3 test_action_23 <> test_result_23.
Proof. discriminate. Qed.

(* p_send correct with sending closures *)
Definition test_process_24 : Process := (inl ([FParams (ICall erlang send) [VPid 2] []], RValSeq [ex_Clos_1], emptyBox, ∅, true)).
Definition test_action_24  : Action  := (ASend 1 2 (SMessage (ex_Clos_1))).
Definition test_result_24  : option Process := Some (inl ([], RValSeq [ex_Clos_1], emptyBox, ∅, true)).
Goal processLocalStepFunc test_process_24 test_action_24 = test_result_24.
Proof. reflexivity. Qed.

Definition test_process_25 : Process := (inl ([FParams (ICall erlang send) [VPid 2] []], RValSeq [ex_Clos_1], emptyBox, ∅, true)).
Definition test_action_25  : Action  := (ASend 1 2 (SMessage (ex_Clos_1))).
Definition test_result_25  : option Process := Some (inl ([], RValSeq [ex_Clos_2], emptyBox, ∅, true)).
Goal processLocalStepFunc test_process_25 test_action_25 <> test_result_25.
Proof. discriminate. Qed.

(* p_exit *)
Definition test_process_26 : Process := (inl ([FParams (ICall erlang exit) [VPid 2] []], RValSeq [VNil], emptyBox, ∅, true)).
Definition test_action_26  : Action  := (ASend 1 2 (SExit VNil false)).
Definition test_result_26  : option Process := Some (inl ([], RValSeq [ttrue], emptyBox, ∅, true)).
Goal processLocalStepFunc test_process_26 test_action_26 = test_result_26.
Proof. reflexivity. Qed.

(* p_exit can't send wrong reason *)
Definition test_process_27 : Process := (inl ([FParams (ICall erlang exit) [VPid 2] []], RValSeq [VNil], emptyBox, ∅, true)).
Definition test_action_27  : Action  := (ASend 1 2 (SExit (VLit 0%Z) false)).
Definition test_result_27  : option Process := None.
Goal processLocalStepFunc test_process_27 test_action_27 = test_result_27.
Proof. reflexivity. Qed.

(* p_link *)
Definition test_process_28 : Process := (inl ([FParams (ICall erlang link) [] []], RValSeq [VPid 2], emptyBox, ∅, true)).
Definition test_action_28  : Action  := (ASend 1 2 SLink).
Definition test_result_28  : option Process :=  Some (inl ([], RValSeq [ok], emptyBox, {[2]}, true)).
Goal processLocalStepFunc test_process_28 test_action_28 = test_result_28.
Proof. reflexivity. Qed.

(* p_link to already linked process *)
Definition test_process_29 : Process := (inl ([FParams (ICall erlang link) [] []], RValSeq [VPid 2], emptyBox, {[2]}, true)).
Definition test_action_29  : Action  := (ASend 1 2 SLink).
Definition test_result_29  : option Process := Some (inl ([], RValSeq [ok], emptyBox, {[2]}, true)).
Goal processLocalStepFunc test_process_29 test_action_29 = test_result_29.
Proof. reflexivity. Qed.

(* p_link can't link to wrong process *)
Definition test_process_30 : Process := (inl ([FParams (ICall erlang link) [] []], RValSeq [VPid 2], emptyBox, ∅, true)).
Definition test_action_30  : Action  := (ASend 1 3 SLink).
Definition test_result_30  : option Process := None.
Goal processLocalStepFunc test_process_30 test_action_30 = test_result_30.
Proof. reflexivity. Qed.

(* p_unlink *)
Definition test_process_31 : Process := (inl ([FParams (ICall erlang unlink) [] []], RValSeq [VPid 2], emptyBox, {[2]}, true)).
Definition test_action_31  : Action  := (ASend 1 2 SUnlink).
Definition test_result_31  : option Process := Some (inl ([], RValSeq [ok], emptyBox, ∅, true)).
Goal processLocalStepFunc test_process_31 test_action_31 = test_result_31.
Proof. reflexivity. Qed.

(* p_unlink from not linked process *)
Definition test_process_32 : Process := (inl ([FParams (ICall erlang unlink) [] []], RValSeq [VPid 2], emptyBox, {[3]}, true)).
Definition test_action_32  : Action  := (ASend 1 2 SUnlink).
Definition test_result_32  : option Process := Some (inl ([], RValSeq [ok], emptyBox, {[3]}, true)).
Goal processLocalStepFunc test_process_32 test_action_32 = test_result_32.
Proof. reflexivity. Qed.

(* p_unlink can't unlink from wrong process *)
Definition test_process_33 : Process := (inl ([FParams (ICall erlang unlink) [] []], RValSeq [VPid 2], emptyBox, ∅, true)).
Definition test_action_33  : Action  := (ASend 1 3 SUnlink).
Definition test_result_33  : option Process := None.
Goal processLocalStepFunc test_process_33 test_action_33 = test_result_33.
Proof. reflexivity. Qed.

(* p_dead *)
Definition test_process_34 : Process := (inr {[ 1 := killed; 2 := normal; 3 := kill ]}).
Definition test_action_34  : Action  := (ASend 1 2 (SExit normal true)).
Definition test_result_34  : option Process := Some (inr {[1 := killed; 3 := kill]}).
Goal processLocalStepFunc test_process_34 test_action_34 = test_result_34.
Proof. reflexivity. Qed.

(* p_dead wrong reason *)
Definition test_process_35 : Process := (inr {[ 1 := killed; 2 := normal; 3 := kill ]}).
Definition test_action_35  : Action  := (ASend 1 2 (SExit kill true)).
Definition test_result_35  : option Process := None.
Goal processLocalStepFunc test_process_35 test_action_35 = test_result_35.
Proof. reflexivity. Qed.

(* p_dead nonexistant linked process *)
Definition test_process_36 : Process := (inr {[ 1 := killed; 2 := normal; 3 := kill ]}).
Definition test_action_36  : Action  := (ASend 1 42 (SExit normal true)).
Definition test_result_36  : option Process := None.
Goal processLocalStepFunc test_process_36 test_action_36 = test_result_36.
Proof. reflexivity. Qed.

(** SELF *)

(* p_self *)
Definition test_process_37 : Process := (inl ([FParams (ICall erlang self) [] []], RBox, emptyBox, ∅, true)).
Definition test_action_37  : Action  := (ASelf 420).
Definition test_result_37  : option Process := Some (inl ([], RValSeq [VPid 420], emptyBox, ∅, true)).
Goal processLocalStepFunc test_process_37 test_action_37 = test_result_37.
Proof. reflexivity. Qed.

(** SPAWNING *)

Definition ex_Cons_1 : Val :=
  VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) VNil)).

Definition ex_Clos_3 : Val :=
  VClos [] 1 3 (˝ VNil).

Definition ex_Clos_4 : Val :=
  VClos [] 1 4 (˝ VNil).

(* p_spawn simple case *)
Definition test_process_38 : Process := (inl ([FParams (ICall erlang spawn) [ex_Clos_3] []], RValSeq [ex_Cons_1], emptyBox, ∅, true)).
Definition test_action_38  : Action  := (ASpawn 42 ex_Clos_3 ex_Cons_1 false).
Definition test_result_38  : option Process := Some (inl ([], RValSeq [VPid 42], emptyBox, ∅, true)).
Goal processLocalStepFunc test_process_38 test_action_38 = test_result_38.
Proof. reflexivity. Qed.

(* p_spawn wrong number of args *)
Definition test_process_39 : Process := (inl ([FParams (ICall erlang spawn) [ex_Clos_4] []], RValSeq [ex_Cons_1], emptyBox, ∅, true)).
Definition test_action_39  : Action  := (ASpawn 42 ex_Clos_4 ex_Cons_1 false).
Definition test_result_39  : option Process := None.
Goal processLocalStepFunc test_process_39 test_action_39 = test_result_39.
Proof. reflexivity. Qed.

(* p_spawn_link simple case *)
Definition test_process_40 : Process := (inl ([FParams (ICall erlang spawn_link) [ex_Clos_3] []], RValSeq [ex_Cons_1], emptyBox, ∅, true)).
Definition test_action_40  : Action  := (ASpawn 42 ex_Clos_3 ex_Cons_1 true).
Definition test_result_40  : option Process := Some (inl ([], RValSeq [VPid 42], emptyBox, {[42]}, true)).
Goal processLocalStepFunc test_process_40 test_action_40 = test_result_40.
Proof. reflexivity. Qed.

(* p_spawn_link wrong number of args *)
Definition test_process_41 : Process := (inl ([FParams (ICall erlang spawn_link) [ex_Clos_4] []], RValSeq [ex_Cons_1], emptyBox, ∅, true)).
Definition test_action_41  : Action  := (ASpawn 42 ex_Clos_4 ex_Cons_1 true).
Definition test_result_41  : option Process := None.
Goal processLocalStepFunc test_process_41 test_action_41 = test_result_41.
Proof. reflexivity. Qed.

(** RECEIVING *)
Definition ex_msg : Val := VLit "you've got mail!"%string.
Definition ex_msg_2 : Val := VLit "you've got more mail!"%string.
Definition ex_msg_3 : Val := VLit "you've got even more mail!"%string.

(* p_recv_peek_message_ok *)
Definition test_process_42 : Process := (inl ([FParams (IPrimOp "recv_peek_message") [] []], RBox, ([], [ex_msg]), ∅, true)).
Definition test_action_42  : Action  := τ.
Definition test_result_42  : option Process := Some (inl ([], RValSeq [ttrue; ex_msg], ([], [ex_msg]), ∅, true)).
Goal processLocalStepFunc test_process_42 test_action_42 = test_result_42.
Proof. reflexivity. Qed.

(* p_recv_peek_message_no_message *)
Definition test_process_43 : Process := (inl ([FParams (IPrimOp "recv_peek_message") [] []], RBox, emptyBox, ∅, true)).
Definition test_action_43  : Action  := ε.
Definition test_result_43  : option Process := Some (inl ([], RValSeq [ffalse; ErrorVal], emptyBox, ∅, true)).
Goal processLocalStepFunc test_process_43 test_action_43 = test_result_43.
Proof. reflexivity. Qed.

(* p_recv_next *)
Definition test_process_44 : Process := (inl ([FParams (IPrimOp "recv_next") [] []], RBox, ([], [ex_msg]), ∅, true)).
Definition test_action_44  : Action  := τ.
Definition test_result_44  : option Process := Some (inl ([], RValSeq [ok], ([ex_msg], []), ∅, true)).
Goal processLocalStepFunc test_process_44 test_action_44 = test_result_44.
Proof. reflexivity. Qed.

(* p_remove_message *)
Definition test_process_45 : Process := (inl ([FParams (IPrimOp "remove_message") [] []], RBox, ([ex_msg_2], [ex_msg]), ∅, true)).
Definition test_action_45  : Action  := τ.
Definition test_result_45  : option Process :=  Some (inl ([], RValSeq [ok], ([], [ex_msg_2]), ∅, true)).
Goal processLocalStepFunc test_process_45 test_action_45 = test_result_45.
Proof. reflexivity. Qed.

(* p_remove_message doesn't work with empty unseen messages *)
Definition test_process_46 : Process := (inl ([FParams (IPrimOp "remove_message") [] []], RBox, ([ex_msg], []), ∅, true)).
Definition test_action_46  : Action  := τ.
Definition test_result_46  : option Process := None.
Goal processLocalStepFunc test_process_46 test_action_46 = test_result_46.
Proof. reflexivity. Qed.

(* p_recv_wait_timeout_new_message *)
Definition test_process_47 : Process := (inl ([FParams (IPrimOp "recv_wait_timeout") [] []], RValSeq [infinity], ([ex_msg], [ex_msg_2; ex_msg_3]), ∅, true)).
Definition test_action_47  : Action  := τ.
Definition test_result_47  : option Process := Some (inl ([], RValSeq [ffalse], ([ex_msg], [ex_msg_2; ex_msg_3]), ∅, true)).
Goal processLocalStepFunc test_process_47 test_action_47 = test_result_47.
Proof. reflexivity. Qed.

(* p_recv_wait_timeout_0 *)
Definition test_process_48 : Process := (inl ([FParams (IPrimOp "recv_wait_timeout") [] []], RValSeq [VLit 0%Z], ([ex_msg], [ex_msg_2; ex_msg_3]), ∅, true)).
Definition test_action_48  : Action  := τ.
Definition test_result_48  : option Process := Some (inl ([], RValSeq [ttrue], ([ex_msg], [ex_msg_2; ex_msg_3]), ∅, true)).
Goal processLocalStepFunc test_process_48 test_action_48 = test_result_48.
Proof. reflexivity. Qed.

(* p_recv_wait_timeout_invalid string *)
Definition test_process_49 : Process := (inl ([FParams (IPrimOp "recv_wait_timeout") [] []], RValSeq [VLit "This is invalid"%string], ([ex_msg], [ex_msg_2; ex_msg_3]), ∅, true)).
Definition test_action_49  : Action  := τ.
Definition test_result_49  : option Process := Some (inl ([], RExc (Error, VLit "timeout_value"%string, VLit "This is invalid"%string), ([ex_msg], [ex_msg_2; ex_msg_3]), ∅, true)).
Goal processLocalStepFunc test_process_49 test_action_49 = test_result_49.
Proof. reflexivity. Qed.

(* p_recv_wait_timeout_invalid number *)
Definition test_process_50 : Process := (inl ([FParams (IPrimOp "recv_wait_timeout") [] []], RValSeq [VLit 21%Z], ([ex_msg], [ex_msg_2; ex_msg_3]), ∅, true)).
Definition test_action_50  : Action  := τ.
Definition test_result_50  : option Process := Some (inl ([], RExc (Error, VLit "timeout_value"%string, VLit 21%Z), ([ex_msg], [ex_msg_2; ex_msg_3]), ∅, true)).
Goal processLocalStepFunc test_process_50 test_action_50 = test_result_50.
Proof. reflexivity. Qed.

(* p_recv_wait_timeout_invalid nonliteral *)
Definition test_process_51 : Process := (inl ([FParams (IPrimOp "recv_wait_timeout") [] []], RValSeq [VNil], ([ex_msg], [ex_msg_2; ex_msg_3]), ∅, true)).
Definition test_action_51  : Action  := τ.
Definition test_result_51  : option Process := Some (inl ([], RExc (Error, VLit "timeout_value"%string, VNil), ([ex_msg], [ex_msg_2; ex_msg_3]), ∅, true)).
Goal processLocalStepFunc test_process_51 test_action_51 = test_result_51.
Proof. reflexivity. Qed.

(** PROCESS FLAG *)

(* p_set_flag with previous true flag, set to true *)
Definition test_process_52 : Process := (inl ([FParams (ICall erlang process_flag) [VLit "trap_exit"%string] []], RValSeq [VLit (Atom "true"%string)], emptyBox, ∅, true)).
Definition test_action_52  : Action  := ε.
Definition test_result_52  : option Process := Some (inl ([], RValSeq [VLit "true"%string], emptyBox, ∅, true)).
Goal processLocalStepFunc test_process_52 test_action_52 = test_result_52.
Proof. reflexivity. Qed.

(* p_set_flag with previous false flag, set to true *)
Definition test_process_53 : Process := (inl ([FParams (ICall erlang process_flag) [VLit "trap_exit"%string] []], RValSeq [VLit (Atom "true"%string)], emptyBox, ∅, false)).
Definition test_action_53  : Action  := ε.
Definition test_result_53  : option Process := Some (inl ([], RValSeq [VLit "false"%string], emptyBox, ∅, true)).
Goal processLocalStepFunc test_process_53 test_action_53 = test_result_53.
Proof. reflexivity. Qed.

(* p_set_flag with previous true flag, set to false *)
Definition test_process_54 : Process := (inl ([FParams (ICall erlang process_flag) [VLit "trap_exit"%string] []], RValSeq [VLit (Atom "false"%string)], emptyBox, ∅, true)).
Definition test_action_54  : Action  := ε.
Definition test_result_54  : option Process := Some (inl ([], RValSeq [VLit "true"%string], emptyBox, ∅, false)).
Goal processLocalStepFunc test_process_54 test_action_54 = test_result_54.
Proof. reflexivity. Qed.

(* p_set_flag with previous false flag, set to false *)
Definition test_process_55 : Process := (inl ([FParams (ICall erlang process_flag) [VLit "trap_exit"%string] []], RValSeq [VLit (Atom "false"%string)], emptyBox, ∅, false)).
Definition test_action_55  : Action  := ε.
Definition test_result_55  : option Process := Some (inl ([], RValSeq [VLit "false"%string], emptyBox, ∅, false)).
Goal processLocalStepFunc test_process_55 test_action_55 = test_result_55.
Proof. reflexivity. Qed.

(* p_set_flag_exc *)
Definition test_process_56 : Process := (inl ([FParams (ICall erlang process_flag) [VLit "trap_exit"%string] []], RValSeq [VNil], emptyBox, ∅, true)).
Definition test_action_56  : Action  := τ.
Definition test_result_56  : option Process := Some (inl ([], RExc (Error, VLit "badarg"%string, VNil), emptyBox, ∅, true)).
Goal processLocalStepFunc test_process_56 test_action_56 = test_result_56.
Proof. reflexivity. Qed.

(** TERMINATION *)

(* p_terminate *)
Definition test_process_57 : Process := (inl ([], RValSeq [VLit "42"%string], emptyBox, {[1;2;3]}, true)).
Definition test_action_57  : Action  := ε.
Definition test_result_57  : option Process := Some (inr {[ 1 := normal; 2 := normal; 3 := normal ]}).
Goal processLocalStepFunc test_process_57 test_action_57 = test_result_57.
Proof. reflexivity. Qed.

(** EXCEPTIONS *)

(* p_terminate_exc *)
Definition test_process_58 : Process := (inl ([], RExc (Error, VLit "reason"%string, VLit "this is irrelevant"%string), emptyBox, {[1;2]}, true)).
Definition test_action_58  : Action  := ε.
Definition test_result_58  : option Process := Some (inr {[ 1 := VLit "reason"%string; 2 := VLit "reason"%string ]}).
Goal processLocalStepFunc test_process_58 test_action_58 = test_result_58.
Proof. reflexivity. Qed.

Definition positive_tests : list (Process * Action * option Process) := 
[
  (test_process_1 , test_action_1 , test_result_1 );
  (test_process_2 , test_action_2 , test_result_2 );

  (test_process_4 , test_action_4 , test_result_4 );

  (test_process_6 , test_action_6 , test_result_6 );
  (test_process_7 , test_action_7 , test_result_7 );
  (test_process_8 , test_action_8 , test_result_8 );


  (test_process_11, test_action_11, test_result_11);
  (test_process_12, test_action_12, test_result_12);
  (test_process_13, test_action_13, test_result_13);
  (test_process_14, test_action_14, test_result_14);
  (test_process_15, test_action_15, test_result_15);
  (test_process_16, test_action_16, test_result_16);
  (test_process_17, test_action_17, test_result_17);
  (test_process_18, test_action_18, test_result_18);
  (test_process_19, test_action_19, test_result_19);
  (test_process_20, test_action_20, test_result_20);
  (test_process_21, test_action_21, test_result_21);
  (test_process_22, test_action_22, test_result_22);

  (test_process_24, test_action_24, test_result_24);

  (test_process_26, test_action_26, test_result_26);
  (test_process_27, test_action_27, test_result_27);
  (test_process_28, test_action_28, test_result_28);
  (test_process_29, test_action_29, test_result_29);
  (test_process_30, test_action_30, test_result_30);
  (test_process_31, test_action_31, test_result_31);
  (test_process_32, test_action_32, test_result_32);
  (test_process_33, test_action_33, test_result_33);
  (test_process_34, test_action_34, test_result_34);
  (test_process_35, test_action_35, test_result_35);
  (test_process_36, test_action_36, test_result_36);
  (test_process_37, test_action_37, test_result_37);
  (test_process_38, test_action_38, test_result_38);
  (test_process_39, test_action_39, test_result_39);
  (test_process_40, test_action_40, test_result_40);
  (test_process_41, test_action_41, test_result_41);
  (test_process_42, test_action_42, test_result_42);
  (test_process_43, test_action_43, test_result_43);
  (test_process_44, test_action_44, test_result_44);
  (test_process_45, test_action_45, test_result_45);
  (test_process_46, test_action_46, test_result_46);
  (test_process_47, test_action_47, test_result_47);
  (test_process_48, test_action_48, test_result_48);
  (test_process_49, test_action_49, test_result_49);
  (test_process_50, test_action_50, test_result_50);
  (test_process_51, test_action_51, test_result_51);
  (test_process_52, test_action_52, test_result_52);
  (test_process_53, test_action_53, test_result_53);
  (test_process_54, test_action_54, test_result_54);
  (test_process_55, test_action_55, test_result_55);
  (test_process_56, test_action_56, test_result_56);
  (test_process_57, test_action_57, test_result_57);
  (test_process_58, test_action_58, test_result_58)
].

Definition negative_tests : list (Process * Action * option Process) := 
[
  (test_process_3 , test_action_3 , test_result_3 );
  (test_process_5 , test_action_5 , test_result_5 );
  (test_process_9 , test_action_9 , test_result_9 );
  (test_process_10, test_action_10, test_result_10);
  (test_process_23, test_action_23, test_result_23);
  (test_process_25, test_action_25, test_result_25)
].

Theorem positive_tests_correct: forall (p : Process) (a : Action) (p' : option Process),
  In (p, a, p') positive_tests -> processLocalStepFunc p a = p'.
Proof.
  intros. simpl in H.
  repeat (destruct H;[inv H; reflexivity|]).
  inv H.
Qed.

Theorem negative_tests_correct: forall (p : Process) (a : Action) (p' : option Process),
  In (p, a, p') negative_tests -> processLocalStepFunc p a <> p'.
Proof.
  intros. simpl in H.
  repeat (destruct H;[inv H; discriminate|]).
  inv H.
Qed.







