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
Goal processLocalStepFunc (inl ([], RBox, emptyBox, ∅, true)) (AArrive 1 2 (SMessage (VLit 0%Z)))
     = Some (inl ([], RBox, ([], [VLit 0%Z]), ∅, true)).
Proof. reflexivity. Qed.

(* p_arrive correct with sending PIDs *)
Goal processLocalStepFunc (inl ([], RBox, emptyBox, ∅, true)) (AArrive 1 2 (SMessage (VPid 0)))
     = Some (inl ([], RBox, ([], [VPid 0]), ∅, true)).
Proof. reflexivity. Qed.

Goal processLocalStepFunc (inl ([], RBox, emptyBox, ∅, true)) (AArrive 1 2 (SMessage (VPid 0)))
     <> Some (inl ([], RBox, ([], [VPid 1]), ∅, true)).
Proof. discriminate. Qed.

(* p_arrive correct with sending closures *)
Goal processLocalStepFunc (inl ([], RBox, emptyBox, ∅, true)) (AArrive 1 2 (SMessage ex_Clos_1))
     = Some (inl ([], RBox, ([], [ex_Clos_1]), ∅, true)).
Proof. reflexivity. Qed.

Goal processLocalStepFunc (inl ([], RBox, emptyBox, ∅, true)) (AArrive 1 2 (SMessage ex_Clos_1))
     <> Some (inl ([], RBox, ([], [ex_Clos_2]), ∅, true)).
Proof. discriminate. Qed.

(* p_arrive preserves things *)

Goal forall fs e links flag, processLocalStepFunc (inl (fs, e, emptyBox, links, flag)) (AArrive 1 2 (SMessage ex_Clos_1))
     = Some (inl (fs, e, ([], [ex_Clos_1]), links, flag)).
Proof. reflexivity. Qed.

(* p_exit_drop *)
(* reason = normal /\ dest <> source /\ flag = false *)
Goal processLocalStepFunc (inl ([], RBox, emptyBox, ∅, false)) (AArrive 42 2 (SExit normal true))
     = Some (inl ([], RBox, emptyBox, ∅, false)).
Proof. reflexivity. Qed.

(* source ∉ links /\ b = true /\ dest <> source *)
Goal processLocalStepFunc (inl ([], RBox, emptyBox, ∅, true)) (AArrive 42 2 (SExit normal true))
     = Some (inl ([], RBox, emptyBox, ∅, true)).
Proof. reflexivity. Qed.

(* p_exit_terminate *)
(* (reason = kill /\ b = false /\ reason' = killed) *)
Goal processLocalStepFunc (inl ([], RBox, emptyBox, {[1;2;3]}, true)) (AArrive 42 2 (SExit kill false))
     = Some (inr {[ 1 := killed; 2 := killed; 3 := killed]}).
Proof. reflexivity. Qed.

(* others do not get notified *)
Goal processLocalStepFunc (inl ([], RBox, emptyBox, {[1;2;3]}, true)) (AArrive 42 2 (SExit kill false))
     <> Some (inr {[ 1 := killed; 2 := killed; 3 := killed; 4 := killed]}).
Proof. discriminate. Qed.

(* everyone gets notified *)
Goal processLocalStepFunc (inl ([], RBox, emptyBox, {[1;2;3]}, true)) (AArrive 42 2 (SExit kill false))
     <> Some (inr ∅).
Proof. discriminate. Qed.

(* (flag = false /\ reason <> normal /\ reason' = reason /\ b = true /\ source ∈ links *)
Goal processLocalStepFunc (inl ([], RBox, emptyBox, {[1;2;3]}, false)) (AArrive 1 2 (SExit kill true))
     = Some (inr {[ 1 := kill; 2 := kill; 3 := kill]}).
Proof. reflexivity. Qed.

(* (flag = false /\ reason <> normal /\ reason' = reason /\ b = false /\ reason <> kill) *)
Goal processLocalStepFunc (inl ([], RBox, emptyBox, {[1;2;3]}, false)) (AArrive 42 2 (SExit killed false))
     = Some (inr {[ 1 := killed; 2 := killed; 3 := killed]}).
Proof. reflexivity. Qed.

(* (flag = false /\ reason <> normal /\ reason' = reason /\ source ∈ links /\ reason <> kill) *)
Goal forall b, processLocalStepFunc (inl ([], RBox, emptyBox, {[1;2;3]}, false)) (AArrive 1 2 (SExit killed b))
     = Some (inr {[ 1 := killed; 2 := killed; 3 := killed]}).
Proof. intros. destruct b; reflexivity. Qed.

(* p_exit_convert *)
(* (b = false /\ reason <> kill) *)
Goal processLocalStepFunc (inl ([], RBox, emptyBox, ∅, true)) (AArrive 42 2 (SExit normal false))
     = Some (inl ([], RBox, ([], [VTuple [EXIT; VPid 42; normal]]), ∅, true)).
Proof. reflexivity. Qed.

(* (b = true /\ source ∈ links) *)
Goal processLocalStepFunc (inl ([], RBox, emptyBox, {[42]}, true)) (AArrive 42 2 (SExit normal true))
     = Some (inl ([], RBox, ([], [VTuple [EXIT; VPid 42; normal]]), {[42]}, true)).
Proof. reflexivity. Qed.

(* p_link_arrived *)
(* p_link_arrived simple case *)
Goal processLocalStepFunc (inl ([], RBox, emptyBox, ∅, true)) (AArrive 42 2 SLink)
     = Some (inl ([], RBox, emptyBox, {[42]}, true)).
Proof. reflexivity. Qed.

(* p_link_arrived same link arrives *)
Goal processLocalStepFunc (inl ([], RBox, emptyBox, {[42]}, true)) (AArrive 42 2 SLink)
     = Some (inl ([], RBox, emptyBox, {[42]}, true)).
Proof. reflexivity. Qed.

(* p_link_arrived preserves things *)
Goal forall fs e mb flag, processLocalStepFunc (inl (fs, e, mb, ∅, flag)) (AArrive 42 2 SLink)
     = Some (inl (fs, e, mb, {[42]}, flag)).
Proof. reflexivity. Qed.

(* p_unlink_arrived *)
(* p_unlink_arrived simple case *)
Goal processLocalStepFunc (inl ([], RBox, emptyBox, {[42]}, true)) (AArrive 42 2 SUnlink)
     = Some (inl ([], RBox, emptyBox, ∅, true)).
Proof. reflexivity. Qed.

(* p_unlink_arrived simple case *)
Goal processLocalStepFunc (inl ([], RBox, emptyBox, {[42]}, true)) (AArrive 42 2 SUnlink)
     = Some (inl ([], RBox, emptyBox, ∅, true)).
Proof. reflexivity. Qed.

(* p_unlink_arrived nonexistant link *)
Goal processLocalStepFunc (inl ([], RBox, emptyBox, {[42]}, true)) (AArrive 1 2 SUnlink)
     = Some (inl ([], RBox, emptyBox, {[42]}, true)).
Proof. reflexivity. Qed.

(* p_unlink_arrived preserves things *)
Goal forall fs e mb flag, processLocalStepFunc (inl (fs, e, mb, ∅, flag)) (AArrive 42 2 SUnlink)
     = Some (inl (fs, e, mb, ∅, flag)).
Proof. reflexivity. Qed.

(** SIGNAL SENDING *)

(* p_send simple case *)
Goal processLocalStepFunc (inl ([FParams (ICall erlang send) [VPid 2] []], RValSeq [VNil], emptyBox, ∅, true)) (ASend 1 2 (SMessage VNil))
     = Some (inl ([], RValSeq [VNil], emptyBox, ∅, true)).
Proof. reflexivity. Qed.

(* p_send can't send wrong reason *)
Goal processLocalStepFunc (inl ([FParams (ICall erlang send) [VPid 2] []], RValSeq [VNil], emptyBox, ∅, true)) (ASend 1 2 (SMessage (VLit 0%Z)))
     = None.
Proof. reflexivity. Qed.

(* p_send correct with sending PIDs *)
Goal processLocalStepFunc (inl ([FParams (ICall erlang send) [VPid 2] []], RValSeq [VPid 420], emptyBox, ∅, true)) (ASend 1 2 (SMessage (VPid 420)))
     = Some (inl ([], RValSeq [VPid 420], emptyBox, ∅, true)).
Proof. reflexivity. Qed.

Goal processLocalStepFunc (inl ([FParams (ICall erlang send) [VPid 2] []], RValSeq [VPid 420], emptyBox, ∅, true)) (ASend 1 2 (SMessage (VPid 420)))
     <> Some (inl ([], RValSeq [VPid 42], emptyBox, ∅, true)).
Proof. discriminate. Qed.

(* p_send correct with sending closures *)
Goal processLocalStepFunc (inl ([FParams (ICall erlang send) [VPid 2] []], RValSeq [ex_Clos_1], emptyBox, ∅, true)) (ASend 1 2 (SMessage (ex_Clos_1)))
     = Some (inl ([], RValSeq [ex_Clos_1], emptyBox, ∅, true)).
Proof. reflexivity. Qed.

Goal processLocalStepFunc (inl ([FParams (ICall erlang send) [VPid 2] []], RValSeq [ex_Clos_1], emptyBox, ∅, true)) (ASend 1 2 (SMessage (ex_Clos_1)))
     <> Some (inl ([], RValSeq [ex_Clos_2], emptyBox, ∅, true)).
Proof. discriminate. Qed.

(* p_exit *)
Goal processLocalStepFunc (inl ([FParams (ICall erlang exit) [VPid 2] []], RValSeq [VNil], emptyBox, ∅, true)) (ASend 1 2 (SExit VNil false))
     = Some (inl ([], RValSeq [ttrue], emptyBox, ∅, true)).
Proof. reflexivity. Qed.

(* p_exit can't send wrong reason *)
Goal processLocalStepFunc (inl ([FParams (ICall erlang exit) [VPid 2] []], RValSeq [VNil], emptyBox, ∅, true)) (ASend 1 2 (SExit (VLit 0%Z) false))
     = None.
Proof. reflexivity. Qed.

(* p_link *)
Goal processLocalStepFunc (inl ([FParams (ICall erlang link) [] []], RValSeq [VPid 2], emptyBox, ∅, true)) (ASend 1 2 SLink)
     = Some (inl ([], RValSeq [ok], emptyBox, {[2]}, true)).
Proof. reflexivity. Qed.

(* p_link to already linked process *)
Goal processLocalStepFunc (inl ([FParams (ICall erlang link) [] []], RValSeq [VPid 2], emptyBox, {[2]}, true)) (ASend 1 2 SLink)
     = Some (inl ([], RValSeq [ok], emptyBox, {[2]}, true)).
Proof. reflexivity. Qed.

(* p_link can't link to wrong process *)
Goal processLocalStepFunc (inl ([FParams (ICall erlang link) [] []], RValSeq [VPid 2], emptyBox, ∅, true)) (ASend 1 3 SLink)
     = None.
Proof. reflexivity. Qed.

(* p_unlink *)
Goal processLocalStepFunc (inl ([FParams (ICall erlang unlink) [] []], RValSeq [VPid 2], emptyBox, {[2]}, true)) (ASend 1 2 SUnlink)
     = Some (inl ([], RValSeq [ok], emptyBox, ∅, true)).
Proof. reflexivity. Qed.

(* p_unlink from not linked process *)
Goal processLocalStepFunc (inl ([FParams (ICall erlang unlink) [] []], RValSeq [VPid 2], emptyBox, {[3]}, true)) (ASend 1 2 SUnlink)
     = Some (inl ([], RValSeq [ok], emptyBox, {[3]}, true)).
Proof. reflexivity. Qed.

(* p_unlink can't unlink from wrong process *)
Goal processLocalStepFunc (inl ([FParams (ICall erlang unlink) [] []], RValSeq [VPid 2], emptyBox, ∅, true)) (ASend 1 3 SUnlink)
     = None.
Proof. reflexivity. Qed.

(* p_dead *)
Goal processLocalStepFunc (inr {[ 1 := killed; 2 := normal; 3 := kill ]}) (ASend 1 2 (SExit normal true))
     = Some (inr {[1 := killed; 3 := kill]}).
Proof. reflexivity. Qed.

(* p_dead wrong reason *)
Goal processLocalStepFunc (inr {[ 1 := killed; 2 := normal; 3 := kill ]}) (ASend 1 2 (SExit kill true))
     = None.
Proof. reflexivity. Qed.

(* p_dead nonexistant linked process *)
Goal processLocalStepFunc (inr {[ 1 := killed; 2 := normal; 3 := kill ]}) (ASend 1 42 (SExit normal true))
     = None.
Proof. reflexivity. Qed.

(** SELF *)

(* p_self *)
Goal processLocalStepFunc (inl ([FParams (ICall erlang self) [] []], RBox, emptyBox, ∅, true)) (ASelf 420)
     = Some (inl ([], RValSeq [VPid 420], emptyBox, ∅, true)).
Proof. reflexivity. Qed.

(** SPAWNING *)

Definition ex_Cons_1 : Val :=
  VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) VNil)).

Definition ex_Clos_3 : Val :=
  VClos [] 1 3 (˝ VNil).

Definition ex_Clos_4 : Val :=
  VClos [] 1 4 (˝ VNil).

(* p_spawn simple case *)
Goal processLocalStepFunc (inl ([FParams (ICall erlang spawn) [ex_Clos_3] []], RValSeq [ex_Cons_1], emptyBox, ∅, true)) (ASpawn 42 ex_Clos_3 ex_Cons_1 false)
     = Some (inl ([], RValSeq [VPid 42], emptyBox, ∅, true)).
Proof. reflexivity. Qed.

(* p_spawn wrong number of args *)
Goal processLocalStepFunc (inl ([FParams (ICall erlang spawn) [ex_Clos_4] []], RValSeq [ex_Cons_1], emptyBox, ∅, true)) (ASpawn 42 ex_Clos_4 ex_Cons_1 false)
     = None.
Proof. reflexivity. Qed.

(* p_spawn_link simple case *)
Goal processLocalStepFunc (inl ([FParams (ICall erlang spawn_link) [ex_Clos_3] []], RValSeq [ex_Cons_1], emptyBox, ∅, true)) (ASpawn 42 ex_Clos_3 ex_Cons_1 true)
     = Some (inl ([], RValSeq [VPid 42], emptyBox, {[42]}, true)).
Proof. reflexivity. Qed.

(* p_spawn_link wrong number of args *)
Goal processLocalStepFunc (inl ([FParams (ICall erlang spawn_link) [ex_Clos_4] []], RValSeq [ex_Cons_1], emptyBox, ∅, true)) (ASpawn 42 ex_Clos_4 ex_Cons_1 true)
     = None.
Proof. reflexivity. Qed.

(** RECEIVING *)
Definition ex_msg : Val := VLit "you've got mail!"%string.
Definition ex_msg_2 : Val := VLit "you've got more mail!"%string.
Definition ex_msg_3 : Val := VLit "you've got even more mail!"%string.

(* p_recv_peek_message_ok *)
Goal processLocalStepFunc (inl ([FParams (IPrimOp "recv_peek_message") [] []], RBox, ([], [ex_msg]), ∅, true)) τ
     = Some (inl ([], RValSeq [ttrue; ex_msg], ([], [ex_msg]), ∅, true)).
Proof. reflexivity. Qed.

(* p_recv_peek_message_no_message *)
Goal processLocalStepFunc (inl ([FParams (IPrimOp "recv_peek_message") [] []], RBox, emptyBox, ∅, true)) ε
     = Some (inl ([], RValSeq [ffalse; ErrorVal], emptyBox, ∅, true)).
Proof. reflexivity. Qed.

(* p_recv_next *)
Goal processLocalStepFunc (inl ([FParams (IPrimOp "recv_next") [] []], RBox, ([], [ex_msg]), ∅, true)) τ
     = Some (inl ([], RValSeq [ok], ([ex_msg], []), ∅, true)).
Proof. reflexivity. Qed.

(* p_remove_message *)
Goal processLocalStepFunc (inl ([FParams (IPrimOp "remove_message") [] []], RBox, ([ex_msg_2], [ex_msg]), ∅, true)) τ
     = Some (inl ([], RValSeq [ok], ([], [ex_msg_2]), ∅, true)).
Proof. reflexivity. Qed.

(* p_remove_message doesn't work with empty unseen messages *)
Goal processLocalStepFunc (inl ([FParams (IPrimOp "remove_message") [] []], RBox, ([ex_msg], []), ∅, true)) τ
     = None.
Proof. reflexivity. Qed.

(* p_recv_wait_timeout_new_message *)
Goal processLocalStepFunc (inl ([FParams (IPrimOp "recv_wait_timeout") [] []], RValSeq [infinity], ([ex_msg], [ex_msg_2; ex_msg_3]), ∅, true)) τ
     = Some (inl ([], RValSeq [ffalse], ([ex_msg], [ex_msg_2; ex_msg_3]), ∅, true)).
Proof. reflexivity. Qed.

(* p_recv_wait_timeout_0 *)
Goal processLocalStepFunc (inl ([FParams (IPrimOp "recv_wait_timeout") [] []], RValSeq [VLit 0%Z], ([ex_msg], [ex_msg_2; ex_msg_3]), ∅, true)) τ
     = Some (inl ([], RValSeq [ttrue], ([ex_msg], [ex_msg_2; ex_msg_3]), ∅, true)).
Proof. reflexivity. Qed.

Print timeout_value.

(* p_recv_wait_timeout_invalid string *)
Goal processLocalStepFunc (inl ([FParams (IPrimOp "recv_wait_timeout") [] []], RValSeq [VLit "This is invalid"%string], ([ex_msg], [ex_msg_2; ex_msg_3]), ∅, true)) τ
     = Some (inl ([], RExc (Error, VLit "timeout_value"%string, VLit "This is invalid"%string), ([ex_msg], [ex_msg_2; ex_msg_3]), ∅, true)).
Proof. reflexivity. Qed.

(* p_recv_wait_timeout_invalid number *)
Goal processLocalStepFunc (inl ([FParams (IPrimOp "recv_wait_timeout") [] []], RValSeq [VLit 21%Z], ([ex_msg], [ex_msg_2; ex_msg_3]), ∅, true)) τ
     = Some (inl ([], RExc (Error, VLit "timeout_value"%string, VLit 21%Z), ([ex_msg], [ex_msg_2; ex_msg_3]), ∅, true)).
Proof. reflexivity. Qed.

(* p_recv_wait_timeout_invalid nonliteral *)
Goal processLocalStepFunc (inl ([FParams (IPrimOp "recv_wait_timeout") [] []], RValSeq [VNil], ([ex_msg], [ex_msg_2; ex_msg_3]), ∅, true)) τ
     = Some (inl ([], RExc (Error, VLit "timeout_value"%string, VNil), ([ex_msg], [ex_msg_2; ex_msg_3]), ∅, true)).
Proof. reflexivity. Qed.

(** PROCESS FLAG *)

(* p_set_flag with previous true flag, set to true *)
Goal processLocalStepFunc (inl ([FParams (ICall erlang process_flag) [VLit "trap_exit"%string] []], RValSeq [VLit (Atom "true"%string)], emptyBox, ∅, true)) ε
     = Some (inl ([], RValSeq [VLit "true"%string], emptyBox, ∅, true)).
Proof. reflexivity. Qed.

(* p_set_flag with previous false flag, set to true *)
Goal processLocalStepFunc (inl ([FParams (ICall erlang process_flag) [VLit "trap_exit"%string] []], RValSeq [VLit (Atom "true"%string)], emptyBox, ∅, false)) ε
     = Some (inl ([], RValSeq [VLit "false"%string], emptyBox, ∅, true)).
Proof. reflexivity. Qed.

(* p_set_flag with previous true flag, set to false *)
Goal processLocalStepFunc (inl ([FParams (ICall erlang process_flag) [VLit "trap_exit"%string] []], RValSeq [VLit (Atom "false"%string)], emptyBox, ∅, true)) ε
     = Some (inl ([], RValSeq [VLit "true"%string], emptyBox, ∅, false)).
Proof. reflexivity. Qed.

(* p_set_flag with previous false flag, set to false *)
Goal processLocalStepFunc (inl ([FParams (ICall erlang process_flag) [VLit "trap_exit"%string] []], RValSeq [VLit (Atom "false"%string)], emptyBox, ∅, false)) ε
     = Some (inl ([], RValSeq [VLit "false"%string], emptyBox, ∅, false)).
Proof. reflexivity. Qed.

(* p_set_flag_exc *)
Goal processLocalStepFunc (inl ([FParams (ICall erlang process_flag) [VLit "trap_exit"%string] []], RValSeq [VNil], emptyBox, ∅, true)) τ
     = Some (inl ([], RExc (Error, VLit "badarg"%string, VNil), emptyBox, ∅, true)).
Proof. reflexivity. Qed.

(** TERMINATION *)

(* p_terminate *)
Goal processLocalStepFunc (inl ([], RValSeq [VLit "42"%string], emptyBox, {[1;2;3]}, true)) ε
     = Some (inr {[ 1 := normal; 2 := normal; 3 := normal ]}).
Proof. reflexivity. Qed.

(** EXCEPTIONS *)

(* p_terminate_exc *)
Goal processLocalStepFunc (inl ([], RExc (Error, VLit "reason"%string, VLit "this is irrelevant"%string), emptyBox, {[1;2]}, true)) ε
     = Some (inr {[ 1 := VLit "reason"%string; 2 := VLit "reason"%string ]}).
Proof. reflexivity. Qed.