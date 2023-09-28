(* This part of the work is based on https://dl.acm.org/doi/10.1145/3123569.3123576 *)
From CoreErlang.FrameStack Require Export SubstSemantics.
Require Export Coq.Sorting.Permutation.
Require Export Coq.Classes.EquivDec.

Import ListNotations.

(* mailbox: [old msg₁, old msg₁, ...] ++ 
            current msg₁ :: [new msg₁, new msg₂, ...] *)
Definition Mailbox : Set := list Val * list Val.
Definition emptyBox : Mailbox := ([], []).
Definition ProcessFlag : Set := bool.
Definition LiveProcess : Set := FrameStack * Redex * Mailbox * (list PID) * ProcessFlag.
Definition DeadProcess : Set := list (PID * Val).
Definition Process : Set := LiveProcess + DeadProcess.

Inductive Signal : Set :=
| Message (e : Val)
| Exit (r : Val) (b : bool)
| Link
| Unlink.

Inductive Action : Set :=
| ASend (sender receiver : PID) (t : Signal)
(* | AReceive (t : Exp) *)
| AArrive (sender receiver : PID) (t : Signal)
| ASelf (ι : PID)
| ASpawn (ι : PID) (t1 t2 : Val)
| τ
| ATerminate
| ASetFlag.

Notation "x '.1'" := (fst x) (at level 20, left associativity).
Notation "x '.2'" := (snd x) (at level 20, left associativity).

Definition removeMessage (m : Mailbox) : option Mailbox :=
  match m with
  | (m1, msg :: m2) => Some (m1 ++ m2, [])
  | _ => None
  end.

(* in Core Erlang, this function returns a flag and a message, if there is
   a current message *)
Definition peekMessage (m : Mailbox) : option Val :=
  match m with
  | (m1, msg :: m2) => Some msg
  | _ => None
  end.

(* TODO: Check C implementation, how this exactly works *)
Definition recvNext (m : Mailbox) : Mailbox :=
  match m with
  | (m1, msg :: m2) => (m1 ++ [msg], m2)
  | (m1, [])        => (m1         , [])
  end.

Definition mailboxPush (m : Mailbox) (msg : Val) : Mailbox :=
  (m.1, m.2 ++ [msg]).

Arguments mailboxPush m msg /.

(* Since OTP 24.0, receive-s are syntactic sugars *)
Definition EReceive l e :=
  ELetRec [(0, 
     °ELet 2 (EPrimOp "recv_peek_message" [])
       (ECase (`VFunId (0, 0)) [
         ([PLit (Atom "true")], `ttrue, °ECase (`VVar 1) (l ++
           [([PVar], `ttrue, °ESeq (EPrimOp "recv_next" [])
                                 (EApp (`VFunId (3, 0)) [])
           )]));
         ([PLit (Atom "false")], `ttrue,
           °ELet 1 (EPrimOp "recv_wait_timeout" [])
              (ECase (`VVar 0)
                [([PLit (Atom "true")], `ttrue, e); (* TODO: timeout *)
                 ([PLit (Atom "false")], `ttrue, °EApp (`VFunId (3, 0)) [])
                ]
              )
         )
       ])
    )]
    (EApp (`VFunId (0, 0)) []).

(* Fixpoint find_clause (vs : list Val) (c : list (list Pat * Exp * Exp)) :
  option (Exp * Exp) :=
match c with
| [] => None
| (ps, g, e)::xs => match match_pattern_list ps vs with
                     | None => find_clause vs xs
                     | Some l => Some (g.[list_subst l idsubst],
                                       e.[list_subst l idsubst])
                    end
end.

Fixpoint receive (m : Mailbox) (c : list (list Pat * Exp * Exp)) : option (Exp * Exp) :=
match m with
| [] => None
| m::ms => match find_clause [m] c with (* NOTE: this is the point where
                                                 it is required that there
                                                 is only one pattern in the
                                                 clauses of receive *)
           | Some res => Some res
           | None => receive ms c
           end
end. *)

(*
  if a `receive` is evaluated:
  1) try the first message against the clauses
    a) if it matches one, evaluate its guard
    b) if the guard is true, go to step 2)
    c) if the guard is false, or the message did not match, save the message
       into a separate cell, then evaluate `receive` with step 1), second message
  2) remove the current message from the mailbox, re-build the mailbox with
     the first part retrieved from the separate cell, and the second is the
     current mailbox
*)

(* Definition pop (v : Val) (m : Mailbox) := removeFirst Exp_eq_dec v m.
Definition etherPop := removeFirst (prod_eqdec Nat.eq_dec Exp_eq_dec). *)

(* TODO: move this to Auxiliaries.v, and refactor eval_length *)
Fixpoint len (l : Val) : option nat :=
match l with
| VNil => Some 0
| VCons v1 v2 => match len v2 with
                 | Some n2 => Some (S n2)
                 | _ => None
                 end
| _ => None
end.

(* TODO: move this to Auxiliaries.v, and refactor eval_list_tuple *)
Fixpoint mk_list (l : Val) : option (list Val) :=
match l with
| VNil => Some []
| VCons v1 v2 => match mk_list v2 with
                 | Some l => Some (v1 :: l)
                 | _ => None
                 end
| _ => None
end.

Definition lit_from_bool (b : bool) : Val :=
match b with
| true => VLit "true"%string
| false => VLit "false"%string
end.
Definition bool_from_lit (e : Val) : option bool :=
match e with
| VLit (Atom x) =>
  if eqb x "true"%string
  then Some true
  else if eqb x "false"%string
       then Some false
       else None
| _ => None
end.

Reserved Notation "p -⌈ a ⌉-> p'" (at level 50).
(*
  Fredlund: https://www.diva-portal.org/smash/get/diva2:8988/FULLTEXT01.pdf
  - it is similar, kill rules on page 66 are quite similar to our exit rules, and both differ from doc.
*)
Inductive processLocalSemantics : Process -> Action -> Process -> Prop :=
(********** LOCAL STEPS **********)
| p_local fs e fs' e' mb links flag :
  ⟨fs, e⟩ --> ⟨fs', e'⟩
->
  inl (fs, e, mb, links, flag) -⌈ τ ⌉-> inl (fs', e', mb, links, flag)


(********** SIGNAL ARRIVAL **********)
(* message arrival *)
| p_arrive mb fs e v flag links source dest :
  inl (fs, e, mb, links, flag) -⌈ AArrive source dest (Message v) ⌉-> inl (fs, e, mailboxPush mb v, links, flag)

(* exiting actions should come here *)
(* dropping exit signals *)
| p_exit_drop fs e mb links flag dest source reason b :
  (
    reason = normal /\ dest <> source /\ flag = false \/
    ~ In source links /\ b = true /\ dest <> source
                                           (*    ^------------ TODO: this check is missing from doc? *)
  ) ->
  inl (fs, e, mb, links, flag) -⌈ AArrive source dest (Exit reason b) ⌉->
  inl (fs, e, mb, links, flag)
(* terminating process *)
| p_exit_terminate fs e mb links flag dest source reason reason' b :
  (reason = kill /\ b = false /\ reason' = killed) \/
  (flag = false /\ reason <> normal /\ reason' = reason /\ (b = true -> In source links) /\ 
  (b = false -> reason <> kill))
                  (*    ^------------ TODO: this check is missing from doc. *)
 \/
  (flag = false /\ reason = normal /\ source = dest /\ reason' = reason) ->
  (*    ^------------ TODO: this check is missing from doc. *)
  inl (fs, e, mb, links, flag) -⌈ AArrive source dest (Exit reason b) ⌉->
  inr (map (fun l => (l, reason')) links)
(* convert exit signal to message *)
(* TODO, NOTE: here tuple should be used instead of list! *)
| p_exit_convert fs e mb links dest source reason b:
  (b = false /\ reason <> kill) \/
  (b = true /\ In source links)
 ->
  inl (fs, e, mb, links, true) -⌈ AArrive source dest (Exit reason b) ⌉->
  inl (fs, e, mailboxPush mb (VCons EXIT 
                           (VCons (VPid source) (VCons reason VNil))), links, true)
(* link received *)
| p_link_arrived fs e mb links source dest flag:
  inl (fs, e, mb, links, flag) -⌈AArrive source dest Link⌉->
  inl (fs, e, mb, source :: links, flag)

(* unlink received *)
| p_unlink_arrived fs e mb links source dest flag :
  inl (fs, e, mb, links, flag) -⌈AArrive source dest Unlink⌉->
  inl (fs, e, mb, remove Nat.eq_dec source links, flag)

(********** SIGNAL SENDING **********)
(* message send *)
| p_send ι v mb fs flag links source :
  inl (FParams (ICall erlang send) [VPid ι] [] :: fs, RValSeq [v], mb, links, flag)
  -⌈ ASend source ι (Message v) ⌉-> inl (fs, RValSeq [v], mb, links, flag)
(* exit, 2 parameters *)
| p_exit fs v mb flag ι selfι links :
  inl (FParams (ICall erlang exit) [VPid ι] [] :: fs, RValSeq [v], mb, links, flag) -⌈ ASend selfι ι (Exit v false) ⌉->
  inl (fs, RValSeq [ttrue], mb, links, flag)
(* link *)
| p_link fs ι mb flag links selfι :
  inl (FParams (ICall erlang link) [] [] :: fs, RValSeq [VPid ι], mb, links, flag)
  -⌈ASend selfι ι Link⌉->
  inl (fs, RValSeq [ok], mb, ι :: links, flag)
(* unlink *)
| p_unlink fs ι mb flag links selfι :
  inl (FParams (ICall erlang unlink) [] [] :: fs, RValSeq [VPid ι], mb, links, flag) 
  -⌈ASend selfι ι Unlink⌉->
  inl (fs, RValSeq [ok], mb, remove Nat.eq_dec ι links, flag)
(* DEAD PROCESSES *)
| p_dead ι selfι links reason:
  inr ((ι, reason) :: links) -⌈ASend selfι ι (Exit reason true)⌉-> inr links


(********** SELF **********)
(* self *)
| p_self ι fs mb flag links :
  inl (FParams (ICall erlang self) [] [] :: fs, RBox, mb, links, flag) -⌈ ASelf ι ⌉-> inl (fs, RValSeq [VPid ι], mb, links, flag)

(********** SPAWN **********)
(* spawn *)
| p_spawn ι fs mb ext id vars e l flag links :
  Some vars = len l ->
  inl (FParams (ICall erlang spawn) [VClos ext id vars e] [] :: fs, RValSeq [l], mb, links, flag)
    -⌈ASpawn ι (VClos ext id vars e) l⌉-> inl (fs, RValSeq [VPid ι], mb, links, flag)

(********** RECEVIE **********)
| p_recv_peek_message fs mb msg links flag :
  peekMessage mb = Some msg ->
  inl (FParams (IPrimOp "recv_peek_message") [] [] :: fs, RBox, mb, links, flag) -⌈τ⌉->
    inl (fs, RValSeq [msg], mb, links, flag)

| p_recv_next fs mb links flag:
  inl (FParams (IPrimOp "recv_next") [] [] :: fs, RBox, mb, links, flag) -⌈τ⌉->
    inl (fs, RValSeq [ok], recvNext mb, links, flag) (* TODO: in Core Erlang, this result cannot be observed *)

| p_remove_message fs mb mb' links flag:
  removeMessage mb = Some mb' ->
  inl (FParams (IPrimOp "remove_message") [] [] :: fs, RBox, mb, links, flag) -⌈τ⌉->
    inl (fs, RValSeq [ok], mb', links, flag) (* TODO: in Core Erlang, this result cannot be observed *)

| p_recv_wait_timeout_new_message fs oldmb msg newmb links flag:
  (* There is a new message *)
  inl (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs, RValSeq [infinity], (oldmb, msg :: newmb), links, flag) -⌈τ⌉->
  inl (fs, RValSeq [ffalse], (oldmb, msg :: newmb), links, flag)

| p_recv_wait_timeout_0 fs mb links flag:
  (* 0 timeout is reached *)
  inl (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs, RValSeq [VLit 0%Z], mb, links, flag) -⌈τ⌉->
  inl (fs, RValSeq [ttrue], mb, links, flag)

| p_recv_wait_timeout_invalid fs mb links flag v:
  v <> VLit 0%Z -> v <> infinity ->
  inl (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs, RValSeq [v], mb, links, flag) -⌈τ⌉-> inl (fs, RExc (timeout_value v), mb, links, flag)

(********** PROCESS FLAG **********)
(* Replace process flags *)
| p_set_flag fs mb flag y v links :
  Some y = bool_from_lit v ->
  inl (FParams (ICall erlang process_flag) [] [] :: fs, RValSeq [v], mb, links, flag) 
   -⌈ ASetFlag ⌉-> inl (fs, RValSeq [lit_from_bool flag], mb, links, y)

(********** TERMINATION **********)
(* termination *)
| p_terminate v mb links flag:
  (* NOTE: "singletonness" is checked in compile time in Core Erlang *)
  inl ([], RValSeq [v], mb, links, flag) -⌈ATerminate⌉->
   inr (map (fun l => (l, normal)) links) (* NOTE: is internal enough here? - no, it's not for bisimulations *)

(* exit with one parameter <- this is sequential, it's in FrameStack/Auxiliaries.v *)

(********** EXCEPTIONS **********)
(* creation *)
| p_terminate_exc exc mb links flag:
  (* NOTE: if the final result is an exception, it's reason is sent
     to the linked processes *)
  inl ([], RExc exc, mb, links, flag) -⌈ATerminate⌉->
   inr (map (fun l => (l, exc.1.2)) links)

where "p -⌈ a ⌉-> p'" := (processLocalSemantics p a p').

Inductive LabelStar {A B : Type} (r : A -> B -> A -> Prop) : A -> list B -> A -> Prop :=
| lsrefl x : LabelStar r x [] x
| lsstep x l ls y z : r x l y -> LabelStar r y ls z -> LabelStar r x (l::ls) z.

Notation "x -⌈ xs ⌉->* y" := (LabelStar processLocalSemantics x xs y) (at level 50).

