(**
  This file defines the process-local semantics of Core Erlang. This involves
  the formalisation of processes, and how a process reacts to a concurrent
  action. This work is partially based on a related [formalisation in Isabelle](https://dl.acm.org/doi/10.1145/3123569.3123576).
*)
From CoreErlang Require Export StrictEqualities.
From CoreErlang.FrameStack Require Export SubstSemantics.
From CoreErlang.FrameStack Require Import SubstSemanticsLemmas.
From CoreErlang.Concurrent Require Export PIDRenaming.
Require Export Stdlib.Sorting.Permutation.
From stdpp Require Export option gmap.

Import ListNotations.
Import Notations.

(** Case-splits on the first `decide (x = y)` of the goal or of a
    hypothesis, and solves the contradictory branches with `congruence`.
    (The name `destruct_decide` is already taken by stdpp.) *)
Ltac destruct_decide_eq :=
  match goal with
  | [ |- context [ decide (?x = ?y) ] ] =>
      destruct (decide (x = y)); try congruence
  | [H : context [ decide (?x = ?y) ] |- _] =>
      destruct (decide (x = y)); try congruence
  end.

(** * Processes *)

(** Mailboxes consist of two parts: the messages that have already been
    checked by the current `receive`, and the unchecked ones, the first of
    which is the current message:
    `([old msg₁, old msg₂, ...], current msg :: [new msg₁, new msg₂, ...])` *)
Definition Mailbox : Set := list Val * list Val.

(** The empty mailbox *)
Definition emptyBox : Mailbox := ([], []).

(** The `trap_exit` flag of processes *)
Definition ProcessFlag : Set := bool.

(** Live processes: a frame stack, the redex under evaluation, the mailbox,
    the linked processes and the `trap_exit` flag. *)
Definition LiveProcess : Set := FrameStack * Redex * Mailbox * gset PID * ProcessFlag.

(** Equality of values is decidable (as an stdpp instance). *)
#[global] Instance Val_eq_decision : EqDecision Val.
Proof.
  pose proof Val_eq_dec.
  unfold EqDecision, Decision. apply H.
Defined.

#[global] Hint Resolve Val_eq_decision : core.

(** Dead processes: the exit reasons still to be sent to the linked
    processes. *)
Definition DeadProcess : Set := gmap PID Val.

(** Processes are either alive or dead. *)
Definition Process : Set := LiveProcess + DeadProcess.

(** Signals that processes can send to each other: messages, exit signals
    (the boolean flag is true if the signal is sent because of a link), and
    link and unlink requests. *)
Inductive Signal : Set :=
| SMessage (e : Val)
| SExit (r : Val) (b : bool)
| SLink
| SUnlink.

(** Equality of signals is decidable. *)
Theorem Signal_eq_dec (s s' : Signal) : {s = s'} + {s <> s'}.
Proof. decide equality; try apply Val_eq_dec; try apply Nat.eq_dec. decide equality. Qed.

(** The actions of processes: sending and receiving (arrival of) signals,
    querying the own PID, spawning a new process, and silent steps. *)
Inductive Action : Set :=
| ASend (sender receiver : PID) (t : Signal)
| AArrive (sender receiver : PID) (t : Signal)
| ASelf (ι : PID)
| ASpawn (ι : PID) (t1 t2 : Val) (link : bool)
| τ (** tau denotes strongly confluent actions of the semantics (these are silent steps and a few other reductions) *)
| ε (** epsilon is used for process-local silent operations (e.g., mailbox manipulation), which are NOT confluent *)
.

(** Equality of actions is decidable. *)
#[global] Instance Action_dec : EqDecision Action.
Proof.
  unfold EqDecision. intros. unfold Decision.
  decide equality; subst; auto.
  all: try apply Nat.eq_dec.
  all: try apply Val_eq_dec.
  all: decide equality.
  all: try apply Val_eq_dec.
  all: decide equality.
Defined.

(** * Mailbox operations *)

(** Removes the current message, and moves the already checked messages back
    to the unchecked part (used when a `receive` clause matched). *)
Definition removeMessage (m : Mailbox) : option Mailbox :=
  match m with
  | (m1, msg :: m2) => Some ([], m1 ++ m2)
  | _ => None
  end.

(** The current message, if there is one. *)
(* in Core Erlang, this function returns a flag and a message, if there is
   a current message *)
Definition peekMessage (m : Mailbox) : option Val :=
  match m with
  | (m1, msg :: m2) => Some msg
  | _ => None
  end.

(** Moves the current message to the already checked part (used when no
    `receive` clause matched the current message). *)
(* TODO: Check C implementation, how this exactly works *)
Definition recvNext (m : Mailbox) : option Mailbox :=
  match m with
  | (m1, msg :: m2) => Some (m1 ++ [msg], m2)
  | (m1, [])        => None
  end.

(** Appends a newly arrived message to the end of the mailbox. *)
Definition mailboxPush (m : Mailbox) (msg : Val) : Mailbox :=
  (m.1, m.2 ++ [msg]).

Arguments mailboxPush m msg /.

(** * `receive` as derived syntax *)

(** Renames the clauses of a case expression in the same way as [renameNonVal]
    does for [ECase]: the guards and bodies are renamed under the variables
    bound by the patterns. *)
Definition rename_clauses (ρ : Renaming) (l : list (list Pat * Exp * Exp))
  : list (list Pat * Exp * Exp) :=
  map (fun '(p, x, y) => (map (renamePat ρ) p,
                          rename (uprenn (PatListVars p) ρ) x,
                          rename (uprenn (PatListVars p) ρ) y)) l.

(** Since OTP 24.0, receive-s are syntactic sugars
   https://www.erlang.org/eeps/eep-0052

  `EReceive l t e` is `receive l after t -> e end`, where the clauses `l`, the
  timeout `t` and the after-body `e` are all written in the scope of the
  receive itself. The expansion binds 3 variables around the clauses and the
  timeout (the `ELetRec` and the `ELet`), and 4 around the after-body (+ the
  `ELet` of the timeout); these are not visible to the arguments, because the
  arguments are shifted over them.
*)
Definition EReceive l t e :=
  ELetRec [(0,
     °ELet 2 (EPrimOp "recv_peek_message" [])
       (ECase (˝VVar 0) [
         ([PLit (Atom "true")], ˝ttrue, °ECase (˝VVar 1) (
           map (fun '(pl, g, e) => (pl, g, °ESeq (EPrimOp "remove_message" []) e))
               (rename_clauses (Nat.add 3) l) ++
           [([PVar], ˝ttrue, °ESeq (EPrimOp "recv_next" [])
                                 (EApp (˝VFunId (3, 0)) [])
           )]));
         ([PLit (Atom "false")], ˝ttrue,
           °ELet 1 (EPrimOp "recv_wait_timeout" [rename (Nat.add 3) t])
              (ECase (˝VVar 0)
                [([PLit (Atom "true")], ˝ttrue, rename (Nat.add 4) e); (* TODO: timeout *)
                 ([PLit (Atom "false")], ˝ttrue, °EApp (˝VFunId (3, 0)) [])
                ]
              )
         )
       ])
    )]
    (EApp (˝VFunId (0, 0)) []).

(** The expansion of `receive` is well-scoped if its components are.

  If a `receive` is evaluated:
  1) try the first message against the clauses
    a) if it matches one, evaluate its guard
    b) if the guard is true, go to step 2)
    c) if the guard is false, or the message did not match, save the message
       into a separate cell, then evaluate ˝receive˝ with step 1), second message
  2) remove the current message from the mailbox, re-build the mailbox with
     the first part retrieved from the separate cell, and the second is the
     current mailbox
*)
Lemma EReceive_scope :
  forall l time r Γ,
  Forall (fun '(pl, g, e) =>
    Forall (PatScoped Γ) pl /\
    EXP PatListVars pl + Γ ⊢ g /\ EXP PatListVars pl + Γ ⊢ e) l ->
  EXP Γ ⊢ time ->
  EXP Γ ⊢ r ->
  EXP Γ ⊢ EReceive l time r.
Proof.
  intros l time r Γ Hl Ht Hr.
  (* first, the shifted arguments are scoped under the binders of the expansion *)
  pose proof ren_preserves_scope as [Hexp [_ [_ Hpat]]].
  assert (forall n, RENSCOPE Γ ⊢ Nat.add n ∷ n + Γ) as Hshift.
  { intros n x Hx. lia. }
  assert (Forall (fun '(pl, g, e) =>
    Forall (PatScoped (3 + Γ)) pl /\
    EXP PatListVars pl + (3 + Γ) ⊢ g /\ EXP PatListVars pl + (3 + Γ) ⊢ e)
    (rename_clauses (Nat.add 3) l)) as H.
  {
    unfold rename_clauses. rewrite Forall_map.
    eapply Forall_impl; [exact Hl|].
    intros [[pl g] e] (Hp & Hg & He). cbn.
    rewrite PatListVars_rename.
    split; [|split].
    - rewrite Forall_map. eapply Forall_impl; [exact Hp|].
      intros p Hp'. apply (proj1 (Hpat p Γ) Hp'), (Hshift 3).
    - apply (proj1 (Hexp g _) Hg). apply uprenn_scope, (Hshift 3).
    - apply (proj1 (Hexp e _) He). apply uprenn_scope, (Hshift 3).
  }
  assert (EXP 3 + Γ ⊢ rename (Nat.add 3) time) as H0.
  { apply (proj1 (Hexp time Γ) Ht), (Hshift 3). }
  assert (EXP 4 + Γ ⊢ rename (Nat.add 4) r) as H1.
  { apply (proj1 (Hexp r Γ) Hr), (Hshift 4). }
  (* then, the expansion itself is scoped *)
  unfold EReceive. revert H H0 H1.
  generalize (rename_clauses (Nat.add 3) l) (rename (Nat.add 3) time) (rename (Nat.add 4) r).
  clear l time r Hl Ht Hr Hexp Hpat Hshift.
  intros l time r H H0 H1.
  repeat scope_solver_step.
  1: scope_solver.
  1-3: lia.
  scope_solver.
  1, 5: lia.
  4: scope_solver.
  all: intros; simpl in *; rewrite length_app, length_map in H2; simpl in H2;
  assert (i < length l \/ i = length l) as X by lia; destruct X.
  (* guards *)
  {
    rewrite indexed_to_forall with (def := ([], ˝VNil, ˝VNil)) in H.
    apply H in H3 as H'.
    repeat rewrite map_app. repeat rewrite map_map. simpl.
    rewrite app_nth1. 2: by rewrite length_map.
    rewrite app_nth1. 2: by rewrite length_map.
    rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
    setoid_rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
    destruct nth, p. cbn. apply H'.
  }
  (* last guard *)
  {
    rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
    setoid_rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
    subst. erewrite <- length_map. rewrite nth_middle. cbn. scope_solver.
  }
  (* bodies *)
  {
    rewrite indexed_to_forall with (def := ([], ˝VNil, ˝VNil)) in H.
    apply H in H3 as H'.
    repeat rewrite map_app. repeat rewrite map_map. simpl.
    rewrite app_nth1. 2: by rewrite length_map.
    rewrite app_nth1. 2: by rewrite length_map.
    setoid_rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
    extract_map_fun F.
    assert (° ESeq (° EPrimOp "remove_message" []) (˝VNil) = F ([], ˝VNil, ˝VNil)). {
      by subst F.
    }
    erewrite (nth_indep (map F l) _ (° ESeq (° EPrimOp "remove_message" []) (˝ VNil))).
    rewrite H4. rewrite map_nth. subst F.
    destruct nth, p. cbn.
    do 2 scope_solver_step.
    1: scope_solver.
    1: apply H'.
    by rewrite length_map.
  }
  (* last body *)
  {
    rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
    setoid_rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
    subst. erewrite <- length_map. rewrite nth_middle. cbn. scope_solver.
  }
  (* patterns *)
  {
    rewrite map_app in H3 |- *.
    rewrite app_nth1 in H3; [|by rewrite !length_map].
    rewrite app_nth1; [|by rewrite !length_map].
    assert (HLP : Forall (Forall (PatScoped (3 + Γ)))
      (map (fst ∘ fst) (map (λ '(pl, g, e), (pl, g, ° ESeq (° EPrimOp "remove_message" []) e)) l))).
    { rewrite map_map, Forall_map. eapply Forall_impl; [exact H|].
      intros [[pl g] e] [Hp _]. cbn. exact Hp. }
    rewrite Forall_nth in HLP.
    pose proof (HLP i ltac:(rewrite !length_map; exact H4)) as HP.
    rewrite Forall_nth in HP.
    exact (HP j H3).
  }
  (* last pattern *)
  {
    rewrite map_app in H3 |- *.
    rewrite app_nth2 in H3; [|by rewrite !length_map; lia].
    rewrite app_nth2; [|by rewrite !length_map; lia].
    rewrite !length_map, H4, Nat.sub_diag in H3 |- *.
    cbn in *.
    destruct j; [apply scoped_pvar | lia].
  }
Qed.

(** * Process-local semantics *)

(** Converts a boolean to the corresponding atom. *)
Definition lit_from_bool (b : bool) : Val :=
match b with
| true => VLit "true"%string
| false => VLit "false"%string
end.

(** Converts the atoms `true` and `false` to booleans. *)
Definition bool_from_lit (e : Val) : option bool :=
match e with
| VLit (Atom x) =>
  if String.eqb x "true"%string
  then Some true
  else if String.eqb x "false"%string
       then Some false
       else None
| _ => None
end.

(** The exit reason sent to the linked processes of a process terminated by
    the uncaught exception `(class, reason, details)`. As in Erlang, the
    reasons of errors are paired with the stack trace, and the reasons of
    throws are also wrapped in `{nocatch, reason}`; the details of
    exceptions approximate the stack trace (see `Exception` in
    `Syntax.v`). *)
Definition make_exit_signal (exc : Exception) : Val :=
match exc with
| (Error, reason, details) => VTuple [reason; details]
| (Throw, reason, details) =>
    VTuple [VTuple [VLit "nocatch"%string; reason]; details]
| (Exit, reason, _) => reason
end.

Reserved Notation "p -⌈ a ⌉-> p'" (at level 50).
(*
  Fredlund: https://www.diva-portal.org/smash/get/diva2:8988/FULLTEXT01.pdf
  - it is similar, kill rules on page 66 are quite similar to our exit rules, and both differ from doc.
*)
(** `p -⌈ a ⌉-> p'`: the process `p` can take a step to `p'` with the action
    `a`. *)
Inductive processLocalStep : Process -> Action -> Process -> Prop :=
(********** LOCAL STEPS **********)
| p_local fs e fs' e' mb links flag :
  ⟨fs, e⟩ --> ⟨fs', e'⟩
->
  inl (fs, e, mb, links, flag) -⌈ τ ⌉-> inl (fs', e', mb, links, flag)

(********** SIGNAL ARRIVAL **********)
(* message arrival *)
| p_arrive mb fs e v flag links source dest :
  inl (fs, e, mb, links, flag) -⌈ AArrive source dest (SMessage v) ⌉-> inl (fs, e, mailboxPush mb v, links, flag)

(* exiting actions should come here *)
(* dropping exit signals *)
| p_exit_drop fs e mb links flag dest source reason b :
  (
    reason = normal /\ dest <> source /\ flag = false \/
    (source ∉ links) /\ b = true /\ dest <> source
                                           (*    ^------------ TODO: this check is missing from doc? *)
  ) ->
  inl (fs, e, mb, links, flag) -⌈ AArrive source dest (SExit reason b) ⌉->
  inl (fs, e, mb, links, flag)
(* terminating process *)
| p_exit_terminate fs e mb links flag dest source reason reason' b :
  (reason = kill /\ b = false /\ reason' = killed) \/
  (flag = false /\ reason <> normal /\ reason' = reason /\ (b = true -> source ∈ links) /\ 
  (b = false -> reason <> kill))
                  (*    ^------------ TODO: this check is missing from doc. *)
 \/
  (flag = false /\ reason = normal /\ source = dest /\ reason' = reason) ->
  (*    ^------------ TODO: this check is missing from doc. *)
  inl (fs, e, mb, links, flag) -⌈ AArrive source dest (SExit reason b) ⌉->
  inr (gset_to_gmap reason' links)
(* convert exit signal to message *)
| p_exit_convert fs e mb links dest source reason b:
  (b = false /\ reason <> kill) \/
  (b = true /\ source ∈ links)
 ->
  inl (fs, e, mb, links, true) -⌈ AArrive source dest (SExit reason b) ⌉->
  inl (fs, e, mailboxPush mb (VTuple [EXIT; VPid source; reason]), links, true)
(* link received *)
| p_link_arrived fs e mb links source dest flag:
  inl (fs, e, mb, links, flag) -⌈AArrive source dest SLink⌉->
  inl (fs, e, mb, {[source]} ∪ links, flag)

(* unlink received *)
| p_unlink_arrived fs e mb links source dest flag :
  inl (fs, e, mb, links, flag) -⌈AArrive source dest SUnlink⌉->
  inl (fs, e, mb, links ∖ {[source]}, flag)

(********** SIGNAL SENDING **********)
(* message send *)
| p_send ι v mb fs flag links source :
  inl (FParams (ICall erlang send) [VPid ι] [] :: fs, RValSeq [v], mb, links, flag)
  -⌈ ASend source ι (SMessage v) ⌉-> inl (fs, RValSeq [v], mb, links, flag)
(* exit, 2 parameters *)
| p_exit fs v mb flag ι selfι links :
  inl (FParams (ICall erlang exit) [VPid ι] [] :: fs, RValSeq [v], mb, links, flag) -⌈ ASend selfι ι (SExit v false) ⌉->
  inl (fs, RValSeq [ttrue], mb, links, flag)
(* link *)
| p_link fs ι mb flag links selfι :
  inl (FParams (ICall erlang link) [] [] :: fs, RValSeq [VPid ι], mb, links, flag)
  -⌈ASend selfι ι SLink⌉->
  inl (fs, RValSeq [ttrue], mb, {[ι]} ∪ links, flag)
(* unlink *)
| p_unlink fs ι mb flag links selfι :
  inl (FParams (ICall erlang unlink) [] [] :: fs, RValSeq [VPid ι], mb, links, flag) 
  -⌈ASend selfι ι SUnlink⌉->
  inl (fs, RValSeq [ttrue], mb, links ∖ {[ι]}, flag)
(* DEAD PROCESSES *)
| p_dead ι selfι links reason:
  links !! ι = Some reason ->
  inr links -⌈ASend selfι ι (SExit reason true)⌉-> inr (delete ι links)

(********** SELF **********)
(* self *)
| p_self ι fs mb flag links :
  inl (FParams (ICall erlang self) [] [] :: fs, RBox, mb, links, flag) -⌈ ASelf ι ⌉-> inl (fs, RValSeq [VPid ι], mb, links, flag)

(********** SPAWN **********)
(* spawn *)
| p_spawn ι fs mb ext id vars e l flag links :
  Some vars = len l ->
  inl (FParams (ICall erlang spawn) [VClos ext id vars e] [] :: fs, RValSeq [l], mb, links, flag)
    -⌈ASpawn ι (VClos ext id vars e) l false⌉-> inl (fs, RValSeq [VPid ι], mb, links, flag)

(* spawn_link *)
| p_spawn_link ι fs mb ext id vars e l flag links :
  Some vars = len l ->
  inl (FParams (ICall erlang spawn_link) [VClos ext id vars e] [] :: fs, RValSeq [l], mb, links, flag)
    -⌈ASpawn ι (VClos ext id vars e) l true⌉-> inl (fs, RValSeq [VPid ι], mb, {[ι]} ∪ links, flag)

(********** RECEIVE **********)
(* nonempty peeks are confluent, while empty peeks are not *)
| p_recv_peek_message_ok fs mb msg links flag :
  peekMessage mb = Some msg ->
  inl (FParams (IPrimOp "recv_peek_message") [] [] :: fs, RBox, mb, links, flag) -⌈τ⌉->
    inl (fs, RValSeq [ttrue;msg], mb, links, flag)

(* This action is not confluent with message arrival: *)
| p_recv_peek_message_no_message fs mb links flag :
  peekMessage mb = None ->
  inl (FParams (IPrimOp "recv_peek_message") [] [] :: fs, RBox, mb, links, flag) -⌈ε⌉->
    inl (fs, RValSeq [ffalse;ErrorVal], mb, links, flag) (* TODO: errorVal is probably not used here, but I could not find the behaviour *)

| p_recv_next fs mb links flag mb':
  recvNext mb = Some mb' ->
  inl (FParams (IPrimOp "recv_next") [] [] :: fs, RBox, mb, links, flag) -⌈ τ ⌉->
    inl (fs, RValSeq [ok], mb', links, flag) (* TODO: in Core Erlang, this result cannot be observed *)

(* This rule only works for nonempty mailboxes, thus it is confluent *)
| p_remove_message fs mb mb' links flag:
  removeMessage mb = Some mb' ->
  inl (FParams (IPrimOp "remove_message") [] [] :: fs, RBox, mb, links, flag) -⌈ τ ⌉->
    inl (fs, RValSeq [ok], mb', links, flag) (* TODO: in Core Erlang, this result cannot be observed *)

| p_recv_wait_timeout_new_message fs oldmb msg newmb links flag:
  (* There is a new message *)
  inl (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs, RValSeq [infinity], (oldmb, msg :: newmb), links, flag) -⌈τ⌉->
  inl (fs, RValSeq [ffalse], (oldmb, msg :: newmb), links, flag)

(* This rule is also confluent *)
| p_recv_wait_timeout_0 fs mb links flag:
  (* 0 timeout is reached *)
  inl (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs, RValSeq [VLit 0%Z], mb, links, flag) -⌈τ⌉->
  inl (fs, RValSeq [ttrue], mb, links, flag)

(* This rule is also confluent *)
(* NOTE: time is not modelled, thus finite, non-zero timeouts are not
   supported: they raise `timeout_value` too, while in Erlang, they are valid
   (e.g., `receive ... after 1000 -> ...`). *)
| p_recv_wait_timeout_invalid fs mb links flag v:
  v <> VLit 0%Z -> v <> infinity ->
  inl (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs, RValSeq [v], mb, links, flag) -⌈τ⌉-> inl (fs, RExc (timeout_value v), mb, links, flag)

(********** PROCESS FLAG **********)
(* Replace process flags *)
| p_set_flag fs mb flag y v links :
  Some y = bool_from_lit v ->
  inl (FParams (ICall erlang process_flag) [VLit "trap_exit"%string] [] :: fs, RValSeq [v], mb, links, flag) 
   -⌈ ε ⌉-> inl (fs, RValSeq [lit_from_bool flag], mb, links, y)

(* process flag exception *)
| p_set_flag_exc fs mb flag v links :
  None = bool_from_lit v ->
  inl (FParams (ICall erlang process_flag) [VLit "trap_exit"%string] [] :: fs, RValSeq [v], mb, links, flag) 
   -⌈ τ ⌉-> inl (fs, RExc (badarg v), mb, links, flag)

(********** TERMINATION **********)
(* termination *)
| p_terminate v mb links flag:
  (* NOTE: "singletonness" is checked in compile time in Core Erlang *)
  inl ([], RValSeq [v], mb, links, flag) -⌈ε⌉->
   inr (gset_to_gmap normal links)

(* exit with one parameter <- this is sequential, it's in FrameStack/Auxiliaries.v *)

(********** EXCEPTIONS **********)
(* creation *)
| p_terminate_exc exc mb links flag:
  (* NOTE: if the final result is an exception, its exit reason is sent
     to the linked processes *)
  inl ([], RExc exc, mb, links, flag) -⌈ε⌉->
   inr (gset_to_gmap (make_exit_signal exc) links)

where "p -⌈ a ⌉-> p'" := (processLocalStep p a p').

(** A peculiar exit: a `kill` exit signal sent through a link by a process
    which is not linked is dropped. *)
Local Example kill_from_unlinked_dropped :
  inl ([], RExp (˝VNil), emptyBox, ∅, false) -⌈AArrive 0 1 (SExit kill true)⌉->
  inl ([], RExp (˝VNil), emptyBox, ∅, false).
Proof.
  apply p_exit_drop.
  set_solver.
Qed.

(** `p -⌈ as ⌉->* p'`: the process `p` can take a sequence of steps with the
    actions `as` to `p'`. *)
Notation "x -⌈ xs ⌉->* y" := (LabelStar processLocalStep x xs y) (at level 50).

(** * PID renaming in processes and actions *)

(** This is needed to ensure that a process is not spawned with a wrong PID
    in the equivalence. *)
Definition spawnPIDOf (a : Action) : option PID :=
  match a with
  | ASpawn ι _ _ _ => Some ι
  | _ => None
  end.

(** This is needed for barbed bisimulations *)
Definition sendPIDOf (a : Action) : option PID :=
  match a with
  | ASend _ ι _ => Some ι
  | _ => None
  end.

(** The PIDs selected by `f` (e.g., `spawnPIDOf`) from the actions of a
    list of actions paired with the PIDs of the acting processes. *)
(* TODO: do this with Applicative/Monad *)
Definition PIDsOf (f : Action -> option PID) (l : list (Action * PID)) : list PID :=
  flat_map (fun a =>
    match f a.1 with
    | Some ι => [ι]
    | None => []
    end) l.

(** Renaming a single PID *)
Definition renamePIDPID (p p' : PID) := fun s => if s =? p
                                                 then p'
                                                 else s.

(** PID renaming in signals *)
Definition renamePIDSignal (p p' : PID) (s : Signal) : Signal :=
match s with
 | SMessage e => SMessage (renamePIDVal p p' e)
 | SExit r b => SExit (renamePIDVal p p' r) b
 | SLink => s
 | SUnlink => s
end.

(** The PIDs used in signals *)
Definition usedPIDsSignal (s : Signal) : gset PID :=
match s with
 | SMessage e => usedPIDsVal e
 | SExit r b => usedPIDsVal r
 | SLink => ∅
 | SUnlink => ∅
end.

(** Notation for PID renaming in signals *)
Notation "e .ₛ[ x ↦ y ]" := (renamePIDSignal x y e) (at level 1).

(** Renaming a PID that does not occur in a signal leaves the signal
    unchanged. *)
Corollary isNotUsed_renamePID_sig :
  forall s from to, from ∉ (usedPIDsSignal s) -> renamePIDSignal from to s = s.
Proof.
  intros. destruct s; try reflexivity; simpl.
  * now rewrite isNotUsed_renamePID_val.
  * now rewrite isNotUsed_renamePID_val.
Qed.

(** Renaming the PID `from` to `to` and then back restores a signal in which `to`
    does not occur. *)
Corollary double_renamePID_sig :
  forall s from to, to ∉ (usedPIDsSignal s) -> renamePIDSignal to from (renamePIDSignal from to s) = s.
Proof.
  intros. destruct s; try reflexivity; simpl.
  * now rewrite double_renamePID_val.
  * now rewrite double_renamePID_val.
Qed.

(** Processes are compared by Leibniz equality (as an stdpp instance). *)
#[global] Instance Process_equiv : Equiv Process := eq.

(** The equivalence of processes is Leibniz equality. *)
#[global] Instance Process_leibniz : LeibnizEquiv Process.
Proof.
  intros x y H. exact H.
Defined.

(** PID renaming in mailboxes *)
Definition renamePIDMb (p p' : PID) (mb : Mailbox) : Mailbox :=
  (map (renamePIDVal p p') mb.1, map (renamePIDVal p p') mb.2).

(** Swaps the PIDs `p` and `p'`; it is used to rename the keys of dead
    processes, since PID renaming has to be injective there. *)
Definition renamePIDPID_sym (p p' : PID) := fun s => if s =? p
                                                     then p'
                                                     else if s =? p'
                                                      (* This part is needed
                                                         for Inj eq eq *)
                                                          then p
                                                          else s.

(** Swapping PIDs is injective. *)
#[global] Instance renamePIDPID_sym_Inj p p' : Inj eq eq (renamePIDPID_sym p p').
Proof.
  unfold Inj. intros. unfold renamePIDPID_sym in H.
  repeat case_match; eqb_to_eq; subst; auto; try congruence.
Defined.

#[global] Hint Resolve renamePIDPID_sym_Inj : core.
#[global] Hint Resolve prod_map_inj : core.
#[global] Hint Resolve id_inj : core.

(** PID renaming in processes: in live processes, the PID is renamed in all
    components; in dead processes, the keys (linked PIDs) are swapped, and
    the PID is renamed in the exit reasons. *)
Definition renamePIDProc (p p' : PID) (pr : Process) : Process :=
match pr with
| inl (fs, r, mb, links, flag) =>
  inl (renamePIDStack p p' fs, renamePIDRed p p' r,
       renamePIDMb p p' mb,
       set_map (renamePIDPID p p') links, flag)
| inr dpr => inr (kmap (renamePIDPID_sym p p') (fmap (renamePIDVal p p') dpr))
end.

(** The PIDs used in processes: in dead processes, both the linked PIDs and
    the PIDs of the exit reasons count. *)
Definition usedPIDsProc (p : Process) : gset PID :=
match p with
| inl (fs, r, mb, links, flag) =>
    usedPIDsStack fs ∪
    usedPIDsRed r ∪
    links ∪
    flat_union usedPIDsVal mb.1 ∪
    flat_union usedPIDsVal mb.2
| inr links => (* should links should be considered? - Definitely *)
    (* map_fold (fun k x acc => {[k]} ∪ usedPIDsVal x ∪ acc) ∅ links <- simple, but no support with theorems *)
    @union_set _ _ _ gsetPID_elem_of _ (map_to_set (fun k x => {[k]} ∪ usedPIDsVal x) links)
end.

(** Case-splits on the PID equalities of `renamePIDPID` (`_sym`) in the goal
    or in a hypothesis. *)
Ltac renamePIDPID_case_match :=
  unfold renamePIDPID; repeat case_match; eqb_to_eq; subst; try lia.
Ltac renamePIDPID_case_match_hyp H :=
  unfold renamePIDPID in H; repeat case_match; eqb_to_eq; subst; try lia.
Ltac renamePIDPID_sym_case_match :=
  unfold renamePIDPID_sym; repeat case_match; eqb_to_eq; subst; try lia.
Ltac renamePIDPID_sym_case_match_hyp H :=
  unfold renamePIDPID_sym in H; repeat case_match; eqb_to_eq; subst; try lia.

(** Renaming a PID that does not occur in a process leaves the process
    unchanged; for dead processes, the new PID must not occur either, since
    their keys are swapped. *)
Corollary isNotUsed_renamePID_proc :
  forall p from to, from ∉ (usedPIDsProc p) ->
    to ∉ usedPIDsProc p -> (* needed for dead processes *)
    renamePIDProc from to p = p.
Proof.
  intros * H Hdead. destruct p; simpl.
  * destruct l, p, p, p, m. simpl.
    simpl in H. repeat apply not_elem_of_union in H as [H ?].
    rewrite not_elem_of_flat_union in *.
    rewrite isNotUsed_renamePID_red, isNotUsed_renamePID_stack; auto.
    repeat f_equal.
    1: unfold renamePIDMb; simpl; f_equal.
    1-2: rewrite <- map_id; apply map_ext_in; intros; simpl.
    1-2: rewrite isNotUsed_renamePID_val; apply list_elem_of_In in H4; set_solver.
    apply set_eq; split; intros.
    - apply elem_of_map in H4; destruct_hyps.
      unfold renamePIDPID in H4; renamePIDPID_case_match_hyp H4.
      congruence. assumption.
    - apply elem_of_map. destruct (decide (x = from)).
      + congruence.
      + exists x. split. by renamePIDPID_case_match. assumption.
  * f_equal.
    apply map_eq. intros.
    (* TODO: Lot of boiler plate, since stdpp is not quite easily extensible with
       helper lemmas :(  *)
    destruct (decide (i = from)). 2: destruct (decide (i = to)).
    - subst.
      replace from with (renamePIDPID_sym from to to) at 1 by  renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      setoid_rewrite lookup_fmap. simpl in *.
      destruct (d !! to) eqn:P1. 2: destruct (d !! from) eqn:P2.
      3: by setoid_rewrite P1; setoid_rewrite P2.
      + exfalso. apply Hdead.
        unfold union_set in *. apply elem_of_union_list.
        exists ({[to]} ∪ usedPIDsVal v). split. 2: set_solver.
        apply elem_of_elements. apply elem_of_map_to_set.
        do 2 eexists. split. exact P1. reflexivity.
      + exfalso. apply H.
        unfold union_set in *. apply elem_of_union_list.
        exists ({[from]} ∪ usedPIDsVal v). split. 2: set_solver.
        apply elem_of_elements. apply elem_of_map_to_set.
        do 2 eexists. split. exact P2. reflexivity.
    - subst.
      replace to with (renamePIDPID_sym from to from) at 1 by  renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      setoid_rewrite lookup_fmap. simpl in *.
      destruct (d !! to) eqn:P1. 2: destruct (d !! from) eqn:P2.
      3: by setoid_rewrite P1; setoid_rewrite P2.
      + exfalso. apply Hdead.
        unfold union_set in *. apply elem_of_union_list.
        exists ({[to]} ∪ usedPIDsVal v). split. 2: set_solver.
        apply elem_of_elements. apply elem_of_map_to_set.
        do 2 eexists. split. exact P1. reflexivity.
      + exfalso. apply H.
        unfold union_set in *. apply elem_of_union_list.
        exists ({[from]} ∪ usedPIDsVal v). split. 2: set_solver.
        apply elem_of_elements. apply elem_of_map_to_set.
        do 2 eexists. split. exact P2. reflexivity.
    - replace i with (renamePIDPID_sym from to i) at 1 by  renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      setoid_rewrite lookup_fmap. simpl in *.
      destruct (d !! i) eqn:P.
      2: by setoid_rewrite P.
      setoid_rewrite P. simpl. f_equal.
      rewrite isNotUsed_renamePID_val; auto.
      intro. apply H.
      unfold union_set in *. apply elem_of_union_list.
      exists ({[i]} ∪ usedPIDsVal v). split. 2: set_solver.
      apply elem_of_elements. apply elem_of_map_to_set.
      do 2 eexists. split. exact P. reflexivity.
Qed.

(** Renaming the PID `from` to `to` and then back restores a process in which `to`
    does not occur. *)
Corollary double_renamePID_proc :
  forall p from to, to ∉ (usedPIDsProc p) -> renamePIDProc to from (renamePIDProc from to p) = p.
Proof.
  intros. destruct p; simpl.
  * destruct l, p, p, p, m. simpl.
    simpl in H. repeat apply not_elem_of_union in H as [H ?].
    rewrite not_elem_of_flat_union in H0, H1.
    rewrite double_renamePID_red, double_renamePID_stack; auto.
    repeat f_equal.
    1: unfold renamePIDMb; simpl; f_equal.
    1-2: rewrite map_map, <- map_id; apply map_ext_in; intros; simpl.
    1-2: rewrite double_renamePID_val; apply list_elem_of_In in H4; set_solver.
    apply set_eq; split; intros.
    - apply elem_of_map in H4; destruct_hyps.
      apply elem_of_map in H5; destruct_hyps.
      unfold renamePIDPID in H4, H5; renamePIDPID_case_match_hyp H4; auto.
      congruence.
    - apply elem_of_map. destruct (decide (x = from)).
      + exists to. split. by renamePIDPID_case_match.
        apply elem_of_map. exists from. split. by renamePIDPID_case_match. by subst.
      + exists x. split. by renamePIDPID_case_match.
        apply elem_of_map. exists x. split. by renamePIDPID_case_match. assumption.
  * f_equal.
    apply map_eq. intros.
    (* TODO: Lot of boiler plate, since stdpp is not quite easily extensible with
       helper lemmas :(  *)
    destruct (decide (i = from)). 2: destruct (decide (i = to)).
    - subst.
      replace from with (renamePIDPID_sym to from to) at 1 by  renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      setoid_rewrite lookup_fmap. simpl in *.
      replace to with (renamePIDPID_sym from to from) at 2 by  renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      setoid_rewrite lookup_fmap. simpl in *.
      destruct (d !! from) eqn:P.
      2: by setoid_rewrite P.
      setoid_rewrite P. simpl.
      rewrite double_renamePID_val. reflexivity.
      intro. apply H.
      unfold union_set in *. apply elem_of_union_list.
      exists ({[from]} ∪ usedPIDsVal v). split. 2: set_solver.
      apply elem_of_elements. apply elem_of_map_to_set.
      do 2 eexists. split. exact P. reflexivity.
    - subst.
      replace to with (renamePIDPID_sym to from from) at 1 by  renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      setoid_rewrite lookup_fmap. simpl in *.
      replace from with (renamePIDPID_sym from to to) at 2 by  renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      setoid_rewrite lookup_fmap. simpl in *.
      destruct (d !! to) eqn:P.
      2: by setoid_rewrite P.
      setoid_rewrite P. simpl.
      rewrite double_renamePID_val. reflexivity.
      intro. apply H.
      unfold union_set in *. apply elem_of_union_list.
      exists ({[to]} ∪ usedPIDsVal v). split. 2: set_solver.
      apply elem_of_elements. apply elem_of_map_to_set.
      do 2 eexists. split. exact P. reflexivity.
    - subst.
      replace i with (renamePIDPID_sym to from i) at 1 by  renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      setoid_rewrite lookup_fmap. simpl in *.
      replace i with (renamePIDPID_sym from to i) at 1 by  renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      setoid_rewrite lookup_fmap. simpl in *.
      destruct (d !! i) eqn:P.
      2: by setoid_rewrite P.
      setoid_rewrite P. simpl.
      rewrite double_renamePID_val. reflexivity.
      intro. apply H.
      unfold union_set in *. apply elem_of_union_list.
      exists ({[i]} ∪ usedPIDsVal v). split. 2: set_solver.
      apply elem_of_elements. apply elem_of_map_to_set.
      do 2 eexists. split. exact P. reflexivity.
Qed.

(** Notation for PID renaming in processes *)
Notation "e .ₚ⟦ x ↦ y ⟧" := (renamePIDProc x y e) (at level 1).

(** PID renaming in actions *)
Definition renamePIDAct (from to : PID) (a : Action) : Action :=
  match a with
  | ASend sender receiver t =>
    ASend (renamePIDPID from to sender) (renamePIDPID from to receiver) (renamePIDSignal from to t)
  | AArrive sender receiver t =>
    AArrive (renamePIDPID from to sender) (renamePIDPID from to receiver) (renamePIDSignal from to t)
  | ASelf ι => ASelf (renamePIDPID from to ι)
  | ASpawn ι t1 t2 lin =>
    ASpawn (renamePIDPID from to ι) (renamePIDVal from to t1) (renamePIDVal from to t2) lin
  | x => x
  end.

(** Notation for PID renaming in actions *)
Notation "e .ₐ⟦ x ↦ y ⟧" := (renamePIDAct x y e) (at level 1).

(** PID renaming commutes with pushing a message into a mailbox. *)
Lemma mailboxPush_renamePID :
  forall mb v from to, 
         renamePIDMb from to (mailboxPush mb v) =
         mailboxPush (renamePIDMb from to mb) (renamePIDVal from to v).
Proof.
  intros.
  unfold renamePIDMb, mailboxPush; simpl.
  destruct mb; simpl.
  rewrite map_app. now simpl.
Qed.

(** The PIDs used in actions *)
Definition usedPIDsAct (a : Action) : gset PID :=
match a with
 | ASend sender receiver t => {[sender]} ∪ {[receiver]} ∪ usedPIDsSignal t
 | AArrive sender receiver t => {[sender]} ∪ {[receiver]} ∪ usedPIDsSignal t
 | ASelf ι => {[ι]}
 | ASpawn ι t1 t2 _ => {[ι]} ∪ usedPIDsVal t1 ∪ usedPIDsVal t2
 | _ => ∅
end.

(** Renaming the PIDs of a list commutes with removing a PID from it, if the
    new PID does not occur in the list. *)
Lemma map_renamePIDPID_remove :
  forall l x from to,
    to ∉ l ->
    x <> to ->
    map (renamePIDPID from to) (remove Nat.eq_dec x l) = remove Nat.eq_dec (renamePIDPID from to x) (map (renamePIDPID from to) l).
Proof.
  induction l; intros; simpl; try reflexivity.
  apply not_elem_of_cons in H as [H_1 H_2].
  unfold renamePIDPID at 2 3.
  destruct Nat.eq_dec.
  - subst. break_match_goal.
    + now apply IHl.
    + congruence.
  - break_match_goal.
    + do 2 break_match_hyp; eqb_to_eq; subst; try congruence.
    + do 2 break_match_hyp; eqb_to_eq; subst; try congruence.
      -- simpl; rewrite IHl; now auto.
      -- simpl; rewrite IHl; now auto.
      -- simpl; rewrite IHl; now auto.
Qed.

(** PID renaming does not change the length of a Core Erlang list. *)
Lemma len_renamePID :
  forall l from to, len l.⟦from ↦ to⟧ᵥ = len l.
Proof.
  valinduction; intros; simpl; try reflexivity.
  * now break_match_goal.
  * now rewrite IHl2.
  * constructor.
  * constructor; auto.
  * constructor.
  * constructor; auto.
Qed.

(** The current message of a renamed mailbox is the renamed current
    message. *)
Lemma peekMessage_renamePID :
  forall mb from to,
    peekMessage (renamePIDMb from to mb) = fmap (renamePIDVal from to) (peekMessage mb).
Proof.
  destruct mb. intros. simpl.
  now destruct l0.
Qed.

(** PID renaming commutes with `recvNext`. *)
Lemma recvNext_renamePID :
  forall mb from to,
    option_map (renamePIDMb from to) (recvNext mb) = recvNext (renamePIDMb from to mb).
Proof.
  destruct mb. intros. simpl. destruct l0; try reflexivity.
  cbn. unfold renamePIDMb. simpl. f_equal.
  simpl. by rewrite map_app.
Qed.

(** PID renaming commutes with `removeMessage`. *)
Lemma removeMessage_renamePID :
  forall mb from to,
    removeMessage (renamePIDMb from to mb) = fmap (renamePIDMb from to) (removeMessage mb).
Proof.
  destruct mb. intros. simpl. destruct l0; try reflexivity.
  simpl. f_equal. unfold renamePIDMb. simpl.
  f_equal. now rewrite map_app.
Qed.

(** Renaming the PID `a` to `b` maps `a` to `b`. *)
Lemma renamePIDPID_1 :
  forall a b, renamePIDPID a b a = b.
Proof.
  unfold renamePIDPID. intros. by rewrite Nat.eqb_refl.
Qed.

(** Swapping `a` and `b` maps `a` to `b`. *)
Lemma renamePIDPID_sym_1 :
  forall a b, renamePIDPID_sym a b a = b.
Proof.
  unfold renamePIDPID_sym. intros. by rewrite Nat.eqb_refl.
Qed.

(** Swapping `from` and `to` agrees with renaming the PID `from` to `to` on PIDs
    different from `to`. *)
Lemma renamePIDPID_sym_neq :
  forall from to ι,
  ι <> to ->
  renamePIDPID_sym from to ι = renamePIDPID from to ι.
Proof.
  unfold renamePIDPID_sym, renamePIDPID. intros.
  case_match; auto. case_match; auto.
  eqb_to_eq; congruence.
Qed.

(** PID renaming commutes with computing the exit reason of an exception. *)
Lemma renamePID_make_exit_signal :
  forall c r d from to,
    (make_exit_signal (c, r, d)).⟦from ↦ to⟧ᵥ =
    make_exit_signal (c, r.⟦from ↦ to⟧ᵥ, d.⟦from ↦ to⟧ᵥ).
Proof.
  destruct c; reflexivity.
Qed.

Opaque mailboxPush.
(** The process-local steps are preserved by renaming to a fresh PID (i.e.,
    one which is used neither by the process, nor by the action). *)
Theorem renamePID_is_preserved_local :
  forall p p' a, p -⌈a⌉-> p' ->
    forall from to,
      to ∉ (usedPIDsAct a) ->
      to ∉ (usedPIDsProc p) ->
      renamePIDProc from to p -⌈renamePIDAct from to a⌉->
      renamePIDProc from to p'.
Proof.
  intros. inv H.
  all: try now simpl; constructor.
  * apply renamePID_is_preserved with (from := from) (to := to) in H2.
    simpl. destruct mb. now constructor.
  * simpl. rewrite mailboxPush_renamePID.
    constructor.
  * simpl. constructor. destruct_or!; destruct_and!; subst; simpl in *.
    - left. split; auto. split; auto.
      unfold renamePIDPID. repeat break_match_goal; eqb_to_eq; subst; try lia.
      1-2: set_solver.
    - right. split; auto. 2: split; auto.
      + intro.
        apply elem_of_map in H2 as [x [P_1 P_2]].
        unfold renamePIDPID in P_1. repeat break_match_hyp; eqb_to_eq; subst.
        ** contradiction.
        ** repeat apply not_elem_of_union in H1 as [H1 ?]. set_solver.
        ** repeat apply not_elem_of_union in H1 as [H1 ?]. set_solver.
        ** contradiction.
      + unfold renamePIDPID. repeat break_match_goal; eqb_to_eq; subst; set_solver.
  * simpl.
    replace (inr _) with
        (inr (gset_to_gmap (reason'.⟦ from ↦ to ⟧ᵥ) ((set_map (renamePIDPID from to) links) : gset PID)) : Process).
    2: {
      assert (to ∉ links) by set_solver.
      assert (to ∉ usedPIDsVal reason) by set_solver.
      clear -H H3.
      f_equal. apply map_eq. intros.
      rewrite lookup_gset_to_gmap. unfold guard. case_match; simpl.
      * clear H0. apply elem_of_map in e; destruct_hyps.
        subst. rewrite <- renamePIDPID_sym_neq by set_solver.
        setoid_rewrite lookup_kmap; auto.
        setoid_rewrite lookup_fmap.
        rewrite lookup_gset_to_gmap. simpl.
        unfold guard. case_match. 2: { clear H0. set_solver. }
        reflexivity.
      * clear H0.
        destruct (decide (i = from)). 2: destruct (decide (i = to)).
        - subst.
          replace from with (renamePIDPID_sym from to to) at 1 by renamePIDPID_sym_case_match.
          setoid_rewrite lookup_kmap; auto.
          setoid_rewrite lookup_fmap.
          rewrite lookup_gset_to_gmap. simpl.
          unfold guard. case_match. 2: { clear H0. set_solver. }
          by clear H0.
        - subst.
          replace to with (renamePIDPID_sym from to from) at 1 by renamePIDPID_sym_case_match.
          setoid_rewrite lookup_kmap; auto.
          setoid_rewrite lookup_fmap.
          rewrite lookup_gset_to_gmap. simpl.
          unfold guard. case_match. 2: { clear H0. set_solver. }
          clear H0. exfalso. apply n. apply elem_of_map. exists from.
          split. by renamePIDPID_case_match. assumption.
        - assert (i ∉ links). {
            intro. apply n. apply elem_of_map. exists i.
            split. renamePIDPID_case_match. assumption.
          }
          replace i with (renamePIDPID_sym from to i) at 1 by
            renamePIDPID_sym_case_match.
          setoid_rewrite lookup_kmap; auto.
          setoid_rewrite lookup_fmap.
          rewrite lookup_gset_to_gmap. simpl.
          unfold guard. case_match. 2: { clear H1. set_solver. }
          by clear H1.
    }
    constructor. destruct_or!; destruct_and!; subst.
    - left. now split; auto.
    - right. left. repeat (split; auto).
      + intro. simpl in *.
        destruct reason; simpl in *; try congruence.
        break_match_hyp; congruence.
      + intro. apply H4 in H.
        apply elem_of_map. exists source. split; auto.
      + intro. apply H6 in H.
        clear -H. intro; destruct reason; simpl in *; try congruence.
        break_match_hyp; congruence.
    - right. right. now split; auto.
  * simpl. rewrite mailboxPush_renamePID. simpl.
    pose proof (p_exit_convert (renamePIDStack from to fs) (e .⟦ from ↦ to ⟧ᵣ)
       (renamePIDMb from to mb) (set_map (renamePIDPID from to) links) (renamePIDPID from to dest) (renamePIDPID from to source) (reason .⟦ from ↦ to ⟧ᵥ) b).
    (* TODO: boiler plate code: *)
    destruct (from =? source) eqn:P.
    - unfold renamePIDPID in H at 6. rewrite Nat.eqb_sym in P. rewrite P in H.
      apply H. destruct_or!; destruct_and!.
      + left; split; auto. clear -H4. intro.
        destruct reason; simpl in *; try congruence.
        break_match_hyp; congruence.
      + right; split; auto. clear -H4.
        apply elem_of_map. exists source. split; auto.
    - unfold renamePIDPID in H at 6. rewrite Nat.eqb_sym in P. rewrite P in H.
      apply H. destruct_or!; destruct_and!.
      + left; split; auto. clear -H4. intro.
        destruct reason; simpl in *; try congruence.
        break_match_hyp; congruence.
      + right; split; auto. clear -H4.
        apply elem_of_map. exists source. split; auto.
  * simpl in *. repeat apply not_in_union in H1 as [H1 ?].
    replace (set_map (renamePIDPID from to) ({[source]} ∪ links)) with
      ({[renamePIDPID from to source]} ∪ set_map (renamePIDPID from to) links : gset PID) by (clear; set_solver).
    constructor.
  * simpl in *.
    unfold set_map at 2. (* Why does replace not work without unfolding?? *)
    (* TODO: extract it somehow to a separate theorem about set_map and ∖ - couldn't do it because of the tangled typeclasses *)
    replace (list_to_set (renamePIDPID from to <$> elements (links ∖ {[source]})))
      with ((set_map (renamePIDPID from to) links ∖ {[renamePIDPID from to source]}) : gset PID).
    2: {
      apply set_eq. split; intros.
      * apply elem_of_difference in H as [H ?].
        apply elem_of_map in H. destruct_hyps. subst.
        destruct (decide (x0 = source)). set_solver.
        assert (x0 ≠ to) by set_solver.
        destruct (decide (x0 = from)).
        - subst. renamePIDPID_case_match. renamePIDPID_case_match_hyp H2.
          apply elem_of_map. exists from. rewrite Nat.eqb_refl. set_solver.
        - renamePIDPID_case_match. renamePIDPID_case_match_hyp H2.
          apply elem_of_map. exists x0. case_match; eqb_to_eq; set_solver.
          apply elem_of_map. exists x0. case_match; eqb_to_eq; set_solver.
      * apply elem_of_map in H. destruct_hyps. subst.
        assert (x0 ≠ to) by set_solver.
        destruct (decide (x0 = from)).
        - subst. renamePIDPID_case_match. set_solver.
          apply elem_of_difference. split. 2: set_solver.
          apply elem_of_map. exists from. rewrite Nat.eqb_refl. split. reflexivity.
          set_solver.
        - subst. renamePIDPID_case_match.
          + apply elem_of_difference. split. 2: set_solver.
            apply elem_of_map. exists x0. case_match; eqb_to_eq; set_solver.
          + apply elem_of_difference. split. 2: set_solver.
            apply elem_of_map. exists x0. case_match; eqb_to_eq; set_solver.
    }
    constructor.
  * simpl in *. destruct Nat.eqb eqn:P; eqb_to_eq; subst.
    - replace (renamePIDPID ι to ι) with to by (renamePIDPID_case_match). constructor.
    - replace (renamePIDPID from to ι) with ι by renamePIDPID_case_match.
      constructor.
  * simpl in *. destruct Nat.eqb eqn:P; eqb_to_eq; subst.
    - replace (renamePIDPID ι to ι) with to by (renamePIDPID_case_match).
      constructor.
    - replace (renamePIDPID from to ι) with ι by renamePIDPID_case_match.
      constructor.
  * simpl in *. rewrite set_map_union_L. simpl.
    destruct Nat.eqb eqn:P; eqb_to_eq; subst.
    - rewrite set_map_singleton_L.
      replace (renamePIDPID ι to ι) with to by renamePIDPID_case_match.
      constructor.
    - rewrite set_map_singleton_L.
      replace (renamePIDPID from to ι) with ι by renamePIDPID_case_match.
      constructor.
  * simpl in *.
    unfold set_map at 2. (* Why does replace not work without unfolding?? *)
    (* TODO: extract it somehow to a separate theorem about set_map and ∖ - couldn't do it because of the tangled typeclasses *)
    replace (list_to_set (renamePIDPID from to <$> elements (links ∖ {[ι]})))
      with ((set_map (renamePIDPID from to) links ∖ {[renamePIDPID from to ι]}) : gset PID).
    2: {
      apply set_eq. split; intros.
      * apply elem_of_difference in H as [H ?].
        apply elem_of_map in H. destruct_hyps. subst.
        destruct (decide (x0 = ι)). set_solver.
        assert (x0 ≠ to) by set_solver.
        destruct (decide (x0 = from)).
        - subst. renamePIDPID_case_match. renamePIDPID_case_match_hyp H2.
          apply elem_of_map. exists from. rewrite Nat.eqb_refl. set_solver.
        - renamePIDPID_case_match. renamePIDPID_case_match_hyp H2.
          apply elem_of_map. exists x0. case_match; eqb_to_eq; set_solver.
          apply elem_of_map. exists x0. case_match; eqb_to_eq; set_solver.
      * apply elem_of_map in H. destruct_hyps. subst.
        assert (x0 ≠ to) by set_solver.
        destruct (decide (x0 = from)).
        - subst. renamePIDPID_case_match. set_solver.
          apply elem_of_difference. split. 2: set_solver.
          apply elem_of_map. exists from. rewrite Nat.eqb_refl. split. reflexivity.
          set_solver.
        - subst. renamePIDPID_case_match.
          + apply elem_of_difference. split. 2: set_solver.
            apply elem_of_map. exists x0. case_match; eqb_to_eq; set_solver.
          + apply elem_of_difference. split. 2: set_solver.
            apply elem_of_map. exists x0. case_match; eqb_to_eq; set_solver.
    }
    destruct Nat.eqb eqn:P; eqb_to_eq; subst.
    - replace (renamePIDPID ι to ι) with to by renamePIDPID_case_match.
      constructor.
    - replace (renamePIDPID from to ι) with ι by renamePIDPID_case_match.
    constructor.
  * simpl in *.
    setoid_rewrite fmap_delete.
    setoid_rewrite kmap_delete; auto.
    rewrite renamePIDPID_sym_neq. 2: set_solver. apply p_dead.
    setoid_rewrite lookup_kmap_Some; auto.
    exists ι. split. rewrite renamePIDPID_sym_neq. 2: set_solver. reflexivity.
    setoid_rewrite lookup_fmap. by setoid_rewrite H2.
  * simpl in *. destruct Nat.eqb eqn:P; eqb_to_eq; subst.
    - replace (renamePIDPID ι to ι) with to by (unfold renamePIDPID; now rewrite Nat.eqb_refl). constructor.
    - replace (renamePIDPID from to ι) with ι by renamePIDPID_case_match.
      constructor.
  * simpl in *. destruct Nat.eqb eqn:P; eqb_to_eq; subst.
    - replace (renamePIDPID ι to ι) with to by  renamePIDPID_case_match. constructor. now rewrite len_renamePID.
    - replace (renamePIDPID from to ι) with ι by renamePIDPID_case_match.
      constructor. now rewrite len_renamePID.
  * simpl in *.
    rewrite set_map_union_L, set_map_singleton_L.
    destruct Nat.eqb eqn:P; eqb_to_eq; subst.
    - replace (renamePIDPID ι to ι) with to by  renamePIDPID_case_match. constructor. now rewrite len_renamePID.
    - replace (renamePIDPID from to ι) with ι by renamePIDPID_case_match.
      constructor. now rewrite len_renamePID.
  * simpl. apply p_recv_peek_message_ok. rewrite peekMessage_renamePID, H2. reflexivity.
  * simpl. constructor. rewrite peekMessage_renamePID, H2. reflexivity.
  * simpl. constructor. by rewrite <-recvNext_renamePID, H2.
  * simpl. constructor. rewrite removeMessage_renamePID, H2. reflexivity.
  * simpl. apply p_recv_wait_timeout_invalid.
    all: intro X; destruct v; simpl in X; try congruence.
    all: break_match_hyp; congruence.
  * simpl. destruct flag; simpl; apply p_set_flag.
    all: destruct v; inv H2; simpl; auto.
  * simpl. destruct flag; simpl; apply p_set_flag_exc.
    all: destruct v; inv H2; simpl; auto.
    all: by case_match.
  * simpl.
    rewrite fmap_gset_to_gmap.
    replace (inr _) with
      (inr (gset_to_gmap normal (set_map (renamePIDPID from to) links)) : Process).
    2: {
      f_equal. apply map_eq. intros.
      rewrite lookup_gset_to_gmap. unfold guard. case_match.
      * clear H. simpl.
        apply elem_of_map in e. destruct_hyps. subst.
        rewrite <- renamePIDPID_sym_neq. 2: set_solver.
        setoid_rewrite lookup_kmap; auto.
        rewrite lookup_gset_to_gmap. unfold guard. case_match.
        all: clear H; set_solver.
      * clear H. symmetry. apply lookup_kmap_None; auto.
        intros. subst.
        apply lookup_gset_to_gmap_None.
        intro. apply n. apply elem_of_map. eexists. split.
        rewrite renamePIDPID_sym_neq. 2: set_solver.
        reflexivity. assumption.
    }
    constructor.
  * destruct exc, p.
    remember (make_exit_signal (e, v0, v)) as reason eqn:Hreason.
    simpl. rewrite fmap_gset_to_gmap.
    replace (inr _) with
      (inr (gset_to_gmap reason .⟦ from ↦ to ⟧ᵥ (set_map (renamePIDPID from to) links)) : Process).
    2: {
      f_equal. apply map_eq. intros.
      rewrite lookup_gset_to_gmap. unfold guard. case_match.
      * clear H. simpl.
        apply elem_of_map in e0. destruct_hyps. subst.
        rewrite <- renamePIDPID_sym_neq. 2: set_solver.
        setoid_rewrite lookup_kmap; auto.
        rewrite lookup_gset_to_gmap. unfold guard. case_match.
        all: clear H; set_solver.
      * clear H. symmetry. apply lookup_kmap_None; auto.
        intros. subst.
        apply lookup_gset_to_gmap_None.
        intro. apply n. apply elem_of_map. eexists. split.
        rewrite renamePIDPID_sym_neq. 2: set_solver.
        reflexivity. assumption.
    }
    subst reason. rewrite renamePID_make_exit_signal.
    constructor.
Qed.
Transparent mailboxPush.

(** Renaming a PID to itself leaves a process unchanged. *)
Corollary renamePID_id_proc :
  forall pr p, renamePIDProc p p pr = pr.
Proof.
  destruct pr; simpl; intros.
  * destruct l, p0, p0, p0.
    rewrite renamePID_id_stack, renamePID_id_red. f_equal.
    f_equal. f_equal. f_equal.
    - destruct m; unfold renamePIDMb. simpl. f_equal.
      + rewrite <- (map_id l) at 2. apply map_ext_in_iff. intros.
        by rewrite renamePID_id_val.
      + rewrite <- (map_id l0) at 2. apply map_ext_in_iff. intros.
        by rewrite renamePID_id_val.
    - (* TODO: set_map_id *)
      apply set_eq. split; intros.
      + apply elem_of_map in H. destruct_hyps. renamePIDPID_case_match_hyp H;
        auto.
      + apply elem_of_map. exists x. split; auto.
        renamePIDPID_case_match.
  * f_equal.
    apply map_eq. intros.
    destruct (d !! i) eqn:P; setoid_rewrite P.
    - apply lookup_kmap_Some; auto. exists i. split.
      + renamePIDPID_sym_case_match.
      + setoid_rewrite lookup_fmap. setoid_rewrite P.
        simpl. by rewrite renamePID_id_val.
    - apply lookup_kmap_None; auto. intros.
      setoid_rewrite lookup_fmap. renamePIDPID_sym_case_match_hyp H; by setoid_rewrite P.
Qed.

(** Renaming a PID to itself leaves a signal unchanged. *)
Corollary renamePID_id_sig :
  forall s p, renamePIDSignal p p s = s.
Proof.
  destruct s; intros; simpl; try reflexivity.
  all: by rewrite renamePID_id_val.
Qed.

(** Renaming a PID to itself leaves an action unchanged. *)
Corollary renamePID_id_act :
  forall a p, renamePIDAct p p a = a.
Proof.
  destruct a; intros; simpl; try reflexivity.
  4: do 2 rewrite renamePID_id_val. 1-2: rewrite renamePID_id_sig.
  all: by renamePIDPID_case_match.
Qed.

(** Renaming a PID that does not occur in an action leaves the action
    unchanged. *)
Corollary isNotUsed_renamePID_action :
  forall a from to, from ∉ (usedPIDsAct a) -> renamePIDAct from to a = a.
Proof.
  intros. destruct a; try reflexivity; simpl in *.
  * rewrite isNotUsed_renamePID_sig.
    unfold renamePIDPID; repeat case_match; eqb_to_eq. all: set_solver.
  * rewrite isNotUsed_renamePID_sig.
    unfold renamePIDPID; repeat case_match; eqb_to_eq. all: set_solver.
  * unfold renamePIDPID; repeat case_match; eqb_to_eq. all: set_solver.
  * rewrite isNotUsed_renamePID_val. rewrite isNotUsed_renamePID_val.
    unfold renamePIDPID; repeat case_match; eqb_to_eq. all: set_solver.
Qed.

(** Renaming the PID `from` to `to` and then back restores an action in which `to`
    does not occur. *)
Corollary double_renamePID_action :
  forall a from to, to ∉ (usedPIDsAct a) -> renamePIDAct to from (renamePIDAct from to a) = a.
Proof.
  intros. destruct a; try reflexivity; simpl.
  * unfold renamePIDPID. simpl in *.
    rewrite double_renamePID_sig.
    repeat case_match; eqb_to_eq. all: set_solver.
  * unfold renamePIDPID. simpl in *.
    rewrite double_renamePID_sig.
    repeat case_match; eqb_to_eq. all: set_solver.
  * unfold renamePIDPID. simpl in *.
    repeat case_match; eqb_to_eq. all: set_solver.
  * unfold renamePIDPID. simpl in *.
    rewrite double_renamePID_val. rewrite double_renamePID_val.
    repeat case_match; eqb_to_eq. all: set_solver.
Qed.

(** Two independent PID renamings (`from1 ≠ from2`, `from1 ≠ to2`,
    `from2 ≠ to1`) can be applied to a signal in either order. *)
Corollary renamePID_swap_sig :
  forall s from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 ->
               renamePIDSignal from1 to1 (renamePIDSignal from2 to2 s) =
               renamePIDSignal from2 to2 (renamePIDSignal from1 to1 s).
Proof.
  destruct s; intros; try reflexivity; simpl.
  * by rewrite renamePID_swap_val.
  * by rewrite renamePID_swap_val.
Qed.

(** Two independent PID renamings (`from1 ≠ from2`, `from1 ≠ to2`,
    `from2 ≠ to1`) can be applied to an action in either order. *)
Corollary renamePID_swap_act :
  forall a from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 ->
               renamePIDAct from1 to1 (renamePIDAct from2 to2 a) =
               renamePIDAct from2 to2 (renamePIDAct from1 to1 a).
Proof.
  destruct a; intros; simpl.
  * rewrite renamePID_swap_sig; try lia. f_equal.
    - renamePIDPID_case_match.
    - renamePIDPID_case_match.
  * rewrite renamePID_swap_sig; try lia. f_equal.
    - renamePIDPID_case_match.
    - renamePIDPID_case_match.
  * f_equal. renamePIDPID_case_match.
  * rewrite renamePID_swap_val, (renamePID_swap_val t2); try lia. f_equal.
    renamePIDPID_case_match.
  * reflexivity.
  * reflexivity.
Qed.

(** Two independent PID renamings with different new PIDs can be applied to a
    process in either order (the extra condition `to1 ≠ to2` is needed
    because the keys of dead processes are swapped). *)
Corollary renamePID_swap_proc :
  forall p from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 -> to1 ≠ to2 ->
               renamePIDProc from1 to1 (renamePIDProc from2 to2 p) =
               renamePIDProc from2 to2 (renamePIDProc from1 to1 p).
Proof.
  destruct p.
  * destruct l, p, p, p; intros; simpl.
    rewrite renamePID_swap_red.
    rewrite renamePID_swap_stack.
    all: try lia. f_equal. f_equal. f_equal. f_equal.
    - destruct m; unfold renamePIDMb. simpl.
      repeat rewrite map_map. f_equal.
      + apply map_ext_in_iff. intros. by rewrite renamePID_swap_val.
      + apply map_ext_in_iff. intros. by rewrite renamePID_swap_val.
    - apply set_eq. split; intros X; apply elem_of_map in X; destruct_hyps; subst;
        apply elem_of_map in H4; destruct_hyps; subst.
      + destruct (decide (x = from1)). 2: destruct (decide (x = from2)).
        ** apply elem_of_map. exists to1. split.
           renamePIDPID_case_match. apply elem_of_map.
           exists from1. split.
           renamePIDPID_case_match. by subst.
        ** apply elem_of_map. exists from2. split.
           renamePIDPID_case_match. apply elem_of_map.
           exists from2. split.
           renamePIDPID_case_match. by subst.
        ** apply elem_of_map. exists x. split.
           renamePIDPID_case_match. apply elem_of_map.
           exists x. split.
           renamePIDPID_case_match. by subst.
      + destruct (decide (x = from1)). 2: destruct (decide (x = from2)).
        ** apply elem_of_map. exists from1. split.
           renamePIDPID_case_match. apply elem_of_map.
           exists from1. split.
           renamePIDPID_case_match. by subst.
        ** apply elem_of_map. exists to2. split.
           renamePIDPID_case_match. apply elem_of_map.
           exists from2. split.
           renamePIDPID_case_match. by subst.
        ** apply elem_of_map. exists x. split.
           renamePIDPID_case_match. apply elem_of_map.
           exists x. split.
           renamePIDPID_case_match. by subst.
  * intros. simpl. f_equal.
    apply map_eq. intros.
    (* Solution strategy is analogous for these 5 cases *)
    destruct (decide (i = from1)). 2: destruct (decide (i = from2)).
    3: destruct (decide (i = to1)). 4: destruct (decide (i = to2)).
    all: subst.
    - replace from1 with (renamePIDPID_sym from1 to1 to1) at 1 by renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      replace from1 with (renamePIDPID_sym from2 to2 from1) at 2 by renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      setoid_rewrite lookup_fmap.
      replace to1 with (renamePIDPID_sym from2 to2 to1) at 2 by renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      replace from1 with (renamePIDPID_sym from1 to1 to1) at 2 by renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      setoid_rewrite lookup_fmap. destruct (d !! to1) eqn:P; setoid_rewrite P; simpl.
      2: reflexivity.
      1: by rewrite renamePID_swap_val.
    - replace from2 with (renamePIDPID_sym from1 to1 from2) at 1 by renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      replace from2 with (renamePIDPID_sym from2 to2 to2) at 4 by renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      setoid_rewrite lookup_fmap.
      replace from2 with (renamePIDPID_sym from2 to2 to2) at 1 by renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      replace to2 with (renamePIDPID_sym from1 to1 to2) at 4 by renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      setoid_rewrite lookup_fmap. destruct (d !! to2) eqn:P; setoid_rewrite P; simpl.
      2: reflexivity.
      1: by rewrite renamePID_swap_val.
    - replace to1 with (renamePIDPID_sym from1 to1 from1) at 1 by renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      replace to1 with (renamePIDPID_sym from2 to2 to1) at 2 by renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      setoid_rewrite lookup_fmap.
      replace from1 with (renamePIDPID_sym from2 to2 from1) at 2 by renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      replace to1 with (renamePIDPID_sym from1 to1 from1) at 2 by renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      setoid_rewrite lookup_fmap. destruct (d !! from1) eqn:P; setoid_rewrite P; simpl.
      2: reflexivity.
      1: by rewrite renamePID_swap_val.
    - replace to2 with (renamePIDPID_sym from1 to1 to2) at 1 by renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      replace to2 with (renamePIDPID_sym from2 to2 from2) at 4 by renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      setoid_rewrite lookup_fmap.
      replace to2 with (renamePIDPID_sym from2 to2 from2) at 1 by renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      replace from2 with (renamePIDPID_sym from1 to1 from2) at 4 by renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      setoid_rewrite lookup_fmap. destruct (d !! from2) eqn:P; setoid_rewrite P; simpl.
      2: reflexivity.
      1: by rewrite renamePID_swap_val.
    - replace i with (renamePIDPID_sym from1 to1 i) at 1 by renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      replace i with (renamePIDPID_sym from2 to2 i) at 2 by renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      setoid_rewrite lookup_fmap.
      replace i with (renamePIDPID_sym from2 to2 i) at 1 by renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      replace i with (renamePIDPID_sym from1 to1 i) at 2 by renamePIDPID_sym_case_match.
      setoid_rewrite lookup_kmap; auto.
      setoid_rewrite lookup_fmap. destruct (d !! i) eqn:P; setoid_rewrite P; simpl.
      2: reflexivity.
      1: by rewrite renamePID_swap_val.
Qed.

(** Renaming the PID `p` to `p'` in a signal removes `p` from its used PIDs, and
    adds `p'` if `p` was used. *)
Corollary usedPIDsSig_rename :
  (forall s p p',
    usedPIDsSignal (renamePIDSignal p p' s) = if decide (p ∈ usedPIDsSignal s)
                                        then {[p']} ∪ usedPIDsSignal s ∖ {[p]}
                                        else usedPIDsSignal s ∖ {[p]}).
Proof.
  destruct s; intros; simpl.
  3-4: set_solver.
  1-2: rewrite usedPIDsVal_rename; set_solver.
Qed.

(** Renaming the PID `p` to `p'` in an action removes `p` from its used PIDs, and
    adds `p'` if `p` was used. *)
Corollary usedPIDsAct_rename :
  (forall a p p',
    usedPIDsAct (renamePIDAct p p' a) = if decide (p ∈ usedPIDsAct a)
                                        then {[p']} ∪ usedPIDsAct a ∖ {[p]}
                                        else usedPIDsAct a ∖ {[p]}).
Proof.
  destruct a; intros; simpl.
  5-6: set_solver.
  * unfold renamePIDPID. rewrite usedPIDsSig_rename.
    repeat destruct decide; repeat case_match; eqb_to_eq; subst; set_solver.
  * unfold renamePIDPID. rewrite usedPIDsSig_rename.
    repeat destruct decide; repeat case_match; eqb_to_eq; subst; set_solver.
  * unfold renamePIDPID.
    repeat destruct decide; repeat case_match; eqb_to_eq; subst; set_solver.
  * unfold renamePIDPID. do 2 rewrite usedPIDsVal_rename.
    repeat destruct decide; repeat case_match; eqb_to_eq; subst; set_solver.
Qed.

(** Renaming the PID `p` to `p'` in a live process removes `p` from its used PIDs,
    and adds `p'` if `p` was used. *)
Corollary usedPIDsLiveProc_rename :
  forall pr p p',
    usedPIDsProc (renamePIDProc p p' (inl pr)) = if decide (p ∈ usedPIDsProc (inl pr))
                                        then {[p']} ∪ usedPIDsProc (inl pr) ∖ {[p]}
                                        else usedPIDsProc (inl pr) ∖ {[p]}.
Proof.
  destruct pr, p, p, p; simpl; intros.
  rewrite usedPIDsStack_rename, usedPIDsRed_rename. destruct m. simpl.
  do 2 rewrite usedPIDsVal_flat_union.
  remember (flat_union _ l) as X. remember (flat_union _ l0) as Y.
  clear HeqX HeqY.
  replace (set_map (renamePIDPID p p') g) with
                                       ((if (decide (p ∈ g))
                                        then {[p']} ∪ g ∖ {[p]}
                                        else g ∖ {[p]}) : gset PID).
  2: {
    case_match; clear H; apply set_eq; split; intros.
    * apply elem_of_union in H as [|].
      - assert (x = p') by set_solver. subst.
        apply elem_of_map. exists p. split; by renamePIDPID_case_match.
      - apply elem_of_difference in H as [? ?].
        apply elem_of_map. exists x. split. renamePIDPID_case_match. set_solver.
        assumption.
    * apply elem_of_map in H. destruct_hyps. subst.
      renamePIDPID_case_match.
      - set_solver.
      - set_solver.
    * apply elem_of_difference in H as [? ?].
      apply elem_of_map. exists x. split. renamePIDPID_case_match. set_solver.
      assumption.
    * apply elem_of_map in H. destruct_hyps. subst.
      renamePIDPID_case_match.
      - set_solver.
      - set_solver.
  }
  repeat destruct decide; set_solver. (* NOTE: this line takes long to compile *)
Qed.

(** PID renaming does not change whether a PID different from the old and the
    new PID occurs in a dead process. *)
Theorem usedPIDsDeadProc_rename_neq :
  forall d ι p p',
  ι <> p -> ι <> p' ->
  ι ∈ usedPIDsProc (inr d) <->
  ι ∈ usedPIDsProc (inr d) .ₚ⟦ p ↦ p' ⟧.
Proof.
  split; intros; simpl in *; apply elem_of_union_list in H1; destruct_hyps;
    apply elem_of_elements, elem_of_map_to_set in H1; destruct_hyps.
  {
    subst.
    apply elem_of_union in H2 as [|].
    * apply elem_of_union_list. exists ({[x0]} ∪ (usedPIDsVal (renamePIDVal p p' x1))). split.
      2: set_solver.
      apply elem_of_elements, elem_of_map_to_set.
      exists x0. eexists. split. 2: simpl; reflexivity.
      setoid_rewrite lookup_kmap_Some; auto.
      exists ι. renamePIDPID_sym_case_match. split. set_solver.
      setoid_rewrite lookup_fmap. assert (ι = x0) by set_solver.
      subst. by setoid_rewrite H1.
    * apply elem_of_union_list.
      destruct (decide (x0 = p)). 2: destruct (decide (x0 = p')).
      - exists ({[p']} ∪ (usedPIDsVal (renamePIDVal p p' x1))). split.
        2: rewrite usedPIDsVal_rename; destruct decide; set_solver.
        apply elem_of_elements, elem_of_map_to_set.
        subst. exists p'. eexists. split. 2: simpl; reflexivity.
        setoid_rewrite lookup_kmap_Some; auto.
        subst. exists p. split. by renamePIDPID_sym_case_match.
        setoid_rewrite lookup_fmap. by setoid_rewrite H1.
      - exists ({[p]} ∪ (usedPIDsVal (renamePIDVal p p' x1))). split.
        2: rewrite usedPIDsVal_rename; destruct decide; set_solver.
        apply elem_of_elements, elem_of_map_to_set.
        subst. exists p. eexists. split. 2: simpl; reflexivity.
        setoid_rewrite lookup_kmap_Some; auto.
        subst. exists p'. split. by renamePIDPID_sym_case_match.
        setoid_rewrite lookup_fmap. by setoid_rewrite H1.
      - exists ({[x0]} ∪ (usedPIDsVal (renamePIDVal p p' x1))). split.
        2: rewrite usedPIDsVal_rename; destruct decide; set_solver.
        apply elem_of_elements, elem_of_map_to_set.
        subst. exists x0. eexists. split. 2: simpl; reflexivity.
        setoid_rewrite lookup_kmap_Some; auto.
        subst. exists x0. split. by renamePIDPID_sym_case_match.
        setoid_rewrite lookup_fmap. by setoid_rewrite H1.
  }
  {
    apply lookup_kmap_Some in H1; auto. destruct_hyps. subst.
    setoid_rewrite lookup_fmap in H4.
    destruct (d !! x2) eqn:P; setoid_rewrite P in H4; inv H4.
    apply elem_of_union in H2 as [|].
    * renamePIDPID_sym_case_match_hyp H1.
      - apply elem_of_union_list. exists ({[p']} ∪ usedPIDsVal v). split.
        2: set_solver.
        apply elem_of_elements, elem_of_map_to_set.
        do 2 eexists. split. exact P. set_solver.
      - apply elem_of_union_list. exists ({[p]} ∪ usedPIDsVal v). split.
        2: set_solver.
        apply elem_of_elements, elem_of_map_to_set.
        do 2 eexists. split. exact P. set_solver.
      - apply elem_of_union_list. exists ({[x2]} ∪ usedPIDsVal v). split.
        2: set_solver.
        apply elem_of_elements, elem_of_map_to_set.
        do 2 eexists. split. exact P. set_solver.
    * apply elem_of_union_list. exists ({[x2]} ∪ usedPIDsVal v). split.
      2: rewrite usedPIDsVal_rename in H1; destruct decide; set_solver.
      apply elem_of_elements, elem_of_map_to_set.
      do 2 eexists. split. exact P. set_solver.
  }
Qed.

(** If the renamed PID occurs in a renamed dead process, then the new PID
    occurs in the original process. *)
Theorem usedPIDsDeadProc_rename_old :
  forall d p p',
  p ∈ usedPIDsProc (inr d) .ₚ⟦ p ↦ p' ⟧ ->
  p' ∈ usedPIDsProc (inr d).
Proof.
  intros; simpl in *; apply elem_of_union_list in H; destruct_hyps;
    apply elem_of_elements, elem_of_map_to_set in H; destruct_hyps.
  setoid_rewrite lookup_kmap_Some in H; auto. destruct_hyps. subst.
  setoid_rewrite lookup_fmap in H2.
  destruct (d !! x2) eqn:P; setoid_rewrite P in H2; inv H2.
  apply elem_of_union in H0 as [|].
  * renamePIDPID_sym_case_match_hyp H.
    - assert (p = p') by set_solver. subst.
      apply elem_of_union_list. exists ({[p']} ∪ usedPIDsVal v). split. 2: set_solver.
      apply elem_of_elements, elem_of_map_to_set.
      exists p', v. split; by auto.
    - apply elem_of_union_list. exists ({[p']} ∪ usedPIDsVal v). split. 2: set_solver.
      apply elem_of_elements, elem_of_map_to_set.
      exists p', v. split; by auto.
    - apply elem_of_union_list. exists ({[x2]} ∪ usedPIDsVal v). split. 2: set_solver.
      apply elem_of_elements, elem_of_map_to_set.
      exists x2, v. split; by auto.
  * apply elem_of_union_list. exists ({[x2]} ∪ usedPIDsVal v). split.
    2: rewrite usedPIDsVal_rename in H; destruct decide; set_solver.
    apply elem_of_elements, elem_of_map_to_set.
    do 2 eexists. split. exact P. set_solver.
Qed.

(** If the old PID occurs in a dead process, then the new PID occurs in the
    renamed process. *)
Theorem usedPIDsDeadProc_rename_new_1 :
  forall d p p',
  p ∈ usedPIDsProc (inr d) ->
  p' ∈ usedPIDsProc (inr d) .ₚ⟦ p ↦ p' ⟧ .
Proof.
  intros; simpl in *; apply elem_of_union_list in H; destruct_hyps;
    apply elem_of_elements, elem_of_map_to_set in H; destruct_hyps.
  subst. apply elem_of_union in H0 as [|].
  * assert (p = x0) by set_solver. subst.
    apply elem_of_union_list. exists ({[p']} ∪ (usedPIDsVal (renamePIDVal x0 p' x1))). split.
    2: set_solver.
    apply elem_of_elements, elem_of_map_to_set.
    exists p'. eexists. split. 2: simpl; reflexivity.
    setoid_rewrite lookup_kmap_Some; auto.
    exists x0. renamePIDPID_sym_case_match. split. set_solver.
    setoid_rewrite lookup_fmap. subst. by setoid_rewrite H.
  * apply elem_of_union_list.
    destruct (decide (x0 = p)). 2: destruct (decide (x0 = p')).
    - exists ({[p']} ∪ (usedPIDsVal (renamePIDVal p p' x1))). split.
      2: rewrite usedPIDsVal_rename; destruct decide; set_solver.
      apply elem_of_elements, elem_of_map_to_set.
      subst. exists p'. eexists. split. 2: simpl; reflexivity.
      setoid_rewrite lookup_kmap_Some; auto.
      subst. exists p. split. by renamePIDPID_sym_case_match.
      setoid_rewrite lookup_fmap. by setoid_rewrite H.
    - exists ({[p]} ∪ (usedPIDsVal (renamePIDVal p p' x1))). split.
      2: rewrite usedPIDsVal_rename; destruct decide; set_solver.
      apply elem_of_elements, elem_of_map_to_set.
      subst. exists p. eexists. split. 2: simpl; reflexivity.
      setoid_rewrite lookup_kmap_Some; auto.
      subst. exists p'. split. by renamePIDPID_sym_case_match.
      setoid_rewrite lookup_fmap. by setoid_rewrite H.
    - exists ({[x0]} ∪ (usedPIDsVal (renamePIDVal p p' x1))). split.
      2: rewrite usedPIDsVal_rename; destruct decide; set_solver.
      apply elem_of_elements, elem_of_map_to_set.
      subst. exists x0. eexists. split. 2: simpl; reflexivity.
      setoid_rewrite lookup_kmap_Some; auto.
      subst. exists x0. split. by renamePIDPID_sym_case_match.
      setoid_rewrite lookup_fmap. by setoid_rewrite H.
Qed.

(** Renaming the PID `p` to a fresh `p'` in a dead process removes `p` from its used
    PIDs, and adds `p'` if `p` was used (only one direction holds, as an
    inclusion). *)
Theorem usedPIDsDeadProc_rename :
  forall pr p p',
    p' ∉ usedPIDsProc (inr pr) -> (* Remaning is symmetric for dead processes, thus
                                     this side condition is needed. E.g.,
                                     inr [(p', 'ok')] *)
    (if decide (p ∈ usedPIDsProc (inr pr))
    then {[p']} ∪ usedPIDsProc (inr pr) ∖ {[p]}
    else usedPIDsProc (inr pr) ∖ {[p]}) ⊆ usedPIDsProc (renamePIDProc p p' (inr pr)).
Proof.
  intros. simpl.
  unfold union_set.
  apply elem_of_subseteq; intros.
  break_match_hyp.
  * apply elem_of_union_list in e. destruct_hyps.
    apply elem_of_elements in H1. apply elem_of_map_to_set in H1.
    destruct_hyps. subst.
    assert (x1 ≠ p') as X.
    {
      intro. subst. apply H.
      apply elem_of_union_list. exists ({[p']} ∪ usedPIDsVal x2).
      split. 2: set_solver.
      apply elem_of_elements, elem_of_map_to_set.
      do 2 eexists. split. 2: reflexivity. assumption.
    }
    destruct (decide (x = p')).
    - subst.
      destruct (decide (p = x1)).
      + subst.
        apply elem_of_union_list. exists ({[p']} ∪ usedPIDsVal (renamePIDVal x1 p' x2)). split. 2: set_solver.
        apply elem_of_elements, elem_of_map_to_set.
        do 2 eexists. split. 2: reflexivity.
        setoid_rewrite lookup_kmap_Some; auto.
        exists x1. split. renamePIDPID_sym_case_match. setoid_rewrite lookup_fmap.
        by setoid_rewrite H1.
      + apply elem_of_union_list. exists ({[x1]} ∪ usedPIDsVal (renamePIDVal p p' x2)). split.
        2: rewrite usedPIDsVal_rename; destruct decide; set_solver.
        apply elem_of_elements, elem_of_map_to_set.
        do 2 eexists. split. 2: reflexivity.
        setoid_rewrite lookup_kmap_Some; auto.
        exists x1. split. renamePIDPID_sym_case_match. setoid_rewrite lookup_fmap.
        by setoid_rewrite H1.
    - apply elem_of_union in H0 as [|]. set_solver.
      apply elem_of_difference in H0 as [? ?].
      apply elem_of_union_list in H0. destruct_hyps.
      apply elem_of_elements, elem_of_map_to_set in H0. destruct_hyps.
      subst.
      assert (x ≠ p) by set_solver. clear H3.
      apply elem_of_union in H4 as [|].
      + assert (x = x3) by set_solver. subst. clear H3.
        apply elem_of_union_list. exists ({[x3]} ∪ usedPIDsVal (renamePIDVal p p' x4)).
        split. 2: rewrite usedPIDsVal_rename; destruct decide; set_solver.
        apply elem_of_elements, elem_of_map_to_set.
        do 2 eexists. split. 2: reflexivity.
        setoid_rewrite lookup_kmap_Some; auto. exists x3.
        split. renamePIDPID_sym_case_match.
        setoid_rewrite lookup_fmap.
        by setoid_rewrite H0.
      + assert (x3 ≠ p') as X2. {
          intro. subst. apply H.
          apply elem_of_union_list. exists ({[p']} ∪ usedPIDsVal x4).
          split. 2: set_solver.
          apply elem_of_elements, elem_of_map_to_set.
          do 2 eexists. split. 2: reflexivity. assumption.
        }
        destruct (decide (x3 = p)).
        {
          subst.
          apply elem_of_union_list. exists ({[p']} ∪ usedPIDsVal (renamePIDVal p p' x4)).
          split. 2: rewrite usedPIDsVal_rename; destruct decide; set_solver.
          apply elem_of_elements, elem_of_map_to_set.
          do 2 eexists. split. 2: reflexivity.
          setoid_rewrite lookup_kmap_Some; auto. exists p.
          split. renamePIDPID_sym_case_match.
          setoid_rewrite lookup_fmap.
          by setoid_rewrite H0.
        }
        {
          subst.
          apply elem_of_union_list. exists ({[x3]} ∪ usedPIDsVal (renamePIDVal p p' x4)).
          split. 2: rewrite usedPIDsVal_rename; destruct decide; set_solver.
          apply elem_of_elements, elem_of_map_to_set.
          do 2 eexists. split. 2: reflexivity.
          setoid_rewrite lookup_kmap_Some; auto. exists x3.
          split. renamePIDPID_sym_case_match.
          setoid_rewrite lookup_fmap.
          by setoid_rewrite H0.
        }
  * pose proof (isNotUsed_renamePID_proc (inr pr) p p' n H).
    cbn in H1. inv H1. repeat setoid_rewrite H3.
    set_solver.
Qed.

(** * Strict equality of signals *)

(** Strict boolean equality of signals, based on `Val_eqb_strict`. *)
Definition Signal_eqb_strict (sig1 sig2 : Signal) : bool :=
  match sig1, sig2 with
  | SMessage v1, SMessage v2 => Val_eqb_strict v1 v2
  | SExit v1 b1, SExit v2 b2 => Val_eqb_strict v1 v2 && Bool.eqb b1 b2
  | SLink, SLink => true
  | SUnlink, SUnlink => true
  | _, _ => false
  end.

(** `Signal_eqb_strict` is reflexive. *)
Lemma Signal_eqb_strict_refl: forall sig, Signal_eqb_strict sig sig = true.
Proof.
  intros. destruct sig; simpl; auto.
  * apply eqb_strict_refl_val.
  * rewrite eqb_strict_refl_val. simpl. apply eqb_reflx.
Qed.

(** `Signal_eqb_strict` decides the equality of signals. *)
Lemma Signal_eqb_strict_eq: forall sig1 sig2, Signal_eqb_strict sig1 sig2 = true <-> sig1 = sig2.
Proof.
  intros. split; intro.
  * unfold Signal_eqb_strict in H. destruct sig1 eqn:Hs1.
    + destruct sig2 eqn:Hs2; try discriminate.
      apply eqb_strict_eq_val in H. subst. reflexivity.
    + destruct sig2 eqn:Hs2; try discriminate.
      symmetry in H. apply andb_true_eq in H. destruct H.
      symmetry in H0, H. apply eqb_prop in H0. apply eqb_strict_eq_val in H.
      subst. reflexivity.
    + destruct sig2 eqn:Hs2; try discriminate. reflexivity.
    + destruct sig2 eqn:Hs2; try discriminate. reflexivity.
  * rewrite H. apply Signal_eqb_strict_refl.
Qed.

(** * Properties of the process-local semantics *)

(** Values converted to booleans by `bool_from_lit` are closed. *)
Theorem bool_from_lit_val :
  forall y e, Some y = bool_from_lit e -> VALCLOSED e.
Proof.
  destruct e; intros; inversion H.
  now constructor.
Qed.

(** The process-local semantics is deterministic for a given action. *)
Lemma process_local_determinism :
  forall p p' a, p -⌈a⌉-> p' -> forall p'', p -⌈a⌉-> p'' -> p' = p''.
Proof.
  intros p p' a IH. induction IH; intros; try now inv H.
  * inv H0; try (now inv H; cbn in *; invSome).
    - eapply step_determinism in H. 2: exact H7. destruct H. now subst.
  * inv H0; firstorder; subst; try congruence.
  * inv H0; firstorder; subst; try congruence.
  * inv H0; firstorder; subst; try congruence.
  * inv H0; firstorder; subst; try congruence.
  * now inv H0.
  * now inv H0.
  * inv H0.
    - inv H7.
    - reflexivity.
  * inv H0. congruence.
  * inv H0. by inv H7. reflexivity.
  * inv H0.
    - inv H7.
    - reflexivity.
  * inv H.
    - inv H6.
    - now auto.
  * inv H.
    - by inv H6.
    - reflexivity.
  * inv H1.
    - inv H8.
    - now auto.
  * inv H0. rewrite <-H in H7. now inv H7.
  * inv H0. now inv H7.
    reflexivity.
Qed.

(** Only live processes can take `τ` steps. *)
Theorem internal_is_alive :
  forall p p', p -⌈τ⌉-> p' -> exists pa, p = inl pa.
Proof.
  intros. inversion H; subst; try (do 2 eexists; split; reflexivity).
Qed.

(** * Equality of signals up to `Val_eqb` *)

(** Boolean equality of signals based on `Val_eqb` (which considers all PIDs
    equal, see `Equalities.v`); used to compare the barbs of nodes in the
    bisimulations. *)
Definition Signal_eqb (s1 s2 : Signal) : bool :=
match s1,  s2 with
 | SMessage m, SMessage m' => m =ᵥ m'
 | SExit r b, SExit r' b' => Bool.eqb b b' && (r =ᵥ r')
 | SLink, SLink => true
 | SUnlink, SUnlink => true
 | _, _ => false
end.

Notation "s1 ==ₛ s2" := (Signal_eqb s1 s2) (at level 69, no associativity).

(** The propositional version of `Signal_eqb` *)
Definition Signal_eq (s1 s2 : Signal) : Prop := s1 ==ₛ s2 = true.

Arguments Signal_eq s1 s2 /.

Notation "s1 =ₛ s2" := (Signal_eq s1 s2) (at level 69, no associativity).

(** `Signal_eq` unfolds to `Signal_eqb` with `simpl` (because of its
    `Arguments` declaration). *)
Local Example Signal_eq_unfold : forall s1 s2, s1 ==ₛ s2 = true -> s1 =ₛ s2.
Proof.
  intros. simpl. assumption.
Qed.

(** `=ₛ` is reflexive. *)
Corollary Signal_eq_refl :
  forall s, s =ₛ s.
Proof.
  destruct s; cbn; try reflexivity.
  * cbn. unfold "=ₛ". simpl. apply Val_eqb_refl.
  * cbn. unfold "=ₛ". simpl. rewrite Val_eqb_refl.
    now destruct b.
Qed.

(** `=ₛ` is symmetric. *)
Corollary Signal_eq_sym :
  forall s s', s =ₛ s' -> s' =ₛ s.
Proof.
  destruct s eqn:ES1, s' eqn:ES2; unfold "=ₛ"; cbn; intro H; try reflexivity; try now inv H.
  * now rewrite Val_eqb_sym.
  * cbn. rewrite Val_eqb_sym.
    destruct b, b0; auto.
Qed.

(** `=ₛ` is transitive. *)
Corollary Signal_eq_trans :
  forall s s' s'', s =ₛ s' -> s' =ₛ s'' -> s =ₛ s''.
Proof.
  destruct s eqn:ES1, s' eqn:ES2, s'' eqn:ES3;
    unfold "=ₛ"; cbn; intros H1 H2; try reflexivity; try now inv H1; try now inv H2.
  * erewrite Val_eqb_trans; eauto.
  * apply andb_true_iff in H1, H2. destruct_and!.
    rewrite (Val_eqb_trans _ _ _ H3 H0).
    now destruct b, b0, b1.
Qed.

(** A signal is `=ₛ`-equal to its PID-renamed version. *)
Lemma Signal_eq_renamePID :
  forall s from to,
    s =ₛ renamePIDSignal from to s.
Proof.
  destruct s; intros; try reflexivity.
  all: unfold Signal_eq; simpl; rewrite renamePID_Val_eqb.
  2: rewrite eqb_reflx.
  all: reflexivity.
Qed.
