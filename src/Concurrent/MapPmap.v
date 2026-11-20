(**
  This file proves the equivalence of a sequential and a parallel
  implementation of `map` (`map_pmap_empty_context_bisim`). The sequential
  implementation (`map_seq_send`) maps the list with the `map` closure of
  `FrameStack/Examples.v`, and sends the result to the observed PID `ι`. The
  parallel implementation (`par_map`) splits the list into two parts, spawns
  a process that maps the first part and sends it back, maps the second part
  itself, then receives the first part, and sends the concatenation of the
  two parts to `ι`. Both programs are evaluated in a single-process node with
  an empty ether, and the two nodes are barbed bisimilar, observing `ι`.
*)

From CoreErlang.Concurrent Require Import BisimReductions.
From CoreErlang.FrameStack Require Import SubstSemantics Examples.

Import ListNotations.
Import Notations.

Hint Resolve map_clos_closed : examples.

Section map_pmap.

(** The mapped list `l` (and its meta-level representation `l'`), the mapped
    function `f`, simulated by the closure `f_clos`, and the observed PID
    `ι`. *)
Context {l : Val}
        {l' : list Val}
        {ident : nat}
        {f : Val -> Val}
        {f_clos : Val}
        {f_clos_closed : VALCLOSED f_clos}
        {ι : PID}.

(** The closure `f_clos` computes `f` on the elements of the list. *)
Hypothesis f_simulates :
  forall v : Val,
    v ∈ l' ->
    exists e_body eff,
    create_result (IApp f_clos) [v] = Some (e_body, eff) /\
    ⟨[], e_body⟩ -->* RValSeq [f v].
(** `l` is a proper list. *)
Hypothesis l_is_proper : mk_list l = Some l'.
(** `f` maps closed values to closed values. *)
Hypothesis f_closed : forall v, VALCLOSED v -> VALCLOSED (f v).
(** `l` is closed. *)
Hypothesis l_closed : VALCLOSED l.
(** No PIDs appear in the list. *)
Hypothesis (l_is_free_of_PIDs : usedPIDsVal (meta_to_cons l') = ∅).
(** No PIDs appear in the mapped parts of the list. These two hypotheses
    should be rephrased as properties of `f` (together with
    `l_is_free_of_PIDs`). *)
Hypothesis (Hfmeta1 : forall idx, usedPIDsVal (meta_to_cons (map f (take idx l'))) = ∅).
Hypothesis (Hfmeta2 : forall idx, usedPIDsVal (meta_to_cons (map f (drop idx l'))) = ∅).

Open Scope string_scope.

(** The list is split at the valid index `idx`. *)
Context (idx : nat)
        (Hidx : idx < length l').

(** The parallel implementation corresponds to the following Erlang code:

```
pmap(F, L) ->
  {L1, L2} = lists:split(Idx, L),
  Self = self(),
  spawn(fun(Addr, L0) -> Addr ! map(F, L0) end, [Self, L1]),
  Mapped = map(F, L2),
  receive
    MappedL1 -> ι ! MappedL1 ++ Mapped
  end.
```

    `receive` is the final `receive` expression of this function. *)
Definition receive : Exp :=
(EReceive [
               ([PVar], ˝ttrue, 
                 °ECall (˝erlang) (˝send)
                   [
                    ˝VPid ι;
                    (* VVar 0 is the variable of the clause (MappedL1),
                       VVar 1 is the first variable outside the receive
                       (Mapped) *)
                    °ECall (˝erlang) (˝VLit "++") [˝VVar 0; ˝VVar 1]
                   ])
             ] (˝infinity) (˝VNil)).

(** The sequential part of the parent process in `par_map`: mapping the
    second part of the list (`VVar 2`), then receiving the first part. *)
Definition seq_sec : Exp :=
  ELet 1 (°EApp (˝@map_clos ident) [˝f_clos; ˝VVar 2])
             receive.

(** `receive` is scoped in an environment of one variable (`Mapped`). *)
Lemma receive_closed :
  EXP 1 ⊢ receive.
Proof.
  repeat constructor; simpl. 2: lia.
  destruct i. 2: lia.
  simpl. intros. do 4 scope_solver_step.
  1, 2: scope_solver.
  1-2: destruct i; intros.
  2, 4: destruct i; try lia.
  all: simpl. 1-2: scope_solver.
  all: do 3 scope_solver_step.
  1: scope_solver.
  1: scope_solver_step.
  1: scope_solver.
  all: try destruct i; intros.
  1, 3, 5, 7: simpl. 1-3:scope_solver.
  1: do 10 scope_solver_step.
  all: do 8 scope_solver_step.
  all: intros; destruct i; try destruct i; try destruct i.
  all: do 2 scope_solver_step. lia.
  all: intros; destruct i; try destruct i; try destruct i.
  all: scope_solver.
Qed.

Hint Resolve receive_closed : examples.

(** The body of the spawned function: it maps its second parameter (`L0`),
    and sends the result to its first parameter (`Addr`). *)
Definition send_body : Exp :=
  (°ECall (˝erlang) (˝send) [˝VVar 0; °EApp (˝@map_clos ident) [˝f_clos; ˝VVar 1]]).

(** The parallel implementation of `map` (see the Erlang code above). *)
Definition par_map : Redex :=
  ECase (ECall (˝VLit "lists") (˝VLit "split") [˝VLit (Z.of_nat idx); ˝l])
    [
      ([PTuple [PVar; PVar]], ˝ttrue,
        °ELet 1 (°ECall (˝erlang) (˝self) [])
          (°ESeq 
            (°ECall (˝erlang) (˝spawn) [
             °EFun 2 send_body;
             °ECons (˝VVar 0) (°ECons (˝VVar 1) (˝VNil))])
          (
            seq_sec
          )
        )
      )
    ].

(** The first part of the list is closed. *)
Lemma take_helper1 :
  VALCLOSED (meta_to_cons (take idx l')).
Proof.
  apply meta_to_cons_closed.
  apply mk_list_closed with (Γ := 0) in l_is_proper. 2: assumption.
  by apply Forall_take.
Qed.

(** The mapped first part of the list is closed. *)
Lemma take_helper2 :
  VALCLOSED (meta_to_cons (map f (take idx l'))).
Proof.
  apply meta_to_cons_closed.
  apply mk_list_closed with (Γ := 0) in l_is_proper. 2: assumption.
  apply list.Forall_forall. intros. apply list_elem_of_fmap in H.
  destruct_hyps. subst.
  apply f_closed. rewrite list.Forall_forall in l_is_proper.
  apply l_is_proper. clear-H0.
  pose proof subseteq_take idx l'. set_solver.
Qed.

(** The second part of the list is closed. *)
Lemma drop_helper1 :
  VALCLOSED (meta_to_cons (drop idx l')).
Proof.
  apply meta_to_cons_closed.
  apply mk_list_closed with (Γ := 0) in l_is_proper. 2: assumption.
  by apply Forall_drop.
Qed.

(** The mapped second part of the list is closed. *)
Lemma drop_helper2 :
  VALCLOSED (meta_to_cons (map f (drop idx l'))).
Proof.
  apply meta_to_cons_closed.
  apply mk_list_closed with (Γ := 0) in l_is_proper. 2: assumption.
  apply list.Forall_forall. intros. apply list_elem_of_fmap in H.
  destruct_hyps. subst.
  apply f_closed. rewrite list.Forall_forall in l_is_proper.
  apply l_is_proper. clear-H0.
  pose proof subseteq_drop idx l'. set_solver.
Qed.

Hint Resolve take_helper1 : examples.
Hint Resolve take_helper2 : examples.
Hint Resolve drop_helper1 : examples.
Hint Resolve drop_helper2 : examples.

(** The parent process, waiting for the mapped first part of the list with
    this part already in its mailbox, receives the message, and evaluates the
    concatenation of the two mapped parts, up to sending it to `ι`. *)
Lemma eval_helper_peek_message :
  inl
  ([FParams (IPrimOp "recv_peek_message") [] [];
    FLet 2
      (° ECase (˝ VVar 0)
           [([PLit "true"], ˝ VLit "true",
             ° ECase (˝ VVar 1)
                 [([PVar], ˝ VLit "true",
                   ° ESeq (° EPrimOp "remove_message" [])
                       (° ECall (˝ VLit "erlang") (˝ VLit "!")
                            [˝ VPid ι;
                             ° ECall (˝ VLit "erlang") (˝ VLit "++")
                                 [˝ VVar 0; ˝ meta_to_cons (map f (drop idx l'))]]));
                  ([PVar], ˝ VLit "true",
                   ° ESeq (° EPrimOp "recv_next" [])
                       (° EApp
                            (˝ VClos
                                 [(0, 0,
                                   ° ELet 2 (° EPrimOp "recv_peek_message" [])
                                       (° ECase (˝ VVar 0)
                                            [([PLit "true"], ˝ 
                                              VLit "true",
                                              ° ECase (˝ VVar 1)
                                                  [([PVar], ˝ 
                                                    VLit "true",
                                                    ° ESeq (° EPrimOp "remove_message" [])
                                                        (° ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [
                                                             ˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                   ([PVar], ˝ 
                                                    VLit "true",
                                                    ° ESeq (° EPrimOp "recv_next" [])
                                                        (° EApp (˝ VFunId (3, 0)) []))]);
                                             ([PLit "false"], ˝ 
                                              VLit "true",
                                              ° ELet 1
                                                  (° EPrimOp "recv_wait_timeout"
                                                       [˝ VLit "infinity"])
                                                  (° ECase (˝ VVar 0)
                                                       [([PLit "true"], ˝ 
                                                         VLit "true", ˝ VNil);
                                                        ([PLit "false"], ˝ 
                                                         VLit "true",
                                                         ° EApp (˝ VFunId (3, 0)) [])]))]))]
                                 0 0
                                 (° ELet 2 (° EPrimOp "recv_peek_message" [])
                                      (° ECase (˝ VVar 0)
                                           [([PLit "true"], ˝ 
                                             VLit "true",
                                             ° ECase (˝ VVar 1)
                                                 [([PVar], ˝ VLit "true",
                                                   ° ESeq (° EPrimOp "remove_message" [])
                                                       (° ECall 
                                                            (˝ VLit "erlang") 
                                                            (˝ VLit "!")
                                                            [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                  ([PVar], ˝ VLit "true",
                                                   ° ESeq (° EPrimOp "recv_next" [])
                                                       (° EApp (˝ VFunId (3, 0)) []))]);
                                            ([PLit "false"], ˝ 
                                             VLit "true",
                                             ° ELet 1
                                                 (° EPrimOp "recv_wait_timeout"
                                                      [˝ VLit "infinity"])
                                                 (° ECase (˝ VVar 0)
                                                      [([PLit "true"], ˝ 
                                                        VLit "true", ˝ VNil);
                                                       ([PLit "false"], ˝ 
                                                        VLit "true",
                                                        ° EApp (˝ VFunId (3, 0)) [])]))])))
                            []))]);
            ([PLit "false"], ˝ VLit "true",
             ° ELet 1 (° EPrimOp "recv_wait_timeout" [˝ VLit "infinity"])
                 (° ECase (˝ VVar 0)
                      [([PLit "true"], ˝ VLit "true", ˝ VNil);
                       ([PLit "false"], ˝ VLit "true",
                        ° EApp
                            (˝ VClos
                                 [(0, 0,
                                   ° ELet 2 (° EPrimOp "recv_peek_message" [])
                                       (° ECase (˝ VVar 0)
                                            [([PLit "true"], ˝ 
                                              VLit "true",
                                              ° ECase (˝ VVar 1)
                                                  [([PVar], ˝ 
                                                    VLit "true",
                                                    ° ESeq (° EPrimOp "remove_message" [])
                                                        (° ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [
                                                             ˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                   ([PVar], ˝ 
                                                    VLit "true",
                                                    ° ESeq (° EPrimOp "recv_next" [])
                                                        (° EApp (˝ VFunId (3, 0)) []))]);
                                             ([PLit "false"], ˝ 
                                              VLit "true",
                                              ° ELet 1
                                                  (° EPrimOp "recv_wait_timeout"
                                                       [˝ VLit "infinity"])
                                                  (° ECase (˝ VVar 0)
                                                       [([PLit "true"], ˝ 
                                                         VLit "true", ˝ VNil);
                                                        ([PLit "false"], ˝ 
                                                         VLit "true",
                                                         ° EApp (˝ VFunId (3, 0)) [])]))]))]
                                 0 0
                                 (° ELet 2 (° EPrimOp "recv_peek_message" [])
                                      (° ECase (˝ VVar 0)
                                           [([PLit "true"], ˝ 
                                             VLit "true",
                                             ° ECase (˝ VVar 1)
                                                 [([PVar], ˝ VLit "true",
                                                   ° ESeq (° EPrimOp "remove_message" [])
                                                       (° ECall 
                                                            (˝ VLit "erlang") 
                                                            (˝ VLit "!")
                                                            [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                  ([PVar], ˝ VLit "true",
                                                   ° ESeq (° EPrimOp "recv_next" [])
                                                       (° EApp (˝ VFunId (3, 0)) []))]);
                                            ([PLit "false"], ˝ 
                                             VLit "true",
                                             ° ELet 1
                                                 (° EPrimOp "recv_wait_timeout"
                                                      [˝ VLit "infinity"])
                                                 (° ECase (˝ VVar 0)
                                                      [([PLit "true"], ˝ 
                                                        VLit "true", ˝ VNil);
                                                       ([PLit "false"], ˝ 
                                                        VLit "true",
                                                        ° EApp (˝ VFunId (3, 0)) [])]))])))
                            [])]))])], RBox, ([], [meta_to_cons (map f (take idx l'))]),
   ∅, false) -⌈ repeat τ 34 ⌉->* inl
     ([FParams (ICall (VLit "erlang") (VLit "!")) [VPid ι] []], RValSeq [
      meta_to_cons (map f l')], emptyBox, ∅, false).
Proof.
  eapply lsstep. apply p_recv_peek_message_ok. reflexivity.
  eapply lsstep. apply p_local. constructor. reflexivity.
  simpl.
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. apply eval_step_case_match. reflexivity.
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. apply eval_step_case_true. simpl.
  rewrite idsubst_is_id_val. simpl.
  repeat rewrite closed_ignores_ren_val; auto with examples.
  repeat rewrite closed_ignores_sub_val; auto with examples.
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. constructor; auto with examples.
  eapply lsstep. apply p_local. apply eval_step_case_match. reflexivity.
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. apply eval_step_case_true. simpl.
  (* remove message from the mailbox *)
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_remove_message. by cbn.
  eapply lsstep. apply p_local. constructor.
  repeat rewrite closed_ignores_sub_val;  auto with examples.
  (* Reading configurations is easier from here *)
  (* evaluate send *)
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. constructor. congruence.
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. constructor.
  (* evaluate append *)
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. constructor.
  eapply lsstep. apply p_local. constructor. simpl.
  eapply lsstep. apply p_local. constructor. congruence.
  eapply lsstep. apply p_local. constructor; auto with examples.
  eapply lsstep. apply p_local. constructor. simpl.
  repeat rewrite closed_ignores_sub_val; auto with examples.
  eapply lsstep. apply p_local. constructor; auto with examples.
  eapply lsstep. apply p_local. econstructor.
  { (* evaluate the meta-theoretical simulated append *)
    simpl. cbn.
    rewrite eval_append_correct.
    rewrite <- map_app, take_drop. reflexivity.
  }
  apply lsrefl.
Qed.

(** The parent process waiting for the mapped first part of the list (with
    this part already in its mailbox) is bisimilar to the process that is
    about to send the result to `ι`. *)
Lemma bisim_helper : forall ι_base, ι_base <> ι -> (∅,
 ι_base
 ↦ inl
     ([FParams (IPrimOp "recv_peek_message") [] [];
       FLet 2
         (° ECase (˝ VVar 0)
              [([PLit "true"], ˝ VLit "true",
                ° ECase (˝ VVar 1)
                    [([PVar], ˝ VLit "true",
                      ° ESeq (° EPrimOp "remove_message" [])
                          (° ECall (˝ VLit "erlang") (˝ VLit "!")
                               [˝ VPid ι;
                                ° ECall (˝ VLit "erlang") (˝ VLit "++")
                                    [˝ VVar 0; ˝ meta_to_cons (map f (drop idx l'))]]));
                     ([PVar], ˝ VLit "true",
                      ° ESeq (° EPrimOp "recv_next" [])
                          (° EApp
                               (˝ VClos
                                    [(0, 0,
                                      ° ELet 2 (° EPrimOp "recv_peek_message" [])
                                          (° ECase (˝ VVar 0)
                                               [([PLit "true"], ˝ 
                                                 VLit "true",
                                                 ° ECase (˝ VVar 1)
                                                     [([PVar], ˝ 
                                                       VLit "true",
                                                       ° ESeq
                                                           (° EPrimOp "remove_message" [])
                                                           (° 
                                                            ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                      ([PVar], ˝ 
                                                       VLit "true",
                                                       ° ESeq 
                                                           (° EPrimOp "recv_next" [])
                                                           (° EApp (˝ VFunId (3, 0)) []))]);
                                                ([PLit "false"], ˝ 
                                                 VLit "true",
                                                 ° ELet 1
                                                     (° EPrimOp "recv_wait_timeout"
                                                          [˝ VLit "infinity"])
                                                     (° ECase 
                                                          (˝ VVar 0)
                                                          [([PLit "true"], ˝ 
                                                            VLit "true", ˝ VNil);
                                                           ([PLit "false"], ˝ 
                                                            VLit "true",
                                                            ° 
                                                            EApp (˝ VFunId (3, 0)) [])]))]))]
                                    0 0
                                    (° ELet 2 (° EPrimOp "recv_peek_message" [])
                                         (° ECase (˝ VVar 0)
                                              [([PLit "true"], ˝ 
                                                VLit "true",
                                                ° ECase (˝ VVar 1)
                                                    [([PVar], ˝ 
                                                      VLit "true",
                                                      ° ESeq
                                                          (° EPrimOp "remove_message" [])
                                                          (° ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                     ([PVar], ˝ 
                                                      VLit "true",
                                                      ° ESeq (° EPrimOp "recv_next" [])
                                                          (° EApp (˝ VFunId (3, 0)) []))]);
                                               ([PLit "false"], ˝ 
                                                VLit "true",
                                                ° ELet 1
                                                    (° EPrimOp "recv_wait_timeout"
                                                         [˝ VLit "infinity"])
                                                    (° ECase (˝ VVar 0)
                                                         [([PLit "true"], ˝ 
                                                           VLit "true", ˝ VNil);
                                                          ([PLit "false"], ˝ 
                                                           VLit "true",
                                                           ° EApp (˝ VFunId (3, 0)) [])]))])))
                               []))]);
               ([PLit "false"], ˝ VLit "true",
                ° ELet 1 (° EPrimOp "recv_wait_timeout" [˝ VLit "infinity"])
                    (° ECase (˝ VVar 0)
                         [([PLit "true"], ˝ VLit "true", ˝ VNil);
                          ([PLit "false"], ˝ VLit "true",
                           ° EApp
                               (˝ VClos
                                    [(0, 0,
                                      ° ELet 2 (° EPrimOp "recv_peek_message" [])
                                          (° ECase (˝ VVar 0)
                                               [([PLit "true"], ˝ 
                                                 VLit "true",
                                                 ° ECase (˝ VVar 1)
                                                     [([PVar], ˝ 
                                                       VLit "true",
                                                       ° ESeq
                                                           (° EPrimOp "remove_message" [])
                                                           (° 
                                                            ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                      ([PVar], ˝ 
                                                       VLit "true",
                                                       ° ESeq 
                                                           (° EPrimOp "recv_next" [])
                                                           (° EApp (˝ VFunId (3, 0)) []))]);
                                                ([PLit "false"], ˝ 
                                                 VLit "true",
                                                 ° ELet 1
                                                     (° EPrimOp "recv_wait_timeout"
                                                          [˝ VLit "infinity"])
                                                     (° ECase 
                                                          (˝ VVar 0)
                                                          [([PLit "true"], ˝ 
                                                            VLit "true", ˝ VNil);
                                                           ([PLit "false"], ˝ 
                                                            VLit "true",
                                                            ° 
                                                            EApp (˝ VFunId (3, 0)) [])]))]))]
                                    0 0
                                    (° ELet 2 (° EPrimOp "recv_peek_message" [])
                                         (° ECase (˝ VVar 0)
                                              [([PLit "true"], ˝ 
                                                VLit "true",
                                                ° ECase (˝ VVar 1)
                                                    [([PVar], ˝ 
                                                      VLit "true",
                                                      ° ESeq
                                                          (° EPrimOp "remove_message" [])
                                                          (° ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                     ([PVar], ˝ 
                                                      VLit "true",
                                                      ° ESeq (° EPrimOp "recv_next" [])
                                                          (° EApp (˝ VFunId (3, 0)) []))]);
                                               ([PLit "false"], ˝ 
                                                VLit "true",
                                                ° ELet 1
                                                    (° EPrimOp "recv_wait_timeout"
                                                         [˝ VLit "infinity"])
                                                    (° ECase (˝ VVar 0)
                                                         [([PLit "true"], ˝ 
                                                           VLit "true", ˝ VNil);
                                                          ([PLit "false"], ˝ 
                                                           VLit "true",
                                                           ° EApp (˝ VFunId (3, 0)) [])]))])))
                               [])]))])], RBox,
      ([], [meta_to_cons (map f (take idx l'))]), ∅, false) ∥ ∅) ~ᵇ
(∅,
 ι_base
 ↦ inl
     ([FParams (ICall (VLit "erlang") (VLit "!")) [VPid ι] []], RValSeq [
      meta_to_cons (map f l')], emptyBox, ∅, false) ∥ ∅) observing {[ι]}.
Proof.
  intros. constructor.
  2,4: intros; exists source, []; eexists; simpl; split; try by constructor.
  {
    (* parent receive primitives *)
    (* peek_message *)
    intros. destruct A'.
    intros. assert (ι0 = ι_base). {
      apply deconstruct_reduction in H0. destruct_hyps.
      put (lookup ι0 : ProcessPool -> _) on H0 as H'.
      setoid_rewrite lookup_insert_eq in H'. destruct (decide (ι0 = ι_base)).
      assumption.
      setoid_rewrite lookup_insert_ne in H'; auto. set_solver.
    }
    inv H0.
    1: { put (lookup ι_base : ProcessPool -> _) on H4 as H'.
      setoid_rewrite lookup_insert_eq in H'. inv H'.
      by inv H6.
    }
    2: { put (lookup ι_base : ProcessPool -> _) on H3 as H'.
      setoid_rewrite lookup_insert_eq in H'. inv H'.
      by inv H13.
    }
    put (lookup ι_base : ProcessPool -> _) on H3 as H'.
    setoid_rewrite lookup_insert_eq in H'. inv H'.
    assert (forall p, ι_base ↦ p ∥ Π = ι_base ↦ p ∥ ∅) as HM. {
      intros. apply map_eq. intros.
      put (lookup i : ProcessPool -> _) on H3 as H'.
      destruct (decide (i = ι_base)).
      * subst. by setoid_rewrite lookup_insert_eq.
      * setoid_rewrite lookup_insert_ne; auto.
        setoid_rewrite lookup_insert_ne in H'; auto.
    }
    rewrite HM in *. clear HM. clear H3.
    destruct_or! H9; subst; inv H7.
    1: inv H6; by inv H7.
    (* peek_message_ok *)
    simpl in H5. inv H5.
    do 2 eexists. split. apply n_refl.
    eapply barbedBisim_trans.
    {
      (* silent steps *)
      eapply normalisation_τ_many_bisim. shelve.
      apply sequential_to_node.
      do 8 do_step_with_examples.
      all: repeat rewrite closed_ignores_sub_val; auto with examples.
      do 5 do_step_with_examples.
      constructor.
    }
    { (* removeMessage *)
      intros. constructor.
      2,4: intros; exists source, []; eexists; simpl; split; try by constructor.
      {
        intros. destruct A'.
        intros. assert (ι0 = ι_base). {
          apply deconstruct_reduction in H0. destruct_hyps.
          put (lookup ι0 : ProcessPool -> _) on H0 as H'.
          setoid_rewrite lookup_insert_eq in H'. destruct (decide (ι0 = ι_base)).
          assumption.
          setoid_rewrite lookup_insert_ne in H'; auto. set_solver.
        }
        inv H0.
        1: { put (lookup ι_base : ProcessPool -> _) on H4 as H'.
          setoid_rewrite lookup_insert_eq in H'. inv H'.
          by inv H6.
        }
        2: { put (lookup ι_base : ProcessPool -> _) on H3 as H'.
          setoid_rewrite lookup_insert_eq in H'. inv H'.
          by inv H13.
        }
        put (lookup ι_base : ProcessPool -> _) on H3 as H'.
        setoid_rewrite lookup_insert_eq in H'. inv H'.
        assert (forall p, ι_base ↦ p ∥ Π0 = ι_base ↦ p ∥ ∅) as HM. {
          intros. apply map_eq. intros.
          put (lookup i : ProcessPool -> _) on H3 as H'.
          destruct (decide (i = ι_base)).
          * subst. by setoid_rewrite lookup_insert_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in H'; auto.
        }
        rewrite HM in *. clear HM. clear H3.
        destruct_or! H9; subst; inv H7.
        1: inv H6; by inv H7.
        (* remove_message_ok *)
        simpl in H5. inv H5.
        do 2 eexists. split. apply n_refl.
        rewrite closed_ignores_sub_val; auto with examples.
        eapply normalisation_τ_many_bisim. shelve.
        apply sequential_to_node.
        do 16 do_step_with_examples; auto with examples.
        do 2 do_step_with_examples; auto with examples.
        econstructor 2. econstructor. cbn. rewrite eval_append_correct. reflexivity.
        rewrite <- map_app, take_drop.
        constructor.
      }
      {
        (* sequential send *)
        intros.
        intros. assert (ι0 = ι_base). {
          destruct B'.
          apply deconstruct_reduction in H0. destruct_hyps.
          put (lookup ι0 : ProcessPool -> _) on H0 as H'.
          setoid_rewrite lookup_insert_eq in H'. destruct (decide (ι0 = ι_base)).
          assumption.
          setoid_rewrite lookup_insert_ne in H'; auto. set_solver.
        }
        subst.
        assert (a = ASend ι_base ι (SMessage (meta_to_cons (map f l')))). {
          inv H0.
          * put (lookup ι_base : ProcessPool -> _) on H3 as P.
            setoid_rewrite lookup_insert_eq in P. inv P. by inv H6.
          * put (lookup ι_base : ProcessPool -> _) on H2 as P.
            setoid_rewrite lookup_insert_eq in P. inv P.
            destruct_or! H7; inv H3; try inv H10; cbn in *; try congruence.
          * put (lookup ι_base : ProcessPool -> _) on H2 as P.
            setoid_rewrite lookup_insert_eq in P. inv P.
            inv H11.
        }
        subst. inv H0. 2: { destruct_or! H7; congruence. }
        rename ι0 into ι_base.
        put (lookup ι_base : ProcessPool -> _) on H3 as P.
        setoid_rewrite lookup_insert_eq in P. inv P. inv H8.
        (* prs = ∅ *)
        assert (forall p, ι_base ↦ p ∥ prs = ι_base ↦ p ∥ ∅) as X. {
          intros.
          apply map_eq. intros. put (lookup i : ProcessPool -> _) on H3 as D.
          destruct (decide (i = ι_base)).
          * subst. by setoid_rewrite lookup_insert_eq.
          * setoid_rewrite lookup_insert_ne in D; auto.
            by setoid_rewrite lookup_insert_ne.
        }
        clear H3.
        (***)
        do 2 eexists. split.
        {
          (* parent remove_message
          *)
          eapply n_trans. apply n_other. apply p_remove_message. reflexivity. set_solver.
          simpl.
          rewrite closed_ignores_sub_val; auto with examples.
          eapply closureNodeSem_trans.
          {
            apply sequential_to_node.
            do 16 do_step_with_examples; auto with examples.
            do 2 do_step_with_examples; auto with examples.
            econstructor 2. econstructor. cbn. rewrite eval_append_correct. reflexivity.
            rewrite <- map_app, take_drop.
            constructor.
          }
          (* parent sends the result *)
          eapply n_trans. apply n_send. constructor.
          apply n_refl.
        }
        { (* equivalence - we need two helpers about dead processes and ether inserts *)
          rewrite X.
          apply barbedBisim_refl.
        }
      }
    }
  }
  {
    (* sequential send *)
    intros.
    intros. assert (ι0 = ι_base). {
      destruct B'.
      apply deconstruct_reduction in H0. destruct_hyps.
      put (lookup ι0 : ProcessPool -> _) on H0 as H'.
      setoid_rewrite lookup_insert_eq in H'. destruct (decide (ι0 = ι_base)).
      assumption.
      setoid_rewrite lookup_insert_ne in H'; auto. set_solver.
    }
    subst.
    assert (a = ASend ι_base ι (SMessage (meta_to_cons (map f l')))). {
      inv H0.
      * put (lookup ι_base : ProcessPool -> _) on H3 as P.
        setoid_rewrite lookup_insert_eq in P. inv P. by inv H6.
      * put (lookup ι_base : ProcessPool -> _) on H2 as P.
        setoid_rewrite lookup_insert_eq in P. inv P.
        destruct_or! H7; inv H3; try inv H10; cbn in *; try congruence.
      * put (lookup ι_base : ProcessPool -> _) on H2 as P.
        setoid_rewrite lookup_insert_eq in P. inv P.
        inv H11.
    }
    subst. inv H0. 2: { destruct_or! H7; congruence. }
    rename ι0 into ι_base.
    put (lookup ι_base : ProcessPool -> _) on H3 as P.
    setoid_rewrite lookup_insert_eq in P. inv P. inv H8.
    (* prs = ∅ *)
    assert (forall p, ι_base ↦ p ∥ prs = ι_base ↦ p ∥ ∅) as X. {
      intros.
      apply map_eq. intros. put (lookup i : ProcessPool -> _) on H3 as D.
      destruct (decide (i = ι_base)).
      * subst. by setoid_rewrite lookup_insert_eq.
      * setoid_rewrite lookup_insert_ne in D; auto.
        by setoid_rewrite lookup_insert_ne.
    }
    clear H3.
    (***)
    do 2 eexists. split.
    {
      (* parent message peek
      *)
      eapply closureNodeSem_trans.
      {
        eapply process_local_to_node.
        {
          apply eval_helper_peek_message.
        }
        {
          repeat constructor.
        }
      }
      (* parent sends the result *)
      eapply n_trans. apply n_send. constructor.
      apply n_refl.
    }
    { (* equivalence - we need two helpers about dead processes and ether inserts *)
      rewrite X.
      apply barbedBisim_refl.
    }
  }
Unshelve.
  all: by apply Forall_repeat.
Qed.


(** The PID of the process evaluating the implementations, which is not the
    observed PID. The equivalence is stated for a node that contains only
    this process, with an empty ether. This has implicit consequences:
    - only the spawned child process communicates with the parent, there are
      no other messages waiting to be processed by the parent;
    - since the ether is empty, errors (e.g., exit signals from other
      processes) are ruled out. *)
Context (ι_base : PID)
        (Hbase : ι_base <> ι).

Opaque eval_split.
Opaque seq_sec.
Opaque map_clos.
(** The parallel implementation evaluates to the point of spawning the
    child process with silent and `self` steps. *)
Theorem split_eval O :
  exists l,
    (∅, ι_base ↦ inl ([], par_map, emptyBox, ∅, false) ∥ ∅) -[l]ₙ->* 
    (∅, ι_base ↦ inl ([FParams (ICall erlang spawn) [VClos [] 0 2 send_body] [];FSeq seq_sec.[up_subst
                (meta_to_cons (take idx l') .: meta_to_cons (drop idx l') .: idsubst)].[
     VPid ι_base/] ], RValSeq [VCons (VPid ι_base) (VCons (meta_to_cons (take idx l')) VNil)], emptyBox, ∅, false) ∥ ∅) with O /\
    Forall (fun x => x.1 = τ \/ exists ι, x.1 = ASelf ι) l.
Proof.
  eexists. split.
  {
    eapply closureNodeSem_trans.
    * apply sequential_to_node.
      do 10 do_step_with_examples.
      econstructor 2. econstructor. reflexivity. simpl.
      unfold eval_transform_list. simpl.
      erewrite eval_split_correct. 2-3: eassumption.
      do 9 do_step_with_examples.
      rewrite closed_ignores_sub_val; auto with examples.
      rewrite closed_ignores_sub_val; auto with examples.
      constructor.
    * eapply n_trans. apply n_other with (ι := ι_base) (a := ASelf ι_base).
      2: set_solver.
      constructor.
      apply sequential_to_node.
      do 11 do_step_with_examples.
      rewrite closed_ignores_sub_val; auto with examples.
      rewrite closed_ignores_sub_val; auto with examples.
      rewrite closed_ignores_ren_val; auto with examples.
      do 4 do_step_with_examples; auto with examples.
      rewrite closed_ignores_sub_val; auto with examples.
      do 4 do_step_with_examples; auto with examples.
      constructor.
  }
  {
    apply Forall_app. split. 2: constructor.
    1, 3: by apply Forall_repeat; left.
    right. by eexists.
  }
Qed.
Transparent eval_split.
Transparent seq_sec.


(** The sequential implementation: `ι ! map(F, L)`. *)
Definition map_seq_send :Exp :=
  °ECall (˝erlang) (˝send)
       [
        ˝VPid ι;
        °EApp (˝@map_clos ident) [˝f_clos; ˝l]
       ].

Opaque receive.
(** The sequential and the parallel implementations of `map` are barbed
    bisimilar, observing `ι`. *)
(* NOTE: coercions start to tangle up here for parsing *)
Theorem map_pmap_empty_context_bisim :
  (∅, ι_base ↦ inl ([], RExp (map_seq_send), emptyBox, ∅, false) ∥ ∅) ~ᵇ
  (∅, ι_base ↦ inl ([], par_map, emptyBox, ∅, false) ∥ ∅) observing {[ι]}.
Proof.
  opose proof* (@map_clos_eval l l' ident f f_clos).
  all:try assumption.
  destruct H as [mapₖ [Hres HD]].
  pose proof split_eval {[ι]}. destruct H as [pmapₗ [HD2 Hₗ]].
  eapply barbedBisim_trans.
  eapply normalisation_τ_many_bisim.
  2: {
    apply sequential_to_node.
    do 8 do_step_with_examples.
    eapply frame_indep_core in HD.
    exact HD.
  }
  1: by apply Forall_repeat.
  simpl.
  eapply barbedBisim_trans.
  2: {
    apply barbedBisim_sym. eapply silent_steps_bisim.
    2: exact HD2.
    1: assumption.
  }
  constructor.
  2,4: intros; exists source, []; eexists; simpl; split; try by constructor.
  { (* sequential process gets a signal (which can only be a send)
       In this case, the entire concurrent map has to be evaluated!
     *)
    intros. assert (ι0 = ι_base). {
      destruct A'.
      apply deconstruct_reduction in H. destruct_hyps.
      put (lookup ι0 : ProcessPool -> _) on H as H'.
      setoid_rewrite lookup_insert_eq in H'. destruct (decide (ι0 = ι_base)).
      assumption.
      setoid_rewrite lookup_insert_ne in H'; auto. set_solver.
    }
    subst.
    assert (a = ASend ι_base ι (SMessage (meta_to_cons (map f l')))). {
      inv H.
      * put (lookup ι_base : ProcessPool -> _) on H2 as P.
        setoid_rewrite lookup_insert_eq in P. inv P. by inv H5.
      * put (lookup ι_base : ProcessPool -> _) on H1 as P.
        setoid_rewrite lookup_insert_eq in P. inv P.
        destruct_or! H6; inv H2; try inv H9; cbn in *; try congruence.
      * put (lookup ι_base : ProcessPool -> _) on H1 as P.
        setoid_rewrite lookup_insert_eq in P. inv P.
        inv H2. inv H10.
    }
    subst. inv H. 2: { destruct_or! H6; congruence. }
    rename ι0 into ι_base.
    put (lookup ι_base : ProcessPool -> _) on H2 as P.
    setoid_rewrite lookup_insert_eq in P. inv P. inv H7. 
    (* prs = ∅ *)
    assert (forall p, ι_base ↦ p ∥ prs = ι_base ↦ p ∥ ∅) as X. {
      intros.
      apply map_eq. intros. put (lookup i : ProcessPool -> _) on H2 as D.
      destruct (decide (i = ι_base)).
      * subst. by setoid_rewrite lookup_insert_eq.
      * setoid_rewrite lookup_insert_ne in D; auto.
        by setoid_rewrite lookup_insert_ne.
    }
    clear H2.
    (* To be able to use eexists, we need to pose map evaluation first! *)
    opose proof* (@map_clos_eval (meta_to_cons (take idx l')) (take idx l') ident f f_clos) as InitEval.
    all: try eassumption; auto with examples.
    1: {
      intros. apply f_simulates. pose proof subseteq_take idx l'. set_solver.
    }
    1: apply meta_to_cons_mk_list.
    opose proof* (@map_clos_eval (meta_to_cons (drop idx l')) (drop idx l') ident f f_clos) as TailEval.
    all: try eassumption; auto with examples.
    1: {
      intros. apply f_simulates. pose proof subseteq_drop idx l'. set_solver.
    }
    1: apply meta_to_cons_mk_list.
    destruct InitEval as [Initₖ [InitRes InitEval]].
    destruct TailEval as [Tailₖ [TailRes TailEval]].
    (**)
    do 2 eexists. split.
    {
      (* reductions *)
      eapply n_trans.
      (* spawning the new process *)
      pose proof (infinite_is_fresh (ι :: ι_base :: elements (usedPIDsVal f_clos))) as HF.
      eapply n_spawn with (ι := ι_base) (ι' := fresh ([ι; ι_base] ++ (elements (usedPIDsVal f_clos)))%list).
      2: { clear-HF. set_solver. }
      2: {
         (* revise fresh generation on the ether + pool! that will 
                  also be future proof for general ethers *)
          intro. apply isUsedPool_insert_1 in H. destruct_or!.
          * setoid_rewrite delete_empty in H.
            destruct H. set_solver. destruct_hyps. set_solver.
          * pose proof (infinite_is_fresh (ι :: ι_base :: elements (usedPIDsVal f_clos))). set_solver.
          * unfold usedPIDsProc in H. cbn in H.
            rewrite closed_ignores_sub_val in H; auto with examples.
            rewrite closed_ignores_sub_val in H; auto with examples.
Transparent receive.
Transparent map_clos.
            unfold map_clos, map_body in H. simpl in *.
            rewrite closed_ignores_sub_val in H; auto with examples.
            rewrite closed_ignores_sub_val in H; auto with examples.
            rewrite closed_ignores_ren_val in H; auto with examples.
            rewrite closed_ignores_sub_val in H; auto with examples.
            assert (usedPIDsVal (meta_to_cons (take idx l')) = ∅). {
              clear -l_is_free_of_PIDs. revert l' l_is_free_of_PIDs.
              induction idx; intros; destruct l'; simpl.
              1-3: set_solver.
              cbn in *. set_solver.
            }
            assert (usedPIDsVal (meta_to_cons (drop idx l')) = ∅). {
              clear -l_is_free_of_PIDs. revert l' l_is_free_of_PIDs.
              induction idx; intros; destruct l'; simpl.
              1-3: set_solver.
              cbn in *. set_solver.
            }
            rewrite H0, H1 in H.
            clear-H.
            pose proof (infinite_is_fresh (ι :: ι_base :: elements (usedPIDsVal f_clos))).
            set_solver.
Opaque receive.
Opaque map_clos.
      }
      2: {
        (* revise fresh generation on the ether + pool! that will 
                  also be future proof for general ethers *)
        clear. intro. destruct H. 2: destruct H.
        * destruct H, H. set_solver.
        * destruct H. set_solver.
        * destruct_hyps. set_solver.
      }
      3: {
        constructor. reflexivity.
      }
      1: {
        simpl. reflexivity.
      }
      1: {
        simpl. reflexivity.
      }
      rewrite closed_ignores_sub_val; auto with examples.
      rewrite closed_ignores_sub_val; auto with examples.
      (* map is evaluated in the spawned process *)
      eapply closureNodeSem_trans.
      {
        apply sequential_to_node.
        do 8 do_step_with_examples.
        eapply frame_indep_core in InitEval.
        exact InitEval.
      }
      simpl.
      repeat rewrite (closed_ignores_sub_val map_clos); auto with examples.
      repeat rewrite (closed_ignores_sub_val f_clos); auto with examples.
      repeat rewrite closed_ignores_ren_val; auto with examples.
      (* map is sent back to the parent *)
      eapply n_trans. eapply n_send. constructor; auto with examples.
      (* map arrives to the parent *)
      setoid_rewrite insert_insert_ne.
      2: {
        pose proof (infinite_is_fresh (ι :: ι_base :: elements (usedPIDsVal f_clos))).
        set_solver.
      }
      eapply n_trans. apply n_arrive with (ι0 := fresh (ι :: ι_base :: elements (usedPIDsVal f_clos))).
      {
        unfold etherAdd, etherPop.
        setoid_rewrite lookup_empty.
        setoid_rewrite lookup_insert_eq.
        setoid_rewrite lookup_empty.
        setoid_rewrite insert_insert_eq.
        reflexivity.
      }
      {
        constructor.
      }
      (* parent evaluates the map *)
      eapply closureNodeSem_trans.
      {
        apply sequential_to_node.
        do 2 do_step_with_examples.
        rewrite closed_ignores_sub_val; auto with examples.
        eapply frame_indep_core in TailEval.
        eapply transitive_eval. exact TailEval.
        simpl. do_step_with_examples.
        constructor.
      }
      (* parent receives the first part of the map
        This is painful :(
      *)
      eapply closureNodeSem_trans.
      {
        eapply process_local_to_node.
        {
  Transparent receive.
          unfold receive, EReceive, rename_clauses. simpl.
          repeat rewrite closed_ignores_ren_val; auto with examples.
          eapply lsstep. constructor. constructor. cbn. reflexivity.
          cbn.
          eapply lsstep. do 2 constructor.
          eapply lsstep. do 2 constructor.
          eapply lsstep. do 2 constructor.
          eapply lsstep. apply p_local. econstructor. congruence. reflexivity.
          simpl.
          eapply lsstep. apply p_local. constructor.
          eapply lsstep. apply p_local. constructor.
          repeat rewrite closed_ignores_ren_val; auto with examples.
          repeat rewrite closed_ignores_sub_val; auto with examples.
          apply eval_helper_peek_message.
        }
        {
          repeat constructor.
        }
      }
      (* parent sends the result *)
      eapply n_trans. apply n_send. constructor.
      (* the child process should be terminated for the equivalence *)
      setoid_rewrite insert_insert_ne.
      2: {
        clear. pose proof (infinite_is_fresh (ι :: ι_base :: elements (usedPIDsVal f_clos))).
        set_solver.
      }
      eapply n_trans. apply n_other. apply p_terminate. by clear; set_solver.
      setoid_rewrite gset_to_gmap_empty.
      apply n_refl.
    }
    { (* equivalence - we need two helpers about dead processes and ether inserts *)
      rewrite X.
      eapply barbedBisim_trans.
      apply terminated_process_bisim with (ι := fresh (ι :: ι_base :: elements (usedPIDsVal f_clos))).
      1: clear; pose proof (infinite_is_fresh (ι :: ι_base :: elements (usedPIDsVal f_clos))); set_solver.
      1: clear; pose proof (infinite_is_fresh (ι :: ι_base :: elements (usedPIDsVal f_clos))); set_solver.
      simpl. (* now the pools are equal, we have to do the same for the ethers *)
      unfold etherAdd. setoid_rewrite lookup_empty.
      setoid_rewrite lookup_insert_ne.
      2: clear; pose proof (infinite_is_fresh (ι :: ι_base :: elements (usedPIDsVal f_clos))); set_solver.
      setoid_rewrite lookup_empty.
      setoid_rewrite insert_insert_ne at 2.
      2: clear; pose proof (infinite_is_fresh (ι :: ι_base :: elements (usedPIDsVal f_clos))); set_solver.
      remember (_ ↦ _ ∥ _ ↦ _ ∥ ∅) as P.
      setoid_rewrite <- HeqP.
      remember (insert (ι_base, ι) _ ∅) as E.
      apply ether_empty_update_bisim.
      clear-Hbase. set_solver.
      simpl. subst E. left.
      setoid_rewrite lookup_insert_ne. set_solver.
      set_solver.
    }
  }
  {
    Opaque receive.
    opose proof* (@map_clos_eval (meta_to_cons (take idx l')) (take idx l') ident f f_clos) as InitEval.
    all: try eassumption; auto with examples.
    1: {
      intros. apply f_simulates. pose proof subseteq_take idx l'. set_solver.
    }
    1: apply meta_to_cons_mk_list.
    opose proof* (@map_clos_eval (meta_to_cons (drop idx l')) (drop idx l') ident f f_clos) as TailEval.
    all: try eassumption; auto with examples.
    1: {
      intros. apply f_simulates. pose proof subseteq_drop idx l'. set_solver.
    }
    1: apply meta_to_cons_mk_list.
    destruct InitEval as [Initₖ [InitRes InitEval]].
    destruct TailEval as [Tailₖ [TailRes TailEval]].

    intros. eexists. exists []. split. eapply n_refl.
    intros. assert (ι0 = ι_base). {
      destruct B'.
      apply deconstruct_reduction in H. destruct_hyps.
      put (lookup ι0 : ProcessPool -> _) on H as H'.
      setoid_rewrite lookup_insert_eq in H'. destruct (decide (ι0 = ι_base)).
      assumption.
      setoid_rewrite lookup_insert_ne in H'; auto. set_solver.
    }
    subst.
    assert (exists ι_new, a = ASpawn ι_new (VClos [] 0 2 send_body) (VCons (VPid ι_base) (VCons (meta_to_cons (take idx l')) VNil)) false). {
      inv H.
      * put (lookup ι_base : ProcessPool -> _) on H2 as P.
        setoid_rewrite lookup_insert_eq in P. inv P. by inv H5.
      * put (lookup ι_base : ProcessPool -> _) on H1 as P.
        setoid_rewrite lookup_insert_eq in P. inv P.
        destruct_or! H6; inv H2; try inv H9; cbn in *; try congruence.
      * put (lookup ι_base : ProcessPool -> _) on H1 as P.
        setoid_rewrite lookup_insert_eq in P. inv P.
        inv H2. inv H10. by eexists.
    }
    destruct H0; subst. inv H. destruct_or! H6; congruence.
    put (lookup ι_base : ProcessPool -> _) on H1 as HX.
    setoid_rewrite lookup_insert_eq in HX. inv HX. simpl in *. inv H6.
    simpl in H12. inv H12.
    assert (forall p, ι_base ↦ p ∥ Π = ι_base ↦ p ∥ ∅) as X. {
      intros. apply map_eq. intros.
      put (lookup i : ProcessPool -> _) on H1 as X.
        destruct (decide (i = ι_base)).
        - subst. by setoid_rewrite lookup_insert_eq.
        - setoid_rewrite lookup_insert_ne; auto.
          by setoid_rewrite lookup_insert_ne in X.
    }
    rewrite X. rewrite X in H10.
    inv H13. clear H15.
    clear H1. clear HD2.
    assert (x ≠ ι_base) as Heqx. {
      intro. subst. apply H10.
      left. by setoid_rewrite lookup_insert_eq.
    }
    eapply barbedBisim_trans.
    2: {
      apply barbedBisim_sym.
      eapply normalisation_τ_many_bisim.
      1: shelve.
      eapply closureNodeSem_trans.
      { (* parent map *)
        eapply sequential_to_node.
        repeat rewrite (closed_ignores_sub_val); auto with examples.
        do 8 do_step_with_examples.
        eapply frame_indep_core in InitEval as InitEval'.
        simpl. apply InitEval'.
      }
      { (* child map *)
        setoid_rewrite insert_insert_ne; auto.
        eapply sequential_to_node.
        repeat rewrite (closed_ignores_sub_val); auto with examples.
        2: repeat rewrite closed_ignores_ren_val; auto with examples.
        do 2 do_step_with_examples.
        repeat rewrite closed_ignores_ren_val; auto with examples.
        eapply frame_indep_core in TailEval as TailEval'.
        eapply transitive_eval.
        apply TailEval'.
        simpl. do 4 do_step_with_examples.
        do_step_with_examples.
        repeat rewrite (closed_ignores_sub_val); auto with examples.
        econstructor 2. econstructor. congruence. reflexivity.
        repeat rewrite (closed_ignores_sub_val); auto with examples.
        repeat rewrite (closed_ignores_ren_val); auto with examples.
        simpl. do_step_with_examples.
        repeat rewrite (closed_ignores_sub_val); auto with examples.
        repeat rewrite (closed_ignores_ren_val); auto with examples.
        do_step_with_examples. constructor 1.
      }
    }
    (* child send - we have to reason about this with the definition of bisim.
       it would be simpler to use simulation equivalence, since again we have to
       prove both directions
     *)
    rewrite (closed_ignores_sub_val) in H10; auto with examples.
    rewrite (closed_ignores_sub_val) in H10; auto with examples.
    rewrite (closed_ignores_sub_val) in H10; auto with examples.
    rewrite (closed_ignores_sub_val) in H10; auto with examples.
    rewrite (closed_ignores_ren_val) in H10; auto with examples.
    rewrite (closed_ignores_sub_val) in H10; auto with examples.
    constructor.
    2,4: intros; exists source, []; eexists; simpl; split; try by constructor.
    * (* -> direction, we have already proved this *)
      intros. assert (ι0 = ι_base). {
        destruct A'.
        apply deconstruct_reduction in H. destruct_hyps.
        put (lookup ι0 : ProcessPool -> _) on H as H'.
        setoid_rewrite lookup_insert_eq in H'. destruct (decide (ι0 = ι_base)).
        assumption.
        setoid_rewrite lookup_insert_ne in H'; auto. set_solver.
      }
      subst.
      assert (a = ASend ι_base ι (SMessage (meta_to_cons (map f l')))). {
        inv H.
        * put (lookup ι_base : ProcessPool -> _) on H2 as P.
          setoid_rewrite lookup_insert_eq in P. inv P. by inv H5.
        * put (lookup ι_base : ProcessPool -> _) on H1 as P.
          setoid_rewrite lookup_insert_eq in P. inv P.
          destruct_or! H6; inv H2; try inv H12; cbn in *; try congruence.
        * put (lookup ι_base : ProcessPool -> _) on H1 as P.
          setoid_rewrite lookup_insert_eq in P. inv P.
          inv H2. inv H13.
      }
      subst. inv H. 2: { destruct_or! H6; congruence. }
      rename ι0 into ι_base.
      put (lookup ι_base : ProcessPool -> _) on H2 as P.
      setoid_rewrite lookup_insert_eq in P. inv P. inv H8.
      clear X.
      (* prs = ∅ *)
      assert (forall p, ι_base ↦ p ∥ prs = ι_base ↦ p ∥ ∅) as X. {
        intros.
        apply map_eq. intros. put (lookup i : ProcessPool -> _) on H2 as D.
        destruct (decide (i = ι_base)).
        * subst. by setoid_rewrite lookup_insert_eq.
        * setoid_rewrite lookup_insert_ne in D; auto.
          by setoid_rewrite lookup_insert_ne.
      }
      clear H2.
      (**)
      do 2 eexists. split.
      {
        (* reductions *)
        (* map is sent back to the parent *)
        setoid_rewrite insert_insert_ne; auto.
        eapply n_trans. eapply n_send. constructor; auto with examples.
        (* map arrives to the parent *)
        setoid_rewrite insert_insert_ne.
        2: {
          pose proof (infinite_is_fresh [ι; ι_base]).
          set_solver.
        }
        eapply n_trans. apply n_arrive with (ι0 := x).
        {
          unfold etherAdd, etherPop.
          setoid_rewrite lookup_empty.
          setoid_rewrite lookup_insert_eq.
          setoid_rewrite lookup_empty.
          setoid_rewrite insert_insert_eq.
          reflexivity.
        }
        {
          constructor.
        }
        (* parent message peek
        *)
        eapply closureNodeSem_trans.
        {
          eapply process_local_to_node.
          {
            apply eval_helper_peek_message.
          }
          {
            repeat constructor.
          }
        }
        (* parent sends the result *)
        eapply n_trans. apply n_send. constructor.
        (* the child process should be terminated for the equivalence *)
        setoid_rewrite insert_insert_ne.
        2: {
          set_solver.
        }
        eapply n_trans. apply n_other. apply p_terminate. by clear; set_solver.
        setoid_rewrite gset_to_gmap_empty.
        apply n_refl.
      }
      { (* equivalence - we need two helpers about dead processes and ether inserts *)
        rewrite X.
        eapply barbedBisim_trans.
        apply terminated_process_bisim with (ι := x).
        1-2: set_solver.
        simpl. (* now the pools are equal, we have to do the same for the ethers *)
        unfold etherAdd. setoid_rewrite lookup_empty.
        setoid_rewrite lookup_insert_ne.
        2: set_solver.
        setoid_rewrite lookup_empty.
        setoid_rewrite insert_insert_ne at 2.
        2: set_solver.
        remember (_ ↦ _ ∥ _ ↦ _ ∥ ∅) as P.
        setoid_rewrite <- HeqP.
        remember (insert (ι_base, ι) _ ∅) as E.
        apply ether_empty_update_bisim.
        clear-Hbase. set_solver.
        simpl. subst E. left.
        setoid_rewrite lookup_insert_ne. set_solver.
        set_solver.
      }




    * intros. simpl in *.
      (* parent could potentially peek the message queue, but the child can also
         do the message send - in both cases, we have to do the same reductions
         to finish the evaluation
       *)
      inv H.
      - (* send happens in the child *)
        put (lookup ι0 : ProcessPool -> _) on H2 as HX2.
        assert (ι0 <> ι_base). {
          intro. subst. setoid_rewrite lookup_insert_eq in HX2. inv HX2. inv H5.
        }
        setoid_rewrite lookup_insert_eq in HX2.
        setoid_rewrite lookup_insert_ne in HX2; auto.
        symmetry in HX2. apply lookup_insert_Some in HX2. destruct HX2 as [HX2 | HX2].
        2: { clear-HX2. set_solver. }
        destruct HX2 as [EQ1 EQ2]. inv EQ2.
        remember (inl (_, _, _, _, _)) as recp in H2 at 2.
        assert (forall p, ι0 ↦ p ∥ prs = ι0 ↦ p ∥ ι_base ↦ recp ∥ ∅) as XX. {
          intros. apply map_eq. intros.
          destruct (decide (i = ι0)).
          * subst. by setoid_rewrite lookup_insert_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            put (lookup i : ProcessPool -> _) on H2 as HX2.
            destruct (decide (i = ι_base)).
            - subst. setoid_rewrite lookup_insert_eq in HX2.
              setoid_rewrite lookup_insert_ne in HX2; auto.
              setoid_rewrite lookup_insert_eq. assumption.
            - setoid_rewrite lookup_insert_ne in HX2; auto.
              setoid_rewrite lookup_insert_ne in HX2; auto.
              setoid_rewrite lookup_insert_ne; auto.
        }
        rewrite XX in *. inv H5. clear XX H2.
        (* starting here, the same chain of thought has to be applied in the
           failing peek_message case too! *)
        eexists. exists []. split. apply n_refl.
        apply barbedBisim_sym.

        eapply barbedBisim_trans.
        {
          (* eapply normalisation_τ_many_bisim.
          1: shelve.
          1:{
            repeat setoid_rewrite dom_insert_L. set_solver.
          }
          apply process_local_to_node. 2: shelve.
          eapply lsstep. apply p_terminate. setoid_rewrite gset_to_gmap_empty.
          apply lsrefl. *)
          apply barbedBisim_sym.
          pose proof (almost_terminated_bisim {[ι]} (etherAdd ι0 ι' (SMessage (meta_to_cons (map f (take idx l')))) ∅, ι'
   ↦ inl
       ([FParams (IPrimOp "recv_peek_message") [] [];
         FLet 2
           (° ECase (˝ VVar 0)
                [([PLit "true"], ˝ VLit "true",
                  ° ECase (˝ VVar 1)
                      [([PVar], ˝ VLit "true",
                        ° ESeq (° EPrimOp "remove_message" [])
                            (° ECall (˝ VLit "erlang") (˝ VLit "!")
                                 [˝ VPid ι;
                                  ° ECall (˝ VLit "erlang") (˝ VLit "++")
                                      [˝ VVar 0; ˝ meta_to_cons (map f (drop idx l'))]]));
                       ([PVar], ˝ VLit "true",
                        ° ESeq (° EPrimOp "recv_next" [])
                            (° EApp
                                 (˝ VClos
                                      [(0, 0,
                                        ° ELet 2 (° EPrimOp "recv_peek_message" [])
                                            (° ECase (˝ VVar 0)
                                                 [([PLit "true"], ˝ 
                                                   VLit "true",
                                                   ° ECase (˝ VVar 1)
                                                       [([PVar], ˝ 
                                                         VLit "true",
                                                         ° ESeq
                                                             (° 
                                                             EPrimOp "remove_message" [])
                                                             (° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                        ([PVar], ˝ 
                                                         VLit "true",
                                                         ° ESeq 
                                                             (° EPrimOp "recv_next" [])
                                                             (° EApp (˝ VFunId (3, 0)) []))]);
                                                  ([PLit "false"], ˝ 
                                                   VLit "true",
                                                   ° ELet 1
                                                       (° EPrimOp "recv_wait_timeout"
                                                            [˝ 
                                                            VLit "infinity"])
                                                       (° ECase 
                                                            (˝ VVar 0)
                                                            [(
                                                             [
                                                             PLit "true"], ˝ 
                                                             VLit "true", ˝ VNil);
                                                             (
                                                             [
                                                             PLit "false"], ˝ 
                                                             VLit "true",
                                                             ° 
                                                             EApp (˝ VFunId (3, 0)) [])]))]))]
                                      0 0
                                      (° ELet 2 (° EPrimOp "recv_peek_message" [])
                                           (° ECase (˝ VVar 0)
                                                [([PLit "true"], ˝ 
                                                  VLit "true",
                                                  ° ECase (˝ VVar 1)
                                                      [([PVar], ˝ 
                                                        VLit "true",
                                                        ° ESeq
                                                            (° 
                                                             EPrimOp "remove_message" [])
                                                            (° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                       ([PVar], ˝ 
                                                        VLit "true",
                                                        ° ESeq 
                                                            (° EPrimOp "recv_next" [])
                                                            (° EApp (˝ VFunId (3, 0)) []))]);
                                                 ([PLit "false"], ˝ 
                                                  VLit "true",
                                                  ° ELet 1
                                                      (° EPrimOp "recv_wait_timeout"
                                                           [˝ 
                                                           VLit "infinity"])
                                                      (° ECase 
                                                           (˝ VVar 0)
                                                           [([
                                                             PLit "true"], ˝ 
                                                             VLit "true", ˝ VNil);
                                                            ([
                                                             PLit "false"], ˝ 
                                                             VLit "true",
                                                             ° 
                                                             EApp (˝ VFunId (3, 0)) [])]))])))
                                 []))]);
                 ([PLit "false"], ˝ VLit "true",
                  ° ELet 1 (° EPrimOp "recv_wait_timeout" [˝ VLit "infinity"])
                      (° ECase (˝ VVar 0)
                           [([PLit "true"], ˝ VLit "true", ˝ VNil);
                            ([PLit "false"], ˝ VLit "true",
                             ° EApp
                                 (˝ VClos
                                      [(0, 0,
                                        ° ELet 2 (° EPrimOp "recv_peek_message" [])
                                            (° ECase (˝ VVar 0)
                                                 [([PLit "true"], ˝ 
                                                   VLit "true",
                                                   ° ECase (˝ VVar 1)
                                                       [([PVar], ˝ 
                                                         VLit "true",
                                                         ° ESeq
                                                             (° 
                                                             EPrimOp "remove_message" [])
                                                             (° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                        ([PVar], ˝ 
                                                         VLit "true",
                                                         ° ESeq 
                                                             (° EPrimOp "recv_next" [])
                                                             (° EApp (˝ VFunId (3, 0)) []))]);
                                                  ([PLit "false"], ˝ 
                                                   VLit "true",
                                                   ° ELet 1
                                                       (° EPrimOp "recv_wait_timeout"
                                                            [˝ 
                                                            VLit "infinity"])
                                                       (° ECase 
                                                            (˝ VVar 0)
                                                            [(
                                                             [
                                                             PLit "true"], ˝ 
                                                             VLit "true", ˝ VNil);
                                                             (
                                                             [
                                                             PLit "false"], ˝ 
                                                             VLit "true",
                                                             ° 
                                                             EApp (˝ VFunId (3, 0)) [])]))]))]
                                      0 0
                                      (° ELet 2 (° EPrimOp "recv_peek_message" [])
                                           (° ECase (˝ VVar 0)
                                                [([PLit "true"], ˝ 
                                                  VLit "true",
                                                  ° ECase (˝ VVar 1)
                                                      [([PVar], ˝ 
                                                        VLit "true",
                                                        ° ESeq
                                                            (° 
                                                             EPrimOp "remove_message" [])
                                                            (° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                       ([PVar], ˝ 
                                                        VLit "true",
                                                        ° ESeq 
                                                            (° EPrimOp "recv_next" [])
                                                            (° EApp (˝ VFunId (3, 0)) []))]);
                                                 ([PLit "false"], ˝ 
                                                  VLit "true",
                                                  ° ELet 1
                                                      (° EPrimOp "recv_wait_timeout"
                                                           [˝ 
                                                           VLit "infinity"])
                                                      (° ECase 
                                                           (˝ VVar 0)
                                                           [([
                                                             PLit "true"], ˝ 
                                                             VLit "true", ˝ VNil);
                                                            ([
                                                             PLit "false"], ˝ 
                                                             VLit "true",
                                                             ° 
                                                             EApp (˝ VFunId (3, 0)) [])]))])))
                                 [])]))])], RBox, emptyBox, ∅, false) ∥ ∅)) as HH.
          apply HH; clear HH.                    (* TODO: bug? Direct 
                                                   apply does not work here*)

          (* Restriction is used here: PIDs cannot appear in the mapped
             list, because otherwise the helper lemma could not be used *)
          - simpl in *. split. 2: split.
            + intro Y. destruct Y as [ιs [l'' Y]].
              unfold etherAdd in Y. setoid_rewrite lookup_empty in Y.
              setoid_rewrite lookup_insert_ne in Y. 2: intro YY; inv YY; lia.
              by setoid_rewrite lookup_empty in Y.
            + intros * Y. unfold etherAdd in Y. setoid_rewrite lookup_empty in Y.
              apply lookup_insert_Some in Y as [[? ?]|].
              ** inv H0. simpl. by rewrite Hfmeta1.
              ** destruct H0. set_solver.
            + intros * Y. unfold etherAdd in Y. setoid_rewrite lookup_empty in Y.
              apply lookup_insert_Some in Y as [[? ?]|].
              ** inv H0. clear. set_solver.
              ** set_solver.
          - simpl in *. intro Y.
            apply isUsedPool_insert_1 in Y as [|[|]].
            + destruct H0. set_solver. destruct_hyps. set_solver.
            + congruence.
            + simpl in *.
              assert (usedPIDsVal (meta_to_cons (map f (drop idx l'))) = ∅). {
                apply Hfmeta2.
              }
              rewrite H1 in H0. set_solver.
          - assumption.
        }
      (* parent receives *)
      constructor.
      2,4: intros; exists source, []; eexists; simpl; split; try by constructor.
      (* etherAdd needs special care in this case *)
      2: {
        unfold etherAdd. simpl. setoid_rewrite lookup_empty.
        setoid_rewrite lookup_insert_ne. by setoid_rewrite lookup_empty.
        intro Y. inv Y. set_solver.
      }
      2: {
        unfold etherAdd. simpl. setoid_rewrite lookup_empty.
        setoid_rewrite lookup_insert_ne. by setoid_rewrite lookup_empty.
        intro Y. inv Y. set_solver.
      }
      (***)
      2: { (* Proved it already - to some extent *)
        intros. assert (ι1 = ι'). {
          destruct B'.
          apply deconstruct_reduction in H0. destruct_hyps.
          put (lookup ι1 : ProcessPool -> _) on H0 as H'.
          setoid_rewrite lookup_insert_eq in H'. destruct (decide (ι1 = ι')).
          assumption.
          setoid_rewrite lookup_insert_ne in H'; auto. set_solver.
        }
        subst.
        assert (a = ASend ι' ι (SMessage (meta_to_cons (map f l')))). {
          inv H0.
          * put (lookup ι' : ProcessPool -> _) on H3 as P.
            setoid_rewrite lookup_insert_eq in P. inv P. by inv H6.
          * put (lookup ι' : ProcessPool -> _) on H2 as P.
            setoid_rewrite lookup_insert_eq in P. inv P.
            destruct_or! H8; inv H3; try inv H13; cbn in *; try congruence.
          * put (lookup ι' : ProcessPool -> _) on H2 as P.
            setoid_rewrite lookup_insert_eq in P. inv P.
            inv H3. inv H14.
        }
        subst. inv H0. 2: { destruct_or! H8; congruence. }
        rename ι1 into ι'.
        put (lookup ι' : ProcessPool -> _) on H3 as P.
        setoid_rewrite lookup_insert_eq in P. inv P. inv H9.
        clear X.
        (* prs = ∅ *)
        assert (forall p, ι' ↦ p ∥ prs0 = ι' ↦ p ∥ ∅) as X. {
          intros.
          apply map_eq. intros. put (lookup i : ProcessPool -> _) on H3 as D.
          destruct (decide (i = ι')).
          * subst. by setoid_rewrite lookup_insert_eq.
          * setoid_rewrite lookup_insert_ne in D; auto.
            by setoid_rewrite lookup_insert_ne.
        }
        clear H3. rewrite X in *.
        (**)
        do 2 eexists. split.
        {
          (* reductions *)
          (* map arrives to the parent *)
          eapply n_trans. apply n_arrive with (ι0 := ι0).
          {
            unfold etherAdd, etherPop.
            setoid_rewrite lookup_empty.
            setoid_rewrite lookup_insert_eq.
            setoid_rewrite lookup_empty.
            setoid_rewrite insert_insert_eq.
            reflexivity.
          }
          {
            constructor.
          }
          (* parent message peek
          *)
          eapply closureNodeSem_trans.
          {
            eapply process_local_to_node.
            {
              apply eval_helper_peek_message.
            }
            {
              repeat constructor.
            }
          }
          (* parent sends the result *)
          eapply n_trans. apply n_send. constructor.
          apply n_refl.
        }
        { (* equivalence - we need two helpers about dead processes and ether inserts *)
          simpl. (* now the pools are equal, we have to do the same for the ethers *)
          unfold etherAdd. setoid_rewrite lookup_empty.
          setoid_rewrite lookup_insert_ne.
          2: set_solver.
          setoid_rewrite lookup_empty.
          remember (insert (ι', ι) _ ∅) as E.
          setoid_rewrite insert_insert_ne. 2: intro Y; inv Y; lia.
          apply barbedBisim_sym.
          setoid_rewrite HeqE.
          apply ether_empty_update_bisim.
          clear-Hbase. set_solver.
          simpl. subst E. left.
          setoid_rewrite lookup_insert_ne. set_solver.
          set_solver.
        }
      }

      {
        intros.
        inv H0.
        * put (lookup ι1 : ProcessPool -> _) on H3 as XX.
          setoid_rewrite lookup_insert_eq in XX.
          destruct (decide (ι' = ι1)).
          - subst. setoid_rewrite lookup_insert_eq in XX. inv XX.
            inv H6.
          - by setoid_rewrite lookup_insert_ne in XX.
        (* arrive *)
        * unfold etherPop, etherAdd in H3.
          setoid_rewrite lookup_empty in H3.
          destruct (decide ((ι0, ι') = (ι3, ι1))).
          2: {
            setoid_rewrite lookup_insert_ne in H3; auto.
            by setoid_rewrite lookup_empty in H3.
          }
          inv e. setoid_rewrite lookup_insert_eq in H3.
          setoid_rewrite lookup_empty in H3.
          setoid_rewrite insert_insert_eq in H3. inv H3.
          put (lookup ι1 : ProcessPool -> _) on H2 as HX1.
          setoid_rewrite lookup_insert_eq in HX1. inv HX1.
          assert (forall p, ι1 ↦ p ∥ prs0 = ι1 ↦ p ∥ ∅) as XX. {
            intros. apply map_eq. intros.
            put (lookup i : ProcessPool -> _) on H2 as HX2.
            destruct (decide (i = ι1)).
            * subst. by setoid_rewrite lookup_insert_eq.
            * setoid_rewrite lookup_insert_ne in HX2; auto.
              by setoid_rewrite lookup_insert_ne.
          }
          rewrite XX in *. clear XX H2.
          inv H8.
          eexists. exists []. split. apply n_refl.
          (* receive finished *)
          (* cleanup of empty ether update: *)
          eapply barbedBisim_trans.
          apply barbedBisim_sym.
          epose proof (ether_empty_update_bisim {[ι]} _ (∅,
ι1
 ↦ inl
     ([FParams (IPrimOp "recv_peek_message") [] [];
       FLet 2
         (° ECase (˝ VVar 0)
              [([PLit "true"], ˝ VLit "true",
                ° ECase (˝ VVar 1)
                    [([PVar], ˝ VLit "true",
                      ° ESeq (° EPrimOp "remove_message" [])
                          (° ECall (˝ VLit "erlang") (˝ VLit "!")
                               [˝ VPid ι;
                                ° ECall (˝ VLit "erlang") (˝ VLit "++")
                                    [˝ VVar 0; ˝ meta_to_cons (map f (drop idx l'))]]));
                     ([PVar], ˝ VLit "true",
                      ° ESeq (° EPrimOp "recv_next" [])
                          (° EApp
                               (˝ VClos
                                    [(0, 0,
                                      ° ELet 2 (° EPrimOp "recv_peek_message" [])
                                          (° ECase (˝ VVar 0)
                                               [([PLit "true"], ˝ 
                                                 VLit "true",
                                                 ° ECase (˝ VVar 1)
                                                     [([PVar], ˝ 
                                                       VLit "true",
                                                       ° ESeq
                                                           (° EPrimOp "remove_message" [])
                                                           (° 
                                                            ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                      ([PVar], ˝ 
                                                       VLit "true",
                                                       ° ESeq 
                                                           (° EPrimOp "recv_next" [])
                                                           (° EApp (˝ VFunId (3, 0)) []))]);
                                                ([PLit "false"], ˝ 
                                                 VLit "true",
                                                 ° ELet 1
                                                     (° EPrimOp "recv_wait_timeout"
                                                          [˝ VLit "infinity"])
                                                     (° ECase 
                                                          (˝ VVar 0)
                                                          [([PLit "true"], ˝ 
                                                            VLit "true", ˝ VNil);
                                                           ([PLit "false"], ˝ 
                                                            VLit "true",
                                                            ° 
                                                            EApp (˝ VFunId (3, 0)) [])]))]))]
                                    0 0
                                    (° ELet 2 (° EPrimOp "recv_peek_message" [])
                                         (° ECase (˝ VVar 0)
                                              [([PLit "true"], ˝ 
                                                VLit "true",
                                                ° ECase (˝ VVar 1)
                                                    [([PVar], ˝ 
                                                      VLit "true",
                                                      ° ESeq
                                                          (° EPrimOp "remove_message" [])
                                                          (° ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                     ([PVar], ˝ 
                                                      VLit "true",
                                                      ° ESeq (° EPrimOp "recv_next" [])
                                                          (° EApp (˝ VFunId (3, 0)) []))]);
                                               ([PLit "false"], ˝ 
                                                VLit "true",
                                                ° ELet 1
                                                    (° EPrimOp "recv_wait_timeout"
                                                         [˝ VLit "infinity"])
                                                    (° ECase (˝ VVar 0)
                                                         [([PLit "true"], ˝ 
                                                           VLit "true", ˝ VNil);
                                                          ([PLit "false"], ˝ 
                                                           VLit "true",
                                                           ° EApp (˝ VFunId (3, 0)) [])]))])))
                               []))]);
               ([PLit "false"], ˝ VLit "true",
                ° ELet 1 (° EPrimOp "recv_wait_timeout" [˝ VLit "infinity"])
                    (° ECase (˝ VVar 0)
                         [([PLit "true"], ˝ VLit "true", ˝ VNil);
                          ([PLit "false"], ˝ VLit "true",
                           ° EApp
                               (˝ VClos
                                    [(0, 0,
                                      ° ELet 2 (° EPrimOp "recv_peek_message" [])
                                          (° ECase (˝ VVar 0)
                                               [([PLit "true"], ˝ 
                                                 VLit "true",
                                                 ° ECase (˝ VVar 1)
                                                     [([PVar], ˝ 
                                                       VLit "true",
                                                       ° ESeq
                                                           (° EPrimOp "remove_message" [])
                                                           (° 
                                                            ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                      ([PVar], ˝ 
                                                       VLit "true",
                                                       ° ESeq 
                                                           (° EPrimOp "recv_next" [])
                                                           (° EApp (˝ VFunId (3, 0)) []))]);
                                                ([PLit "false"], ˝ 
                                                 VLit "true",
                                                 ° ELet 1
                                                     (° EPrimOp "recv_wait_timeout"
                                                          [˝ VLit "infinity"])
                                                     (° ECase 
                                                          (˝ VVar 0)
                                                          [([PLit "true"], ˝ 
                                                            VLit "true", ˝ VNil);
                                                           ([PLit "false"], ˝ 
                                                            VLit "true",
                                                            ° 
                                                            EApp (˝ VFunId (3, 0)) [])]))]))]
                                    0 0
                                    (° ELet 2 (° EPrimOp "recv_peek_message" [])
                                         (° ECase (˝ VVar 0)
                                              [([PLit "true"], ˝ 
                                                VLit "true",
                                                ° ECase (˝ VVar 1)
                                                    [([PVar], ˝ 
                                                      VLit "true",
                                                      ° ESeq
                                                          (° EPrimOp "remove_message" [])
                                                          (° ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "!")
                                                             [˝ 
                                                             VPid ι;
                                                             ° 
                                                             ECall 
                                                             (˝ VLit "erlang")
                                                             (˝ VLit "++")
                                                             [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                                     ([PVar], ˝ 
                                                      VLit "true",
                                                      ° ESeq (° EPrimOp "recv_next" [])
                                                          (° EApp (˝ VFunId (3, 0)) []))]);
                                               ([PLit "false"], ˝ 
                                                VLit "true",
                                                ° ELet 1
                                                    (° EPrimOp "recv_wait_timeout"
                                                         [˝ VLit "infinity"])
                                                    (° ECase (˝ VVar 0)
                                                         [([PLit "true"], ˝ 
                                                           VLit "true", ˝ VNil);
                                                          ([PLit "false"], ˝ 
                                                           VLit "true",
                                                           ° EApp (˝ VFunId (3, 0)) [])]))])))
                               [])]))])], RBox,
      mailboxPush emptyBox (meta_to_cons (map f (take idx l'))), ∅, false) ∥ ∅)) as Heth. simpl in Heth. eapply Heth.
          1-2: set_solver.
          (* same state *)
          by apply bisim_helper.
        * put (lookup ι1 : ProcessPool -> _) on H2 as XX.
          setoid_rewrite lookup_insert_eq in XX.
          destruct (decide (ι' = ι1)).
          2: {
            setoid_rewrite lookup_insert_ne in XX; auto. set_solver.
          }
          subst. setoid_rewrite lookup_insert_eq in XX. inv XX.
          destruct_or!; subst; inv H3. inv H9. inv H8.
          (* peeking can be done again, before receiving unfortunately :( *)
          (* technical steps are needed from below - labelled as
                    (* failing peek_message *) 
           *)
          assert (forall p, ι1 ↦ p ∥ Π0 = ι1 ↦ p ∥ ∅) as XX. {
            intros. apply map_eq. intros.
            destruct (decide (i = ι1)).
            * subst. by setoid_rewrite lookup_insert_eq.
            * setoid_rewrite lookup_insert_ne; auto.
              put (lookup i : ProcessPool -> _) on H2 as HX2.
              setoid_rewrite lookup_insert_ne in HX2; auto.
          }
          rewrite XX in *. clear H2.
          eexists. exists []. split. 1: apply n_refl.
          eapply barbedBisim_trans.
          {
            eapply normalisation_τ_many_bisim.
            1: shelve.
            apply process_local_to_node.
            2: shelve.
            eapply lsstep. eapply p_local. constructor. reflexivity. simpl.
            repeat rewrite (closed_ignores_sub_val); auto with examples.
            eapply lsstep. eapply p_local. constructor.
            eapply lsstep. eapply p_local. constructor.
            eapply lsstep. eapply p_local. apply eval_step_case_not_match. reflexivity.
            eapply lsstep. eapply p_local. apply eval_step_case_match. reflexivity.
            simpl.
            repeat rewrite (closed_ignores_sub_val); auto with examples.
            eapply lsstep. eapply p_local. constructor.
            eapply lsstep. eapply p_local. constructor.
            eapply lsstep. eapply p_local. constructor.
            eapply lsstep. eapply p_local. constructor.
            eapply lsstep. eapply p_local. constructor. congruence.
            eapply lsstep. eapply p_local. constructor.
            (* infinity timeout can only be reached, if something is in the mailbox *)
            apply lsrefl.
          }
          simpl.

          (* parent receives *)
          constructor.
          2,4: intros; exists source, []; eexists; simpl; split; try by constructor.
          (* etherAdd needs special care in this case *)
          2: {
            unfold etherAdd. simpl. setoid_rewrite lookup_empty.
            setoid_rewrite lookup_insert_ne. by setoid_rewrite lookup_empty.
            intro Y. inv Y. set_solver.
          }
          2: {
            unfold etherAdd. simpl. setoid_rewrite lookup_empty.
            setoid_rewrite lookup_insert_ne. by setoid_rewrite lookup_empty.
            intro Y. inv Y. set_solver.
          }
          (***)
          2: {
            (* Proved it already - to some extent *)
            intros. assert (ι1 = ι2). {
              destruct B'.
              apply deconstruct_reduction in H0. destruct_hyps.
              put (lookup ι2 : ProcessPool -> _) on H0 as H'.
              setoid_rewrite lookup_insert_eq in H'. destruct (decide (ι1 = ι2)).
              assumption.
              setoid_rewrite lookup_insert_ne in H'; auto. set_solver.
            }
            subst.
            assert (a = ASend ι2 ι (SMessage (meta_to_cons (map f l')))). {
              inv H0.
              * put (lookup ι2 : ProcessPool -> _) on H3 as P.
                setoid_rewrite lookup_insert_eq in P. inv P. by inv H6.
              * put (lookup ι2 : ProcessPool -> _) on H2 as P.
                setoid_rewrite lookup_insert_eq in P. inv P.
                destruct_or! H8; inv H3; try inv H13; cbn in *; try congruence.
              * put (lookup ι2 : ProcessPool -> _) on H2 as P.
                setoid_rewrite lookup_insert_eq in P. inv P.
                inv H14.
            }
            subst. inv H0. 2: { destruct_or! H8; congruence. }
            rename ι1 into ι2.
            put (lookup ι2 : ProcessPool -> _) on H3 as P.
            setoid_rewrite lookup_insert_eq in P. inv P. inv H9.
            clear X.
            (* prs = ∅ *)
            assert (forall p, ι2 ↦ p ∥ prs0 = ι2 ↦ p ∥ ∅) as X. {
              intros.
              apply map_eq. intros. put (lookup i : ProcessPool -> _) on H3 as D.
              destruct (decide (i = ι2)).
              * subst. by setoid_rewrite lookup_insert_eq.
              * setoid_rewrite lookup_insert_ne in D; auto.
                by setoid_rewrite lookup_insert_ne.
            }
            clear H3. rewrite X in *.
            (**)
            do 2 eexists. split.
            {
              (* reductions *)
              (* map arrives to the parent *)
              eapply n_trans. apply n_arrive with (ι0 := ι0).
              {
                unfold etherAdd, etherPop.
                setoid_rewrite lookup_empty.
                setoid_rewrite lookup_insert_eq.
                setoid_rewrite lookup_empty.
                setoid_rewrite insert_insert_eq.
                reflexivity.
              }
              {
                constructor.
              }
              (* parent recv_timeout then message peek
              *)
              eapply closureNodeSem_trans.
              {
                eapply process_local_to_node.
                {
                  (* recv_timeout *)
                  eapply lsstep. apply p_recv_wait_timeout_new_message.
                  eapply lsstep. apply p_local. constructor. reflexivity.
                  simpl. eapply lsstep. apply p_local. constructor.
                  repeat rewrite (closed_ignores_sub_val); auto with examples.
                  simpl. eapply lsstep. apply p_local. constructor.
                  eapply lsstep. apply p_local. apply eval_step_case_not_match. reflexivity.
                  eapply lsstep. apply p_local. apply eval_step_case_match. reflexivity.
                  eapply lsstep. apply p_local. constructor.
                  eapply lsstep. apply p_local. constructor.
                  simpl. repeat rewrite (closed_ignores_sub_val); auto with examples.
                  eapply lsstep. apply p_local. constructor.
                  eapply lsstep. apply p_local. constructor.
                  eapply lsstep. apply p_local. constructor.
                  eapply lsstep. apply p_local. econstructor. congruence. simpl. reflexivity.
                  simpl. repeat rewrite (closed_ignores_sub_val); auto with examples.
                  repeat rewrite (closed_ignores_ren_val); auto with examples.
                  eapply lsstep. apply p_local. constructor.
                  eapply lsstep. apply p_local. constructor.
                  (* message_peek *)
                  apply eval_helper_peek_message.
                }
                {
                  constructor. 2: repeat constructor.
                  by left.
                }
              }
              (* parent sends the result *)
              eapply n_trans. apply n_send. constructor.
              apply n_refl.
            }
            { (* equivalence - we need two helpers about dead processes and ether inserts *)
              simpl. (* now the pools are equal, we have to do the same for the ethers *)
              unfold etherAdd. setoid_rewrite lookup_empty.
              setoid_rewrite lookup_insert_ne.
              2: set_solver.
              setoid_rewrite lookup_empty.
              remember (insert (ι2, ι) _ ∅) as E.
              setoid_rewrite insert_insert_ne. 2: intro Y; inv Y; lia.
              apply barbedBisim_sym.
              setoid_rewrite HeqE.
              apply ether_empty_update_bisim.
              clear-Hbase. set_solver.
              simpl. subst E. left.
              setoid_rewrite lookup_insert_ne. set_solver.
              set_solver.
            }
          }



          {
            clear XX. intros.
            inv H0.
            * put (lookup ι2 : ProcessPool -> _) on H3 as XX.
              setoid_rewrite lookup_insert_eq in XX.
              destruct (decide (ι1 = ι2)).
              - subst. setoid_rewrite lookup_insert_eq in XX. inv XX.
                inv H6.
              - by setoid_rewrite lookup_insert_ne in XX.
            (* arrive *)
            * unfold etherPop, etherAdd in H3.
              setoid_rewrite lookup_empty in H3.
              destruct (decide ((ι0, ι1) = (ι4, ι2))).
              2: {
                setoid_rewrite lookup_insert_ne in H3; auto.
                by setoid_rewrite lookup_empty in H3.
              }
              inv e. setoid_rewrite lookup_insert_eq in H3.
              setoid_rewrite lookup_empty in H3.
              setoid_rewrite insert_insert_eq in H3. inv H3.
              put (lookup ι2 : ProcessPool -> _) on H2 as HX1.
              setoid_rewrite lookup_insert_eq in HX1. inv HX1.
              assert (forall p, ι2 ↦ p ∥ prs0 = ι2 ↦ p ∥ ∅) as XX. {
                intros. apply map_eq. intros.
                put (lookup i : ProcessPool -> _) on H2 as HX2.
                destruct (decide (i = ι2)).
                * subst. by setoid_rewrite lookup_insert_eq.
                * setoid_rewrite lookup_insert_ne in HX2; auto.
                  by setoid_rewrite lookup_insert_ne.
              }
              rewrite XX in *. clear XX H2.
              eexists. exists []. split. apply n_refl.
              inv H8.
              (* receive finished *)
              (* cleanup of empty ether update: *)
              eapply barbedBisim_trans.
              apply barbedBisim_sym.
              epose proof (ether_empty_update_bisim {[ι]} _ (∅,
 ι2
 ↦ inl
     ([FParams (IPrimOp "recv_wait_timeout") [] [];
       FLet 1
         (° ECase (˝ VVar 0)
              [([PLit "true"], ˝ VLit "true", ˝ VNil);
               ([PLit "false"], ˝ VLit "true",
                ° EApp
                    (˝ VClos
                         [(0, 0,
                           ° ELet 2 (° EPrimOp "recv_peek_message" [])
                               (° ECase (˝ VVar 0)
                                    [([PLit "true"], ˝ VLit "true",
                                      ° ECase (˝ VVar 1)
                                          [([PVar], ˝ VLit "true",
                                            ° ESeq (° EPrimOp "remove_message" [])
                                                (° ECall (˝ VLit "erlang") 
                                                     (˝ VLit "!")
                                                     [˝ VPid ι;
                                                      ° ECall 
                                                          (˝ VLit "erlang") 
                                                          (˝ VLit "++")
                                                          [˝ VVar 0;
                                                           ˝ meta_to_cons
                                                             (map f (drop idx l'))]]));
                                           ([PVar], ˝ VLit "true",
                                            ° ESeq (° EPrimOp "recv_next" [])
                                                (° EApp (˝ VFunId (3, 0)) []))]);
                                     ([PLit "false"], ˝ VLit "true",
                                      ° ELet 1
                                          (° EPrimOp "recv_wait_timeout"
                                               [˝ VLit "infinity"])
                                          (° ECase (˝ VVar 0)
                                               [([PLit "true"], ˝ VLit "true", ˝ VNil);
                                                ([PLit "false"], ˝ 
                                                 VLit "true", ° 
                                                 EApp (˝ VFunId (3, 0)) [])]))]))] 0 0
                         (° ELet 2 (° EPrimOp "recv_peek_message" [])
                              (° ECase (˝ VVar 0)
                                   [([PLit "true"], ˝ VLit "true",
                                     ° ECase (˝ VVar 1)
                                         [([PVar], ˝ VLit "true",
                                           ° ESeq (° EPrimOp "remove_message" [])
                                               (° ECall (˝ VLit "erlang") 
                                                    (˝ VLit "!")
                                                    [˝ VPid ι;
                                                     ° ECall (˝ VLit "erlang")
                                                         (˝ VLit "++")
                                                         [˝ VVar 0;
                                                          ˝ meta_to_cons
                                                             (map f (drop idx l'))]]));
                                          ([PVar], ˝ VLit "true",
                                           ° ESeq (° EPrimOp "recv_next" [])
                                               (° EApp (˝ VFunId (3, 0)) []))]);
                                    ([PLit "false"], ˝ VLit "true",
                                     ° ELet 1
                                         (° EPrimOp "recv_wait_timeout"
                                              [˝ VLit "infinity"])
                                         (° ECase (˝ VVar 0)
                                              [([PLit "true"], ˝ VLit "true", ˝ VNil);
                                               ([PLit "false"], ˝ 
                                                VLit "true", ° 
                                                EApp (˝ VFunId (3, 0)) [])]))]))) [])])],
      RValSeq [VLit "infinity"], mailboxPush emptyBox (meta_to_cons (map f (take idx l'))), ∅,
      false) ∥ ∅)) as Heth. simpl in Heth. eapply Heth.
              1-2: set_solver.
              { (* next: wait timeout succeeds - again low level reasoning needed *)
                constructor.
                2,4: intros; exists source, []; eexists; simpl; split; try by constructor.
                2: { (* again, we proved this already to some extent *)
                    intros. assert (ι0 = ι2). {
                    destruct B'.
                    apply deconstruct_reduction in H0. destruct_hyps.
                    put (lookup ι0 : ProcessPool -> _) on H0 as H'.
                    setoid_rewrite lookup_insert_eq in H'. destruct (decide (ι0 = ι2)).
                    assumption.
                    setoid_rewrite lookup_insert_ne in H'; auto. set_solver.
                  }
                  subst.
                  assert (a = ASend ι2 ι (SMessage (meta_to_cons (map f l')))). {
                    inv H0.
                    * put (lookup ι2 : ProcessPool -> _) on H3 as P.
                      setoid_rewrite lookup_insert_eq in P. inv P. by inv H6.
                    * put (lookup ι2 : ProcessPool -> _) on H2 as P.
                      setoid_rewrite lookup_insert_eq in P. inv P.
                      destruct_or! H8; inv H3; try inv H13; cbn in *; try congruence.
                    * put (lookup ι2 : ProcessPool -> _) on H2 as P.
                      setoid_rewrite lookup_insert_eq in P. inv P.
                      inv H14.
                  }
                  subst. inv H0. 2: { destruct_or! H8; congruence. }
                  rename ι0 into ι2.
                  put (lookup ι2 : ProcessPool -> _) on H3 as P.
                  setoid_rewrite lookup_insert_eq in P. inv P. inv H9.
                  clear X.
                  (* prs = ∅ *)
                  assert (forall p, ι2 ↦ p ∥ prs1 = ι2 ↦ p ∥ ∅) as X. {
                    intros.
                    apply map_eq. intros. put (lookup i : ProcessPool -> _) on H3 as D.
                    destruct (decide (i = ι2)).
                    * subst. by setoid_rewrite lookup_insert_eq.
                    * setoid_rewrite lookup_insert_ne in D; auto.
                      by setoid_rewrite lookup_insert_ne.
                  }
                  clear H3. rewrite X in *.
                  (**)
                  do 2 eexists. split.
                  {
                    (* reductions *)
                    (* parent recv_timeout then message peek
                    *)
                    eapply closureNodeSem_trans.
                    {
                      eapply process_local_to_node.
                      {
                        (* recv_timeout *)
                        eapply lsstep. apply p_recv_wait_timeout_new_message.
                        eapply lsstep. apply p_local. constructor. reflexivity.
                        simpl. eapply lsstep. apply p_local. constructor.
                        repeat rewrite (closed_ignores_sub_val); auto with examples.
                        simpl. eapply lsstep. apply p_local. constructor.
                        eapply lsstep. apply p_local. apply eval_step_case_not_match. reflexivity.
                        eapply lsstep. apply p_local. apply eval_step_case_match. reflexivity.
                        eapply lsstep. apply p_local. constructor.
                        eapply lsstep. apply p_local. constructor.
                        simpl. repeat rewrite (closed_ignores_sub_val); auto with examples.
                        eapply lsstep. apply p_local. constructor.
                        eapply lsstep. apply p_local. constructor.
                        eapply lsstep. apply p_local. constructor.
                        eapply lsstep. apply p_local. econstructor. congruence. simpl. reflexivity.
                        simpl. repeat rewrite (closed_ignores_sub_val); auto with examples.
                        repeat rewrite (closed_ignores_ren_val); auto with examples.
                        eapply lsstep. apply p_local. constructor.
                        eapply lsstep. apply p_local. constructor.
                        (* message_peek *)
                        apply eval_helper_peek_message.
                      }
                      {
                        constructor. 2: repeat constructor.
                        by left.
                      }
                    }
                    (* parent sends the result *)
                    eapply n_trans. apply n_send. constructor.
                    apply n_refl.
                  }
                  { (* equivalence - we need two helpers about dead processes and ether inserts *)
                    simpl. (* now the pools are equal, we have to do the same for the ethers *)
                    unfold etherAdd. setoid_rewrite lookup_empty.
                    apply barbedBisim_refl.
                  }
                }
                intros. inv H0.
                * put (lookup ι0 : ProcessPool -> _) on H3 as XX.
                  setoid_rewrite lookup_insert_eq in XX.
                  destruct (decide (ι0 = ι2)).
                  - subst. setoid_rewrite lookup_insert_eq in XX. inv XX.
                    inv H6.
                  - by setoid_rewrite lookup_insert_ne in XX; auto.
                * put (lookup ι0 : ProcessPool -> _) on H2 as XX.
                  setoid_rewrite lookup_insert_eq in XX.
                  destruct (decide (ι0 = ι2)).
                  2: by setoid_rewrite lookup_insert_ne in XX; auto.
                  subst. setoid_rewrite lookup_insert_eq in XX. inv XX.
                  destruct_or! H8; subst; inv H3.
                  1: by inv H9.
                  assert (forall p, ι2 ↦ p ∥ Π1 = ι2 ↦ p ∥ ∅) as XXX. {
                    intros. apply map_eq. intros.
                    destruct (decide (i = ι2)).
                    * subst. by setoid_rewrite lookup_insert_eq.
                    * setoid_rewrite lookup_insert_ne; auto.
                      put (lookup i : ProcessPool -> _) on H2 as HX2.
                      by setoid_rewrite lookup_insert_ne in HX2; auto.
                  }
                  rewrite XXX in *. clear H2 XXX.
                  eexists. exists []. split. apply n_refl.
                  eapply barbedBisim_trans.
                  {
                    eapply normalisation_τ_many_bisim.
                    1: shelve.
                    apply sequential_to_node.
                    do 9 do_step_with_examples.
                    repeat rewrite (closed_ignores_sub_val); auto with examples.
                    do_step_with_examples. econstructor 2. econstructor. congruence. simpl. reflexivity.
                    repeat rewrite (closed_ignores_sub_val); auto with examples.
                    repeat rewrite (closed_ignores_ren_val); auto with examples.
                    do 2 do_step_with_examples.
                    constructor 1.
                  }
                  (* peek_message succeeds - this was done previously *)
                  by apply bisim_helper.
                * put (lookup ι0 : ProcessPool -> _) on H2 as XX.
                    setoid_rewrite lookup_insert_eq in XX.
                    destruct (decide (ι0 = ι2)).
                    - subst. setoid_rewrite lookup_insert_eq in XX. inv XX.
                      by inv H14.
                    - by setoid_rewrite lookup_insert_ne in XX.
                  }
             * put (lookup ι2 : ProcessPool -> _) on H2 as XX.
               setoid_rewrite lookup_insert_eq in XX.
               destruct (decide (ι2 = ι1)).
               - subst. setoid_rewrite lookup_insert_eq in XX. inv XX.
                 destruct_or! H8; subst; inv H3.
                 1: by inv H9.
               - by setoid_rewrite lookup_insert_ne in XX.
             * put (lookup ι2 : ProcessPool -> _) on H2 as XX.
               setoid_rewrite lookup_insert_eq in XX.
               destruct (decide (ι2 = ι1)).
               - subst. setoid_rewrite lookup_insert_eq in XX. inv XX.
                 by inv H14.
               - by setoid_rewrite lookup_insert_ne in XX.
          }
        * put (lookup ι1 : ProcessPool -> _) on H2 as XX.
          setoid_rewrite lookup_insert_eq in XX.
          destruct (decide (ι' = ι1)).
          - subst. setoid_rewrite lookup_insert_eq in XX. inv XX.
            by inv H14.
          - by setoid_rewrite lookup_insert_ne in XX.
        }

      - (* failing peek_message *)
        put (lookup ι0 : ProcessPool -> _) on H1 as HX1.
        setoid_rewrite lookup_insert_eq in HX1.
        destruct (decide (ι0 = ι_base)).
        2: {
          setoid_rewrite lookup_insert_ne in HX1; auto.
          setoid_rewrite lookup_insert_ne in HX1; auto. set_solver.
          intro. subst.
          setoid_rewrite lookup_insert_eq in HX1. inv HX1.
          destruct_or! H6; subst; inv H2. by inv H8.
        }
        subst. setoid_rewrite lookup_insert_eq in HX1. inv HX1.
        assert (forall p, ι_base ↦ p ∥ Π0 = ι_base ↦ p ∥ x ↦ inl
              ([FParams (ICall (VLit "erlang") (VLit "!")) [VPid ι_base] []],
               RValSeq [meta_to_cons (map f (take idx l'))], emptyBox, ∅, false) ∥ ∅) as XX. {
          intros. apply map_eq. intros.
          destruct (decide (i = ι_base)).
          * subst. by setoid_rewrite lookup_insert_eq.
          * setoid_rewrite lookup_insert_ne; auto.
            put (lookup i : ProcessPool -> _) on H1 as HX2.
            setoid_rewrite lookup_insert_ne in HX2; auto.
        }
        rewrite XX. clear H1.
        destruct_or! H6; subst; inv H2.
        1: inv H6; inv H5.
        1: inv H5.
        eexists. exists []. split. 1: apply n_refl.
        apply barbedBisim_sym. eapply barbedBisim_trans.
        {
          eapply normalisation_τ_many_bisim.
          1: shelve.
          apply process_local_to_node.
          2: shelve.
          eapply lsstep. eapply p_local. constructor. reflexivity. simpl.
          repeat rewrite (closed_ignores_sub_val); auto with examples.
          eapply lsstep. eapply p_local. constructor.
          eapply lsstep. eapply p_local. constructor.
          eapply lsstep. eapply p_local. apply eval_step_case_not_match. reflexivity.
          eapply lsstep. eapply p_local. apply eval_step_case_match. reflexivity.
          simpl.
          repeat rewrite (closed_ignores_sub_val); auto with examples.
          eapply lsstep. eapply p_local. constructor.
          eapply lsstep. eapply p_local. constructor.
          eapply lsstep. eapply p_local. constructor.
          eapply lsstep. eapply p_local. constructor.
          eapply lsstep. eapply p_local. constructor. congruence.
          eapply lsstep. eapply p_local. constructor.
          (* infinity timeout can only be reached, if something is in the mailbox *)
          apply lsrefl.
        }
        simpl.
        (* send happens in the child *)
        constructor.
        2,4: intros; exists source, []; eexists; simpl; split; try by constructor.
        2: {
          (* Proved it already - to some extent *)
          intros. assert (ι_base = ι0). {
            destruct B'.
            apply deconstruct_reduction in H. destruct_hyps.
            put (lookup ι0 : ProcessPool -> _) on H as H'.
            setoid_rewrite lookup_insert_eq in H'. destruct (decide (ι_base = ι0)).
            assumption.
            setoid_rewrite lookup_insert_ne in H'; auto. set_solver.
          }
          subst.
          assert (a = ASend ι0 ι (SMessage (meta_to_cons (map f l')))). {
            inv H.
            * put (lookup ι0 : ProcessPool -> _) on H2 as P.
              setoid_rewrite lookup_insert_eq in P. inv P. by inv H5.
            * put (lookup ι0 : ProcessPool -> _) on H1 as P.
              setoid_rewrite lookup_insert_eq in P. inv P.
              destruct_or! H6; inv H2; try inv H12; cbn in *; try congruence.
            * put (lookup ι0 : ProcessPool -> _) on H1 as P.
              setoid_rewrite lookup_insert_eq in P. inv P.
              inv H2. inv H13.
          }
          subst. inv H. 2: { destruct_or! H6; congruence. }
          rename ι1 into ι0.
          put (lookup ι0 : ProcessPool -> _) on H2 as P.
          setoid_rewrite lookup_insert_eq in P. inv P. inv H8.
          clear X.
          (* prs = ∅ *)
          assert (forall p, ι0 ↦ p ∥ prs = ι0 ↦ p ∥ ∅) as X. {
            intros.
            apply map_eq. intros. put (lookup i : ProcessPool -> _) on H2 as D.
            destruct (decide (i = ι0)).
            * subst. by setoid_rewrite lookup_insert_eq.
            * setoid_rewrite lookup_insert_ne in D; auto.
              by setoid_rewrite lookup_insert_ne.
          }
          clear H2. rewrite X in *.
          (**)
          do 2 eexists. split.
          {
            (* reductions *)
            (* map is sent back to the parent *)
            setoid_rewrite insert_insert_ne; auto.
            eapply n_trans. eapply n_send. constructor; auto with examples.
            (* map arrives to the parent *)
            setoid_rewrite insert_insert_ne; auto.
            (* parent receive message recv_timeout then message peek
            *)
            eapply n_trans. apply n_arrive with (ι0 := x).
            {
              unfold etherAdd, etherPop.
              setoid_rewrite lookup_empty.
              setoid_rewrite lookup_insert_eq.
              setoid_rewrite lookup_empty.
              setoid_rewrite insert_insert_eq.
              reflexivity.
            }
            {
              constructor.
            }
            eapply closureNodeSem_trans.
            {
              eapply process_local_to_node.
              {
                (* recv_timeout *)
                eapply lsstep. apply p_recv_wait_timeout_new_message.
                eapply lsstep. apply p_local. constructor. reflexivity.
                simpl. eapply lsstep. apply p_local. constructor.
                repeat rewrite (closed_ignores_sub_val); auto with examples.
                simpl. eapply lsstep. apply p_local. constructor.
                eapply lsstep. apply p_local. apply eval_step_case_not_match. reflexivity.
                eapply lsstep. apply p_local. apply eval_step_case_match. reflexivity.
                eapply lsstep. apply p_local. constructor.
                eapply lsstep. apply p_local. constructor.
                simpl. repeat rewrite (closed_ignores_sub_val); auto with examples.
                eapply lsstep. apply p_local. constructor.
                eapply lsstep. apply p_local. constructor.
                eapply lsstep. apply p_local. constructor.
                eapply lsstep. apply p_local. econstructor. congruence. simpl. reflexivity.
                simpl. repeat rewrite (closed_ignores_sub_val); auto with examples.
                repeat rewrite (closed_ignores_ren_val); auto with examples.
                eapply lsstep. apply p_local. constructor.
                eapply lsstep. apply p_local. constructor.
                (* message_peek *)
                apply eval_helper_peek_message.
              }
              {
                constructor. 2: repeat constructor.
                by left.
              }
            }
            (* parent sends the result *)
            eapply n_trans. apply n_send. constructor.
            (* child process should be terminated *)
            setoid_rewrite insert_insert_ne.
            2: {
              set_solver.
            }
            eapply n_trans. apply n_other. apply p_terminate. by clear; set_solver.
            setoid_rewrite gset_to_gmap_empty.
            apply n_refl.
          }
          { (* equivalence - we need two helpers about dead processes and ether inserts *)
            eapply barbedBisim_trans.
            apply barbedBisim_sym.
            pose proof (terminated_process_bisim {[ι]} (etherAdd ι0 ι (SMessage (meta_to_cons (map f l'))) (<[(x, ι0):=[]]> ∅), <[ι0:=inl ([], RValSeq [meta_to_cons (map f l')], emptyBox, ∅, false)]> ∅)) as XXX. (* again, direct apply won't work for some reason *)
            apply XXX.
            1: set_solver.
            1: set_solver.
            simpl. (* now the pools are equal, we have to do the same for the ethers *)
            unfold etherAdd. setoid_rewrite lookup_empty.
            setoid_rewrite lookup_insert_ne.
            2: set_solver.
            setoid_rewrite lookup_empty.
            setoid_rewrite insert_insert_ne.
            2: set_solver.
            remember (insert (ι0, ι) _ ∅) as E.
            apply barbedBisim_sym.
            apply ether_empty_update_bisim.
            clear-Hbase. set_solver.
            simpl. subst E. left.
            setoid_rewrite lookup_insert_ne. set_solver.
            set_solver.
          }
        }
        intros. inv H.
        + put (lookup ι0 : ProcessPool -> _) on H2 as HX2.
          assert (ι0 <> ι_base). {
            intro. subst. setoid_rewrite lookup_insert_eq in HX2. inv HX2. inv H5.
          }
          setoid_rewrite lookup_insert_eq in HX2.
          setoid_rewrite lookup_insert_ne in HX2; auto.
          symmetry in HX2. apply lookup_insert_Some in HX2. destruct HX2 as [HX2 | HX2].
          2: { clear-HX2. set_solver. }
          destruct HX2 as [EQ1 EQ2]. inv EQ2.
          remember (inl _) as recp in H2 at 2.
          assert (forall p, ι0 ↦ p ∥ prs = ι0 ↦ p ∥ ι_base ↦ recp ∥ ∅) as XXX. {
            intros. apply map_eq. intros.
            destruct (decide (i = ι0)).
            * subst. by setoid_rewrite lookup_insert_eq.
            * setoid_rewrite lookup_insert_ne; auto.
              put (lookup i : ProcessPool -> _) on H2 as HX2.
              destruct (decide (i = ι_base)).
              - subst. setoid_rewrite lookup_insert_eq in HX2.
                setoid_rewrite lookup_insert_ne in HX2; auto.
                setoid_rewrite lookup_insert_eq. assumption.
              - setoid_rewrite lookup_insert_ne in HX2; auto.
                setoid_rewrite lookup_insert_ne in HX2; auto.
                setoid_rewrite lookup_insert_ne; auto.
          }
          rewrite XXX in *. clear H2. inv H5.
          eexists. exists []. split. apply n_refl.
          (* child terminates *)
          eapply barbedBisim_trans.
          {
            apply barbedBisim_sym.
            pose proof (almost_terminated_bisim {[ι]} (etherAdd ι0 ι' (SMessage (meta_to_cons (map f (take idx l')))) ∅, ι'
   ↦ inl
       ([FParams (IPrimOp "recv_wait_timeout") [] [];
         FLet 1
           (° ECase (˝ VVar 0)
                [([PLit "true"], ˝ VLit "true", ˝ VNil);
                 ([PLit "false"], ˝ VLit "true",
                  ° EApp
                      (˝ VClos
                           [(0, 0,
                             ° ELet 2 (° EPrimOp "recv_peek_message" [])
                                 (° ECase (˝ VVar 0)
                                      [([PLit "true"], ˝ VLit "true",
                                        ° ECase (˝ VVar 1)
                                            [([PVar], ˝ VLit "true",
                                              ° ESeq (° EPrimOp "remove_message" [])
                                                  (° ECall (˝ VLit "erlang") 
                                                       (˝ VLit "!")
                                                       [˝ VPid ι;
                                                        ° ECall 
                                                            (˝ VLit "erlang")
                                                            (˝ VLit "++")
                                                            [˝ 
                                                             VVar 0;
                                                             ˝ 
                                                             meta_to_cons
                                                             (map f (drop idx l'))]]));
                                             ([PVar], ˝ VLit "true",
                                              ° ESeq (° EPrimOp "recv_next" [])
                                                  (° EApp (˝ VFunId (3, 0)) []))]);
                                       ([PLit "false"], ˝ VLit "true",
                                        ° ELet 1
                                            (° EPrimOp "recv_wait_timeout"
                                                 [˝ VLit "infinity"])
                                            (° ECase (˝ VVar 0)
                                                 [([PLit "true"], ˝ VLit "true", ˝ VNil);
                                                  ([PLit "false"], ˝ 
                                                   VLit "true",
                                                   ° EApp (˝ VFunId (3, 0)) [])]))]))] 0 0
                           (° ELet 2 (° EPrimOp "recv_peek_message" [])
                                (° ECase (˝ VVar 0)
                                     [([PLit "true"], ˝ VLit "true",
                                       ° ECase (˝ VVar 1)
                                           [([PVar], ˝ VLit "true",
                                             ° ESeq (° EPrimOp "remove_message" [])
                                                 (° ECall (˝ VLit "erlang") 
                                                      (˝ VLit "!")
                                                      [˝ VPid ι;
                                                       ° ECall 
                                                           (˝ VLit "erlang") 
                                                           (˝ VLit "++")
                                                           [˝ 
                                                            VVar 0;
                                                            ˝ 
                                                            meta_to_cons
                                                             (map f (drop idx l'))]]));
                                            ([PVar], ˝ VLit "true",
                                             ° ESeq (° EPrimOp "recv_next" [])
                                                 (° EApp (˝ VFunId (3, 0)) []))]);
                                      ([PLit "false"], ˝ VLit "true",
                                       ° ELet 1
                                           (° EPrimOp "recv_wait_timeout"
                                                [˝ VLit "infinity"])
                                           (° ECase (˝ VVar 0)
                                                [([PLit "true"], ˝ VLit "true", ˝ VNil);
                                                 ([PLit "false"], ˝ 
                                                  VLit "true", ° 
                                                  EApp (˝ VFunId (3, 0)) [])]))]))) [])])],
        RValSeq [VLit "infinity"], emptyBox, ∅, false) ∥ ∅)) as HH.
            apply HH; clear HH.
            - simpl in *. split. 2: split.
              + intro Y. destruct Y as [ιs [l'' Y]].
                unfold etherAdd in Y. setoid_rewrite lookup_empty in Y.
                setoid_rewrite lookup_insert_ne in Y. 2: intro YY; inv YY; lia.
                by setoid_rewrite lookup_empty in Y.
              + intros * Y. unfold etherAdd in Y. setoid_rewrite lookup_empty in Y.
                apply lookup_insert_Some in Y as [[? ?]|].
                ** inv H0. simpl. by rewrite Hfmeta1.
                ** destruct H0. set_solver.
              + intros * Y. unfold etherAdd in Y. setoid_rewrite lookup_empty in Y.
                apply lookup_insert_Some in Y as [[? ?]|].
                ** inv H0. clear. set_solver.
                ** set_solver.
            - simpl in *. intro Y.
              apply isUsedPool_insert_1 in Y as [|[|]].
              + destruct H0. set_solver. destruct_hyps. set_solver.
              + congruence.
              + simpl in *.
                assert (usedPIDsVal (meta_to_cons (map f (drop idx l'))) = ∅). {
                  apply Hfmeta2.
                }
                rewrite H1 in H0. clear -H7 H0 Heqx. set_solver.
            - assumption.
          }
          (* parent receives *)
          constructor.
          (* etherAdd needs special care in this case *)
          2,4: intros; exists source, []; eexists; simpl; split; try by constructor.
          2: {
            unfold etherAdd. simpl. setoid_rewrite lookup_empty.
            setoid_rewrite lookup_insert_ne. by setoid_rewrite lookup_empty.
            intro Y. inv Y. set_solver.
          }
          2: {
            unfold etherAdd. simpl. setoid_rewrite lookup_empty.
            setoid_rewrite lookup_insert_ne. by setoid_rewrite lookup_empty.
            intro Y. inv Y. set_solver.
          }
          (***)
          2: {
            (* again, we proved this already to some extent *)
            intros. assert (ι' = ι1). {
              destruct B'.
              apply deconstruct_reduction in H0. destruct_hyps.
              put (lookup ι1 : ProcessPool -> _) on H0 as H'.
              setoid_rewrite lookup_insert_eq in H'. destruct (decide (ι' = ι1)).
              assumption.
              setoid_rewrite lookup_insert_ne in H'; auto. set_solver.
            }
            subst.
            assert (a = ASend ι1 ι (SMessage (meta_to_cons (map f l')))). {
              inv H0.
              * put (lookup ι1 : ProcessPool -> _) on H3 as P.
                setoid_rewrite lookup_insert_eq in P. inv P. by inv H6.
              * put (lookup ι1 : ProcessPool -> _) on H2 as P.
                setoid_rewrite lookup_insert_eq in P. inv P.
                destruct_or! H8; inv H3; try inv H13; cbn in *; try congruence.
              * put (lookup ι1 : ProcessPool -> _) on H2 as P.
                setoid_rewrite lookup_insert_eq in P. inv P.
                by inv H14.
            }
            subst. inv H0. 2: { destruct_or! H8; congruence. }
            rename ι2 into ι1.
            put (lookup ι1 : ProcessPool -> _) on H3 as P.
            setoid_rewrite lookup_insert_eq in P. inv P. inv H9.
            clear X.
            (* prs = ∅ *)
            assert (forall p, ι1 ↦ p ∥ prs0 = ι1 ↦ p ∥ ∅) as X. {
              intros.
              apply map_eq. intros. put (lookup i : ProcessPool -> _) on H3 as D.
              destruct (decide (i = ι1)).
              * subst. by setoid_rewrite lookup_insert_eq.
              * setoid_rewrite lookup_insert_ne in D; auto.
                by setoid_rewrite lookup_insert_ne.
            }
            clear H3. rewrite X in *.
            (**)
            do 2 eexists. split.
            {
              (* reductions *)
              (* parent receive message recv_timeout then message peek
              *)
              eapply n_trans. apply n_arrive with (ι0 := ι0).
              {
                unfold etherAdd, etherPop.
                setoid_rewrite lookup_empty.
                setoid_rewrite lookup_insert_eq.
                setoid_rewrite lookup_empty.
                setoid_rewrite insert_insert_eq.
                reflexivity.
              }
              {
                constructor.
              }
              eapply closureNodeSem_trans.
              {
                eapply process_local_to_node.
                {
                  (* recv_timeout *)
                  eapply lsstep. apply p_recv_wait_timeout_new_message.
                  eapply lsstep. apply p_local. constructor. reflexivity.
                  simpl. eapply lsstep. apply p_local. constructor.
                  repeat rewrite (closed_ignores_sub_val); auto with examples.
                  simpl. eapply lsstep. apply p_local. constructor.
                  eapply lsstep. apply p_local. apply eval_step_case_not_match. reflexivity.
                  eapply lsstep. apply p_local. apply eval_step_case_match. reflexivity.
                  eapply lsstep. apply p_local. constructor.
                  eapply lsstep. apply p_local. constructor.
                  simpl. repeat rewrite (closed_ignores_sub_val); auto with examples.
                  eapply lsstep. apply p_local. constructor.
                  eapply lsstep. apply p_local. constructor.
                  eapply lsstep. apply p_local. constructor.
                  eapply lsstep. apply p_local. econstructor. congruence. simpl. reflexivity.
                  simpl. repeat rewrite (closed_ignores_sub_val); auto with examples.
                  repeat rewrite (closed_ignores_ren_val); auto with examples.
                  eapply lsstep. apply p_local. constructor.
                  eapply lsstep. apply p_local. constructor.
                  (* message_peek *)
                  apply eval_helper_peek_message.
                }
                {
                  constructor. 2: repeat constructor.
                  by left.
                }
              }
              (* parent sends the result *)
              eapply n_trans. apply n_send. constructor.
              apply n_refl.
            }
            { (* equivalence - we need two helpers about dead processes and ether inserts *)
              simpl. (* now the pools are equal, we have to do the same for the ethers *)
              unfold etherAdd. setoid_rewrite lookup_empty.
              setoid_rewrite lookup_insert_ne.
              2: set_solver.
              setoid_rewrite lookup_empty.
              remember (insert (ι1, ι) _ ∅) as E.
              setoid_rewrite insert_insert_ne. 2: intro Y; inv Y; lia.
              apply barbedBisim_sym.
              setoid_rewrite HeqE.
              apply ether_empty_update_bisim.
              clear-Hbase. set_solver.
              simpl. subst E. left.
              setoid_rewrite lookup_insert_ne. set_solver.
              set_solver.
            }
          }
          {
            clear XX XXX. intros.
            inv H0.
            * put (lookup ι1 : ProcessPool -> _) on H3 as XX.
              setoid_rewrite lookup_insert_eq in XX.
              destruct (decide (ι' = ι1)).
              - subst. setoid_rewrite lookup_insert_eq in XX. inv XX.
                inv H6.
              - by setoid_rewrite lookup_insert_ne in XX.
            (* arrive *)
            * unfold etherPop, etherAdd in H3.
              setoid_rewrite lookup_empty in H3.
              destruct (decide ((ι0, ι') = (ι3, ι1))).
              2: {
                setoid_rewrite lookup_insert_ne in H3; auto.
                by setoid_rewrite lookup_empty in H3.
              }
              inv e. setoid_rewrite lookup_insert_eq in H3.
              setoid_rewrite lookup_empty in H3.
              setoid_rewrite insert_insert_eq in H3. inv H3.
              put (lookup ι1 : ProcessPool -> _) on H2 as HX1.
              setoid_rewrite lookup_insert_eq in HX1. inv HX1.
              assert (forall p, ι1 ↦ p ∥ prs0 = ι1 ↦ p ∥ ∅) as XX. {
                intros. apply map_eq. intros.
                put (lookup i : ProcessPool -> _) on H2 as HX2.
                destruct (decide (i = ι1)).
                * subst. by setoid_rewrite lookup_insert_eq.
                * setoid_rewrite lookup_insert_ne in HX2; auto.
                  by setoid_rewrite lookup_insert_ne.
              }
              rewrite XX in *. clear XX H2.
              inv H8.
              eexists. exists []. split. apply n_refl.
              (* receive finished *)
              (* cleanup of empty ether update: *)
              eapply barbedBisim_trans.
              apply barbedBisim_sym.
              epose proof (ether_empty_update_bisim {[ι]} _ (∅,
 ι1
 ↦ inl
     ([FParams (IPrimOp "recv_wait_timeout") [] [];
       FLet 1
         (° ECase (˝ VVar 0)
              [([PLit "true"], ˝ VLit "true", ˝ VNil);
               ([PLit "false"], ˝ VLit "true",
                ° EApp
                    (˝ VClos
                         [(0, 0,
                           ° ELet 2 (° EPrimOp "recv_peek_message" [])
                               (° ECase (˝ VVar 0)
                                    [([PLit "true"], ˝ VLit "true",
                                      ° ECase (˝ VVar 1)
                                          [([PVar], ˝ VLit "true",
                                            ° ESeq (° EPrimOp "remove_message" [])
                                                (° ECall (˝ VLit "erlang") 
                                                     (˝ VLit "!")
                                                     [˝ VPid ι;
                                                      ° ECall 
                                                          (˝ VLit "erlang") 
                                                          (˝ VLit "++")
                                                          [˝ VVar 0;
                                                           ˝ meta_to_cons
                                                             (map f (drop idx l'))]]));
                                           ([PVar], ˝ VLit "true",
                                            ° ESeq (° EPrimOp "recv_next" [])
                                                (° EApp (˝ VFunId (3, 0)) []))]);
                                     ([PLit "false"], ˝ VLit "true",
                                      ° ELet 1
                                          (° EPrimOp "recv_wait_timeout"
                                               [˝ VLit "infinity"])
                                          (° ECase (˝ VVar 0)
                                               [([PLit "true"], ˝ VLit "true", ˝ VNil);
                                                ([PLit "false"], ˝ 
                                                 VLit "true", ° 
                                                 EApp (˝ VFunId (3, 0)) [])]))]))] 0 0
                         (° ELet 2 (° EPrimOp "recv_peek_message" [])
                              (° ECase (˝ VVar 0)
                                   [([PLit "true"], ˝ VLit "true",
                                     ° ECase (˝ VVar 1)
                                         [([PVar], ˝ VLit "true",
                                           ° ESeq (° EPrimOp "remove_message" [])
                                               (° ECall (˝ VLit "erlang") 
                                                    (˝ VLit "!")
                                                    [˝ VPid ι;
                                                     ° ECall (˝ VLit "erlang")
                                                         (˝ VLit "++")
                                                         [˝ VVar 0;
                                                          ˝ meta_to_cons
                                                             (map f (drop idx l'))]]));
                                          ([PVar], ˝ VLit "true",
                                           ° ESeq (° EPrimOp "recv_next" [])
                                               (° EApp (˝ VFunId (3, 0)) []))]);
                                    ([PLit "false"], ˝ VLit "true",
                                     ° ELet 1
                                         (° EPrimOp "recv_wait_timeout"
                                              [˝ VLit "infinity"])
                                         (° ECase (˝ VVar 0)
                                              [([PLit "true"], ˝ VLit "true", ˝ VNil);
                                               ([PLit "false"], ˝ 
                                                VLit "true", ° 
                                                EApp (˝ VFunId (3, 0)) [])]))]))) [])])],
      RValSeq [VLit "infinity"], mailboxPush emptyBox (meta_to_cons (map f (take idx l'))), ∅,
      false) ∥ ∅)) as Heth. simpl in Heth. eapply Heth.
              1-2: set_solver.
              { (* next: wait timeout succeeds - again low level reasoning needed *)
                constructor.
                2,4: intros; exists source, []; eexists; simpl; split; try by constructor.
                2: {
                  (* again, we proved this already to some extent *)
                  intros. assert (ι0 = ι1). {
                    destruct B'.
                    apply deconstruct_reduction in H0. destruct_hyps.
                    put (lookup ι0 : ProcessPool -> _) on H0 as H'.
                    setoid_rewrite lookup_insert_eq in H'. destruct (decide (ι0 = ι1)).
                    assumption.
                    setoid_rewrite lookup_insert_ne in H'; auto. set_solver.
                  }
                  subst.
                  assert (a = ASend ι1 ι (SMessage (meta_to_cons (map f l')))). {
                    inv H0.
                    * put (lookup ι1 : ProcessPool -> _) on H3 as P.
                      setoid_rewrite lookup_insert_eq in P. inv P. by inv H6.
                    * put (lookup ι1 : ProcessPool -> _) on H2 as P.
                      setoid_rewrite lookup_insert_eq in P. inv P.
                      destruct_or! H8; inv H3; try inv H13; cbn in *; try congruence.
                    * put (lookup ι1 : ProcessPool -> _) on H2 as P.
                      setoid_rewrite lookup_insert_eq in P. inv P.
                      by inv H14.
                  }
                  subst. inv H0. 2: { destruct_or! H8; congruence. }
                  rename ι0 into ι1.
                  put (lookup ι1 : ProcessPool -> _) on H3 as P.
                  setoid_rewrite lookup_insert_eq in P. inv P. inv H9.
                  clear X.
                  (* prs = ∅ *)
                  assert (forall p, ι1 ↦ p ∥ prs1 = ι1 ↦ p ∥ ∅) as X. {
                    intros.
                    apply map_eq. intros. put (lookup i : ProcessPool -> _) on H3 as D.
                    destruct (decide (i = ι1)).
                    * subst. by setoid_rewrite lookup_insert_eq.
                    * setoid_rewrite lookup_insert_ne in D; auto.
                      by setoid_rewrite lookup_insert_ne.
                  }
                  clear H3. rewrite X in *.
                  (**)
                  do 2 eexists. split.
                  {
                    (* reductions *)
                    (* parent recv_timeout then message peek
                    *)
                    eapply closureNodeSem_trans.
                    {
                      eapply process_local_to_node.
                      {
                        (* recv_timeout *)
                        eapply lsstep. apply p_recv_wait_timeout_new_message.
                        eapply lsstep. apply p_local. constructor. reflexivity.
                        simpl. eapply lsstep. apply p_local. constructor.
                        repeat rewrite (closed_ignores_sub_val); auto with examples.
                        simpl. eapply lsstep. apply p_local. constructor.
                        eapply lsstep. apply p_local. apply eval_step_case_not_match. reflexivity.
                        eapply lsstep. apply p_local. apply eval_step_case_match. reflexivity.
                        eapply lsstep. apply p_local. constructor.
                        eapply lsstep. apply p_local. constructor.
                        simpl. repeat rewrite (closed_ignores_sub_val); auto with examples.
                        eapply lsstep. apply p_local. constructor.
                        eapply lsstep. apply p_local. constructor.
                        eapply lsstep. apply p_local. constructor.
                        eapply lsstep. apply p_local. econstructor. congruence. simpl. reflexivity.
                        simpl. repeat rewrite (closed_ignores_sub_val); auto with examples.
                        repeat rewrite (closed_ignores_ren_val); auto with examples.
                        eapply lsstep. apply p_local. constructor.
                        eapply lsstep. apply p_local. constructor.
                        (* message_peek *)
                        apply eval_helper_peek_message.
                      }
                      {
                        constructor. 2: repeat constructor.
                        by left.
                      }
                    }
                    (* parent sends the result *)
                    eapply n_trans. apply n_send. constructor.
                    apply n_refl.
                  }
                  { (* equivalence - we need two helpers about dead processes and ether inserts *)
                    simpl. (* now the pools are equal, we have to do the same for the ethers *)
                    unfold etherAdd. setoid_rewrite lookup_empty.
                    apply barbedBisim_refl.
                  }
                }
                intros. inv H0.
                * put (lookup ι0 : ProcessPool -> _) on H3 as XX.
                  setoid_rewrite lookup_insert_eq in XX.
                  destruct (decide (ι0 = ι1)).
                  - subst. setoid_rewrite lookup_insert_eq in XX. inv XX.
                    inv H6.
                  - by setoid_rewrite lookup_insert_ne in XX; auto.
                * put (lookup ι0 : ProcessPool -> _) on H2 as XX.
                  setoid_rewrite lookup_insert_eq in XX.
                  destruct (decide (ι0 = ι1)).
                  2: by setoid_rewrite lookup_insert_ne in XX; auto.
                  subst. setoid_rewrite lookup_insert_eq in XX. inv XX.
                  destruct_or! H8; subst; inv H3.
                  1: by inv H9.
                  assert (forall p, ι1 ↦ p ∥ Π1 = ι1 ↦ p ∥ ∅) as XXX. {
                    intros. apply map_eq. intros.
                    destruct (decide (i = ι1)).
                    * subst. by setoid_rewrite lookup_insert_eq.
                    * setoid_rewrite lookup_insert_ne; auto.
                      put (lookup i : ProcessPool -> _) on H2 as HX2.
                      by setoid_rewrite lookup_insert_ne in HX2; auto.
                  }
                  rewrite XXX in *. clear H2 XXX.
                  eexists. exists []. split. apply n_refl.
                  eapply barbedBisim_trans.
                  {
                    eapply normalisation_τ_many_bisim.
                    1: shelve.
                    apply sequential_to_node.
                    do 9 do_step_with_examples.
                    repeat rewrite (closed_ignores_sub_val); auto with examples.
                    do_step_with_examples. econstructor 2. econstructor. congruence. simpl. reflexivity.
                    repeat rewrite (closed_ignores_sub_val); auto with examples.
                    repeat rewrite (closed_ignores_ren_val); auto with examples.
                    do 2 do_step_with_examples.
                    constructor 1.
                  }
                  (* peek_message succeeds - this was done previously *)
                  by apply bisim_helper.
                * put (lookup ι0 : ProcessPool -> _) on H2 as XX.
                  setoid_rewrite lookup_insert_eq in XX.
                  destruct (decide (ι0 = ι1)).
                  - subst. setoid_rewrite lookup_insert_eq in XX. inv XX.
                    inv H14.
                  - by setoid_rewrite lookup_insert_ne in XX; auto.
              }
            * put (lookup ι1 : ProcessPool -> _) on H2 as XX.
              setoid_rewrite lookup_insert_eq in XX.
              destruct (decide (ι' = ι1)).
              - subst. setoid_rewrite lookup_insert_eq in XX. inv XX.
                destruct_or!; subst; inv H3. inv H9.
              - by setoid_rewrite lookup_insert_ne in XX.
            * put (lookup ι1 : ProcessPool -> _) on H2 as XX.
              setoid_rewrite lookup_insert_eq in XX.
              destruct (decide (ι' = ι1)).
              - subst. setoid_rewrite lookup_insert_eq in XX. inv XX.
                inv H14.
              - by setoid_rewrite lookup_insert_ne in XX.
          }
        + put (lookup ι0 : ProcessPool -> _) on H1 as HX1.
          setoid_rewrite lookup_insert_eq in HX1.
          destruct (decide (ι0 = ι_base)).
          ** subst. setoid_rewrite lookup_insert_eq in HX1. inv HX1.
             destruct_or! H6; subst; inv H2. inv H8.
          ** setoid_rewrite lookup_insert_ne in HX1; auto.
             destruct (decide (ι0 = x)).
             -- subst. setoid_rewrite lookup_insert_eq in HX1. inv HX1.
                destruct_or! H6; subst; inv H2. inv H8.
             -- setoid_rewrite lookup_insert_ne in HX1; auto. clear-HX1. set_solver.
        + put (lookup ι0 : ProcessPool -> _) on H1 as HX1.
          setoid_rewrite lookup_insert_eq in HX1.
          destruct (decide (ι0 = ι_base)).
          ** subst. setoid_rewrite lookup_insert_eq in HX1. inv HX1. inv H13.
          ** setoid_rewrite lookup_insert_ne in HX1; auto.
             destruct (decide (ι0 = x)).
             -- subst. setoid_rewrite lookup_insert_eq in HX1. inv HX1. inv H13.
             -- setoid_rewrite lookup_insert_ne in HX1; auto. clear-HX1. set_solver.
      - put (lookup ι0 : ProcessPool -> _) on H1 as HX1.
        setoid_rewrite lookup_insert_eq in HX1.
        destruct (decide (ι0 = ι_base)).
        + subst. setoid_rewrite lookup_insert_eq in HX1. inv HX1. inv H13.
        + setoid_rewrite lookup_insert_ne in HX1; auto.
          destruct (decide (ι0 = x)).
          ** subst. setoid_rewrite lookup_insert_eq in HX1. inv HX1. inv H13.
          ** setoid_rewrite lookup_insert_ne in HX1; auto. clear-HX1. set_solver.
  }
Unshelve.
  apply Forall_app; split.
  all: try by apply Forall_repeat.
  all: try by repeat constructor.
Qed. (* This takes an awful lot time (obviously) ~ᵇ 2-3 minutes*)
Transparent map_clos.
Transparent receive.

End map_pmap.
