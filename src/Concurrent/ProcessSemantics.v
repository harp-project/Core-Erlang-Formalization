(* This part of the work is based on https://dl.acm.org/doi/10.1145/3123569.3123576 *)
From CoreErlang.FrameStack Require Export SubstSemantics.
From CoreErlang.Concurrent Require Export PIDRenaming.
Require Export Coq.Sorting.Permutation.
From stdpp Require Export option gmap.

Import ListNotations.

(* mailbox: [old msg₁, old msg₁, ...] ++ 
            current msg₁ :: [new msg₁, new msg₂, ...] *)
Definition Mailbox : Set := list Val * list Val.
Definition emptyBox : Mailbox := ([], []).
Definition ProcessFlag : Set := bool.
Definition LiveProcess : Set := FrameStack * Redex * Mailbox * gset PID * ProcessFlag.

Instance PIDVal_eq_dec : EqDecision (PID * Val).
Proof.
  pose proof Val_eq_dec.
  eapply prod_eq_dec.
  Unshelve.
  unfold EqDecision, Decision. apply H.
Defined.

Hint Resolve PIDVal_eq_dec : core.

Instance Val_eq_decision : EqDecision Val.
Proof.
  pose proof Val_eq_dec.
  unfold EqDecision, Decision. apply H.
Defined.

Hint Resolve Val_eq_decision : core.


Instance singleton_PID : Singleton PID (gset PID).
Proof.
  unfold Singleton.
  intro x. exact {[x]}.
Defined.

Hint Resolve singleton_PID : core.

Definition DeadProcess : Set := gmap PID Val.
Definition Process : Set := LiveProcess + DeadProcess.

Inductive Signal : Set :=
| SMessage (e : Val)
| SExit (r : Val) (b : bool)
| SLink
| SUnlink.

Inductive Action : Set :=
| ASend (sender receiver : PID) (t : Signal)
| AArrive (sender receiver : PID) (t : Signal)
| ASelf (ι : PID)
| ASpawn (ι : PID) (t1 t2 : Val) (link : bool)
| τ (* tau denotes confluent actions of the semantics (these are silent steps and a few other reductions) *)
| ε (* epsilon is used for process-local silent operations (e.g., mailbox manipulation), which are NOT confluent *)
.

Definition removeMessage (m : Mailbox) : option Mailbox :=
  match m with
  | (m1, msg :: m2) => Some ([], m1 ++ m2)
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
Definition EReceive l t e :=
  ELetRec [(0, 
     °ELet 2 (EPrimOp "recv_peek_message" [])
       (ECase (˝VFunId (0, 0)) [
         ([PLit (Atom "true")], ˝ttrue, °ECase (˝VVar 1) (l ++
           [([PVar], ˝ttrue, °ESeq (EPrimOp "recv_next" [])
                                 (EApp (˝VFunId (3, 0)) [])
           )]));
         ([PLit (Atom "false")], ˝ttrue,
           °ELet 1 (EPrimOp "recv_wait_timeout" [t])
              (ECase (˝VVar 0)
                [([PLit (Atom "true")], ˝ttrue, e); (* TODO: timeout *)
                 ([PLit (Atom "false")], ˝ttrue, °EApp (˝VFunId (3, 0)) [])
                ]
              )
         )
       ])
    )]
    (EApp (˝VFunId (0, 0)) []).

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
  if a ˝receive˝ is evaluated:
  1) try the first message against the clauses
    a) if it matches one, evaluate its guard
    b) if the guard is true, go to step 2)
    c) if the guard is false, or the message did not match, save the message
       into a separate cell, then evaluate ˝receive˝ with step 1), second message
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
  if String.eqb x "true"%string
  then Some true
  else if String.eqb x "false"%string
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
  inl (fs, e, mb, links, flag) -⌈ AArrive source dest (SMessage v) ⌉-> inl (fs, e, mailboxPush mb v, links, flag)

(* exiting actions should come here *)
(* dropping exit signals *)
| p_exit_drop fs e mb links flag dest source reason b :
  (
    reason = normal /\ dest <> source /\ flag = false \/
    source ∉ links /\ b = true /\ dest <> source
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
  VALCLOSED v ->
  inl (FParams (ICall erlang send) [VPid ι] [] :: fs, RValSeq [v], mb, links, flag)
  -⌈ ASend source ι (SMessage v) ⌉-> inl (fs, RValSeq [v], mb, links, flag)
(* exit, 2 parameters *)
| p_exit fs v mb flag ι selfι links :
  VALCLOSED v ->
  inl (FParams (ICall erlang exit) [VPid ι] [] :: fs, RValSeq [v], mb, links, flag) -⌈ ASend selfι ι (SExit v false) ⌉->
  inl (fs, RValSeq [ttrue], mb, links, flag)
(* link *)
| p_link fs ι mb flag links selfι :
  inl (FParams (ICall erlang link) [] [] :: fs, RValSeq [VPid ι], mb, links, flag)
  -⌈ASend selfι ι SLink⌉->
  inl (fs, RValSeq [ok], mb, {[ι]} ∪ links, flag)
(* unlink *)
| p_unlink fs ι mb flag links selfι :
  inl (FParams (ICall erlang unlink) [] [] :: fs, RValSeq [VPid ι], mb, links, flag) 
  -⌈ASend selfι ι SUnlink⌉->
  inl (fs, RValSeq [ok], mb, links ∖ {[ι]}, flag)
(* DEAD PROCESSES *)
| p_dead ι selfι links reason:
  VALCLOSED reason ->
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

(********** RECEVIE **********)
(* nonempty peeks are confluent, while empty peeks are not *)
| p_recv_peek_message_ok fs mb msg links flag :
  peekMessage mb = Some msg ->
  inl (FParams (IPrimOp "recv_peek_message") [] [] :: fs, RBox, mb, links, flag) -⌈τ⌉->
    inl (fs, RValSeq [ttrue;msg], mb, links, flag)

| p_recv_peek_message_no_message fs mb links flag :
  peekMessage mb = None ->
  inl (FParams (IPrimOp "recv_peek_message") [] [] :: fs, RBox, mb, links, flag) -⌈ε⌉->
    inl (fs, RValSeq [ffalse;ErrorVal], mb, links, flag) (* TODO: errorVal is probably not used here, but I could not find the behaviour *)

| p_recv_next fs mb links flag:
  inl (FParams (IPrimOp "recv_next") [] [] :: fs, RBox, mb, links, flag) -⌈ ε ⌉->
    inl (fs, RValSeq [ok], recvNext mb, links, flag) (* TODO: in Core Erlang, this result cannot be observed *)

(* This rule only works for nonempty mailboxes, thus it is confluent *)
| p_remove_message fs mb mb' links flag:
  removeMessage mb = Some mb' ->
  inl (FParams (IPrimOp "remove_message") [] [] :: fs, RBox, mb, links, flag) -⌈ τ ⌉->
    inl (fs, RValSeq [ok], mb', links, flag) (* TODO: in Core Erlang, this result cannot be observed *)

| p_recv_wait_timeout_new_message fs oldmb msg newmb links flag:
  (* There is a new message *)
  inl (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs, RValSeq [infinity], (oldmb, msg :: newmb), links, flag) -⌈ε⌉->
  inl (fs, RValSeq [ffalse], (oldmb, msg :: newmb), links, flag)

(* This rule is also confluent *)
| p_recv_wait_timeout_0 fs mb links flag:
  (* 0 timeout is reached *)
  inl (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs, RValSeq [VLit 0%Z], mb, links, flag) -⌈τ⌉->
  inl (fs, RValSeq [ttrue], mb, links, flag)

(* This rule is also confluent *)
| p_recv_wait_timeout_invalid fs mb links flag v:
  v <> VLit 0%Z -> v <> infinity ->
  inl (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs, RValSeq [v], mb, links, flag) -⌈τ⌉-> inl (fs, RExc (timeout_value v), mb, links, flag)

(********** PROCESS FLAG **********)
(* Replace process flags *)
| p_set_flag fs mb flag y v links :
  Some y = bool_from_lit v ->
  inl (FParams (ICall erlang process_flag) [] [] :: fs, RValSeq [v], mb, links, flag) 
   -⌈ ε ⌉-> inl (fs, RValSeq [lit_from_bool flag], mb, links, y)

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
  (* NOTE: if the final result is an exception, it's reason is sent
     to the linked processes *)
  inl ([], RExc exc, mb, links, flag) -⌈ε⌉->
   inr (gset_to_gmap exc.1.2 links)

where "p -⌈ a ⌉-> p'" := (processLocalSemantics p a p').

Inductive LabelStar {A B : Type} (r : A -> B -> A -> Prop) : A -> list B -> A -> Prop :=
| lsrefl x : LabelStar r x [] x
| lsstep x l ls y z : r x l y -> LabelStar r y ls z -> LabelStar r x (l::ls) z.

Notation "x -⌈ xs ⌉->* y" := (LabelStar processLocalSemantics x xs y) (at level 50).


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

(* TODO: do this with Applicative/Monad *)
Definition PIDsOf (f : Action -> option PID) (l : list (Action * PID)) : list PID :=
  flat_map (fun a =>
    match f a.1 with
    | Some ι => [ι]
    | None => []
    end) l.

Definition renamePIDPID (p p' : PID) := fun s => if s =? p
                                                 then p'
                                                 else s.

Definition renamePIDSignal (p p' : PID) (s : Signal) : Signal :=
match s with
 | SMessage e => SMessage (renamePIDVal p p' e)
 | SExit r b => SExit (renamePIDVal p p' r) b
 | SLink => s
 | SUnlink => s
end.

Definition usedPIDsSignal (s : Signal) : gset PID :=
match s with
 | SMessage e => usedPIDsVal e
 | SExit r b => usedPIDsVal r
 | SLink => ∅
 | SUnlink => ∅
end.


Notation "e .[ x ↦ y ]ₛ" := (renamePIDSignal x y e) (at level 2).

Corollary isNotUsed_renamePID_signal :
  forall s from to, from ∉ (usedPIDsSignal s) -> renamePIDSignal from to s = s.
Proof.
  intros. destruct s; try reflexivity; simpl.
  * now rewrite isNotUsed_renamePID_val.
  * now rewrite isNotUsed_renamePID_val.
Qed.

Corollary double_renamePID_signal :
  forall s from to, to ∉ (usedPIDsSignal s) -> renamePIDSignal to from (renamePIDSignal from to s) = s.
Proof.
  intros. destruct s; try reflexivity; simpl.
  * now rewrite double_PIDrenaming_val.
  * now rewrite double_PIDrenaming_val.
Qed.

From stdpp Require Import base.

Instance Process_equiv : Equiv Process := eq.
Instance Process_leibniz : LeibnizEquiv Process.
Proof.
  intros x y H. exact H.
Defined.

Definition renamePIDMb (p p' : PID) (mb : Mailbox) : Mailbox :=
  (map (renamePIDVal p p') mb.1, map (renamePIDVal p p') mb.2).

Definition renamePIDPID_sym (p p' : PID) := fun s => if s =? p
                                                     then p'
                                                     else if s =? p'
                                                      (* This part is needed
                                                         for Inj eq eq *)
                                                          then p
                                                          else s.

Instance renamePIDPID_sym_Inj p p' : Inj eq eq (renamePIDPID_sym p p').
Proof.
  unfold Inj. intros. unfold renamePIDPID_sym in H.
  repeat case_match; eqb_to_eq; subst; auto; try congruence.
Defined.

Hint Resolve renamePIDPID_sym_Inj : core.
Hint Resolve prod_map_inj : core.
Hint Resolve id_inj : core.

Definition renamePIDProc (p p' : PID) (pr : Process) : Process :=
match pr with
| inl (fs, r, mb, links, flag) =>
  inl (renamePIDStack p p' fs, renamePIDRed p p' r,
       renamePIDMb p p' mb,
       set_map (renamePIDPID p p') links, flag)
| inr dpr => inr (kmap (renamePIDPID_sym p p') (fmap (renamePIDVal p p') dpr))
end.

Definition union_set {A C : Type} {H : Union C} {H0 : Elements C A} {H1 : Empty C} (s : A) : C := union_list (elements s).

Instance gsetPID_elem_of : Elements (gset PID) (gset (gset PID)).
Proof.
  unfold Elements.
  exact elements.
Defined.


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

Ltac renamePIDPID_case_match :=
  unfold renamePIDPID; repeat case_match; eqb_to_eq; subst; try lia.
Ltac renamePIDPID_case_match_hyp H :=
  unfold renamePIDPID in H; repeat case_match; eqb_to_eq; subst; try lia.
Ltac renamePIDPID_sym_case_match :=
  unfold renamePIDPID_sym; repeat case_match; eqb_to_eq; subst; try lia.
Ltac renamePIDPID_sym_case_match_hyp H :=
  unfold renamePIDPID_sym in H; repeat case_match; eqb_to_eq; subst; try lia.

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
    1-2: rewrite isNotUsed_renamePID_val; apply elem_of_list_In in H4; set_solver.
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

Corollary double_renamePID_proc :
  forall p from to, to ∉ (usedPIDsProc p) -> renamePIDProc to from (renamePIDProc from to p) = p.
Proof.
  intros. destruct p; simpl.
  * destruct l, p, p, p, m. simpl.
    simpl in H. repeat apply not_elem_of_union in H as [H ?].
    rewrite not_elem_of_flat_union in H0, H1.
    rewrite double_PIDrenaming_red, double_PIDrenaming_stack; auto.
    repeat f_equal.
    1: unfold renamePIDMb; simpl; f_equal.
    1-2: rewrite map_map, <- map_id; apply map_ext_in; intros; simpl.
    1-2: rewrite double_PIDrenaming_val; apply elem_of_list_In in H4; set_solver.
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
      rewrite double_PIDrenaming_val. reflexivity.
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
      rewrite double_PIDrenaming_val. reflexivity.
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
      rewrite double_PIDrenaming_val. reflexivity.
      intro. apply H.
      unfold union_set in *. apply elem_of_union_list.
      exists ({[i]} ∪ usedPIDsVal v). split. 2: set_solver.
      apply elem_of_elements. apply elem_of_map_to_set.
      do 2 eexists. split. exact P. reflexivity.
Qed.

Notation "e .⟦ x ↦ y ⟧ₚ" := (renamePIDProc x y e) (at level 2).

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

Notation "e .⟦ x ↦ y ⟧ₐ" := (renamePIDAct x y e) (at level 2).

Lemma mailboxPush_rename :
  forall mb v from to, 
         renamePIDMb from to (mailboxPush mb v) =
         mailboxPush (renamePIDMb from to mb) (renamePIDVal from to v).
Proof.
  intros.
  unfold renamePIDMb, mailboxPush; simpl.
  destruct mb; simpl.
  rewrite map_app. now simpl.
Qed.

Definition usedPIDsAct (a : Action) : gset PID :=
match a with
 | ASend sender receiver t => {[sender]} ∪ {[receiver]} ∪ usedPIDsSignal t
 | AArrive sender receiver t => {[sender]} ∪ {[receiver]} ∪ usedPIDsSignal t
 | ASelf ι => {[ι]}
 | ASpawn ι t1 t2 _ => {[ι]} ∪ usedPIDsVal t1 ∪ usedPIDsVal t2
 | _ => ∅
end.

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

Lemma peekMessage_renamePID :
  forall mb from to,
    peekMessage (renamePIDMb from to mb) = fmap (renamePIDVal from to) (peekMessage mb).
Proof.
  destruct mb. intros. simpl.
  now destruct l0.
Qed.

Lemma recvNext_renamePID :
  forall mb from to,
    renamePIDMb from to (recvNext mb) = recvNext (renamePIDMb from to mb).
Proof.
  destruct mb. intros. simpl. destruct l0; try reflexivity.
  cbn. unfold renamePIDMb. simpl. f_equal.
  apply map_app.
Qed.

Lemma removeMessage_renamePID :
  forall mb from to,
    removeMessage (renamePIDMb from to mb) = fmap (renamePIDMb from to) (removeMessage mb).
Proof.
  destruct mb. intros. simpl. destruct l0; try reflexivity.
  simpl. f_equal. unfold renamePIDMb. simpl.
  f_equal. now rewrite map_app.
Qed.

Lemma renamePIDPID_1 :
  forall a b, renamePIDPID a b a = b.
Proof.
  unfold renamePIDPID. intros. by rewrite Nat.eqb_refl.
Qed.

Lemma renamePIDPID_sym_1 :
  forall a b, renamePIDPID_sym a b a = b.
Proof.
  unfold renamePIDPID_sym. intros. by rewrite Nat.eqb_refl.
Qed.

Lemma rename_eq :
  forall from to ι,
  ι <> to ->
  renamePIDPID_sym from to ι = renamePIDPID from to ι.
Proof.
  unfold renamePIDPID_sym, renamePIDPID. intros.
  case_match; auto. case_match; auto.
  eqb_to_eq; congruence.
Qed.

Opaque mailboxPush.
(* For this theorem, freshness is needed! *)
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
  * simpl. rewrite mailboxPush_rename.
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
      rewrite lookup_gset_to_gmap. unfold mguard, option_guard. case_match.
      * clear H0. apply elem_of_map in e; destruct_hyps.
        subst. rewrite <- rename_eq by set_solver.
        setoid_rewrite lookup_kmap; auto.
        setoid_rewrite lookup_fmap.
        rewrite lookup_gset_to_gmap. simpl.
        unfold mguard, option_guard. case_match. 2: { clear H0. set_solver. }
        reflexivity.
      * clear H0.
        destruct (decide (i = from)). 2: destruct (decide (i = to)).
        - subst.
          replace from with (renamePIDPID_sym from to to) at 1 by renamePIDPID_sym_case_match.
          setoid_rewrite lookup_kmap; auto.
          setoid_rewrite lookup_fmap.
          rewrite lookup_gset_to_gmap. simpl.
          unfold mguard, option_guard. case_match. 2: { clear H0. set_solver. }
          by clear H0.
        - subst.
          replace to with (renamePIDPID_sym from to from) at 1 by renamePIDPID_sym_case_match.
          setoid_rewrite lookup_kmap; auto.
          setoid_rewrite lookup_fmap.
          rewrite lookup_gset_to_gmap. simpl.
          unfold mguard, option_guard. case_match. 2: { clear H0. set_solver. }
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
          unfold mguard, option_guard. case_match. 2: { clear H1. set_solver. }
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
  * simpl. rewrite mailboxPush_rename. simpl.
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
    (* TODO: extract it somehow to a separate theorem about set_map and ∖ - couldn't do it because of the tagling typeclasses *)
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
    - replace (renamePIDPID ι to ι) with to by (renamePIDPID_case_match). constructor. now apply renamePID_preserves_scope.
    - replace (renamePIDPID from to ι) with ι by renamePIDPID_case_match.
      constructor. now apply renamePID_preserves_scope.
  * simpl in *. destruct Nat.eqb eqn:P; eqb_to_eq; subst.
    - replace (renamePIDPID ι to ι) with to by (renamePIDPID_case_match).
      constructor. by apply renamePID_preserves_scope.
    - replace (renamePIDPID from to ι) with ι by renamePIDPID_case_match.
      constructor. by apply renamePID_preserves_scope.
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
    (* TODO: extract it somehow to a separate theorem about set_map and ∖ - couldn't do it because of the tagling typeclasses *)
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
    rewrite rename_eq. 2: set_solver. apply p_dead.
    - by apply renamePID_preserves_scope.
    - setoid_rewrite lookup_kmap_Some; auto.
      exists ι. split. rewrite rename_eq. 2: set_solver. reflexivity.
      setoid_rewrite lookup_fmap. by setoid_rewrite H3.
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
  * simpl. rewrite recvNext_renamePID. constructor.
  * simpl. constructor. rewrite removeMessage_renamePID, H2. reflexivity.
  * simpl. apply p_recv_wait_timeout_invalid.
    all: intro X; destruct v; simpl in X; try congruence.
    all: break_match_hyp; congruence.
  * simpl. destruct flag; simpl; apply p_set_flag.
    all: destruct v; inv H2; simpl; auto.
  * simpl.
    rewrite fmap_gset_to_gmap.
    replace (inr _) with
      (inr (gset_to_gmap normal (set_map (renamePIDPID from to) links)) : Process).
    2: {
      f_equal. apply map_eq. intros.
      rewrite lookup_gset_to_gmap. unfold mguard, option_guard. case_match.
      * clear H.
        apply elem_of_map in e. destruct_hyps. subst.
        rewrite <- rename_eq. 2: set_solver.
        setoid_rewrite lookup_kmap; auto.
        rewrite lookup_gset_to_gmap. unfold mguard, option_guard. case_match.
        all: clear H; set_solver.
      * clear H. symmetry. apply lookup_kmap_None; auto.
        intros. subst.
        apply lookup_gset_to_gmap_None.
        intro. apply n. apply elem_of_map. eexists. split.
        rewrite rename_eq. 2: set_solver.
        reflexivity. assumption.
    }
    constructor.
  * simpl. destruct exc, p. simpl.
    rewrite fmap_gset_to_gmap.
    replace (inr _) with
      (inr (gset_to_gmap v0 .⟦ from ↦ to ⟧ᵥ (set_map (renamePIDPID from to) links)) : Process).
    2: {
      f_equal. apply map_eq. intros.
      rewrite lookup_gset_to_gmap. unfold mguard, option_guard. case_match.
      * clear H.
        apply elem_of_map in e0. destruct_hyps. subst.
        rewrite <- rename_eq. 2: set_solver.
        setoid_rewrite lookup_kmap; auto.
        rewrite lookup_gset_to_gmap. unfold mguard, option_guard. case_match.
        all: clear H; set_solver.
      * clear H. symmetry. apply lookup_kmap_None; auto.
        intros. subst.
        apply lookup_gset_to_gmap_None.
        intro. apply n. apply elem_of_map. eexists. split.
        rewrite rename_eq. 2: set_solver.
        reflexivity. assumption.
    }
    constructor.
Qed.
Transparent mailboxPush.

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

Corollary renamePID_id_sig :
  forall s p, renamePIDSignal p p s = s.
Proof.
  destruct s; intros; simpl; try reflexivity.
  all: by rewrite renamePID_id_val.
Qed.

Corollary renamePID_id_act :
  forall a p, renamePIDAct p p a = a.
Proof.
  destruct a; intros; simpl; try reflexivity.
  4: do 2 rewrite renamePID_id_val. 1-2: rewrite renamePID_id_sig.
  all: by renamePIDPID_case_match.
Qed.

Corollary isNotUsed_renamePID_action :
  forall a from to, from ∉ (usedPIDsAct a) -> renamePIDAct from to a = a.
Proof.
  intros. destruct a; try reflexivity; simpl in *.
  * rewrite isNotUsed_renamePID_signal.
    unfold renamePIDPID; repeat case_match; eqb_to_eq. all: set_solver.
  * rewrite isNotUsed_renamePID_signal.
    unfold renamePIDPID; repeat case_match; eqb_to_eq. all: set_solver.
  * unfold renamePIDPID; repeat case_match; eqb_to_eq. all: set_solver.
  * rewrite isNotUsed_renamePID_val. rewrite isNotUsed_renamePID_val.
    unfold renamePIDPID; repeat case_match; eqb_to_eq. all: set_solver.
Qed.

Corollary double_renamePID_action :
  forall a from to, to ∉ (usedPIDsAct a) -> renamePIDAct to from (renamePIDAct from to a) = a.
Proof.
  intros. destruct a; try reflexivity; simpl.
  * unfold renamePIDPID. simpl in *.
    rewrite double_renamePID_signal.
    repeat case_match; eqb_to_eq. all: set_solver.
  * unfold renamePIDPID. simpl in *.
    rewrite double_renamePID_signal.
    repeat case_match; eqb_to_eq. all: set_solver.
  * unfold renamePIDPID. simpl in *.
    repeat case_match; eqb_to_eq. all: set_solver.
  * unfold renamePIDPID. simpl in *.
    rewrite double_PIDrenaming_val. rewrite double_PIDrenaming_val.
    repeat case_match; eqb_to_eq. all: set_solver.
Qed.

Corollary renamePID_swap_sig :
  forall s from1 from2 to1 to2, from1 ≠ from2 -> from1 ≠ to2 -> from2 ≠ to1 ->
               renamePIDSignal from1 to1 (renamePIDSignal from2 to2 s) =
               renamePIDSignal from2 to2 (renamePIDSignal from1 to1 s).
Proof.
  destruct s; intros; try reflexivity; simpl.
  * by rewrite renamePID_swap_val.
  * by rewrite renamePID_swap_val.
Qed.

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

Corollary usedPIDsProc_rename :
  (forall pr p p',
    usedPIDsProc (renamePIDProc p p' pr) = if decide (p ∈ usedPIDsProc pr)
                                        then {[p']} ∪ usedPIDsProc pr ∖ {[p]}
                                        else usedPIDsProc pr ∖ {[p]}).
Proof.
  destruct pr; intros; simpl.
  * destruct l, p0, p0, p0; simpl.
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
    repeat destruct decide; set_solver. (* NOTE: this line takes long time to compile *)
  * admit.
Admitted.
