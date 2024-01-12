(* This part of the work is based on https://dl.acm.org/doi/10.1145/3123569.3123576 *)
From CoreErlang.FrameStack Require Export SubstSemantics.
From CoreErlang.Concurrent Require Export PIDRenaming.
Require Export Coq.Sorting.Permutation.
Require Export Coq.Classes.EquivDec.
From stdpp Require Export option.

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
| SMessage (e : Val)
| SExit (r : Val) (b : bool)
| SLink
| SUnlink.

Inductive Action : Set :=
| ASend (sender receiver : PID) (t : Signal)
(* | ANext
| ARemove
| APeek 
*)
(* | ADestroy (* <- this is a concurrent action *) *)
| AArrive (sender receiver : PID) (t : Signal)
| ASelf (ι : PID)
| ASpawn (ι : PID) (t1 t2 : Val)
| τ
| ε (* epsilon is used for process-local silent operations (e.g., mailbox manipulation) *)
(* | ATerminate
| ASetFlag *)
.

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
       (ECase (˝VFunId (0, 0)) [
         ([PLit (Atom "true")], ˝ttrue, °ECase (˝VVar 1) (l ++
           [([PVar], ˝ttrue, °ESeq (EPrimOp "recv_next" [])
                                 (EApp (˝VFunId (3, 0)) [])
           )]));
         ([PLit (Atom "false")], ˝ttrue,
           °ELet 1 (EPrimOp "recv_wait_timeout" [])
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
  inr (map (fun l => (l, reason')) links)
(* convert exit signal to message *)
(* TODO, NOTE: here tuple should be used instead of list! *)
| p_exit_convert fs e mb links dest source reason b:
  (b = false /\ reason <> kill) \/
  (b = true /\ source ∈ links)
 ->
  inl (fs, e, mb, links, true) -⌈ AArrive source dest (SExit reason b) ⌉->
  inl (fs, e, mailboxPush mb (VCons EXIT 
                           (VCons (VPid source) (VCons reason VNil))), links, true)
(* link received *)
| p_link_arrived fs e mb links source dest flag:
  inl (fs, e, mb, links, flag) -⌈AArrive source dest SLink⌉->
  inl (fs, e, mb, source :: links, flag)

(* unlink received *)
| p_unlink_arrived fs e mb links source dest flag :
  inl (fs, e, mb, links, flag) -⌈AArrive source dest SUnlink⌉->
  inl (fs, e, mb, remove Nat.eq_dec source links, flag)

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
  inl (fs, RValSeq [ok], mb, ι :: links, flag)
(* unlink *)
| p_unlink fs ι mb flag links selfι :
  inl (FParams (ICall erlang unlink) [] [] :: fs, RValSeq [VPid ι], mb, links, flag) 
  -⌈ASend selfι ι SUnlink⌉->
  inl (fs, RValSeq [ok], mb, remove Nat.eq_dec ι links, flag)
(* DEAD PROCESSES *)
| p_dead ι selfι links reason:
  VALCLOSED reason ->
  inr ((ι, reason) :: links) -⌈ASend selfι ι (SExit reason true)⌉-> inr links


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
| p_recv_peek_message_ok fs mb msg links flag :
  peekMessage mb = Some msg ->
  inl (FParams (IPrimOp "recv_peek_message") [] [] :: fs, RBox, mb, links, flag) -⌈ε⌉->
    inl (fs, RValSeq [ttrue;msg], mb, links, flag)

| p_recv_peek_message_no_message fs mb links flag :
  peekMessage mb = None ->
  inl (FParams (IPrimOp "recv_peek_message") [] [] :: fs, RBox, mb, links, flag) -⌈ε⌉->
    inl (fs, RValSeq [ffalse;ErrorVal], mb, links, flag) (* TODO: errorVal is probably not used here, but I could not find the behaviour *)

| p_recv_next fs mb links flag:
  inl (FParams (IPrimOp "recv_next") [] [] :: fs, RBox, mb, links, flag) -⌈ ε ⌉->
    inl (fs, RValSeq [ok], recvNext mb, links, flag) (* TODO: in Core Erlang, this result cannot be observed *)

| p_remove_message fs mb mb' links flag:
  removeMessage mb = Some mb' ->
  inl (FParams (IPrimOp "remove_message") [] [] :: fs, RBox, mb, links, flag) -⌈ ε ⌉->
    inl (fs, RValSeq [ok], mb', links, flag) (* TODO: in Core Erlang, this result cannot be observed *)

| p_recv_wait_timeout_new_message fs oldmb msg newmb links flag:
  (* There is a new message *)
  inl (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs, RValSeq [infinity], (oldmb, msg :: newmb), links, flag) -⌈ε⌉->
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
   -⌈ ε ⌉-> inl (fs, RValSeq [lit_from_bool flag], mb, links, y)

(********** TERMINATION **********)
(* termination *)
| p_terminate v mb links flag:
  (* NOTE: "singletonness" is checked in compile time in Core Erlang *)
  inl ([], RValSeq [v], mb, links, flag) -⌈ε⌉->
   inr (map (fun l => (l, normal)) links) (* NOTE: is internal enough here? - no, it's not for bisimulations *)

(* exit with one parameter <- this is sequential, it's in FrameStack/Auxiliaries.v *)

(********** EXCEPTIONS **********)
(* creation *)
| p_terminate_exc exc mb links flag:
  (* NOTE: if the final result is an exception, it's reason is sent
     to the linked processes *)
  inl ([], RExc exc, mb, links, flag) -⌈ε⌉->
   inr (map (fun l => (l, exc.1.2)) links)

where "p -⌈ a ⌉-> p'" := (processLocalSemantics p a p').

Inductive LabelStar {A B : Type} (r : A -> B -> A -> Prop) : A -> list B -> A -> Prop :=
| lsrefl x : LabelStar r x [] x
| lsstep x l ls y z : r x l y -> LabelStar r y ls z -> LabelStar r x (l::ls) z.

Notation "x -⌈ xs ⌉->* y" := (LabelStar processLocalSemantics x xs y) (at level 50).


(** This is needed to ensure that a process is not spawned with a wrong PID
    in the equivalence. *)
Definition spawnPIDOf (a : Action) : option PID :=
  match a with
  | ASpawn ι _ _ => Some ι
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

Definition renamePIDProc (p p' : PID) (pr : Process) : Process :=
match pr with
| inl (fs, r, mb, links, flag) =>
  inl (renamePIDStack p p' fs, renamePIDRed p p' r,
       renamePIDMb p p' mb,
       map (renamePIDPID p p') links, flag)
| inr dpr => inr (map (fun '(d, v) => (renamePIDPID p p' d, renamePIDVal p p' v)) dpr)
end.

Definition usedPIDsProc (p : Process) : gset PID :=
match p with
| inl (fs, r, mb, links, flag) => 
    usedPIDsStack fs ∪
    usedPIDsRed r ∪
    list_to_set links ∪
    flat_union usedPIDsVal mb.1 ∪
    flat_union usedPIDsVal mb.2
| inr links => (* TODO: should links should be considered? - Probably *)
    flat_union (fun x => {[x.1]} ∪ usedPIDsVal x.2) links
end.

Corollary isNotUsed_renamePID_proc :
  forall p from to, from ∉ (usedPIDsProc p) -> renamePIDProc from to p = p.
Proof.
  intros. destruct p; simpl.
  * destruct l, p, p, p, m. simpl.
    simpl in H. repeat apply not_elem_of_union in H as [H ?].
    rewrite not_elem_of_flat_union in *.
    rewrite isNotUsed_renamePID_red, isNotUsed_renamePID_stack; auto.
    repeat f_equal.
    1: unfold renamePIDMb; simpl; f_equal.
    all: rewrite <- map_id; apply map_ext_in; intros; simpl.
    1-2: rewrite isNotUsed_renamePID_val; apply elem_of_list_In in H4; set_solver.
    unfold renamePIDPID. break_match_goal; eqb_to_eq; subst. 2: reflexivity.
    apply elem_of_list_In in H4. set_solver.
  * f_equal. rewrite <- map_id; apply map_ext_in; intros; simpl. destruct a.
    unfold usedPIDsProc in H.
    rewrite elem_of_flat_union in H.
    apply elem_of_list_In in H0.
    rewrite isNotUsed_renamePID_val. 2: intro; apply H; set_solver.
    unfold renamePIDPID. case_match; auto. eqb_to_eq; subst.
    set_solver.
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
    all: rewrite map_map, <- map_id; apply map_ext_in; intros; simpl.
    1-2: rewrite double_PIDrenaming_val; apply elem_of_list_In in H4; set_solver.
    unfold renamePIDPID. repeat case_match; eqb_to_eq; subst; try congruence.
    apply elem_of_list_In in H4. set_solver.
  * f_equal. rewrite map_map, <- map_id; apply map_ext_in; intros; simpl. destruct a.
    unfold usedPIDsProc in H.
    rewrite not_elem_of_flat_union in H.
    apply elem_of_list_In in H0.
    apply H in H0. simpl in H0.
    rewrite double_PIDrenaming_val. 2: set_solver.
    unfold renamePIDPID.
    repeat case_match; eqb_to_eq; subst; try congruence.
    set_solver.
Qed.

Notation "e .⟦ x ↦ y ⟧ₚ" := (renamePIDProc x y e) (at level 2).

Definition renamePIDAct (from to : PID) (a : Action) : Action :=
  match a with
  | ASend sender receiver t =>
    ASend (renamePIDPID from to sender) (renamePIDPID from to receiver) (renamePIDSignal from to t)
  | AArrive sender receiver t =>
    AArrive (renamePIDPID from to sender) (renamePIDPID from to receiver) (renamePIDSignal from to t)
  | ASelf ι => ASelf (renamePIDPID from to ι)
  | ASpawn ι t1 t2 =>
    ASpawn (renamePIDPID from to ι) (renamePIDVal from to t1) (renamePIDVal from to t2)
  | τ => τ
  | ε => ε
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
 | ASpawn ι t1 t2 => {[ι]} ∪ usedPIDsVal t1 ∪ usedPIDsVal t2
 | τ => ∅
 | ε => ∅
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

Corollary elem_of_map_iff :
  ∀ (A B : Type) (f : A → B) (l : list A) (y : B),
    y ∈ (map f l) ↔ (∃ x : A, f x = y ∧ x ∈ l).
Proof.
  intros. rewrite elem_of_list_In. split; intros.
  * apply in_map_iff in H. destruct_hyps. do 2 eexists. eassumption.
    by apply elem_of_list_In.
  * destruct_hyps. apply elem_of_list_In in H0.
    apply in_map_iff. set_solver.
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
        apply elem_of_map_iff in H2 as [x [P_1 P_2]].
        unfold renamePIDPID in P_1. repeat break_match_hyp; eqb_to_eq; subst.
        ** contradiction.
        ** repeat apply not_elem_of_union in H1 as [H1 ?]. set_solver.
        ** repeat apply not_elem_of_union in H1 as [H1 ?]. set_solver.
        ** contradiction.
      + unfold renamePIDPID. repeat break_match_goal; eqb_to_eq; subst; set_solver.
  * simpl.
    replace ((map _ (map _ links))) with
        (map (λ l : PID, (l, reason'.⟦ from ↦ to ⟧ᵥ)) (map (renamePIDPID from to) links)).
    2: {
      now repeat rewrite map_map.
    }
    constructor. destruct_or!; destruct_and!; subst.
    - left. now split; auto.
    - right. left. repeat (split; auto).
      + intro. simpl in *.
        destruct reason; simpl in *; try congruence.
        break_match_hyp; congruence.
      + intro. apply H4 in H.
        apply elem_of_map_iff. exists source. split; auto.
      + intro. apply H6 in H.
        clear -H. intro; destruct reason; simpl in *; try congruence.
        break_match_hyp; congruence.
    - right. right. now split; auto.
  * simpl. rewrite mailboxPush_rename. simpl.
    pose proof (p_exit_convert (renamePIDStack from to fs) (e .⟦ from ↦ to ⟧ᵣ)
       (renamePIDMb from to mb) (map (renamePIDPID from to) links) (renamePIDPID from to dest) (renamePIDPID from to source) (reason .⟦ from ↦ to ⟧ᵥ) b).
    (* TODO: boiler plate code: *)
    destruct (from =? source) eqn:P.
    - unfold renamePIDPID in H at 6. rewrite Nat.eqb_sym in P. rewrite P in H.
      apply H. destruct_or!; destruct_and!.
      + left; split; auto. clear -H4. intro.
        destruct reason; simpl in *; try congruence.
        break_match_hyp; congruence.
      + right; split; auto. clear -H4.
        apply elem_of_map_iff. exists source. split; auto.
    - unfold renamePIDPID in H at 6. rewrite Nat.eqb_sym in P. rewrite P in H.
      apply H. destruct_or!; destruct_and!.
      + left; split; auto. clear -H4. intro.
        destruct reason; simpl in *; try congruence.
        break_match_hyp; congruence.
      + right; split; auto. clear -H4.
        apply elem_of_map_iff. exists source. split; auto.
  * simpl in *. repeat apply not_in_union in H1 as [H1 ?].
    rewrite map_renamePIDPID_remove; auto. now constructor.
    all: set_solver.
  * simpl in *. destruct Nat.eqb eqn:P; eqb_to_eq; subst.
    - replace (renamePIDPID ι to ι) with to by (unfold renamePIDPID; now rewrite Nat.eqb_refl). apply p_send. now apply renamePID_preserves_scope.
    - replace (renamePIDPID from to ι) with ι. 2: {
        unfold renamePIDPID. apply Nat.eqb_neq in P. rewrite Nat.eqb_sym in P.
        now rewrite P.
      }
      apply p_send. now apply renamePID_preserves_scope.
  * simpl in *. destruct Nat.eqb eqn:P; eqb_to_eq; subst.
    - replace (renamePIDPID ι to ι) with to by (unfold renamePIDPID; now rewrite Nat.eqb_refl). constructor. now apply renamePID_preserves_scope.
    - replace (renamePIDPID from to ι) with ι. 2: {
        unfold renamePIDPID. apply Nat.eqb_neq in P. rewrite Nat.eqb_sym in P.
        now rewrite P.
      }
      constructor. now apply renamePID_preserves_scope.
  * simpl in *. destruct Nat.eqb eqn:P; eqb_to_eq; subst.
    - replace (renamePIDPID ι to ι) with to by (unfold renamePIDPID; now rewrite Nat.eqb_refl). constructor.
    - replace (renamePIDPID from to ι) with ι. 2: {
        unfold renamePIDPID. apply Nat.eqb_neq in P. rewrite Nat.eqb_sym in P.
        now rewrite P.
      }
      constructor.
  * simpl in *. rewrite map_renamePIDPID_remove; auto.
    2: set_solver.
    destruct Nat.eqb eqn:P; eqb_to_eq; subst. 3: set_solver.
    - replace (renamePIDPID ι to ι) with to by (unfold renamePIDPID; now rewrite Nat.eqb_refl). constructor.
    - replace (renamePIDPID from to ι) with ι. 2: {
        unfold renamePIDPID. apply Nat.eqb_neq in P. rewrite Nat.eqb_sym in P.
        now rewrite P.
      }
      constructor.
  * simpl in *. constructor. now apply renamePID_preserves_scope.
  * simpl in *. destruct Nat.eqb eqn:P; eqb_to_eq; subst.
    - replace (renamePIDPID ι to ι) with to by (unfold renamePIDPID; now rewrite Nat.eqb_refl). constructor.
    - replace (renamePIDPID from to ι) with ι. 2: {
        unfold renamePIDPID. apply Nat.eqb_neq in P. rewrite Nat.eqb_sym in P.
        now rewrite P.
      }
      constructor.
  * simpl in *. destruct Nat.eqb eqn:P; eqb_to_eq; subst.
    - replace (renamePIDPID ι to ι) with to by (unfold renamePIDPID; now rewrite Nat.eqb_refl). constructor. now rewrite len_renamePID.
    - replace (renamePIDPID from to ι) with ι. 2: {
        unfold renamePIDPID. apply Nat.eqb_neq in P. rewrite Nat.eqb_sym in P.
        now rewrite P.
      }
      constructor. now rewrite len_renamePID.
  * simpl. constructor. rewrite peekMessage_renamePID, H2. reflexivity.
  * simpl. constructor. rewrite peekMessage_renamePID, H2. reflexivity.
  * simpl. rewrite recvNext_renamePID. constructor.
  * simpl. constructor. rewrite removeMessage_renamePID, H2. reflexivity.
  * simpl. apply p_recv_wait_timeout_invalid.
    all: intro X; destruct v; simpl in X; try congruence.
    all: break_match_hyp; congruence.
  * simpl. destruct flag; simpl; apply p_set_flag.
    all: destruct v; inv H2; simpl; auto.
  * simpl.
    replace (map _ (map _ _)) with
      (map (λ l, (l, VLit "normal"%string)) (map (renamePIDPID from to) links)).
    apply p_terminate.
    repeat rewrite map_map. now simpl.
  * simpl. destruct exc, p.
    replace (map _ (map _ _)) with
      (map (λ l, (l, (e, v0 .⟦ from ↦ to ⟧ᵥ, v .⟦ from ↦ to ⟧ᵥ).1.2)) (map (renamePIDPID from to) links)).
    apply p_terminate_exc.
    repeat rewrite map_map. now simpl.
Qed.
Transparent mailboxPush.

Corollary renamePID_id_proc :
  forall pr p, renamePIDProc p p pr = pr.
Proof.

Admitted.

Corollary renamePID_id_sig :
  forall s p, renamePIDSignal p p s = s.
Proof.

Admitted.

Corollary renamePID_id_act :
  forall a p, renamePIDAct p p a = a.
Proof.

Admitted.
