From CoreErlang.Concurrent Require Import BisimRenaming.

Import ListNotations.


Theorem normalisation :
  forall O (n n' : Node) l,
   (*  ether_wf n.1 -> *)
    (forall ι, ι ∈ (PIDsOf sendPIDOf l) -> ι ∉ O) -> (* Signals shouldn't be sent to the "world" *)
    (* (forall ι source dest s, In (AArrive source dest s, ι) l ->
                             n'.2 ι <> None) -> (* Signals should not
                                                   arrive to the "world" *) *)
    (* (forall ι ι', n.2 ι' = None -> n.1 ι ι' = []) -> *)
    O ## dom n.2 ->
    n -[l]ₙ->* n' with O ->
    n ~ n' observing O.
Proof.
  intros. apply barbedExpansion_implies_bisim.
  generalize dependent n. generalize dependent n'. revert l H. cofix IH. intros.
  constructor; auto.
  (* 1: split; [ by eapply reduction_produces_preCompatibleNodes; eassumption
            | by eapply reduction_produces_preCompatibleNodes_sym; try eassumption].
  1: now apply ether_wf_preserved in H2. *)
  * intros.
    rename n into A, A' into B, n' into C.
    admit.
  * intros. exists source. eapply reductions_preserve_singals_targeting_O in H2.
    - exact H2.
    - eassumption.
    - assumption.
    - assumption.
  * intros. exists B', (l ++ [(a, ι)]).
    split. 2: split. all: simpl.
    - rewrite app_length. slia.
    - eapply closureNodeSem_trans. eassumption. econstructor. eassumption. constructor.
    - apply barbedExpansion_refl.
(*       eapply ether_wf_preserved. 2: eassumption.
      eapply closureNodeSem_trans. eassumption. econstructor. eassumption. constructor.
 *)
  * intros. exists source, l, n'. split; auto.
    apply option_biforall_refl. intros. by apply Signal_eq_refl.
Abort.

(* It seems that this approach is not going to work, because the two
   cases should be handled separately, since  *)
Theorem compatiblePIDOf_options :
  forall a a',
    compatiblePIDOf a a' \/
    (exists from, (Some from = spawnPIDOf a \/ Some from = spawnPIDOf a') /\
      forall to1 to2, to1 ≠ to2 ->
      to1 ∉ usedPIDsAct a -> to1 ∉ usedPIDsAct a' ->
      to2 ∉ usedPIDsAct a -> to2 ∉ usedPIDsAct a' ->
      compatiblePIDOf (renamePIDAct from to1 a) (renamePIDAct from to2 a')).
Proof.
  intros. destruct a, a'; simpl; try by left; intros.
  * right. exists ι. split. by right. intros. renamePIDPID_case_match. set_solver.
  * right. exists ι. split. by left.  intros. renamePIDPID_case_match. set_solver.
  * right. exists ι. split. by left.  intros. renamePIDPID_case_match. set_solver.
Qed.

Theorem compatiblePIDOf_options_alt :
  forall a a',
    compatiblePIDOf a a' \/
    forall to, to ∉ usedPIDsAct a -> to ∉ usedPIDsAct a' ->
      (exists from, Some from = spawnPIDOf a /\
        compatiblePIDOf (renamePIDAct from to a) a') \/
      (exists from, Some from = spawnPIDOf a' /\
        compatiblePIDOf a (renamePIDAct from to a')).
Proof.
  intros. destruct a, a'; simpl; try by left; intros.
  * right; intros. right. exists ι. split. reflexivity. renamePIDPID_case_match. set_solver.
  * right; intros. left. exists ι. split. reflexivity. renamePIDPID_case_match. set_solver.
  * right; intros. left. exists ι. split. reflexivity. renamePIDPID_case_match. set_solver.
Qed.

(* Theorem compatiblePIDOf_options_alt :
  forall a a' n n' n'' ι ι' O,
    n -[a |ι]ₙ-> n' with O ->
    n -[a' |ι']ₙ-> n'' with O ->
    compatiblePIDOf a a' \/
    forall to, to ∉ usedPIDsAct a -> to ∉ usedPIDsAct a' ->
      (exists from, Some from = spawnPIDOf a /\ from ∉ usedPIDsAct a' /\
        compatiblePIDOf (renamePIDAct from to a) a') \/
      (exists from, Some from = spawnPIDOf a' /\ from ∉ usedPIDsAct a /\
        compatiblePIDOf a (renamePIDAct from to a')) \/
      (exists from, Some from = spawnPIDOf a /\ Some from = spawnPIDOf a' /\
        compatiblePIDOf a (renamePIDAct from to a')).
Proof.
  intros. destruct a, a'; simpl; try by left; intros.
  * right; intros. right. left. exists ι. split. reflexivity. renamePIDPID_case_match. set_solver.
  * right; intros. left. exists ι. split. reflexivity. renamePIDPID_case_match. set_solver.
  * right; intros. left. exists ι. split. reflexivity. renamePIDPID_case_match. set_solver.
Qed.
 *)
(* Theorem compatiblePIDOf_options_alt :
  forall a a' n n' O,
    n -[a |ι]ₙ-> n' with O ->
    compatiblePIDOf a a' \/
    forall to, to ∉ usedPIDsAct a -> to ∉ usedPIDsAct a' ->
      (exists from, Some from = spawnPIDOf a /\ from ∉ usedPIDsAct a' /\
        compatiblePIDOf (renamePIDAct from to a) a') \/
      (exists from, Some from = spawnPIDOf a' /\ from ∉ usedPIDsAct a /\
        compatiblePIDOf a (renamePIDAct from to a')) \/
      (exists from, Some from = spawnPIDOf a /\ Some from = spawnPIDOf a' /\
        ).
Proof.
  intros. destruct a, a'; simpl; try by left; intros.
  * right; intros. right. exists ι. split. reflexivity. renamePIDPID_case_match. set_solver.
  * right; intros. left. exists ι. split. reflexivity. renamePIDPID_case_match. set_solver.
  * right; intros. left. exists ι. split. reflexivity. renamePIDPID_case_match. set_solver.
Qed.
 *)

(*  *)
Theorem local_chainable :
  forall (A B C : Process) (a a' : Action),
     A -⌈a⌉-> B ->
     A -⌈a'⌉-> C ->
     (exists D, B -⌈a⌉-> D /\ C -⌈a'⌉-> D) \/
     (B = C) \/ (* if the actions were the same *)
     B -⌈a'⌉-> C \/ (* if a' is an exit *)
     C -⌈a⌉-> B (* if a is an exit *).
Proof.
  
Abort.

Instance Action_dec : EqDecision Action.
Proof.
  unfold EqDecision. intros. unfold Decision.
  decide equality; subst; auto.
  all: try apply Nat.eq_dec.
  all: try apply Signal_eq_dec.
  all: try apply Val_eq_dec.
  decide equality.
Defined.

(* Arrive and ε actions create non-confluent reductions with any other reduction of the same process instrumented by the inter-process semantics. *)
Definition isChainable (a : Action) : Prop :=
match a with
 | AArrive _ _ _ | ε | ASend _ _ SLink | ASend _ _ SUnlink => False
 | _ => True
end.

Theorem remove_subset :
  forall {A} eq_dec (l : list A) a,
    remove eq_dec a l ⊆ l.
Proof.
  intros.
  apply elem_of_subseteq. intros.
  apply elem_of_list_In in H.
  apply in_remove in H as [H _].
  by apply elem_of_list_In.
Qed.

Definition optional_update (Π : ProcessPool) (a : Action) (ιbase : PID) (s : Signal) : ProcessPool :=
match a with
| ASpawn ι v1 v2 f =>
  match mk_list v2 with
  | Some l =>
    (* NOTE: keep this consistent with the definition in NodeSemantics.v *)
    match create_result (IApp v1) l [], f with
    | Some (r, eff), true =>
      match Π !! ιbase, s with
      (* NOTE: Π !! ιbase is always going to be a dead process where this function is used *)
      | Some (inr links), SExit reas b =>
         match b, decide (reas = VLit "kill"%string) with
         | false, left _ =>
           ι ↦ inl ([], r, ([], []), if f then {[ι]} else ∅, false) ∥
           ιbase ↦ inr (<[ι:=VLit "killed"%string]>links) ∥ Π
         | _, _ =>
           ι ↦ inl ([], r, ([], []), if f then {[ι]} else ∅, false) ∥
           ιbase ↦ inr (<[ι:=reas]>links) ∥ Π
         end
      | _, _ => Π
      end
    | Some (r, eff), false => ι ↦ inl ([], r, ([], []), ∅, false) ∥ Π
    | _, _ => Π
    end
  | _ => Π
  end
| _ => Π
end.

(* This theorem won't hold
   In Lanese et al., Lemma 9 does not hold for this semantics,
   because arrival can change the semantics of receive primops!!!
   E.g., recv_peek_message returns None for empty mailbox, while the
   first message if it is nonempty (and arrival can put a message into the
   empty mailbox).

   In l,
*)
Theorem chain_arrive_later :
  forall O A B C a ι ιs s,
  a <> AArrive ιs ι s ->
  A -[ a | ι ]ₙ-> B with O ->
  isChainable a ->
  A -[ AArrive ιs ι s | ι]ₙ-> C with O ->
  exists D, B -[ AArrive ιs ι s | ι]ₙ-> D with O /\ (* Arrive can be evaluated later *)
    ((exists neweth, etherPop ιs ι B.1 = Some (s, neweth) /\ (* We remove the arrived signal from B's ether *)
     (neweth, optional_update C.2 a ι s) = D) \/ (* For spawns, there is a new process, moreover, for spawn_links the dead process has a new link in the list of links! *)
     C -[ a | ι ]ₙ-> D with O) (* For most actions, arrives are confluent *).
Proof.
  intros * Hneq HD1 ? HD2.
  inv HD2. 2: { destruct_or!; congruence. }
  inv H7.
  (* message arrival *)
  * inv HD1.
    - put (lookup ι : ProcessPool -> option _) on H2 as P.
      setoid_rewrite lookup_insert in P. inv P.
      inv H7.
     (* message send *)
     (* TODO: proofs for these cases are almost identical *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor.
           }
        right.
        assert (ι
    ↦ inl
    (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
    :: fs0, RValSeq [v0], mailboxPush mb v, links, flag) ∥ prs = ι
    ↦ inl
    (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
    :: fs0, RValSeq [v0], mailboxPush mb v, links, flag) ∥ prs0). {
               apply map_eq. intros.
               clear -H2.
               put (lookup i : ProcessPool -> _) on H2 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_send. by constructor.
      (* exit send *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [
        VPid ι'] [] :: fs0, RValSeq [v0], mailboxPush mb v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [
        VPid ι'] [] :: fs0, RValSeq [v0], mailboxPush mb v, links, flag) ∥ prs0). {
               apply map_eq. intros.
               clear -H2.
               put (lookup i : ProcessPool -> _) on H2 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_send. by constructor.
      (* link send *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] []
      :: fs0, RValSeq [VPid ι'], mailboxPush mb v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] []
      :: fs0, RValSeq [VPid ι'], mailboxPush mb v, links, flag) ∥ prs0). {
               apply map_eq. intros.
               clear -H2.
               put (lookup i : ProcessPool -> _) on H2 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_send. by constructor.
      (* unlink send *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "unlink"%string)) [] []
      :: fs0, RValSeq [VPid ι'], mailboxPush mb v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "unlink"%string)) [] []
      :: fs0, RValSeq [VPid ι'], mailboxPush mb v, links, flag) ∥ prs0). {
               apply map_eq. intros.
               clear -H2.
               put (lookup i : ProcessPool -> _) on H2 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_send. by constructor.
    (* arrivals - cannot happen *)
    - inv H.
    (* local actions *)
    - put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. inv P.
(* case separation is needed at this point, because
 exists can't be instantiated first, also ε actions
 could terminate a process -> no chaining

TODO: this cases a lot of boiler plate
*)
      destruct_or! H8; subst; inv H2.
      (* silent steps *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι ↦ inl (fs, e, mailboxPush mb v, links, flag) ∥ prs = ι ↦ inl (fs, e, mailboxPush mb v, links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. by constructor. by left.
      (* recv_peek_message - success *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox,
      mailboxPush mb v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox,
      mailboxPush mb v, links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. eapply p_recv_peek_message_ok.
             { destruct mb; clear-H10. simpl.
               destruct l0; inv H10. reflexivity. }
             by left.
      (* removeMessage *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "remove_message") [] [] :: fs0, RBox,
      mailboxPush mb v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "remove_message") [] [] :: fs0, RBox,
      mailboxPush mb v, links, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other.
        econstructor.
        {
          clear -H10. destruct mb. simpl in *.
          destruct l0; invSome. simpl.
          by rewrite app_assoc.
        }
        by left.
      (* recv_wait_timeout 0 *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      VLit 0%Z], mailboxPush mb v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      VLit 0%Z], mailboxPush mb v, links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. by constructor. by left.
      (* recv_wait_timeout error *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      v0], mailboxPush mb v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      v0], mailboxPush mb v, links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. by constructor. by left.
      (* self *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "self"%string)) [] []
      :: fs0, RBox, mailboxPush mb v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "self"%string)) [] []
      :: fs0, RBox, mailboxPush mb v, links, flag) ∥ Π). {
               apply map_eq. intros.
               clear -H1.
               put (lookup i : ProcessPool -> _) on H1 as HH.
               destruct (decide (i = ι)).
               * subst. by setoid_rewrite lookup_insert.
               * setoid_rewrite lookup_insert_ne; auto.
                 setoid_rewrite lookup_insert_ne in HH; auto.
             }
             setoid_rewrite H0.
             eapply n_other. by constructor. by right; left.
      (* recv_peek_message - fail - This cannot be proved
         after pushing a message, peekMessage won't fail anymore *)
      + inv H.
      (* recv_next *)
      + inv H.
      (* recv_wait_timeout infinity *)
      + inv H.
      (* normal termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* exceptional termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* setflag *)
      + inv H.
    (* spawns *)
    - inv H12.
      (* spawn *)
      {
        eexists. split.
        1: {
          setoid_rewrite insert_commute. 2: {
            intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
          }
          constructor. eassumption.
          constructor. }
        right.
        assert (ι ↦ inl (fs, e, mailboxPush mb v, links, flag) ∥ prs = ι ↦ inl (fs, e, mailboxPush mb v, links, flag) ∥  Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        setoid_rewrite insert_commute. 2: {
          intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
        }
        eapply n_spawn; try eassumption.
        1: {
          rewrite <- H0. rewrite H1 in H5.
          clear -H5 H7 H6.
          intro. apply isUsedPool_insert_1 in H as [H | [H | H]].
          * apply H5. apply isUsedPool_insert_2. by left.
          * subst. apply H5. left. by setoid_rewrite lookup_insert.
          * simpl in H. rewrite flat_union_app in H. simpl in H.
            assert (ι' ∉ usedPIDsVal v). {
              intro. apply H7.
              unfold etherPop in H6. repeat case_match; try congruence.
              subst. inv H6.
              right. right. do 3 eexists. split. exact H1.
              set_solver.
            }
            apply H5. right. exists ι. eexists.
            split. by setoid_rewrite lookup_insert.
            simpl. set_solver.
        }
        1: {
          clear -H6 H7.
          intro. eapply appearsEther_etherPop_rev in H; eauto.
        }
        put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. inv P.
        constructor; assumption.
      }
      { (* spawn_link - the proof is the same *)
         eexists. split.
        1: {
          setoid_rewrite insert_commute. 2: {
            intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
          }
          constructor. eassumption.
          constructor. }
        right.
        assert (ι ↦ inl (fs, e, mailboxPush mb v, links, flag) ∥ prs = ι ↦ inl (fs, e, mailboxPush mb v, links, flag) ∥  Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        setoid_rewrite insert_commute. 2: {
          intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
        }
        eapply n_spawn; try eassumption.
        1: {
          rewrite <- H0. rewrite H1 in H5.
          clear -H5 H7 H6.
          intro. apply isUsedPool_insert_1 in H as [H | [H | H]].
          * apply H5. apply isUsedPool_insert_2. by left.
          * subst. apply H5. left. by setoid_rewrite lookup_insert.
          * simpl in H. rewrite flat_union_app in H. simpl in H.
            assert (ι' ∉ usedPIDsVal v). {
              intro. apply H7.
              unfold etherPop in H6. repeat case_match; try congruence.
              subst. inv H6.
              right. right. do 3 eexists. split. exact H1.
              set_solver.
            }
            apply H5. right. exists ι. eexists.
            split. by setoid_rewrite lookup_insert.
            simpl. set_solver.
        }
        1: {
          clear -H6 H7.
          intro. eapply appearsEther_etherPop_rev in H; eauto.
        }
        put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. inv P.
        constructor; assumption.
      }
  (* exit dropped - it is potentially influenced by links, process flag *)
  * inv HD1.
    - put (lookup ι : ProcessPool -> option _) on H2 as P.
      setoid_rewrite lookup_insert in P. inv P.
      inv H7.
     (* message send *)
     (* TODO: proofs for these cases are almost identical *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor. set_solver.
           }
        right.
        eapply n_send. by constructor.
      (* exit send *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor. set_solver.
           }
        right.
        eapply n_send. by constructor.
      (* link send *)
      + inv H. (* can't be done *)
      (* unlink send *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor.
             set_solver.
           }
        right.
        eapply n_send. by constructor.
    (* arrivals - cannot happen *)
    - inv H.
    (* local actions *)
    - put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. inv P.
(* case separation is needed at this point, because
 exists can't be instantiated first, also ε actions
 could terminate a process -> no chaining

TODO: this cases a lot of boiler plate
*)
      destruct_or! H9; subst; inv H2.
      (* silent steps *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by left.
      (* recv_peek_message - success *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by left.
      (* removeMessage *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by intuition.
      (* recv_wait_timeout 0 *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by left.
      (* recv_wait_timeout error *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by left.
      (* self *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by right;left.
      (* recv_peek_message - fail *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by intuition.
      (* recv_next *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by intuition.
      (* recv_wait_timeout infinity *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by intuition.
      (* normal termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* exceptional termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* setflag *)
      + inv H.
    (* spawn *)
    - inv H13.
      { (* spawn *)
        put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. inv P.
        eexists. split.
        1: {
          setoid_rewrite insert_commute. 2: {
            intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
          }
          constructor. eassumption.
          constructor. assumption.
        }
        right.
        setoid_rewrite insert_commute. 2: {
          intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
        }
        eapply n_spawn; try eassumption.
        1: {
          clear -H6 H7.
          intro. eapply appearsEther_etherPop_rev in H; eauto.
        }
        constructor; assumption.
      }
      { (* spawn_link *)
        put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. inv P.
        eexists. split.
        1: {
          setoid_rewrite insert_commute. 2: {
            intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
          }
          constructor. eassumption.
          constructor.
          assert (ιs ≠ ι'). {
            intro. subst.
            apply H7. right. left.
            exists ι. intro.
            clear -H0 H6.
            unfold etherPop in H6. repeat case_match; try congruence.
          }
          clear -H8 H0.
          set_solver.
        }
        right.
        setoid_rewrite insert_commute. 2: {
          intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
        }
        eapply n_spawn; try eassumption.
        1: {
          clear -H6 H7.
          intro. eapply appearsEther_etherPop_rev in H; eauto.
        }
        constructor; assumption.
      }
  (* exit terminates - it is potentially influenced by links, process flag *)
  * inv HD1.
    - put (lookup ι : ProcessPool -> option _) on H2 as P.
      setoid_rewrite lookup_insert in P. inv P.
      inv H7.
     (* message send *)
     (* TODO: proofs for these cases are almost identical *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: by apply etherPop_greater.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H2 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* exit send *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: by apply etherPop_greater.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H2 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* link send - can't be done, since links are potentially modified *)
      + inv H.
      (* unlink send - can't be done, since links are potentially modified *)
      + inv H.
    (* arrivals - cannot happen *)
    - inv H.
    (* local actions *)
    - put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. inv P.
(* case separation is needed at this point, because
 exists can't be instantiated first, also ε actions
 could terminate a process -> no chaining

TODO: this cases a lot of boiler plate
*)
      destruct_or! H9; subst; inv H2.
      (* silent steps *)
      + eexists. split.
        1: { constructor. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: eassumption.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H1 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* recv_peek_message - success *)
      + eexists. split.
        1: { constructor. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: eassumption.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H1 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* removeMessage *)
      + eexists. split.
        1: { constructor. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: eassumption.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H1 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* recv_wait_timeout 0 *)
      + eexists. split.
        1: { constructor. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: eassumption.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H1 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* recv_wait_timeout error *)
      + eexists. split.
        1: { constructor. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: eassumption.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H1 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* self *)
      + eexists. split.
        1: { constructor. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: eassumption.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H1 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* recv_peek_message - fail *)
      + eexists. split.
        1: { constructor. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: eassumption.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H1 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* recv_next *)
      + eexists. split.
        1: { constructor. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: eassumption.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H1 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* recv_wait_timeout infinity *)
      + eexists. split.
        1: { constructor. eassumption.
             apply p_exit_terminate. set_solver.
           }
        left. simpl. eexists. split. 1: eassumption.
        f_equal. apply map_eq.
        intros. destruct (decide (ι = i)).
        1: subst; by setoid_rewrite lookup_insert.
        setoid_rewrite lookup_insert_ne; auto.
        put (lookup i : ProcessPool -> _) on H1 as H'.
        by setoid_rewrite lookup_insert_ne in H'.
      (* normal termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* exceptional termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* setflag *)
      + inv H.
    (* spawn -
       if the exit is delivered first, a process cannot be
       spawned *)
    - inv H13.
      {
        put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. inv P.
        eexists. split.
        1: {
          setoid_rewrite insert_commute. 2: {
            intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
          }
          constructor. eassumption.
          apply p_exit_terminate. eassumption.
        }
        left.
        assert (ι' <> ι). {
          intro. subst. apply H5. left. by setoid_rewrite lookup_insert.
        }
        eexists; split. simpl. eassumption.
        simpl. rewrite H2. simpl in H9. rewrite H9.
        f_equal.
        setoid_rewrite insert_commute at 1; auto.
        apply map_eq. intros.
        destruct (decide (i = ι)). 2: destruct (decide (i = ι')).
        all: subst.
        1: by setoid_rewrite lookup_insert.
        1: setoid_rewrite lookup_insert_ne; try lia.
        1: by setoid_rewrite lookup_insert.
        do 2 (setoid_rewrite lookup_insert_ne; try lia).
        put (lookup i : ProcessPool -> _) on H1 as H'.
        simpl in H'.
        by (setoid_rewrite lookup_insert_ne in H'; try lia).
      }
      {
      (* spawn_link is more tricky - can the arrive not termiate it? - potentially
         not, since ι' does not appear anywhere - thus it could not affect the behaviour *)
      - put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. inv P.
        eexists. split.
        1: {
          setoid_rewrite insert_commute. 2: {
            intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
          }
          constructor. eassumption.
          apply p_exit_terminate.
          assert (ιs ≠ ι'). {
            clear -H7 H6. intro. subst. apply H7.
            right. left. exists ι. intro.
            unfold etherPop in H6. repeat case_match; try congruence.
          }
          Unshelve. 2: exact reason'.
          clear -H0 H8. set_solver.
        }
        left.
        assert (ι' <> ι). {
          intro. subst. apply H5. left. by setoid_rewrite lookup_insert.
        }
        eexists; split. simpl. eassumption.
        simpl. rewrite H2. simpl in H9. rewrite H9.
        f_equal.
        setoid_rewrite insert_commute at 1; auto.
        apply map_eq. intros.
        setoid_rewrite lookup_insert.
        clear H9. repeat case_match.
        { (* NOTE: boiler plate for "killed" reason *)
          subst.
          destruct (decide (i = ι)). 2: destruct (decide (i = ι')).
          all: subst.
          1: {
             setoid_rewrite lookup_insert_ne; auto; setoid_rewrite lookup_insert.
             setoid_rewrite gset_to_gmap_union_singleton.
             clear -H8.
             intuition; subst; auto. congruence.
          }
          1: by setoid_rewrite lookup_insert.
          repeat (setoid_rewrite lookup_insert_ne; try lia).
          put (lookup i : ProcessPool -> _) on H1 as H'.
          simpl in H'.
          by (setoid_rewrite lookup_insert_ne in H'; try lia).
        }
        { (* original reason is kept *)
          subst.
          destruct (decide (i = ι)). 2: destruct (decide (i = ι')).
          all: subst.
          1: {
             setoid_rewrite lookup_insert_ne; auto; setoid_rewrite lookup_insert.
             setoid_rewrite gset_to_gmap_union_singleton.
             clear -H8.
             intuition; subst; auto. congruence.
          }
          1: by setoid_rewrite lookup_insert.
          repeat (setoid_rewrite lookup_insert_ne; try lia).
          put (lookup i : ProcessPool -> _) on H1 as H'.
          simpl in H'.
          by (setoid_rewrite lookup_insert_ne in H'; try lia).
        }
        { (* original reason is kept *)
          subst.
          destruct (decide (i = ι)). 2: destruct (decide (i = ι')).
          all: subst.
          1: {
             setoid_rewrite lookup_insert_ne; auto; setoid_rewrite lookup_insert.
             setoid_rewrite gset_to_gmap_union_singleton.
             clear -H8 n.
             intuition; subst; auto.
          }
          1: by setoid_rewrite lookup_insert.
          repeat (setoid_rewrite lookup_insert_ne; try lia).
          put (lookup i : ProcessPool -> _) on H1 as H'.
          simpl in H'.
          by (setoid_rewrite lookup_insert_ne in H'; try lia).
        }
      }
  (* exit converted - it is potentially influenced by links, process flag, mailbox *)
  * inv HD1.
    - put (lookup ι : ProcessPool -> option _) on H2 as P.
      setoid_rewrite lookup_insert in P. inv P.
      inv H7.
     (* message send *)
     (* TODO: proofs for these cases are almost identical *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             apply p_exit_convert. assumption.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
      :: fs0, RValSeq [v],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
      :: fs0, RValSeq [v],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs0). {
          apply map_eq. intros.
          clear -H2.
          put (lookup i : ProcessPool -> _) on H2 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_send. by constructor.
      (* exit send *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             apply p_exit_convert. assumption.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [
        VPid ι'] [] :: fs0, RValSeq [v],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [
        VPid ι'] [] :: fs0, RValSeq [v],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs0). {
          apply map_eq. intros.
          clear -H2.
          put (lookup i : ProcessPool -> _) on H2 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_send. by constructor.
      (* link send - maybe this should not be proved? *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             apply p_exit_convert.
             clear -H8. set_solver.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] []
      :: fs0, RValSeq [VPid ι'],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] []
      :: fs0, RValSeq [VPid ι'],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs0). {
        apply map_eq. intros.
        clear -H2.
        put (lookup i : ProcessPool -> _) on H2 as HH.
        destruct (decide (i = ι)).
        * subst. by setoid_rewrite lookup_insert.
        * setoid_rewrite lookup_insert_ne; auto.
          setoid_rewrite lookup_insert_ne in HH; auto.
      }
      setoid_rewrite H0.
      eapply n_send. by constructor.
      (* unlink send - can't be proved, list of links influence the behaviour of exits *)
      + inv H.
    (* arrivals - cannot happen *)
    - inv H.
    (* local actions *)
    - put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. inv P.
(* case separation is needed at this point, because
 exists can't be instantiated first, also ε actions
 could terminate a process -> no chaining

TODO: this cases a lot of boiler plate
*)
      destruct_or! H9; subst; inv H2.
      (* silent steps *)
      + eexists. split.
        1: { constructor. eassumption. apply p_exit_convert. assumption. }
        right.
        assert (ι
 ↦ inl
     (fs, e, mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]),
      links, true) ∥ prs = ι
 ↦ inl
     (fs, e, mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]),
      links, true) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. by constructor. by left.
      (* recv_peek_message - success *)
      + eexists. split.
        1: { constructor. eassumption. by apply p_exit_convert. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox,
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox,
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. eapply p_recv_peek_message_ok.
        { destruct mb; clear-H11. simpl.
          destruct l0; inv H11. reflexivity. }
        by left.
      (* removeMessage *)
      + eexists. split.
        1: { constructor. eassumption. by apply p_exit_convert. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "remove_message") [] [] :: fs0, RBox,
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "remove_message") [] [] :: fs0, RBox,
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ Π). {
         apply map_eq. intros.
         clear -H1.
         put (lookup i : ProcessPool -> _) on H1 as HH.
         destruct (decide (i = ι)).
         * subst. by setoid_rewrite lookup_insert.
         * setoid_rewrite lookup_insert_ne; auto.
           setoid_rewrite lookup_insert_ne in HH; auto.
       }
       setoid_rewrite H0.
       eapply n_other.
       econstructor.
       {
         clear -H11. destruct mb. simpl in *.
         destruct l0; invSome. simpl.
         by rewrite app_assoc.
       }
       by intuition.
      (* recv_wait_timeout 0 *)
      + eexists. split.
        1: { constructor. eassumption. by apply p_exit_convert. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      VLit 0%Z],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      VLit 0%Z],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. by constructor. by left.
      (* recv_wait_timeout error *)
      + eexists. split.
        1: { constructor. eassumption. by apply p_exit_convert. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [v],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [v],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. by constructor. by left.
      (* self *)
      + eexists. split.
        1: { constructor. eassumption. by apply p_exit_convert. }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "self"%string)) [] []
      :: fs0, RBox,
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "self"%string)) [] []
      :: fs0, RBox,
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. by constructor. by right; left.
      (* recv_peek_message - fail - This cannot be proved
         after pushing a message, peekMessage won't fail anymore *)
      + inv H.
      (* recv_next *)
      + inv H. (* eexists. split.
        1: { constructor. eassumption. by apply p_exit_convert. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_next") [] [] :: fs0, RBox,
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_next") [] [] :: fs0, RBox,
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
      true) ∥ Π). {
           apply map_eq. intros.
           clear -H1.
           put (lookup i : ProcessPool -> _) on H1 as HH.
           destruct (decide (i = ι)).
           * subst. by setoid_rewrite lookup_insert.
           * setoid_rewrite lookup_insert_ne; auto.
             setoid_rewrite lookup_insert_ne in HH; auto.
         }
         setoid_rewrite H0.
         destruct mb as [old new]. destruct new.
         1: admit. (* This won't work if the mailbox is empty *)
         assert (mailboxPush (recvNext (old, v :: new)) (VTuple [VLit "EXIT"%string; VPid ιs; reason]) = recvNext (mailboxPush (old, v :: new) (VTuple [VLit "EXIT"%string; VPid ιs; reason]))) by reflexivity.
         rewrite H2.
         eapply n_other. econstructor.
         by intuition. *)
      (* recv_wait_timeout infinity *)
      + eexists. split.
        1: { constructor. eassumption. by apply p_exit_convert. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0,
      RValSeq [VLit "infinity"%string],
      mailboxPush (oldmb, msg :: newmb)
        (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links, true) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0,
      RValSeq [VLit "infinity"%string],
      mailboxPush (oldmb, msg :: newmb)
        (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links, true) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other.
        econstructor.
        by intuition.
      (* normal termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* exceptional termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* setflag *)
      + inv H.
    (* spawn *)
    - inv H13.
      {
        put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. inv P.
        eexists. split.
        1: {
          setoid_rewrite insert_commute. 2: {
            intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
          }
          constructor. eassumption.
          by apply p_exit_convert.
        }
        right.
        assert (ι
   ↦ inl
       (FParams (ICall (VLit "erlang"%string) (VLit "spawn"%string))
          [VClos ext id vars e0] [] :: fs0, RValSeq [v2],
        mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
        true) ∥ prs = ι
   ↦ inl
       (FParams (ICall (VLit "erlang"%string) (VLit "spawn"%string))
          [VClos ext id vars e0] [] :: fs0, RValSeq [v2],
        mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links,
        true) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        setoid_rewrite insert_commute. 2: {
          intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
        }
        eapply n_spawn; try eassumption.
        1: {
          rewrite <- H0. rewrite H1 in H5.
          clear -H5 H7 H6.
          intro. apply isUsedPool_insert_1 in H as [H | [H | H]].
          * apply H5. apply isUsedPool_insert_2. by left.
          * subst. apply H5. left. by setoid_rewrite lookup_insert.
          * simpl in H. rewrite flat_union_app in H. simpl in H.
            assert (ι' ∉ usedPIDsVal reason /\ ι' <> ιs). {
              unfold etherPop in H6. repeat case_match; try congruence.
              split.
              * intro. apply H7.
                subst. inv H6.
                right. right. do 3 eexists. split. exact H0.
                set_solver.
              * intro. subst. apply H7. right. left.
                eexists. by rewrite H0.
            }
            apply H5. right. exists ι. eexists.
            split. by setoid_rewrite lookup_insert.
            simpl. set_solver.
        }
        1: {
          clear -H6 H7.
          intro. eapply appearsEther_etherPop_rev in H; eauto.
        }
        constructor; assumption.
      }
      { (* spawn_link *)
        put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. inv P.
        eexists. split.
        1: {
          setoid_rewrite insert_commute. 2: {
            intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
          }
          constructor. eassumption.
          apply p_exit_convert.
          (* NOTE: at this point we exploit that ι' is not used anywhere! *)
          assert (ι' ≠ ιs) as X. {
            clear -H6 H7. intro. subst.
            apply H7. right. left. exists ι. intro.
            unfold etherPop in H6. repeat case_match; try congruence.
          }
          clear -X H8. set_solver.
        }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "spawn_link"%string)) [VClos ext id vars e0] []
      :: fs0, RValSeq [v2], mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links, true)
 ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "spawn_link"%string)) [VClos ext id vars e0] []
      :: fs0, RValSeq [v2], mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links, true)
 ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        setoid_rewrite insert_commute. 2: {
          intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
        }
        eapply n_spawn; try eassumption.
        1: {
          rewrite <- H0. rewrite H1 in H5.
          clear -H5 H7 H6.
          intro. apply isUsedPool_insert_1 in H as [H | [H | H]].
          * apply H5. apply isUsedPool_insert_2. by left.
          * subst. apply H5. left. by setoid_rewrite lookup_insert.
          * simpl in H. rewrite flat_union_app in H. simpl in H.
            assert (ι' ∉ usedPIDsVal reason /\ ι' <> ιs). {
              unfold etherPop in H6. repeat case_match; try congruence.
              split.
              * intro. apply H7.
                subst. inv H6.
                right. right. do 3 eexists. split. exact H0.
                set_solver.
              * intro. subst. apply H7. right. left.
                eexists. by rewrite H0.
            }
            apply H5. right. exists ι. eexists.
            split. by setoid_rewrite lookup_insert.
            simpl. set_solver.
        }
        1: {
          clear -H6 H7.
          intro. eapply appearsEther_etherPop_rev in H; eauto.
        }
        constructor; assumption.
      }
  (* link arrives *)
  * inv HD1.
    - put (lookup ι : ProcessPool -> option _) on H2 as P.
      setoid_rewrite lookup_insert in P. inv P.
      inv H7.
     (* message send *)
     (* TODO: proofs for these cases are almost identical *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
      :: fs0, RValSeq [v], mb, {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
      :: fs0, RValSeq [v], mb, {[ιs]} ∪ links, flag) ∥ prs0). {
          apply map_eq. intros.
          clear -H2.
          put (lookup i : ProcessPool -> _) on H2 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_send. by constructor.
      (* exit send *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [
        VPid ι'] [] :: fs0, RValSeq [v], mb, {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [
        VPid ι'] [] :: fs0, RValSeq [v], mb, {[ιs]} ∪ links, flag) ∥ prs0). {
          apply map_eq. intros.
          clear -H2.
          put (lookup i : ProcessPool -> _) on H2 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_send. by constructor.
      (* link send - maybe this should not be proved? *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] []
      :: fs0, RValSeq [VPid ι'], mb, {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] []
      :: fs0, RValSeq [VPid ι'], mb, {[ιs]} ∪ links, flag) ∥ prs0). {
          apply map_eq. intros.
          clear -H2.
          put (lookup i : ProcessPool -> _) on H2 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_send. inv H. (* TODO: links should be formalised as sets *)
      (* unlink send - can't be proved if the same link is established and deleted in the two reductions *)
      + inv H.
    (* arrivals - cannot happen *)
    - inv H.
    (* local actions *)
    - put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. inv P.
(* case separation is needed at this point, because
 exists can't be instantiated first, also ε actions
 could terminate a process -> no chaining

TODO: this cases a lot of boiler plate
*)
      destruct_or! H8; subst; inv H2.
      (* silent steps *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι ↦ inl (fs, e, mb, {[ιs]} ∪ links, flag) ∥ prs = ι ↦ inl (fs, e, mb, {[ιs]} ∪ links, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. by constructor. by left.
      (* recv_peek_message - success *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      {[ιs]} ∪ links, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. eapply p_recv_peek_message_ok.
        assumption.
        by intuition.
      (* removeMessage *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "remove_message") [] [] :: fs0, RBox, mb,
      {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "remove_message") [] [] :: fs0, RBox, mb,
      {[ιs]} ∪ links, flag) ∥ Π). {
         apply map_eq. intros.
         clear -H1.
         put (lookup i : ProcessPool -> _) on H1 as HH.
         destruct (decide (i = ι)).
         * subst. by setoid_rewrite lookup_insert.
         * setoid_rewrite lookup_insert_ne; auto.
           setoid_rewrite lookup_insert_ne in HH; auto.
       }
       setoid_rewrite H0.
       eapply n_other.
       econstructor.
       assumption.
       by intuition.
     (* recv_wait_timeout 0 *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      VLit 0%Z], mb, {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      VLit 0%Z], mb, {[ιs]} ∪ links, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. by constructor. by left.
      (* recv_wait_timeout error *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [v], mb,
      {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [v], mb,
      {[ιs]} ∪ links, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. by constructor. by left.
      (* self *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "self"%string)) [] []
      :: fs0, RBox, mb, {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "self"%string)) [] []
      :: fs0, RBox, mb, {[ιs]} ∪ links, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. by constructor. by right; left.
      (* recv_peek_message - fail *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      {[ιs]} ∪ links, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. econstructor.
        assumption.
        by intuition.
      (* recv_next *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_next") [] [] :: fs0, RBox, mb, 
      {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_next") [] [] :: fs0, RBox, mb, 
      {[ιs]} ∪ links, flag) ∥ Π). {
           apply map_eq. intros.
           clear -H1.
           put (lookup i : ProcessPool -> _) on H1 as HH.
           destruct (decide (i = ι)).
           * subst. by setoid_rewrite lookup_insert.
           * setoid_rewrite lookup_insert_ne; auto.
             setoid_rewrite lookup_insert_ne in HH; auto.
         }
         setoid_rewrite H0.
         eapply n_other. econstructor.
         by intuition.
      (* recv_wait_timeout infinity *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0,
      RValSeq [VLit "infinity"%string], (oldmb, msg :: newmb), 
      {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0,
      RValSeq [VLit "infinity"%string], (oldmb, msg :: newmb), 
      {[ιs]} ∪ links, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other.
        econstructor.
        by intuition.
      (* normal termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* exceptional termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* setflag *)
      + inv H.
    (* spawn *)
    - inv H12.
      {
        put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. inv P.
        eexists. split.
        1: {
          setoid_rewrite insert_commute. 2: {
            intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
          }
          constructor. eassumption. constructor.
        }
        right.
        assert (ι
   ↦ inl
       (FParams (ICall (VLit "erlang"%string) (VLit "spawn"%string))
          [VClos ext id vars e0] [] :: fs0, RValSeq [v2], mb, 
        {[ιs]} ∪ links, flag) ∥ prs = ι
   ↦ inl
       (FParams (ICall (VLit "erlang"%string) (VLit "spawn"%string))
          [VClos ext id vars e0] [] :: fs0, RValSeq [v2], mb, 
        {[ιs]} ∪ links, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        setoid_rewrite insert_commute. 2: {
          intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
        }
        eapply n_spawn; try eassumption.
        1: {
          rewrite <- H0. rewrite H1 in H5.
          clear -H5 H7 H6.
          intro. apply isUsedPool_insert_1 in H as [H | [H | H]].
          * apply H5. apply isUsedPool_insert_2. by left.
          * subst. apply H5. left. by setoid_rewrite lookup_insert.
          * simpl in H.
            assert (ι' <> ιs). {
              unfold etherPop in H6. repeat case_match; try congruence.
              intro. subst. apply H7. right. left.
              eexists. by rewrite H0.
            }
            apply H5. right. exists ι. eexists.
            split. by setoid_rewrite lookup_insert.
            simpl. set_solver.
        }
        1: {
          clear -H6 H7.
          intro. eapply appearsEther_etherPop_rev in H; eauto.
        }
        constructor; assumption.
      }
      { (* spawn_link *)
        put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. inv P.
        eexists. split.
        1: {
          setoid_rewrite insert_commute. 2: {
            intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
          }
          constructor. eassumption. constructor.
        }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "spawn_link"%string)) [VClos ext id vars e0] []
      :: fs0, RValSeq [v2], mb, {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "spawn_link"%string)) [VClos ext id vars e0] []
      :: fs0, RValSeq [v2], mb, {[ιs]} ∪ links, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        setoid_rewrite insert_commute. 2: {
          intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
        }
        eapply n_spawn; try eassumption.
        1: {
          rewrite <- H0. rewrite H1 in H5.
          clear -H5 H7 H6.
          intro. apply isUsedPool_insert_1 in H as [H | [H | H]].
          * apply H5. apply isUsedPool_insert_2. by left.
          * subst. apply H5. left. by setoid_rewrite lookup_insert.
          * simpl in H.
            assert (ι' <> ιs). {
              unfold etherPop in H6. repeat case_match; try congruence.
              intro. subst. apply H7. right. left.
              eexists. by rewrite H0.
            }
            apply H5. right. exists ι. eexists.
            split. by setoid_rewrite lookup_insert.
            simpl. set_solver.
        }
        1: {
          clear -H6 H7.
          intro. eapply appearsEther_etherPop_rev in H; eauto.
        }
        replace ({[ιs]} ∪ ({[ι']} ∪ links)) with
          ({[ι']} ∪ ({[ιs]} ∪ links)) by (clear; set_solver).
        constructor; assumption.
      }
  (* unlink arrives *)
  * inv HD1.
    - put (lookup ι : ProcessPool -> option _) on H2 as P.
      setoid_rewrite lookup_insert in P. inv P.
      inv H7.
     (* message send *)
     (* TODO: proofs for these cases are almost identical *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
      :: fs0, RValSeq [v], mb, links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
      :: fs0, RValSeq [v], mb, links ∖ {[ιs]}, flag) ∥ prs0). {
          apply map_eq. intros.
          clear -H2.
          put (lookup i : ProcessPool -> _) on H2 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_send. by constructor.
      (* exit send *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [
        VPid ι'] [] :: fs0, RValSeq [v], mb, links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [
        VPid ι'] [] :: fs0, RValSeq [v], mb, links ∖ {[ιs]}, flag) ∥ prs0). {
          apply map_eq. intros.
          clear -H2.
          put (lookup i : ProcessPool -> _) on H2 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_send. by constructor.
      (* link send - maybe this should not be proved? *)
      + eexists. split.
        1: { constructor. apply etherPop_greater. eassumption.
             constructor.
           }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] []
      :: fs0, RValSeq [VPid ι'], mb, links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] []
      :: fs0, RValSeq [VPid ι'], mb, links ∖ {[ιs]}, flag) ∥ prs0). {
          apply map_eq. intros.
          clear -H2.
          put (lookup i : ProcessPool -> _) on H2 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_send. inv H. (* TODO: links should be formalised as sets *)
      (* unlink send - can't be proved if the same link is established and deleted in the two reductions *)
      + inv H.
    (* arrivals - cannot happen *)
    - inv H.
    (* local actions *)
    - put (lookup ι : ProcessPool -> option _) on H1 as P.
      setoid_rewrite lookup_insert in P. inv P.
(* case separation is needed at this point, because
 exists can't be instantiated first, also ε actions
 could terminate a process -> no chaining

TODO: this cases a lot of boiler plate
*)
      destruct_or! H8; subst; inv H2.
      (* silent steps *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι ↦ inl (fs, e, mb, links ∖ {[ιs]}, flag) ∥ prs = ι ↦ inl (fs, e, mb, links ∖ {[ιs]}, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. by constructor. by left.
      (* recv_peek_message - success *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      links ∖ {[ιs]}, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. eapply p_recv_peek_message_ok.
        assumption.
        by intuition.
      (* removeMessage *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "remove_message") [] [] :: fs0, RBox, mb,
      links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "remove_message") [] [] :: fs0, RBox, mb,
      links ∖ {[ιs]}, flag) ∥ Π). {
         apply map_eq. intros.
         clear -H1.
         put (lookup i : ProcessPool -> _) on H1 as HH.
         destruct (decide (i = ι)).
         * subst. by setoid_rewrite lookup_insert.
         * setoid_rewrite lookup_insert_ne; auto.
           setoid_rewrite lookup_insert_ne in HH; auto.
       }
       setoid_rewrite H0.
       eapply n_other.
       econstructor.
       assumption.
       by intuition.
      (* recv_wait_timeout 0 *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      VLit 0%Z], mb, links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      VLit 0%Z], mb, links ∖ {[ιs]}, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. by constructor. by left.
      (* recv_wait_timeout error *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [v], mb,
      links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [v], mb,
      links ∖ {[ιs]}, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. by constructor. by left.
      (* self *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "self"%string)) [] []
      :: fs0, RBox, mb, links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "self"%string)) [] []
      :: fs0, RBox, mb, links ∖ {[ιs]}, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. by constructor. by right; left.
      (* recv_peek_message - fail *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox, mb,
      links ∖ {[ιs]}, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other. econstructor.
        assumption.
        by intuition.
      (* recv_next *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_next") [] [] :: fs0, RBox, mb, 
      links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_next") [] [] :: fs0, RBox, mb, 
      links ∖ {[ιs]}, flag) ∥ Π). {
           apply map_eq. intros.
           clear -H1.
           put (lookup i : ProcessPool -> _) on H1 as HH.
           destruct (decide (i = ι)).
           * subst. by setoid_rewrite lookup_insert.
           * setoid_rewrite lookup_insert_ne; auto.
             setoid_rewrite lookup_insert_ne in HH; auto.
         }
         setoid_rewrite H0.
         eapply n_other. econstructor.
         by intuition.
      (* recv_wait_timeout infinity *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0,
      RValSeq [VLit "infinity"%string], (oldmb, msg :: newmb), 
      links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0,
      RValSeq [VLit "infinity"%string], (oldmb, msg :: newmb), 
      links ∖ {[ιs]}, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        eapply n_other.
        econstructor.
        by intuition.
      (* normal termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* exceptional termination *)
      + inv H. (* arrive can't be chained on a dead process *)
      (* setflag *)
      + inv H.
    (* spawn *)
    - inv H12.
      {
        put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. inv P.
        eexists. split.
        1: {
          setoid_rewrite insert_commute. 2: {
            intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
          }
          constructor. eassumption. constructor.
        }
        right.
        assert (ι
   ↦ inl
       (FParams (ICall (VLit "erlang"%string) (VLit "spawn"%string))
          [VClos ext id vars e0] [] :: fs0, RValSeq [v2], mb, 
        links ∖ {[ιs]}, flag) ∥ prs = ι
   ↦ inl
       (FParams (ICall (VLit "erlang"%string) (VLit "spawn"%string))
          [VClos ext id vars e0] [] :: fs0, RValSeq [v2], mb, 
        links ∖ {[ιs]}, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        setoid_rewrite insert_commute. 2: {
          intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
        }
        eapply n_spawn; try eassumption.
        1: {
          rewrite <- H0. rewrite H1 in H5.
          clear -H5 H7 H6.
          intro. apply isUsedPool_insert_1 in H as [H | [H | H]].
          * apply H5. apply isUsedPool_insert_2. by left.
          * subst. apply H5. left. by setoid_rewrite lookup_insert.
          * apply H5. right. exists ι. eexists.
            split. by setoid_rewrite lookup_insert.
            simpl.
            clear -H. simpl in H.
            set_solver.
        }
        1: {
          clear -H6 H7.
          intro. eapply appearsEther_etherPop_rev in H; eauto.
        }
        constructor; assumption.
      }
      { (* spawn_link *)
        put (lookup ι : ProcessPool -> option _) on H1 as P.
        setoid_rewrite lookup_insert in P. inv P.
        eexists. split.
        1: {
          setoid_rewrite insert_commute. 2: {
            intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
          }
          constructor. eassumption. constructor.
        }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "spawn_link"%string)) [VClos ext id vars e0] []
      :: fs0, RValSeq [v2], mb, links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "spawn_link"%string)) [VClos ext id vars e0] []
      :: fs0, RValSeq [v2], mb, links ∖ {[ιs]}, flag) ∥ Π). {
          apply map_eq. intros.
          clear -H1.
          put (lookup i : ProcessPool -> _) on H1 as HH.
          destruct (decide (i = ι)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HH; auto.
        }
        setoid_rewrite H0.
        setoid_rewrite insert_commute. 2: {
          intro. subst. apply H5. left. by setoid_rewrite lookup_insert. 
        }
        eapply n_spawn; try eassumption.
        1: {
          rewrite <- H0. rewrite H1 in H5.
          clear -H5 H7 H6.
          intro. apply isUsedPool_insert_1 in H as [H | [H | H]].
          * apply H5. apply isUsedPool_insert_2. by left.
          * subst. apply H5. left. by setoid_rewrite lookup_insert.
          * apply H5. right. exists ι. eexists.
            split. by setoid_rewrite lookup_insert.
            simpl.
            clear -H. simpl in H.
            set_solver.
        }
        1: {
          clear -H6 H7.
          intro. eapply appearsEther_etherPop_rev in H; eauto.
        }
        replace (({[ι']} ∪ links) ∖ {[ιs]}) with
          ({[ι']} ∪ (links ∖ {[ιs]})). 2: {
          (* NOTE: we exploit that ι' is fresh *)
          clear -H6 H7.
          assert (ι' ≠ ιs) as X. {
            intro. subst. apply H7.
            right. left. exists ι. intro.
            unfold etherPop in H6. repeat case_match; congruence.
          }
          set_solver.
        }
        constructor; assumption.
      }
Qed.

(*
  THOUGHTS.
  We can't prove normalisation of "Playing with bisimulation in Erlang".
  We could prove normalisation up to exits in a fully general way (spawns,
  compatible sends and τ could be included in the normalisation chain), though.

  Although, currently we couldn't prove map and concurrent map equivalent for
  their naive implementations?
  - The issue is with exit arriving after/before doing a spawn:
    - Parent terminates:
        One process will compute the result of the map, then send this result
        to the terminated parent, then it terminates. Since the parent is not
        in O (it is not observed), this would not show up in the observed messages.
    - Child terminates:
        Parent will be waiting forever for a message from the child

  To rule out exits, we can use the following approaches:
  - Define barbed bisimulation up to exits (~ᵉ), and prove that:
      A ~ B -> A ~ᵉ B
  - Is it enough to ensure that in the starting configuration, there are no
    exits in the ether? I suppose not, because the system can introduce them
    during evaluation, and we do not know how/when they get delivered.
  - No exits in the ether, and the reductions should not send exits.
  - We do not rule out exits from the normalisation, but then we have to rule out
    spawns.

  Would some mechanism (e.g., spawn_link), which would give us guarantees that
  the spawned process will be terminated too?
  - In this case, confluence is not going to be strict obviously (multiple steps instead of single ones)
  - In chain_arrive_later, B would reduce to D in three steps: arrive + send link exit + arrive link exit
  - Although, C and D would still not be equal, since one would contain a dead process which the other one an unused PID
  - spawn_link should be confluent with the arrives, because while the list of
    links is extended, that extension could 

  What if instead of an ether, we use an individual ether for each process,
  and the process local semantics determines whether it moves something from
  there to the mailbox/terminates the process/drops signals, etc.?
  - Probably would not help, since there should be an action representing
    this step of the local semantics which should be confluent with the others.


*)


Check chain_arrive_later.
Print Assumptions CIU_Val_compat_closed_reverse.
(* TODO: stricten isChainable by disallowing normal spawns! *)
Theorem confluence_any :
  ∀ (O : gset PID) (A B C : Node) (l : list (Action * PID)) (ι ιs : PID) (s : Signal),
    A -[l]ₙ->* B with O ->
    Forall (isChainable ∘ fst) l ->
    A -[ AArrive ιs ι s | ι ]ₙ-> C with O ->
    exists D,
      B -[ AArrive ιs ι s | ι ]ₙ-> D with O /\
      (* ((∃ neweth : Ether,
         etherPop ιs ι B.1 = Some (s, neweth)
         ∧ (neweth, optional_update C.2 a ι s) = D)
        ∨ C -[l]ₙ->* D with O) *)
        exists l' D', C -[l']ₙ->* D' with O(*  /\ D ~ D' observing O *) (*
                 - at this point D and D' only differ in dead processes, and messages targeting dead processes *)
        (* etherPop ιs ι B.1 = Some (s, neweth) /\
        D' = () *).
Proof.
  
Qed.

Theorem action_options :
  forall O n n' n'' a ι a' ι',
    n -[a | ι]ₙ-> n' with O ->
    n -[a' | ι']ₙ-> n'' with O ->
    ι = ι' ->
    a = a' \/
    (exists v1 v2 ι1 ι2 f1 f2, a = ASpawn ι1 v1 v2 f1 /\ a' = ASpawn ι2 v1 v2 f2) \/
    (exists s ιs, a = AArrive ιs ι s)
    \/ (exists s ιs, a' = AArrive ιs ι' s).
Proof.
  intros. subst. inv H; inv H0.
  (* NOTATION: single reduction + reduction from l *)
  (* send + send *)
  * subst. put (lookup ι' : ProcessPool -> option Process) on H3 as P.
    setoid_rewrite lookup_insert in P. inv P.
    inv H1; inv H6; try by left.
    (* TODO: both actions are sends from dead processes - with the new set-based
       presentation they can choose any exit signal to send to the defined targets *)
  (* arrive + send *)
  * right. right. right. by do 2 eexists.
  (* local + send - PIDs should be different *)
  * subst. put (lookup ι' : ProcessPool -> option Process) on H2 as P.
    setoid_rewrite lookup_insert in P. inv P.
    destruct_or!; subst; inv H1; inv H3; try by left.
    all: try (inv H8; by cbn in H6).
    all: try (inv H7; by cbn in H6).
  (* spawn + send - PIDs should be different *)
  * subst. put (lookup ι' : ProcessPool -> option Process) on H2 as P.
    setoid_rewrite lookup_insert in P. inv P.
    inv H1; inv H11; try by left.
  (* send + arrive *)
  * right. right. left. by do 2 eexists.
  (* arrive + arrive *)
  * right. right. left. by do 2 eexists.
  (* local + arrive *)
  * right. right. left. by do 2 eexists.
  (* spawn + arrive *)
  * right. right. left. by do 2 eexists.
  (* send + local - PIDs should be different *)
  * subst. put (lookup ι' : ProcessPool -> option Process) on H4 as P.
    setoid_rewrite lookup_insert in P. inv P.
    destruct_or!; subst; inv H1; inv H7; try by left.
    all: try (inv H; by cbn in H4).
  (* arrive + local *)
  * right. right. right. by do 2 eexists.
  (* local + local - PIDs should be different *)
  * subst. put (lookup ι' : ProcessPool -> option Process) on H3 as P.
    setoid_rewrite lookup_insert in P. inv P.
    destruct_or!; subst; inv H1; inv H4; try by left.
    all: try (inv H7; by cbn in *).
    all: try (inv H8; by cbn in *).
    all: try (inv H; by cbn in *).
    congruence.
    congruence.
  (* spawn + local - PIDs should be different *)
  * subst. put (lookup ι' : ProcessPool -> option Process) on H3 as P.
    setoid_rewrite lookup_insert in P. inv P.
    destruct_or!; subst; inv H1; inv H12; try by left.
    all: try (inv H; by cbn in *).
  (* send + spawn - PIDs should be different *)
  * subst. put (lookup ι' : ProcessPool -> option Process) on H8 as P.
    setoid_rewrite lookup_insert in P. inv P.
    inv H6; inv H11; try by left.
  (* arrive + spawn *)
  * right. right. right. by do 2 eexists.
  (* local + spawn - PIDs should be different *)
  * subst. put (lookup ι' : ProcessPool -> option Process) on H7 as P.
    setoid_rewrite lookup_insert in P. inv P.
    destruct_or!; inv H6; inv H8; try by left.
    inv H12. by cbn in *.
  (* spawn + spawn - PIDs should be different *)
  * subst. put (lookup ι' : ProcessPool -> option Process) on H7 as P.
    setoid_rewrite lookup_insert in P. inv P.
    inv H16. inv H6. subst.
    right. left. do 4 eexists. split; by reflexivity.
Qed.

Theorem action_chainable :
  (* NOTE: only l (and n n') can be constrained for the proof of normalisation!
     NOTE: don't forget that 
           we would like to prove equivalences like map ≈ paralell map *)
  forall l O A C, A -[l]ₙ->* C with O ->
    forall B a ι, A -[a | ι]ₙ-> B with O ->
      Forall (compatiblePIDOf a ∘ fst) l -> (* If some PID is not compatible, 
                                               we rename l *)
      Forall (isChainable ∘ fst) l ->
      (* (a, ι) ∈ l \/ *)
      (exists D l'', ((exists l', C -[l']ₙ->* D with O /\ length l' ≤ 1)
       \/ (exists from fresh, D = prod_map (renamePIDEther from fresh) (renamePIDPool from fresh) C) (* this part is needed for spawns + potentially exits in the future *))
       /\ B -[l'']ₙ->* D with O)
      (* (exists n''', n'' -[a | ι]ₙ-> n''' with O) \/ (* normal arrivals, sends, other processes can take the step at the end *)
      (True) (* if some processes die due to l *) *).
Proof.
  induction l using list_length_ind. rename H into IH.
  destruct l; intros ? ? ? HD1 ? ? ? HD2 Hcompat Harrives.
  {
    inv HD1. exists B, []. split. left. exists [(a, ι)]. split_and!; simpl.
    * econstructor. eassumption. constructor.
    * lia.
    * constructor.
  }
  {
    inv HD1.
    destruct (decide (ι = ι0)).
    {
      destruct (decide (a0 = a)). {
        subst. eapply concurrent_determinism in H2.
        2: exact HD2. subst.
        subst. exists C, l. split. left. exists []. split.
        - constructor.
        - slia.
        - assumption.
      }
      rename n into HX.
      subst.
      epose proof (action_options _ _ _ _ _ _ _ _ H2 HD2 eq_refl).
      intuition; destruct_hyps.
      * subst.
        assert (exists to, to ∉ flat_union (usedPIDsAct ∘ fst) l /\ ¬appearsEther to B.1 /\ ¬appearsEther to n'.1 /\ ¬isUsedPool to B.2 /\ ¬isUsedPool to n'.2 /\ to ∉ O). {
          admit. (* freshness *)
        }
        destruct H as [to [I1 [I2 [I3 [I4 [I5 I6]]]]]].
        exists (prod_map (renamePIDEther x1 to) (renamePIDPool x1 to) C), (map (prod_map (renamePIDAct x1 to) (renamePIDPID_sym x1 to)) l).
        split. right.
        - do 2 eexists. reflexivity.
        - replace B with (prod_map (renamePIDEther x1 to) (renamePIDPool x1 to) n').
          2: {
            inv HD2. 1: destruct_or!; congruence.
            inv H2. 1: destruct_or!; congruence.
            put (lookup ι0 : ProcessPool -> option Process) on H0 as P.
            setoid_rewrite lookup_insert in P. inv P.
            simpl. rewrite does_not_appear_renamePID_ether; auto.
            unfold renamePIDPool. clear IH.
            do 2 setoid_rewrite fmap_insert.
            do 2 (setoid_rewrite kmap_insert; auto).
            simpl.
            setoid_rewrite isNotUsed_renamePID_pool; auto.
            all: admit. (* TODO: technical, x1 is not used anywhere except the new PID *)
          }
          apply renamePID_is_preserved_node_semantics_steps; auto.
          by rewrite <- surjective_pairing, <- surjective_pairing.
      * subst. inv Harrives. destruct H1. (* arrives can't be in l *)
      * subst. inv Harrives. inv Hcompat.
        eapply chain_arrive_later in HD2; eauto.
        destruct HD2 as [D HD2].
        eapply IH in H4. 2: slia. 2: exact HD2.
        2-3: assumption.
        destruct H4 as [Dnew [l'' H4]].
        destruct H4 as [H4_1 H4_2].
        do 2 eexists. split.
        2: {
          
        }
      
      
        (* every combination of arrives should be checked *)
        inv HD2. 2: { destruct_or!; congruence. }
        inv H8.
        (* message arrival *)
        - inv H2.
          + put (lookup ι0 : ProcessPool -> option _) on H1 as P.
            setoid_rewrite lookup_insert in P. inv P.
            inv H8.
            (* message send *)
            (* TODO: proofs for these cases are almost identical *)
            ** eapply IH in H4. 2: slia. 3-4: by destruct_foralls.
               2: {
                 constructor.
                 apply etherPop_greater. eassumption.
                 by constructor.
               }
               destruct H4 as [D [l'' H4]].
               destruct H4 as [H4_1 H4_2].
               do 2 eexists. split.
                2: { eapply n_trans. 2: exact H4_2.
                       assert (ι0
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
      :: fs0, RValSeq [v0], mailboxPush mb v, links, flag) ∥ prs = ι0
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid ι'] []
      :: fs0, RValSeq [v0], mailboxPush mb v, links, flag) ∥ prs0). {
                         apply map_eq. intros.
                         clear -H1.
                         put (lookup i : ProcessPool -> _) on H1 as HH.
                         destruct (decide (i = ι0)).
                         * subst. by setoid_rewrite lookup_insert.
                         * setoid_rewrite lookup_insert_ne; auto.
                           setoid_rewrite lookup_insert_ne in HH; auto.
                       }
                       setoid_rewrite H.
                       eapply n_send. by constructor.
                  }
               destruct H4_1.
               -- destruct_hyps. left. eexists; split; eassumption.
               -- destruct_hyps. right. do 2 eexists; eassumption.
            (* exit send *)
            ** eapply IH in H4. 2: slia. 3-4: by destruct_foralls.
               2: {
                 constructor.
                 apply etherPop_greater. eassumption.
                 by constructor.
               }
               destruct H4 as [D [l'' H4]].
               destruct H4 as [H4_1 H4_2].
               do 2 eexists. split.
                2: { eapply n_trans. 2: exact H4_2.
                       assert (ι0
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [VPid ι'] []
      :: fs0, RValSeq [v0], mailboxPush mb v, links, flag) ∥ prs = ι0
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "exit"%string)) [VPid ι'] []
      :: fs0, RValSeq [v0], mailboxPush mb v, links, flag) ∥ prs0). {
                         apply map_eq. intros.
                         clear -H1.
                         put (lookup i : ProcessPool -> _) on H1 as HH.
                         destruct (decide (i = ι0)).
                         * subst. by setoid_rewrite lookup_insert.
                         * setoid_rewrite lookup_insert_ne; auto.
                           setoid_rewrite lookup_insert_ne in HH; auto.
                       }
                       setoid_rewrite H.
                       eapply n_send. by constructor.
                  }
               destruct H4_1.
               -- destruct_hyps. left. eexists; split; eassumption.
               -- destruct_hyps. right. do 2 eexists; eassumption.
            (* link send *)
            ** eapply IH in H4. 2: slia. 3-4: by destruct_foralls.
               2: {
                 constructor.
                 apply etherPop_greater. eassumption.
                 by constructor.
               }
               destruct H4 as [D [l'' H4]].
               destruct H4 as [H4_1 H4_2].
               do 2 eexists. split.
                2: { eapply n_trans. 2: exact H4_2.
                       assert (ι0
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] [] :: fs0,
      RValSeq [VPid ι'], mailboxPush mb v, links, flag) ∥ prs = ι0
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "link"%string)) [] [] :: fs0,
      RValSeq [VPid ι'], mailboxPush mb v, links, flag) ∥ prs0). {
                         apply map_eq. intros.
                         clear -H1.
                         put (lookup i : ProcessPool -> _) on H1 as HH.
                         destruct (decide (i = ι0)).
                         * subst. by setoid_rewrite lookup_insert.
                         * setoid_rewrite lookup_insert_ne; auto.
                           setoid_rewrite lookup_insert_ne in HH; auto.
                       }
                       setoid_rewrite H.
                       eapply n_send. by constructor.
                  }
               destruct H4_1.
               -- destruct_hyps. left. eexists; split; eassumption.
               -- destruct_hyps. right. do 2 eexists; eassumption.
            (* unlink send *)
            **  eapply IH in H4. 2: slia. 3-4: by destruct_foralls.
               2: {
                 constructor.
                 apply etherPop_greater. eassumption.
                 by constructor.
               }
               destruct H4 as [D [l'' H4]].
               destruct H4 as [H4_1 H4_2].
               do 2 eexists. split.
                2: { eapply n_trans. 2: exact H4_2.
                       assert (ι0
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "unlink"%string)) [] [] :: fs0,
      RValSeq [VPid ι'], mailboxPush mb v, links, flag) ∥ prs = ι0
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "unlink"%string)) [] [] :: fs0,
      RValSeq [VPid ι'], mailboxPush mb v, links, flag) ∥ prs0). {
                         apply map_eq. intros.
                         clear -H1.
                         put (lookup i : ProcessPool -> _) on H1 as HH.
                         destruct (decide (i = ι0)).
                         * subst. by setoid_rewrite lookup_insert.
                         * setoid_rewrite lookup_insert_ne; auto.
                           setoid_rewrite lookup_insert_ne in HH; auto.
                       }
                       setoid_rewrite H.
                       eapply n_send. by constructor.
                  }
               destruct H4_1.
               -- destruct_hyps. left. eexists; split; eassumption.
               -- destruct_hyps. right. do 2 eexists; eassumption.
          (* arrive *)
          + inv Harrives. destruct H5.
          (* local *)
          + put (lookup ι0 : ProcessPool -> option _) on H0 as P.
            setoid_rewrite lookup_insert in P. inv P.
            inv Hcompat. inv Harrives.
            (* case separation is needed at this point, because
               exists can't be instantiated first, also ε actions
               could terminate a process -> no chaining

              TODO: this cases a lot of boiler plate
             *)
            destruct_or! H9; subst; inv H1.
            (* silent steps *)
            ** eapply IH in H4. 2: slia. 3-4: eassumption.
               2: {
                 constructor; auto.
                 exact H7.
                 apply p_arrive.
               }
               destruct H4 as [D [l'' H4]].
               destruct H4 as [H4_1 H4_2].
               do 2 eexists. split.
               2: {
                  eapply n_trans. 2: exact H4_2.
                  assert (ι0 ↦ inl (fs, e, mailboxPush mb v, links, flag) ∥ prs = ι0 ↦ inl (fs, e, mailboxPush mb v, links, flag) ∥ Π). {
                    apply map_eq. intros.
                    clear -H0.
                     put (lookup i : ProcessPool -> _) on H0 as HH.
                    destruct (decide (i = ι0)).
                    * subst. by setoid_rewrite lookup_insert.
                    * setoid_rewrite lookup_insert_ne; auto.
                      setoid_rewrite lookup_insert_ne in HH; auto.
                  }
                 rewrite H.
                 eapply n_other. by apply p_local.
                 by left.
               }
               destruct H4_1.
               -- destruct_hyps. left. eexists; split; eassumption.
               -- destruct_hyps. right. do 2 eexists; eassumption.
            (* recv_wait_timeout *)
            ** eapply IH in H4. 2: slia. 3-4: eassumption.
               2: {
                 constructor; auto.
                 exact H7.
                 apply p_arrive.
               }
               destruct H4 as [D [l'' H4]].
               destruct H4 as [H4_1 H4_2].
               do 2 eexists. split.
               2: {
                  eapply n_trans. 2: exact H4_2.
                  assert (ι0
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      VLit 0%Z], mailboxPush mb v, links, flag) ∥ prs = ι0
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      VLit 0%Z], mailboxPush mb v, links, flag) ∥ Π). {
                    apply map_eq. intros.
                    clear -H0.
                     put (lookup i : ProcessPool -> _) on H0 as HH.
                    destruct (decide (i = ι0)).
                    * subst. by setoid_rewrite lookup_insert.
                    * setoid_rewrite lookup_insert_ne; auto.
                      setoid_rewrite lookup_insert_ne in HH; auto.
                  }
                 setoid_rewrite H.
                 eapply n_other. apply p_recv_wait_timeout_0.
                 by left.
               }
               destruct H4_1.
               -- destruct_hyps. left. eexists; split; eassumption.
               -- destruct_hyps. right. do 2 eexists; eassumption.
            (* recv_wait_timeout invalid *)
            ** eapply IH in H4. 2: slia. 3-4: eassumption.
               2: {
                 constructor; auto.
                 exact H7.
                 apply p_arrive.
               }
               destruct H4 as [D [l'' H4]].
               destruct H4 as [H4_1 H4_2].
               do 2 eexists. split.
               2: {
                  eapply n_trans. 2: exact H4_2.
                  assert (ι0
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      v0], mailboxPush mb v, links, flag) ∥ prs = ι0
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [
      v0], mailboxPush mb v, links, flag) ∥ Π). {
                    apply map_eq. intros.
                    clear -H0.
                     put (lookup i : ProcessPool -> _) on H0 as HH.
                    destruct (decide (i = ι0)).
                    * subst. by setoid_rewrite lookup_insert.
                    * setoid_rewrite lookup_insert_ne; auto.
                      setoid_rewrite lookup_insert_ne in HH; auto.
                  }
                 setoid_rewrite H.
                 eapply n_other. apply p_recv_wait_timeout_invalid.
                 1-2: assumption.
                 by left.
               }
               destruct H4_1.
               -- destruct_hyps. left. eexists; split; eassumption.
               -- destruct_hyps. right. do 2 eexists; eassumption.
            (* self *)
            ** eapply IH in H4. 2: slia. 3-4: eassumption.
               2: {
                 constructor; auto.
                 exact H7.
                 apply p_arrive.
               }
               destruct H4 as [D [l'' H4]].
               destruct H4 as [H4_1 H4_2].
               do 2 eexists. split.
               2: {
                  eapply n_trans. 2: exact H4_2.
                  assert (ι0
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "self"%string)) [] [] :: fs0,
      RBox, mailboxPush mb v, links, flag) ∥ prs = ι0
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "self"%string)) [] [] :: fs0,
      RBox, mailboxPush mb v, links, flag) ∥ Π). {
                    apply map_eq. intros.
                    clear -H0.
                     put (lookup i : ProcessPool -> _) on H0 as HH.
                    destruct (decide (i = ι0)).
                    * subst. by setoid_rewrite lookup_insert.
                    * setoid_rewrite lookup_insert_ne; auto.
                      setoid_rewrite lookup_insert_ne in HH; auto.
                  }
                 setoid_rewrite H.
                 eapply n_other. apply p_self.
                 by right; left.
               }
               destruct H4_1.
               -- destruct_hyps. left. eexists; split; eassumption.
               -- destruct_hyps. right. do 2 eexists; eassumption.
            (* peek_message *)
            ** eapply IH in H4. 2: slia. 3-4: eassumption.
               2: {
                 constructor; auto.
                 exact H7.
                 apply p_arrive.
               }
               destruct H4 as [D [l'' H4]].
               destruct H4 as [H4_1 H4_2].
               do 2 eexists. split.
               2: {
                  eapply n_trans. 2: exact H4_2.
                  assert (ι0
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox,
      mailboxPush mb v, links, flag) ∥ prs = ι0
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox,
      mailboxPush mb v, links, flag) ∥ Π). {
                    apply map_eq. intros.
                    clear -H0.
                     put (lookup i : ProcessPool -> _) on H0 as HH.
                    destruct (decide (i = ι0)).
                    * subst. by setoid_rewrite lookup_insert.
                    * setoid_rewrite lookup_insert_ne; auto.
                      setoid_rewrite lookup_insert_ne in HH; auto.
                  }
                 setoid_rewrite H.
                 eapply n_other. apply p_recv_peek_message_ok.
                 destruct mb; simpl in *. destruct l1; inv H14.
                 by simpl.
                 by intuition.
               }
               destruct H4_1.
               -- destruct_hyps. left. eexists; split; eassumption.
               -- destruct_hyps. right. do 2 eexists; eassumption.
            (* peek_message_fail *)
            ** eapply IH in H4. 2: slia. 3-4: eassumption.
               2: {
                 constructor; auto.
                 exact H7.
                 apply p_arrive.
               }
               destruct H4 as [D [l'' H4]].
               destruct H4 as [H4_1 H4_2].
               do 2 eexists. split.
               2: {
                  eapply n_trans. 2: exact H4_2.
                  assert (ι0
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox,
      mailboxPush mb v, links, flag) ∥ prs = ι0
 ↦ inl
     (FParams (IPrimOp "recv_peek_message") [] [] :: fs0, RBox,
      mailboxPush mb v, links, flag) ∥ Π). {
                    apply map_eq. intros.
                    clear -H0.
                     put (lookup i : ProcessPool -> _) on H0 as HH.
                    destruct (decide (i = ι0)).
                    * subst. by setoid_rewrite lookup_insert.
                    * setoid_rewrite lookup_insert_ne; auto.
                      setoid_rewrite lookup_insert_ne in HH; auto.
                  }
                 setoid_rewrite H.
                 eapply n_other. apply p_recv_peek_message_no_message.
                 destruct mb; simpl in *. destruct l1; inv H14.
                 by simpl.
                 by intuition.
               }
               destruct H4_1.
               -- destruct_hyps. left. eexists; split; eassumption.
               -- destruct_hyps. right. do 2 eexists; eassumption.
            **
            **
            **
            **
            **
            **
          (* spawn *)
          + put (lookup ι0 : ProcessPool -> option _) on H0 as P.
            setoid_rewrite lookup_insert in P. inv P. admit.
        (* exit drop *)
        - exfalso. inv Harrives.
          specialize (H1 _ _ _ eq_refl) as [? ?]. congruence.
        (* exit terminates *)
        - exfalso. inv Harrives.
          specialize (H1 _ _ _ eq_refl) as [? ?]. congruence.
        (* exit converted *)
        - exfalso. inv Harrives.
          specialize (H1 _ _ _ eq_refl) as [? ?]. congruence.
        (* link *)
        - exfalso. inv Harrives.
          specialize (H1 _ _ _ eq_refl) as [? ?]. congruence.
        (* unlink *)
        - exfalso. inv Harrives.
          specialize (H1 _ _ _ eq_refl) as [? ?]. congruence.
    }
    {
      (* pose proof (compatiblePIDOf_options_alt a a0) as [Ha | Ha ]. *)
      (* pose proof (compatiblePIDOf_options a a0) as [Ha | Ha ].
      { *)
      inv Hcompat. simpl in H1.
      pose proof (confluence _ _ _ _ _ HD2 _ _ _ H1 H2 n).
      destruct_hyps.
      eapply IH in H4. 3: exact H0. 2: slia. 2: eassumption.
      destruct H4 as [D [l'' H4]].
      destruct H4 as [H4_1 H4_2]. destruct H4_1.
      * destruct_hyps. exists D, ((a0, ι0)::l''). split.
        - left. exists x0. split; assumption.
        - econstructor; eassumption.
      * exists D, ((a0, ι0)::l''). split.
        - right. destruct_hyps. do 2 eexists. eassumption.
        - econstructor; eassumption.
Qed.

Theorem action_chainable_old :
  (* NOTE: only l (and n n') can be constrained for the proof of normalisation!
     NOTE: don't forget that 
           we would like to prove equivalences like map ≈ paralell map *)
  forall l O A C, A -[l]ₙ->* C with O ->
    forall B a ι, A -[a | ι]ₙ-> B with O ->
      (* Forall (compatiblePIDOf a ∘ fst) l -> (* If some PID is not compatible, 
                                               we rename l *) *)
      (* (a, ι) ∈ l \/ *)
      (exists D l'', ((exists l', C -[l']ₙ->* D with O /\ length l' ≤ 1)
       \/ (exists from fresh, D = prod_map (renamePIDEther from fresh) (renamePIDPool from fresh) C))
       /\ B -[l'']ₙ->* D with O)
      (* (exists n''', n'' -[a | ι]ₙ-> n''' with O) \/ (* normal arrivals, sends, other processes can take the step at the end *)
      (True) (* if some processes die due to l *) *).
Proof.
  induction l using list_length_ind. rename H into IH.
  destruct l; intros ? ? ? HD1 ? ? ? HD2.
  {
    inv HD1. exists B, []. split. left. exists [(a, ι)]. split_and!; simpl.
    * econstructor. eassumption. constructor.
    * lia.
    * constructor.
  }
  {
    inv HD1.
    destruct (decide (ι = ι0)).
    {
      subst.
      epose proof (action_options _ _ _ _ _ _ _ _ H2 HD2 eq_refl).
      intuition; destruct_hyps.
      * subst. eapply concurrent_determinism in HD2. 2: exact H2.
        subst. exists C, l. split. left. exists []. split.
        - constructor.
        - slia.
        - assumption.
      * subst.
        assert (exists to, to ∉ flat_union (usedPIDsAct ∘ fst) l /\ ¬appearsEther to B.1 /\ ¬appearsEther to n'.1 /\ ¬isUsedPool to B.2 /\ ¬isUsedPool to n'.2 /\ to ∉ O). {
          admit. (* freshness *)
        }
        destruct (decide (x1 = x2)). { (* same spawn - the inequality in needed later *)
          subst. eapply concurrent_determinism in HD2. 2: exact H2.
          subst. exists C, l. split. left. exists []. split.
          - constructor.
          - slia.
          - assumption.
        }
        destruct H as [to [I1 [I2 [I3 [I4 [I5 I6]]]]]].
        exists (prod_map (renamePIDEther x1 to) (renamePIDPool x1 to) C), (map (prod_map (renamePIDAct x1 to) (renamePIDPID_sym x1 to)) l).
        split. right.
        - do 2 eexists. reflexivity.
        - replace B with (prod_map (renamePIDEther x1 to) (renamePIDPool x1 to) n').
          2: {
            inv HD2. 1: destruct_or!; congruence.
            inv H2. 1: destruct_or!; congruence.
            put (lookup ι0 : ProcessPool -> option Process) on H0 as P.
            setoid_rewrite lookup_insert in P. inv P.
            simpl. rewrite does_not_appear_renamePID_ether; auto.
            unfold renamePIDPool. clear IH.
            do 2 setoid_rewrite fmap_insert.
            do 2 (setoid_rewrite kmap_insert; auto).
            simpl.
            setoid_rewrite isNotUsed_renamePID_pool; auto.
            all: admit. (* TODO: technical, x1 is not used anywhere except the new PID *)
          }
          apply renamePID_is_preserved_node_semantics_steps; auto.
          by rewrite <- surjective_pairing, <- surjective_pairing.
      * subst.
        (* every combination of arrives should be checked *)
        admit.
      * admit.
    }
    {
      (* pose proof (compatiblePIDOf_options_alt a a0) as [Ha | Ha ]. *)
      pose proof (compatiblePIDOf_options a a0) as [Ha | Ha ].
      {
        pose proof (confluence _ _ _ _ _ HD2 _ _ _ Ha H2 n).
        destruct_hyps.
        eapply IH in H4. 3: exact H0. 2: slia. destruct H4 as [D [l'' H4]].
        destruct H4 as [H4_1 H4_2]. destruct H4_1.
        * destruct_hyps. exists D, ((a0, ι0)::l''). split.
          - left. exists x0. split; assumption.
          - econstructor; eassumption.
        * exists D, ((a0, ι0)::l''). split.
          - right. destruct_hyps. do 2 eexists. eassumption.
          - econstructor; eassumption.
      }
      {
        (* assert (exists to, to ∉ flat_union (usedPIDsAct ∘ fst) l /\ ¬appearsEther to A.1 /\ ¬appearsEther to n'.1 /\ ¬isUsedPool to A.2 /\ ¬isUsedPool to n'.2 /\ to ∉ O /\
        to ∉ usedPIDsAct a /\ to ∉ usedPIDsAct a0). {
          admit. (* freshness *)
        }
        destruct H as [to ?]. destruct_hyps.
        specialize (Ha to H7 H8) as [Ha | Ha].
        { (* a0 needs to be renamed *)
          destruct A as [Aeth AΠ].
          destruct B as [Beth BΠ].
          destruct Ha as [from [Ha1 Ha2]].
          eapply renamePID_is_preserved_node_semantics in HD2 as HD2'.
          2-5: eassumption.
          Unshelve. 2: exact from.
          assert (¬ appearsEther from Aeth /\ ¬isUsedPool from AΠ /\ from <> ι0) as [Hfrom1 [Hfrom2 Hfrom3]]. {
            destruct a; inv Ha1. inv HD2. destruct_or!; congruence.
            split_and!; try assumption.
            intro. subst. apply H19.
            left. inv H2; by setoid_rewrite lookup_insert.
          }
          rewrite does_not_appear_renamePID_ether in HD2'; auto.
          rewrite isNotUsed_renamePID_pool in HD2'; auto.
          assert (renamePIDPID_sym from to ι ≠ ι0) as X. {
            renamePIDPID_sym_case_match.
            intro. subst. apply H3. left. inv H2; by setoid_rewrite lookup_insert.
          }
          pose proof (confluence _ _ _ _ _ HD2' _ _ _ Ha2 H2 X).
          destruct_hyps.
          destruct n' as [n'eth n'Π].
          destruct C as [Ceth CΠ].
          apply renamePID_is_preserved_node_semantics_steps with (from := from) (to := to) in H4; auto.
          
          eapply IH in H4. 2: rewrite map_length; simpl; clear.
          2: { (* NOTE For some reason, lia does not work here *)
            apply NPeano.Nat.lt_succ_diag_r.
          }
          2: {
            rewrite does_not_appear_renamePID_ether; auto.
            rewrite isNotUsed_renamePID_pool; auto.
            exact H10.
            eapply not_isUsedPool_step; try eassumption.
          }
          destruct H4 as [D [l'' H4]].
          destruct H4 as [H4_1 H4_2]. destruct H4_1.
          * destruct_hyps. exists D, ((a1, ι0)::l''). split.
            - left. exists x0. split; assumption.
            - econstructor; eassumption.
          * exists D, ((a1, ι0)::l''). split.
            - right. destruct_hyps. do 2 eexists. eassumption.
            - econstructor; eassumption.
        }
        { (* a1 needs to be renamed *)
        
        } *)
        
        
        
        
        destruct Ha as [from Ha].
        assert (exists to1, to1 ∉ flat_union (usedPIDsAct ∘ fst) l /\ ¬appearsEther to1 A.1 /\ ¬appearsEther to1 n'.1 /\ ¬isUsedPool to1 A.2 /\ ¬isUsedPool to1 n'.2 /\ to1 ∉ O /\
        to1 ∉ usedPIDsAct a /\ to1 ∉ usedPIDsAct a0). {
          admit. (* freshness *)
        }
        destruct H as [to1 ?]. destruct_hyps.
        assert (exists to2, to2 ∉ flat_union (usedPIDsAct ∘ fst) l /\ ¬appearsEther to2 A.1 /\ ¬appearsEther to2 n'.1 /\ ¬isUsedPool to2 A.2 /\ ¬isUsedPool to2 n'.2 /\ to2 ∉ O /\
        to2 ∉ usedPIDsAct a /\ to2 ∉ usedPIDsAct a0 /\ to1 ≠ to2). {
          admit. (* freshness *)
        }
        destruct H11 as [to2 ?]. destruct_hyps.
        (* it matters which one of the actions is going to be renamed (which is the spawn) *)
        (* destruct H9.
        {
          specialize (H10 to H7 H8).
          destruct A as [Aeth AΠ]. destruct B as [Beth BΠ].
          destruct n' as [n'eth n'Π].
          eapply renamePID_is_preserved_node_semantics in H2.
          5: eassumption. 2-4: try assumption.
        }
        {
        
        } *)
        
        
        assert (¬ isUsedPool from A.2 /\ ¬appearsEther from A.1 /\ from <> ι /\ from <> ι0) as [HF1 [HF2 [HF3 HF4]]]. {
          destruct H9.
          * destruct a; inv H9. inv HD2. destruct_or!; congruence.
            repeat split; auto.
            all: intro; subst.
            apply H24. left. by setoid_rewrite lookup_insert.
            apply H24. inv H2; left; by setoid_rewrite lookup_insert.
          * destruct a0; inv H9. inv H2. destruct_or!; congruence.
            repeat split; auto.
            all: intro; subst.
            apply H24. inv HD2; left; by setoid_rewrite lookup_insert.
            apply H24. left. by setoid_rewrite lookup_insert.
        }
        specialize (H10 to1 to2 H19 H7 H8 H17 H18).
        destruct A as [Aeth AΠ]. destruct B as [Beth BΠ].
        destruct n' as [n'eth n'Π]. destruct C as [Ceth CΠ].
        simpl in *.
        apply renamePID_is_preserved_node_semantics with (from := from) (to := to2) in H2 as H2D.
        5: eassumption. 2-4: try assumption.
        apply renamePID_is_preserved_node_semantics with (from := from) (to := to1) in HD2 as HD2D.
        5: eassumption. 2-4: try assumption.
        simpl in *.
        rewrite does_not_appear_renamePID_ether in H2D, HD2D; auto.
        rewrite isNotUsed_renamePID_pool in H2D, HD2D; auto.
        replace (renamePIDPID_sym from to1 ι0) with ι0 in H2D.
        replace (renamePIDPID_sym from to2 ι) with ι in HD2D.
        2: {
          renamePIDPID_sym_case_match.
          admit. (* TODO technical from H7 + H8 and H9 *)
        }
        2: {
          renamePIDPID_sym_case_match.
          admit. (* TODO technical from H7 + H8 and H9 *)
        }
        epose proof (confluence _ _ _ _ _ HD2D _ _ _ H10 H2D _). Unshelve.
        2: {
          renamePIDPID_sym_case_match.
          admit. (* TODO technical from H7 + H8 and H9 *)
        }
        destruct_hyps.
        apply renamePID_is_preserved_node_semantics_steps with (from := from) (to := to1) in H4 as H4D.
        5: eassumption. 2-4: try assumption.
        
        
        
        eapply IH in H4D as H4DD. 2: admit. 2: exact H21. destruct H4DD as [D [l'' H4']].
        destruct H4' as [H4_1 H4_2]. destruct H4_1.
        * destruct_hyps.
          eapply n_trans in H4_2. 2: exact H20.
         exists D, ((a1, ι0)::l''). split.
          - left. exists x0. split; assumption.
          - econstructor; eassumption.
        * exists D, ((a1, ι0)::l''). split.
          - right. destruct_hyps. do 2 eexists. eassumption.
          - econstructor; eassumption.
      }
    }
Abort.

(* This would be a consequence of normalisation, but exits break this property
   too. E.g., a potential exit could terminate A, and not B. *)
Theorem normalise_common :
  forall A B C O l₁ l₂,
    A -[l₁]ₙ->* C with O ->
    B -[l₂]ₙ->* C with O ->
    A ~ B observing O.





