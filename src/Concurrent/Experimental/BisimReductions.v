From CoreErlang.Concurrent Require Import BisimRenaming.

Import ListNotations.

Theorem difference_O :
  forall O n n' a ι,
    dom n.2 ## O ->
    n -[a | ι]ₙ-> n' with O ->
    dom n'.2 ## O.
Proof.
  intros. inv H0; simpl in *; setoid_rewrite dom_insert_L; setoid_rewrite dom_insert_L in H.
  1-3: set_solver.
  setoid_rewrite dom_insert_L. set_solver.
Qed.

Theorem normalisation_τ :
  forall O (n n' : Node) ι,
    O ## dom n.2 ->
    n -[τ | ι]ₙ-> n' with O ->
    n ~ n' observing O.
Proof.
  intros. apply barbedExpansion_implies_bisim.
  generalize dependent n. generalize dependent n'. revert ι. cofix IH. intros.
  constructor; auto.
  * intros.
    rename n into A, A' into B, n' into C.
    destruct (decide (ι = ι0)).
    {
      subst. eapply internal_det in H1 as H0'. 2: exact H0.
      destruct H0'; destruct_hyps.
      * subst. exists C, []. split_and!.
        - slia.
        - constructor.
        - apply barbedExpansion_refl.
      * subst. destruct H4.
        { (* confluence *)
          do 2 eexists. split_and!.
          2: {
            eapply n_trans. exact H3. apply n_refl.
          }
          slia.
          eapply IH. 2: exact H2.
          by apply difference_O in H1.
        }
        { (* termination *)
          subst. exists x1. eexists.
          split_and!.
          2: {
            eapply n_trans. exact H3. apply n_refl.
          }
          slia.
          apply barbedExpansion_refl.
        }
    }
    { (* ι ≠ ι0 *)
      epose proof confluence _ _ _ _ _ H0 _ _ _ _ H1 n.
      Unshelve. 2: by simpl.
      destruct_hyps.
      exists x, [(a, ι0)]. split_and!.
      - slia.
      - econstructor. eassumption. constructor.
      - eapply IH. 2: exact H3.
        by apply difference_O in H1.
    }
  * clear IH. intros. exists source.
    eapply n_trans in H0 as HD. 2: eapply n_refl.
    eapply reductions_preserve_singals_targeting_O in HD.
    - exact HD.
    - eassumption.
    - simpl. set_solver.
    - assumption.
  * clear IH. intros. exists B', [(τ, ι); (a, ι0)].
    split. 2: split. all: simpl.
    - slia.
    - econstructor. eassumption. econstructor. eassumption. constructor.
    - apply barbedExpansion_refl.
  * clear IH. intros. exists source, [(τ, ι)], n'. split; auto.
    econstructor. eassumption. constructor.
    apply option_biforall_refl. intros. by apply Signal_eq_refl.
Qed.

Theorem normalisation_τ_many :
  forall l O (n n' : Node),
    Forall (fun x => x.1 = τ) l ->
    O ## dom n.2 ->
    n -[l]ₙ->* n' with O ->
    n ~ n' observing O.
Proof.
  induction l; intros.
  * inv H1. apply barbedBisim_refl.
  * inv H1. inv H. simpl in *. subst.
    eapply barbedBisim_trans.
    eapply normalisation_τ; eauto.
    apply IHl; try assumption.
    by apply difference_O in H5.
Qed.

Theorem deconstruct_reduction :
  forall O A B ι a eth eth',
    (eth, A) -[a | ι]ₙ-> (eth', B) with O->
    exists p p' A' B', A = ι ↦ p ∥ A' /\ B = ι ↦ p' ∥ B' /\
      p -⌈a⌉-> p'.
Proof with subst; left; by setoid_rewrite lookup_insert.
  intros. inv H; do 4 eexists; split_and!; try reflexivity; try assumption.
  setoid_rewrite insert_commute at 1. reflexivity.
  intro. apply H6...
  assumption.
Qed.

(* InductiveNodeSemantics.v *)
Theorem etherAdd_step :
  forall A B O ι a,
    A -[a | ι]ₙ-> B with O ->
    forall ιs ιd s,
      (forall ι', spawnPIDOf a = Some ι' -> ιs <> ι' /\ ιd <> ι' /\ ι' ∉ usedPIDsSignal s) ->
      (ι = ιs -> sendPIDOf a <> Some ιd) -> (* The addition to the ether should not be in conflict with the (send) action taken *)
      (etherAdd ιs ιd s A.1, A.2) -[a | ι]ₙ-> (etherAdd ιs ιd s B.1, B.2) with O.
Proof with by setoid_rewrite lookup_insert.
  intros. inv H; simpl in *; try constructor; auto.
  * destruct (decide (ιs = ι)). destruct (decide (ιd = ι')).
    - subst. exfalso. by apply (H1 eq_refl).
    - rewrite etherAdd_swap_2; auto. by apply n_send.
    - rewrite etherAdd_swap_1; auto. by apply n_send.
  * by apply etherPop_greater.
  * econstructor; try eassumption.
    intro. apply appearsEther_etherAdd_rev in H. congruence.
    1-3: apply (H0 ι' eq_refl).
Qed.

Theorem etherExtend_bisim :
  forall O eth Π ιs ιd s,
    ιd ∉ O ->
    (* -> direction holds based on the previous theorem + renaming
       <- direction won't hold though, because the node on the right
          hand side potentially could do an AArrive which cannot be done
          in the left side *)
    (eth, Π) ~ (etherAdd ιs ιd s eth, Π) observing O.
Proof.
  intros. constructor.
Abort.

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
 | AArrive _ _ _ | ε | ASend _ _ SLink | ASend _ _ SUnlink
 | ASpawn _ _ _ false => False (* normal spaws are not chainable, because
                                  they potentially create a process that
                                  communicates to an observable node, without
                                  killing it on exit arrival *)
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
           ι ↦ inl ([], r, ([], []), if f then {[ιbase]} else ∅, false) ∥
           ιbase ↦ inr (<[ι:=VLit "killed"%string]>links) ∥ Π
         | _, _ =>
           ι ↦ inl ([], r, ([], []), if f then {[ιbase]} else ∅, false) ∥
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

(* Definition node_from (a : Action) (s : Signal) (B : Node) : Node :=
match a, s with
 | ASend sender receiver t, SExit reas b  =>
   match B.1 !! (sender, receiver), B.2 !! sender with
   (* only this can occur - since we are inside a send action *)
   | Some l, Some (_, _, _, links, _) =>
     (<[(sender, receiver) := removelast l]>B.1 , sender ↦ inr () ∥ B.2)
   (* this cannot occur *)
   | _ => B
   end
 | ASpawn ι t1 t2 link, SExit reas b  => _
 (* arrives and εs are filtered by isChainable *)
 | _, _ => B
end. *)


(* This theorem won't hold
   In Lanese et al., Lemma 9 does not hold for this semantics,
   because arrival can change the semantics of receive primops!!!
   E.g., recv_peek_message returns None for empty mailbox, while the
   first message if it is nonempty (and arrival can put a message into the
   empty mailbox).

   In l,
*)
Print isChainable.
Theorem chain_arrive_later :
  forall O A B C a ι ιs s,
  (* a <> AArrive ιs ι s -> *)
  A -[ a | ι ]ₙ-> B with O ->
  isChainable a ->
  A -[ AArrive ιs ι s | ι]ₙ-> C with O ->
  exists D, B -[ AArrive ιs ι s | ι]ₙ-> D with O /\ (* Arrive can be evaluated later *)
    ((exists neweth, etherPop ιs ι B.1 = Some (s, neweth) /\ (* We remove the arrived signal from B's ether *)
     (neweth, optional_update C.2 a ι s) = D (*/\
     C = node_from a s B *)) \/ (* For spawns, there is a new process, moreover, for spawn_links the dead process has a new link in the list of links! *)
     C -[ a | ι ]ₙ-> D with O) (* For most actions, arrives are confluent *).
Proof.
  intros * (* Hneq *) HD1 ? HD2.
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


(* Arrive and ε actions create non-confluent reductions with any other reduction of the same process instrumented by the inter-process semantics. *)
Definition isChainable2 (a : Action) : Prop :=
match a with
 | τ | ASpawn _ _ _ true | ASelf _  => True
 | _ => False
end.

(* Definition optional_update2 (Π : ProcessPool) (a : Action) (ιbase : PID) (s : Signal) : ProcessPool :=
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
end. *)


Theorem chain_arrive_later_2 :
  forall O A B C a ι ιs s,
  (* a <> AArrive ιs ι s -> *)
  A -[ a | ι ]ₙ-> B with O ->
  isChainable2 a ->
  A -[ AArrive ιs ι s | ι]ₙ-> C with O ->
  exists D, B -[ AArrive ιs ι s | ι]ₙ-> D with O /\ (* Arrive can be evaluated later *)
    ((
     (C.1, optional_update C.2 a ι s) = D
(*      /\
     forall p p',
       A !! ι = Some (inl p) ->
       B !! ι = Some (inl p') ->
       inl p -⌈a⌉-> inl p' /\ inl p -⌈AArrive ιs ι s⌉-> inr p.1.2 *)
     (*/\
     C = node_from a s B *)) \/ (* For spawns, there is a new process, moreover, for spawn_links the dead process has a new link in the list of links! *)
     C -[ a | ι ]ₙ-> D with O) (* For most actions, arrives are confluent *).
Proof.
  intros * (* Hneq *) HD1 ? HD2.
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
    - inv H.
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
        left. simpl.
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
        left. simpl.
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
        left. simpl.
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
        left. simpl.
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
        left. simpl.
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
        left. simpl.
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
        left. simpl.
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
        left. simpl.
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
        left. simpl.
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


Unset Guard Checking.
Theorem dead_process_congruence :
  forall O A ι,
    ι ∉ O ->
    (* ¬isUsedPool ι A.2 -> *)
    ι ∉ dom A.2 ->
    A ~ (A.1, ι ↦ inr ∅ ∥ A.2) observing O.
Proof.
  cofix IH. intros * H H0.
  constructor; intros.
  * destruct (spawnPIDOf a) eqn:P.
    { (* renaming needed *)
      assert (∃fresh, fresh <> ι /\ ¬isUsedPool fresh A.2 /\ ¬appearsEther fresh A.1
          /\ fresh ∉ usedPIDsAct a /\ fresh ∉ O).
      {
        (* freshness *)
        pose proof (infinite_is_fresh (ι :: elements (usedPIDsAct a) ++ elements O ++ elements (allPIDsPool A.2) ++ elements (allPIDsEther A.1))).
        remember (fresh _) as y in H2. clear-H2. exists y.
        repeat apply not_elem_of_app in H2 as [? H2].
        split_and!; try assumption.
        1, 4, 5: set_solver.
        * apply allPIDsPool_isNotUsed_1. set_solver.
        * apply allPIDsEther_does_not_appear_1. set_solver.
      }
      destruct a; inv P. inversion H1. subst. destruct_or!; congruence.
      assert (¬isUsedPool p (ι0 ↦ p0 ∥ Π)) as PNot1. {
        by simpl.
      }
      assert (¬appearsEther p ether) as PNot2. {
        by simpl.
      }
      destruct H2 as [fresh ?]. destruct_hyps. simpl in *.
      subst.
      eapply renamePID_is_preserved_node_semantics with (from := p) (to := fresh) in H1 as HD.
      all: auto.
      rewrite isNotUsed_renamePID_pool in HD.
      rewrite does_not_appear_renamePID_ether in HD.
      all: auto.
      inv HD. 1: destruct_or! H12; simpl in *; congruence.
      put (lookup ι0 : ProcessPool -> _) on H4 as Hh.
      assert (renamePIDPID_sym p fresh ι0 = ι0) as HX. {
        clear -PNot1 H16.
        renamePIDPID_sym_case_match.
        * exfalso. apply PNot1. left. by setoid_rewrite lookup_insert.
        * exfalso. apply H16. left. by setoid_rewrite lookup_insert.
      }
      rewrite HX in Hh.
      setoid_rewrite lookup_insert in Hh. inv Hh.
      do 2 eexists.
      assert (ι ≠ ι0). {
        intro. subst. clear -H0. set_solver.
      }
      split.
      {
        eapply n_trans.
        - setoid_rewrite insert_commute; auto.
          eapply n_spawn. 6: exact H26.
          all: try eassumption.
          all: rewrite HX. 2: by auto.
          replace (renamePIDPID p fresh p) with fresh in * by renamePIDPID_case_match.
          setoid_rewrite insert_commute; auto.
          intro. apply H23. apply isUsedPool_insert_1 in H5.
          destruct_or! H5.
          2: congruence.
          2: set_solver.
          setoid_rewrite delete_notin in H5. 2: {
            apply not_elem_of_dom. setoid_rewrite dom_insert_L.
            put (dom : ProcessPool -> _) on H4 as HDom.
            rewrite HX in HDom. setoid_rewrite dom_insert_L in HDom.
            set_solver.
          }
          rewrite HX. assumption.
        - apply n_refl.
      }
      {
        setoid_rewrite (insert_commute _ _ ι).
        setoid_rewrite (insert_commute _ _ ι).
        2: {
          renamePIDPID_case_match.
        }
        2: { by rewrite HX. }
        eapply barbedBisim_trans.
        * simpl.
          apply (rename_bisim _ _ _ [(p, fresh)]).
          simpl. constructor. 2: constructor.
          split_and!; auto. simpl.
          intro. eapply not_isUsedPool_step in H16.
          3: exact H1. 2: simpl; set_solver.
          congruence.
        * simpl.
          rewrite does_not_appear_renamePID_ether; auto.
          (* at this point, IH could be applied, but first the renaming
             should be simplified *)
          setoid_rewrite <- H12. apply IH. assumption.
          (* NOTE: this use of IH is unguarded, since it is under a renaming!!! *)
          simpl. setoid_rewrite dom_insert_L.
          rewrite <- H4 in H0. simpl in H0. rewrite HX in H0.
          rewrite HX. unfold renamePIDPID. rewrite Nat.eqb_refl.
          set_solver.
      }
    }
    { (* no renaming needed *)
      assert (ι ≠ ι0) as X. {
        intro. subst. inv H1.
        4: inv P.
        all: apply H0; simpl; set_solver.
      }
      exists (A'.1, ι ↦ inr ∅ ∥ A'.2), [(a, ι0)]. split_and!.
      econstructor. 2: constructor.
      * destruct A as [Aeth AΠ], A' as [A'eth A'Π]; simpl in *.
        inv H1.
        - setoid_rewrite insert_commute; auto.
          by constructor.
        - setoid_rewrite insert_commute; auto.
          by constructor.
        - setoid_rewrite insert_commute; auto.
          by constructor.
        - inv P.
     * apply IH; try assumption.
       intro; inv H1.
       all: apply H0; simpl; set_solver.
    }
  * exists source, []. eexists. split. constructor.
    simpl. apply option_biforall_refl. intros. apply Signal_eq_refl.
  * destruct (decide (ι = ι0)).
    { (* dead process communicates *)
      subst. destruct A as [Aeth AΠ]. destruct B' as [Beth BΠ]. simpl in *.
      inv H1.
      2: {
        put (lookup ι0 : ProcessPool -> _) on H3 as HD.
        setoid_rewrite lookup_insert in HD. inv HD. inv H9.
      }
      2: {
        put (lookup ι0 : ProcessPool -> _) on H3 as HD.
        setoid_rewrite lookup_insert in HD. inv HD. inv H7.
        destruct_or!; congruence.
      }
      2: {
        put (lookup ι0 : ProcessPool -> _) on H3 as HD.
        setoid_rewrite lookup_insert in HD. inv HD. inv H13.
      }
      put (lookup ι0 : ProcessPool -> _) on H4 as HD.
      setoid_rewrite lookup_insert in HD. inv HD. inv H6.
      set_solver.
    }
    {
      (* TODO: boiler plate, should be abstracted away *)
      destruct A as [Aeth AΠ]. destruct B' as [Beth BΠ]. simpl in *. inv H1.
      * assert (AΠ = ι0 ↦ p ∥ AΠ). {
          apply map_eq. intros.
          put (lookup i : ProcessPool -> _) on H4 as HD.
          destruct (decide (i = ι0)).
          * subst. setoid_rewrite lookup_insert in HD.
            setoid_rewrite lookup_insert_ne in HD; auto.
            by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
        }
        assert (ι0 ↦ p' ∥ prs = ι ↦ inr ∅ ∥ ι0 ↦ p' ∥ AΠ). {
          apply map_eq. intros.
          put (lookup i : ProcessPool -> _) on H4 as HD.
          destruct (decide (i = ι)). 2: destruct (decide (i = ι0)).
          * subst. setoid_rewrite lookup_insert in HD.
            setoid_rewrite lookup_insert_ne in HD; auto.
            setoid_rewrite lookup_insert.
            setoid_rewrite lookup_insert_ne; auto.
          * subst. setoid_rewrite lookup_insert; auto.
            setoid_rewrite lookup_insert in HD; auto.
            setoid_rewrite lookup_insert_ne in HD; auto.
            setoid_rewrite lookup_insert_ne; auto.
            by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HD; auto.
            setoid_rewrite lookup_insert_ne; auto.
        }
        rewrite H1.
        eexists. exists [(ASend ι0 ι' t, ι0)]. split.
        - econstructor. 2: constructor. by apply n_send.
        - rewrite H2. apply IH; auto. simpl.
          setoid_rewrite dom_insert_L. set_solver.
      * assert (AΠ = ι0 ↦ p ∥ AΠ). {
          apply map_eq. intros.
          put (lookup i : ProcessPool -> _) on H3 as HD.
          destruct (decide (i = ι0)).
          * subst. setoid_rewrite lookup_insert in HD.
            setoid_rewrite lookup_insert_ne in HD; auto.
            by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
        }
        assert (ι0 ↦ p' ∥ prs = ι ↦ inr ∅ ∥ ι0 ↦ p' ∥ AΠ). {
          apply map_eq. intros.
          put (lookup i : ProcessPool -> _) on H3 as HD.
          destruct (decide (i = ι)). 2: destruct (decide (i = ι0)).
          * subst. setoid_rewrite lookup_insert in HD.
            setoid_rewrite lookup_insert_ne in HD; auto.
            setoid_rewrite lookup_insert.
            setoid_rewrite lookup_insert_ne; auto.
          * subst. setoid_rewrite lookup_insert; auto.
            setoid_rewrite lookup_insert in HD; auto.
            setoid_rewrite lookup_insert_ne in HD; auto.
            setoid_rewrite lookup_insert_ne; auto.
            by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HD; auto.
            setoid_rewrite lookup_insert_ne; auto.
        }
        rewrite H1.
        eexists. exists [(AArrive ι2 ι0 t, ι0)]. split.
        - econstructor. 2: constructor. by apply n_arrive.
        - rewrite H2. apply IH; auto. simpl.
          setoid_rewrite dom_insert_L. set_solver.
      * assert (AΠ = ι0 ↦ p ∥ AΠ). {
          apply map_eq. intros.
          put (lookup i : ProcessPool -> _) on H3 as HD.
          destruct (decide (i = ι0)).
          * subst. setoid_rewrite lookup_insert in HD.
            setoid_rewrite lookup_insert_ne in HD; auto.
            by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
        }
        assert (ι0 ↦ p' ∥ Π = ι ↦ inr ∅ ∥ ι0 ↦ p' ∥ AΠ). {
          apply map_eq. intros.
          put (lookup i : ProcessPool -> _) on H3 as HD.
          destruct (decide (i = ι)). 2: destruct (decide (i = ι0)).
          * subst. setoid_rewrite lookup_insert in HD.
            setoid_rewrite lookup_insert_ne in HD; auto.
            setoid_rewrite lookup_insert.
            setoid_rewrite lookup_insert_ne; auto.
          * subst. setoid_rewrite lookup_insert; auto.
            setoid_rewrite lookup_insert in HD; auto.
            setoid_rewrite lookup_insert_ne in HD; auto.
            setoid_rewrite lookup_insert_ne; auto.
            by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HD; auto.
            setoid_rewrite lookup_insert_ne; auto.
        }
        rewrite H1.
        eexists. exists [(a, ι0)]. split.
        - econstructor. 2: constructor. by apply n_other.
        - rewrite H2. apply IH; auto. simpl.
          setoid_rewrite dom_insert_L. set_solver.
      * assert (AΠ = ι0 ↦ p ∥ AΠ). {
          apply map_eq. intros.
          put (lookup i : ProcessPool -> _) on H3 as HD.
          destruct (decide (i = ι0)).
          * subst. setoid_rewrite lookup_insert in HD.
            setoid_rewrite lookup_insert_ne in HD; auto.
            by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
        }
        assert (ι0 ↦ p' ∥ Π = ι ↦ inr ∅ ∥ ι0 ↦ p' ∥ AΠ). {
          apply map_eq. intros.
          put (lookup i : ProcessPool -> _) on H3 as HD.
          destruct (decide (i = ι)). 2: destruct (decide (i = ι0)).
          * subst. setoid_rewrite lookup_insert in HD.
            setoid_rewrite lookup_insert_ne in HD; auto.
            setoid_rewrite lookup_insert.
            setoid_rewrite lookup_insert_ne; auto.
          * subst. setoid_rewrite lookup_insert; auto.
            setoid_rewrite lookup_insert in HD; auto.
            setoid_rewrite lookup_insert_ne in HD; auto.
            setoid_rewrite lookup_insert_ne; auto.
            by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in HD; auto.
            setoid_rewrite lookup_insert_ne; auto.
        }
        rewrite H1.
        eexists. exists [(ASpawn ι' v1 v2 link_flag, ι0)]. split.
        - econstructor. 2: constructor. eapply n_spawn; try eassumption.
          rewrite H3 in H8. rewrite <- H1.
          clear -H8 n H0.
          intro. apply H8.
          assert (ι' <> ι). {
            intro. subst. apply H8. left. by setoid_rewrite lookup_insert.
          }
          destruct H.
          + left. by setoid_rewrite lookup_insert_ne.
          + right. destruct_hyps. exists x, x0. split. 2: assumption.
            setoid_rewrite lookup_insert_ne; auto.
            intro. subst. apply not_elem_of_dom in H0. by setoid_rewrite H0 in H.
        - assert (ι <> ι'). {
            intro. subst.
            apply H8. rewrite H3. left. by setoid_rewrite lookup_insert.
          }
          rewrite H2. setoid_rewrite (insert_commute _ ι' ι); auto.
          apply IH; auto.
          + simpl. do 2 setoid_rewrite dom_insert_L. set_solver.
    }
  * exists source, []. eexists. split. constructor.
    simpl. apply option_biforall_refl. intros. apply Signal_eq_refl.
Qed.
Set Guard Checking.

Definition optional_send (a : Action) (ιs ιd : PID) : list Signal :=
match a with
| ASend from to t => match (decide ((ιs, ιd) = (from, to))) with
                     | left _  => [t]
                     | right _ => []
                     end
| _ => []
end.

Definition optional_send_deleted (a : Action) (ιs ιd : PID) (e : Ether) : Ether :=
match a with
| ASend from to t => match (decide ((ιs, ιd) = (from, to))) with
                     | left _  => <[(ιs,ιd):=[t]]>e
                     | right _ => e
                     end
| _ => e
end.

Lemma ether_update_reduction :
  forall O Aeth AΠ Beth BΠ ιs ιd l a ι links links',
    AΠ !! ιd = Some (inr links) ->
    AΠ !! ιs = Some (inr links') ->
    (Aeth, AΠ) -[a | ι]ₙ-> (Beth, BΠ) with O ->
    (forall ιspawn, Some ιspawn = spawnPIDOf a -> ιspawn ∉ flat_union usedPIDsSignal l) ->
    (<[(ιs, ιd):=l]> Aeth, AΠ) -[ a | ι ]ₙ-> (<[(ιs, ιd):=l ++ optional_send a ιs ιd]>Beth, BΠ) with O /\
    (delete (ιs, ιd) Aeth, AΠ) -[ a | ι ]ₙ-> (optional_send_deleted a ιs ιd (delete (ιs, ιd) Beth), BΠ) with O.
Proof.
  intros * Hdead Hdead2 HD Hspawn. inv HD.
  * assert (<[(ιs, ιd):=l ++ optional_send (ASend ι ι' t) ιs ιd]> (etherAdd ι ι' t Aeth) = etherAdd ι ι' t (<[(ιs, ιd):=l]>Aeth) /\
            optional_send_deleted (ASend ι ι' t) ιs ιd (etherAdd ι ι' t Aeth -- (ιs, ιd)) =
            etherAdd ι ι' t (delete (ιs, ιd) Aeth)). {
    unfold etherAdd. simpl.
    destruct (decide ((ιs, ιd) = (ι, ι'))).
    * inv e. setoid_rewrite lookup_insert. case_match.
      all: setoid_rewrite insert_insert.
      setoid_rewrite <- (insert_insert Aeth (ι, ι') (l ++[t]) (l0 ++ [t])).
      2: setoid_rewrite <- (insert_insert Aeth (ι, ι') (l ++ [t]) ([t])).
      all: setoid_rewrite lookup_delete; setoid_rewrite insert_delete_insert.
      2: setoid_rewrite insert_insert; by split.
      setoid_rewrite insert_insert. by split.
    * setoid_rewrite lookup_insert_ne; auto.
      setoid_rewrite lookup_delete_ne; auto.
      case_match.
      ** setoid_rewrite H.
         setoid_rewrite insert_commute at 1; auto.
         rewrite app_nil_r.
         setoid_rewrite delete_insert_ne; by auto.
      ** setoid_rewrite H. setoid_rewrite insert_commute at 1; auto.
         setoid_rewrite delete_insert_ne; auto.
         by rewrite app_nil_r.
    }
    destruct H as [Hf Hs]. setoid_rewrite Hf. setoid_rewrite Hs.
    split; apply n_send; exact H3.
  * unfold etherPop in H4. repeat case_match; try congruence.
    inv H4.
    assert (ιd <> ι). {
      intro. subst. setoid_rewrite lookup_insert in Hdead. inv Hdead.
      inv H6.
    }
    split.
    - apply n_arrive with (ι0 := ι1).
      unfold etherPop.
      setoid_rewrite lookup_insert_ne. 2: intro X; inv X; lia.
      setoid_rewrite H. simpl. rewrite app_nil_r.
      setoid_rewrite insert_commute at 1. reflexivity.
      intro X; inv X; lia.
      assumption.
    - apply n_arrive with (ι0 := ι1).
      unfold etherPop.
      setoid_rewrite lookup_delete_ne. 2: intro X; inv X; lia.
      setoid_rewrite H. simpl.
      setoid_rewrite delete_insert_ne at 1. reflexivity.
      intro X; inv X; lia.
      assumption.
  * assert (ιd <> ι). {
      intro. subst. setoid_rewrite lookup_insert in Hdead. inv Hdead. inv H4.
      destruct_or! H6; congruence.
    }
    destruct_or! H6; subst; simpl; rewrite app_nil_r.
    all: split; apply n_other; try assumption.
    all: set_solver.
  * assert (ιd <> ι). {
      intro. subst. setoid_rewrite lookup_insert in Hdead. inv Hdead. inv H10.
    }
    (* tricky, spawnPID freshness assumption is probably needed *)
    simpl. rewrite app_nil_r.
    split.
    - eapply n_spawn; try eassumption.
      {
        specialize (Hspawn _ eq_refl).
        intro. apply H8. destruct H0. 2: destruct H0.
        * destruct H0, H0.
          destruct (decide ((x, ι') = (ιs, ιd))).
          - inv e. setoid_rewrite lookup_insert in H0. inv H0.
            exfalso. apply H5. left.
            setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in Hdead; auto.
            by setoid_rewrite Hdead.
          - setoid_rewrite lookup_insert_ne in H0; auto.
            left. by exists x, x0.
        * destruct_hyps.
          destruct (decide ((ι', x) = (ιs, ιd))).
          - inv e.
            exfalso. apply H5. left.
            assert (ιs <> ι). {
              intro. subst. apply H5. left. by setoid_rewrite lookup_insert.
            }
            setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in Hdead2; auto.
            by setoid_rewrite Hdead2.
          - setoid_rewrite lookup_insert_ne in H0; auto.
            right. left. by exists x.
        * destruct_hyps.
          destruct (decide ((x, x0) = (ιs, ιd))).
          - inv e. setoid_rewrite lookup_insert in H0. inv H0.
            exfalso. congruence.
          - setoid_rewrite lookup_insert_ne in H0; auto.
            right. right. do 3 eexists. split; eassumption.
      }
    - eapply n_spawn; try eassumption.
      {
        specialize (Hspawn _ eq_refl).
        intro. apply H8. destruct H0. 2: destruct H0.
        * destruct H0, H0.
          destruct (decide ((x, ι') = (ιs, ιd))).
          - inv e. setoid_rewrite lookup_delete in H0. inv H0.
          - setoid_rewrite lookup_delete_ne in H0; auto.
            left. by exists x, x0.
        * destruct_hyps.
          destruct (decide ((ι', x) = (ιs, ιd))).
          - inv e.
            exfalso. apply H5. left.
            assert (ιs <> ι). {
              intro. subst. apply H5. left. by setoid_rewrite lookup_insert.
            }
            setoid_rewrite lookup_insert_ne; auto.
            setoid_rewrite lookup_insert_ne in Hdead2; auto.
            by setoid_rewrite Hdead2.
          - setoid_rewrite lookup_delete_ne in H0; auto.
            right. left. by exists x.
        * destruct_hyps.
          destruct (decide ((x, x0) = (ιs, ιd))).
          - inv e. setoid_rewrite lookup_delete in H0. inv H0.
          - setoid_rewrite lookup_delete_ne in H0; auto.
            right. right. do 3 eexists. split; eassumption.
      }
Qed.

(* InductiveNodeSemantics *)
Theorem dead_processes_stay_dead :
  forall O (A B : Node) (a : Action) (ι : PID),
    A -[a | ι]ₙ-> B with O ->
    forall (ι' : PID) (d : DeadProcess), A.2 !! ι' = Some (inr d) ->
      B.2 !! ι' = Some (inr (if decide (ι = ι')
                             then match sendPIDOf a with
                                  | Some ιd => delete ιd d
                                  | _ => d
                                  end
                             else d)).
Proof.
  intros. inv H; simpl in *.
  * case_match; clear H.
    - subst. setoid_rewrite lookup_insert.
      setoid_rewrite lookup_insert in H0. inv H0. by inv H1.
    - setoid_rewrite lookup_insert_ne; auto.
      setoid_rewrite lookup_insert_ne in H0; auto.
  * case_match; clear H.
    - subst. setoid_rewrite lookup_insert in H0. inv H0. inv H2.
    - setoid_rewrite lookup_insert_ne; auto.
      setoid_rewrite lookup_insert_ne in H0; auto.
  * case_match; clear H.
    - subst. setoid_rewrite lookup_insert in H0. inv H0.
      destruct_or!; subst; inv H1.
    - setoid_rewrite lookup_insert_ne; auto.
      setoid_rewrite lookup_insert_ne in H0; auto.
  * clear H5. destruct decide.
    - subst. setoid_rewrite lookup_insert in H0. inv H0. inv H6.
    - setoid_rewrite lookup_insert_ne; auto.
      setoid_rewrite lookup_insert_ne; auto.
      setoid_rewrite lookup_insert_ne in H0; auto.
      intro. subst.
      apply H3. left. setoid_rewrite lookup_insert_ne; auto.
      setoid_rewrite lookup_insert_ne in H0; auto.
      by setoid_rewrite H0.
Qed.

(* This could be completely general! *)
Definition general_insert (ιs ιd : PID) (l : option (list Signal)) (e : Ether)  : Ether :=
match l with
| None => e -- (ιs, ιd)
| Some l' => <[(ιs, ιd) := l']>e
end.

Unset Guard Checking.
Theorem ether_update_congruence :
  forall O A ιs ιd l dx dy,
    A.2 !! ιd = Some (inr dx) -> (* this could be relaxed to None or Some (inr x) *)
    ιd ∉ O ->
    A.2 !! ιs = Some (inr dy) -> (* source is a terminated process, otherwise the <- 
                                   direction would not hold for sends *)
    A ~ (general_insert ιs ιd l A.1, A.2) observing O.
Proof with by left; setoid_rewrite lookup_insert.
  cofix IH. destruct A as [Aeth AΠ]. intros * H Hin Hs. constructor; simpl in *.
  2, 4: clear IH.
  * intros. destruct A' as [Beth BΠ].
    destruct (spawnPIDOf a) eqn:HP.
    { (* spawn - use renaming first! *)
      destruct a; inv HP. inversion H0; subst. destruct_or! H8; congruence.
      rename link into link_flag. (* Probably this is a Coq/stdpp bug why link is
                                     shadowed by a previous definition. *)
      assert (exists fresh : PID, fresh ∉ O /\ fresh ≠ ιs /\ fresh ≠ ιd /\ fresh ≠ p /\
                     fresh ∉ flat_union usedPIDsSignal (match l with Some l' => l' | None => [] end) /\
                     ¬appearsEther fresh Beth /\ ¬ isUsedPool fresh (ι ↦ p0 ∥ Π) /\
                     fresh ∉ usedPIDsAct (ASpawn p t1 t2 link_flag) /\
                     ¬ isUsedPool fresh
    (p ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false) ∥ ι ↦ p' ∥ Π)).
      {
        (* freshness *)
        pose proof (infinite_is_fresh (
             ιs :: ιd :: p
          :: elements O
          ++ elements (flat_union usedPIDsSignal (match l with | Some l' => l' | _ => [] end))
          ++ elements (allPIDsEther Beth)
          ++ elements (allPIDsPool (ι ↦ p0 ∥ Π))
          ++ elements (usedPIDsAct (ASpawn p t1 t2 link_flag)) 
          ++ elements (allPIDsPool (p ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false)
                       ∥ ι ↦ p' ∥ Π)))).
        remember (fresh _) as y in H1. clear-H1. exists y.
        repeat apply not_elem_of_cons in H1 as [? H1].
        repeat apply not_elem_of_app in H1 as [? H1].
        split_and!; try assumption.
        1, 2, 5: set_solver.
        * apply allPIDsEther_does_not_appear_1. set_solver.
        * apply allPIDsPool_isNotUsed_1. set_solver.
        * apply allPIDsPool_isNotUsed_1. set_solver.
      }
      destruct H1 as [fresh ?]. destruct_hyps.
      apply renamePID_is_preserved_node_semantics with (from := p) (to := fresh) in H0.
      2-5: assumption.
      rewrite isNotUsed_renamePID_pool in H0; auto.
      rewrite does_not_appear_renamePID_ether in H0; auto.
      assert (renamePIDPID_sym p fresh ι = ι) as R1. {
        clear-H12 H7. renamePIDPID_sym_case_match.
        exfalso. apply H12...
        exfalso. apply H7...
      }
      rewrite R1 in H0.
      do 2 setoid_rewrite pool_insert_renamePID in H0.
      replace (renamePIDPID_sym p fresh p) with fresh in H0 by renamePIDPID_sym_case_match.
      replace (renamePIDPID_sym p fresh ι) with ι in H0 by assumption.
      fold (renamePIDPool p fresh Π) in H0.
      assert (ι ↦ renamePIDProc p fresh p' ∥ Π .[ p ⇔ fresh ]ₚₚ =
              ι ↦ renamePIDProc p fresh p' ∥ Π) as R2. {
        apply map_eq. intros. destruct (decide (i = ι)).
        * subst. by setoid_rewrite lookup_insert.
        * setoid_rewrite lookup_insert_ne; auto.
          destruct (decide (i = fresh)). {
            subst.
            replace fresh with (renamePIDPID_sym p fresh p) at 1 by renamePIDPID_sym_case_match.
            setoid_rewrite lookup_kmap; auto.
            setoid_rewrite lookup_fmap.
            destruct (Π !! fresh) eqn:P. {
              exfalso. apply H7. left. setoid_rewrite lookup_insert_ne; auto.
              by setoid_rewrite P.
            }
            destruct (Π !!p) eqn:P2. {
              exfalso. apply H12. left. setoid_rewrite lookup_insert_ne; auto.
              by setoid_rewrite P2.
              intro. subst. apply H12...
            }
            setoid_rewrite P. by setoid_rewrite P2.
          }
          destruct (decide (i = p)). {
            subst.
            replace p with (renamePIDPID_sym p fresh fresh) at 1 by renamePIDPID_sym_case_match.
            setoid_rewrite lookup_kmap; auto.
            setoid_rewrite lookup_fmap.
            destruct (Π !! fresh) eqn:P. {
              exfalso. apply H7. left. setoid_rewrite lookup_insert_ne; auto.
              by setoid_rewrite P.
              intro. subst. apply H7...
            }
            destruct (Π !! p) eqn:P2. {
              exfalso. apply H12. left. setoid_rewrite lookup_insert_ne; auto.
              by setoid_rewrite P2.
            }
            setoid_rewrite P. by setoid_rewrite P2.
          }
          replace i with (renamePIDPID_sym p fresh i) at 1 by renamePIDPID_sym_case_match.
          setoid_rewrite lookup_kmap; auto.
          setoid_rewrite lookup_fmap.
          destruct (Π !! i) eqn:P; setoid_rewrite P. 2: reflexivity.
          simpl. rewrite isNotUsed_renamePID_proc. reflexivity.
          intro. apply H12. right.
          exists i, p1. split. 2: assumption.
          by setoid_rewrite lookup_insert_ne.
          intro. apply H7. right.
          exists i, p1. split. 2: assumption.
          by setoid_rewrite lookup_insert_ne.
      }

      destruct l. (* TODO This case separation is boiler plate! *)
      {
        opose proof* (ether_update_reduction O _ _ _ _ ιs ιd l _ _ dx dy H Hs H0).
        {
          intros. simpl in H16. inv H16.
          renamePIDPID_case_match; assumption.
        }
        destruct H16 as [H16 _].
        do 2 eexists. split. eapply n_trans. 2: apply n_refl. exact H16.
        eapply barbedBisim_trans.
        apply rename_bisim with (l := [(p, fresh)]).
        * cbn. split_and!; try assumption. trivial.
        * simpl.
          rewrite app_nil_r.
          rewrite does_not_appear_renamePID_ether; auto.
          do 2 setoid_rewrite pool_insert_renamePID.
          replace (renamePIDPID_sym p fresh p) with fresh by renamePIDPID_sym_case_match.
          replace (renamePIDPID_sym p fresh ι) with ι by assumption.
          fold (renamePIDPool p fresh Π).
          rewrite R2. simpl.
          epose proof (IH O (Beth, fresh
 ↦ inl
     ([], renamePIDRed p fresh r, renamePIDMb p fresh emptyBox,
      set_map (renamePIDPID p fresh) (if link_flag then {[ι]} else ∅), false)
 ∥ ι ↦ renamePIDProc p fresh p' ∥ Π) ιs ιd (Some l)). simpl in H17.
          eapply H17.
          - setoid_rewrite lookup_insert_ne; auto.
            destruct (decide (ι = ιd)); subst.
            + setoid_rewrite lookup_insert in H. inv H. inv H15.
            + setoid_rewrite lookup_insert_ne in H; auto.
              setoid_rewrite lookup_insert_ne; auto.
              eassumption.
          - assumption.
          - setoid_rewrite lookup_insert_ne; auto.
            destruct (decide (ι = ιs)); subst.
            + setoid_rewrite lookup_insert in Hs. inv Hs. inv H15.
            + setoid_rewrite lookup_insert_ne in Hs; auto.
              by setoid_rewrite lookup_insert_ne; auto.
      }
      {
        opose proof* (ether_update_reduction O _ _ _ _ ιs ιd [] _ _ dx dy H Hs H0).
        {
          intros. simpl in H16. inv H16.
          renamePIDPID_case_match; assumption.
        }
        destruct H16 as [_ H16].
        do 2 eexists. split. eapply n_trans. 2: apply n_refl. exact H16.
        eapply barbedBisim_trans.
        apply rename_bisim with (l := [(p, fresh)]).
        * cbn. split_and!; try assumption. trivial.
        * simpl.
          rewrite does_not_appear_renamePID_ether; auto.
          do 2 setoid_rewrite pool_insert_renamePID.
          replace (renamePIDPID_sym p fresh p) with fresh by renamePIDPID_sym_case_match.
          replace (renamePIDPID_sym p fresh ι) with ι by assumption.
          fold (renamePIDPool p fresh Π).
          rewrite R2. simpl.
          epose proof (IH O (Beth, fresh
 ↦ inl
     ([], renamePIDRed p fresh r, renamePIDMb p fresh emptyBox,
      set_map (renamePIDPID p fresh) (if link_flag then {[ι]} else ∅), false)
 ∥ ι ↦ renamePIDProc p fresh p' ∥ Π) ιs ιd None). simpl in H17.
          eapply H17.
          - setoid_rewrite lookup_insert_ne; auto.
            destruct (decide (ι = ιd)); subst.
            + setoid_rewrite lookup_insert in H. inv H. inv H15.
            + setoid_rewrite lookup_insert_ne in H; auto.
              setoid_rewrite lookup_insert_ne; auto.
              eassumption.
          - assumption.
          - setoid_rewrite lookup_insert_ne; auto.
            destruct (decide (ι = ιs)); subst.
            + setoid_rewrite lookup_insert in Hs. inv Hs. inv H15.
            + setoid_rewrite lookup_insert_ne in Hs; auto.
              by setoid_rewrite lookup_insert_ne; auto.
      }
    }
    {
      destruct l. (* TODO This case separation is boiler plate! *)
      {
        opose proof* (ether_update_reduction O Aeth AΠ Beth BΠ ιs ιd l a ι dx dy H Hs H0).
        {
          intros. congruence.
        }
        destruct H1 as [H1 _].
        do 2 eexists. split. eapply n_trans. 2: apply n_refl. exact H1.
        epose proof (IH O (Beth, BΠ) ιs ιd (Some (l ++ optional_send a ιs ιd))).
        simpl in H2. eapply H2.
        * eapply dead_processes_stay_dead in H0. 2: exact H.
          eassumption.
        * assumption.
        * eapply dead_processes_stay_dead in H0. 2: exact Hs.
          eassumption.
      }
      {
        opose proof* (ether_update_reduction O Aeth AΠ Beth BΠ ιs ιd [] a ι dx dy H Hs H0).
        {
          intros. congruence.
        }
        destruct H1 as [H1_0 H1].
        do 2 eexists. split. eapply n_trans. 2: apply n_refl. exact H1.
        epose proof (IH O (Beth, BΠ) ιs ιd None).
        unfold optional_send_deleted. destruct a. case_match.
        setoid_rewrite insert_delete_insert. clear H3. inv e.
        all: simpl in H2; try eapply H2; try assumption.
        2,4,6,8,10,12: eapply dead_processes_stay_dead in H0; try exact H; try eassumption.
        2-7: eapply dead_processes_stay_dead in H0; try exact Hs; try eassumption.
        epose proof (IH O (Beth, BΠ) _ _ (Some [t])). simpl in H3. eapply H3.
        * eapply dead_processes_stay_dead in H0; try exact H; try eassumption.
        * eassumption.
        * eapply dead_processes_stay_dead in H0; try exact Hs; try eassumption.
      }
    }
  * intros.
    exists source, []. eexists. split. apply n_refl.
    simpl. assert (ιd <> dest) by set_solver.
    destruct l.
    - setoid_rewrite lookup_insert_ne. 2: intro X; inv X; lia.
      apply option_biforall_refl. intros. apply Signal_eq_refl.
    - simpl. setoid_rewrite lookup_delete_ne. 2: intro X; inv X; lia.
      apply option_biforall_refl. intros. apply Signal_eq_refl.
  * intros.
    exists source, []. eexists. split. apply n_refl.
    simpl. assert (ιd <> dest) by set_solver.
    destruct l.
    - setoid_rewrite lookup_insert_ne. 2: intro X; inv X; lia.
      apply option_biforall_refl. intros. apply Signal_eq_refl.
    - simpl. setoid_rewrite lookup_delete_ne. 2: intro X; inv X; lia.
      apply option_biforall_refl. intros. apply Signal_eq_refl.
   (* Hs is only needed in this proof *)


  (** In the last case, we use a trick: double ether update, where the second
      update will cancel the first to obtain the original ether. Next, we proceed
      with basically the same proof as in the 1st case *)
  * intros.
    intros. destruct B' as [Beth BΠ].
    destruct (spawnPIDOf a) eqn:HP.
    { (* spawn - use renaming first! *)
      destruct a; inv HP. inversion H0; subst. destruct_or! H8; congruence.
      rename link into link_flag. (* Probably this is a Coq/stdpp bug why link is
                                     shadowed by a previous definition. *)
      assert (exists fresh : PID, fresh ∉ O /\ fresh ≠ ιs /\ fresh ≠ ιd /\ fresh ≠ p /\
                     fresh ∉ flat_union usedPIDsSignal (match l with Some l' => l' | None => [] end) /\
                     ¬appearsEther fresh (general_insert ιs ιd l Aeth) /\
                     ¬appearsEther fresh Aeth /\ (* extra condition *)
                     ¬ isUsedPool fresh (ι ↦ p0 ∥ Π) /\
                     fresh ∉ usedPIDsAct (ASpawn p t1 t2 link_flag) /\
                     ¬ isUsedPool fresh
    (p ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false) ∥ ι ↦ p' ∥ Π)).
      {
        (* freshness *)
        pose proof (infinite_is_fresh (
             ιs :: ιd :: p
          :: elements O
          ++ elements (flat_union usedPIDsSignal (match l with | Some l' => l' | _ => [] end))
          ++ elements (allPIDsEther (general_insert ιs ιd l Aeth))
          ++ elements (allPIDsEther Aeth)
          ++ elements (allPIDsPool (ι ↦ p0 ∥ Π))
          ++ elements (usedPIDsAct (ASpawn p t1 t2 link_flag)) 
          ++ elements (allPIDsPool (p ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false)
                       ∥ ι ↦ p' ∥ Π)))).
        remember (fresh _) as y in H1. clear-H1. exists y.
        repeat apply not_elem_of_cons in H1 as [? H1].
        repeat apply not_elem_of_app in H1 as [? H1].
        split_and!; try assumption.
        1, 2, 6: set_solver.
        * apply allPIDsEther_does_not_appear_1. set_solver.
        * apply allPIDsEther_does_not_appear_1. set_solver.
        * apply allPIDsPool_isNotUsed_1. set_solver.
        * apply allPIDsPool_isNotUsed_1. set_solver.
      }
      destruct H1 as [fresh ?]. destruct_hyps.
      apply renamePID_is_preserved_node_semantics with (from := p) (to := fresh) in H0.
      2-5: assumption.
      rewrite isNotUsed_renamePID_pool in H0; auto.
      rewrite does_not_appear_renamePID_ether in H0; auto.
      assert (renamePIDPID_sym p fresh ι = ι) as R1. {
        clear-H12 H8. renamePIDPID_sym_case_match.
        exfalso. apply H12...
        exfalso. apply H8...
      }
      rewrite R1 in H0.
      do 2 setoid_rewrite pool_insert_renamePID in H0.
      replace (renamePIDPID_sym p fresh p) with fresh in H0 by renamePIDPID_sym_case_match.
      replace (renamePIDPID_sym p fresh ι) with ι in H0 by assumption.
      fold (renamePIDPool p fresh Π) in H0.
      assert (ι ↦ renamePIDProc p fresh p' ∥ Π .[ p ⇔ fresh ]ₚₚ =
              ι ↦ renamePIDProc p fresh p' ∥ Π) as R2. {
        apply map_eq. intros. destruct (decide (i = ι)).
        * subst. by setoid_rewrite lookup_insert.
        * setoid_rewrite lookup_insert_ne; auto.
          destruct (decide (i = fresh)). {
            subst.
            replace fresh with (renamePIDPID_sym p fresh p) at 1 by renamePIDPID_sym_case_match.
            setoid_rewrite lookup_kmap; auto.
            setoid_rewrite lookup_fmap.
            destruct (Π !! fresh) eqn:P. {
              exfalso. apply H8. left. setoid_rewrite lookup_insert_ne; auto.
              by setoid_rewrite P.
            }
            destruct (Π !!p) eqn:P2. {
              exfalso. apply H12. left. setoid_rewrite lookup_insert_ne; auto.
              by setoid_rewrite P2.
              intro. subst. apply H12...
            }
            setoid_rewrite P. by setoid_rewrite P2.
          }
          destruct (decide (i = p)). {
            subst.
            replace p with (renamePIDPID_sym p fresh fresh) at 1 by renamePIDPID_sym_case_match.
            setoid_rewrite lookup_kmap; auto.
            setoid_rewrite lookup_fmap.
            destruct (Π !! fresh) eqn:P. {
              exfalso. apply H8. left. setoid_rewrite lookup_insert_ne; auto.
              by setoid_rewrite P.
              intro. subst. apply H8...
            }
            destruct (Π !! p) eqn:P2. {
              exfalso. apply H12. left. setoid_rewrite lookup_insert_ne; auto.
              by setoid_rewrite P2.
            }
            setoid_rewrite P. by setoid_rewrite P2.
          }
          replace i with (renamePIDPID_sym p fresh i) at 1 by renamePIDPID_sym_case_match.
          setoid_rewrite lookup_kmap; auto.
          setoid_rewrite lookup_fmap.
          destruct (Π !! i) eqn:P; setoid_rewrite P. 2: reflexivity.
          simpl. rewrite isNotUsed_renamePID_proc. reflexivity.
          intro. apply H12. right.
          exists i, p1. split. 2: assumption.
          by setoid_rewrite lookup_insert_ne.
          intro. apply H8. right.
          exists i, p1. split. 2: assumption.
          by setoid_rewrite lookup_insert_ne.
      }
      rewrite R2 in H0.
      destruct (Aeth !! (ιs, ιd)) eqn:Heth.
      {
        assert (Aeth = <[(ιs, ιd):=l1]>(general_insert ιs ιd l Aeth)). {
          destruct l; simpl.
          setoid_rewrite insert_insert. by setoid_rewrite insert_id.
          setoid_rewrite insert_delete_insert. by setoid_rewrite insert_id.
        }
        rewrite H17. (* at 1 <- but this does not work for some reason *)
        opose proof* (ether_update_reduction O _ _ _ _ ιs ιd l1 _ _ dx dy H Hs H0).
        {
          intros. simpl in H18. inv H18.
          clear -H7 Heth. renamePIDPID_case_match.
          intro. apply H7. do 2 right. do 3 eexists; split; eassumption.
        }
        destruct H18 as [H18 _].
        simpl in H18.
        replace (renamePIDPID p fresh p) with fresh in H18 by renamePIDPID_case_match.
        rewrite app_nil_r in H18.
        do 2 eexists. split.
        {
          eapply n_trans. 2: apply n_refl. exact H18.
        }
        rewrite <-H17.
        (* here in bisim. trans. renaming and IH are swapped *)
        eapply barbedBisim_trans.
        * eapply IH with (dx := dx) (ιs := ιs) (ιd := ιd); try assumption.
          - simpl. setoid_rewrite lookup_insert_ne; auto.
            destruct (decide (ιd = ι)).
            + subst. exfalso.
              setoid_rewrite lookup_insert in H. inv H.
              inv H15.
            + setoid_rewrite lookup_insert_ne; auto.
              by setoid_rewrite lookup_insert_ne in H; auto.
          - simpl. setoid_rewrite lookup_insert_ne; auto.
            destruct (decide (ιs = ι)).
            + subst. exfalso.
              setoid_rewrite lookup_insert in Hs. inv Hs.
              inv H15.
            + setoid_rewrite lookup_insert_ne; auto.
              by setoid_rewrite lookup_insert_ne in Hs; auto.
        * Unshelve. 2: exact l.
          cbn. clear H18.
          apply barbedBisim_sym.
          eapply barbedBisim_trans.
          1: apply rename_bisim with (l := [(p, fresh)]); cbn.
          1: set_solver.
          (* This should be just reflexivity *)
          simpl.
          rewrite does_not_appear_renamePID_ether; auto.
          do 2 setoid_rewrite pool_insert_renamePID.
          replace (renamePIDPID_sym p fresh p) with fresh by renamePIDPID_sym_case_match.
          replace (renamePIDPID_sym p fresh ι) with ι by assumption.
          fold (renamePIDPool p fresh Π).
          rewrite R2. simpl.
          apply barbedBisim_refl.
      }
      {
        assert (Aeth = (general_insert ιs ιd l Aeth) -- (ιs, ιd)). {
          destruct l; simpl.
          setoid_rewrite delete_insert_delete. by setoid_rewrite delete_notin.
          setoid_rewrite delete_idemp. by setoid_rewrite delete_notin.
        }
        rewrite H17. (* at 1 <- but this does not work for some reason *)
        opose proof* (ether_update_reduction O _ _ _ _ ιs ιd [] _ _ dx dy H Hs H0).
        {
          intros. clear. set_solver.
        }
        destruct H18 as [_ H18].
        simpl in H18.
        replace (renamePIDPID p fresh p) with fresh in H18 by renamePIDPID_case_match.
        do 2 eexists. split.
        {
          eapply n_trans. 2: apply n_refl. exact H18.
        }
        rewrite <-H17.
        (* here in bisim. trans. renaming and IH are swapped *)
        eapply barbedBisim_trans.
        * eapply IH with (dx := dx) (ιs := ιs) (ιd := ιd); try assumption.
          - simpl. setoid_rewrite lookup_insert_ne; auto.
            destruct (decide (ιd = ι)).
            + subst. exfalso.
              setoid_rewrite lookup_insert in H. inv H.
              inv H15.
            + setoid_rewrite lookup_insert_ne; auto.
              by setoid_rewrite lookup_insert_ne in H; auto.
          - simpl. setoid_rewrite lookup_insert_ne; auto.
            destruct (decide (ιs = ι)).
            + subst. exfalso.
              setoid_rewrite lookup_insert in Hs. inv Hs.
              inv H15.
            + setoid_rewrite lookup_insert_ne; auto.
              by setoid_rewrite lookup_insert_ne in Hs; auto.
        * Unshelve. 2: exact l.
          cbn. clear H18.
          apply barbedBisim_sym.
          eapply barbedBisim_trans.
          1: apply rename_bisim with (l := [(p, fresh)]); cbn.
          1: set_solver.
          (* This should be just reflexivity *)
          simpl.
          rewrite does_not_appear_renamePID_ether; auto.
          do 2 setoid_rewrite pool_insert_renamePID.
          replace (renamePIDPID_sym p fresh p) with fresh by renamePIDPID_sym_case_match.
          replace (renamePIDPID_sym p fresh ι) with ι by assumption.
          fold (renamePIDPool p fresh Π).
          rewrite R2. simpl.
          apply barbedBisim_refl.
      }
    }
    {
      destruct (Aeth !! (ιs, ιd)) eqn:Heth.
      {
        assert (Aeth = (<[(ιs, ιd):=l0]>(general_insert ιs ιd l Aeth) : Ether)). {
          destruct l.
          - setoid_rewrite insert_insert.
            apply map_eq. intros. destruct (decide (i = (ιs, ιd))).
            * subst. by setoid_rewrite lookup_insert.
            * by setoid_rewrite lookup_insert_ne.
          - setoid_rewrite insert_delete_insert.
            apply map_eq. intros. destruct (decide (i = (ιs, ιd))).
            * subst. by setoid_rewrite lookup_insert.
            * by setoid_rewrite lookup_insert_ne.
        }
        opose proof* (ether_update_reduction O _ _ _ _ ιs ιd l0 _ _ dx dy H Hs H0).
        {
          intros. congruence.
        }
        destruct H2 as [H2 _].
        rewrite H1. do 2 eexists. split. eapply n_trans. 2: apply n_refl. exact H2.
        apply barbedBisim_sym.
        epose proof (IH O (Beth, BΠ) _ _ (Some (l0 ++ optional_send a ιs ιd))). simpl in H3. eapply H3.
        * eapply dead_processes_stay_dead in H0. 2: exact H.
          eassumption.
        * assumption.
        * eapply dead_processes_stay_dead in H0. 2: exact Hs.
          eassumption.
      }
      {
        assert (Aeth = delete (ιs, ιd) (general_insert ιs ιd l Aeth)). {
          destruct l; simpl.
          by setoid_rewrite delete_insert.
          setoid_rewrite delete_idemp. by setoid_rewrite delete_notin.
        }
        opose proof* (ether_update_reduction O _ _ _ _ ιs ιd [] _ _ dx dy H Hs H0).
        {
          intros. congruence.
        }
        destruct H2 as [_ H2].
        rewrite H1. do 2 eexists. split. eapply n_trans. 2: apply n_refl. exact H2.
        apply barbedBisim_sym.
        assert (optional_send_deleted a ιs ιd (Beth -- (ιs, ιd)) = Beth -- (ιs, ιd) \/
                (exists t, a = ASend ιs ιd t /\
                optional_send_deleted a ιs ιd (Beth -- (ιs, ιd)) = (<[(ιs, ιd):=[t]]>Beth : Ether))).
        {
          unfold optional_send_deleted. repeat case_match.
          all: try by left.
          right. eexists. split. clear H4. inv e. reflexivity.
          by setoid_rewrite insert_delete_insert.
        }
        destruct H3.
        - rewrite H3. epose proof (IH O (Beth, BΠ) _ _ None). simpl in H4.
          eapply H4.
          * eapply dead_processes_stay_dead in H0. 2: exact H.
            eassumption.
          * assumption.
          * eapply dead_processes_stay_dead in H0. 2: exact Hs.
            eassumption.
        - destruct_hyps. rewrite H4.
          epose proof (IH O (Beth, BΠ) _ _ (Some [x])). simpl in H5.
          eapply H5.
          * eapply dead_processes_stay_dead in H0. 2: exact H.
            eassumption.
          * assumption.
          * eapply dead_processes_stay_dead in H0. 2: exact Hs.
            eassumption.
      }
    }
Qed.
Set Guard Checking.

(*
  This definition expresses that there are no exits sent with the
  same source and destination with 'normal' reason.
 *)
Definition no_self_exits_via_link (e : Ether) :=
  forall ι l, e !! (ι, ι) = Some l ->
    Forall (fun s => forall b, s <> SExit normal b) l.

Theorem normalisation_2 :
  forall O A B ι a,
  (* Sends should not be included in chainability!
     A send can happen before termination that potentially causes difference
     in the two systems (in the other one, this send never happened). *)
    ether_wf A.1 -> (* message sending requires VALCLOSED - needed for dead processes *)
    no_self_exits_via_link A.1 ->
    isChainable2 a ->
    dom A.2 ## O ->
    A -[a |ι]ₙ-> B with O ->
    A ~ B observing O.
Proof.
  cofix IH.
  intros * Heth Heth2 ? Hdom ?. constructor.
  * intros.
    destruct (decide (ι = ι0)).
    { (* same process *)
      subst. destruct (decide (a0 = a)).
      { (* determinism *)
        subst. eapply concurrent_determinism in H0. 2: exact H1.
        subst. exists B, []. split_and!; try assumption.
        constructor.
        apply barbedBisim_refl.
      }
      {
        destruct a0.
        (* send *)
        * inv H0; subst.
          - simpl in H. inv H. (* 
             inv H1. 2: { clear-H8. destruct_or!; congruence. }
            put (lookup ι0 : ProcessPool -> _) on H4 as HD.
            setoid_rewrite lookup_insert in HD. inv HD.
            inv H2; inv H9; try (exfalso; apply n; reflexivity).
            (* dead process communication is problematic *)
            assert (ι' <> receiver). {
              intro; subst. setoid_rewrite H8 in H10. inv H10. by apply n.
            }
            do 2 eexists. split.
            eapply n_trans. 2: apply n_refl. apply n_send.
            apply p_dead.
            + exact H6.
            + setoid_rewrite lookup_delete_ne. exact H10. assumption.
            + simpl in H.
             (* TODO: this should be doable by checking whether
                      the exit is in l -> then either no steps are made from
                      B or, the exit is chained after reaching B.
                      Since the targets are different, the etherAdd
                      order can be swapped *) *)
          - inv H.
          - inv H1. 2: { clear-H9. destruct_or!; congruence. }
            exfalso.
            put (lookup ι0 : ProcessPool -> _) on H5 as HD.
            setoid_rewrite lookup_insert in HD. inv HD.
            destruct_or! H3; subst; inv H10; inv H2.
            + inv H9. by cbn in *.
            + inv H9. by cbn in *.
            + inv H8. by cbn in *.
            + inv H8. by cbn in *.
          - inv H1. 2: { clear-H13. destruct_or!; congruence. }
            exfalso.
            put (lookup ι0 : ProcessPool -> _) on H9 as HD.
            setoid_rewrite lookup_insert in HD. inv HD.
            subst; inv H7; inv H14.
        (* arrive *)
        * apply not_eq_sym in n.
          assert (receiver = ι0). {
            inv H1; auto. destruct_or!; congruence.
          }
          subst.
          eapply (chain_arrive_later_2 _ _ _ _ _ _ _ _ H0 H) in H1 as HD2.
          destruct HD2 as [D [HD1 [P | P]]].
          (* arrive killed some process *)
          - (* This case is problematic *)
            subst.
            destruct a; try inv H.
            + (* a = self *)
              exists A'. destruct A'. simpl in HD1. eexists. split.
              eapply n_trans. exact HD1. constructor.
              apply barbedBisim_refl.
            + (* a = spawn *)
              destruct A'. simpl in HD1.
              inv H0. 1: by destruct_or! H3; congruence.
              rewrite H6 in HD1. simpl in H13. rewrite H13 in HD1.
              clear H13. simpl in H; destruct @link eqn:P. 2: inv H.
              repeat case_match.
              (* live process - no update *)
              ** exists (e, p). eexists. split.
                 eapply n_trans. exact HD1. constructor.
                 apply barbedBisim_refl.
              (* message - no update *)
              ** exists (e, p). eexists. split.
                 eapply n_trans. exact HD1. constructor.
                 apply barbedBisim_refl.
              (* linked exit - update *)
              ** assert (ι <> ι0) as HX. {
                   intro. subst. apply H9.
                   left. by setoid_rewrite lookup_insert.
                 }
                 (* How the arrive happened (it terminated a process): *)
                 pose proof HD1 as HD1copy.
                 inv HD1. 2: { destruct_or! H17; congruence. }
                 put (lookup ι0 : ProcessPool -> _) on H8 as HX2.
                 setoid_rewrite lookup_insert in HX2.
                 setoid_rewrite lookup_insert_ne in HX2; auto.
                 setoid_rewrite lookup_insert in HX2. inv HX2.
                 put (lookup ι0 : ProcessPool -> _) on H18 as HX3.
                 setoid_rewrite lookup_insert in HX3.
                 setoid_rewrite lookup_insert_ne in HX3; auto.
                 setoid_rewrite lookup_insert in HX3. inv HX3.
                 inv H19.
                 (***)
                 assert (VALCLOSED r0) as Hcl.
                 { (* ether_wf is used here *)
                   clear -H16 Heth.
                   simpl in Heth. unfold etherPop in H16.
                   repeat case_match; try congruence. subst.
                   apply Heth in H. inv H. inv H16. apply H2.
                 }
                 subst. do 2 eexists. split.
                 {
                   eapply n_trans. rewrite H8. exact HD1copy.
                   eapply n_trans. setoid_rewrite insert_commute; auto.
                   apply n_send. apply p_dead. by exact Hcl.
                   by setoid_rewrite lookup_insert.
                   eapply n_trans.
                   {
                     setoid_rewrite insert_commute; auto.
                     (* asserting emptyness of the signal list for the new process *)
                     assert (etherPop ι0 ι (etherAdd ι0 ι (SExit r0 true) e) = Some ((SExit r0 true), <[(ι0,ι):=[]]>e)). {
                       clear-H16 H12 HX. (* etherPop + appears + ι ≠ ι0 *)
                       unfold etherPop in H16. repeat case_match; try congruence.
                       inv H16.
                       unfold etherAdd. case_match.
                       * exfalso. apply H12.
                         left. exists ι0, l.
                         setoid_rewrite lookup_insert_ne in H0. 2: intro X; inv X; lia.
                         assumption.
                       * unfold etherPop. setoid_rewrite lookup_insert. do 2 f_equal.
                         by setoid_rewrite insert_insert.
                     }
                     apply n_arrive. eassumption.
                     apply p_exit_terminate. instantiate (1 := reason').
                     destruct_or! H4. 1-2: clear -H4; set_solver.
                     destruct_hyps; subst. exfalso.
                     {
                       (* This action should not happen ever, that a process
                        sends an exit signal to itself via a link!!! *)
                       unfold etherPop, etherAdd in H2.
                       destruct (e !! (ι0, ι)) eqn:P; setoid_rewrite lookup_insert in H2.
                       * apply H12. destruct l0; inv H2.
                         - clear -H16 P HX.
                           unfold etherPop in H16. repeat case_match; try congruence.
                           inv H16. setoid_rewrite lookup_insert_ne in P.
                           2: intro X; inv X; lia.
                           left. by exists ι0, [].
                         - clear -H16 P HX.
                           unfold etherPop in H16. repeat case_match; try congruence.
                           inv H16. setoid_rewrite lookup_insert_ne in P.
                           2: intro X; inv X; lia.
                           left. exists ι0. by eexists.
                       * (* admit. *) (* This action should not happen ever, that a process
                        sends an exit signal to itself via a link!!! See H1! *)
                          clear-Heth2 H16. unfold etherPop in H16.
                          repeat case_match; try congruence. inv H16.
                          simpl in Heth2. apply Heth2 in H. inv H.
                          by apply (H2 true).
                     }
                   }
                   eapply n_trans. 2: apply n_refl. apply n_send.
                   apply p_dead. 2: {
                     apply lookup_gset_to_gmap_Some. split.
                     apply elem_of_singleton. reflexivity.
                     reflexivity.
                   }
                   set_solver.
                 }
                 {
                   assert (<[ι0:=inr (<[ι:=r0]> d -- ι)]> p = p). {
                     apply map_eq. intros. destruct (decide (i = ι0)).
                     * subst. setoid_rewrite lookup_insert.
                       setoid_rewrite H0. f_equal.
                       setoid_rewrite delete_insert. reflexivity.
                       apply eq_None_ne_Some_2. intros ? ?.
                       eapply not_isUsedPool_step in H1; eauto.
                       2: {
                         intro. apply H12. clear-H16 H3.
                         unfold etherPop in H16; repeat case_match; try congruence.
                         inv H16. simpl in *.
                         destruct (decide (ι = sender)). 2: destruct (decide (ι = ι0)).
                         - subst. right. left. exists ι0. congruence.
                         - subst. left. exists sender. eexists. eassumption.
                         - do 2 right. exists sender, ι0. eexists. split. exact H.
                           set_solver.
                       }
                       apply H1. right. exists ι0, (inr d). split. assumption.
                       simpl. apply elem_of_union_list. exists ({[ι]} ∪ usedPIDsVal x).
                       split. 2: clear; set_solver.
                       apply elem_of_elements, elem_of_map_to_set.
                       do 2 eexists. split. 2: reflexivity. assumption.
                     * by setoid_rewrite lookup_insert_ne.
                   }
                   setoid_rewrite H2.
                   assert (gset_to_gmap reason' {[ι0]} -- ι0 = ∅). {
                     clear. setoid_rewrite <- gset_to_gmap_difference_singleton.
                     setoid_rewrite difference_diag_L.
                     by apply gset_to_gmap_empty.
                   }
                   setoid_rewrite H3. (* this is slow for some reason *)
                   (* two restricted lemmas needed here:
                     - None-s in the ether can be replaced by empty lists
                     - dead processes can be added which only communicate
                       with other dead processes
                           *)
                   eapply barbedBisim_trans.
                   apply dead_process_congruence with (ι := ι). assumption.
                   {
                     eapply not_isUsedPool_step in H1.
                     2: eassumption.
                     2: {
                       simpl. intro. apply H12. clear -H5 H16 HX.
                       unfold etherPop in H16. repeat case_match; try congruence.
                       inv H16.
                       destruct (decide (ι = sender)).
                       * subst. right. left. exists ι0. congruence.
                       * right. right. do 3 eexists. split. eassumption. set_solver.
                     }
                     simpl. setoid_rewrite <- H2 in H1.
                     apply not_isUsedPool_insert_1 in H1.
                     by apply H1.
                   }
                   simpl.
                   assert (exists l, 
                      etherAdd ι ι0 (SExit reason' true) (<[(ι0, ι):=[]]> e) =
                       <[(ι, ι0):=l]> (<[(ι0, ι):=[]]> e)). {
                     unfold etherAdd. setoid_rewrite lookup_insert_ne. 2: congruence.
                     case_match; eexists; reflexivity.
                   }
                   destruct H5 as [xl Hxl]. setoid_rewrite Hxl.

                   (* TODO: progress is here, thm needs to be generalised *)
                   eapply barbedBisim_trans.
                   eapply ether_update_congruence with (ιd := ι0) (ιs := ι) (l := Some xl).
                   {
                     simpl. setoid_rewrite lookup_insert_ne; auto.
                     eassumption.
                   }
                   {
                     (* O ## dom Π *)
                     intro. clear -H5 Hdom. simpl in Hdom. set_solver.
                   }
                   {
                     simpl. by setoid_rewrite lookup_insert.
                   }
                   simpl.
                   setoid_rewrite insert_commute. 2: intro X; inv X; lia.
                   eapply ether_update_congruence with (l := Some []).
                   - by setoid_rewrite lookup_insert.
                   - assumption.
                   - simpl. setoid_rewrite lookup_insert_ne; auto.
                     rewrite <-H2. setoid_rewrite lookup_insert. reflexivity.
                 }
              (* kill exit - update *)
              ** assert (ι <> ι0) as HX. {
                   intro. subst. apply H9.
                   left. by setoid_rewrite lookup_insert.
                 }
                 (* How the arrive happened (it terminated a process): *)
                 pose proof HD1 as HD1copy.
                 inv HD1. 2: { destruct_or! H18; congruence. }
                 put (lookup ι0 : ProcessPool -> _) on H10 as HX2.
                 setoid_rewrite lookup_insert in HX2.
                 setoid_rewrite lookup_insert_ne in HX2; auto.
                 setoid_rewrite lookup_insert in HX2. inv HX2.
                 put (lookup ι0 : ProcessPool -> _) on H19 as HX3.
                 setoid_rewrite lookup_insert in HX3.
                 setoid_rewrite lookup_insert_ne in HX3; auto.
                 setoid_rewrite lookup_insert in HX3. inv HX3.
                 inv H20.
                 (***)
                 subst. do 2 eexists. split.
                 {
                   eapply n_trans. rewrite H10. exact HD1copy.
                   eapply n_trans. setoid_rewrite insert_commute; auto.
                   apply n_send. apply p_dead.
                   2: { by setoid_rewrite lookup_insert. }
                   1: by constructor.
                   eapply n_trans.
                   {
                     setoid_rewrite insert_commute; auto.
                     (* asserting emptyness of the signal list for the new process *)
                     assert (etherPop ι0 ι (etherAdd ι0 ι (SExit (VLit "killed"%string) true) e) = Some ((SExit (VLit "killed"%string) true), <[(ι0,ι):=[]]>e)). {
                       clear-H17 H12 HX. (* etherPop + appears + ι ≠ ι0 *)
                       unfold etherPop in H17. repeat case_match; try congruence.
                       inv H17.
                       unfold etherAdd. case_match.
                       * exfalso. apply H12.
                         left. exists ι0, l.
                         setoid_rewrite lookup_insert_ne in H0. 2: intro X; inv X; lia.
                         assumption.
                       * unfold etherPop. setoid_rewrite lookup_insert. do 2 f_equal.
                         by setoid_rewrite insert_insert.
                     }
                     apply n_arrive. eassumption.
                     apply p_exit_terminate. instantiate (1 := reason').
                     destruct_or! H4. 1-2: clear -H4; set_solver.
                     destruct_hyps; subst. congruence.
                   }
                   eapply n_trans. 2: apply n_refl. apply n_send.
                   apply p_dead. 2: {
                     apply lookup_gset_to_gmap_Some. split.
                     apply elem_of_singleton. reflexivity.
                     reflexivity.
                   }
                   set_solver.
                 }
                 {
                   assert (<[ι0:=inr (<[ι:=VLit "killed"%string]> d -- ι)]> p = p). {
                     apply map_eq. intros. destruct (decide (i = ι0)).
                     * subst. setoid_rewrite lookup_insert.
                       setoid_rewrite H0. f_equal.
                       setoid_rewrite delete_insert. reflexivity.
                       apply eq_None_ne_Some_2. intros ? ?.
                       eapply not_isUsedPool_step in H1; eauto.
                       2: {
                         intro. apply H12. clear-H17 H3.
                         unfold etherPop in H17; repeat case_match; try congruence.
                         inv H17. simpl in *.
                         destruct (decide (ι = sender)). 2: destruct (decide (ι = ι0)).
                         - subst. right. left. exists ι0. congruence.
                         - subst. left. exists sender. eexists. eassumption.
                         - do 2 right. exists sender, ι0. eexists. split. exact H.
                           set_solver.
                       }
                       apply H1. right. exists ι0, (inr d). split. assumption.
                       simpl. apply elem_of_union_list. exists ({[ι]} ∪ usedPIDsVal x).
                       split. 2: clear; set_solver.
                       apply elem_of_elements, elem_of_map_to_set.
                       do 2 eexists. split. 2: reflexivity. assumption.
                     * by setoid_rewrite lookup_insert_ne.
                   }
                   setoid_rewrite H2.
                   assert (gset_to_gmap reason' {[ι0]} -- ι0 = ∅). {
                     clear. setoid_rewrite <- gset_to_gmap_difference_singleton.
                     setoid_rewrite difference_diag_L.
                     by apply gset_to_gmap_empty.
                   }
                   setoid_rewrite H3. (* this is slow for some reason *)
                   (* two restricted lemmas needed here:
                     - None-s in the ether can be replaced by empty lists
                     - dead processes can be added which only communicate
                       with other dead processes
                           *)
                   eapply barbedBisim_trans.
                   apply dead_process_congruence with (ι := ι). assumption.
                   {
                     eapply not_isUsedPool_step in H1.
                     2: eassumption.
                     2: {
                       simpl. intro. apply H12. clear -H17 HX H8.
                       unfold etherPop in H17. repeat case_match; try congruence.
                       inv H17.
                       destruct (decide (ι = sender)).
                       * subst. right. left. exists ι0. congruence.
                       * right. right. do 3 eexists. split. eassumption. set_solver.
                     }
                     simpl. setoid_rewrite <- H2 in H1.
                     apply not_isUsedPool_insert_1 in H1.
                     by apply H1.
                   }
                   simpl.
                   assert (exists l, 
                      etherAdd ι ι0 (SExit reason' true) (<[(ι0, ι):=[]]> e) =
                       <[(ι, ι0):=l]> (<[(ι0, ι):=[]]> e)). {
                     unfold etherAdd. setoid_rewrite lookup_insert_ne. 2: congruence.
                     case_match; eexists; reflexivity.
                   }
                   destruct H8 as [xl Hxl]. setoid_rewrite Hxl.

                   (* TODO: progress is here, thm needs to be generalised *)
                   eapply barbedBisim_trans.
                   eapply ether_update_congruence with (ιd := ι0) (ιs := ι) (l := Some xl).
                   {
                     simpl. setoid_rewrite lookup_insert_ne; auto.
                     eassumption.
                   }
                   {
                     (* O ## dom Π *)
                     intro. clear -H8 Hdom. simpl in Hdom. set_solver.
                   }
                   {
                     simpl. by setoid_rewrite lookup_insert.
                   }
                   simpl.
                   setoid_rewrite insert_commute. 2: intro X; inv X; lia.
                   eapply ether_update_congruence with (l := Some []).
                   - by setoid_rewrite lookup_insert.
                   - assumption.
                   - simpl. setoid_rewrite lookup_insert_ne; auto.
                     rewrite <-H2. setoid_rewrite lookup_insert. reflexivity.
                 }
              (* non-kill exit - update *)
              ** assert (ι <> ι0) as HX. {
                   intro. subst. apply H9.
                   left. by setoid_rewrite lookup_insert.
                 }
                 (* How the arrive happened (it terminated a process): *)
                 pose proof HD1 as HD1copy.
                 inv HD1. 2: { destruct_or! H18; congruence. }
                 put (lookup ι0 : ProcessPool -> _) on H10 as HX2.
                 setoid_rewrite lookup_insert in HX2.
                 setoid_rewrite lookup_insert_ne in HX2; auto.
                 setoid_rewrite lookup_insert in HX2. inv HX2.
                 put (lookup ι0 : ProcessPool -> _) on H19 as HX3.
                 setoid_rewrite lookup_insert in HX3.
                 setoid_rewrite lookup_insert_ne in HX3; auto.
                 setoid_rewrite lookup_insert in HX3. inv HX3.
                 inv H20.
                 (***)
                 (* We need to apply some tricks here about the newly spawned
                    process termination, based on the termination of the parent.
                    The reason_value will affect the result dead processes! *)
                 subst.
                 do 2 eexists. split.
                 {
                   eapply n_trans. rewrite H10. exact HD1copy.
                   eapply n_trans. setoid_rewrite insert_commute; auto.
                   apply n_send. apply p_dead.
                   2: { by setoid_rewrite lookup_insert. }
                   1: {
                     clear -H17 Heth.
                     unfold etherPop in H17. repeat case_match; try congruence.
                     inv H17. apply Heth in H. by inv H.
                   }
                   eapply n_trans.
                   {
                     setoid_rewrite insert_commute; auto.
                     (* asserting emptyness of the signal list for the new process *)
                     assert (etherPop ι0 ι (etherAdd ι0 ι (SExit r0 true) e) = Some ((SExit r0 true), <[(ι0,ι):=[]]>e)). {
                       clear-H17 H12 HX. (* etherPop + appears + ι ≠ ι0 *)
                       unfold etherPop in H17. repeat case_match; try congruence.
                       inv H17.
                       unfold etherAdd. case_match.
                       * exfalso. apply H12.
                         left. exists ι0, l.
                         setoid_rewrite lookup_insert_ne in H0. 2: intro X; inv X; lia.
                         assumption.
                       * unfold etherPop. setoid_rewrite lookup_insert. do 2 f_equal.
                         by setoid_rewrite insert_insert.
                     }
                     apply n_arrive. eassumption. apply p_exit_terminate.
                     instantiate (1 := r0).
                     clear -H4 Heth2 H17 n0.
                     destruct_or! H4; destruct_hyps.
                     - congruence.
                     - right. left. set_solver.
                     - exfalso. simpl in *. subst.
                       unfold etherPop in H17. repeat case_match; try congruence.
                       inv H17. apply Heth2 in H. inv H.
                       by apply (H2 false).
                   }
                   eapply n_trans. 2: apply n_refl. apply n_send.
                   apply p_dead. 2: {
                     apply lookup_gset_to_gmap_Some. split.
                     apply elem_of_singleton. reflexivity.
                     reflexivity.
                   }
                   clear - H17 Heth.
                   unfold etherPop in H17. repeat case_match; try congruence.
                   inv H17. apply Heth in H. by inv H.
                 }
                 {
                   assert (<[ι0:=inr (<[ι:=r0]> d -- ι)]> p = p). {
                     apply map_eq. intros. destruct (decide (i = ι0)).
                     * subst. setoid_rewrite lookup_insert.
                       setoid_rewrite H0. f_equal.
                       setoid_rewrite delete_insert. reflexivity.
                       apply eq_None_ne_Some_2. intros ? ?.
                       eapply not_isUsedPool_step in H1; eauto.
                       2: {
                         intro. apply H12. clear-H17 H3.
                         unfold etherPop in H17; repeat case_match; try congruence.
                         inv H17. simpl in *.
                         destruct (decide (ι = sender)). 2: destruct (decide (ι = ι0)).
                         - subst. right. left. exists ι0. congruence.
                         - subst. left. exists sender. eexists. eassumption.
                         - do 2 right. exists sender, ι0. eexists. split. exact H.
                           set_solver.
                       }
                       apply H1. right. exists ι0, (inr d). split. assumption.
                       simpl. apply elem_of_union_list. exists ({[ι]} ∪ usedPIDsVal x).
                       split. 2: clear; set_solver.
                       apply elem_of_elements, elem_of_map_to_set.
                       do 2 eexists. split. 2: reflexivity. assumption.
                     * by setoid_rewrite lookup_insert_ne.
                   }
                   setoid_rewrite H2.
                   assert (gset_to_gmap r0 {[ι0]} -- ι0 = ∅). {
                     clear. setoid_rewrite <- gset_to_gmap_difference_singleton.
                     setoid_rewrite difference_diag_L.
                     by apply gset_to_gmap_empty.
                   }
                   setoid_rewrite H3. (* this is slow for some reason *)
                   (* two restricted lemmas needed here:
                     - None-s in the ether can be replaced by empty lists
                     - dead processes can be added which only communicate
                       with other dead processes
                           *)
                   eapply barbedBisim_trans.
                   apply dead_process_congruence with (ι := ι). assumption.
                   {
                     eapply not_isUsedPool_step in H1.
                     2: eassumption.
                     2: {
                       simpl. intro. apply H12. clear -H17 HX H8.
                       unfold etherPop in H17. repeat case_match; try congruence.
                       inv H17.
                       destruct (decide (ι = sender)).
                       * subst. right. left. exists ι0. congruence.
                       * right. right. do 3 eexists. split. eassumption. set_solver.
                     }
                     simpl. setoid_rewrite <- H2 in H1.
                     apply not_isUsedPool_insert_1 in H1.
                     by apply H1.
                   }
                   simpl.
                   assert (exists l, 
                      etherAdd ι ι0 (SExit r0 true) (<[(ι0, ι):=[]]> e) =
                       <[(ι, ι0):=l]> (<[(ι0, ι):=[]]> e)). {
                     unfold etherAdd. setoid_rewrite lookup_insert_ne. 2: congruence.
                     case_match; eexists; reflexivity.
                   }
                   destruct H8 as [xl Hxl]. setoid_rewrite Hxl.

                   (* TODO: progress is here, thm needs to be generalised *)
                   eapply barbedBisim_trans.
                   eapply ether_update_congruence with (ιd := ι0) (ιs := ι) (l := Some xl).
                   {
                     simpl. setoid_rewrite lookup_insert_ne; auto.
                     eassumption.
                   }
                   {
                     (* O ## dom Π *)
                     intro. clear -H8 Hdom. simpl in Hdom. set_solver.
                   }
                   {
                     simpl. by setoid_rewrite lookup_insert.
                   }
                   simpl.
                   setoid_rewrite insert_commute. 2: intro X; inv X; lia.
                   eapply ether_update_congruence with (l := Some []).
                   - by setoid_rewrite lookup_insert.
                   - assumption.
                   - simpl. setoid_rewrite lookup_insert_ne; auto.
                     rewrite <-H2. setoid_rewrite lookup_insert. reflexivity.
                 }
              (* link *)
              ** exists (e, p). eexists. split.
                 eapply n_trans. exact HD1. constructor.
                 apply barbedBisim_refl.
              (* unlink *)
              ** exists (e, p). eexists. split.
                 eapply n_trans. exact HD1. constructor.
                 apply barbedBisim_refl.
              (* if the destination does not exists - impossible *)
              ** exists (e, p). eexists. split.
                 eapply n_trans. exact HD1. constructor.
                 apply barbedBisim_refl.
            + (* a = τ *)
              exists A'. destruct A'. simpl in HD1. eexists. split.
              eapply n_trans. exact HD1. constructor.
              apply barbedBisim_refl.
          (* arrive was confluent *)
          - exists D. eexists. split_and!.
            eapply n_trans. eassumption. apply n_refl.
            eapply IH; try eassumption.
            eapply ether_wf_preserved. 2: eassumption.
            eapply n_trans. 2: apply n_refl. eassumption.
            2: by eapply difference_O.
            {
              clear -Heth2 H1.
              inv H1; simpl. 2: { destruct_or!; congruence. }
              unfold etherPop in H6. repeat case_match; try congruence.
              inv H6. intros ι l H0.
              destruct (decide ((ι, ι) = (sender, ι0))).
              * inv e. apply Heth2 in H. inv H.
                setoid_rewrite lookup_insert in H0. by inv H0.
              * setoid_rewrite lookup_insert_ne in H0; auto.
                eapply Heth2. eassumption.
            }
         (* self *)
         * admit. (* TODO HELPER needed *)
         (* spawn *)
         * admit. (* TODO HELPER needed *)
         (* τ *)
         * admit. (* TODO HELPER needed *)
         (* ε *)
         * admit. (* TODO HELPER needed *)
       }
    }
    { (* confluence *)
      admit.
    }
  * admit.
  * admit.
  * admit.
Qed.



Check chain_arrive_later.
Theorem confluence_any :
  ∀ (O : gset PID) (l : list (Action * PID)) (A B C : Node) (a : Action) (ι : PID),
    A -[l]ₙ->* B with O ->
    Forall (isChainable ∘ fst) l ->
    Forall (compatiblePIDOf a ∘ fst) l ->
    A -[ a | ι ]ₙ-> C with O ->
    exists D D' l' l'',
      B -[ l' ]ₙ->* D with O /\
      C -[l'']ₙ->* D' with O /\
      D ~ D' observing O.
Proof.
  induction l; intros; inv H.
  {
    exists C, C, [(a, ι)], []. split. 2: split.
    econstructor. eassumption. 1-2: constructor.
    apply barbedBisim_refl.
  }
  {
    inv H0. inv H1. simpl in *.
    destruct (decide (ι = ι0)).
    { (* same process *)
      subst. destruct (decide (a0 = a1)).
      { (* determinism *)
        subst. eapply concurrent_determinism in H2. 2: exact H6.
        subst. exists B, B, [], l. split_and!; try assumption.
        constructor.
        apply barbedBisim_refl.
      }
      { (* we check the actions for a0 - arrives are problematic
           while the others can't occur due to the determinism *)
        destruct a0.
        (* send *)
        * inv H6; subst.
          - inv H2. 2: { clear-H12. destruct_or!; congruence. }
            put (lookup ι0 : ProcessPool -> _) on H6 as HD.
            setoid_rewrite lookup_insert in HD. inv HD.
            inv H; inv H13; try (exfalso; apply n; reflexivity).
            (* dead process communication is problematic *)
            assert (ι' <> receiver). {
              intro; subst. setoid_rewrite H12 in H14. inv H14. by apply n.
            }
            admit. (* TODO: this should be doable by checking whether
                      the exit is in l -> then either no steps are made from
                      B or, the exit is chained after reaching B.
                      Since the targets are different, the etherAdd
                      order can be swapped *)
          - inv H4.
          - inv H2. 2: { clear-H13. destruct_or!; congruence. }
            exfalso.
            put (lookup ι0 : ProcessPool -> _) on H9 as HD.
            setoid_rewrite lookup_insert in HD. inv HD.
            destruct_or! H0; subst; inv H14; inv H.
            + inv H13. by cbn in H12.
            + inv H13. by cbn in H12.
            + inv H12. by cbn in H11.
            + inv H12. by cbn in H11.
          - inv H2. 2: { clear-H17. destruct_or!; congruence. }
            exfalso.
            put (lookup ι0 : ProcessPool -> _) on H13 as HD.
            setoid_rewrite lookup_insert in HD. inv HD.
            subst; inv H11; inv H18.
        (* arrive *)
        * apply not_eq_sym in n.
          assert (receiver = ι0). {
            inv H2; auto. destruct_or!; congruence.
          }
          subst.
          eapply (chain_arrive_later _ _ _ _ _ _ _ _ n H6 H4) in H2 as HD2.
          destruct HD2 as [D [HD1 [P | P]]].
          (* arrive killed some process *)
          - (* This case is problematic *)
            destruct P as [neweth [Eq1 Eq2]].
            subst.
            admit.
           
            
          
          (* arrive was confluent *)
          - eapply (IHl _ _ _ _ _ H8 H5 H7) in HD1.
            destruct HD1 as [D' [D'' [l' [l'' [P1 [P2 PB]]]]]].
            exists D', D'', l', ((a1, ι0)::l''). split_and!; try assumption.
            econstructor; eassumption.
        (* self *)
        * admit.
        (* spawn *)
        * admit.
        (* τ *)
        * admit.
        (* ε *)
        * admit.
      }
    }
    { (* different process - easy, by confluence *)
      pose proof (confluence _ _ _ _ _ H2 _ _ _ H3 H6 n).
      destruct_hyps.
      eapply IHl in H8. 4: exact H0. 2-3: assumption.
      destruct H8 as [D [D' [l' [l'' [P1 [P2 PB]]]]]].
      exists D, D', l', ((a1, ι0)::l''). split_and!; try assumption.
      econstructor; eassumption.
    }
  }
Qed.






Theorem confluence_any :
  ∀ (O : gset PID) (l : list (Action * PID)) (A B C : Node) (ι ιs : PID) (s : Signal),
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
        D' = () *)
         /\
        (*(D = D' \/
         ) *)
       D ~ D' observing O.
Proof.
  induction l; intros; inv H.
  {
    exists C. split. assumption.
    exists [], C. split. constructor. apply barbedBisim_refl.
  }
  {
    inv H0. simpl in *.
    destruct (decide (a0 = AArrive ιs ι s )).
    {
      subst. inv H3. (* arrives are not in the chain *)
    }
    {
      destruct (decide (ι = ι0)).
      { (* same process *)
        
      }
      { (* different process *)
      
      }
    }
  }
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






(* 
Lemma bisim_congr :
  forall U Π Π' eth eth', (eth, Π) ~ (eth', Π') using U ->
    forall Π2, (eth, Π ∪ Π2) ~ (eth', Π' ∪ Π2) using U.
Proof.
  cofix IH. intros. inv H. constructor; auto; simpl in *.
  * clear -H0. destruct H0. split; unfold preCompatibleNodes in *; intros.
    - apply isUntaken_comp in H1 as [H1_1 H1_2].
      apply H in H1_1.
      assert (isUntaken ι (eth', Π2)). {
        destruct H1_1, H1_2. split; auto.
      }
      now apply isUntaken_comp.
    - apply isUntaken_comp in H1 as [H1_1 H1_2].
      apply H0 in H1_1.
      assert (isUntaken ι (eth, Π2)). {
        destruct H1_1, H1_2. split; auto.
      }
      now apply isUntaken_comp.
  * clear H4 H5 H6. intros. destruct A'.
    apply step_in_comp in H as H'. destruct H' as [[Π1' [? ?]] | [Π2' [? ?]]].
    - subst. apply H3 in H4 as H4'. destruct_hyps. destruct x as [e' Π1''].
      (* (* At this point, we need renamings :( - or to know what PIDs are
         spawned by Π *)
      Print reductionPreCompatibility.
      (* spawns in x0 should be distinct from:
         - syntactically used PIDs in Π2 - for goal 3
         - ι0 -> if a = send(ι, ι0 <- destination, msg)
         - We also need a proof that (eth, Π) ~ (eth[x|->y], Π[x|->y])
      *)
      exists (e', Π1'' ∪ Π2), x0. split. 2: split. 3: split.
      4: { apply IH. assumption. }
      3: apply reductions_are_preserved_by_comp; auto.
      3: {
        intros. destruct H6 as [H6 _]. rewrite Forall_forall in H6.
        apply H6 in H9. unfold isUntaken in H9. simpl in *.
      } *)
      admit.
    - subst. exists (e, Π' ∪ Π2'), [(a, ι)]. split_and!.
      + split.
        ** destruct a; auto. simpl. constructor; auto. intro.
           eapply (no_spawn_unTaken (eth, Π ∪ Π2)). eapply n_trans. eassumption.
           apply n_refl. 2: cbn; left; reflexivity.
           apply isUntaken_comp in H5 as [? ?]. apply H0 in H5.
           apply isUntaken_comp; split; auto.
           (* ι0 should be Untaken wrt. eth *)
           destruct H5, H6. split; simpl in *; auto.
        ** intros; simpl in *; destruct a; auto; simpl in *.
           destruct_or!; auto. split. 2: split; auto.
           subst.
           (* ISSUE: we do not know, whether Π' uses ι0 *)
           (* is it okay to assume, that Π2 does not communicate to 
              PIDs in the domain of Π/Π' -> NO!

              is it okay to assume, that Π2 does not communicate to
              PIDs in ((dom Π ∪ dom Π') \ (dom Π ∩ dom Π')). Probably not.
            *)
           admit.
      + split.
        ** destruct a; auto. simpl. constructor; auto. intro.
           eapply (no_spawn_unTaken (eth, Π ∪ Π2)). eapply n_trans. eassumption.
           apply n_refl. 2: cbn; left; reflexivity.
           apply isUntaken_comp in H5 as [? ?].
           apply isUntaken_comp; split; auto.
        ** intros; simpl in *; destruct a; auto; simpl in *.
           destruct_or!; auto. split. 2: split; auto.
           subst.
           (* ISSUE: we do not know, whether Π uses ι0
              BOTTOMLINE: we should specify where can Π2 send messages?
            *)
           admit.
      + econstructor.
        apply reduction_is_preserved_by_comp_r. (* eassumption. *) admit. admit. admit. admit.
      + admit.
(*     - subst. exists (e, Π ∪ Π2'), [(a, ι)]. split_and!.
      split.
      + destruct a; auto. simpl. constructor; auto. intro.
        eapply (no_spawn_unTaken (eth, Π ∪ Π2)). eapply n_trans. eassumption.
        apply n_refl. 2: cbn; left; reflexivity.
        apply isUntaken_comp in H5 as [? ?]. apply H0 in H5.
        apply isUntaken_comp; split; auto.
        (* ι0 should be Untaken wrt. eth *)
        destruct H5, H6. split; simpl in *; auto.
      + intros; simpl in *; destruct a; auto; simpl in *.
        destruct_or!; auto. split. 2: split; auto.
        subst.
        (* ISSUE: we do not know, whether Π' uses ι0 *)
        admit.
      4: { apply IH. apply barbedBisim_refl. } *)
Abort.
 *)

