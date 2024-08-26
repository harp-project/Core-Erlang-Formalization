From CoreErlang.Concurrent Require Export BisimRenaming.

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

Theorem normalisation_τ_bisim :
  forall O (n n' : Node) ι,
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
      subst. eapply internal_det in H0 as H0'. 2: exact H.
      destruct H0'; destruct_hyps.
      * subst. exists C, []. split_and!.
        - slia.
        - constructor.
        - apply barbedExpansion_refl.
      * subst. destruct H3.
        { (* confluence *)
          do 2 eexists. split_and!.
          2: {
            eapply n_trans. exact H2. apply n_refl.
          }
          slia.
          eapply IH. exact H1.
        }
        { (* termination *)
          subst. exists x1. eexists.
          split_and!.
          2: {
            eapply n_trans. exact H2. apply n_refl.
          }
          slia.
          apply barbedExpansion_refl.
        }
    }
    { (* ι ≠ ι0 *)
      epose proof confluence _ _ _ _ _ H _ _ _ _ H0 n.
      Unshelve. 2: by simpl.
      destruct_hyps.
      exists x, [(a, ι0)]. split_and!.
      - slia.
      - econstructor. eassumption. constructor.
      - eapply IH. exact H2.
    }
  * clear IH. intros. exists source.
    eapply n_trans in H as HD. 2: eapply n_refl.
    inv HD. inv H6. inv H7. apply option_biforall_refl. intros. apply Signal_eq_refl.
  * clear IH. intros. exists B', [(τ, ι); (a, ι0)].
    split. 2: split. all: simpl.
    - slia.
    - econstructor. eassumption. econstructor. eassumption. constructor.
    - apply barbedExpansion_refl.
  * clear IH. intros. exists source, [(τ, ι)], n'. split; auto.
    econstructor. eassumption. constructor.
    apply option_biforall_refl. intros. by apply Signal_eq_refl.
Qed.

Theorem normalisation_τ_many_bisim :
  forall l O (n n' : Node),
    Forall (fun x => x.1 = τ) l ->
    n -[l]ₙ->* n' with O ->
    n ~ n' observing O.
Proof.
  induction l; intros.
  * inv H0. apply barbedBisim_refl.
  * inv H0. inv H. simpl in *. subst.
    eapply barbedBisim_trans.
    eapply normalisation_τ_bisim; eauto.
    apply IHl; try assumption.
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

(* In Lanese et al., Lemma 9 does not hold for this semantics,
   because arrival can change the semantics of receive primops!!!
   E.g., recv_peek_message returns None for empty mailbox, while the
   first message if it is nonempty (and arrival can put a message into the
   empty mailbox).
*)

Theorem chain_arrive_later :
  forall O A B C a ι ιs s,
  (* a <> AArrive ιs ι s -> *)
  A -[ a | ι ]ₙ-> B with O ->
  isChainable a ->
  A -[ AArrive ιs ι s | ι]ₙ-> C with O ->
  exists D, B -[ AArrive ιs ι s | ι]ₙ-> D with O /\ (* Arrive can be evaluated later *)
    ((exists neweth, etherPop ιs ι B.1 = Some (s, neweth) /\ (* We remove the arrived signal from B's ether *)
     (neweth, optional_update C.2 a ι s) = D (*/\
     C = node_from a s B *)
     ) \/ (* For spawns, there is a new process, moreover, for spawn_links the dead process has a new link in the list of links! *)
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
      (* recv_next *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_next") [] [] :: fs0, RBox,
      mailboxPush mb v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_next") [] [] :: fs0, RBox,
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
          destruct l0; invSome. by simpl.
        }
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
      (* recv_wait_timeout infinity *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [VLit "infinity"%string],
      mailboxPush (oldmb, msg :: newmb) v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [VLit "infinity"%string],
      mailboxPush (oldmb, msg :: newmb) v, links, flag) ∥ Π). {
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
      (* trap_exit exception *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v0], mailboxPush mb v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v0], mailboxPush mb v, links, flag) ∥ Π). {
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
      (* recv_next *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by left.
      (* removeMessage *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by intuition.
      (* recv_wait_timeout infinity *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by left.
      (* recv_wait_timeout 0 *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by left.
      (* recv_wait_timeout error *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by left.
      (* trap_exit exception *)
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
      (* trap_exit exception *)
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
      (* recv_next *)
      + eexists. split.
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
       eapply n_other.
       econstructor.
       {
         clear -H11. destruct mb. simpl in *.
         destruct l0; invSome. by simpl.
       }
       by intuition.
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
      (* recv_wait_timeout infinity *)
      + eexists. split.
        1: { constructor. eassumption. by apply p_exit_convert. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [VLit "infinity"%string],
      mailboxPush (oldmb, msg :: newmb) (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links, true)
 ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [VLit "infinity"%string],
      mailboxPush (oldmb, msg :: newmb) (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links, true)
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
        eapply n_other. by constructor. by left.
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
      (* trap_exit exception *)
      + eexists. split.
        1: { constructor. eassumption. by apply p_exit_convert. }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links, true) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links, true) ∥ Π). {
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
       eapply n_other.
       econstructor.
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
     (* recv_wait_timeout infinity *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [VLit "infinity"%string],
      (oldmb, msg :: newmb), {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [VLit "infinity"%string],
      (oldmb, msg :: newmb), {[ιs]} ∪ links, flag) ∥ Π). {
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
      (* trap_exit exception *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v], mb, {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v], mb, {[ιs]} ∪ links, flag) ∥ Π). {
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
         eapply n_other. by econstructor.
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
        by econstructor.
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
      (* trap_exit exception *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v], mb, links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v], mb, links ∖ {[ιs]}, flag) ∥ Π). {
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

(* Arrive and ε actions create non-confluent reductions with any other reduction of the same process instrumented by the inter-process semantics. *)
Definition isChainable2 (a : Action) : Prop :=
match a with
 | τ | ASpawn _ _ _ true | ASelf _  => True
 | _ => False
end.

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
      (* recv_next *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_next") [] [] :: fs0, RBox,
      mailboxPush mb v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_next") [] [] :: fs0, RBox,
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
          destruct l0; invSome. by simpl.
        }
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
      (* recv_wait_timeout infinity *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [VLit "infinity"%string],
      mailboxPush (oldmb, msg :: newmb) v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (IPrimOp "recv_wait_timeout") [] [] :: fs0, RValSeq [VLit "infinity"%string],
      mailboxPush (oldmb, msg :: newmb) v, links, flag) ∥ Π). {
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
      (* trap_exit exception *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v0], mailboxPush mb v, links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v0], mailboxPush mb v, links, flag) ∥ Π). {
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
      (* recv_next *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by intuition.
      (* removeMessage *)
      + eexists. split.
        1: { constructor. eassumption. constructor. assumption. }
        right. eapply n_other. by constructor. by intuition.
      (* recv_wait_timeout infinity *)
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
      (* trap_exit exception *)
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
      (* trap_exit exception *)
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
      (* recv_next *)
      + eexists. split.
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
       eapply n_other.
       econstructor.
       {
         clear -H11. destruct mb. simpl in *.
         destruct l0; invSome. by simpl.
       }
       by intuition.
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
        by econstructor.
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
      (* trap_exit exception *)
      + eexists. split.
        1: { constructor. eassumption. by apply p_exit_convert. }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links, true) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v],
      mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ιs; reason]), links, true) ∥ Π). {
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
         eapply n_other. by econstructor.
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
        by econstructor.
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
      (* trap_exit exception *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v], mb, {[ιs]} ∪ links, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v], mb, {[ιs]} ∪ links, flag) ∥ Π). {
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
         eapply n_other. by econstructor.
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
        by econstructor.
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
      (* trap_exit exception *)
      + eexists. split.
        1: { constructor. eassumption. constructor. }
        right.
        assert (ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v], mb, links ∖ {[ιs]}, flag) ∥ prs = ι
 ↦ inl
     (FParams (ICall (VLit "erlang"%string) (VLit "process_flag"%string))
        [VLit "trap_exit"%string] [] :: fs0, RValSeq [v], mb, links ∖ {[ιs]}, flag) ∥ Π). {
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
Theorem terminated_process_bisim :
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
      eapply renamePID_is_preserved with (from := p) (to := fresh) in H1 as HD.
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
Theorem ether_update_terminated :
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
      apply renamePID_is_preserved with (from := p) (to := fresh) in H0.
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
      apply renamePID_is_preserved with (from := p) (to := fresh) in H0.
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
(* Definition no_self_exits_via_link (e : Ether) :=
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
    A ~ B observing O. *)

Theorem normalisation_self_bisim :
  forall O (n n' : Node) ι,
(*     O ## dom n.2 -> *)
    n -[ASelf ι | ι]ₙ-> n' with O ->
    n ~ n' observing O.
Proof.
  intros. apply barbedExpansion_implies_bisim.
  generalize dependent n. generalize dependent n'. revert ι. cofix IH. intros.
  constructor; auto.
  * intros.
    rename n into A, A' into B, n' into C.
    destruct (decide (ι = ι0)).
    {
      subst.
      inv H. clear H2. inv H1. simpl in *. inv H0.
      * put (lookup ι0 : ProcessPool -> _) on H2 as D.
        setoid_rewrite lookup_insert in D. inv D. inv H5.
      * put (lookup ι0 : ProcessPool -> _) on H1 as D.
        setoid_rewrite lookup_insert in D. inv D. inv H6.
        (* TODO: boiler plate, there is minimal difference in 5 of the
          following 6 cases (the case for terminated exit is different!) *)
        { (* message *)
          do 2 eexists. split_and!. 2: {
            eapply n_trans. apply n_arrive. eassumption.
            constructor. apply n_refl.
          }
          1: slia.
          apply IH with (ι := ι0); clear IH.
          * replace (ι0 ↦ inl (fs, RValSeq [VPid ι0], mailboxPush mb v, links, flag) ∥ Π) with
              (ι0 ↦ inl (fs, RValSeq [VPid ι0], mailboxPush mb v, links, flag) ∥ prs).
            2: {
              apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as D.
              destruct (decide (i = ι0)).
              * subst. by setoid_rewrite lookup_insert.
              * setoid_rewrite lookup_insert_ne in D; auto.
                by setoid_rewrite lookup_insert_ne.
            }
            apply n_other. constructor. set_solver.
        }
        { (* dropped exit *)
          do 2 eexists. split_and!. 2: {
            eapply n_trans. apply n_arrive. eassumption.
            constructor. assumption. apply n_refl.
          }
          1: slia.
          apply IH with (ι := ι0); clear IH.
          * replace (ι0 ↦ inl (fs, RValSeq [VPid ι0], mb, links, flag) ∥ Π) with
              (ι0 ↦ inl (fs, RValSeq [VPid ι0], mb, links, flag) ∥ prs).
            2: {
              apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as D.
              destruct (decide (i = ι0)).
              * subst. by setoid_rewrite lookup_insert.
              * setoid_rewrite lookup_insert_ne in D; auto.
                by setoid_rewrite lookup_insert_ne.
            }
            apply n_other. constructor. set_solver.
        }
        { (* terminated exit *)
          do 2 eexists. split_and!. 2: {
            eapply n_trans. apply n_arrive. eassumption.
            apply p_exit_terminate. eassumption. apply n_refl.
          }
          1: slia.
          replace (ι0 ↦ inr (gset_to_gmap reason' links) ∥ Π) with
              (ι0 ↦ inr (gset_to_gmap reason' links) ∥ prs).
          2: {
            apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as D.
            destruct (decide (i = ι0)).
            * subst. by setoid_rewrite lookup_insert.
            * setoid_rewrite lookup_insert_ne in D; auto.
              by setoid_rewrite lookup_insert_ne.
          }
          apply barbedExpansion_refl.
        }
        { (* converted exit *)
          do 2 eexists. split_and!. 2: {
            eapply n_trans. apply n_arrive. eassumption.
            apply p_exit_convert. assumption. apply n_refl.
          }
          1: slia.
          apply IH with (ι := ι0); clear IH.
          * replace (ι0 ↦ inl (fs, RValSeq [VPid ι0], mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ι1; reason]), links, true) ∥ Π) with
              (ι0 ↦ inl (fs, RValSeq [VPid ι0], mailboxPush mb (VTuple [VLit "EXIT"%string; VPid ι1; reason]), links, true) ∥ prs).
            2: {
              apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as D.
              destruct (decide (i = ι0)).
              * subst. by setoid_rewrite lookup_insert.
              * setoid_rewrite lookup_insert_ne in D; auto.
                by setoid_rewrite lookup_insert_ne.
            }
            apply n_other. constructor. set_solver.
        }
        { (* link *)
          do 2 eexists. split_and!. 2: {
            eapply n_trans. apply n_arrive. eassumption.
            constructor. apply n_refl.
          }
          1: slia.
          apply IH with (ι := ι0); clear IH.
          * replace (ι0 ↦ inl (fs, RValSeq [VPid ι0], mb, {[ι1]} ∪ links, flag) ∥ Π) with
              (ι0 ↦ inl (fs, RValSeq [VPid ι0], mb, {[ι1]} ∪ links, flag) ∥ prs).
            2: {
              apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as D.
              destruct (decide (i = ι0)).
              * subst. by setoid_rewrite lookup_insert.
              * setoid_rewrite lookup_insert_ne in D; auto.
                by setoid_rewrite lookup_insert_ne.
            }
            apply n_other. constructor. set_solver.
        }
        { (* unlink *)
          do 2 eexists. split_and!. 2: {
            eapply n_trans. apply n_arrive. eassumption.
            constructor. apply n_refl.
          }
          1: slia.
          apply IH with (ι := ι0); clear IH.
          * replace (ι0 ↦ inl (fs, RValSeq [VPid ι0], mb, links ∖ {[ι1]}, flag) ∥ Π) with
              (ι0 ↦ inl (fs, RValSeq [VPid ι0], mb, links ∖ {[ι1]}, flag) ∥ prs).
            2: {
              apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as D.
              destruct (decide (i = ι0)).
              * subst. by setoid_rewrite lookup_insert.
              * setoid_rewrite lookup_insert_ne in D; auto.
                by setoid_rewrite lookup_insert_ne.
            }
            apply n_other. constructor. set_solver.
        }
      * put (lookup ι0 : ProcessPool -> _) on H1 as D.
        setoid_rewrite lookup_insert in D. inv D. destruct_or! H6.
        - subst. inv H2. inv H7. inv H6.
        - subst. inv H2.
          eexists. exists []. split. slia. split. apply n_refl.
          replace (ι0 ↦ inl (fs, RValSeq [VPid ι0], mb, links, flag) ∥ Π0) with
             (ι0 ↦ inl (fs, RValSeq [VPid ι0], mb, links, flag) ∥ Π).
          2: {
            apply map_eq. intros. put (lookup i : ProcessPool -> _) on H1 as D.
            destruct (decide (i = ι0)).
            * subst. by setoid_rewrite lookup_insert.
            * setoid_rewrite lookup_insert_ne in D; auto.
              by setoid_rewrite lookup_insert_ne.
          }
          apply barbedExpansion_refl.
        - subst. inv H2.
      * put (lookup ι0 : ProcessPool -> _) on H1 as D.
        setoid_rewrite lookup_insert in D. inv D. inv H10.
    }
    { (* ι ≠ ι0 *)
      epose proof confluence _ _ _ _ _ H _ _ _ _ H0 n.
      Unshelve. 2: by simpl.
      destruct_hyps.
      exists x, [(a, ι0)]. split_and!.
      - slia.
      - econstructor. eassumption. constructor.
      - eapply IH. exact H2.
    }
  * clear IH. intros. exists source.
    eapply n_trans in H as HD. 2: eapply n_refl.
    inv HD. inv H6. inv H7.
    apply option_biforall_refl. intros. by apply Signal_eq_refl.
  * clear IH. intros. exists B', [(ASelf ι, ι); (a, ι0)].
    split. 2: split. all: simpl.
    - slia.
    - econstructor. eassumption. econstructor. eassumption. constructor.
    - apply barbedExpansion_refl.
  * clear IH. intros. exists source, [(ASelf ι, ι)], n'. split; auto.
    econstructor. eassumption. constructor.
    apply option_biforall_refl. intros. by apply Signal_eq_refl.
Qed.

Theorem silent_steps_bisim :
  forall l O (n n' : Node),
    Forall (fun x => x.1 = τ \/ exists ι, x.1 = ASelf ι) l ->
    n -[l]ₙ->* n' with O ->
    n ~ n' observing O.
Proof.
  induction l; intros.
  * inv H0. apply barbedBisim_refl.
  * inv H0. inv H. simpl in *. destruct H2; subst.
    - eapply barbedBisim_trans.
      eapply normalisation_τ_bisim; eauto.
      apply IHl; try assumption.
    - destruct H. subst. eapply barbedBisim_trans.
      assert (ι = x). {
        inv H4. destruct_or! H0; try congruence.
      }
      subst.
      eapply normalisation_self_bisim; eauto.
      eapply IHl; try eassumption.
Qed.

Opaque create_result.
Unset Guard Checking.
Theorem ether_empty_update_bisim :
  forall ιs ιd A O,
    ιd ∉ O ->
    (A.1 !! (ιs, ιd) = None \/ A.1 !! (ιs, ιd) = Some []) ->
    A ~ (<[(ιs, ιd):=[]]>A.1, A.2) observing O.
Proof.
  cofix IH; intros.
  destruct H0.
  {
    constructor.
    * intros.
      inv H1; simpl in *.
      - do 2 eexists. split. eapply n_trans. apply n_send. exact H2.
        apply n_refl.
        unfold etherAdd. destruct (decide ((ι, ι') = (ιs, ιd))).
        + clear IH. inv e. setoid_rewrite lookup_insert.
          rewrite H0. simpl. setoid_rewrite insert_insert.
          apply barbedBisim_refl.
        + setoid_rewrite lookup_insert_ne; auto.
          destruct (ether !! (ι, ι')) eqn:P; setoid_rewrite P.
          all: setoid_rewrite insert_commute; auto.
          all: apply IH; try assumption.
          all: simpl; left; by setoid_rewrite lookup_insert_ne.
      - unfold etherPop in H2. repeat case_match; try congruence. inv H2.
        assert ((ι1, ι) <> (ιs, ιd)) by (intro X; inv X; congruence).
        do 2 eexists. split. eapply n_trans. apply n_arrive. 2: exact H3.
        2: apply n_refl.
        1: {
          unfold etherPop.
          setoid_rewrite lookup_insert_ne; auto. setoid_rewrite H1.
          reflexivity.
        }
        setoid_rewrite insert_commute; auto.
        apply IH; auto. left. by setoid_rewrite lookup_insert_ne.
      - do 2 eexists. split. eapply n_trans. apply n_other. exact H2.
        exact H3. apply n_refl.
        apply IH; auto.
      - assert (∃fresh,  ¬ isUsedPool fresh (ι ↦ p ∥ Π) /\
                         ¬ appearsEther fresh ether /\
                         ¬ appearsEther fresh (<[(ιs, ιd):=[]]> ether) /\
                         fresh <> ιs /\ fresh <> ιd /\
                         fresh ∉ usedPIDsAct (ASpawn ι' v1 v2 link_flag) /\
                         fresh ∉ O /\
                         ¬ isUsedPool fresh
         (ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false) ∥ ι ↦ p' ∥ Π)). {
          (* freshness *)
          pose proof (infinite_is_fresh (
             ιs :: ιd
          :: elements O
          ++ elements (allPIDsPool (ι ↦ p ∥ Π))
          ++ elements (allPIDsPool (ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false)
                     ∥ ι ↦ p' ∥ Π))
          ++ elements (allPIDsEther ether)
          ++ elements (allPIDsEther (<[(ιs, ιd):=[]]> ether))
          ++ elements (usedPIDsAct (ASpawn ι' v1 v2 link_flag)) 
          )).
        remember (fresh _) as y in H1. clear-H1. exists y.
        repeat apply not_elem_of_cons in H1 as [? H1].
        repeat apply not_elem_of_app in H1 as [? H1].
        split_and!; try assumption.
        4, 5: set_solver.
        * apply allPIDsPool_isNotUsed_1. set_solver.
        * apply allPIDsEther_does_not_appear_1. set_solver.
        * apply allPIDsEther_does_not_appear_1. set_solver.
        * apply allPIDsPool_isNotUsed_1. set_solver.
        }
        assert (ι' ∉ usedPIDsVal v1 ∪ usedPIDsVal v2 ∪ usedPIDsProc p). {
          clear H1. intro. apply H4.
          right. exists ι, p. split. by setoid_rewrite lookup_insert.
          inv H7; simpl in *; set_solver.
        }
        destruct H1 as [fresh ?]. destruct_hyps.
        do 2 eexists. split.
        eapply n_trans. eapply n_spawn with (ι' := fresh); try eassumption.
        2: apply n_refl.
        {
          eapply renamePID_is_preserved_local with (from := ι') (to := fresh) in H7.
          simpl in H7.
          rewrite renamePIDPID_1 in H7. 2: assumption.
          2: {
            intro. apply H1. right. exists ι, p.
            by setoid_rewrite lookup_insert.
          }
          rewrite isNotUsed_renamePID_val in H7.
          rewrite isNotUsed_renamePID_val in H7.
          rewrite isNotUsed_renamePID_proc in H7 at 1. exact H7.
          1,3,4: set_solver.
          {
            intro. apply H1. right. exists ι, p.
            by setoid_rewrite lookup_insert.
          }
        }
        opose proof* (rename_bisim O ether (ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false) ∥ ι ↦ p' ∥ Π) [(ι', fresh)]).
        1: {
          cbn. set_solver.
        }
        simpl in H16.
        rewrite does_not_appear_renamePID_ether in H16; auto.
        rewrite pool_insert_renamePID in H16.
        rewrite renamePIDPID_sym_1 in H16.
        rewrite isNotUsed_renamePID_proc in H16; auto.
        2: {
          intro. apply create_result_usedPIDs in H6 as H6'.
          apply mk_list_usedPIDs with (ι' := ι') in H2 as H2'. simpl in H17.
          assert (ι' ∈ usedPIDsRed r). {
            assert (ι' <> ι). {
              intro. subst. apply H4. left. by setoid_rewrite lookup_insert.
            }
            destruct link_flag; set_solver.
          }
          simpl in H6.
          apply H4. right. exists ι, p. split. by setoid_rewrite lookup_insert.
          inv H7; simpl.
Transparent create_result.
          all: simpl in H6; inv H6.
          all: case_match; inv H19; simpl in H18.
          2,4: set_solver.
          {
            apply subst_usedPIDs in H18 as [|]. set_solver.
            destruct_hyps. apply list_subst_idsubst_inl in H7.
            apply elem_of_app in H7 as [|].
            * apply elem_of_map_iff in H7. destruct_hyps. destruct x1, p.
              subst. simpl in H18.
              assert (ι' ∈ flat_union (λ x : nat * nat * Exp, usedPIDsExp x.2) ext). {
                apply elem_of_union in H18 as [|]. 2: set_solver.
                apply elem_of_flat_union. eexists. split; eassumption.
              }
              set_solver.
            * opose proof* (proj2 H2').
              apply elem_of_flat_union. eexists; split; eassumption.
              set_solver.
          }
          {
            apply subst_usedPIDs in H18 as [|]. set_solver.
            destruct_hyps. apply list_subst_idsubst_inl in H7.
            apply elem_of_app in H7 as [|].
            * apply elem_of_map_iff in H7. destruct_hyps. destruct x1, p.
              subst. simpl in H18.
              assert (ι' ∈ flat_union (λ x : nat * nat * Exp, usedPIDsExp x.2) ext). {
                apply elem_of_union in H18 as [|]. 2: set_solver.
                apply elem_of_flat_union. eexists. split; eassumption.
              }
              set_solver.
            * opose proof* (proj2 H2').
              apply elem_of_flat_union. eexists; split; eassumption.
              set_solver.
          }
        }
        2: {
          intro. apply H15. right. exists ι'. eexists. split.
          by setoid_rewrite lookup_insert. assumption.
        }
        assert ((ι ↦ p' ∥ Π) .[ ι' ⇔ fresh ]ₚₚ = ι ↦ renamePIDProc ι' fresh p'  ∥ Π) as HX. {
          rewrite pool_insert_renamePID.
          assert (renamePIDPID_sym ι' fresh ι = ι). {
            simpl in H13.
            unfold renamePIDPID_sym. replace (ι =? fresh) with false.
            2: { symmetry. apply Nat.eqb_neq. intro. subst.
                 apply H1. left. by setoid_rewrite lookup_insert.
            }
            break_match_goal. 2: reflexivity.
            eqb_to_eq. exfalso. subst. apply H4.
            left. by setoid_rewrite lookup_insert.
          }
          rewrite H17. apply map_eq.
          intros. destruct (decide (ι = i)).
          * subst. by setoid_rewrite lookup_insert.
          * setoid_rewrite lookup_insert_ne; auto.
            unfold renamePIDPool.
            apply not_isUsedPool_insert_1 in H1 as HF.
            apply not_isUsedPool_insert_1 in H4 as Hi.
            destruct (decide (i = fresh)).
            2: destruct (decide (i = ι')).
            - subst.
              replace fresh with (renamePIDPID_sym ι' fresh ι') at 1 by renamePIDPID_sym_case_match.
              setoid_rewrite lookup_kmap; auto.
              setoid_rewrite lookup_fmap.
              destruct HF.
              apply not_elem_of_dom in H18.
              setoid_rewrite H18.
              destruct Hi. apply not_elem_of_dom in H20. setoid_rewrite H20.
              reflexivity.
            - subst.
              replace ι' with (renamePIDPID_sym ι' fresh fresh) at 1 by renamePIDPID_sym_case_match.
              setoid_rewrite lookup_kmap; auto.
              setoid_rewrite lookup_fmap.
              destruct HF.
              apply not_elem_of_dom in H18.
              setoid_rewrite H18.
              destruct Hi. apply not_elem_of_dom in H20. setoid_rewrite H20.
              reflexivity.
            - replace i with (renamePIDPID_sym ι' fresh i) at 1 by renamePIDPID_sym_case_match.
              setoid_rewrite lookup_kmap; auto.
              setoid_rewrite lookup_fmap.
              destruct (Π!!i) eqn:P; setoid_rewrite P. 2: reflexivity.
              simpl. setoid_rewrite isNotUsed_renamePID_proc.
              reflexivity.
              1: intro; apply H4; right.
              2: intro; apply H1; right.
              all: exists i, p0; split; try setoid_rewrite lookup_insert_ne; auto.
        }
        rewrite HX in H16.
        eapply barbedBisim_trans.
        exact H16.
        apply IH; auto.
    * clear IH.
      intros. exists source, []. eexists.
      split. constructor.
      simpl. setoid_rewrite lookup_insert_ne. 2: intro X; inv X; set_solver.
      apply option_biforall_refl. intros. apply Signal_eq_refl.
    * intros. destruct A. simpl in *.
      inv H1; simpl in *; subst.
      - do 2 eexists. split. eapply n_trans. apply n_send. exact H7.
        apply n_refl.
        unfold etherAdd. destruct (decide ((ι, ι') = (ιs, ιd))).
        + clear IH. inv e0. setoid_rewrite lookup_insert.
          rewrite H0. simpl. setoid_rewrite insert_insert.
          apply barbedBisim_refl.
        + setoid_rewrite lookup_insert_ne; auto.
          destruct (e !! (ι, ι')) eqn:P; setoid_rewrite P.
          all: setoid_rewrite insert_commute; auto.
          all: apply IH; try assumption.
          all: simpl; left; by setoid_rewrite lookup_insert_ne.
      - unfold etherPop in H4. repeat case_match; try congruence. inv H4.
        assert ((ι1, ι) <> (ιs, ιd)).
        {
          intro X. inv X. by setoid_rewrite lookup_insert in H1.
        }
        do 2 eexists. split. eapply n_trans. apply n_arrive. 2: exact H8.
        2: apply n_refl.
        1: {
          unfold etherPop.
          setoid_rewrite lookup_insert_ne in H1; auto. setoid_rewrite H1.
          reflexivity.
        }
        setoid_rewrite insert_commute; auto.
        apply IH; auto. left. by setoid_rewrite lookup_insert_ne.
      - do 2 eexists. split. eapply n_trans. apply n_other. exact H4.
        exact H8. apply n_refl.
        apply IH; auto.
      - do 2 eexists. split. eapply n_trans. eapply n_spawn. 6: exact H12.
        all: try eassumption.
        2: apply n_refl.
        2: apply IH; auto.
        intro. apply H7. destruct H1. 2: destruct H1.
        + left. destruct H1, H1. exists x, x0. setoid_rewrite lookup_insert_ne.
          assumption.
          intro X. inv X. congruence.
        + destruct_hyps. right. left.
          exists x. setoid_rewrite lookup_insert_ne.
          assumption.
          intro X. inv X. congruence.
        + destruct_hyps. right. right.
          exists x, x0, x1. setoid_rewrite lookup_insert_ne.
          split; assumption.
          intro X. inv X. congruence.
    * clear IH.
      intros. exists source, []. eexists.
      split. constructor.
      simpl. setoid_rewrite lookup_insert_ne. 2: intro X; inv X; set_solver.
      apply option_biforall_refl. intros. apply Signal_eq_refl.
  }
  {
    assert (A.1 = <[(ιs, ιd):=[]]> A.1). {
      apply map_eq. intro. destruct (decide (i = (ιs, ιd))).
      * subst. by setoid_rewrite lookup_insert.
      * by setoid_rewrite lookup_insert_ne.
    }
    rewrite <- H1. destruct A.
    apply barbedBisim_refl.
  }
Qed.
Set Guard Checking.