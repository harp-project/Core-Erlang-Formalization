(**
  This file contains the inter-process semantics of Core Erlang. This semantics
  defines how concurrent actions should be propagated between processes.

  The file contains:
  - the ether (the signals in transit), process pools and nodes;
  - the operations of the ether and their properties;
  - the inter-process (node) semantics and its reflexive, transitive closure;
  - the PIDs used in ethers and process pools;
  - PID renaming in process pools and ethers.
*)

From CoreErlang.Concurrent Require Export ProcessSemantics.
From stdpp Require Export base fin_maps gmap.

Import ListNotations.

(** * Ethers, process pools and nodes *)

(** The ether contains the signals in transit, indexed by their source and
    destination. This representation assures that signals sent from the same
    process to the same destination are delivered in the same order. *)
Definition Ether : Set := gmap (PID * PID) (list Signal).

(** Inserting a list of signals into the ether *)
Local Example ether_insert_lookup :
  ((<[(1, 2):=[]]>∅ : Ether) !! (1, 2)) = Some [].
Proof.
  cbn. reflexivity.
Qed.

(** The domain of an ether with a single inserted entry *)
Local Example ether_insert_dom :
  dom (<[(1, 2):=[]]>∅ : Ether) = {[(1,2)]}.
Proof.
  reflexivity.
Qed.

(** A PID that is not in the set `K` *)
Definition fresh_pid (K : gset PID) : PID := fresh K.

(** `fresh_pid` does not return an element of the set. *)
Local Example fresh_pid_test :
  fresh_pid ({[1;2;3]} : gset PID) ≠ 1.
Proof.
  pose proof (is_fresh ({[1;2;3]} : gset PID)). unfold fresh_pid. set_solver.
Qed.

(** Process pools map PIDs to processes. *)
Definition ProcessPool : Set := gmap PID Process.

(** Inserting a process into a pool *)
Local Example pool_insert_lookup :
  (<[1:=inl ([], RValSeq [VNil], ([], []), ∅, false)]>∅ : ProcessPool) !! 1 <> None.
Proof.
  intro. inv H.
Qed.

(** `ι ↦ p ∥ Π` inserts the process `p` with PID `ι` into the pool `Π`, and
    `Π -- ι` removes the process with PID `ι`. *)
Notation "pid ↦ p ∥ n" := (@insert PID Process ProcessPool _ pid p n) (at level 32, right associativity).
Notation "n -- pid" := (delete pid n) (at level 31, left associativity).

(** Nodes consist of an ether and a process pool. *)
Definition Node : Set := Ether * ProcessPool.

(** Removing a process from a pool *)
Local Example pool_insert_delete :
  (<[1:=inl ([], RValSeq [VNil], ([], []), ∅, false)]>∅ -- 1 : ProcessPool) = ∅.
Proof. cbn. reflexivity. Qed.

(** * Ether operations *)

(** Appends the signal `m` from `source` to `dest` to the ether. *)
Definition etherAdd (source dest : PID) (m : Signal) (n : Ether) : Ether :=
  match n !! (source, dest) with
  | Some l => <[(source, dest) := l ++ [m]]>n
  | None   => <[(source, dest) := [m]]>n
  end.

(** Removes the first signal in transit from `source` to `dest` from the
    ether, if there is one. *)
Definition etherPop (source dest : PID) (n : Ether) :
  option (Signal * Ether) :=
match n !! (source, dest) with
| None | Some [] => None
| Some (x::xs) => Some (x, <[(source, dest):=xs]>n)
end.

(** Popping a signal from the ether commutes with adding a signal. *)
Lemma etherPop_etherAdd :
  forall ι ether s ι' ether', etherPop ι ι' ether = Some (s, ether') ->
  forall ι'' ι''' s', etherPop ι ι' (etherAdd ι'' ι''' s' ether) = Some (s, etherAdd ι'' ι''' s' ether').
Proof.
  intros. unfold etherPop, etherAdd in *.
  break_match_hyp.
  * destruct (ether !! (ι'', ι''')) eqn:D2; cbn.
    destruct (decide ((ι'', ι''') = (ι, ι'))) as [EQ | EQ].
    - inv EQ.
      setoid_rewrite lookup_insert_eq. destruct l. simpl; try congruence.
      inv H. do 2 f_equal.
      setoid_rewrite insert_insert_eq.
      setoid_rewrite lookup_insert_eq.
      by setoid_rewrite insert_insert_eq.
    - destruct l; inv H.
      setoid_rewrite lookup_insert_ne.
      setoid_rewrite D2.
      setoid_rewrite Heqo.
      do 2 f_equal.
      setoid_rewrite insert_insert_ne. 
      all: auto.
      rewrite insert_insert_ne by apply EQ; reflexivity.
    - destruct l; inv H.
      destruct (decide ((ι'', ι''') = (ι, ι'))) as [EQ | EQ]; subst. 1: congruence.
      setoid_rewrite lookup_insert_ne.
      setoid_rewrite D2.
      setoid_rewrite Heqo.
      setoid_rewrite insert_insert_ne. 
      rewrite insert_insert_ne by apply EQ; reflexivity.
      all: auto.
  * congruence.
Qed.

(** Adding signals between different source-destination pairs can be done in
    either order. *)
Lemma etherAdd_swap :
  forall ether ιs1 ιd1 m1 ιs2 ιd2 m2, (ιs1, ιd1) <> (ιs2, ιd2) ->
    etherAdd ιs1 ιd1 m1 (etherAdd ιs2 ιd2 m2 ether) =
    etherAdd ιs2 ιd2 m2 (etherAdd ιs1 ιd1 m1 ether).
Proof.
  intros. unfold etherAdd.
  destruct (ether !! _) eqn:D1; break_match_goal.
  all: (* normal rewrite fails on the potential different type class instances *)
    setoid_rewrite lookup_insert_ne in Heqo; [|congruence];
    setoid_rewrite Heqo;
    setoid_rewrite lookup_insert_ne; [|congruence];
    setoid_rewrite D1;
    setoid_rewrite Heqo;
    apply insert_insert_ne; congruence.
Qed.

(** Adding signals from different sources can be done in either order. *)
Corollary etherAdd_swap_1 :
  forall ether ιs1 ιd1 m1 ιs2 ιd2 m2, ιs1 <> ιs2 ->
    etherAdd ιs1 ιd1 m1 (etherAdd ιs2 ιd2 m2 ether) =
    etherAdd ιs2 ιd2 m2 (etherAdd ιs1 ιd1 m1 ether).
Proof.
  intros. apply etherAdd_swap. congruence.
Qed.

(** Adding signals to different destinations can be done in either order. *)
Corollary etherAdd_swap_2 :
  forall ether ιs1 ιd1 m1 ιs2 ιd2 m2, ιd1 <> ιd2 ->
    etherAdd ιs1 ιd1 m1 (etherAdd ιs2 ιd2 m2 ether) =
    etherAdd ιs2 ιd2 m2 (etherAdd ιs1 ιd1 m1 ether).
Proof.
  intros. apply etherAdd_swap. congruence.
Qed.

(** An entry of the ether after adding a signal is either an original entry,
    or the entry of the updated source-destination pair, ending with the new
    signal. *)
Lemma etherAdd_lookup :
  forall ιs ιd ι1 ι2 t l eth,
    etherAdd ιs ιd t eth !! (ι1, ι2) = Some l ->
      eth !! (ι1, ι2) = Some l \/
      (ι1 = ιs /\ ι2 = ιd /\ exists l', l = l' ++ [t]).
Proof.
  intros. destruct (decide ((ιs, ιd) = (ι1, ι2))).
  * inv e. right. intuition.
    unfold etherAdd in H. case_match; setoid_rewrite lookup_insert_eq in H; inv H.
    1: by eexists.
    1: by exists [].
  * unfold etherAdd in H. case_match; setoid_rewrite lookup_insert_ne in H; auto.
Qed.

(** * PIDs appearing in the ether *)

(** Targetedness checks whether the ether potentially contains (or
    contained) signals with the given destination. *)
Definition isTargetedEther (ι : PID) (n : Ether) : Prop :=
  exists ι' l, n !! (ι', ι) = Some l.

(** If a PID appears in the ether, it is either targeted, or it is the
    source of a signal, or it appears inside a signal. *)
Definition appearsEther (ι : PID) (eth : Ether) : Prop :=
  isTargetedEther ι eth \/
  (exists (ι' : PID), eth !! (ι, ι') ≠ None) \/
  (exists (ιs ιd : PID) (t : list Signal),
     eth !! (ιs, ιd) = Some t /\ ι ∈ (flat_union usedPIDsSignal t)).

(** A PID does not appear in the ether, if it is neither the destination nor
    the source of signals, and it does not occur in any signal. *)
Proposition not_appearsEther_alt :
  forall ι eth, ¬appearsEther ι eth <->
    (
      (forall ι', eth !! (ι', ι) = None) /\
      (forall ι', eth !! (ι, ι') = None) /\
      (forall ιs ιd t, eth !! (ιs, ιd) = Some t -> ι ∉ (flat_union usedPIDsSignal t))
    ).
Proof.
  intros. split; intros.
  * intuition.
    - apply eq_None_ne_Some_2. intros ? ?. apply H. left.
      do 2 eexists. eassumption.
    - apply eq_None_ne_Some_2. intros. intro.
      apply H. right. left. exists ι'. by rewrite H0.
    - apply H. right. right.
      apply elem_of_flat_union in H1. destruct_hyps.
      exists ιs, ιd, t. split; auto.
      apply elem_of_flat_union. set_solver.
  * intro. unfold appearsEther, isTargetedEther in H0. destruct_hyps. destruct H0. destruct_hyps.
    congruence.
    destruct_or!.
    - set_solver.
    - set_solver.
Qed.

(** Adding a signal preserves targetedness. *)
Lemma isTargetedEther_etherAdd :
  forall ether ι ι' ι'' s,
    isTargetedEther ι ether ->
    isTargetedEther ι (etherAdd ι' ι'' s ether).
Proof.
  intros. unfold etherAdd, isTargetedEther.
  destruct H as [ι'0 [l H]].
  exists ι'0. repeat break_match_goal; eqb_to_eq; subst; auto.
  all: destruct (decide ((ι'0, ι) = (ι', ι''))); try rewrite e.
  all: try setoid_rewrite lookup_insert_eq; auto.
  all: try setoid_rewrite lookup_insert_ne; auto.
  all: eexists; try reflexivity; try eassumption.
Qed.

(** Adding a signal preserves the PIDs appearing in the ether. *)
Lemma appearsEther_etherAdd :
  forall ether ι ι' ι'' s,
    appearsEther ι ether ->
    appearsEther ι (etherAdd ι' ι'' s ether).
Proof.
  intros. unfold etherAdd, appearsEther.
  destruct H. 2: destruct H.
  {
    left. by apply isTargetedEther_etherAdd.
  }
  {
    destruct_hyps. right. left.
    exists x. intro. case_match.
    * setoid_rewrite lookup_insert_ne in H0.
      2: { intro X; inv X. setoid_rewrite H1 in H.
           by setoid_rewrite lookup_insert_eq in H0.
          }
      by setoid_rewrite H0 in H.
    * setoid_rewrite lookup_insert_ne in H0. 2: congruence.
      by setoid_rewrite H0 in H.
  }
  {
    destruct_hyps. do 2 right.
    case_match.
    * destruct (decide ((ι', ι'') = (x, x0))).
      {
        inv e. do 3 eexists. split.
        setoid_rewrite lookup_insert. rewrite decide_True.
        reflexivity. auto.
        rewrite flat_union_app. set_solver.
      }
      exists x, x0, x1.
      setoid_rewrite lookup_insert_ne; auto.
    * assert ((x, x0) ≠ (ι', ι'')) by set_solver.
      exists x, x0, x1.
      setoid_rewrite lookup_insert_ne; auto.
  }
Qed.

(** If a PID is targeted after adding a signal with a different destination,
    then it was targeted before adding the signal as well. *)
Lemma isTargetedEther_etherAdd_rev :
  forall ether ι ι' ι'' s,
    isTargetedEther ι (etherAdd ι' ι'' s ether) ->
    ι'' <> ι ->
    isTargetedEther ι ether.
Proof.
  intros. unfold etherAdd in *. unfold isTargetedEther in *.
  destruct H as [ι'0 [l H]].
  destruct (ether !! (ι', ι'')) eqn:Eq; simpl in *.
  all: setoid_rewrite lookup_insert_ne in H; [|intro X; inv X; congruence].
  * do 2 eexists. eassumption.
  * do 2 eexists. eassumption.
Qed.

(** If a PID appears in the ether after adding a signal in which it does not
    occur (neither as source, nor as destination, nor in the signal), then it
    appeared in the ether before adding the signal as well. *)
Lemma appearsEther_etherAdd_rev :
  forall ether ι ι' ι'' s,
    appearsEther ι (etherAdd ι' ι'' s ether) ->
    ι'' <> ι ->
    ι' <> ι ->
    ι ∉ usedPIDsSignal s ->
    appearsEther ι ether.
Proof.
  intros. unfold etherAdd in *. unfold appearsEther in *.
  destruct H. 2: destruct H.
  {
    left. by apply isTargetedEther_etherAdd_rev in H.
  }
  {
    destruct_hyps.
    case_match.
    * setoid_rewrite lookup_insert_ne in H.
      {
        right. left. eexists. exact H.
      }
      {
        intro X. inv X.
      }
    * setoid_rewrite lookup_insert_ne in H.
      {
        right. left. eexists. exact H.
      }
      {
        intro X. inv X.
      }
  }
  {
    destruct_hyps.
    case_match.
    * destruct (decide ((ι', ι'') = (x, x0))).
      {
        inv e. setoid_rewrite lookup_insert_eq in H. inv H.
        rewrite flat_union_app in H3. simpl in H3.
        right. right.
        do 3 eexists. split. eassumption. set_solver.
      }
      {
        setoid_rewrite lookup_insert_ne in H; auto.
        right. right.
        do 3 eexists. split; eassumption.
      }
    * destruct (decide ((ι', ι'') = (x, x0))).
      {
        inv e. setoid_rewrite lookup_insert_eq in H. inv H.
        set_solver.
      }
      {
        setoid_rewrite lookup_insert_ne in H; auto.
        right. right.
        do 3 eexists. split; eassumption.
      }
  }
Qed.

(** Popping a signal preserves targetedness, except possibly for the
    destination of the popped signal. *)
Lemma isTargetedEther_etherPop :
  forall {ether ι ι' ι'' s ether'},
    isTargetedEther ι ether ->
    etherPop ι' ι'' ether = Some (s, ether') ->
    isTargetedEther ι ether' \/ ι = ι''.
Proof.
  intros.
  destruct H as [ι'0 [l H]].
  unfold etherPop in H0. break_match_hyp. 2: congruence.
  destruct l0; inv H0.
  destruct (Nat.eq_dec ι ι''); auto.
  left. exists ι'0.
  setoid_rewrite lookup_insert_ne; try split; auto.
  2: intro; congruence.
  eexists. eassumption.
Qed.

(** Popping a signal preserves the PIDs appearing in the ether, except
    possibly for the source, the destination and the PIDs of the popped
    signal. *)
Lemma appearsEther_etherPop :
  forall {ether ι ι' ι'' s ether'},
    appearsEther ι ether ->
    etherPop ι' ι'' ether = Some (s, ether') ->
    appearsEther ι ether' \/ ι = ι'' \/ ι = ι' \/ ι ∈ usedPIDsSignal s.
Proof.
  intros.
  destruct H. 2: destruct H.
  {
    eapply isTargetedEther_etherPop in H0. 2: exact H.
    destruct H0. by left;left. by right; left.
  }
  {
    destruct_hyps. unfold etherPop in H0. case_match. 2: congruence.
    case_match. congruence.
    subst l. inv H0. left. right. left.
    exists x. destruct (decide ((ι', ι'') = (ι, x))).
    {
      inv e. by setoid_rewrite lookup_insert_eq.
    }
    {
      by setoid_rewrite lookup_insert_ne.
    }
  }
  {
    destruct_hyps. unfold etherPop in H0. case_match. 2: congruence.
    case_match. congruence.
    subst l. inv H0.
    destruct (decide ((ι', ι'') = (x, x0))).
    {
      inv e. simpl in H1.
      apply elem_of_union in H1 as [|]. 1: set_solver.
      left. right. right.
      do 3 eexists.
      split. by setoid_rewrite lookup_insert_eq.
      assumption.
    }
    {
      left. right. right.
      do 3 eexists.
      split. setoid_rewrite lookup_insert_ne. 2: exact n.
      eassumption. assumption.
    }
  }
Qed.

(** If a PID is targeted after popping a signal, then it was targeted before
    popping the signal as well. *)
Lemma isTargetedEther_etherPop_rev :
  forall {ether ι ι' ι'' s ether'},
    isTargetedEther ι ether' ->
    etherPop ι' ι'' ether = Some (s, ether') ->
    isTargetedEther ι ether.
Proof.
  intros.
  destruct H as [ι'0 [l H]].
  unfold etherPop in H0. break_match_hyp. 2: congruence.
  destruct l0. congruence. inv H0.
  unfold isTargetedEther.
  destruct (decide ((ι', ι'') = (ι'0, ι))); try inv e.
  * setoid_rewrite lookup_insert in H. inv H.
    exists ι'0. eexists. eassumption.
  * setoid_rewrite lookup_insert_ne in H. 2: auto.
    exists ι'0. eexists. eassumption.
Qed.

(** If a PID appears in the ether after popping a signal, then it appeared in
    the ether before popping the signal as well. *)
Lemma appearsEther_etherPop_rev :
  forall {ether ι ι' ι'' s ether'},
    appearsEther ι ether' ->
    etherPop ι' ι'' ether = Some (s, ether') ->
    appearsEther ι ether.
Proof.
  intros.
  destruct H. 2: destruct H.
  {
    left. by eapply isTargetedEther_etherPop_rev in H0.
  }
  {
    destruct_hyps. unfold etherPop in H0. break_match_hyp. 2: congruence.
    destruct l. congruence. inv H0.
    destruct (decide ((ι', ι'') = (ι, x))).
    {
      inv e. setoid_rewrite lookup_insert in H.
      right. left. exists x. intro. congruence.
    }
    {
      setoid_rewrite lookup_insert_ne in H; auto.
      right. left. eexists. eassumption.
    }
  }
  {
    destruct_hyps. unfold etherPop in H0. break_match_hyp. 2: congruence.
    destruct l. congruence. inv H0.
    destruct (decide ((ι', ι'') = (x, x0))).
    {
      inv e. setoid_rewrite lookup_insert_eq in H. inv H.
      right. right. exists x, x0, (s :: x1).
      simpl. set_solver.
    }
    {
      setoid_rewrite lookup_insert_ne in H; auto.
      right. right. exists x, x0, x1. split; assumption.
    }
  }
Qed.

(** * Inter-process semantics *)

(** A PID is used in a pool if it is associated with a process, or it occurs
    in a process. *)
Definition isUsedPool (ι : PID) (Π : ProcessPool) :=
  Π !! ι <> None \/
  (exists ι' p, Π !! ι' = Some p /\ ι ∈ (usedPIDsProc p)).

Reserved Notation "n -[ a | ι ]ₙ-> n' 'with' O" (at level 50).
(** `n -[ a | ι ]ₙ-> n' with O`: the node `n` can take a step to `n'`, in
    which the process `ι` performs the action `a`. `O` is the set of observed
    PIDs - these can be assumed to have associated processes that consume
    the signals sent to these PIDs. This is exploited in the
    bisimulation-based program equivalence definitions which check the
    communication on these PIDs. *)
Inductive interProcessStep (O : gset PID) : Node -> Action -> PID -> Node -> Prop :=
(** sending any signal *)
| n_send p p' ether prs (ι ι' : PID) t :
  p -⌈ASend ι ι' t⌉-> p'
->
  (ether, ι ↦ p ∥ prs) -[ASend ι ι' t | ι]ₙ->  (etherAdd ι ι' t ether, ι ↦ p' ∥ prs) with O

(** This leads to the loss of determinism: *)
(** arrival of any signal *)
| n_arrive ι ι0 p p' ether ether' prs t:
  etherPop ι0 ι ether = Some (t, ether') ->
  p -⌈AArrive ι0 ι t⌉-> p' ->
  (ether, ι ↦ p ∥ prs) -[AArrive ι0 ι t | ι]ₙ-> (ether',
                                            ι ↦ p' ∥ prs) with O

(* NOTE: link sent to non-existing process triggers exit, messages should be discarded when sent to non-existing process? - Probably not to argue about the congruence of ∥ *)
(** internal actions *)
| n_other p p' a Π (ι : PID) ether:
  p -⌈a⌉-> p' ->
  (a = τ \/ a = ASelf ι \/ a = ε)
->
   (ether, ι ↦ p ∥ Π) -[a| ι]ₙ-> (ether, ι ↦ p' ∥ Π) with O

(** spawning processes *)
| n_spawn Π (p p' : Process) v1 v2 l ι ι' ether r eff link_flag:
  mk_list v2 = Some l ->
  ι' ∉ O -> (* can't spawn on outside interface/observable PIDs *)
  (* NOTE: these two are a bit restricted. We do not model systems that use
     PIDs before they are spawned. PIDs currently in use cannot be spawned
     (i.e., if they appear either as a source or target of a floating message,
     inside a floating message, process, or they are associated with a process).

     link_flag influences whether spawn_link was called or just spawn
   *)
  ~isUsedPool ι' (ι ↦ p ∥ Π) ->
  ~appearsEther ι' ether -> (* We can't model spawning such processes that receive
                         already floating messages from the ether. *)
  create_result (IApp v1) l = Some (r, eff) ->
  p -⌈ASpawn ι' v1 v2 link_flag⌉-> p'
->
  (ether, ι ↦ p ∥ Π) -[ASpawn ι' v1 v2 link_flag | ι]ₙ-> (ether, ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false) ∥ ι ↦ p' ∥ Π) with O

where "n -[ a | ι ]ₙ-> n' 'with' O" := (interProcessStep O n a ι n').

Reserved Notation "n -[ l ]ₙ->* n' 'with' O" (at level 50).
(** Reflexive, transitive closure of the inter-process semantics, with the
    log of the actions and the acting processes. *)
Inductive closureNodeSem (O : gset PID) : Node -> list (Action * PID) -> Node -> Prop :=
| n_refl n : n -[ [] ]ₙ->* n with O
| n_trans n n' n'' l a ι:
  n -[a|ι]ₙ-> n' with O -> n' -[l]ₙ->* n'' with O
->
  n -[(a,ι)::l]ₙ->* n'' with O
where "n -[ l ]ₙ->* n' 'with' O" := (closureNodeSem O n l n').

(** * PIDs used in nodes *)

(** All PIDs of an ether: the sources, the destinations and the PIDs used in
    the signals. *)
Definition allPIDsEther (eth : Ether) : gset PID :=
  flat_union (fun '((ιs, ιd), sigs) => {[ιs; ιd]} ∪ flat_union usedPIDsSignal sigs) (map_to_list eth).

(** All PIDs of a process pool: the PIDs of the processes and the PIDs used
    in them. *)
Definition allPIDsPool (Π : ProcessPool) : gset PID :=
  flat_union (fun '(ι, proc) => {[ι]} ∪ usedPIDsProc proc) (map_to_list Π).

(** A PID that is not in `allPIDsPool` is not used in the pool. *)
Lemma allPIDsPool_isNotUsed_1 :
  forall ι Π,
    ι ∉ allPIDsPool Π -> ¬isUsedPool ι Π.
Proof.
  intros. intro. destruct H0.
  * apply H. apply elem_of_flat_union.
    apply not_eq_None_Some in H0. destruct H0 as [proc H0].
    exists (ι, proc). split. 2: set_solver.
    by apply elem_of_map_to_list.
  * apply H. apply elem_of_flat_union.
    destruct H0 as [ι' [proc [P_1 P_2]]].
    exists (ι', proc). split.
    by apply elem_of_map_to_list.
    set_solver.
Qed.

(** A PID that is not used in the pool is not in `allPIDsPool` (the converse
    of `allPIDsPool_isNotUsed_1`). *)
Lemma allPIDsPool_isNotUsed_2 :
  forall ι Π,
    ¬isUsedPool ι Π ->
    ι ∉ allPIDsPool Π.
Proof.
  intros. intro. apply H.
  unfold allPIDsPool in H0. apply elem_of_flat_union in H0.
  destruct_hyps. destruct x as [ι' proc].
  apply elem_of_map_to_list in H0 as P.
  apply elem_of_union in H1 as [|].
  * assert (ι = ι') by set_solver.
    subst. left. by setoid_rewrite P.
  * right. exists ι', proc. split; assumption.
Qed.

(** A PID that is not in `allPIDsEther` does not appear in the ether. *)
Lemma allPIDsEther_does_not_appear_1 :
  forall ι eth,
    ι ∉ allPIDsEther eth -> ¬appearsEther ι eth.
Proof.
  intros. intro. apply H.
  apply elem_of_flat_union.
  destruct H0. 2: destruct H0.
  * destruct H0 as [ιs [l H0]].
    exists (ιs, ι, l). split.
    by apply elem_of_map_to_list.
    set_solver.
  * destruct H0 as [ιd H0].
    apply not_eq_None_Some in H0. destruct H0 as [l H0].
    exists (ι, ιd, l). split.
    by apply elem_of_map_to_list.
    set_solver.
  * destruct H0 as [ιs [ιd [l [P1 P2]]]].
    exists (ιs, ιd, l). split.
    by apply elem_of_map_to_list.
    set_solver.
Qed.

(** A PID that does not appear in the ether is not in `allPIDsEther` (the
    converse of `allPIDsEther_does_not_appear_1`). *)
Lemma allPIDsEther_does_not_appear_2 :
  forall ι eth,
    ¬appearsEther ι eth ->
    ι ∉ allPIDsEther eth.
Proof.
  intros. intro. apply H.
  unfold allPIDsEther in H0. apply elem_of_flat_union in H0.
  destruct_hyps. destruct x as [[ιs ιd] l].
  apply elem_of_map_to_list in H0 as P.
  apply elem_of_union in H1 as [|].
  destruct (decide (ι = ιd)).
  * subst. left. by exists ιs, l.
  * assert (ι = ιs) by set_solver. subst. right. left.
    exists ιd. by setoid_rewrite P.
  * right. right. exists ιs, ιd, l. split; assumption.
Qed.

(** * PID renaming in nodes *)

(** PID renaming in process pools. Only the keys are swapped (`p` and `p'`
    are exchanged, to keep the keys injective); inside the processes, `p` is
    renamed to `p'` (with `renamePIDProc`), which is not a swap. *)
Definition renamePIDPool (p p' : PID) (Π : ProcessPool) : ProcessPool :=
  kmap (renamePIDPID_sym p p') (renamePIDProc p p' <$> Π).

(** Notation for PID renaming in process pools *)
Notation "e .[ x ⇔ y ]ₚₚ" := (renamePIDPool x y e) (at level 1, left associativity).

(** PID renaming in ethers. Only the keys (the source and destination PIDs)
    are swapped; inside the signals, `p` is renamed to `p'` (with
    `renamePIDSignal`), which is not a swap. *)
Definition renamePIDEther (p p' : PID) (eth : Ether) : Ether :=
  kmap (prod_map (renamePIDPID_sym p p') (renamePIDPID_sym p p'))
    ((map (renamePIDSignal p p')) <$> eth).

(** Notation for PID renaming in ethers *)
Notation "e .[ x ⇔ y ]ₑ" := (renamePIDEther x y e) (at level 1, left associativity).

(** * Properties of process pools and ethers *)

(** If inserting into two maps at the same key results in equal maps, then
    the inserted elements are equal. *)
Lemma insert_eq : forall {K T} {H : EqDecision K} {H0: Countable K} ι (p p' : T) (Π Π' : gmap K T),
  <[ι:=p]>Π = <[ι:=p']> Π' -> p = p'.
Proof.
  intros. apply map_eq_iff with (i := ι) in H1.
  setoid_rewrite lookup_insert in H1. simplify_map_eq. reflexivity. 
Qed.

(** If inserting into two maps at the same key results in equal maps, then
    inserting any other element at that key also results in equal maps. *)
Lemma insert_eq_Π : forall {K T} {H : EqDecision K} {H0: Countable K} ι (p p' : T) (Π Π' : gmap K T),
  <[ι:=p]>Π = <[ι:=p']>Π' -> forall p'', <[ι:=p'']>Π = <[ι:=p'']>Π'.
Proof.
  intros.
  apply map_eq_iff. intro ι''.
  apply map_eq_iff with (i := ι'') in H1.
  destruct (decide (ι'' = ι)).
  * subst. setoid_rewrite lookup_insert. by destruct_decide_eq.
  * setoid_rewrite lookup_insert_ne in H1; auto.
  setoid_rewrite lookup_insert_ne; auto.
Qed.

(** A PID used in a pool after inserting a process is either used in the
    rest of the pool, or it is the PID of the process, or it is used by the
    process. *)
Lemma isUsedPool_insert_1 :
  forall prs ι ι0 p,
    isUsedPool ι (ι0 ↦ p ∥ prs) ->
    isUsedPool ι (prs -- ι0) \/ ι = ι0 \/ ι ∈ (usedPIDsProc p).
Proof.
  intros. unfold isUsedPool in *. destruct (decide (ι = ι0)).
  * subst. setoid_rewrite lookup_insert in H; intros.
    all: right. left. reflexivity. 
  * setoid_rewrite lookup_insert_ne in H at 1; auto. intros; destruct_or!.
    (* all: try now firstorder. *)
    - left. left. intro. apply lookup_delete_None in H0. firstorder.
    - destruct H as [ι' [p0 [H_1 H_2]]].
      destruct (decide (ι0 = ι')).
      + subst. setoid_rewrite lookup_insert in H_1. inv H_1.
        destruct_decide_eq.
        inv H0.
        set_solver.
      + setoid_rewrite lookup_insert_ne in H_1; auto.
        left. right. exists ι', p0. split; auto.
        apply lookup_delete_Some. split; auto.
Qed.

(** The converse of `isUsedPool_insert_1`. *)
Lemma isUsedPool_insert_2 :
  forall prs ι ι0 p,
    (isUsedPool ι (prs -- ι0)) \/ ι = ι0 \/ ι ∈ (usedPIDsProc p) ->
    isUsedPool ι (ι0 ↦ p ∥ prs).
Proof.
  intros. unfold isUsedPool in *.
  destruct (decide (ι = ι0)).
  * subst. setoid_rewrite lookup_insert. simplify_map_eq. by left.
  * setoid_rewrite lookup_insert_ne at 1; auto. destruct_or!.
    - left. intro. apply H. apply lookup_delete_None. by right.
    - destruct_hyps. right. exists x, x0.
      apply lookup_delete_Some in H as [H_1 H_2].
      setoid_rewrite lookup_insert_ne; set_solver.
    - right. exists ι0, p. split; auto.
      by setoid_rewrite lookup_insert. set_solver.
    - right. exists ι0, p. setoid_rewrite lookup_insert.
      destruct_decide_eq. by split.
Qed.

(** A PID which is not used in a pool after inserting a process is neither in
    the domain of the rest of the pool, nor the PID of the process. *)
Lemma not_isUsedPool_insert_1 :
  forall Π ι' ι p,
  ¬ isUsedPool ι' (ι ↦ p ∥ Π) ->
  (ι' ∉ dom Π) /\ ι' <> ι.
Proof.
  intros. unfold isUsedPool in H.
  split; intro; apply H.
  * left. apply elem_of_dom in H0. unfold is_Some in H0. destruct_hyps.
    destruct (decide (ι = ι')); subst.
    - setoid_rewrite lookup_insert. by destruct_decide_eq.
    - setoid_rewrite lookup_insert_ne; auto. by setoid_rewrite H0.
  * left. subst. setoid_rewrite lookup_insert. by destruct_decide_eq.
Qed.

(** Targetedness is decidable. *)
Proposition isTargetedEther_dec :
  forall ι ether, isTargetedEther ι ether \/ ~isTargetedEther ι ether.
Proof.
  intros.
  unfold isTargetedEther.
  remember (base.filter (fun '((ιs, ιd), l) => ι = ιd) ether) as newmap.
  destruct (map_eq_dec_empty newmap).
  * right. intro. destruct H as [x [l H]].
    subst newmap.
    destruct (ether !! (x, ι)) eqn:P. 2: congruence. inv H.
    eapply map_filter_empty_not_lookup with (i := (x, ι)) (x := l) in e.
    contradiction. auto.
  * left.
    apply map_choose in n as n'. destruct n' as [x [l H]].
    destruct x.
    subst newmap. exists p.
    apply map_lookup_filter_Some_1_2 in H as H'. destruct H'.
    apply map_lookup_filter_Some_1_1 in H. subst.
    setoid_rewrite H. now do 2 eexists.
Qed.

(** Whether a PID appears in the ether is decidable. *)
Proposition appearsEther_dec :
  forall ι ether, appearsEther ι ether \/ ~appearsEther ι ether.
Proof.
  intros.
  unfold appearsEther.
  remember (base.filter (fun '((ιs, ιd), l) => ι = ιd \/ ι = ιs \/ ι ∈ flat_union  usedPIDsSignal l) ether) as newmap.
  destruct (map_eq_dec_empty newmap).
  * right. intro. destruct H. 2: destruct H.
    {
      destruct H as [x [l H]].
      subst newmap.
      destruct (ether !! (x, ι)) eqn:P. 2: congruence. inv H.
      eapply map_filter_empty_not_lookup with (i := (x, ι)) (x := l) in e.
      contradiction. auto.
    }
    {
      subst newmap. destruct_hyps.
      destruct (ether !! (ι, x)) eqn:P. 2: congruence.
      eapply map_filter_empty_not_lookup with (i := (ι, x)) (x := l) in e.
      contradiction. auto.
    }
    {
      subst newmap. destruct_hyps.
      destruct (ether !! (x, x0)) eqn:P. 2: congruence. inv H.
      eapply map_filter_empty_not_lookup with (i := (x, x0)) (x := x1) in e.
      contradiction. auto.
    }
  * left.
    apply map_choose in n as n'. destruct n' as [x [l H]].
    destruct x.
    subst newmap.
    apply map_lookup_filter_Some_1_1 in H as Hin.
    apply map_lookup_filter_Some_1_2 in H.
    destruct H. 2: destruct H.
    {
      subst. left. do 2 eexists. exact Hin.
    }
    {
      subst. right. left. exists p0. intro. by setoid_rewrite Hin in H.
    }
    {
      right. right.
      do 3 eexists. split. exact Hin. assumption.
    }
Qed.
