(**
  This file contains the inter-process semantics of Core Erlang. This semantics
  defines how concurrent actions should be propagated between processes.
*)

From CoreErlang.Concurrent Require Export ProcessSemantics.
From stdpp Require Export base fin_maps gmap.

Import ListNotations.

Theorem Signal_eq_dec (s s' : Signal) : {s = s'} + {s <> s'}.
Proof. decide equality; try apply Val_eq_dec; try apply Nat.eq_dec. decide equality. Qed.

(** This representation assures that messages sent from the same process,
    are delivered in the same order *)
Definition Ether : Set := gmap (PID * PID) (list Signal).

Local Goal ((<[(1, 2):=[]]>∅ : Ether) !! (1, 2)) = Some [].
Proof.
  cbn. reflexivity.
Qed.

Local Goal dom (<[(1, 2):=[]]>∅ : Ether) = {[(1,2)]}.
Proof.
  reflexivity.
Qed.

Definition fresh_pid (K : gset nat) : nat := fresh K.

Local Goal fresh_pid ({[1;2;3]} : gset nat) ≠ 1.
Proof.
  epose proof (is_fresh {[1;2;3]}). set_solver.
  Unshelve. exact nat. exact (gset nat). all: typeclasses eauto.
Defined.

Definition ProcessPool : Set := gmap PID Process.
Local Goal (<[1:=inl ([], RValSeq [VNil], ([], []), ∅, false)]>∅ : ProcessPool) !! 1 <> None.
Proof.
  intro. inv H.
Qed.

Notation "pid ↦ p ∥ n" := (@insert PID Process ProcessPool _ pid p n) (at level 32, right associativity).
Notation "n -- pid" := (delete pid n) (at level 31, left associativity).

Definition Node : Set := Ether * ProcessPool.
Local Goal (<[1:=inl ([], RValSeq [VNil], ([], []), ∅, false)]>∅ -- 1 : ProcessPool) = ∅.
Proof. cbn. reflexivity. Qed.

Definition etherAdd (source dest : PID) (m : Signal) (n : Ether) : Ether :=
  match n !! (source, dest) with
  | Some l => <[(source, dest) := l ++ [m]]>n
  | None   => <[(source, dest) := [m]]>n
  end.

Definition etherPop (source dest : PID) (n : Ether) :
  option (Signal * Ether) :=
match n !! (source, dest) with
| None | Some [] => None
| Some (x::xs) => Some (x, <[(source, dest):=xs]>n)
end.

Lemma etherPop_greater :
  forall ι ether s ι' ether', etherPop ι ι' ether = Some (s, ether') ->
  forall ι'' ι''' s', etherPop ι ι' (etherAdd ι'' ι''' s' ether) = Some (s, etherAdd ι'' ι''' s' ether').
Proof.
  intros. unfold etherPop, etherAdd in *.
  break_match_hyp.
  * destruct (ether !! (ι'', ι''')) eqn:D2; cbn.
    destruct (decide ((ι'', ι''') = (ι, ι'))) as [EQ | EQ].
    - inv EQ;
      setoid_rewrite lookup_insert; destruct l; simpl; try congruence.
      inv H. do 2 f_equal. setoid_rewrite insert_insert.
      setoid_rewrite lookup_insert.
      now setoid_rewrite insert_insert.
    - destruct l; inv H.
      setoid_rewrite lookup_insert_ne.
      setoid_rewrite D2.
      setoid_rewrite Heqo.
      now setoid_rewrite insert_commute at 1.
      all: auto.
    - destruct l; inv H.
      destruct (decide ((ι'', ι''') = (ι, ι'))) as [EQ | EQ]; subst. 1: congruence.
      setoid_rewrite lookup_insert_ne.
      setoid_rewrite D2.
      setoid_rewrite Heqo.
      now setoid_rewrite insert_commute at 1.
      all: auto.
  * congruence.
Qed.

Corollary etherAdd_swap_1 :
  forall ether ιs1 ιd1 m1 ιs2 ιd2 m2, ιs1 <> ιs2 ->
    etherAdd ιs1 ιd1 m1 (etherAdd ιs2 ιd2 m2 ether) =
    etherAdd ιs2 ιd2 m2 (etherAdd ιs1 ιd1 m1 ether).
Proof.
  intros. unfold etherAdd.
  destruct (ether !! _) eqn:D1; break_match_goal.
  all: (* normal rewrite fails on the potential different type class instances *)
    setoid_rewrite lookup_insert_ne in Heqo; [|intro D; inv D; congruence];
    setoid_rewrite Heqo;
    setoid_rewrite lookup_insert_ne; [|intro D; inv D; congruence];
    setoid_rewrite D1;
    setoid_rewrite Heqo;
    apply insert_commute; intro D; inv D; congruence.
Qed.

Corollary etherAdd_swap_2 :
  forall ether ιs1 ιd1 m1 ιs2 ιd2 m2, ιd1 <> ιd2 ->
    etherAdd ιs1 ιd1 m1 (etherAdd ιs2 ιd2 m2 ether) =
    etherAdd ιs2 ιd2 m2 (etherAdd ιs1 ιd1 m1 ether).
Proof.
  intros. unfold etherAdd.
  destruct (ether !! _) eqn:D1; break_match_goal.
  all: (* normal rewrite fails on the potential different type class instances *)
    setoid_rewrite lookup_insert_ne in Heqo; [|intro D; inv D; congruence];
    setoid_rewrite Heqo;
    setoid_rewrite lookup_insert_ne; [|intro D; inv D; congruence];
    setoid_rewrite D1;
    setoid_rewrite Heqo;
    apply insert_commute; intro D; inv D; congruence.
Qed.

(* Targetedness checks whether the ether potentially contains (or contained)
   signals with the given destination *)
Definition isTargetedEther (ι : PID) (n : Ether) : Prop :=
  exists ι' l, n !! (ι', ι) = Some l.

(* If a PID appears in the ether, it is either targeted, or is a source of a signal
   or it appears inside a signal's PIDs.
  *)
Definition appearsEther (ι : PID) (eth : Ether) : Prop :=
  isTargetedEther ι eth \/
  (exists (ι' : PID), eth !! (ι, ι') ≠ None) \/
  (exists (ιs ιd : PID) (t : list Signal),
     eth !! (ιs, ιd) = Some t /\ ι ∈ (flat_union usedPIDsSignal t)).

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

Lemma isTargetedEther_etherAdd :
  forall ether ι ι' ι'' s,
    isTargetedEther ι ether ->
    isTargetedEther ι (etherAdd ι' ι'' s ether).
Proof.
  intros. unfold etherAdd, isTargetedEther.
  destruct H as [ι'0 [l H]].
  exists ι'0. repeat break_match_goal; eqb_to_eq; subst; auto.
  all: destruct (decide ((ι'0, ι) = (ι', ι''))); try rewrite e.
  all: try setoid_rewrite lookup_insert; auto.
  all: try setoid_rewrite lookup_insert_ne; auto.
  all: eexists; try reflexivity; try eassumption.
Qed.

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
           by setoid_rewrite lookup_insert in H0.
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
        setoid_rewrite lookup_insert. reflexivity.
        rewrite flat_union_app. set_solver.
      }
      exists x, x0, x1.
      setoid_rewrite lookup_insert_ne; auto.
    * assert ((x, x0) ≠ (ι', ι'')) by set_solver.
      exists x, x0, x1.
      setoid_rewrite lookup_insert_ne; auto.
  }
Qed.

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
        inv e. setoid_rewrite lookup_insert in H. inv H.
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
        inv e. setoid_rewrite lookup_insert in H. inv H.
        set_solver.
      }
      {
        setoid_rewrite lookup_insert_ne in H; auto.
        right. right.
        do 3 eexists. split; eassumption.
      }
  }
Qed.

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
      inv e. by setoid_rewrite lookup_insert.
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
      split. setoid_rewrite lookup_insert. reflexivity. assumption.
    }
    {
      left. right. right.
      do 3 eexists.
      split. setoid_rewrite lookup_insert_ne. 2: exact n.
      eassumption. assumption.
    }
  }
Qed.

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
      inv e. setoid_rewrite lookup_insert in H. inv H.
      right. right. exists x, x0, (s :: x1). split.
      assumption.
      simpl. set_solver.
    }
    {
      setoid_rewrite lookup_insert_ne in H; auto.
      right. right. exists x, x0, x1. split; assumption.
    }
  }
Qed.

Definition isUsedPool (ι : PID) (Π : ProcessPool) :=
  Π !! ι <> None \/
  (exists ι' p, Π !! ι' = Some p /\ ι ∈ (usedPIDsProc p)).

(* In this definition O is used for observed PIDs - these can be assumed
   to have associated processes that consume the signals sent to these PIDs.
   This is exploited in the bisimulation-based program equivalence definitions
   which check the communication on these PIDs *)
Reserved Notation "n -[ a | ι ]ₙ-> n' 'with' O" (at level 50).
Inductive interProcessStep (O : gset PID) : Node -> Action -> PID -> Node -> Prop :=
(** sending any signal *)
| n_send p p' ether prs (ι ι' : PID) t :
  p -⌈ASend ι ι' t⌉-> p'
->
  (ether, ι ↦ p ∥ prs) -[ASend ι ι' t | ι]ₙ->  (etherAdd ι ι' t ether, ι ↦ p' ∥ prs) with O

(** This leads to the loss of determinism: *)
(** arrial of any signal *)
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
  create_result (IApp v1) l [] = Some (r, eff) ->
  p -⌈ASpawn ι' v1 v2 link_flag⌉-> p'
->
  (ether, ι ↦ p ∥ Π) -[ASpawn ι' v1 v2 link_flag | ι]ₙ-> (ether, ι' ↦ inl ([], r, emptyBox, if link_flag then {[ι]} else ∅, false) ∥ ι ↦ p' ∥ Π) with O

(* (** Process termination, no more notifyable links *)
| n_terminate ether ι Π :
  (ether, ι ↦ inr [] ∥ Π) -[ADestroy | ι]ₙ-> (ether, Π -- ι) *)

where "n -[ a | ι ]ₙ-> n' 'with' O" := (interProcessStep O n a ι n').


Definition allPIDsEther (eth : Ether) : gset PID :=
  flat_union (fun '((ιs, ιd), sigs) => {[ιs; ιd]} ∪ flat_union usedPIDsSignal sigs) (map_to_list eth).
Definition allPIDsPool (Π : ProcessPool) : gset PID :=
  flat_union (fun '(ι, proc) => {[ι]} ∪ usedPIDsProc proc) (map_to_list Π).

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

(* ONLY keys are symmetrically replaced  *)
Definition renamePIDPool (p p' : PID) (Π : ProcessPool) : ProcessPool :=
  kmap (renamePIDPID_sym p p') (renamePIDProc p p' <$> Π).

Notation "e .[ x ⇔ y ]ₚₚ" := (renamePIDPool x y e) (at level 2, left associativity).

(* ONLY keys are symmetrically replaced  *)
Definition renamePIDEther (p p' : PID) (eth : Ether) : Ether :=
  kmap (prod_map (renamePIDPID_sym p p') (renamePIDPID_sym p p'))
    ((map (renamePIDSignal p p')) <$> eth).

Notation "e .[ x ⇔ y ]ₑ" := (renamePIDEther x y e) (at level 2, left associativity).
