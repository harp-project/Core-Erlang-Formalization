From CoreErlang.Concurrent Require Export ProcessSemantics.
From stdpp Require Export base fin_maps gmap.

Import ListNotations.

Theorem Signal_eq_dec (s s' : Signal) : {s = s'} + {s <> s'}.
Proof. decide equality; try apply Val_eq_dec; try apply Nat.eq_dec. decide equality. Qed.

(* Definition update {T : Type} (pid : PID) (p : T) (n : PID -> T) : PID -> T :=
  fun ι => if Nat.eqb pid ι then p else n ι. *)


(*
Definition Ether : Set := gmap PID (gmap PID (list Signal)).

Definition option_lookup {K V} {H : EqDecision K} {H0 : Countable K} (m : option (gmap K V)) (i : K) : option V :=
  match m with
  | None => None
  | Some m => m !! i
  end.

Definition renamePIDEther (p p' : PID) (eth : Ether) : Ether :=
  ((fmap (fmap (map renamePIDSignal)) eth)).

Notation "e .[ x ⇔ y ]ₑ" := (renamePIDEther x y e) (at level 2).


*)

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
Local Goal (<[1:=inl ([], RValSeq [VNil], ([], []), [], false)]>∅ : ProcessPool) !! 1 <> None.
Proof.
  intro. inv H.
Qed.

Notation "pid ↦ p ∥ n" := (@insert PID Process ProcessPool _ pid p n) (at level 32, right associativity).
Notation "n -- pid" := (delete pid n) (at level 31, left associativity).

Definition Node : Set := Ether * ProcessPool.
Local Goal (<[1:=inl ([], RValSeq [VNil], ([], []), [], false)]>∅ -- 1 : ProcessPool) = ∅.
Proof. cbn. reflexivity. Qed.


(* Notation "pid ↦ p ∥ n" := (update pid (Some p) n) (at level 32, right associativity).
Notation "n -- pid" := (update pid None n) (at level 31, left associativity).
Lemma update_same : forall T ι (p p' : T) Π, update ι p (update ι p' Π) = update ι p Π.
Proof.
  intros. unfold update. extensionality ι'.
  break_match_goal; auto.
Qed.
Corollary par_same :  forall T ι (p p' : T) Π, ι ↦ p ∥ ι ↦ p' ∥ Π = ι ↦ p ∥ Π.
Proof.
  intros. apply update_same.
Qed.

Lemma update_this :
  forall T ι (p : T) Π,
    update ι p Π ι = p.
Proof.
  intros. unfold update.
  now rewrite Nat.eqb_refl.
Qed.

Lemma update_next :
  forall T ι ι' (p' : T) Π, ι' <> ι ->
    update ι' p' Π ι = Π ι.
Proof.
  intros. unfold update.
  apply Nat.eqb_neq in H. now rewrite H.
Qed.


Lemma update_swap : forall T ι ι' (p p' : T) Π, ι <> ι' ->
   update ι p (update ι' p' Π) = update ι' p' (update ι p Π).
Proof.
  intros. unfold update. extensionality ι''.
  break_match_goal; auto.
  subst. break_match_goal; auto.
  apply Nat.eqb_eq in Heqb0. apply Nat.eqb_eq in Heqb. congruence.
Qed.
Corollary par_swap :  forall ι ι' (p p' : (option Process)) Π, ι <> ι' ->
   @update (option Process) ι p (update ι' p' Π) = update ι' p' (update ι p Π).
Proof.
  intros. now apply update_swap.
Qed.
Lemma nullpool_remove : forall ι, nullpool -- ι = nullpool.
Proof.
  intros. extensionality ι'.
  unfold update. break_match_goal; auto.
Qed. *)

Definition etherAdd (source dest : PID) (m : Signal) (n : Ether) : Ether :=
  (* update source (update dest (n source dest ++ [m]) (n source) ) n *)
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

(* Theorem update_noop :
  forall T x (xval : T) n, n x = xval -> update x xval n = n.
Proof.
  intros. extensionality y.
  unfold update. break_match_goal.
  apply Nat.eqb_eq in Heqb. now subst.
  reflexivity.
Qed.*)



Lemma etherPop_greater :
  forall ι ether s ι' ether', etherPop ι ι' ether = Some (s, ether') ->
  forall ι'' ι''' s', etherPop ι ι' (etherAdd ι'' ι''' s' ether) = Some (s, etherAdd ι'' ι''' s' ether').
Proof.
  intros. unfold etherPop, etherAdd in *.
  break_match_hyp.
  * destruct (ether !! (ι'', ι''')) eqn:D2; cbn.
    destruct (decide ((ι'', ι''') = (ι, ι'))) as [EQ | EQ];
    [ inv EQ;
      setoid_rewrite lookup_insert; destruct l0; simpl; try congruence;
      destruct l; try congruence; inv H; setoid_rewrite lookup_insert;
      rewrite Heqo in D2; inv D2; do 2 f_equal;
      now setoid_rewrite insert_insert
    | ].
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

Corollary etherAdd_swap :
  forall ether ιs1 ιd1 m1 ιs2 ιd2 m2, ιs1 <> ιs2 ->
    etherAdd ιs1 ιd1 m1 (etherAdd ιs2 ιd2 m2 ether) =
    etherAdd ιs2 ιd2 m2 (etherAdd ιs1 ιd1 m1 ether).
Proof.
  intros. unfold etherAdd.
  destruct (ether !! _) eqn:D1; break_match_goal.
  all: (* for some reason, normal rewrite fails *)
    setoid_rewrite lookup_insert_ne in Heqo; [|intro D; inv D; congruence];
    setoid_rewrite Heqo;
    setoid_rewrite lookup_insert_ne; [|intro D; inv D; congruence];
    setoid_rewrite D1;
    setoid_rewrite Heqo;
    apply insert_commute; intro D; inv D; congruence.
Qed.

(* If we only consider things in the ether: *)
Definition isTargetedEther (ι : PID) (n : Ether) : Prop :=
  (* exists ι', n !! (ι', ι) <> Some [] /\ n !! (ι', ι) <> None. *)
  (* TODO: would this be easier: exists ι x l, n !! (ι', ι) = Some (x::l)? *)
(*                  ^------- only the target is considered, not the source *)
  (* exists ι' x l, n !! (ι', ι) = Some (x::l) <- NOTE: this is the exact definition, but we strenghten it to gain usability *)
  (* We consider `Some []` in the ether as used *)
  exists ι' l, n !! (ι', ι) = Some l.

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
        setoid_rewrite H in H1. inv H1.
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
        intro X. inv X. congruence.
      }
    * setoid_rewrite lookup_insert_ne in H.
      {
        right. left. eexists. exact H.
      }
      {
        intro X. inv X. congruence.
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
      inv e. setoid_rewrite H in H2. inv H2. simpl in H1.
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

Reserved Notation "n -[ a | ι ]ₙ-> n' 'with' O" (at level 50).
Inductive nodeSemantics (O : gset PID) : Node -> Action -> PID -> Node -> Prop :=
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

(* TODO: link sent to non-existing process triggers exit, messages should be discarded when sent to non-existing process *)


(** internal actions *)
| n_other p p' a Π (ι : PID) ether:
  p -⌈a⌉-> p' ->
  (a = τ \/ a = ASelf ι \/ a = ε)
->
   (ether, ι ↦ p ∥ Π) -[a| ι]ₙ-> (ether, ι ↦ p' ∥ Π) with O

(** spawning processes *)
| n_spawn Π (p p' : Process) v1 v2 l ι ι' ether r eff:
  mk_list v2 = Some l ->
  (* (ι ↦ p ∥ Π) !! ι' = None -> *)
  (* ι' ∉ dom Π -> *)
  ι' ∉ O -> (* can't spawn on outside interface/observable PIDs *)
  ι' <> ι ->
  (* NOTE: these two are a bit restricted. We do not model systems that use
     PIDs before they are spawned. PIDs currently in use cannot be spawned
     (i.e., if they appear either as a source or target of a floating message,
     inside a floating message, process, or they are associated with a process). *)
  ~isUsedPool ι' Π ->
  ~appearsEther ι' ether -> (* We can't model spawning such processes that receive
                         already floating messages from the ether. *)
  create_result (IApp v1) l [] = Some (r, eff) ->
  p -⌈ASpawn ι' v1 v2⌉-> p'
->
  (ether, ι ↦ p ∥ Π) -[ASpawn ι' v1 v2 | ι]ₙ-> (ether, ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π) with O

(* (** Process termination, no more notifyable links *)
| n_terminate ether ι Π :
  (ether, ι ↦ inr [] ∥ Π) -[ADestroy | ι]ₙ-> (ether, Π -- ι) *)

where "n -[ a | ι ]ₙ-> n' 'with' O" := (nodeSemantics O n a ι n').

