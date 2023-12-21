From CoreErlang.Concurrent Require Export ProcessSemantics.
From stdpp Require Export base fin_maps gmap.

Import ListNotations.

Theorem Signal_eq_dec (s s' : Signal) : {s = s'} + {s <> s'}.
Proof. decide equality; try apply Val_eq_dec; try apply Nat.eq_dec. decide equality. Qed.

(* Definition update {T : Type} (pid : PID) (p : T) (n : PID -> T) : PID -> T :=
  fun ι => if Nat.eqb pid ι then p else n ι. *)

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
Definition isUsedEther (ι : PID) (n : Ether) : Prop :=
  (* exists ι', n !! (ι', ι) <> Some [] /\ n !! (ι', ι) <> None. *)
  (* TODO: would this be easier: exists ι x l, n !! (ι', ι) = Some (x::l)? *)
(*                  ^------- only the target is considered, not the source *)
  exists ι' x l, n !! (ι', ι) = Some (x::l).

Lemma isUsedEther_etherAdd :
  forall ether ι ι' ι'' s,
    isUsedEther ι ether ->
    isUsedEther ι (etherAdd ι' ι'' s ether).
Proof.
  intros. unfold etherAdd, isUsedEther. destruct H as [ι'0 [x [l H]]].
  exists ι'0. repeat break_match_goal; eqb_to_eq; subst; auto.
  all: destruct (decide ((ι'0, ι) = (ι', ι''))); try rewrite e.
  all: try setoid_rewrite lookup_insert; auto.
  all: try setoid_rewrite lookup_insert_ne; auto.
  all: do 2 eexists; try reflexivity; try eassumption.
  inv e. rewrite H in Heqo. now inv Heqo.
Qed.

Lemma isUsedEther_etherAdd_rev :
  forall ether ι ι' ι'' s,
    isUsedEther ι (etherAdd ι' ι'' s ether) ->
    ι'' <> ι ->
    isUsedEther ι ether.
Proof.
  intros. unfold etherAdd in *. unfold isUsedEther in *.
  destruct H as [ι'0 [x [l H]]].
  destruct (ether !! (ι', ι'')) eqn:Eq; simpl in *.
  all: setoid_rewrite lookup_insert_ne in H; [|intro X; inv X; congruence].
  * do 3 eexists. eassumption.
  * do 3 eexists. eassumption.
Qed.

Lemma isUsedEther_etherPop :
  forall {ether ι ι' ι'' s ether'},
    isUsedEther ι ether ->
    etherPop ι' ι'' ether = Some (s, ether') ->
    isUsedEther ι ether' \/ ι = ι''.
Proof.
  intros. destruct H as [ι'0 [x [l H]]].
  unfold etherPop in H0. break_match_hyp. 2: congruence.
  destruct l0; inv H0.
  destruct (Nat.eq_dec ι ι''); auto.
  left. exists ι'0.
  setoid_rewrite lookup_insert_ne; try split; auto.
  2: intro; congruence.
  do 2 eexists. eassumption.
Qed.

Lemma isUsedEther_etherPop_rev :
  forall {ether ι ι' ι'' s ether'},
    isUsedEther ι ether' ->
    etherPop ι' ι'' ether = Some (s, ether') ->
    isUsedEther ι ether.
Proof.
  intros. destruct H as [ι'0 [x [l H]]].
  unfold etherPop in H0. break_match_hyp. 2: congruence.
  destruct l0. congruence. inv H0.
  unfold isUsedEther.
  destruct (decide ((ι', ι'') = (ι'0, ι))); try inv e.
  * setoid_rewrite lookup_insert in H. inv H.
    exists ι'0. do 2 eexists. eassumption.
  * setoid_rewrite lookup_insert_ne in H. 2: auto.
    exists ι'0. do 2 eexists. eassumption.
Qed.


Reserved Notation "n -[ a | ι ]ₙ-> n'" (at level 50).
Inductive nodeSemantics : Node -> Action -> PID -> Node -> Prop :=
(** sending any signal *)
| n_send p p' ether prs (ι ι' : PID) t :
  p -⌈ASend ι ι' t⌉-> p'
->
  (ether, ι ↦ p ∥ prs) -[ASend ι ι' t | ι]ₙ->  (etherAdd ι ι' t ether, ι ↦ p' ∥ prs)

(** This leads to the loss of determinism: *)
(** arrial of any signal *)
| n_arrive ι ι0 p p' ether ether' prs t:
  etherPop ι0 ι ether = Some (t, ether') ->
  p -⌈AArrive ι0 ι t⌉-> p' ->
  (ether, ι ↦ p ∥ prs) -[AArrive ι0 ι t | ι]ₙ-> (ether',
                                            ι ↦ p' ∥ prs)

(* TODO: link sent to non-existing process triggers exit, messages should be discarded when sent to non-existing process *)


(** internal actions *)
| n_other p p' a Π (ι : PID) ether:
  p -⌈a⌉-> p' ->
  (a = τ \/ a = ASelf ι \/ a = ε)
->
   (ether, ι ↦ p ∥ Π) -[a| ι]ₙ-> (ether, ι ↦ p' ∥ Π)

(** spawning processes *)
| n_spawn Π (p p' : Process) v1 v2 l ι ι' ether r eff:
  mk_list v2 = Some l ->
  (* (ι ↦ p ∥ Π) !! ι' = None -> *)
  ι' ∉ dom Π ->
  ι' <> ι ->
  ~isUsedEther ι' ether -> (* We can't model spawning such processes that receive
                         already floating messages from the ether. *)
  create_result (IApp v1) l [] = Some (r, eff) ->
  p -⌈ASpawn ι' v1 v2⌉-> p'
->
  (ether, ι ↦ p ∥ Π) -[ASpawn ι' v1 v2 | ι]ₙ-> (ether, ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π)

(* (** Process termination, no more notifyable links *)
| n_terminate ether ι Π :
  (ether, ι ↦ inr [] ∥ Π) -[ADestroy | ι]ₙ-> (ether, Π -- ι) *)

where "n -[ a | ι ]ₙ-> n'" := (nodeSemantics n a ι n').

