From CoreErlang.Concurrent Require Export ProcessSemantics.

Import ListNotations.

Theorem Signal_eq_dec (s s' : Signal) : {s = s'} + {s <> s'}.
Proof. decide equality; try apply Val_eq_dec; try apply Nat.eq_dec. decide equality. Qed.

Definition update {T : Type} (pid : PID) (p : T) (n : PID -> T) : PID -> T :=
  fun ι => if Nat.eqb pid ι then p else n ι.

(** This representation assures that messages sent from the same process,
    are delivered in the same order *)
Definition Ether : Set := PID -> PID -> list Signal.
Definition etherPop (source dest : PID) (n : Ether) :
  option (Signal * Ether) :=
match n source dest with
| [] => None
| x::xs => Some (x, update source (update dest xs (n source)) n)
end.

Definition ProcessPool : Set := (PID -> option Process).
Definition Node : Set := Ether * ProcessPool.

Definition nullpool : ProcessPool := fun ι => None.

Notation "pid ↦ p ∥ n" := (update pid (Some p) n) (at level 32, right associativity).
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
Qed.

Definition etherAdd (source dest : PID) (m : Signal) (n : Ether) : Ether :=
  update source (update dest (n source dest ++ [m]) (n source) ) n.

Theorem update_noop :
  forall T x (xval : T) n, n x = xval -> update x xval n = n.
Proof.
  intros. extensionality y.
  unfold update. break_match_goal.
  apply Nat.eqb_eq in Heqb. now subst.
  reflexivity.
Qed.

Lemma etherPop_greater :
  forall ι ether s ι' ether', etherPop ι ι' ether = Some (s, ether') ->
  forall ι'' ι''' s', etherPop ι ι' (etherAdd ι'' ι''' s' ether) = Some (s, etherAdd ι'' ι''' s' ether').
Proof.
  intros. unfold etherPop, etherAdd, update in *.
  destruct (Nat.eqb ι'' ι) eqn:Eq1; eqb_to_eq; subst.
  * break_match_hyp; eqb_to_eq; subst; simpl. congruence.
    inversion H.
    break_match_goal.
    - break_match_hyp.
      destruct (ether ι ι'''); simpl in Heql0; inversion Heql0.
      inversion Heql0.
    - break_match_hyp; eqb_to_eq; subst.
      + rewrite Heql in Heql0. simpl in Heql0. inversion Heql0.
        do 3 f_equal.
        extensionality ι0. break_match_goal; eqb_to_eq; subst; auto.
        extensionality ι0'. break_match_goal; eqb_to_eq; subst; auto.
        now do 2 rewrite Nat.eqb_refl.
        rewrite Nat.eqb_refl. apply Nat.eqb_neq in Heqb. now rewrite Heqb.
      + inversion Heql0.
        do 3 f_equal.
        extensionality ι0. break_match_goal; eqb_to_eq; subst; auto.
        extensionality ι0'. break_match_goal; eqb_to_eq; subst; auto.
        do 2 rewrite Nat.eqb_refl. apply Nat.eqb_neq in Heqb. now rewrite Heqb.
        rewrite Nat.eqb_refl. apply not_eq_sym in Heqb.
        apply Nat.eqb_neq in Heqb. rewrite Heqb.
        apply Nat.eqb_neq in Heqb0. now rewrite Heqb0.
  * break_match_hyp; eqb_to_eq; subst; simpl. congruence.
    inversion H.
    break_match_goal.
    - do 3 f_equal.
      extensionality ι0. break_match_goal; eqb_to_eq; subst; auto.
      congruence. congruence.
    - do 3 f_equal.
      extensionality ι0. break_match_goal; eqb_to_eq; subst; auto.
      extensionality ι0'. break_match_goal; eqb_to_eq; subst; auto.
      apply not_eq_sym in Heqb.
      apply Nat.eqb_neq in Heqb. rewrite Heqb. now rewrite Nat.eqb_refl.
      apply not_eq_sym in Heqb.
      apply Nat.eqb_neq in Heqb. rewrite Heqb.
      apply Nat.eqb_neq in Heqb0. now rewrite Heqb0.
Qed.

Corollary etherAdd_swap :
  forall ether ιs1 ιd1 m1 ιs2 ιd2 m2, ιs1 <> ιs2 ->
    etherAdd ιs1 ιd1 m1 (etherAdd ιs2 ιd2 m2 ether) =
    etherAdd ιs2 ιd2 m2 (etherAdd ιs1 ιd1 m1 ether).
Proof.
  intros. unfold etherAdd.
  rewrite update_swap; auto.
  f_equal.
  all: unfold update; extensionality ι; repeat break_match_goal; eqb_to_eq; subst.
  all: auto; try congruence.
Qed.

(* If we only consider things in the ether: *)
Definition isUsedEther (ι : PID) (n : Ether) : Prop :=
  exists ι', (* (n ι ι' <> [])%type \/  *)(n ι' ι <> [])%type.
(*                  ^------- only the target is considered, not the source *)

Lemma isUsedEther_etherAdd :
  forall ether ι ι' ι'' s,
    isUsedEther ι ether ->
    isUsedEther ι (etherAdd ι' ι'' s ether).
Proof.
  intros. unfold etherAdd, update. unfold isUsedEther. destruct H as [ι'0 H].
  * exists ι'0. repeat break_match_goal; eqb_to_eq; subst; auto.
    intro H0; apply length_zero_iff_nil in H0; rewrite app_length in H0.
    simpl in H0; lia.
Qed.

Lemma isUsedEther_etherAdd_rev :
  forall ether ι ι' ι'' s,
    isUsedEther ι (etherAdd ι' ι'' s ether) ->
    ι'' <> ι ->
    isUsedEther ι ether.
Proof.
  intros. unfold etherAdd, update in *. unfold isUsedEther.
  destruct H as [ι'0 H].
  repeat break_match_hyp; eqb_to_eq; subst; eexists; eauto.
  Unshelve. exact ι.
Qed.

Lemma isUsedEther_etherPop :
  forall {ether ι ι' ι'' s ether'},
    isUsedEther ι ether ->
    etherPop ι' ι'' ether = Some (s, ether') ->
    isUsedEther ι ether' \/ ι = ι''.
Proof.
  intros. destruct H as [ι'0 H].
  unfold etherPop in H0. break_match_hyp. congruence.
  inv H0. unfold update.
  destruct (Nat.eq_dec ι ι''); auto.
  left. exists ι'0. repeat break_match_goal; eqb_to_eq; subst; try congruence.
Qed.

Lemma isUsedEther_etherPop_rev :
  forall {ether ι ι' ι'' s ether'},
    isUsedEther ι ether' ->
    etherPop ι' ι'' ether = Some (s, ether') ->
    isUsedEther ι ether.
Proof.
  intros. destruct H as [ι'0 H].
  unfold etherPop in H0. break_match_hyp. congruence.
  unfold isUsedEther.
  inv H0. unfold update in *.
  repeat break_match_hyp; eqb_to_eq; subst; try congruence.
  all: eexists; eauto.
  now rewrite Heql.
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
  (ι ↦ p ∥ Π) ι' = None ->
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

