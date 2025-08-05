From CoreErlang Require Export Concurrent.BarbedBisim.

CoInductive barbedBisimAlt (O : gset PID) : (* nat -> *) Node -> Node -> Prop :=
| is_bisim (A B : Node) :
  (forall A' a ι,
      A -[a | ι]ₙ-> A' with O ->
        exists B' l,
          B -[l]ₙ->* B' with O /\ barbedBisimAlt O (* n *) A' B') ->
  (forall source dest,
      dest ∈ O ->
      exists source',
      option_list_biforall Signal_eq (A.1 !! (source, dest)) (B.1 !! (source', dest))
      (* NOTE: this part could be adjusted based on the equivalence we are
               interested in *)) ->
  (forall B' a ι,
      B -[a | ι]ₙ-> B' with O ->
        exists A' l,
          A -[l]ₙ->* A' with O /\ barbedBisimAlt O (* n *) A' B') ->
  (forall source dest,
      dest ∈ O ->
      exists source',
      option_list_biforall Signal_eq (B.1 !! (source, dest)) (A.1 !! (source', dest))
      (* NOTE: this part could be adjusted based on the equivalence we are
               interested in *)) ->
  barbedBisimAlt O (* (S n) *) A B
.

Notation "A ~~ B 'observing' O" := (barbedBisimAlt O (* n *) A B) (at level 70).

(* Lemma barbedBisim_barbedBisimAlt_1 :
  forall O A B, A ~ B observing O -> A ~~ B observing O.
Proof.
  cofix IH.
  intros. destruct H.
  constructor.
  - intros. apply H in H3 as [B' [l [H3_1 H3_2]]].
    do 2 eexists. split. exact H3_1. apply IH. exact H3_2.
  - intros. apply (H0 source) in H3 as H3'. destruct H3' as [source' [l [B' [D1 bif1]]]].
    
  - intros. apply H1 in H3 as [A' [l [H3_1 H3_2]]].
    do 2 eexists. split. exact H3_1. apply IH. exact H3_2.
  - intros. eapply H2 in H3. destruct H3.
    exists x, [], A. split. constructor.
    eassumption.
Qed. *)

Lemma barbedBisim_barbedBisimAlt_2 :
  forall O A B, A ~~ B observing O -> A ~ B observing O.
Proof.
  cofix IH.
  intros. destruct H.
  constructor.
  - intros. apply H in H3 as [B' [l [H3_1 H3_2]]].
    do 2 eexists. split. exact H3_1. apply IH. exact H3_2.
  - intros. eapply H0 in H3. destruct H3.
    exists x, [], B. split. constructor.
    eassumption.
  - intros. apply H1 in H3 as [A' [l [H3_1 H3_2]]].
    do 2 eexists. split. exact H3_1. apply IH. exact H3_2.
  - intros. eapply H2 in H3. destruct H3.
    exists x, [], A. split. constructor.
    eassumption.
Qed.

Open Scope string_scope.

(** node 1: *)
(** process with PID 0 *)
Definition exp1_0 : Redex :=

(** process with PID 1 *)
Definition exp1_1 : Redex :=


(** node 2: *)
(** process with PID 0 *)
Definition exp2 : Redex :=
  ESeq 
     (ESeq (ECall (˝VLit "erlang") (˝VLit "!") [˝VPid 0;˝VNil])
           (ECall (˝VLit "erlang") (˝VLit "!") [˝VPid 1; (˝VLit 1%Z)]))
     (EPrimOp "remove_message" []).



Goal
  

