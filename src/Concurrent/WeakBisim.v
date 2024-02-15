From CoreErlang Require Export Concurrent.StrongBisim.

Import ListNotations.

Definition isSilent (a : Action) : Prop :=
match a with
 | ASend sender receiver t => False
 | AArrive sender receiver t => False
 | ASelf ι => False
 | ASpawn ι t1 t2 => False
 | τ => True
 | ε => False
end.


CoInductive weakBisim (O : gset PID) : (* nat -> *) Node -> Node -> Prop :=
(* | is_bisim_0 (A B : Node) : barbedBisim O 0 A B *)
| is_strong_bisim (A B : Node) :
  (* symClos (preCompatibleNodes O) A B ->
  ether_wf A.1 ->
  ether_wf B.1 -> *)
  (forall A' a ι,
      A -[a | ι]ₙ-> A' with O ->
        exists B' B'' B''' l₁ l₂,
             Forall (isSilent ∘ fst) l₁
          /\ Forall (isSilent ∘ fst) l₂
          /\ B -[l₁]ₙ->* B' with O
          /\ B' -[a | ι]ₙ-> B'' with O 
          /\ B'' -[l₂]ₙ->* B''' with O
          /\ weakBisim O (* n *) A' B''') ->
  (forall source dest,
      dest ∈ O ->
      exists B' l,
           Forall (isSilent ∘ fst) l
        /\ B -[l]ₙ->* B' with O
        /\ option_list_biforall Signal_eq (A.1 !! (source, dest)) (B'.1 !! (source, dest))
      (* NOTE: this part could be adjusted based on the equivalence we are
               interested in *)) ->
  (forall B' a ι,
      B -[a | ι]ₙ-> B' with O ->
        exists A' A'' A''' l₁ l₂,
             Forall (isSilent ∘ fst) l₁
          /\ Forall (isSilent ∘ fst) l₂
          /\ A -[l₁]ₙ->* A' with O
          /\ A' -[a | ι]ₙ-> A'' with O 
          /\ A'' -[l₂]ₙ->* A''' with O
          /\ weakBisim O (* n *) A''' B') ->
  (forall source dest,
      dest ∈ O ->
      exists A' l,
           Forall (isSilent ∘ fst) l
        /\ A -[l]ₙ->* A' with O
        /\ option_list_biforall Signal_eq (B.1 !! (source, dest)) (A'.1 !! (source, dest))
      (* NOTE: this part could be adjusted based on the equivalence we are
               interested in *)) ->
  weakBisim O (* (S n) *) A B
.

Notation "A ~ʷ B 'observing' O" := (weakBisim O A B) (at level 70).

Theorem strong_is_weak :
  forall O A B, A ~ˢ B observing O -> A ~ʷ B observing O.
Proof.
  cofix IH. intros.
  inv H; constructor; auto.
  * intros. apply H0 in H. destruct H as [B' H]. destruct_hyps.
    exists B, B', B', [], []. split_and!; try by constructor.
    exact H. by apply IH.
  * intros. exists B, []. split_and!; try by constructor. by apply H1.
  * intros. apply H2 in H. destruct H as [A' H]. destruct_hyps.
    exists A, A', A', [], []. split_and!; try by constructor.
    exact H. by apply IH.
  * intros. exists A, []. split_and!; try by constructor.
    specialize (H1 source _ H). clear-H1.
    destruct (A.1 !! _) eqn:P; destruct (B.1 !! _) eqn:P2; simpl in *.
    2-3: congruence. 2: trivial.
    clear -H1.
    apply biforall_length in H1 as HL.
    apply forall_biforall with (d1 := SLink) (d2 := SLink). by auto.
    intros.
    apply biforall_forall with (d1 := SLink) (d2 := SLink) (i := i) in H1.
    2: by lia.
    by apply Signal_eq_sym.
Qed.
