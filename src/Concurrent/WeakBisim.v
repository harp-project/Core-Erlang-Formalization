(**
  This file defines weak barbed bisimulation, and shows that strong barbed
  bisimulations are weak too.
*)

From CoreErlang Require Export Concurrent.StrongBisim.

Import ListNotations.

Definition isSilent (a : Action) : Prop :=
match a with
 | τ => True
 | _ => False
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
     (* NOTE: isSilent actions do not modify the ether *)
(*   (forall source dest,
      dest ∈ O ->
      exists B' l,
           Forall (isSilent ∘ fst) l
        /\ B -[l]ₙ->* B' with O
        /\ option_list_biforall Signal_eq (A.1 !! (source, dest)) (B'.1 !! (source, dest)) *)
      (forall source dest,
      dest ∈ O ->
      option_list_biforall Signal_eq (A.1 !! (source, dest)) (B.1 !! (source, dest))
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
(*   (forall source dest,
      dest ∈ O ->
      option_list_biforall Signal_eq (A.1 !! (source, dest)) (B.1 !! (source, dest))
      (* NOTE: this part could be adjusted based on the equivalence we are
               interested in *)) -> *)
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
  * intros. apply H2 in H. destruct H as [A' H]. destruct_hyps.
    exists A, A', A', [], []. split_and!; try by constructor.
    exact H. by apply IH.
Qed.
