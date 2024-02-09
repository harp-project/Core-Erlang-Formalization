From CoreErlang Require Export Concurrent.BarbedBisim.

Import ListNotations.

CoInductive strongBisim (O : gset PID) : (* nat -> *) Node -> Node -> Prop :=
(* | is_bisim_0 (A B : Node) : barbedBisim O 0 A B *)
| is_strong_bisim (A B : Node) :
  symClos (preCompatibleNodes O) A B ->
  ether_wf A.1 ->
  ether_wf B.1 ->
  (forall A' a ι,
      A -[a | ι]ₙ-> A' with O ->
        exists B',
          B -[a | ι]ₙ-> B' with O /\ strongBisim O (* n *) A' B') ->
  (forall source dest,
      dest ∈ O ->
      option_list_biforall Signal_eq (A.1 !! (source, dest)) (B.1 !! (source, dest))
      (* NOTE: this part could be adjusted based on the equivalence we are
               interested in *)) -> (*
         The condition above does not need to be duplicated since Signal_eq is
         symmetric.
               *)
  (forall B' a ι,
      B -[a | ι]ₙ-> B' with O ->
        exists A',
          A -[a | ι]ₙ-> A' with O /\ strongBisim O (* n *) A' B') ->
  strongBisim O (* (S n) *) A B
.

Notation "A ~ˢ B 'observing' O" := (strongBisim O A B) (at level 70).

