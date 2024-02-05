From CoreErlang Require Import Concurrent.BarbedBisim.

Import ListNotations.

CoInductive strongBisim (O : gset PID) : (* nat -> *) Node -> Node -> Prop :=
(* | is_bisim_0 (A B : Node) : barbedBisim O 0 A B *)
| is_strong_bisim (A B : Node) :
  symClos (preCompatibleNodes O) A B ->
  ether_wf A.1 ->
  ether_wf B.1 ->
  (forall A' a ι,
      A -[a | ι]ₙ-> A' with O ->
        exists B' l,
          B -[l]ₙ->* B' with O /\ barbedBisim O (* n *) A' B') ->
  (forall source dest,
      dest ∈ O ->
      exists source' l B',
      B -[l]ₙ->* B' with O /\
      option_list_biforall Signal_eq (A.1 !! (source, dest)) (B'.1 !! (source', dest))
      (* NOTE: this part could be adjusted based on the equivalence we are
               interested in *)) ->
  (forall B' a ι,
      B -[a | ι]ₙ-> B' with O ->
        exists A' l,
          A -[l]ₙ->* A' with O /\ barbedBisim O (* n *) A' B') ->
  (forall source dest,
      dest ∈ O ->
      exists source' l A',
      A -[l]ₙ->* A' with O /\
      option_list_biforall Signal_eq (B.1 !! (source, dest)) (A'.1 !! (source', dest))
      (* NOTE: this part could be adjusted based on the equivalence we are
               interested in *)) ->
  barbedBisim O (* (S n) *) A B
.

Notation "A ~ B 'observing' O" := (* (forall n, barbedBisim O n A B) (at level 70).