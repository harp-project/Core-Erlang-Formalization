From CoreErlang.Equivalence Require Export Basics.
From CoreErlang.FrameStack Require Export SubstSemantics.

Import SubstSemantics.

(**
* scope_vl_succ
* scope_vl_succ_id
*)

(**
NOTES:  Maybe place this in CoreFrameStack/Scoping! or into FrameStack
*)



Theorem scope_vl_succ :
  forall A i vl (f : A -> Val),
      (∀ i : nat, i < length vl → VALCLOSED (nth i (map f vl) VNil))
  ->  (S i < S (length vl) → VALCLOSED (nth i (map f vl) VNil)).
Proof.
  intros A i vl f Hvl.
  specialize (Hvl i).
  intros Hsucc_lt.
  pose proof Nat.succ_lt_mono 
    as Hmono_succ_lt.
  specialize (Hmono_succ_lt i (base.length vl)).
  destruct Hmono_succ_lt
    as [Hto_succ_lt Hfrom_succ_lt].
  clear Hto_succ_lt.
  apply Hfrom_succ_lt
    in Hsucc_lt 
    as Hlt.
  clear Hfrom_succ_lt Hsucc_lt.
  apply Hvl in Hlt.
  clear Hvl.
  rename Hlt into Hvl.
  exact Hvl.
Qed.






Theorem scope_vl_succ_id :
  forall i vl,
      (∀ i : nat, i < length vl → VALCLOSED (nth i vl VNil))
  ->  (S i < S (length vl) → VALCLOSED (nth i vl VNil)).
Proof.
  intros i vl Hvl.
  assert (map id vl = vl).
  {
    apply Basics.map_id.
  }
  remember
    (base.length vl)
    as _n.
  rewrite <- H.
  rewrite <- H in Hvl.
  rewrite Heq_n in *.
  clear Heq_n _n H.
  pose proof scope_vl_succ Val i vl id Hvl.
  assumption.
Qed.