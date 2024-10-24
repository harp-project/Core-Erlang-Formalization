From CoreErlang.Equivalence Require Export BasicTactics.
Require Export stdpp.list.

(**
* foldl_ext
*)

(**
NOTES:  Maybe place this in CoreErlang/Basics
*)



Lemma foldl_ext :
  forall
    (A B : Type)
    (f1 f2 : A -> B -> A)
    (x1 x2 : A)
    (l1 l2 : list B),
      (forall (a : A) (b : B), f1 a b = f2 a b)
  ->  l1 = l2
  ->  x1 = x2
  ->  fold_left f1 l1 x1
  =   fold_left f2 l2 x2.
Proof.
  intros A B f1 f2 x1 x2 l1 l2 Hf Hl Hx.
  rewrite Hl, Hx.
  clear Hl Hx l1 x1.
  rename l2 into l.
  rename x2 into x.
  revert x.
  induction l as [| b l IHl]; intros; simpl.
  - reflexivity.
  - by rewrite Hf, IHl.
Qed.