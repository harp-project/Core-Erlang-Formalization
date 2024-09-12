From CoreErlang.TMP Require Export BasicTactics.
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
  int A B f1 f2 x1 x2 l1 l2 Hf Hl Hx.
  rwr Hl Hx.
  clr Hl Hx l1 x1.
  ren l x <- l2 x2.
  rev x.
  ind l as [| b l IHf]; int; smp.
  - rfl.
  - by rwr Hf IHf.
Qed.
