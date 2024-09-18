From CoreErlang.TMP.Tactics Require Export Params0.
From CoreErlang.TMP.Tactics Require Export Params1.
From CoreErlang.TMP.Tactics Require Export ParamsN.
From CoreErlang.TMP.Tactics Require Export Name.
From CoreErlang.TMP.Tactics Require Export Transform.
Require Export stdpp.list.



(** NOTES:
* SUGGESTION:
  - Maybe place this in CoreErlang/Basics
*)



(** STRUCTURE:
* foldl_ext     [NotUsed]
*)



(** NOTES [NotUsed]
* FULL NAME:
  - Fold Left Extension
* FUNCTION:
  - Same as foldr_ext but with fold_left
  - States the extensionality property of the left fold function
  - Asserts that if two functions are pointwise equal,
    then the results of folding these functions over a list are also equal
* USING:
  - /
* USED AT:
  - /
* HISTORY:
  - Created for subst_env_empty at ELetRec for rem_env_keys,
    but it's no longer necessary
* SUGGESTION:
  - rewrite fold_left to fold_right at rem_env_keys
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
  itr - A B f1 f2 x1 x2 l1 l2 Hf Hl Hx.
  cwr - Hl Hx.
  clr - l1 x1.
  ren - l x: l2 x2.
  rev - x.
  ind - l: [| b l IHf]; itr; smp.
  - rfl.
  - bwr - Hf IHf.
Qed.