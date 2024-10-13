From CoreErlang.TMP.Tactics Require Export Params0.
From CoreErlang.TMP.Tactics Require Export Params1.
From CoreErlang.TMP.Tactics Require Export ParamsN.
From CoreErlang.TMP.Tactics Require Export Name.
From CoreErlang.TMP.Tactics Require Export Transform.
From CoreErlang Require Export Basics.
Require Export stdpp.list.



(** STRUCTURE:
* Tactics
* Lemmas
  - foldl_ext     [NotUsed]
*)



(** NOTES:
* SUGGESTION:
  - Maybe place this in CoreErlang/Basics
*)












Section Basics_Tactics.



  Ltac des_for := destruct_foralls.
  Ltac des_hyp := destruct_hyps.
  Ltac des_boo := destruct_bools.



End Basics_Tactics.


















Section Basics_Lemmas.



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
    (* #1 Intro: intro/subst/rename/revert *)
    itr - A B f1 f2 x1 x2 l1 l2 Hf Hl Hx.
    sbt.
    ren - l x: l2 x2.
    rev - x.
    (* #2 Induction: induction/intro/simple/rewrite *)
    ind - l as [| b l IHf]:> itr; smp.
    bwr - Hf IHf.
  Qed.



End Basics_Lemmas.