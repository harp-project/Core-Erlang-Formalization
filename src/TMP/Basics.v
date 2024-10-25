From CoreErlang.TMP.Tactics Require Export Params0.
From CoreErlang.TMP.Tactics Require Export Params1.
From CoreErlang.TMP.Tactics Require Export ParamsN.
From CoreErlang.TMP.Tactics Require Export Name.
From CoreErlang.TMP.Tactics Require Export Transform.
From CoreErlang Require Export Basics.
From CoreErlang.BigStep Require Export BigStep.
From CoreErlang.FrameStack Require Export SubstSemanticsLemmas.
Require Export stdpp.list.



(** STRUCTURE:
* Tactics
  - Destruct Foralls
    + des_for
  - FrameStack Step
    + do_framestack_step
    + do_framestack_transitive
    + framestack_step
* Lemmas
  - foldl_ext     [NotUsed]
*)



(** NOTES:
* SUGGESTION:
  - Maybe place this in CoreErlang/Basics
*)












(* Section Basics_Tactics. *)



  (* Destruct Foralls: *)



  Tactic Notation "des_for"
    :=
    destruct_foralls.

  Tactic Notation "des_for"
    "-"   ident(In1)
    ":"   ident(Io1)
    :=
    destruct_foralls;
    ren - In1:
          Io1.

  Tactic Notation "des_for"
    "-"   ident(In1) ident(In2)
    ":"   ident(Io1) ident(Io2)
    :=
    destruct_foralls;
    ren - In1 In2:
          Io1 Io2.

  Tactic Notation "des_for"
    "-"   ident(In1) ident(In2) ident(In3)
    ":"   ident(Io1) ident(Io2) ident(Io3)
    :=
    destruct_foralls;
    ren - In1 In2 In3:
          Io1 Io2 Io3.

  Tactic Notation "des_for"
    "-"   ident(In1) ident(In2) ident(In3) ident(In4)
    ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
    :=
    destruct_foralls;
    ren - In1 In2 In3 In4:
          Io1 Io2 Io3 Io4.

  Tactic Notation "des_for"
    "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
    ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
    :=
    destruct_foralls;
    ren - In1 In2 In3 In4 In5:
          Io1 Io2 Io3 Io4 Io5.

  Tactic Notation "des_for"
    "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
          ident(In6)
    ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
          ident(Io6)
    :=
    destruct_foralls;
    ren - In1 In2 In3 In4 In5 In6:
          Io1 Io2 Io3 Io4 Io5 Io6.

  Tactic Notation "des_for"
    "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
          ident(In6) ident(In7)
    ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
          ident(Io6) ident(Io7)
    :=
    destruct_foralls;
    ren - In1 In2 In3 In4 In5 In6 In7:
          Io1 Io2 Io3 Io4 Io5 Io6 Io7.

  Tactic Notation "des_for"
    "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
          ident(In6) ident(In7) ident(In8)
    ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
          ident(Io6) ident(Io7) ident(Io8)
    :=
    destruct_foralls;
    ren - In1 In2 In3 In4 In5 In6 In7 In8:
          Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8.

  Tactic Notation "des_for"
    "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
          ident(In6) ident(In7) ident(In8) ident(In9)
    ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
          ident(Io6) ident(Io7) ident(Io8) ident(Io9)
    :=
    destruct_foralls;
    ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
          Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9.

  Tactic Notation "des_for"
    "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
          ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
    ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
          ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
    :=
    destruct_foralls;
    ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
          Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10.






  (* FrameStack Step: *)



  Ltac do_framestack_step
    :=
    (econstructor;
    [ (constructor; auto + scope_solver + congruence)
    + (econstructor; constructor)
    + (econstructor;
      [ congruence
      | constructor ])
    | simpl ])
    + (cbn; constructor).



  Ltac do_framestack_transitive H
    :=
    eapply transitive_eval;
    [ eapply frame_indep_core in H;
      exact H
    | clear H;
      simpl ].



  Tactic Notation "framestack_step"
    :=
    repeat do_framestack_step.

  Tactic Notation "framestack_step"
    "-"   hyp(H)
    :=
    repeat do_framestack_step;
    (solve [exact H] + do_framestack_transitive H).

  Tactic Notation "framestack_step"
    "-"   hyp(H)
    "/"   ident(I1)
    :=
    repeat do_framestack_step;
    do_framestack_transitive H;
    clear I1.

  Tactic Notation "framestack_step"
    "-"   hyp(H)
    "/"   ident(I1) ident(I2)
    :=
    repeat do_framestack_step;
    do_framestack_transitive H;
    clear I1 I2.

  Tactic Notation "framestack_step"
    "-"   hyp(H)
    "/"   ident(I1) ident(I2) ident(I3)
    :=
    repeat do_framestack_step;
    do_framestack_transitive H;
    clear I1 I2 I3.

  Tactic Notation "framestack_step"
    "-"   hyp(H)
    "/"   ident(I1) ident(I2) ident(I3) ident(I4)
    :=
    repeat do_framestack_step;
    do_framestack_transitive H;
    clear I1 I2 I3 I4.

  Tactic Notation "framestack_step"
    "-"   hyp(H)
    "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
    :=
    repeat do_framestack_step;
    do_framestack_transitive H;
      clear I1 I2 I3 I4 I5.

  Tactic Notation "framestack_step"
    "-"   hyp(H)
    "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
          ident(I6)
    :=
    repeat do_framestack_step;
    do_framestack_transitive H;
    clear I1 I2 I3 I4 I5 I6.

  Tactic Notation "framestack_step"
    "-"   hyp(H)
    "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
          ident(I6) ident(I7)
    :=
    repeat do_framestack_step;
    do_framestack_transitive H;
    clear I1 I2 I3 I4 I5 I6 I7.

  Tactic Notation "framestack_step"
    "-"   hyp(H)
    "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
          ident(I6) ident(I7) ident(I8)
    :=
    repeat do_framestack_step;
    do_framestack_transitive H;
    clear I1 I2 I3 I4 I5 I6 I7 I8.

  Tactic Notation "framestack_step"
    "-"   hyp(H)
    "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
          ident(I6) ident(I7) ident(I8) ident(I9)
    :=
    repeat do_framestack_step;
    do_framestack_transitive H;
    clear I1 I2 I3 I4 I5 I6 I7 I8 I9.

  Tactic Notation "framestack_step"
    "-"   hyp(H)
    "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
          ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
    :=
    repeat do_framestack_step;
    do_framestack_transitive H;
    clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10.

  Tactic Notation "framestack_step"
    ":"   tactic(T)
    :=
    repeat do_framestack_step + T.

  Tactic Notation "framestack_step"
    ":"   tactic(T)
    "/"   ident(I1)
    :=
    repeat do_framestack_step + T;
    clear I1.

  Tactic Notation "framestack_step"
    ":"   tactic(T)
    "/"   ident(I1) ident(I2)
    :=
    repeat (do_framestack_step + T);
    clear I1 I2.

  Tactic Notation "framestack_step"
    ":"   tactic(T)
    "/"   ident(I1) ident(I2) ident(I3)
    :=
    repeat (do_framestack_step + T);
    clear I1 I2 I3.

  Tactic Notation "framestack_step"
    ":"   tactic(T)
    "/"   ident(I1) ident(I2) ident(I3) ident(I4)
    :=
    repeat (do_framestack_step + T);
    clear I1 I2 I3 I4.

  Tactic Notation "framestack_step"
    ":"   tactic(T)
    "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
    :=
    repeat (do_framestack_step + T);
    clear I1 I2 I3 I4 I5.



(* End Basics_Tactics. *)


















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