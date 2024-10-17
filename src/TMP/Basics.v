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
  - FrameStack Do End
    + fs_end
  - FrameStack Do Step
    + fs_stp
  - FrameStack Do Transitive
    + fs_trn
  - FrameStack Do Step & Transitive
    + fs_srn
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



  (* FrameStack Do Step: *)

  Ltac fs_stp_1
    :=
    econstructor;
    [ constructor; auto
    | simpl ].

  Ltac fs_stp_2
    :=
    econstructor;
    [ econstructor;
      [ congruence
      | constructor ]
    | simpl ].

  Ltac fs_stp :=
    fs_stp_1 +
    fs_stp_2.



  (* FrameStack Do End: *)

  Tactic Notation "fs_end"
    "-"   ident(Hstp)
    :=
    solve [exact Hstp].



  (* FrameStack Do Transitive: *)

  Tactic Notation "fs_trn"
    "-"   ident(Hstp)
    :=
    eapply transitive_eval;
    [ eapply frame_indep_core in Hstp;
      exact Hstp
    | clear Hstp;
      simpl ].

   Tactic Notation "fs_trn"
    "-"   ident(Hstp)
    "/"   ident(I1)
    :=
    eapply transitive_eval;
    [ eapply frame_indep_core in Hstp;
      exact Hstp
    | clear Hstp I1;
      simpl ].

   Tactic Notation "fs_trn"
    "-"   ident(Hstp)
    "/"   ident(I1) ident(I2)
    :=
    eapply transitive_eval;
    [ eapply frame_indep_core in Hstp;
      exact Hstp
    | clear Hstp I1 I2;
      simpl ].

   Tactic Notation "fs_trn"
    "-"   ident(Hstp)
    "/"   ident(I1) ident(I2) ident(I3)
    :=
    eapply transitive_eval;
    [ eapply frame_indep_core in Hstp;
      exact Hstp
    | clear Hstp I1 I2 I3;
      simpl ].

   Tactic Notation "fs_trn"
    "-"   ident(Hstp)
    "/"   ident(I1) ident(I2) ident(I3) ident(I4)
    :=
    eapply transitive_eval;
    [ eapply frame_indep_core in Hstp;
      exact Hstp
    | clear Hstp I1 I2 I3 I4;
      simpl ].

   Tactic Notation "fs_trn"
    "-"   ident(Hstp)
    "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
    :=
    eapply transitive_eval;
    [ eapply frame_indep_core in Hstp;
      exact Hstp
    | clear Hstp I1 I2 I3 I4 I5;
      simpl ].



  (* FrameStack Do Step & Transitive: *)

  Tactic Notation "fs_srn"
    "-"   ident(Hstp)
    "/"   ident(I1)
    :=
    fs_stp;
    eapply transitive_eval;
    [ eapply frame_indep_core in Hstp;
      exact Hstp
    | clear Hstp;
      simpl ].

  Tactic Notation "fs_srn"
    "-"   ident(Hstp)
    "/"   ident(I1)
    :=
    fs_stp;
    eapply transitive_eval;
    [ eapply frame_indep_core in Hstp;
      exact Hstp
    | clear Hstp I1;
      simpl ].

  Tactic Notation "fs_srn"
    "-"   ident(Hstp)
    "/"   ident(I1) ident(I2)
    :=
    fs_stp;
    eapply transitive_eval;
    [ eapply frame_indep_core in Hstp;
      exact Hstp
    | clear Hstp I1 I2;
      simpl ].

  Tactic Notation "fs_srn"
    "-"   ident(Hstp)
    "/"   ident(I1) ident(I2) ident(I3)
    :=
    fs_stp;
    eapply transitive_eval;
    [ eapply frame_indep_core in Hstp;
      exact Hstp
    | clear Hstp I1 I2 I3;
      simpl ].

  Tactic Notation "fs_srn"
    "-"   ident(Hstp)
    "/"   ident(I1) ident(I2) ident(I3) ident(I4)
    :=
    fs_stp;
    eapply transitive_eval;
    [ eapply frame_indep_core in Hstp;
      exact Hstp
    | clear Hstp I1 I2 I3 I4;
      simpl ].

  Tactic Notation "fs_srn"
    "-"   ident(Hstp)
    "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
    :=
    fs_stp;
    eapply transitive_eval;
    [ eapply frame_indep_core in Hstp;
      exact Hstp
    | clear Hstp I1 I2 I3 I4 I5;
      simpl ].



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