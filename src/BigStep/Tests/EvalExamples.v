(**
  This file contains a number of step-by-step program evaluation examples.
*)

From CoreErlang.BigStep Require Import SemanticsEquivalence
                                       SemanticsProofs
                                       MapEval.
Import ListNotations.

Open Scope string_scope.

Section increment.

  Context (Γ : Environment)
          (v : Value)
          (x : Var)
          (HΓ : get_value Γ (inl x) = Some [v]).
  Definition inc : Expression :=
    EFun ["X"] (ECall (ELit (Atom "erlang")) (ELit (Atom "+")) [EVar "X";ELit (Integer 1%Z)]).
  Definition inc_app : Expression := EApp inc [EVar x].

  Local Definition final (v : Value) : ValueSequence + Exception :=
  match v with
  | VLit (Integer x) => inl [VLit (Integer (x + 1)%Z)]
  | _ => inr (badarith (VTuple [VLit (Atom "+"); v; VLit (Integer 1%Z)]))
  end.

  Local Lemma inc_eval :
    | Γ, [], "m", 0, inc_app, [] | -e> |1, final v, []|.
  Proof.
    unfold inc_app.
    eapply eval_app with (eff := [[]]) (ids := [1]) (vals := [v]); try reflexivity.
    * apply eval_fun.
    * reflexivity.
    * intros. simpl in H. destruct i. 2: lia.
      cbn. apply eval_var. assumption.
    * cbn.
      eapply eval_call with (eff := [[];[]]) (ids := [1;1]) (vals := [v;VLit (Integer 1)]); try reflexivity.
      - apply eval_lit.
      - apply eval_lit.
      - intros. cbn in H. destruct i. 2: destruct i. 3: lia.
        + apply eval_var. cbn.
          now rewrite get_value_here.
        + apply eval_lit.
      - cbn. reflexivity.
      - cbn. destruct v; try destruct l; now cbn.
  Qed.

End increment.

Section infinite.
  Definition inf n : Expression :=
    ELetRec [(("f", 1), (["X"],
      ESeq (ECall (ELit (Atom "io")) (ELit (Atom "fwrite")) [EVar "X"])
           (EApp (EFunId ("f", 1)) [
             (ECall (ELit (Atom "erlang")) (ELit (Atom "+")) [EVar "X";ELit (Integer 1%Z)])
           ])))
    ]
    (EApp (EFunId ("f", 1)) [ELit (Integer n)]).

  Local Lemma inf_diverges :
    forall Γ id id' eff eff' r n,
      ~|Γ, [], "m", id, inf n, eff| -e> |id', r, eff'|.
  Proof.
    intros. intro.
    apply fbs_soundness in H as [clock].
    revert Γ id id' eff eff' r n H.
    intros.
    destruct clock. now simpl in H.
    destruct clock. now simpl in H.
    destruct clock. now simpl in H.
    simpl in H.
    cbn in H. rewrite get_value_here in H. simpl in H.
    break_match_hyp; try congruence.
    destruct res; try congruence.
    destruct v; try congruence.
    destruct v0; try congruence.
    1: { (* correct evaluation *)
      cbn in H.
      destruct clock. now simpl in Heqr0.
      destruct clock. now simpl in Heqr0.
      cbn in Heqr0.
      rewrite get_value_here in Heqr0. simpl in Heqr0. inversion Heqr0. subst id0 v eff0.
      clear Heqr0.
      remember (S (S clock)) as cl. clear Heqcl. clear clock.
      revert Γ id id' eff eff' r n H.
      induction cl using Wf_nat.lt_wf_ind.
      remember ((EApp (EFunId ("f", 1))
         [ECall (ELit (Atom "erlang")) (ELit (Atom "+"))
            [EVar "X"; ELit (Integer 1)]])) as rec.
      intros.
      rewrite Heqrec in H0 at 3.
      destruct cl. now simpl in H0.
      simpl in H0.
      destruct cl. now simpl in H0.
      simpl fbs_expr at 1 in H0.
      rewrite get_value_there, get_value_here in H0. 2: congruence.
      destruct (fbs_expr (S cl)) eqn:H0D in H0.
      2-3: now cbn in H0.
      cbn in H0D. destruct cl. now cbn in H0.
      cbn in H0D. rewrite get_value_here in H0D. inversion H0D. subst id0 res eff0.
      clear H0D.
      simpl length in H0. simpl Nat.eqb in H0.
      remember (S cl) as cl2. cbn in H0.
      destruct (fbs_expr cl2) eqn:H0D in H0. 2-3: now simpl in H0.
      destruct cl2. now simpl in H0.
      cbn in H0D.
      destruct cl2. now simpl in H0.
      cbn in H0D. rewrite get_value_here in H0D. inversion H0D. subst id0 res eff0.
      cbn in H0D. clear H0D.
      apply H in H0. assumption.
      lia.
    }
    1: { (* potential exceptional evaluation *)
      inversion H. subst. clear H.
      destruct clock. now simpl in Heqr0.
      destruct clock. now simpl in Heqr0.
      cbn in Heqr0. rewrite get_value_here in Heqr0. cbn in Heqr0.
      inversion Heqr0.
    }
  Qed.

End infinite.

Section map.

  Local Lemma map_eval :
    | [], [], "m", 0,
      @map_exp [ELit (Integer 1);ELit (Integer 2); ELit (Integer 3)]
         (ECall (ELit (Atom "erlang")) (ELit (Atom "+")) [EVar "X";ELit (Integer 1%Z)])
         "X",
    [] |
  -e> 
    | 2, inl [VCons (VLit (Integer 2)) (VCons (VLit (Integer 3)) (VCons (VLit (Integer 4)) VNil))], [] |.
  Proof.
    apply eval_letrec. cbn.
    (** 1st recursive application *)
    eapply eval_app with (ids := [2;2]) (eff := [[];[]]); try reflexivity.
    * unfold_list.
    * apply eval_funid; now cbn.
    * reflexivity.
    * simpl. intros.
      destruct i. 2: destruct i. 3: lia.
      all: simpl.
      - apply eval_fun.
      - eapply eval_cons. 2: apply eval_lit.
        eapply eval_cons. 2: apply eval_lit.
        eapply eval_cons. 2: apply eval_lit.
        apply eval_nil.
    * cbn. eapply eval_case.
      - apply eval_var. cbn. reflexivity.
      (** the 2nd pattern matches *)
      - instantiate (1 := 1). simpl. lia.
      - reflexivity.
      - intros. destruct j. 2: lia.
        cbn in H0. congruence.
      - cbn. apply eval_lit.
      - cbn. eapply eval_cons.
        (** 2nd recursive application *)
        + eapply eval_app with (ids := [2;2]) (eff := [[];[]]); try reflexivity.
          ** unfold_list.
          ** apply eval_funid; now cbn.
          ** reflexivity.
          ** simpl. intros.
             destruct i. 2: destruct i. 3: lia.
             all: simpl.
             -- apply eval_var. reflexivity.
             -- apply eval_var. reflexivity.
          ** cbn. eapply eval_case.
             -- apply eval_var. cbn. reflexivity.
             (** still 2nd pattern matches *)
             -- instantiate (1 := 1). simpl. lia.
             -- reflexivity.
             -- intros. destruct j. 2: lia.
                cbn in H0. congruence.
             -- cbn. apply eval_lit.
             -- cbn. eapply eval_cons.
                (** 3rd recursive application *)
                ++ eapply eval_app with (ids := [2;2]) (eff := [[];[]]);
                   try reflexivity.
                   *** unfold_list.
                   *** apply eval_funid; now cbn.
                   *** reflexivity.
                   *** simpl. intros.
                       destruct i. 2: destruct i. 3: lia.
                       all: simpl.
                       --- apply eval_var. reflexivity.
                       --- apply eval_var. reflexivity.
                   *** cbn. eapply eval_case.
                       --- apply eval_var. cbn. reflexivity.
                       (** still 2nd pattern matches *)
                       --- instantiate (1 := 1). simpl. lia.
                       --- reflexivity.
                       --- intros. destruct j. 2: lia.
                           cbn in H0. congruence.
                       --- cbn. apply eval_lit.
                       --- cbn. eapply eval_cons.
                           (** final recursive application *)
                           +++ eapply eval_app with (ids := [2;2]) (eff := [[];[]]);
                               try reflexivity.
                               **** unfold_list.
                               **** apply eval_funid; now cbn.
                               **** reflexivity.
                               **** simpl. intros.
                                    destruct i. 2: destruct i. 3: lia.
                                    all: simpl.
                                    ---- apply eval_var. reflexivity.
                                    ---- apply eval_var. reflexivity.
                               **** cbn. eapply eval_case.
                                    ---- apply eval_var. cbn. reflexivity.
                                    (** now 1st pattern matches *)
                                    ---- instantiate (1 := 0). simpl. lia.
                                    ---- reflexivity.
                                    ---- lia.
                                    ---- apply eval_lit.
                                    ---- cbn. apply eval_nil.
                           (** Application of the increment function to 3 *)
                           +++ eapply eval_app.
                               **** unfold_list.
                               **** apply eval_var. reflexivity.
                               **** reflexivity.
                               **** unfold_list.
                               **** unfold_list.
                               **** intros. simpl in *.
                                    destruct i. 2: lia.
                                    apply eval_var. reflexivity.
                               **** eapply eval_call.
                                    1-3: unfold_list.
                                    1-2: apply eval_lit.
                                    ---- simpl. intros.
                                         destruct i. 2: destruct i. 3: lia.
                                         ++++ apply eval_var. reflexivity.
                                         ++++ apply eval_lit.
                                    ---- reflexivity.
                                    ---- reflexivity.
                                    ---- reflexivity.
                (** Application of the increment function to 2 *)
                ++ eapply eval_app.
                   *** unfold_list.
                   *** apply eval_var. reflexivity.
                   *** reflexivity.
                   *** unfold_list.
                   *** unfold_list.
                   *** intros. simpl in *.
                       destruct i. 2: lia.
                       apply eval_var. reflexivity.
                   *** eapply eval_call.
                       1-3: unfold_list.
                       1-2: apply eval_lit.
                       --- simpl. intros.
                           destruct i. 2: destruct i. 3: lia.
                           +++ apply eval_var. reflexivity.
                           +++ apply eval_lit.
                       --- reflexivity.
                       --- reflexivity.
                       --- reflexivity.
        (** Application of the increment function to 1 *)
        + eapply eval_app.
          ** unfold_list.
          ** apply eval_var. reflexivity.
          ** reflexivity.
          ** unfold_list.
          ** unfold_list.
          ** intros. simpl in *.
             destruct i. 2: lia.
             apply eval_var. reflexivity.
          ** eapply eval_call.
             1-3: unfold_list.
             1-2: apply eval_lit.
             -- simpl. intros.
                destruct i. 2: destruct i. 3: lia.
                ++ apply eval_var. reflexivity.
                ++ apply eval_lit.
             -- reflexivity.
             -- reflexivity.
             -- reflexivity.
  Qed.

  Local Lemma map_eval_exc :
    | [], [], "m", 0,
      @map_exp [ELit (Atom "a");ELit (Integer 2); ELit (Integer 3)]
         (ECall (ELit (Atom "erlang")) (ELit (Atom "+")) [EVar "X";ELit (Integer 1%Z)])
         "X",
    [] |
  -e> 
    | 2, inr (badarith (VTuple [VLit (Atom "+"); VLit (Atom "a"); VLit (Integer 1)])), [] |.
  Proof.
    apply eval_letrec. cbn.
    (** 1st recursive application *)
    eapply eval_app with (ids := [2;2]) (eff := [[];[]]); try reflexivity.
    * unfold_list.
    * apply eval_funid; now cbn.
    * reflexivity.
    * simpl. intros.
      destruct i. 2: destruct i. 3: lia.
      all: simpl.
      - apply eval_fun.
      - eapply eval_cons. 2: apply eval_lit.
        eapply eval_cons. 2: apply eval_lit.
        eapply eval_cons. 2: apply eval_lit.
        apply eval_nil.
    * cbn. eapply eval_case.
      - apply eval_var. cbn. reflexivity.
      (** the 2nd pattern matches *)
      - instantiate (1 := 1). simpl. lia.
      - reflexivity.
      - intros. destruct j. 2: lia.
        cbn in H0. congruence.
      - cbn. apply eval_lit.
        (** Difference here! We use an exception rule *)
      - cbn. eapply eval_cons_hd_ex.
        (** However, the tail evaluation proceeds the same way as before *)
        (** 2nd recursive application *)
        + eapply eval_app with (ids := [2;2]) (eff := [[];[]]); try reflexivity.
          ** unfold_list.
          ** apply eval_funid; now cbn.
          ** reflexivity.
          ** simpl. intros.
             destruct i. 2: destruct i. 3: lia.
             all: simpl.
             -- apply eval_var. reflexivity.
             -- apply eval_var. reflexivity.
          ** cbn. eapply eval_case.
             -- apply eval_var. cbn. reflexivity.
             (** still 2nd pattern matches *)
             -- instantiate (1 := 1). simpl. lia.
             -- reflexivity.
             -- intros. destruct j. 2: lia.
                cbn in H0. congruence.
             -- cbn. apply eval_lit.
             -- cbn. eapply eval_cons.
                (** 3rd recursive application *)
                ++ eapply eval_app with (ids := [2;2]) (eff := [[];[]]);
                   try reflexivity.
                   *** unfold_list.
                   *** apply eval_funid; now cbn.
                   *** reflexivity.
                   *** simpl. intros.
                       destruct i. 2: destruct i. 3: lia.
                       all: simpl.
                       --- apply eval_var. reflexivity.
                       --- apply eval_var. reflexivity.
                   *** cbn. eapply eval_case.
                       --- apply eval_var. cbn. reflexivity.
                       (** still 2nd pattern matches *)
                       --- instantiate (1 := 1). simpl. lia.
                       --- reflexivity.
                       --- intros. destruct j. 2: lia.
                           cbn in H0. congruence.
                       --- cbn. apply eval_lit.
                       --- cbn. eapply eval_cons.
                           (** final recursive application *)
                           +++ eapply eval_app with (ids := [2;2]) (eff := [[];[]]);
                               try reflexivity.
                               **** unfold_list.
                               **** apply eval_funid; now cbn.
                               **** reflexivity.
                               **** simpl. intros.
                                    destruct i. 2: destruct i. 3: lia.
                                    all: simpl.
                                    ---- apply eval_var. reflexivity.
                                    ---- apply eval_var. reflexivity.
                               **** cbn. eapply eval_case.
                                    ---- apply eval_var. cbn. reflexivity.
                                    (** now 1st pattern matches *)
                                    ---- instantiate (1 := 0). simpl. lia.
                                    ---- reflexivity.
                                    ---- lia.
                                    ---- apply eval_lit.
                                    ---- cbn. apply eval_nil.
                           (** Application of the increment function to 3 *)
                           +++ eapply eval_app.
                               **** unfold_list.
                               **** apply eval_var. reflexivity.
                               **** reflexivity.
                               **** unfold_list.
                               **** unfold_list.
                               **** intros. simpl in *.
                                    destruct i. 2: lia.
                                    apply eval_var. reflexivity.
                               **** eapply eval_call.
                                    1-3: unfold_list.
                                    1-2: apply eval_lit.
                                    ---- simpl. intros.
                                         destruct i. 2: destruct i. 3: lia.
                                         ++++ apply eval_var. reflexivity.
                                         ++++ apply eval_lit.
                                    ---- reflexivity.
                                    ---- reflexivity.
                                    ---- reflexivity.
                (** Application of the increment function to 2 *)
                ++ eapply eval_app.
                   *** unfold_list.
                   *** apply eval_var. reflexivity.
                   *** reflexivity.
                   *** unfold_list.
                   *** unfold_list.
                   *** intros. simpl in *.
                       destruct i. 2: lia.
                       apply eval_var. reflexivity.
                   *** eapply eval_call.
                       1-3: unfold_list.
                       1-2: apply eval_lit.
                       --- simpl. intros.
                           destruct i. 2: destruct i. 3: lia.
                           +++ apply eval_var. reflexivity.
                           +++ apply eval_lit.
                       --- reflexivity.
                       --- reflexivity.
                       --- reflexivity.
        (** Application of the increment function to 'a' -> exception is
            raised here - however, the same tactics solve the goal, since
            the exception was created by `eval` - the simulator function. *)
        + simpl. eapply eval_app.
          ** unfold_list.
          ** apply eval_var. reflexivity.
          ** reflexivity.
          ** unfold_list.
          ** unfold_list.
          ** intros. simpl in *.
             destruct i. 2: lia.
             apply eval_var. reflexivity.
          ** eapply eval_call.
             1-3: unfold_list.
             1-2: apply eval_lit.
             -- simpl. intros.
                destruct i. 2: destruct i. 3: lia.
                ++ apply eval_var. reflexivity.
                ++ apply eval_lit.
             -- reflexivity.
             -- reflexivity.
             -- reflexivity.
  Qed.

End map.