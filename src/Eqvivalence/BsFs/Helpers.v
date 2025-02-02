From CoreErlang.Eqvivalence.BsFs Require Export EraseNames.

Import SubstSemantics.

(** CONTENT:
* SCOPE_AND_STEP (TACTICS; LEMMAS; THEOREMS)
  - Scope_Destructs (TACTICS)
    + des_for
  - Scope_Lists (LEMMAS)
    + scope_list_nth_succ
    + scope_list_nth_succ_id
  - Scope_Values (THEOREMS)
    + scope_vcons
    + scope_vtuple
    + scope_vmap
  - Scope_Tactics (TACTICS)
    + scope
    + start
  - Step (TACTICS)
    + do_step
    + do_transitive
    + step
* ENVIRONMENT_LEMMAS (LEMMAS)
  - EnvironmentLemmas_GetValue (LEMMAS)
    + get_value_singleton
    + get_value_singleton_length
    + get_value_single_det
    + get_value_cons
* ERASE_SUBST_APPEND (LEMMAS; THEOREMS)
  - EraseSubstAppend_EraserLemmas (LEMMAS)
    + add_keys_get_env_app
    + add_keys_append_vars_to_env_app
    + add_keys_append_vars_to_env_get_env_app
    + add_keys_append_funs_to_env_app
  - EraseSubstAppend_SubstLemmas (LEMMAS)
    + list_subst_cons
    + list_subst_fold_right
    + list_subst_app
  - EraseSubstAppend_Theorems (THEOREMS)
    + erase_subst_append_vars
* FRAMEIDENT_Lemmas (LEMMAS)
  * FrameStackEvaluation_NthLemmas
    - BIFORALL ?
    - CREATE_RESULTS ?
* EQVIVALENCE_HELPERS (LEMMAS)
  - EqvivalenceHelpers
* AXIOMS (AXIOM; LEMMAS)
  - Axioms (AXIOM)
    + all_val_is_wfm
    + no_modfunc
    + result_is_result
    + eval_catch_vars_length
    + erase_subst_rem_vars
  - Axioms_Lemmas (LEMMAS)
    + get_value_is_result
    + evar_is_result
    + efunid_is_result
    + efun_is_result
    + catch_vars_length
*)












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: SCOPE_AND_STEP ///////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






(* Section Scope_Destructs. *)



  (** DOCUMENTATION:
  * des_for --> destruct_foralls; rename
    - N:[ident]:1-10 : N:[ident]:1-10
  *)

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



(* End Scope_Destructs. *)









Section Scope_Lists.



  Lemma scope_list_nth_succ :
    forall A i vl (f : A -> Val),
        (i < length vl
        ->  VALCLOSED (nth i (map f vl) VNil))
    ->  (S i < S (length vl)
        ->  VALCLOSED (nth i (map f vl) VNil)).
  Proof.
    (* #1 Pose: intro/pose/destruct/ *)
    itr - A i vl f Hvl Hsucc_lt.
    pse - Nat.succ_lt_mono as Hmono_succ_lt: i (base.length vl).
    des - Hmono_succ_lt as [_ Hfrom_succ_lt].
    (* #2 Apply: apply *)
    app - Hfrom_succ_lt in Hsucc_lt as Hlt; clr - Hfrom_succ_lt.
    bpp - Hvl in Hlt.
  Qed.



  Lemma scope_list_nth_succ_id :
    forall i vl,
        (i < length vl
        ->  VALCLOSED (nth i vl VNil))
    ->  (S i < S (length vl)
        ->  VALCLOSED (nth i vl VNil)).
  Proof.
    (* #1 Assert: intro/assert/remember + apply *)
    itr - i vl Hvl.
    ass > (map id vl = vl) as Hid: apply Basics.map_id.
    rem - n as Hn: (base.length vl).
    (* #2 Rewrite: rewrite *)
    cwl + Hid in Hvl.
    cwr - Hn in *.
    (* #3 Pose by Previus: pose *)
    by pose proof scope_list_nth_succ Val i vl id Hvl.
  Qed.



  Lemma scope_list_to_nth :
    forall vl,
        (Forall (fun v => VALCLOSED v) vl)
    ->  (forall i,
            i < base.length vl
        ->  VALCLOSED (nth i vl VNil)).
  Proof.
    itr - vl Hvl.
    itr - i Hlt.
    erewrite -> Forall_nth in Hvl.
    bpe - Hvl: i VNil Hlt.
  Qed.



End Scope_Lists.









Section Scope_Value.



  Theorem scope_vcons :
    forall v1 v2,
        is_result (RValSeq [v1])
    ->  is_result (RValSeq [v2])
    ->  is_result (RValSeq [VCons v1 v2]).
  Proof.
    (* #1 Inversion: intro/inversion/destruct_foralls *)
    itr - v1 v2 Hv1 Hv2.
    ivc - Hv1 as Hv1: H0.
    ivc - Hv2 as Hv2: H0.
    des_for - Hv1 Hv2: H3 H1.
    (* #2 Finish: pose *)
    ato.
  Qed.






  Theorem scope_vtuple :
    forall v vl,
        is_result (RValSeq [v])
    ->  is_result (RValSeq [VTuple vl])
    ->  is_result (RValSeq [VTuple (v :: vl)]).
  Proof.
    (* #1 Inversion: intro/inversion/destruct_foralls *)
    itr - v vl Hv Hvl.
    ivc - Hv as Hv: H0.
    ivc - Hvl as Hvl: H0.
    des_for - Hv Hvl: H3 H1.
    (* #3 Constructor: constructor *)
    do 3 cns.
    (* #4 Simplify: intro/simpl *)
    itr - i Hl.
    smp *.
    (* #5 Destruct: destruct + exact *)
    des - i: exa - Hv.
    (* #6 Inversion: inversion *)
    ivc - Hvl as Hvl: H1 / v Hv.
    (* #7 Finish: pose *)
    bse - scope_list_nth_succ_id: i vl (Hvl i) Hl.
  Qed.






  Theorem scope_vmap :
    forall v1 v2 vl,
        is_result (RValSeq [v1])
    ->  is_result (RValSeq [v2])
    ->  is_result (RValSeq [VMap vl])
    ->  is_result (RValSeq [VMap ((v1, v2) :: vl)]).
  Proof.
    (* #1 Inversion: intro/inversion/destruct_foralls *)
    itr - v1 v2 vl Hv1 Hv2 Hvl.
    ivc - Hv1 as Hv1: H0.
    ivc - Hv2 as Hv2: H0.
    ivc - Hvl as Hvl: H0.
    des_for - Hv1 Hv2 Hvl: H5 H3 H1.
    (* #3 Constructor: constructor *)
    do 3 cns.
    * (* #4.1 Simplify: intro/simpl *)
      itr - i Hl.
      smp *.
      (* #5.1 Destruct: clear/destruct + exact *)
      clr - Hv2 v2.
      des - i: exa - Hv1.
      (* #6.1 Inversion: inversion *)
      ivc - Hvl as Hvl: H0 / H2 v1 Hv1.
      (* #7.1 Finish: pose *)
      by pose proof scope_list_nth_succ (Val * Val) i vl fst (Hvl i) Hl.
    * (* #4.2 Simplify: intro/simpl *)
      itr - i Hl.
      smp *.
      (* #5.2 Destruct: clear/destruct + exact *)
      clr - Hv1 v1.
      des - i: exa - Hv2.
      (* #6.2 Inversion: inversion *)
      ivc - Hvl as Hvl: H2 / H0 v2 Hv2.
      (* #7.2 Finish: pose *)
      by pose proof scope_list_nth_succ (Val * Val) i vl snd (Hvl i) Hl.
  Qed.






  Theorem scope_app :
    forall vl1 vl2,
        is_result (RValSeq vl1)
    ->  is_result (RValSeq vl2)
    ->  is_result (RValSeq (vl1 ++ vl2)).
  Proof.
    itr - vl1 vl2 Hvl1 Hvl2.
    (* #1 Inversion on Hypothesis: inversion/subst *)
    ivc - Hvl1 as Hvl1: H0.
    ivc - Hvl2 as Hvl2: H0.
    (* #2 Open IsResult: constructor *)
    cns.
    (* #3 Solve by Forall Application Theorem: apply; auto *)
    app - Forall_app.
    ato.
  Qed.






  Theorem scope_cons :
    forall v vl,
        is_result (RValSeq [v])
    ->  is_result (RValSeq vl)
    ->  is_result (RValSeq (v :: vl)).
  Proof.
    itr - v vl Hv Hvl.
    (* #1 Solve By Previues Theorem (Scope App): rewrite/apply + auto *)
    rwr - cons_app.
    app - scope_app; ato.
  Qed.






  Theorem scope_list_to_tuple :
    forall vl,
        is_result (RValSeq vl)
    ->  is_result (RValSeq [VTuple vl]).
  Proof.
    (* #1 Inversion: intro/inversion/destruct_foralls *)
    itr - vl Hvl.
    ivc - Hvl as Hvl: H0.
    (* #3 Constructor: constructor *)
    do 3 cns.
    (* #4 By List to Nth Lemma: apply/trivial *)
    bpp - scope_list_to_nth.
  Qed.


(* 
  Theorem scope_create :
    forall vl ident r,
        ICLOSED ident
    ->  is_result (RValSeq vl)
    ->  Some (r, []) = create_result ident vl []
    ->  is_result r.
  Proof.
    itr - vl ident r Hident Hvl Hcrt.
    (* #1 Inversion on Hypothesis: inversion/subst *)
    ivc - Hvl as Hvl: H0.
    Check ICLOSED_ind.
    apply (ICLOSED_ind (fun ident => (forall r,
    Some (r, []) = create_result ident vl [] -> is_result r))) in Hident.
  
    induction ident using ICLOSED_ind.
    des - ident.
    * smp *. ivc - Hcrt.
      cns.
      exa - Hvl.
    * smp *. ivc - Hcrt.
      do 3 cns.
      bpp - scope_list_to_nth.
    * smp *. ivc - Hcrt.
      do 3 cns.
      admit. admit.
    * admit. (*  smp *.
      des - m.
      - ivc - Hcrt.
        scope_solver.
      do 3 cns.
      bpp - scope_list_to_nth. *)
    * pse - ICLOSED_ind: (fun x => ICLOSED x).
      pose proof create_result_closed
        vl (IPrimOp f) r [] [] Hvl Hident Hcrt
        as Hscope;
        clr - Hvl Hident Hcrt.
      ivs - Hscope.
      - scope_solver.
      Search FrameIdent.
      Search (REDCLOSED _).
      pse - is_result_closed: r.
      assert (Hcontra : ¬REDCLOSED r → ¬is_result r).
      {
        intros HnotClosed Hresult.
        apply HnotClosed.
        apply H.
        assumption.
      }
      (* Since we know REDCLOSED r, we can conclude is_result r *)
      unfold not in Hcontra.
      Search ((_ -> False) -> _ -> False).
      erewrite -> Decidable.contrapositive in Hcontra.
      apply NNPP.
      intro HnotResult.
      apply Hcontra in HnotResult.
      contradiction.
    Qed.
      app - is_result_closed.
      ivs - H.
      -  Search (REDCLOSED _). RBox. auto.
      smp *.
      unfold primop_eval in *.
      Search FrameIdent. admit.
    * smp *. admit.
     (* mp *. ivc - Hcrt.
      do 3 cns.
      bpp - scope_list_to_nth.
      itr - i Hlt. *)
      erewrite -> Forall_nth in Hvl.
      bpe - Hvl: i VNil Hlt.
      exa - Hvl.
      erewrite -> Forall_nth in Hvl.
      Check Forall_nth.
      apply Forall_nth with (d := VNil) in Hvl.
      - (* Now we need to show that the property holds for the nth element *)
        apply Hvl.
        assumption.
      - (* Provide the index and the default value *)
        exact Hlt.
      scope_solver.
      scope_solver.
      exa - Hvl.
     *)


End Scope_Value.









(* Section Scope_Tactics. *)



  Ltac scope :=
    try (apply scope_vcons; [assumption ..]);
    try (apply scope_vtuple; [assumption ..]);
    try (apply scope_vmap; [assumption ..]);
    try (simpl in *; assumption);
    try (constructor);
    try (destruct_foralls);
    try (assumption + scope_solver).



  (** DOCUMENTATION:
  * start --> eexists; split; [> scope]; clear.
    / [ident]:0-3
    - hyp
  *)

  Tactic Notation "start"
      :=
    eexists; split; [(scope + admit) | idtac].

  Tactic Notation "start"
      "/"   ident(I1)
      :=
    eexists; split; [(scope + admit) | idtac];
    clear I1.

  Tactic Notation "start"
      "/"   ident(I1) ident(I2)
      :=
    eexists; split; [(scope + admit) | idtac];
    clear I1 I2.

  Tactic Notation "start"
      "/"   ident(I1) ident(I2) ident(I3)
      :=
    eexists; split; [(scope + admit) | idtac];
    clear I1 I2 I3.

  Tactic Notation "start"
      "-"   ident(H)
      :=
    eexists; split; [ivs - H; (scope + admit) | clear H].



(* End Scope_Tactics. *)









(* Section Step. *)



  Ltac do_step
    :=
    (econstructor;
    [ (constructor; auto + scope_solver + congruence)
    + (econstructor; constructor)
    + (econstructor;
      [ congruence
      | constructor ])
    | simpl ])
    + (cbn; constructor).



  Ltac do_transitive H
    :=
    eapply transitive_eval;
    [ eapply frame_indep_core in H;
      exact H
    | clear H;
      simpl ].



  (** DOCUMENTATION:
  * step --> repeat step; (exact H + do_transitive H).
    / [ident]:0-5
    - hyp / [ident]:0-10
    - tactic / [ident]:0-5
  *)

  Tactic Notation "step"
      :=
    repeat do_step.

  Tactic Notation "step"
      "/"   ident(I1)
      :=
    repeat do_step;
    clear I1.

  Tactic Notation "step"
      "/"   ident(I1) ident(I2)
      :=
    repeat do_step;
    clear I1 I2.

  Tactic Notation "step"
      "/"   ident(I1) ident(I2) ident(I3)
      :=
    repeat do_step;
    clear I1 I2 I3.

  Tactic Notation "step"
      "/"   ident(I1) ident(I2) ident(I3) ident(I4)
      :=
    repeat do_step;
    clear I1 I2 I3 I4.

  Tactic Notation "step"
      "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      :=
    repeat do_step;
    clear I1 I2 I3 I4 I5.

  Tactic Notation "step"
      "-"   hyp(H)
      :=
    repeat do_step;
    (exact H + do_transitive H).

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3 I4.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3 I4 I5.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
            ident(I6)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3 I4 I5 I6.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
            ident(I6) ident(I7)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3 I4 I5 I6 I7.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
            ident(I6) ident(I7) ident(I8)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3 I4 I5 I6 I7 I8.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
            ident(I6) ident(I7) ident(I8) ident(I9)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3 I4 I5 I6 I7 I8 I9.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
            ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10.

  Tactic Notation "step"
      ":"   tactic(T)
      :=
    repeat do_step;
    [T | idtac].

  Tactic Notation "step"
      ":"   tactic(T)
      "/"   ident(I1)
      :=
    repeat do_step;
    [T | idtac];
    clear I1.

  Tactic Notation "step"
      ":"   tactic(T)
      "/"   ident(I1) ident(I2)
      :=
    repeat do_step;
    [T | idtac];
    clear I1 I2.

  Tactic Notation "step"
      ":"   tactic(T)
      "/"   ident(I1) ident(I2) ident(I3)
      :=
    repeat do_step;
    [T | idtac];
    clear I1 I2 I3.

  Tactic Notation "step"
      ":"   tactic(T)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4)
      :=
    repeat do_step;
    [T | idtac];
    clear I1 I2 I3 I4.

  Tactic Notation "step"
      ":"   tactic(T)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      :=
    repeat do_step;
    [T | idtac];
    clear I1 I2 I3 I4 I5.



(* End Step. *)












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: ENVIRONMENT_LEMMAS ///////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

Import BigStep.






Section EnvironmentLemmas_GetValue.



  Lemma get_value_singleton :
    forall Γ key vs,
        get_value Γ key = Some vs
    ->  exists value, vs = [value].
  Proof.
    intros Γ key vs.
     induction Γ as [| [k v] Γ IH]; intros Hget; cbn in Hget.
     * congruence.
     * destruct (var_funid_eqb key k) eqn:Heqb.
       - exists v.
         by inv Hget.
       - by apply IH.
  Qed.



  (*not used*)
  Lemma get_value_singleton_length :
    forall Γ key l,
        get_value Γ key = Some l
    ->  length l = 1.
  Proof.
    (* #1 Pose by Previous: intro/pose/inversion *)
    itr - Γ key vs Hget.
    pse - get_value_singleton as Hsingl: Γ key vs Hget.
    bvs - Hsingl.
  Qed.



  (*not used*)
  Lemma get_value_single_det :
    forall k1 k2 v1 v2,
        get_value [(k1, v1)] k2 = Some [v2]
    ->  k1 = k2 /\  v1 = v2.
  Proof.
    itr - k1 k2 v1 v2 Hget.
    smp - Hget.
    des > (var_funid_eqb k2 k1) as Hk; ivc - Hget.
    spl.
    2: rfl.
    ufl - var_funid_eqb in Hk.
    des - k1 as [s1 | f1]; des - k2 as [s2 | f2]; smp - Hk.
    * app - String.eqb_eq in Hk.
      bvs - Hk.
    * con.
    * con.
    * ufl - funid_eqb in Hk.
      des - f1 as [i1 n1]; des - f2 as [i2 n2]; smp - Hk.
      app - andb_prop in Hk.
      des - Hk as [Hi Hn].
      app - String.eqb_eq in Hi.
      app - Nat.eqb_eq in Hn.
      sbt.
      rfl.
  Qed.



  (*not used*)
  Lemma get_value_cons :
    forall k v Γ key val,
        get_value ((k, v) :: Γ) key = Some [val]
    ->  get_value [(k, v)] key = Some [val]
    \/  get_value Γ key = Some [val].
  Proof.
    (* #1 Destruct Key Equality: intro/simpl/destruct/auto *)
    itr - k v Γ key val Hcons.
    smp *.
    des > (var_funid_eqb key k) as Heqb_key; ato.
  Qed.



  Lemma get_value_cons_eqb :
    forall k v Γ key val,
        get_value ((k, v) :: Γ) key = Some [val]
    ->  (k = key /\ v = val)
    \/  (get_value Γ key = Some [val] /\ var_funid_eqb key k = false).
  Proof.
    (* #1 Destruct Key Equality: intro/simpl/destruct/auto *)
    itr - k v Γ key val Hcons.
    smp *.
    des > (var_funid_eqb key k) as Heqb.
    * lft.
      rwr - var_funid_eqb_eq in Heqb; sbt.
      ivc - Hcons.
      spl; ato.
    * rgt; spl; ato.
  Qed.


  (*not used*)
  Theorem get_value_in :
    forall Γ key var,
        get_value Γ key = Some [var]
    ->  In (key , var) Γ.
  Proof.
    (* #1 Induction on Environment: intro/induction + intro/inversion *)
    itr - Γ.
    ind - Γ as [| [k v] Γ IH] :> itr - key var Hget :- ivc - Hget.
    (* #2 Destruct Get_Value: apply/destruct *)
    app - get_value_cons in Hget.
    des - Hget as [Hget | Hget].
    * (* #3.1 Destruct Key Equality: clear/simpl/destruct + congruence *)
      clr - IH.
      smp *.
      des > (var_funid_eqb key k) as Hkey :- con.
      (* #4.1 Rewrite Var & FunId: left/inversion/apply/rewrite *)
      lft.
      ivc - Hget.
      app - var_funid_eqb_eq in Hkey.
      bwr - Hkey.
    * (* #3.2 Pose In_Cons: specialize/pose *)
      spc - IH: key var Hget.
      by pose proof in_cons (k, v) (key, var) Γ IH.
  Qed.



End EnvironmentLemmas_GetValue.










(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: ERASE_SUBST_APPEND //////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Section EraseSubstAppend_EraserLemmas.



  Lemma add_keys_get_env_app :
    forall ext Γ σ,
        add_keys (map fst (get_env Γ ext)) σ
      = add_ext ext (add_keys (map fst Γ) σ).
  Proof.
    itr - ext Γ σ.
    ufl - get_env.
    rwr - map_app.
    rwr - ext_to_env_fst.
    rwr - add_keys_app.
    ufl - add_ext add_fids.
    bwr - map_map.
  Qed.



  Lemma add_keys_append_vars_to_env_app :
    forall vars vs Γ σ,
        length vars = length vs
    ->  add_keys (map fst (append_vars_to_env vars vs Γ)) σ
      = add_vars vars (add_keys (map fst Γ) σ).
  Proof.
    itr - vars vs Γ σ Hlength.
    ufl - append_vars_to_env.
    rwr - map_app.
    rwr - add_keys_app.
    epose proof length_map (inl : Var -> (Var + FunctionIdentifier)) vars
      as Hlength_map_inl.
    cwl - Hlength_map_inl in Hlength.
    epose proof zip_fst _ _ _ _ Hlength as Hzip_fst;
      clr - Hlength.
    cwr - Hzip_fst.
    ufl - add_vars.
    trv.
  Qed.



  Lemma from_env_append_vars_to_env_app :
    forall vars vs Γ,
        length vars = length vs
    ->  from_env (append_vars_to_env vars vs Γ)
      = add_vars vars (from_env Γ).
  Proof.
    itr - vars vs Γ Hlength.
    ufl - from_env
          add_env.
    app - add_keys_append_vars_to_env_app.
    exa - Hlength.
  Qed.



  Lemma add_keys_append_vars_to_env_get_env_app :
    forall vars vs ext Γ σ,
        length vars = length vs
    ->  add_keys (map fst (append_vars_to_env vars vs (get_env Γ ext))) σ
      = add_vars vars (add_ext ext (add_keys (map fst Γ) σ)).
  Proof.
    itr - vars vs ext Γ σ Hlength.
    rwr - add_keys_append_vars_to_env_app.
    2: asm.
    bwr - add_keys_get_env_app.
  Qed.



  Lemma add_keys_append_funs_to_env_app :
    forall ext n Γ σ,
        add_keys (map fst (append_funs_to_env ext Γ n)) σ
      = add_fids (map fst ext) (add_keys (map fst Γ) σ).
  Proof.
    itr - ext n Γ σ.
    ufl - append_funs_to_env.
    rwr - add_keys_get_env_app.
    ufl - add_ext.
    feq.
    gen - n.
    ind - ext as [| [fid [vars e]] ext IH]: smp.
    itr.
    smp.
    feq.
    bpe - IH: (S n).
  Qed.


End EraseSubstAppend_EraserLemmas.









Section EraseSubstAppend_SubstLemmas.



  Lemma list_subst_cons :
    forall v vs ξ,
      list_subst [v] (list_subst vs ξ)
    = list_subst (v::vs) ξ.
  Proof.
    trv.
  Qed.



  Lemma list_subst_fold_right :
    forall vs ξ,
      fold_right (fun v σ => v .: σ) ξ vs
    = list_subst vs ξ.
  Proof.
    trv.
  Qed.



  Lemma list_subst_app :
    forall vs1 vs2 ξ,
      list_subst vs1 (list_subst vs2 ξ)
    = list_subst (vs1 ++ vs2) ξ.
  Proof.
    itr.
    rewrite <- list_subst_fold_right with (vs:= vs1 ++ vs2).
    rewrite <- list_subst_fold_right with (vs:= vs1).
    rewrite <- list_subst_fold_right with (vs:= vs2).
    bwr - foldr_app.
  Qed.



End EraseSubstAppend_SubstLemmas.









Section EraseSubstAppend_Theorems.




  Theorem erase_subst_append_vars :
    forall Γ vars e vs,
        base.length vars = base.length vs
    ->  (erase_exp
          (from_env (append_vars_to_env vars vs Γ))
          e)
        .[list_subst
          (map
            (fun v => erase_val' v)
            (map snd (append_vars_to_env vars vs Γ)))
          idsubst]
      = (erase_exp
          (add_vars vars (from_env Γ))
          e)
        .[upn (base.length vars)
          (list_subst
            (map
               (fun v => erase_val' v)
               (map snd Γ)) idsubst)]
        .[list_subst
          (map
            (fun v => erase_val' v) vs)
            idsubst].
  Proof.
    itr -  Γ vars e vs Hlen.
    (* add_keys *)
    rwr - from_env_append_vars_to_env_app.
    (* upn to ++ *)
    rwr - subst_comp_exp.
    ass >
      (length vs
        = length (map (fun v => erase_val' v) vs))
      as Hlength_vars:
      rwr - length_map.
    rwl - Hlen in Hlength_vars.
    cwr - Hlength_vars.
    rwr - substcomp_list.
    rwr - substcomp_id_l.
    rwr - list_subst_app.
    (* append to ++ *)
    ufl - append_vars_to_env.
    rwr - map_app.
    epose proof length_map (inl : Var -> (Var + FunctionIdentifier)) vars
      as Hlength_map_inl.
    2: asm.
    cwl - Hlength_map_inl in Hlen.
    epose proof zip_snd _ _ _ _ Hlen as Hzip_snd;
      clr - Hlen.
    rwr - Hzip_snd.
    bwr - map_app.
  Qed.



End EraseSubstAppend_Theorems.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: FRAMESTACK_EVALUATION ////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section FrameStackEvaluation_Nth.



  Theorem fs_eval_nth_map_erase_forall :
    forall σ ξ el vl,
        (forall i,
            i < length vl
        ->  ⟨ [], (erase_exp σ (nth i el ErrorExp)).[ξ] ⟩ -->*
              RValSeq [erase_val' (nth i vl ErrorValue)])
    ->  (forall i,
            i < length vl
        ->  ⟨ [], nth i (map (fun e => (erase_exp σ e).[ξ]) el)
                        (erase_exp σ ErrorExp) ⟩ -->*
              RValSeq [nth i (map erase_val' vl) (erase_val' ErrorValue)]).
  Proof.
    itr - σ ξ el vl Hnth.
    itr - i Hi.
    spe - Hnth: i Hi.
    rewrite <- map_nth
      with (d := ErrorExp) (f := fun e => (erase_exp σ e).[ξ]) in Hnth.
    rewrite <- map_nth
      with (d := ErrorValue) (f := erase_val') in Hnth.
    exa - Hnth.
  Qed.






  Theorem fs_eval_nth_map_erase_single :
    forall σ ξ el i,
       (erase_exp σ (nth i el ErrorExp)).[ξ]
    =  nth i (map (fun e => (erase_exp σ e).[ξ]) el) (erase_exp σ ErrorExp).
  Proof.
    itr - σ ξ el i.
    rewrite map_nth with (d := ErrorExp) (f := fun e => (erase_exp σ e).[ξ]).
    rfl.
  Qed.






  Theorem fs_eval_nth_cons :
    forall e el ex v vl vx,
        (forall i,
            i < base.length (v :: vl)
        ->  ⟨ [], RExp (nth i (e :: el) ex) ⟩ -->* RValSeq [nth i (v :: vl) vx])
    ->  (⟨ [], RExp e ⟩ -->* RValSeq [v]
      /\
        (forall i,
            i < base.length vl
        ->  ⟨ [], RExp (nth i el ex) ⟩ -->* RValSeq [nth i vl vx])).
  Proof.
    itr - e el ex v vl vx Hnth.
    spl.
    * ass > (0 < base.length (v :: vl)) as Hlt: sli.
      spe + Hnth as IHv: 0 Hlt.
      smp - IHv.
      exa - IHv.
    * itr - i Hi.
      spe - Hnth: (S i).
      smp - Hnth.
      rwr - Nat.succ_lt_mono in Hi.
      spe - Hnth: Hi.
      exa - Hnth.
  Qed.






  Theorem fs_eval_nth_to_scope :
    forall el ex vl vx,
        length vl = length el
    ->  (forall i,
            i < length vl
        ->  ⟨ [], RExp (nth i el ex) ⟩ -->* RValSeq [nth i vl vx])
    ->  is_result (RValSeq vl).
  Proof.
    itr - el.
    (* #1 Induction on Expression List: induction + intro *)
    ind - el as [| e el IHvl];
      itr - ex vl vx Hlen Hnth.
    * clr - Hnth.
      (* #2.1 Both List is Empty: simpl/rewrite/subst *)
      smp - Hlen.
      rwr - length_zero_iff_nil in Hlen.
      sbt.
      (* #3.1 Solve Scope: constructor *)
      do 2 cns.
    * (* #2.2 Both List is Cons: (destruct + inversion/subst)/simpl/rewrite *)
      des - vl as [| v vl]: ivs - Hlen.
      smp - Hlen.
      rwr - Nat.succ_inj_wd in Hlen.
      (* #3.2 Pose Nth Cons Theorem: pose/destruct *)
      psc - fs_eval_nth_cons as Hnth_cons: e el ex v vl vx Hnth.
      des - Hnth_cons as [IHv Hnth].
      (* #4.2 Specialize Induction Hypothesis: rewrite/specialize *)
      spc - IHvl as Hscope_vl: ex vl vx Hlen Hnth.
      (* #5.2 Destruct Hypothesis: destruct *)
      des - IHv as [kv [Hscope_v _]].
      (* #6.2 Solve Scope: apply + auto *)
      app - scope_cons; ato.
  Qed.






  Theorem fs_eval_nth_to_result :
    forall ident el ex vl' v' vl vx r eff Fs,
        length vl = length el
    ->  Some (r , eff) = create_result ident (vl' ++ v' :: vl) []
    ->  (forall i,
            i < length vl
        ->  ⟨ [], RExp (nth i el ex) ⟩ -->* RValSeq [nth i vl vx])
    ->  exists k,
          ⟨ (FParams ident vl' el) :: Fs, RValSeq [v'] ⟩ -[ k ]-> ⟨ Fs, r ⟩.
  Proof.
    itr - ident el.
    (* #1 Induction on Expression List: induction + intro *)
    ind - el as [| e el IHvl];
      itr - ex vl' v' vl vx r eff Fs Hlen Hcrt Hnth.
    * clr - Hnth.
      (* #2.1 Both List is Empty: simpl/rewrite/subst *)
      smp - Hlen.
      rwr - length_zero_iff_nil in Hlen.
      sbt.
      (* #3.1 FrameStack Evaluation: exists/constructor/exact *)
      eei.
      do 2 ens.
      exa - Hcrt.
    * (* #2.2 Both List is Cons: (destruct + inversion/subst)/simpl/rewrite *)
      des - vl as [| v vl]: ivs - Hlen.
      smp - Hlen.
      rwr - Nat.succ_inj_wd in Hlen.
      (* #3.2 Pose Nth Cons Theorem: pose/destruct *)
      psc - fs_eval_nth_cons as Hnth_cons: e el ex v vl vx Hnth.
      des - Hnth_cons as [IHv Hnth].
      (* #4.2 Specialize Induction Hypothesis: rewrite/specialize *)
      rwr - cons_app
            app_assoc
            in Hcrt.
      spc - IHvl: ex (vl' ++ [v']) v vl vx r eff Fs Hlen Hcrt Hnth.
      (* #5.2 Destruct Induction Hypothesis: destruct *)
      des - IHv as [kv [Hscope_v Hstep_v]].
      des - IHvl as [kvl Hstep_vl].
      (* #6.2 FrameStack Evaluation: exists/step *)
      eei.
      step - Hstep_v.
      step - Hstep_vl.
  Qed.






  Theorem fs_eval_nth_to_partial :
    forall ident el e' el' ex vl' v' vl vx,
        length vl = length el
    ->  (forall i,
            i < length vl
        ->  ⟨ [], RExp (nth i (el ++ e' :: el') ex) ⟩ -->*
              RValSeq [nth i vl vx])
    ->  exists k,
          ⟨ [FParams ident vl' (el ++ e' :: el')], RValSeq [v'] ⟩ -[ k ]->
          ⟨ [FParams ident (vl' ++ v' :: vl) el'], RExp e' ⟩.
  Proof.
    itr - ident el.
    (* #1 Induction on Expression List: induction + intro *)
    ind - el as [| e el IHvl];
      itr - e' el' ex vl' v' vl vx Hlen Hnth.
    * clr - Hnth.
      (* #2.1 Both List is Empty: simpl/rewrite/subst *)
      smp - Hlen.
      rwr - length_zero_iff_nil in Hlen.
      sbt.
      (* #3.1 FrameStack Evaluation: exists/step *)
      eei.
      step.
    * (* #2.2 Both List is Cons: (destruct + inversion/subst)/simpl/rewrite *)
      des - vl as [| v vl]: ivs - Hlen.
      smp - Hlen.
      rwr - Nat.succ_inj_wd in Hlen.
      (* #3.2 Pose Nth Cons Theorem: pose/destruct *)
      psc - fs_eval_nth_cons as Hnth_cons: e (el ++ e' :: el') ex v vl vx Hnth.
      des - Hnth_cons as [IHv Hnth].
      (* #4.2 Specialize Induction Hypothesis: specialize/rewrite *)
      spc - IHvl: e' el' ex (vl' ++ [v']) v vl vx Hlen Hnth.
      rwl - app_assoc
            cons_app
            in IHvl.
      (* #5.2 Destruct Induction Hypothesis: destruct *)
      des - IHv as [kv [Hscope_v Hstep_v]].
      des - IHvl as [kvl Hstep_vl].
      (* #6.2 FrameStack Evaluation: exists/step *)
      eei.
      step - Hstep_v.
      step - Hstep_vl.
  Qed.



End FrameStackEvaluation_Nth.






Section FrameStackEvaluation_Create.

  Import SubstSemantics.



  Lemma create_result_ivalues :
    forall v vs eff,
      Some (RValSeq (v :: vs), eff)
    = create_result IValues ([v] ++ vs) eff.
  Proof.
    trv.
  Qed.



  Lemma create_result_ituple :
    forall v vl eff,
      Some (RValSeq [VTuple (v :: vl)], eff)
    = create_result ITuple ([v] ++ vl) eff.
  Proof.
    trv.
  Qed.



(*   Lemma create_result_imap :
    forall vl eff,
      Some (RValSeq [VMap (make_val_map vl)], eff)
    = create_result IMap ([] ++ vl) eff.
  Proof.
    trv.
  Qed. *)



End FrameStackEvaluation_Create.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: EQVIVALENCE_HELPERS //////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)


Section EqvivalenceHelpers.



End EqvivalenceHelpers.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: AXIOMS ///////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)


Section Axioms.



  Axiom all_val_is_wfm :
    forall v,
      wfm_fs_val v.



  Axiom no_modfunc :
    forall modules own_module fid,
      get_own_modfunc own_module fid.1 fid.2 (modules ++ stdlib) = None.



  Axiom result_is_result :
    forall Γ modules own_module e r id id' eff eff',
        (eval_expr Γ modules own_module id e eff id' r eff')
    ->  is_result (erase_result r).



  Axiom eval_catch_vars_length :
    forall Γ modules own_module vars1 vars2 e1 e2 e3 r id id' eff eff',
        (eval_expr Γ modules own_module id (ETry e1 vars1 e2 vars2 e3) eff id' r eff')
    ->  length vars2 = 3.



  Axiom erase_subst_rem_vars :
    forall Γ vars e,
       (erase_exp
        (add_vars vars (add_env (rem_vars vars Γ) σ0))
        e)
      .[upn (base.length vars)
        (list_subst
          (map erase_val' (map snd (rem_vars vars Γ)))
          idsubst)]
    = (erase_exp
        (add_vars vars (add_env Γ σ0))
        e)
      .[upn (base.length vars)
        (list_subst
          (map erase_val' (map snd Γ))
          idsubst)].



End Axioms.









Section Axioms_Lemmas.



  Lemma get_value_is_result :
    forall  Γ (modules : list ErlModule) (own_module : string)
            key v (id : nat) (eff : SideEffectList),
        get_value Γ key = Some [v]
    ->  VALCLOSED (erase_val' v).
  Proof.
    itr - Γ modules own_module key v id eff Hget.
    ass > (is_result (RValSeq (map (fun v' => erase_val' v') [v]))) as Hscope.
    {
      rem - r as Hr:
            (inl [v] : ValueSequence + Exception).
      des - key as [var | fid].
      * rem - e as He:
              (EVar var).
        pse - result_is_result as Hresult:
              Γ modules own_module e r id id eff eff.
        sbt.
        app - Hresult.
        clr - Hresult.
        bpp - eval_var.
      * rem - e as He:
              (EFunId fid).
        pse - result_is_result as Hresult:
              Γ modules own_module e r id id eff eff.
        sbt.
        app - Hresult.
        clr - Hresult.
        bpp - eval_funid.
    }
    smp - Hscope.
    ivc - Hscope as Hscope: H0.
    ivc - Hscope as Hscope: H1 / H2.
    exa - Hscope.
  Qed.



  Lemma evar_is_result :
    forall  Γ (modules : list ErlModule) (own_module : string)
            var vs (id : nat) (eff : SideEffectList),
        get_value Γ (inl var) = Some vs
    ->  (exists v,
            [v] = vs
        /\  VALCLOSED (erase_val' v)).
  Proof.
    itr - Γ modules own_module var vs id eff Hget.
    rem - key as Hkey:
          (inl var : Var + FunctionIdentifier).
    pse - get_value_singleton as Hsingle:
          Γ key vs Hget.
    des - Hsingle as [v Hsingle].
    cwr - Hsingle in *; clr - vs.
    exi - v.
    spl.
    rfl.
    pse - get_value_is_result as Hscope:
          Γ modules own_module key v id eff Hget.
    exa - Hscope.
  Qed.



  Lemma efunid_is_result :
    forall  Γ (modules : list ErlModule) (own_module : string)
            fid vs (id : nat) (eff : SideEffectList),
        get_value Γ (inr fid) = Some vs
    ->  (exists v,
            [v] = vs
        /\  VALCLOSED (erase_val' v)).
  Proof.
    itr - Γ modules own_module fid vs id eff Hget.
    rem - key as Hkey:
          (inr fid : Var + FunctionIdentifier).
    pse - get_value_singleton as Hsingle:
          Γ key vs Hget.
    des - Hsingle as [v Hsingle].
    cwr - Hsingle in *; clr - vs.
    exi - v.
    spl.
    rfl.
    pse - get_value_is_result as Hscope:
          Γ modules own_module key v id eff Hget.
    exa - Hscope.
  Qed.



  Lemma efun_is_result :
    forall  Γ (modules : list ErlModule) (own_module : string)
            vars e id (eff : SideEffectList),
      is_result (erase_result (inl [VClos Γ [] id vars e])).
  Proof.
    itr - Γ modules own_module vars e id eff.
    pse - eval_fun as Heval:
          Γ modules own_module vars e eff id.
    bse - result_is_result:
          Γ modules own_module (EFun vars e)
          (inl [VClos Γ [] id vars e] : ValueSequence + Exception)
          id (S id) eff eff Heval.
  Qed.



  Lemma catch_vars_length :
    forall Γ modules own_module (vars1 : list Var) vars2 e1 (e2 : Expression)
           e3 x1 r3 id id' id'' eff eff' eff'',
        eval_expr Γ modules own_module id e1 eff id' (inr x1) eff'
    ->  eval_expr (append_vars_to_env vars2 (exc_to_vals x1) Γ)
                  modules own_module id' e3 eff' id'' r3 eff''
    ->  length vars2 = 3.
  Proof.
    itr - Γ modules own_module vars1 vars2 e1 e2 e3 x1 r3 id id' id''
          eff eff' eff'' IHe1 IHe3.
    rwl - exc_to_vals_eq in IHe3.
    pse - eval_catch as Heval:
          Γ modules own_module vars1 vars2 e1 e2 e3 r3
          eff eff' eff'' id id' id'' x1 IHe1 IHe3.
    bse - eval_catch_vars_length:
          Γ modules own_module vars1 vars2 e1 e2 e3 r3
          id id'' eff eff'' Heval.
  Qed.



End Axioms_Lemmas.