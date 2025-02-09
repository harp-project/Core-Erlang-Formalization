From CoreErlang.Eqvivalence.BsFs Require Export B2MeasureReduction.

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
    + open
  - Step (TACTICS)
    + do_step
    + do_transitive
    + step
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






  Theorem scope_list_to_map :
    forall vll,
        is_result (RValSeq (flatten_list vll))
    ->  is_result (RValSeq [VMap vll]).
  Proof.
    (* #1 Inversion: intro/inversion/destruct_foralls *)
    itr - vll Hvll.
    ivc - Hvll as Hvll: H0.
    ind - vll as [| [v1 v2] vll IHvll].
    * do 3 cns.
      - smp; itr; lia.
      - smp; itr; lia.
    * do 3 cns.
      - ivc - Hvll as Hv1 Hvll: H1 H2.
        ivc - Hvll as Hv2 Hvll: H1 H2.
        spc - IHvll: Hvll.
        ivc - IHvll as IHvll: H0.
        ivc - IHvll as IHvll: H1 / H2.
        ivc - IHvll as Hvll_fst Hvll_snd: H0 H2.
        itr - i Hlt.
        smp *.
        des - i: asm |> clr - Hv1.
        app - Hvll_fst.
        lia.
      - ivc - Hvll as Hv1 Hvll: H1 H2.
        ivc - Hvll as Hv2 Hvll: H1 H2.
        spc - IHvll: Hvll.
        ivc - IHvll as IHvll: H0.
        ivc - IHvll as IHvll: H1 / H2.
        ivc - IHvll as Hvll_fst Hvll_snd: H0 H2.
        itr - i Hlt.
        smp *.
        des - i: asm |> clr - Hv2.
        app - Hvll_snd.
        lia.
  Qed.



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
  * open --> eexists; split; [> scope]; clear.
    / [ident]:0-3
    - hyp
  *)

  Tactic Notation "open"
      :=
    eexists; split; [(scope + admit) | idtac].

  Tactic Notation "open"
      "/"   ident(I1)
      :=
    eexists; split; [(scope + admit) | idtac];
    clear I1.

  Tactic Notation "open"
      "/"   ident(I1) ident(I2)
      :=
    eexists; split; [(scope + admit) | idtac];
    clear I1 I2.

  Tactic Notation "open"
      "/"   ident(I1) ident(I2) ident(I3)
      :=
    eexists; split; [(scope + admit) | idtac];
    clear I1 I2 I3.

  Tactic Notation "open"
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